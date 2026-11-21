/* Foundation collections and values: NSArray, NSDictionary, NSSet (and their mutable subclasses), NSNumber/NSValue,
 * NSNull, NSData, NSEnumerator, NSCharacterSet, NSScanner, NSIndexPath, a minimal NSPredicate, property lists, and the
 * collection- and file-related NSString methods foundation.c does not have.
 *
 * Every object lives in game memory and keeps its state in its own instance variables (game words), so nothing
 * here needs per-object host state and the game can be handed stable addresses (fast enumeration's mutationsPtr).
 * Layouts (offsets from the object; isa at 0):
 *   NSArray        { isa, items, count, cap, mutations }           items: game block of `cap` ids
 *   NSDictionary   { isa, keys, vals, count, cap, mutations, index, index_cap }
 *   NSSet          same as NSDictionary, vals unused (0)
 *                  keys/vals are parallel game blocks in insertion order; index is an open-addressing table of
 *                  (entry + 1) words, rebuilt after a removal. Keys hash and compare by value when they are NSString
 *                  or NSNumber (-hash / -isEqual: semantics), by address otherwise.
 *   NSValue        { isa, kind, payload[16] }                     NSNumber is an NSValue subclass with no ivars
 *   NSData         { isa, bytes, length, cap, owned }             owned: the bytes are freed with the object
 *   NSEnumerator   { isa, snapshot NSArray (retained), index }
 *   NSCharacterSet { isa, bitmap[32], flags }                     bytes 0-255; flags bit 0: members above 255
 *   NSScanner      { isa, string, location, skip set, case-insensitive }
 *   NSIndexPath    { isa, length, index[4] }
 *   NSPredicate    { isa, op, argument, options }
 *
 * Strings are foundation.c's NUL-terminated UTF-8 (lengths in bytes). New strings come from rt_nsstring(_new), or,
 * for an allocated instance (initWith...), from foundation's own -initWithUTF8String: so the class is kept.
 *
 * Fast enumeration (-countByEnumeratingWithState:objects:count:) copies a batch of up to `count` items into the
 * caller's buffer; state = { state: next index, itemsPtr: the buffer, mutationsPtr: the object's mutations word }.
 *
 * Property lists: XML (read/write), binary "bplist00" (read) and the old-style ASCII format (NSString
 * -propertyList, .strings files). Containers read from a file are mutable (a mutable class is-a immutable one).
 *
 * Exceptions: where Cocoa throws (index out of range, nil insertion) this logs once and does nothing / returns nil.
 */
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rt.h"

#define SELF c->r[0]
#define ARG(k) rt_arg(c, (k) + 2)
#define RET(v) rt_ret(c, (uint32_t)(v))
#define M(name) static void name(cpu_t *c, uint8_t *m)

#define NSNotFound 0x7fffffffu

static id cls_string;
static id cls_array, cls_marray, cls_dict, cls_mdict, cls_set, cls_mset;
static id cls_value, cls_number, cls_null, cls_data, cls_mdata, cls_enum;
static id cls_charset, cls_mcharset, cls_scanner, cls_indexpath, cls_predicate;
static id null_singleton;

/* log a message once per call site */
#define LOG_ONCE(...) do { static int once_; if (!once_++) rt_log(__VA_ARGS__); } while (0)

/* ---- host string builder ------------------------------------------------------------------------------------- */
typedef struct { char *p; size_t n, cap; } sb;

static void sb_putn(sb *b, const char *s, size_t n) {
    if (b->n + n + 1 > b->cap) {
        b->cap = (b->n + n + 1) * 2 + 64;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->n, s, n);
    b->n += n;
    b->p[b->n] = 0;
}
static void sb_puts(sb *b, const char *s) { sb_putn(b, s, strlen(s)); }
static void sb_putc(sb *b, char ch) { sb_putn(b, &ch, 1); }
static void sb_printf(sb *b, const char *fmt, ...) {
    char tmp[256];
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(tmp, sizeof tmp, fmt, ap);
    va_end(ap);
    if (n > 0) sb_putn(b, tmp, (size_t)n < sizeof tmp ? (size_t)n : sizeof tmp - 1);
}
static void sb_spaces(sb *b, int n) { for (int k = 0; k < n; k++) sb_putc(b, ' '); }
static const char *sb_str(sb *b) { return b->p ? b->p : ""; }

/* append a code point as UTF-8 */
static void sb_utf8(sb *b, uint32_t u) {
    char o[4];
    if (u < 0x80) { o[0] = (char)u; sb_putn(b, o, 1); }
    else if (u < 0x800) { o[0] = (char)(0xc0 | u >> 6); o[1] = (char)(0x80 | (u & 63)); sb_putn(b, o, 2); }
    else if (u < 0x10000) {
        o[0] = (char)(0xe0 | u >> 12); o[1] = (char)(0x80 | ((u >> 6) & 63)); o[2] = (char)(0x80 | (u & 63));
        sb_putn(b, o, 3);
    } else {
        o[0] = (char)(0xf0 | u >> 18); o[1] = (char)(0x80 | ((u >> 12) & 63));
        o[2] = (char)(0x80 | ((u >> 6) & 63)); o[3] = (char)(0x80 | (u & 63));
        sb_putn(b, o, 4);
    }
}

/* the next code point of a UTF-8 string (invalid bytes pass through as Latin-1) */
static uint32_t utf8_next(const char **ps) {
    const uint8_t *s = (const uint8_t *)*ps;
    uint32_t u = s[0];
    int n = u >= 0xf0 ? 3 : u >= 0xe0 ? 2 : u >= 0xc0 ? 1 : 0;
    for (int k = 1; k <= n; k++)
        if ((s[k] & 0xc0) != 0x80) n = 0;
    if (n) {
        u &= 0x3f >> n;
        for (int k = 1; k <= n; k++) u = u << 6 | (s[k] & 63);
    }
    *ps = (const char *)s + n + 1;
    return u;
}

/* ---- objects ------------------------------------------------------------------------------------------------- */
static int is_str(id o) { return o && rt_is_kind(o, cls_string); }
static int is_num(id o) { return o && rt_is_kind(o, cls_number); }
static const char *S(id s) { const char *u = rt_nsstring_utf8(s); return u ? u : ""; }

/* a retained string of `n` bytes */
static id str_new_n(const char *p, size_t n) {
    char *t = malloc(n + 1);
    memcpy(t, p, n);
    t[n] = 0;
    id s = rt_nsstring_new(t);
    free(t);
    return s;
}

/* initialize an allocated string instance with UTF-8 text through foundation's initializer (keeps its class) */
static id str_init(cpu_t *c, id self, const char *utf8) {
    uint32_t tmp = rt_strdup_guest(utf8);
    id r = rt_send(c, self, "initWithUTF8String:", 1, tmp);
    rt_free(tmp);
    return r;
}

/* store an autoreleased object through an out-pointer argument (NSString **, NSError **) when it is given */
static void out_obj(uint32_t ptr, id v) { if (ptr) rt_st32(ptr, v); }

/* -isEqual: for any two objects: strings and numbers by value, others through their own -isEqual: */
static int num_eq(id a, id b);
static int obj_eq(cpu_t *c, id a, id b) {
    if (a == b) return 1;
    if (!a || !b) return 0;
    if (is_str(a)) return is_str(b) && !strcmp(S(a), S(b));
    if (is_num(a)) return is_num(b) && num_eq(a, b);
    return rt_send(c, a, "isEqual:", 1, b) & 0xff;
}

/* ---- files and text encodings ---------------------------------------------------------------------------------- */
static uint8_t *file_read(const char *gpath, size_t *len) {
    if (!gpath || !*gpath) return NULL;
    FILE *f = fopen(rt_host_path(gpath), "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n < 0) { fclose(f); return NULL; }
    uint8_t *buf = malloc((size_t)n + 2);
    size_t got = fread(buf, 1, (size_t)n, f);
    fclose(f);
    buf[got] = buf[got + 1] = 0;
    *len = got;
    return buf;
}

static int file_write(const char *gpath, const void *p, size_t n, int atomic) {
    if (!gpath || !*gpath) return 0;
    char path[1024], tmp[1100];
    snprintf(path, sizeof path, "%s", rt_host_path(gpath));
    snprintf(tmp, sizeof tmp, "%s.tmp~", path);
    FILE *f = fopen(atomic ? tmp : path, "wb");
    if (!f) { rt_log("collections: cannot write %s", path); return 0; }
    int ok = fwrite(p, 1, n, f) == n;
    ok &= fclose(f) == 0;
    if (!atomic) return ok;
    if (!ok) { remove(tmp); return 0; }
    remove(path); /* rename does not replace on Windows */
    if (rename(tmp, path)) { remove(tmp); return 0; }
    return 1;
}

enum {
    ENC_ASCII = 1, ENC_UTF8 = 4, ENC_LATIN1 = 5, ENC_NONLOSSY = 7, ENC_CP1252 = 12, ENC_UTF16 = 10,
    ENC_MACROMAN = 30, ENC_UTF16BE = 0x90000100u, ENC_UTF16LE = 0x94000100u,
};

/* Windows-1252 0x80-0x9f */
static const uint16_t cp1252[32] = {
    0x20ac, 0x81, 0x201a, 0x192, 0x201e, 0x2026, 0x2020, 0x2021, 0x2c6, 0x2030, 0x160, 0x2039, 0x152, 0x8d, 0x17d, 0x8f,
    0x90, 0x2018, 0x2019, 0x201c, 0x201d, 0x2022, 0x2013, 0x2014, 0x2dc, 0x2122, 0x161, 0x203a, 0x153, 0x9d, 0x17e, 0x178,
};

/* decode bytes in an encoding (a byte-order mark wins) into a malloc'd UTF-8 string; *used gets the encoding */
static char *decode_text(const uint8_t *p, size_t n, uint32_t enc, uint32_t *used) {
    sb b = {0};
    int utf16 = 0, le = 0;
    if (n >= 2 && p[0] == 0xff && p[1] == 0xfe) { utf16 = 1; le = 1; p += 2; n -= 2; }
    else if (n >= 2 && p[0] == 0xfe && p[1] == 0xff) { utf16 = 1; le = 0; p += 2; n -= 2; }
    else if (n >= 3 && p[0] == 0xef && p[1] == 0xbb && p[2] == 0xbf) { p += 3; n -= 3; enc = ENC_UTF8; }
    else if (enc == ENC_UTF16) { utf16 = 1; le = n >= 2 && p[0] && !p[1]; } /* no mark: guess from the first unit */
    else if (enc == ENC_UTF16LE) { utf16 = 1; le = 1; }
    else if (enc == ENC_UTF16BE) { utf16 = 1; le = 0; }
    if (used) *used = utf16 ? ENC_UTF16 : enc;
    if (utf16) {
        for (size_t k = 0; k + 1 < n; k += 2) {
            uint32_t u = le ? (uint32_t)(p[k] | p[k + 1] << 8) : (uint32_t)(p[k] << 8 | p[k + 1]);
            if (u >= 0xd800 && u < 0xdc00 && k + 3 < n) {
                uint32_t v = le ? (uint32_t)(p[k + 2] | p[k + 3] << 8) : (uint32_t)(p[k + 2] << 8 | p[k + 3]);
                if (v >= 0xdc00 && v < 0xe000) { u = 0x10000 + ((u - 0xd800) << 10) + (v - 0xdc00); k += 2; }
            }
            if (u) sb_utf8(&b, u);
        }
    } else if (enc == ENC_LATIN1 || enc == ENC_CP1252 || enc == ENC_MACROMAN) {
        for (size_t k = 0; k < n; k++) {
            uint32_t u = p[k];
            if (enc == ENC_CP1252 && u >= 0x80 && u < 0xa0) u = cp1252[u - 0x80];
            if (u) sb_utf8(&b, u);
        }
    } else {
        size_t k = 0;
        while (k < n && p[k]) k++;
        sb_putn(&b, (const char *)p, k);
    }
    if (!b.p) sb_putn(&b, "", 0);
    return b.p;
}

/* encode UTF-8 text; NULL when a character cannot be represented and the conversion is not lossy */
static uint8_t *encode_text(const char *s, uint32_t enc, int lossy, size_t *len) {
    sb b = {0};
    sb_putn(&b, "", 0);
    if (enc == ENC_UTF16 || enc == ENC_UTF16LE || enc == ENC_UTF16BE) {
        int be = enc == ENC_UTF16BE;
        if (enc == ENC_UTF16) sb_putn(&b, "\xff\xfe", 2); /* -dataUsingEncoding:NSUnicodeStringEncoding has a BOM */
        while (*s) {
            uint32_t u = utf8_next(&s);
            uint16_t units[2];
            int nu = 1;
            if (u >= 0x10000) { u -= 0x10000; units[0] = (uint16_t)(0xd800 + (u >> 10)); units[1] = (uint16_t)(0xdc00 + (u & 0x3ff)); nu = 2; }
            else units[0] = (uint16_t)u;
            for (int k = 0; k < nu; k++) {
                char o[2] = {(char)(be ? units[k] >> 8 : units[k] & 0xff), (char)(be ? units[k] & 0xff : units[k] >> 8)};
                sb_putn(&b, o, 2);
            }
        }
    } else if (enc == ENC_ASCII || enc == ENC_LATIN1 || enc == ENC_CP1252 || enc == ENC_MACROMAN) {
        while (*s) {
            uint32_t u = utf8_next(&s);
            int ok = enc == ENC_ASCII ? u < 0x80 : u < 0x100;
            if (enc == ENC_CP1252 && u >= 0x80 && u < 0xa0) ok = 0;
            if (enc == ENC_CP1252 && !ok)
                for (int k = 0; k < 32; k++)
                    if (cp1252[k] == u) { u = 0x80 + (uint32_t)k; ok = 1; break; }
            if (!ok) {
                if (!lossy) { free(b.p); return NULL; }
                u = '?';
            }
            sb_putc(&b, (char)u);
        }
    } else {
        sb_puts(&b, s); /* UTF-8 and everything else */
    }
    *len = b.n;
    return (uint8_t *)b.p;
}

/* ---- NSArray ------------------------------------------------------------------------------------------------- */
enum { A_ITEMS = 4, A_COUNT = 8, A_CAP = 12, A_MUT = 16, A_IVARS = 16 };

static uint32_t arr_n(id a) { return rt_ld32(a + A_COUNT); }
static uint32_t arr_items(id a) { return rt_ld32(a + A_ITEMS); }
static id arr_get(id a, uint32_t k) { return rt_ld32(arr_items(a) + 4 * k); }
static void bump(id o, uint32_t off) { rt_st32(o + off, rt_ld32(o + off) + 1); }

static void arr_reserve(id a, uint32_t n) {
    uint32_t cap = rt_ld32(a + A_CAP);
    if (n <= cap) return;
    uint32_t nc = cap ? cap * 2 : 8;
    while (nc < n) nc *= 2;
    rt_st32(a + A_ITEMS, rt_realloc(arr_items(a), 4 * nc));
    rt_st32(a + A_CAP, nc);
}

static void arr_insert(id a, uint32_t k, id obj) {
    uint32_t n = arr_n(a);
    if (k > n) k = n;
    arr_reserve(a, n + 1);
    uint32_t it = arr_items(a);
    memmove(rt_mem + it + 4 * (k + 1), rt_mem + it + 4 * k, 4 * (size_t)(n - k));
    rt_st32(it + 4 * k, rt_retain(obj));
    rt_st32(a + A_COUNT, n + 1);
    bump(a, A_MUT);
}
static void arr_add(id a, id obj) { arr_insert(a, arr_n(a), obj); }

static void arr_remove(cpu_t *c, id a, uint32_t k) {
    uint32_t n = arr_n(a), it = arr_items(a);
    if (k >= n) return;
    id obj = arr_get(a, k);
    memmove(rt_mem + it + 4 * k, rt_mem + it + 4 * (k + 1), 4 * (size_t)(n - k - 1));
    rt_st32(a + A_COUNT, n - 1);
    bump(a, A_MUT);
    rt_release(c, obj);
}

static void arr_clear(cpu_t *c, id a) {
    uint32_t n = arr_n(a);
    if (!n) return;
    uint32_t *tmp = malloc(4 * (size_t)n);
    memcpy(tmp, rt_mem + arr_items(a), 4 * (size_t)n);
    rt_st32(a + A_COUNT, 0);
    bump(a, A_MUT);
    for (uint32_t k = 0; k < n; k++) rt_release(c, tmp[k]);
    free(tmp);
}

static id arr_alloc(id cls) { return rt_objc_alloc(cls ? cls : cls_array); }
static id arr_from(id cls, const id *items, uint32_t n) {
    id a = arr_alloc(cls);
    arr_reserve(a, n);
    for (uint32_t k = 0; k < n; k++) arr_add(a, items[k]);
    return a;
}
/* a retained array with the items of another array */
static id arr_copy_of(id cls, id src) {
    id a = arr_alloc(cls);
    uint32_t n = src ? arr_n(src) : 0;
    arr_reserve(a, n);
    for (uint32_t k = 0; k < n; k++) arr_add(a, arr_get(src, k));
    return a;
}

/* the class an +array... constructor should instantiate: the receiver (NSArray, NSMutableArray or a subclass) */
#define RECV_CLASS() (SELF)

/* nil-terminated variadic objects from argument word `first` */
static void add_varargs(cpu_t *c, id a, int first) {
    for (int k = first; k < first + 4096; k++) {
        id o = rt_arg(c, k);
        if (!o) break;
        arr_add(a, o);
    }
}

/* ---- NSDictionary / NSSet hash tables -------------------------------------------------------------------------- */
enum { H_KEYS = 4, H_VALS = 8, H_COUNT = 12, H_CAP = 16, H_MUT = 20, H_INDEX = 24, H_ICAP = 28, H_IVARS = 28 };

static uint32_t mix32(uint64_t v) {
    v ^= v >> 33; v *= 0xff51afd7ed558ccdull; v ^= v >> 33;
    return (uint32_t)v;
}

static double num_d(id n);
static int64_t num_i(id n);
static int num_is_float(id n);

static uint32_t key_hash(id k) {
    if (is_str(k)) {
        uint32_t h = 2166136261u;
        for (const char *p = S(k); *p; p++) h = (h ^ (uint8_t)*p) * 16777619u;
        return h;
    }
    if (is_num(k)) {
        if (num_is_float(k)) {
            double d = num_d(k);
            if (d == floor(d) && fabs(d) < 9e18) return mix32((uint64_t)(int64_t)d);
            if (d == 0) d = 0; /* -0 */
            uint64_t u;
            memcpy(&u, &d, 8);
            return mix32(u);
        }
        return mix32((uint64_t)num_i(k));
    }
    return mix32(k);
}

static int key_eq(id a, id b) {
    if (a == b) return 1;
    if (is_str(a)) return is_str(b) && !strcmp(S(a), S(b));
    if (is_num(a)) return is_num(b) && num_eq(a, b);
    return 0;
}

static uint32_t h_n(id h) { return rt_ld32(h + H_COUNT); }
static id h_key(id h, uint32_t k) { return rt_ld32(rt_ld32(h + H_KEYS) + 4 * k); }
static id h_val(id h, uint32_t k) { return rt_ld32(rt_ld32(h + H_VALS) + 4 * k); }

static void h_index_insert(id h, uint32_t k) {
    uint32_t idx = rt_ld32(h + H_INDEX), cap = rt_ld32(h + H_ICAP);
    for (uint32_t i = key_hash(h_key(h, k)) & (cap - 1);; i = (i + 1) & (cap - 1))
        if (!rt_ld32(idx + 4 * i)) { rt_st32(idx + 4 * i, k + 1); return; }
}

static void h_reindex(id h) {
    uint32_t n = h_n(h), cap = 16;
    while (cap < 2 * n + 2) cap *= 2;
    uint32_t idx = rt_ld32(h + H_INDEX);
    if (rt_ld32(h + H_ICAP) != cap) {
        rt_free(idx);
        idx = rt_malloc(4 * cap);
        rt_st32(h + H_INDEX, idx);
        rt_st32(h + H_ICAP, cap);
    }
    memset(rt_mem + idx, 0, 4 * (size_t)cap);
    for (uint32_t k = 0; k < n; k++) h_index_insert(h, k);
}

static int32_t h_find(id h, id key) {
    uint32_t cap = rt_ld32(h + H_ICAP), idx = rt_ld32(h + H_INDEX);
    if (!cap || !key) return -1;
    for (uint32_t i = key_hash(key) & (cap - 1);; i = (i + 1) & (cap - 1)) {
        uint32_t e = rt_ld32(idx + 4 * i);
        if (!e) return -1;
        if (key_eq(h_key(h, e - 1), key)) return (int32_t)(e - 1);
    }
}

/* keys are copied (NSCopying): strings through -copy, everything else is retained */
static id key_copy(cpu_t *c, id key) { return is_str(key) ? rt_send(c, key, "copy", 0) : rt_retain(key); }

static void h_put(cpu_t *c, id h, id key, id val) {
    int32_t k = h_find(h, key);
    if (k >= 0) {
        uint32_t slot = rt_ld32(h + H_VALS) + 4 * (uint32_t)k;
        id old = rt_ld32(slot);
        rt_st32(slot, rt_retain(val));
        bump(h, H_MUT);
        rt_release(c, old);
        return;
    }
    id kc = key_copy(c, key);
    uint32_t n = h_n(h), cap = rt_ld32(h + H_CAP);
    if (n + 1 > cap) {
        uint32_t nc = cap ? cap * 2 : 8;
        rt_st32(h + H_KEYS, rt_realloc(rt_ld32(h + H_KEYS), 4 * nc));
        rt_st32(h + H_VALS, rt_realloc(rt_ld32(h + H_VALS), 4 * nc));
        rt_st32(h + H_CAP, nc);
    }
    rt_st32(rt_ld32(h + H_KEYS) + 4 * n, kc);
    rt_st32(rt_ld32(h + H_VALS) + 4 * n, rt_retain(val));
    rt_st32(h + H_COUNT, n + 1);
    if (2 * (n + 1) + 2 > rt_ld32(h + H_ICAP)) h_reindex(h);
    else h_index_insert(h, n);
    bump(h, H_MUT);
}

static void h_remove_at(cpu_t *c, id h, uint32_t k) {
    uint32_t n = h_n(h), ks = rt_ld32(h + H_KEYS), vs = rt_ld32(h + H_VALS);
    if (k >= n) return;
    id key = h_key(h, k), val = h_val(h, k);
    memmove(rt_mem + ks + 4 * k, rt_mem + ks + 4 * (k + 1), 4 * (size_t)(n - k - 1));
    memmove(rt_mem + vs + 4 * k, rt_mem + vs + 4 * (k + 1), 4 * (size_t)(n - k - 1));
    rt_st32(h + H_COUNT, n - 1);
    h_reindex(h);
    bump(h, H_MUT);
    rt_release(c, key);
    rt_release(c, val);
}

static void h_remove(cpu_t *c, id h, id key) {
    int32_t k = h_find(h, key);
    if (k >= 0) h_remove_at(c, h, (uint32_t)k);
}

static void h_clear(cpu_t *c, id h) {
    uint32_t n = h_n(h);
    if (!n) return;
    uint32_t *tmp = malloc(8 * (size_t)n);
    memcpy(tmp, rt_mem + rt_ld32(h + H_KEYS), 4 * (size_t)n);
    memcpy(tmp + n, rt_mem + rt_ld32(h + H_VALS), 4 * (size_t)n);
    rt_st32(h + H_COUNT, 0);
    h_reindex(h);
    bump(h, H_MUT);
    for (uint32_t k = 0; k < 2 * n; k++) rt_release(c, tmp[k]);
    free(tmp);
}

static void h_free(id h) {
    rt_free(rt_ld32(h + H_KEYS));
    rt_free(rt_ld32(h + H_VALS));
    rt_free(rt_ld32(h + H_INDEX));
}

static id h_get(id h, id key) {
    int32_t k = h_find(h, key);
    return k >= 0 ? h_val(h, (uint32_t)k) : 0;
}

/* a retained array of the keys (or values) */
static id h_list(id h, int vals) {
    id a = arr_alloc(cls_array);
    uint32_t n = h_n(h);
    arr_reserve(a, n);
    for (uint32_t k = 0; k < n; k++) arr_add(a, vals ? h_val(h, k) : h_key(h, k));
    return a;
}

/* ---- NSValue / NSNumber ----------------------------------------------------------------------------------------- */
enum { V_KIND = 4, V_DATA = 8, V_IVARS = 20 };
enum { NK_INT, NK_UINT, NK_DOUBLE, NK_FLOAT, NK_BOOL, NK_CHAR, NK_SHORT, NK_LONGLONG, NK_ULONGLONG,
       VK_POINTER = 16, VK_OBJECT, VK_POINT, VK_SIZE, VK_RECT, VK_RANGE };
static uint32_t objc_types[24]; /* game C strings for -objCType */

static int num_is_float(id n) { uint32_t k = rt_ld32(n + V_KIND); return k == NK_DOUBLE || k == NK_FLOAT; }
static double num_d(id n) {
    uint32_t k = rt_ld32(n + V_KIND);
    if (k == NK_DOUBLE || k == NK_FLOAT) { double d; memcpy(&d, rt_mem + n + V_DATA, 8); return d; }
    uint64_t u;
    memcpy(&u, rt_mem + n + V_DATA, 8);
    return (k == NK_UINT || k == NK_ULONGLONG) ? (double)u : (double)(int64_t)u;
}
static int64_t num_i(id n) {
    if (num_is_float(n)) {
        double d = num_d(n);
        if (d != d) return 0;
        if (d >= 9.2e18) return INT64_MAX;
        if (d <= -9.2e18) return INT64_MIN;
        return (int64_t)d;
    }
    int64_t v;
    memcpy(&v, rt_mem + n + V_DATA, 8);
    return v;
}
static int num_eq(id a, id b) {
    if (num_is_float(a) || num_is_float(b)) return num_d(a) == num_d(b);
    return num_i(a) == num_i(b);
}
static int num_cmp(id a, id b) {
    if (num_is_float(a) || num_is_float(b)) { double x = num_d(a), y = num_d(b); return x < y ? -1 : x > y; }
    int64_t x = num_i(a), y = num_i(b);
    return x < y ? -1 : x > y;
}

static id num_make(id obj, int kind, int64_t i, double d) {
    rt_st32(obj + V_KIND, (uint32_t)kind);
    if (kind == NK_DOUBLE || kind == NK_FLOAT) memcpy(rt_mem + obj + V_DATA, &d, 8);
    else memcpy(rt_mem + obj + V_DATA, &i, 8);
    return obj;
}
static id num_new(int kind, int64_t i, double d) { return num_make(rt_objc_alloc(cls_number), kind, i, d); }

static void num_string(id n, char *out, size_t cap) {
    uint32_t k = rt_ld32(n + V_KIND);
    if (k == NK_DOUBLE || k == NK_FLOAT) {
        double d = num_d(n);
        snprintf(out, cap, k == NK_FLOAT ? "%.7g" : "%.15g", d);
    } else if (k == NK_UINT || k == NK_ULONGLONG) {
        snprintf(out, cap, "%llu", (unsigned long long)num_i(n));
    } else {
        snprintf(out, cap, "%lld", (long long)num_i(n));
    }
}

/* ---- NSData ------------------------------------------------------------------------------------------------- */
enum { D_BYTES = 4, D_LEN = 8, D_CAP = 12, D_OWNED = 16, D_IVARS = 16 };

static uint32_t data_bytes(id d) { return rt_ld32(d + D_BYTES); }
static uint32_t data_len(id d) { return rt_ld32(d + D_LEN); }

/* make room for n bytes (own buffer; new bytes zeroed) */
static void data_reserve(id d, uint32_t n) {
    uint32_t cap = rt_ld32(d + D_CAP), owned = rt_ld32(d + D_OWNED), len = data_len(d);
    if (n <= cap && owned) return;
    uint32_t nc = cap > 16 ? cap : 16;
    while (nc < n) nc *= 2;
    uint32_t nb = rt_malloc(nc);
    memset(rt_mem + nb, 0, nc);
    if (len) memcpy(rt_mem + nb, rt_mem + data_bytes(d), len);
    if (owned) rt_free(data_bytes(d));
    rt_st32(d + D_BYTES, nb);
    rt_st32(d + D_CAP, nc);
    rt_st32(d + D_OWNED, 1);
}

static void data_set_len(id d, uint32_t n) {
    uint32_t len = data_len(d);
    if (n > len) {
        data_reserve(d, n);
        memset(rt_mem + data_bytes(d) + len, 0, n - len);
    }
    rt_st32(d + D_LEN, n);
}

static void data_append(id d, const void *p, uint32_t n) {
    uint32_t len = data_len(d);
    if (!n) return;
    /* p may point into this data's own buffer, which data_reserve can move */
    void *tmp = malloc(n);
    memcpy(tmp, p, n);
    data_reserve(d, len + n);
    memcpy(rt_mem + data_bytes(d) + len, tmp, n);
    free(tmp);
    rt_st32(d + D_LEN, len + n);
}

static id data_fill(id d, const void *p, uint32_t n) {
    data_reserve(d, n ? n : 1);
    if (n) memmove(rt_mem + data_bytes(d), p, n); /* p may be this object's own bytes (setData: self) */
    rt_st32(d + D_LEN, n);
    return d;
}

/* ---- NSCharacterSet ------------------------------------------------------------------------------------------- */
enum { CS_BITS = 4, CS_FLAGS = 36, CS_IVARS = 36 };

static int cs_has(id cs, uint32_t ch) {
    if (!cs) return 0;
    if (ch >= 256) return rt_ld32(cs + CS_FLAGS) & 1;
    return (rt_mem[cs + CS_BITS + (ch >> 3)] >> (ch & 7)) & 1;
}
static void cs_set(id cs, uint32_t ch, int on) {
    if (ch >= 256) return;
    if (on) rt_mem[cs + CS_BITS + (ch >> 3)] |= (uint8_t)(1 << (ch & 7));
    else rt_mem[cs + CS_BITS + (ch >> 3)] &= (uint8_t)~(1 << (ch & 7));
}
static void cs_add_string(id cs, const char *s, int on) {
    for (const uint8_t *p = (const uint8_t *)s; *p; p++) cs_set(cs, *p, on);
}

enum { CS_WHITESPACE, CS_WHITESPACE_NL, CS_NEWLINE, CS_DIGITS, CS_LETTERS, CS_ALNUM, CS_PUNCT, CS_UPPER, CS_LOWER,
       CS_CONTROL, CS_SYMBOL, CS_NSTD };
static id std_sets[CS_NSTD];

static id cs_standard(int which) {
    if (std_sets[which]) return std_sets[which];
    id cs = rt_objc_alloc(cls_charset); /* kept forever */
    for (uint32_t ch = 0; ch < 256; ch++) {
        int on = 0;
        switch (which) {
        case CS_WHITESPACE: on = ch == ' ' || ch == '\t'; break;
        case CS_WHITESPACE_NL: on = ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' || ch == 0x0b || ch == 0x0c || ch == 0x85; break;
        case CS_NEWLINE: on = ch == '\n' || ch == '\r' || ch == 0x0b || ch == 0x0c || ch == 0x85; break;
        case CS_DIGITS: on = ch >= '0' && ch <= '9'; break;
        case CS_LETTERS: on = isalpha((int)ch) || ch >= 0x80; break; /* UTF-8 sequences count as letters */
        case CS_ALNUM: on = isalnum((int)ch) || ch >= 0x80; break;
        case CS_PUNCT: on = ch < 0x80 && ispunct((int)ch) && !strchr("$+<=>^`|~", (int)ch); break;
        case CS_UPPER: on = ch >= 'A' && ch <= 'Z'; break;
        case CS_LOWER: on = ch >= 'a' && ch <= 'z'; break;
        case CS_CONTROL: on = ch < 0x20 || ch == 0x7f; break;
        case CS_SYMBOL: on = ch < 0x80 && strchr("$+<=>^`|~", (int)ch) && ch; break;
        }
        cs_set(cs, ch, on);
    }
    if (which == CS_LETTERS || which == CS_ALNUM) rt_st32(cs + CS_FLAGS, 1);
    rt_retain(cs); /* one extra reference: an unbalanced release by a holder (NSScanner, the game) never frees it */
    std_sets[which] = cs;
    return cs;
}

/* ---- NSIndexPath ------------------------------------------------------------------------------------------------ */
enum { IP_LEN = 4, IP_IDX = 8, IP_MAX = 4, IP_IVARS = 4 + 4 * IP_MAX };

static id ip_new(const uint32_t *idx, uint32_t n) {
    id p = rt_objc_alloc(cls_indexpath);
    if (n > IP_MAX) { LOG_ONCE("collections: NSIndexPath longer than %d (truncated)", IP_MAX); n = IP_MAX; }
    rt_st32(p + IP_LEN, n);
    for (uint32_t k = 0; k < n; k++) rt_st32(p + IP_IDX + 4 * k, idx[k]);
    return p;
}
static int ip_cmp(id a, id b) {
    uint32_t na = rt_ld32(a + IP_LEN), nb = rt_ld32(b + IP_LEN);
    for (uint32_t k = 0; k < na && k < nb; k++) {
        uint32_t x = rt_ld32(a + IP_IDX + 4 * k), y = rt_ld32(b + IP_IDX + 4 * k);
        if (x != y) return x < y ? -1 : 1;
    }
    return na < nb ? -1 : na > nb;
}

/* ---- description (NSLog of collections) ------------------------------------------------------------------------- */
static int plain_word(const char *s) {
    if (!*s) return 0;
    for (; *s; s++)
        if (!isalnum((uint8_t)*s) && !strchr("_.$/:", *s) && (uint8_t)*s < 0x80) return 0;
    return 1;
}

static void quote_into(sb *b, const char *s) {
    sb_putc(b, '"');
    for (; *s; s++) {
        if (*s == '"' || *s == '\\') { sb_putc(b, '\\'); sb_putc(b, *s); }
        else if (*s == '\n') sb_puts(b, "\\n");
        else if (*s == '\t') sb_puts(b, "\\t");
        else sb_putc(b, *s);
    }
    sb_putc(b, '"');
}

static void describe(cpu_t *c, sb *b, id o, int indent) {
    if (!o) { sb_puts(b, "(null)"); return; }
    if (is_str(o)) {
        const char *s = S(o);
        if (plain_word(s)) sb_puts(b, s);
        else quote_into(b, s);
    } else if (is_num(o)) {
        char t[64];
        num_string(o, t, sizeof t);
        sb_puts(b, t);
    } else if (rt_is_kind(o, cls_array)) {
        uint32_t n = arr_n(o);
        sb_puts(b, "(\n");
        for (uint32_t k = 0; k < n; k++) {
            sb_spaces(b, 4 * (indent + 1));
            describe(c, b, arr_get(o, k), indent + 1);
            sb_puts(b, k + 1 < n ? ",\n" : "\n");
        }
        sb_spaces(b, 4 * indent);
        sb_putc(b, ')');
    } else if (rt_is_kind(o, cls_dict)) {
        uint32_t n = h_n(o);
        sb_puts(b, "{\n");
        for (uint32_t k = 0; k < n; k++) {
            sb_spaces(b, 4 * (indent + 1));
            describe(c, b, h_key(o, k), indent + 1);
            sb_puts(b, " = ");
            describe(c, b, h_val(o, k), indent + 1);
            sb_puts(b, ";\n");
        }
        sb_spaces(b, 4 * indent);
        sb_putc(b, '}');
    } else if (rt_is_kind(o, cls_set)) {
        uint32_t n = h_n(o);
        sb_puts(b, "{(\n");
        for (uint32_t k = 0; k < n; k++) {
            sb_spaces(b, 4 * (indent + 1));
            describe(c, b, h_key(o, k), indent + 1);
            sb_puts(b, k + 1 < n ? ",\n" : "\n");
        }
        sb_spaces(b, 4 * indent);
        sb_puts(b, ")}");
    } else if (rt_is_kind(o, cls_data)) {
        uint32_t n = data_len(o), p = data_bytes(o);
        sb_putc(b, '<');
        for (uint32_t k = 0; k < n; k++) {
            if (k && !(k & 3)) sb_putc(b, ' ');
            sb_printf(b, "%02x", rt_mem[p + k]);
        }
        sb_putc(b, '>');
    } else {
        id d = rt_send(c, o, "description", 0);
        const char *s = d ? rt_nsstring_utf8(d) : NULL;
        if (s) sb_puts(b, s);
        else sb_printf(b, "<%s: %#x>", rt_class_name(rt_object_class(o)), o);
    }
}

static id describe_string(cpu_t *c, id o, int indent) {
    sb b = {0};
    describe(c, &b, o, indent);
    id s = rt_nsstring(sb_str(&b));
    free(b.p);
    return s;
}

/* ---- base64 and dates (property lists) ----------------------------------------------------------------------------- */
static const char b64[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

static uint8_t *b64_decode(const char *s, size_t n, size_t *out_len) {
    uint8_t *out = malloc(n / 4 * 3 + 4);
    size_t o = 0;
    uint32_t acc = 0;
    int bits = 0;
    for (size_t k = 0; k < n; k++) {
        const char *p = s[k] ? strchr(b64, s[k]) : NULL;
        if (!p) continue; /* whitespace, '=' */
        acc = acc << 6 | (uint32_t)(p - b64);
        bits += 6;
        if (bits >= 8) { bits -= 8; out[o++] = (uint8_t)(acc >> bits); }
    }
    *out_len = o;
    return out;
}

static void b64_encode(sb *b, const uint8_t *p, size_t n, int indent) {
    size_t col = 0;
    for (size_t k = 0; k < n; k += 3) {
        uint32_t v = (uint32_t)p[k] << 16 | (k + 1 < n ? (uint32_t)p[k + 1] << 8 : 0) | (k + 2 < n ? p[k + 2] : 0);
        if (col == 0) for (int t = 0; t < indent; t++) sb_putc(b, '\t');
        char q[4] = {b64[v >> 18], b64[(v >> 12) & 63], k + 1 < n ? b64[(v >> 6) & 63] : '=', k + 2 < n ? b64[v & 63] : '='};
        sb_putn(b, q, 4);
        if ((col += 4) >= 68) { sb_putc(b, '\n'); col = 0; }
    }
    if (col) sb_putc(b, '\n');
}

static int64_t days_from_civil(int64_t y, unsigned m, unsigned d) {
    y -= m <= 2;
    int64_t era = (y >= 0 ? y : y - 399) / 400;
    unsigned yoe = (unsigned)(y - era * 400);
    unsigned doy = (153 * (m + (m > 2 ? -3 : 9)) + 2) / 5 + d - 1;
    unsigned doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + (int64_t)doe - 719468;
}

/* an NSDate (retained) for seconds since 2001-01-01, through the class system.c defines; a string if none */
static id make_date(cpu_t *c, double secs, const char *text) {
    id cls = rt_class("NSDate");
    if (cls && rt_responds(cls, "dateWithTimeIntervalSinceReferenceDate:")) {
        uint64_t u;
        memcpy(&u, &secs, 8);
        id d = rt_send(c, cls, "dateWithTimeIntervalSinceReferenceDate:", 2, (uint32_t)u, (uint32_t)(u >> 32));
        if (d) return rt_retain(d);
    }
    LOG_ONCE("collections: property list date without NSDate (kept as a string)");
    return rt_nsstring_new(text ? text : "");
}

static id iso_date(cpu_t *c, const char *s) {
    int y = 2001, mo = 1, d = 1, h = 0, mi = 0, se = 0;
    sscanf(s, "%d-%d-%dT%d:%d:%d", &y, &mo, &d, &h, &mi, &se);
    double secs = (double)(days_from_civil(y, (unsigned)mo, (unsigned)d) - days_from_civil(2001, 1, 1)) * 86400.0 +
                  h * 3600.0 + mi * 60.0 + se;
    return make_date(c, secs, s);
}

/* ---- XML property lists: reading --------------------------------------------------------------------------------- */
typedef struct { const char *p, *e; cpu_t *c; int depth; } xp;

static int xp_starts(xp *x, const char *s) { size_t n = strlen(s); return (size_t)(x->e - x->p) >= n && !memcmp(x->p, s, n); }
static void xp_skip_past(xp *x, const char *s) {
    size_t n = strlen(s);
    while (x->p < x->e && !xp_starts(x, s)) x->p++;
    x->p = x->p + n <= x->e ? x->p + n : x->e;
}
static void xp_skip(xp *x) {
    for (;;) {
        while (x->p < x->e && isspace((uint8_t)*x->p)) x->p++;
        if (xp_starts(x, "<?")) xp_skip_past(x, "?>");
        else if (xp_starts(x, "<!--")) xp_skip_past(x, "-->");
        else if (xp_starts(x, "<!")) xp_skip_past(x, ">");
        else break;
    }
}

/* read a tag at the cursor: <name ...>, </name> or <name/> */
static int xp_tag(xp *x, char *name, size_t cap, int *closing, int *empty) {
    xp_skip(x);
    if (x->p >= x->e || *x->p != '<') return 0;
    x->p++;
    *closing = x->p < x->e && *x->p == '/';
    if (*closing) x->p++;
    size_t n = 0;
    while (x->p < x->e && !isspace((uint8_t)*x->p) && *x->p != '>' && *x->p != '/') {
        if (n + 1 < cap) name[n++] = *x->p;
        x->p++;
    }
    name[n] = 0;
    *empty = 0;
    while (x->p < x->e && *x->p != '>') { if (*x->p == '/') *empty = 1; else if (!isspace((uint8_t)*x->p)) *empty = 0; x->p++; }
    if (x->p < x->e) x->p++;
    return 1;
}

/* the text up to the closing tag (entities decoded, malloc'd); consumes the closing tag */
static char *xp_text(xp *x) {
    sb b = {0};
    sb_putn(&b, "", 0);
    while (x->p < x->e && !xp_starts(x, "</")) {
        if (xp_starts(x, "<![CDATA[")) {
            x->p += 9;
            const char *s = x->p;
            while (x->p < x->e && !xp_starts(x, "]]>")) x->p++;
            sb_putn(&b, s, (size_t)(x->p - s));
            if (x->p < x->e) x->p += 3;
            continue;
        }
        if (*x->p == '&') {
            const char *semi = memchr(x->p, ';', (size_t)(x->e - x->p));
            if (semi && semi - x->p < 12) {
                char ent[16];
                size_t n = (size_t)(semi - x->p - 1);
                memcpy(ent, x->p + 1, n);
                ent[n] = 0;
                uint32_t u = 0;
                if (!strcmp(ent, "lt")) u = '<';
                else if (!strcmp(ent, "gt")) u = '>';
                else if (!strcmp(ent, "amp")) u = '&';
                else if (!strcmp(ent, "quot")) u = '"';
                else if (!strcmp(ent, "apos")) u = '\'';
                else if (ent[0] == '#') u = (uint32_t)strtoul(ent + 1 + (ent[1] == 'x'), NULL, ent[1] == 'x' ? 16 : 10);
                if (u) { sb_utf8(&b, u); x->p = semi + 1; continue; }
            }
        }
        sb_putc(&b, *x->p++);
    }
    xp_skip_past(x, ">");
    return b.p;
}

static id xp_value(xp *x);

/* parse after an opening <dict> / <array>: entries until the closing tag */
static id xp_container(xp *x, int dict) {
    cpu_t *c = x->c;
    id o = rt_objc_alloc(dict ? cls_mdict : cls_marray);
    for (;;) {
        xp_skip(x);
        if (x->p >= x->e) break;
        if (xp_starts(x, "</")) { xp_skip_past(x, ">"); break; }
        if (dict) {
            char name[32];
            int closing, empty;
            if (!xp_tag(x, name, sizeof name, &closing, &empty)) break;
            if (strcmp(name, "key")) { rt_log("collections: plist: <%s> where a <key> belongs", name); break; }
            char *k = empty ? strdup("") : xp_text(x);
            id key = rt_nsstring_new(k);
            free(k);
            id v = xp_value(x);
            if (v) h_put(c, o, key, v);
            rt_release(c, key);
            rt_release(c, v);
            if (!v) break;
        } else {
            id v = xp_value(x);
            if (!v) break;
            arr_add(o, v);
            rt_release(c, v);
        }
    }
    return o;
}

/* one value (retained), or nil */
static id xp_value(xp *x) {
    char name[32];
    int closing, empty;
    if (++x->depth > 256 || !xp_tag(x, name, sizeof name, &closing, &empty) || closing) { x->depth--; return 0; }
    id r = 0;
    char *t;
    if (!strcmp(name, "plist")) {
        r = empty ? 0 : xp_value(x);
        xp_skip(x);
        if (xp_starts(x, "</")) xp_skip_past(x, ">");
    } else if (!strcmp(name, "dict") || !strcmp(name, "array")) {
        int dict = name[0] == 'd';
        r = empty ? rt_objc_alloc(dict ? cls_mdict : cls_marray) : xp_container(x, dict);
    } else if (!strcmp(name, "string") || !strcmp(name, "key")) {
        t = empty ? strdup("") : xp_text(x);
        r = rt_nsstring_new(t);
        free(t);
    } else if (!strcmp(name, "integer")) {
        t = empty ? strdup("0") : xp_text(x);
        const char *s = t;
        while (isspace((uint8_t)*s)) s++;
        if (*s == '-') r = num_new(NK_LONGLONG, strtoll(s, NULL, 0), 0);
        else {
            unsigned long long u = strtoull(s, NULL, 0);
            r = num_new(u > (unsigned long long)INT64_MAX ? NK_ULONGLONG : NK_LONGLONG, (int64_t)u, 0);
        }
        free(t);
    } else if (!strcmp(name, "real")) {
        t = empty ? strdup("0") : xp_text(x);
        r = num_new(NK_DOUBLE, 0, strtod(t, NULL));
        free(t);
    } else if (!strcmp(name, "true") || !strcmp(name, "false")) {
        if (!empty) free(xp_text(x));
        r = num_new(NK_BOOL, name[0] == 't', 0);
    } else if (!strcmp(name, "data")) {
        t = empty ? strdup("") : xp_text(x);
        size_t n;
        uint8_t *bytes = b64_decode(t, strlen(t), &n);
        r = data_fill(rt_objc_alloc(cls_mdata), bytes, (uint32_t)n);
        free(bytes);
        free(t);
    } else if (!strcmp(name, "date")) {
        t = empty ? strdup("") : xp_text(x);
        r = iso_date(x->c, t);
        free(t);
    } else {
        rt_log("collections: plist: unknown element <%s>", name);
        if (!empty) free(xp_text(x));
    }
    x->depth--;
    return r;
}

/* ---- binary property lists: reading ------------------------------------------------------------------------------ */
typedef struct { const uint8_t *d; size_t n; int osz, rsz; uint64_t nobj, otab; cpu_t *c; int depth; } bp;

static uint64_t be_uint(const uint8_t *p, int n) {
    uint64_t v = 0;
    for (int k = 0; k < n; k++) v = v << 8 | p[k];
    return v;
}

static id bp_obj(bp *b, uint64_t ref);

/* object count of a marker byte at `*off` (0xF: an integer object follows) */
static int bp_count(bp *b, size_t *off, uint64_t *count) {
    uint8_t m = b->d[*off];
    (*off)++;
    if ((m & 15) != 15) { *count = m & 15; return 1; }
    if (*off >= b->n || (b->d[*off] & 0xf0) != 0x10) return 0;
    int sz = 1 << (b->d[*off] & 15);
    if (*off + 1 + (size_t)sz > b->n) return 0;
    *count = be_uint(b->d + *off + 1, sz);
    *off += 1 + (size_t)sz;
    return 1;
}

static id bp_obj(bp *b, uint64_t ref) {
    cpu_t *c = b->c;
    if (ref >= b->nobj || b->depth > 256) return 0;
    size_t ot = (size_t)(b->otab + ref * (uint64_t)b->osz);
    if (ot + (size_t)b->osz > b->n) return 0;
    size_t off = (size_t)be_uint(b->d + ot, b->osz);
    if (off >= b->n) return 0;
    uint8_t m = b->d[off], hi = m >> 4;
    uint64_t cnt;
    id r = 0;
    b->depth++;
    switch (hi) {
    case 0x0:
        if (m == 0x08 || m == 0x09) r = num_new(NK_BOOL, m == 0x09, 0);
        break;
    case 0x1: {
        int sz = 1 << (m & 15);
        if (off + 1 + (size_t)sz > b->n) break;
        const uint8_t *p = b->d + off + 1;
        if (sz > 8) { p += sz - 8; sz = 8; }
        uint64_t v = be_uint(p, sz);
        r = num_new(NK_LONGLONG, (int64_t)v, 0); /* 1, 2 and 4-byte integers are unsigned, 8-byte signed */
        break;
    }
    case 0x2: {
        int sz = 1 << (m & 15);
        if (off + 1 + (size_t)sz > b->n) break;
        uint64_t v = be_uint(b->d + off + 1, sz);
        double d;
        if (sz == 4) { uint32_t u = (uint32_t)v; float f; memcpy(&f, &u, 4); d = f; }
        else memcpy(&d, &v, 8);
        r = num_new(sz == 4 ? NK_FLOAT : NK_DOUBLE, 0, d);
        break;
    }
    case 0x3: {
        if (off + 9 > b->n) break;
        uint64_t v = be_uint(b->d + off + 1, 8);
        double d;
        memcpy(&d, &v, 8);
        r = make_date(c, d, "");
        break;
    }
    case 0x4: case 0x5: case 0x6: {
        if (!bp_count(b, &off, &cnt)) break;
        uint64_t bytes = hi == 0x6 ? cnt * 2 : cnt;
        if (off + bytes > b->n) break;
        if (hi == 0x4) r = data_fill(rt_objc_alloc(cls_mdata), b->d + off, (uint32_t)bytes);
        else if (hi == 0x5) r = str_new_n((const char *)b->d + off, (size_t)bytes);
        else {
            char *t = decode_text(b->d + off, (size_t)bytes, ENC_UTF16BE, NULL);
            r = rt_nsstring_new(t);
            free(t);
        }
        break;
    }
    case 0x8: { /* UID */
        int sz = (m & 15) + 1;
        if (sz > 8 || off + 1 + (size_t)sz > b->n) break;
        r = num_new(NK_LONGLONG, (int64_t)be_uint(b->d + off + 1, sz), 0);
        break;
    }
    case 0xa: case 0xc: case 0xd: {
        if (!bp_count(b, &off, &cnt)) break;
        uint64_t nrefs = hi == 0xd ? cnt * 2 : cnt;
        if (off + nrefs * (uint64_t)b->rsz > b->n) break;
        r = rt_objc_alloc(hi == 0xa ? cls_marray : hi == 0xc ? cls_mset : cls_mdict);
        for (uint64_t k = 0; k < cnt; k++) {
            id v = bp_obj(b, be_uint(b->d + off + (size_t)(k * (uint64_t)b->rsz), b->rsz));
            if (hi == 0xd) {
                id val = bp_obj(b, be_uint(b->d + off + (size_t)((k + cnt) * (uint64_t)b->rsz), b->rsz));
                if (v && val) h_put(c, r, v, val);
                rt_release(c, val);
            } else if (v) {
                if (hi == 0xa) arr_add(r, v);
                else if (h_find(r, v) < 0) h_put(c, r, v, 0);
            }
            rt_release(c, v);
        }
        break;
    }
    default:
        rt_log("collections: bplist: unsupported object type %#x", m);
        break;
    }
    b->depth--;
    return r;
}

static id bplist_parse(cpu_t *c, const uint8_t *d, size_t n) {
    if (n < 40) return 0;
    const uint8_t *t = d + n - 32;
    bp b = {d, n, t[6], t[7], be_uint(t + 8, 8), be_uint(t + 24, 8), c, 0};
    uint64_t top = be_uint(t + 16, 8);
    if (b.osz < 1 || b.osz > 8 || b.rsz < 1 || b.rsz > 8 || b.otab >= n) return 0;
    return bp_obj(&b, top);
}

/* ---- old-style (ASCII / .strings) property lists ------------------------------------------------------------------ */
typedef struct { const char *p, *e; cpu_t *c; int depth; } ap;

static void ap_ws(ap *x) {
    for (;;) {
        while (x->p < x->e && isspace((uint8_t)*x->p)) x->p++;
        if (x->e - x->p >= 2 && x->p[0] == '/' && x->p[1] == '/') { while (x->p < x->e && *x->p != '\n') x->p++; }
        else if (x->e - x->p >= 2 && x->p[0] == '/' && x->p[1] == '*') {
            x->p += 2;
            while (x->e - x->p >= 2 && !(x->p[0] == '*' && x->p[1] == '/')) x->p++;
            x->p = x->e - x->p >= 2 ? x->p + 2 : x->e;
        } else break;
    }
}
static int ap_word_char(char ch) { return isalnum((uint8_t)ch) || strchr("_$+/:.-", ch) || (uint8_t)ch >= 0x80; }

static id ap_value(ap *x);

static id ap_string(ap *x) {
    sb b = {0};
    sb_putn(&b, "", 0);
    if (*x->p == '"' || *x->p == '\'') {
        char q = *x->p++;
        while (x->p < x->e && *x->p != q) {
            char ch = *x->p++;
            if (ch == '\\' && x->p < x->e) {
                ch = *x->p++;
                switch (ch) {
                case 'n': ch = '\n'; break;
                case 't': ch = '\t'; break;
                case 'r': ch = '\r'; break;
                case 'U': case 'u': {
                    uint32_t u = 0;
                    for (int k = 0; k < 4 && x->p < x->e && isxdigit((uint8_t)*x->p); k++)
                        u = u * 16 + (uint32_t)(isdigit((uint8_t)*x->p) ? *x->p - '0' : (tolower((uint8_t)*x->p) - 'a' + 10)), x->p++;
                    sb_utf8(&b, u);
                    continue;
                }
                default: break;
                }
            }
            sb_putc(&b, ch);
        }
        if (x->p < x->e) x->p++;
    } else {
        while (x->p < x->e && ap_word_char(*x->p)) sb_putc(&b, *x->p++);
    }
    id s = rt_nsstring_new(b.p);
    free(b.p);
    return s;
}

/* entries `key = value;` until `end` (or the end of the text when end is 0) */
static id ap_dict_body(ap *x, char end) {
    cpu_t *c = x->c;
    id d = rt_objc_alloc(cls_mdict);
    for (;;) {
        ap_ws(x);
        if (x->p >= x->e) break;
        if (end && *x->p == end) { x->p++; break; }
        id k = ap_value(x);
        if (!k) break;
        ap_ws(x);
        id v;
        if (x->p < x->e && *x->p == '=') { x->p++; v = ap_value(x); }
        else v = rt_retain(k); /* "key;" in .strings files */
        if (v) h_put(c, d, k, v);
        rt_release(c, k);
        rt_release(c, v);
        ap_ws(x);
        if (x->p < x->e && *x->p == ';') x->p++;
        else if (!v) break;
    }
    return d;
}

static id ap_value(ap *x) {
    cpu_t *c = x->c;
    ap_ws(x);
    if (x->p >= x->e || ++x->depth > 256) return 0;
    id r = 0;
    char ch = *x->p;
    if (ch == '{') { x->p++; r = ap_dict_body(x, '}'); }
    else if (ch == '(') {
        x->p++;
        r = rt_objc_alloc(cls_marray);
        for (;;) {
            ap_ws(x);
            if (x->p >= x->e) break;
            if (*x->p == ')') { x->p++; break; }
            id v = ap_value(x);
            if (!v) break;
            arr_add(r, v);
            rt_release(c, v);
            ap_ws(x);
            if (x->p < x->e && *x->p == ',') x->p++;
        }
    } else if (ch == '<') {
        x->p++;
        sb b = {0};
        int nib = -1;
        while (x->p < x->e && *x->p != '>') {
            char h = *x->p++;
            if (!isxdigit((uint8_t)h)) continue;
            int v = isdigit((uint8_t)h) ? h - '0' : tolower((uint8_t)h) - 'a' + 10;
            if (nib < 0) nib = v;
            else { sb_putc(&b, (char)(nib << 4 | v)); nib = -1; }
        }
        if (x->p < x->e) x->p++;
        r = data_fill(rt_objc_alloc(cls_mdata), b.p ? b.p : "", (uint32_t)b.n);
        free(b.p);
    } else if (ch == '"' || ch == '\'' || ap_word_char(ch)) {
        r = ap_string(x);
    }
    x->depth--;
    return r;
}

static id ascii_plist_parse(cpu_t *c, const char *s, size_t n) {
    ap x = {s, s + n, c, 0};
    ap_ws(&x);
    if (x.p < x.e && *x.p != '{' && *x.p != '(' && *x.p != '<') {
        /* a .strings file: dictionary entries without braces, or a single string */
        ap probe = x;
        id k = ap_value(&probe);
        ap_ws(&probe);
        int is_dict = probe.p < probe.e && (*probe.p == '=' || *probe.p == ';');
        rt_release(c, k);
        if (is_dict) return ap_dict_body(&x, 0);
    }
    return ap_value(&x);
}

/* any property list in memory (retained), or nil */
static id plist_parse(cpu_t *c, const uint8_t *d, size_t n) {
    if (n >= 8 && !memcmp(d, "bplist00", 8)) return bplist_parse(c, d, n);
    /* text: XML or old-style, maybe UTF-16 */
    char *t = decode_text(d, n, ENC_UTF8, NULL);
    const char *s = t;
    while (isspace((uint8_t)*s)) s++;
    id r;
    if (*s == '<' && (s[1] == '?' || s[1] == '!' || !strncmp(s, "<plist", 6))) {
        xp x = {s, s + strlen(s), c, 0};
        r = xp_value(&x);
    } else {
        r = ascii_plist_parse(c, s, strlen(s));
    }
    free(t);
    return r;
}

static id plist_read_file(cpu_t *c, const char *gpath) {
    size_t n;
    uint8_t *d = file_read(gpath, &n);
    if (!d) return 0;
    id r = plist_parse(c, d, n);
    free(d);
    if (!r) rt_log("collections: %s is not a property list", gpath);
    return r;
}

/* ---- XML property lists: writing ------------------------------------------------------------------------------------ */
static void xml_escape(sb *b, const char *s) {
    for (; *s; s++) {
        if (*s == '<') sb_puts(b, "&lt;");
        else if (*s == '>') sb_puts(b, "&gt;");
        else if (*s == '&') sb_puts(b, "&amp;");
        else sb_putc(b, *s);
    }
}
static void tabs(sb *b, int n) { for (int k = 0; k < n; k++) sb_putc(b, '\t'); }

static int plist_write(cpu_t *c, sb *b, id o, int depth) {
    if (!o || depth > 256) return 0;
    if (is_str(o)) {
        tabs(b, depth); sb_puts(b, "<string>"); xml_escape(b, S(o)); sb_puts(b, "</string>\n");
    } else if (is_num(o)) {
        uint32_t k = rt_ld32(o + V_KIND);
        char t[64];
        tabs(b, depth);
        if (k == NK_BOOL) sb_puts(b, num_i(o) ? "<true/>\n" : "<false/>\n");
        else if (num_is_float(o)) { snprintf(t, sizeof t, "%.17g", num_d(o)); sb_printf(b, "<real>%s</real>\n", t); }
        else { num_string(o, t, sizeof t); sb_printf(b, "<integer>%s</integer>\n", t); }
    } else if (rt_is_kind(o, cls_array)) {
        uint32_t n = arr_n(o);
        tabs(b, depth);
        if (!n) { sb_puts(b, "<array/>\n"); return 1; }
        sb_puts(b, "<array>\n");
        for (uint32_t k = 0; k < n; k++)
            if (!plist_write(c, b, arr_get(o, k), depth + 1)) return 0;
        tabs(b, depth); sb_puts(b, "</array>\n");
    } else if (rt_is_kind(o, cls_dict)) {
        uint32_t n = h_n(o);
        tabs(b, depth);
        if (!n) { sb_puts(b, "<dict/>\n"); return 1; }
        sb_puts(b, "<dict>\n");
        for (uint32_t k = 0; k < n; k++) {
            id key = h_key(o, k);
            if (!is_str(key)) { rt_log("collections: plist: a dictionary key is not a string"); return 0; }
            tabs(b, depth + 1); sb_puts(b, "<key>"); xml_escape(b, S(key)); sb_puts(b, "</key>\n");
            if (!plist_write(c, b, h_val(o, k), depth + 1)) return 0;
        }
        tabs(b, depth); sb_puts(b, "</dict>\n");
    } else if (rt_is_kind(o, cls_data)) {
        tabs(b, depth); sb_puts(b, "<data>\n");
        b64_encode(b, rt_mem + data_bytes(o), data_len(o), depth);
        tabs(b, depth); sb_puts(b, "</data>\n");
    } else if (rt_class("NSDate") && rt_is_kind(o, rt_class("NSDate"))) {
        /* the date's -description is "YYYY-MM-DD HH:MM:SS +0000" */
        const char *d = rt_objc_describe(c, o);
        int y, mo, dd, h, mi, s;
        if (sscanf(d, "%d-%d-%d %d:%d:%d", &y, &mo, &dd, &h, &mi, &s) != 6) return 0;
        tabs(b, depth);
        sb_printf(b, "<date>%04d-%02d-%02dT%02d:%02d:%02dZ</date>\n", y, mo, dd, h, mi, s);
    } else {
        rt_log("collections: plist: cannot write a %s", rt_class_name(rt_object_class(o)));
        return 0;
    }
    return 1;
}

static int plist_write_file(cpu_t *c, id o, const char *gpath, int atomic) {
    sb b = {0};
    sb_puts(&b, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                "<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n"
                "<plist version=\"1.0\">\n");
    int ok = plist_write(c, &b, o, 0);
    sb_puts(&b, "</plist>\n");
    if (ok) ok = file_write(gpath, b.p, b.n, atomic);
    free(b.p);
    return ok;
}

/* ---- fast enumeration --------------------------------------------------------------------------------------------- */
/* countByEnumeratingWithState:(state *)st objects:(id *)buf count:(NSUInteger)len over a block of ids */
static uint32_t fast_enum(cpu_t *c, id self, uint32_t items, uint32_t n, uint32_t mut_off) {
    uint32_t st = ARG(0), buf = ARG(1), len = ARG(2);
    uint32_t k = rt_ld32(st), cnt = 0;
    rt_st32(st + 4, buf);
    rt_st32(st + 8, self + mut_off);
    while (k < n && cnt < len) {
        rt_st32(buf + 4 * cnt, rt_ld32(items + 4 * k));
        k++;
        cnt++;
    }
    rt_st32(st, k);
    return cnt;
}

/* ---- sorting ------------------------------------------------------------------------------------------------------ */
typedef struct { cpu_t *c; int fn; uint32_t sel_or_fn, ctx; } cmpctx;

static int32_t cmp_call(cmpctx *x, id a, id b) {
    if (x->fn) return (int32_t)rt_call(x->c, x->sel_or_fn, 3, a, b, x->ctx);
    return (int32_t)rt_send(x->c, a, rt_sel_name(x->sel_or_fn), 1, b);
}

static void msort(cmpctx *x, uint32_t *v, uint32_t *tmp, uint32_t n) {
    if (n < 2) return;
    uint32_t h = n / 2;
    msort(x, v, tmp, h);
    msort(x, v + h, tmp, n - h);
    uint32_t i = 0, j = h, o = 0;
    while (i < h && j < n) tmp[o++] = cmp_call(x, v[i], v[j]) > 0 ? v[j++] : v[i++]; /* stable */
    while (i < h) tmp[o++] = v[i++];
    while (j < n) tmp[o++] = v[j++];
    memcpy(v, tmp, 4 * (size_t)n);
}

/* sort an array's items in place */
static void arr_sort(cmpctx *x, id a) {
    uint32_t n = arr_n(a);
    if (n < 2) return;
    uint32_t *v = malloc(8 * (size_t)n);
    memcpy(v, rt_mem + arr_items(a), 4 * (size_t)n);
    msort(x, v, v + n, n);
    memcpy(rt_mem + arr_items(a), v, 4 * (size_t)n);
    free(v);
    bump(a, A_MUT);
}

/* ================================================================================================================ */
/* NSArray methods                                                                                                  */
/* ================================================================================================================ */
M(a_array) { RET(rt_autorelease(arr_alloc(RECV_CLASS()))); }
M(a_with_object) { id a = arr_alloc(RECV_CLASS()); if (ARG(0)) arr_add(a, ARG(0)); RET(rt_autorelease(a)); }
M(a_with_objects) { id a = arr_alloc(RECV_CLASS()); add_varargs(c, a, 2); RET(rt_autorelease(a)); }
M(a_with_objects_count) {
    id a = arr_alloc(RECV_CLASS());
    uint32_t p = ARG(0), n = ARG(1);
    for (uint32_t k = 0; k < n; k++) if (rt_ld32(p + 4 * k)) arr_add(a, rt_ld32(p + 4 * k));
    RET(rt_autorelease(a));
}
M(a_with_array) { RET(rt_autorelease(arr_copy_of(RECV_CLASS(), rt_nsarray_count(ARG(0)) ? ARG(0) : 0))); }
M(a_with_capacity) { id a = arr_alloc(RECV_CLASS()); arr_reserve(a, ARG(0) < 65536 ? ARG(0) : 65536); RET(rt_autorelease(a)); }
M(a_with_file) {
    id cls = RECV_CLASS();
    id p = plist_read_file(c, rt_nsstring_utf8(ARG(0)));
    if (p && !rt_is_kind(p, cls_array)) { rt_release(c, p); p = 0; }
    if (p && cls != cls_marray) { id a = arr_copy_of(cls, p); rt_release(c, p); p = a; }
    RET(p ? rt_autorelease(p) : 0);
}

M(a_init) { (void)c; }
M(a_init_objects) { id self = SELF; add_varargs(c, self, 2); RET(self); }
M(a_init_objects_count) {
    id self = SELF;
    uint32_t p = ARG(0), n = ARG(1);
    for (uint32_t k = 0; k < n; k++) if (rt_ld32(p + 4 * k)) arr_add(self, rt_ld32(p + 4 * k));
    RET(self);
}
M(a_init_array) {
    id self = SELF, src = ARG(0);
    uint32_t n = rt_nsarray_count(src);
    for (uint32_t k = 0; k < n; k++) arr_add(self, arr_get(src, k));
    RET(self);
}
M(a_init_capacity) { arr_reserve(SELF, ARG(0) < 65536 ? ARG(0) : 65536); }
M(a_init_file) {
    id self = SELF;
    id p = plist_read_file(c, rt_nsstring_utf8(ARG(0)));
    if (!p || !rt_is_kind(p, cls_array)) { rt_release(c, p); rt_release(c, self); RET(0); return; }
    for (uint32_t k = 0; k < arr_n(p); k++) arr_add(self, arr_get(p, k));
    rt_release(c, p);
    RET(self);
}

M(a_count) { RET(arr_n(SELF)); }
M(a_object_at) {
    id self = SELF;
    uint32_t k = ARG(0);
    if (k >= arr_n(self)) {
        rt_log("collections: -[NSArray objectAtIndex:]: index %u beyond bounds [0 .. %d] (returns nil)", k, (int)arr_n(self) - 1);
        RET(0);
        return;
    }
    RET(arr_get(self, k));
}
M(a_last) { id self = SELF; uint32_t n = arr_n(self); RET(n ? arr_get(self, n - 1) : 0); }
M(a_first) { id self = SELF; RET(arr_n(self) ? arr_get(self, 0) : 0); }
M(a_index_of) {
    id self = SELF, o = ARG(0);
    for (uint32_t k = 0; k < arr_n(self); k++)
        if (obj_eq(c, arr_get(self, k), o)) { RET(k); return; }
    RET(NSNotFound);
}
M(a_index_identical) {
    id self = SELF, o = ARG(0);
    for (uint32_t k = 0; k < arr_n(self); k++)
        if (arr_get(self, k) == o) { RET(k); return; }
    RET(NSNotFound);
}
M(a_contains) {
    id self = SELF, o = ARG(0);
    for (uint32_t k = 0; k < arr_n(self); k++)
        if (obj_eq(c, arr_get(self, k), o)) { RET(1); return; }
    RET(0);
}
M(a_get_objects) { /* getObjects: (all) and getObjects:range: */
    id self = SELF;
    uint32_t dst = ARG(0), loc = 0, len = arr_n(self);
    if (!strcmp(rt_sel_name(c->r[1]), "getObjects:range:")) { loc = ARG(1); len = ARG(2); }
    for (uint32_t k = 0; k < len && loc + k < arr_n(self); k++) rt_st32(dst + 4 * k, arr_get(self, loc + k));
}

static id enum_new(id snapshot_retained, int reverse);
M(a_object_enum) { RET(rt_autorelease(enum_new(arr_copy_of(cls_array, SELF), 0))); }
M(a_reverse_enum) { RET(rt_autorelease(enum_new(arr_copy_of(cls_array, SELF), 1))); }
M(a_fast_enum) { id self = SELF; RET(fast_enum(c, self, arr_items(self), arr_n(self), A_MUT)); }

M(a_adding_object) {
    id a = arr_copy_of(cls_array, SELF);
    if (ARG(0)) arr_add(a, ARG(0));
    RET(rt_autorelease(a));
}
M(a_adding_array) {
    id a = arr_copy_of(cls_array, SELF), o = ARG(0);
    for (uint32_t k = 0; k < rt_nsarray_count(o); k++) arr_add(a, arr_get(o, k));
    RET(rt_autorelease(a));
}
M(a_subarray) { /* subarrayWithRange:(NSRange) in two words */
    id self = SELF, a = arr_alloc(cls_array);
    uint32_t loc = ARG(0), len = ARG(1), n = arr_n(self);
    if (loc > n || len > n - loc) rt_log("collections: -[NSArray subarrayWithRange:] {%u, %u} beyond %u", loc, len, n);
    for (uint32_t k = loc; k < n && k - loc < len; k++) arr_add(a, arr_get(self, k));
    RET(rt_autorelease(a));
}
M(a_joined) {
    id self = SELF;
    const char *sep = S(ARG(0));
    sb b = {0};
    sb_putn(&b, "", 0);
    for (uint32_t k = 0; k < arr_n(self); k++) {
        if (k) sb_puts(&b, sep);
        id o = arr_get(self, k);
        if (is_str(o)) sb_puts(&b, S(o));
        else { sb t = {0}; describe(c, &t, o, 0); sb_puts(&b, sb_str(&t)); free(t.p); }
    }
    RET(rt_nsstring(b.p));
    free(b.p);
}
M(a_is_equal) {
    id self = SELF, o = ARG(0);
    if (o == self) { RET(1); return; }
    if (!o || !rt_is_kind(o, cls_array) || arr_n(o) != arr_n(self)) { RET(0); return; }
    for (uint32_t k = 0; k < arr_n(self); k++)
        if (!obj_eq(c, arr_get(self, k), arr_get(o, k))) { RET(0); return; }
    RET(1);
}
M(a_hash) { RET(arr_n(SELF)); }
M(a_description) { RET(describe_string(c, SELF, 0)); }
M(a_description_indent) { RET(describe_string(c, SELF, (int)ARG(1))); } /* descriptionWithLocale:indent: */
M(a_copy) {
    id self = SELF;
    if (rt_is_kind(self, cls_marray)) RET(arr_copy_of(cls_array, self));
    else RET(rt_retain(self));
}
M(a_mutable_copy) { RET(arr_copy_of(cls_marray, SELF)); }
M(a_write) { id self = SELF; RET(plist_write_file(c, self, rt_nsstring_utf8(ARG(0)), ARG(1) & 0xff)); }
M(a_perform) { /* makeObjectsPerformSelector:(withObject:) */
    id self = SELF;
    const char *sel = rt_sel_name(ARG(0));
    id arg = ARG(1);
    id snap = arr_copy_of(cls_array, self);
    for (uint32_t k = 0; k < arr_n(snap); k++) rt_send(c, arr_get(snap, k), sel, 1, arg);
    rt_release(c, snap);
}
M(a_sorted_sel) {
    id a = arr_copy_of(cls_array, SELF);
    cmpctx x = {c, 0, ARG(0), 0};
    arr_sort(&x, a);
    RET(rt_autorelease(a));
}
M(a_sorted_fn) {
    id a = arr_copy_of(cls_array, SELF);
    cmpctx x = {c, 1, ARG(0), ARG(1)};
    arr_sort(&x, a);
    RET(rt_autorelease(a));
}
M(a_dealloc) {
    id self = SELF;
    arr_clear(c, self);
    rt_free(arr_items(self));
    rt_objc_free(self);
}

/* NSMutableArray */
static int check_nil(id o, const char *what) {
    if (o) return 1;
    rt_log("collections: %s with nil (ignored)", what);
    return 0;
}
M(ma_add) { id self = SELF; if (check_nil(ARG(0), "-[NSMutableArray addObject:]")) arr_add(self, ARG(0)); }
M(ma_add_array) {
    id self = SELF, o = ARG(0);
    uint32_t n = rt_nsarray_count(o);
    for (uint32_t k = 0; k < n; k++) arr_add(self, arr_get(o, k));
}
M(ma_insert) {
    id self = SELF;
    uint32_t k = ARG(1);
    if (!check_nil(ARG(0), "-[NSMutableArray insertObject:atIndex:]")) return;
    if (k > arr_n(self)) { rt_log("collections: insertObject:atIndex: %u beyond %u (appended)", k, arr_n(self)); k = arr_n(self); }
    arr_insert(self, k, ARG(0));
}
M(ma_remove_at) {
    id self = SELF;
    uint32_t k = ARG(0);
    if (k >= arr_n(self)) { rt_log("collections: removeObjectAtIndex: %u beyond %u (ignored)", k, arr_n(self)); return; }
    arr_remove(c, self, k);
}
M(ma_remove_last) { id self = SELF; if (arr_n(self)) arr_remove(c, self, arr_n(self) - 1); }
M(ma_remove_object) {
    id self = SELF, o = ARG(0);
    rt_retain(o); /* may be held only by this array */
    for (uint32_t k = arr_n(self); k-- > 0;)
        if (obj_eq(c, arr_get(self, k), o)) arr_remove(c, self, k);
    rt_release(c, o);
}
M(ma_remove_identical) {
    id self = SELF, o = ARG(0);
    for (uint32_t k = arr_n(self); k-- > 0;)
        if (arr_get(self, k) == o) arr_remove(c, self, k);
}
M(ma_remove_in_array) {
    id self = SELF, o = ARG(0);
    rt_retain(o);
    for (uint32_t k = arr_n(self); k-- > 0;) {
        id e = arr_get(self, k);
        for (uint32_t j = 0; j < rt_nsarray_count(o); j++)
            if (obj_eq(c, e, arr_get(o, j))) { arr_remove(c, self, k); break; }
    }
    rt_release(c, o);
}
M(ma_remove_all) { arr_clear(c, SELF); }
M(ma_replace) {
    id self = SELF, o = ARG(1);
    uint32_t k = ARG(0);
    if (k >= arr_n(self) || !check_nil(o, "replaceObjectAtIndex:withObject:")) return;
    uint32_t slot = arr_items(self) + 4 * k;
    id old = rt_ld32(slot);
    rt_st32(slot, rt_retain(o));
    bump(self, A_MUT);
    rt_release(c, old);
}
M(ma_exchange) {
    id self = SELF;
    uint32_t i = ARG(0), j = ARG(1), it = arr_items(self);
    if (i >= arr_n(self) || j >= arr_n(self)) return;
    id t = rt_ld32(it + 4 * i);
    rt_st32(it + 4 * i, rt_ld32(it + 4 * j));
    rt_st32(it + 4 * j, t);
    bump(self, A_MUT);
}
M(ma_set_array) {
    id self = SELF, o = ARG(0);
    id snap = arr_copy_of(cls_array, rt_nsarray_count(o) ? o : 0);
    arr_clear(c, self);
    for (uint32_t k = 0; k < arr_n(snap); k++) arr_add(self, arr_get(snap, k));
    rt_release(c, snap);
}
M(ma_sort_sel) { id self = SELF; cmpctx x = {c, 0, ARG(0), 0}; arr_sort(&x, self); }
M(ma_sort_fn) { id self = SELF; cmpctx x = {c, 1, ARG(0), ARG(1)}; arr_sort(&x, self); }

/* ================================================================================================================ */
/* NSDictionary methods                                                                                             */
/* ================================================================================================================ */
static id dict_alloc(id cls) { return rt_objc_alloc(cls ? cls : cls_dict); }

/* nil-terminated (object, key) pairs from argument word `first` */
static void dict_varargs(cpu_t *c, id d, int first) {
    for (int k = first; k < first + 8192; k += 2) {
        id o = rt_arg(c, k);
        if (!o) break;
        id key = rt_arg(c, k + 1);
        if (key) h_put(c, d, key, o);
    }
}
static void dict_add_all(cpu_t *c, id d, id src) {
    if (!src || !rt_is_kind(src, cls_dict)) return;
    for (uint32_t k = 0; k < h_n(src); k++) h_put(c, d, h_key(src, k), h_val(src, k));
}
static void dict_objects_for_keys(cpu_t *c, id d, id objs, id keys) {
    uint32_t n = rt_nsarray_count(objs);
    if (rt_nsarray_count(keys) < n) n = rt_nsarray_count(keys);
    for (uint32_t k = 0; k < n; k++) h_put(c, d, arr_get(keys, k), arr_get(objs, k));
}

M(d_dictionary) { RET(rt_autorelease(dict_alloc(SELF))); }
M(d_with_object_key) {
    id d = dict_alloc(SELF);
    if (ARG(0) && ARG(1)) h_put(c, d, ARG(1), ARG(0));
    RET(rt_autorelease(d));
}
M(d_with_objects_keys) { id d = dict_alloc(SELF); dict_objects_for_keys(c, d, ARG(0), ARG(1)); RET(rt_autorelease(d)); }
M(d_with_objects_keys_count) {
    id d = dict_alloc(SELF);
    uint32_t o = ARG(0), kk = ARG(1), n = ARG(2);
    for (uint32_t k = 0; k < n; k++)
        if (rt_ld32(o + 4 * k) && rt_ld32(kk + 4 * k)) h_put(c, d, rt_ld32(kk + 4 * k), rt_ld32(o + 4 * k));
    RET(rt_autorelease(d));
}
M(d_with_objects_and_keys) { id d = dict_alloc(SELF); dict_varargs(c, d, 2); RET(rt_autorelease(d)); }
M(d_with_dictionary) { id d = dict_alloc(SELF); dict_add_all(c, d, ARG(0)); RET(rt_autorelease(d)); }
M(d_with_capacity) { RET(rt_autorelease(dict_alloc(SELF))); }
M(d_with_file) {
    id cls = SELF;
    id p = plist_read_file(c, rt_nsstring_utf8(ARG(0)));
    if (p && !rt_is_kind(p, cls_dict)) { rt_release(c, p); p = 0; }
    if (p && cls != cls_mdict) { id d = dict_alloc(cls); dict_add_all(c, d, p); rt_release(c, p); p = d; }
    RET(p ? rt_autorelease(p) : 0);
}

M(d_init) { (void)c; }
M(d_init_objects_and_keys) { id self = SELF; dict_varargs(c, self, 2); RET(self); }
M(d_init_dictionary) { id self = SELF; dict_add_all(c, self, ARG(0)); RET(self); }
M(d_init_objects_keys) { id self = SELF; dict_objects_for_keys(c, self, ARG(0), ARG(1)); RET(self); }
M(d_init_file) {
    id self = SELF;
    id p = plist_read_file(c, rt_nsstring_utf8(ARG(0)));
    if (!p || !rt_is_kind(p, cls_dict)) { rt_release(c, p); rt_release(c, self); RET(0); return; }
    dict_add_all(c, self, p);
    rt_release(c, p);
    RET(self);
}

M(d_count) { RET(h_n(SELF)); }
M(d_object_for_key) { id self = SELF; RET(h_get(self, ARG(0))); }
M(d_all_keys) { RET(rt_autorelease(h_list(SELF, 0))); }
M(d_all_values) { RET(rt_autorelease(h_list(SELF, 1))); }
M(d_keys_for_object) {
    id self = SELF, o = ARG(0), a = arr_alloc(cls_array);
    for (uint32_t k = 0; k < h_n(self); k++)
        if (obj_eq(c, h_val(self, k), o)) arr_add(a, h_key(self, k));
    RET(rt_autorelease(a));
}
M(d_key_enum) { RET(rt_autorelease(enum_new(h_list(SELF, 0), 0))); }
M(d_object_enum) { RET(rt_autorelease(enum_new(h_list(SELF, 1), 0))); }
M(d_fast_enum) { id self = SELF; RET(fast_enum(c, self, rt_ld32(self + H_KEYS), h_n(self), H_MUT)); }
M(d_is_equal) {
    id self = SELF, o = ARG(0);
    if (o == self) { RET(1); return; }
    if (!o || !rt_is_kind(o, cls_dict) || h_n(o) != h_n(self)) { RET(0); return; }
    for (uint32_t k = 0; k < h_n(self); k++) {
        id v = h_get(o, h_key(self, k));
        if (!v || !obj_eq(c, h_val(self, k), v)) { RET(0); return; }
    }
    RET(1);
}
M(d_hash) { RET(h_n(SELF)); }
M(d_description) { RET(describe_string(c, SELF, 0)); }
M(d_description_indent) { RET(describe_string(c, SELF, (int)ARG(1))); }
M(d_copy) {
    id self = SELF;
    if (rt_is_kind(self, cls_mdict)) { id d = dict_alloc(cls_dict); dict_add_all(c, d, self); RET(d); }
    else RET(rt_retain(self));
}
M(d_mutable_copy) { id self = SELF, d = dict_alloc(cls_mdict); dict_add_all(c, d, self); RET(d); }
M(d_write) { id self = SELF; RET(plist_write_file(c, self, rt_nsstring_utf8(ARG(0)), ARG(1) & 0xff)); }
M(d_dealloc) {
    id self = SELF;
    h_clear(c, self);
    h_free(self);
    rt_objc_free(self);
}

/* NSMutableDictionary */
M(md_set) {
    id self = SELF, o = ARG(0), key = ARG(1);
    if (!key) { rt_log("collections: setObject:forKey: with a nil key (ignored)"); return; }
    if (!o) { rt_log("collections: setObject:nil forKey:%s (ignored)", is_str(key) ? S(key) : "?"); return; }
    h_put(c, self, key, o);
}
M(md_set_value) { /* setValue:forKey: — nil removes */
    id self = SELF, o = ARG(0), key = ARG(1);
    if (!key) return;
    if (o) h_put(c, self, key, o);
    else h_remove(c, self, key);
}
M(md_remove) { id self = SELF; h_remove(c, self, ARG(0)); }
M(md_remove_keys) {
    id self = SELF, keys = ARG(0);
    for (uint32_t k = 0; k < rt_nsarray_count(keys); k++) h_remove(c, self, arr_get(keys, k));
}
M(md_remove_all) { h_clear(c, SELF); }
M(md_add_entries) { id self = SELF; dict_add_all(c, self, ARG(0)); }
M(md_set_dictionary) {
    id self = SELF, o = ARG(0);
    rt_retain(o);
    h_clear(c, self);
    dict_add_all(c, self, o);
    rt_release(c, o);
}

/* ================================================================================================================ */
/* NSSet methods                                                                                                    */
/* ================================================================================================================ */
static void set_add(cpu_t *c, id s, id o) { if (o && h_find(s, o) < 0) h_put(c, s, o, 0); }
static void set_add_array(cpu_t *c, id s, id a) {
    for (uint32_t k = 0; k < rt_nsarray_count(a); k++) set_add(c, s, arr_get(a, k));
}
static void set_add_set(cpu_t *c, id s, id o) {
    if (!o || !rt_is_kind(o, cls_set)) return;
    for (uint32_t k = 0; k < h_n(o); k++) set_add(c, s, h_key(o, k));
}
static void set_varargs(cpu_t *c, id s, int first) {
    for (int k = first; k < first + 4096; k++) {
        id o = rt_arg(c, k);
        if (!o) break;
        set_add(c, s, o);
    }
}

M(st_set) { RET(rt_autorelease(rt_objc_alloc(SELF))); }
M(st_with_object) { id s = rt_objc_alloc(SELF); set_add(c, s, ARG(0)); RET(rt_autorelease(s)); }
M(st_with_objects) { id s = rt_objc_alloc(SELF); set_varargs(c, s, 2); RET(rt_autorelease(s)); }
M(st_with_array) { id s = rt_objc_alloc(SELF); set_add_array(c, s, ARG(0)); RET(rt_autorelease(s)); }
M(st_with_set) { id s = rt_objc_alloc(SELF); set_add_set(c, s, ARG(0)); RET(rt_autorelease(s)); }
M(st_init) { (void)c; }
M(st_init_objects) { id self = SELF; set_varargs(c, self, 2); RET(self); }
M(st_init_array) { id self = SELF; set_add_array(c, self, ARG(0)); RET(self); }
M(st_init_set) { id self = SELF; set_add_set(c, self, ARG(0)); RET(self); }
M(st_count) { RET(h_n(SELF)); }
M(st_any) { id self = SELF; RET(h_n(self) ? h_key(self, 0) : 0); }
M(st_all) { RET(rt_autorelease(h_list(SELF, 0))); }
M(st_contains) { id self = SELF; RET(h_find(self, ARG(0)) >= 0); }
M(st_member) { id self = SELF; int32_t k = h_find(self, ARG(0)); RET(k >= 0 ? h_key(self, (uint32_t)k) : 0); }
M(st_enum) { RET(rt_autorelease(enum_new(h_list(SELF, 0), 0))); }
M(st_fast_enum) { id self = SELF; RET(fast_enum(c, self, rt_ld32(self + H_KEYS), h_n(self), H_MUT)); }
M(st_adding) { id self = SELF, s = rt_objc_alloc(cls_set); set_add_set(c, s, self); set_add(c, s, ARG(0)); RET(rt_autorelease(s)); }
M(st_is_equal) {
    id self = SELF, o = ARG(0);
    if (o == self) { RET(1); return; }
    if (!o || !rt_is_kind(o, cls_set) || h_n(o) != h_n(self)) { RET(0); return; }
    for (uint32_t k = 0; k < h_n(self); k++)
        if (h_find(o, h_key(self, k)) < 0) { RET(0); return; }
    RET(1);
}
M(st_intersects) {
    id self = SELF, o = ARG(0);
    if (o && rt_is_kind(o, cls_set))
        for (uint32_t k = 0; k < h_n(self); k++)
            if (h_find(o, h_key(self, k)) >= 0) { RET(1); return; }
    RET(0);
}
M(st_description) { RET(describe_string(c, SELF, 0)); }
M(st_copy) {
    id self = SELF;
    if (rt_is_kind(self, cls_mset)) { id s = rt_objc_alloc(cls_set); set_add_set(c, s, self); RET(s); }
    else RET(rt_retain(self));
}
M(st_mutable_copy) { id self = SELF, s = rt_objc_alloc(cls_mset); set_add_set(c, s, self); RET(s); }
M(st_perform) {
    id self = SELF;
    const char *sel = rt_sel_name(ARG(0));
    id arg = ARG(1), snap = h_list(self, 0);
    for (uint32_t k = 0; k < arr_n(snap); k++) rt_send(c, arr_get(snap, k), sel, 1, arg);
    rt_release(c, snap);
}
M(mst_add) { id self = SELF; if (check_nil(ARG(0), "-[NSMutableSet addObject:]")) set_add(c, self, ARG(0)); }
M(mst_add_array) { id self = SELF; set_add_array(c, self, ARG(0)); }
M(mst_union) { id self = SELF; set_add_set(c, self, ARG(0)); }
M(mst_remove) { id self = SELF; h_remove(c, self, ARG(0)); }
M(mst_remove_all) { h_clear(c, SELF); }
M(mst_minus) {
    id self = SELF, o = ARG(0);
    if (!o || !rt_is_kind(o, cls_set)) return;
    rt_retain(o);
    for (uint32_t k = 0; k < h_n(o); k++) h_remove(c, self, h_key(o, k));
    rt_release(c, o);
}
M(mst_intersect) {
    id self = SELF, o = ARG(0);
    if (!o || !rt_is_kind(o, cls_set)) return;
    for (uint32_t k = h_n(self); k-- > 0;)
        if (h_find(o, h_key(self, k)) < 0) h_remove_at(c, self, k);
}

/* ================================================================================================================ */
/* NSEnumerator                                                                                                     */
/* ================================================================================================================ */
enum { E_ARRAY = 4, E_INDEX = 8, E_REVERSE = 12, E_IVARS = 12 };

static id enum_new(id snapshot_retained, int reverse) {
    id e = rt_objc_alloc(cls_enum);
    rt_st32(e + E_ARRAY, snapshot_retained);
    rt_st32(e + E_REVERSE, (uint32_t)reverse);
    return e;
}
M(e_next) {
    id self = SELF, a = rt_ld32(self + E_ARRAY);
    uint32_t k = rt_ld32(self + E_INDEX), n = a ? arr_n(a) : 0;
    if (k >= n) { RET(0); return; }
    rt_st32(self + E_INDEX, k + 1);
    RET(arr_get(a, rt_ld32(self + E_REVERSE) ? n - 1 - k : k));
}
M(e_all) {
    id self = SELF, a = rt_ld32(self + E_ARRAY), r = arr_alloc(cls_array);
    uint32_t n = a ? arr_n(a) : 0, rev = rt_ld32(self + E_REVERSE);
    for (uint32_t k = rt_ld32(self + E_INDEX); k < n; k++) arr_add(r, arr_get(a, rev ? n - 1 - k : k));
    rt_st32(self + E_INDEX, n);
    RET(rt_autorelease(r));
}
M(e_fast_enum) { /* enumerators are fast-enumerable too: one object per call */
    id self = SELF;
    uint32_t st = ARG(0), buf = ARG(1);
    id o = rt_send(c, self, "nextObject", 0);
    rt_st32(st + 4, buf);
    rt_st32(st + 8, self + E_REVERSE); /* a word that does not change while enumerating */
    if (!o) { RET(0); return; }
    rt_st32(buf, o);
    rt_st32(st, rt_ld32(st) + 1);
    RET(1);
}
M(e_dealloc) { id self = SELF; rt_release(c, rt_ld32(self + E_ARRAY)); rt_objc_free(self); }

/* ================================================================================================================ */
/* NSValue / NSNumber                                                                                               */
/* ================================================================================================================ */
static id num_recv(cpu_t *c, int kind, int64_t i, double d) { return rt_autorelease(num_new(kind, i, d)); }
static int64_t arg64(cpu_t *c, int k) { return (int64_t)((uint64_t)ARG(k) | (uint64_t)ARG(k + 1) << 32); }

M(n_int) { RET(num_recv(c, NK_INT, (int32_t)ARG(0), 0)); }
M(n_uint) { RET(num_recv(c, NK_UINT, ARG(0), 0)); }
M(n_char) { RET(num_recv(c, NK_CHAR, (int8_t)ARG(0), 0)); }
M(n_uchar) { RET(num_recv(c, NK_INT, (uint8_t)ARG(0), 0)); }
M(n_short) { RET(num_recv(c, NK_SHORT, (int16_t)ARG(0), 0)); }
M(n_ushort) { RET(num_recv(c, NK_INT, (uint16_t)ARG(0), 0)); }
M(n_ll) { RET(num_recv(c, NK_LONGLONG, arg64(c, 0), 0)); }
M(n_ull) { RET(num_recv(c, NK_ULONGLONG, arg64(c, 0), 0)); }
M(n_float) { RET(num_recv(c, NK_FLOAT, 0, rt_farg(c, 2))); }
M(n_double) { RET(num_recv(c, NK_DOUBLE, 0, rt_darg(c, 2))); }
M(n_bool) { RET(num_recv(c, NK_BOOL, (ARG(0) & 0xff) != 0, 0)); }

M(ni_int) { RET(num_make(SELF, NK_INT, (int32_t)ARG(0), 0)); }
M(ni_uint) { RET(num_make(SELF, NK_UINT, ARG(0), 0)); }
M(ni_char) { RET(num_make(SELF, NK_CHAR, (int8_t)ARG(0), 0)); }
M(ni_short) { RET(num_make(SELF, NK_SHORT, (int16_t)ARG(0), 0)); }
M(ni_ll) { RET(num_make(SELF, NK_LONGLONG, arg64(c, 0), 0)); }
M(ni_ull) { RET(num_make(SELF, NK_ULONGLONG, arg64(c, 0), 0)); }
M(ni_float) { RET(num_make(SELF, NK_FLOAT, 0, rt_farg(c, 2))); }
M(ni_double) { RET(num_make(SELF, NK_DOUBLE, 0, rt_darg(c, 2))); }
M(ni_bool) { RET(num_make(SELF, NK_BOOL, (ARG(0) & 0xff) != 0, 0)); }

M(n_int_value) { RET((uint32_t)(int32_t)num_i(SELF)); }
M(n_uint_value) { id self = SELF; RET(num_is_float(self) ? (uint32_t)(int64_t)num_d(self) : (uint32_t)num_i(self)); }
M(n_char_value) { RET((uint32_t)(int8_t)num_i(SELF)); }
M(n_short_value) { RET((uint32_t)(int16_t)num_i(SELF)); }
M(n_ll_value) { uint64_t v = (uint64_t)num_i(SELF); c->r[0] = (uint32_t)v; c->r[1] = (uint32_t)(v >> 32); }
M(n_float_value) { rt_fret(c, (float)num_d(SELF)); }
M(n_double_value) { rt_dret(c, num_d(SELF)); }
M(n_bool_value) { id self = SELF; RET(num_is_float(self) ? num_d(self) != 0 : num_i(self) != 0); }
M(n_string_value) { char t[64]; num_string(SELF, t, sizeof t); RET(rt_nsstring(t)); }
M(n_is_equal) { id self = SELF, o = ARG(0); RET(o == self || (is_num(o) && num_eq(self, o))); }
M(n_hash) { RET(key_hash(SELF)); }
M(n_compare) {
    id self = SELF, o = ARG(0);
    RET(is_num(o) ? (uint32_t)num_cmp(self, o) : 1u);
}
M(n_copy) { RET(rt_retain(SELF)); }

static uint32_t value_size(uint32_t kind) {
    switch (kind) {
    case VK_POINTER: case VK_OBJECT: return 4;
    case VK_POINT: case VK_SIZE: case VK_RANGE: return 8;
    case VK_RECT: return 16;
    default: return 8;
    }
}
M(v_hash) { /* NSNumber hashes by value (key_hash); other values by their bytes, consistent with -isEqual: */
    id self = SELF;
    if (is_num(self)) { RET(key_hash(self)); return; }
    uint32_t h = 2166136261u ^ rt_ld32(self + V_KIND), n = value_size(rt_ld32(self + V_KIND));
    for (uint32_t k = 0; k < n; k++) h = (h ^ rt_mem[self + V_DATA + k]) * 16777619u;
    RET(h);
}
M(v_obj_ctype) {
    uint32_t k = rt_ld32(SELF + V_KIND);
    RET(objc_types[k < 24 ? k : 0]);
}
static id value_new(int kind, cpu_t *c, int first, int words) {
    id v = rt_objc_alloc(cls_value);
    rt_st32(v + V_KIND, (uint32_t)kind);
    for (int k = 0; k < words; k++) rt_st32(v + V_DATA + 4 * (uint32_t)k, rt_arg(c, first + k));
    return rt_autorelease(v);
}
M(v_pointer) { RET(value_new(VK_POINTER, c, 2, 1)); }
M(v_object) { RET(value_new(VK_OBJECT, c, 2, 1)); }
M(v_point) { RET(value_new(VK_POINT, c, 2, 2)); }
M(v_size) { RET(value_new(VK_SIZE, c, 2, 2)); }
M(v_range) { RET(value_new(VK_RANGE, c, 2, 2)); }
M(v_rect) { RET(value_new(VK_RECT, c, 2, 4)); }
M(v_pointer_value) { RET(rt_ld32(SELF + V_DATA)); }
M(v_range_value) { /* NSRange: returned through objc_msgSend_stret */
    id self = c->r[1];
    rt_st32(c->r[0], rt_ld32(self + V_DATA));
    rt_st32(c->r[0] + 4, rt_ld32(self + V_DATA + 4));
}
M(v_struct_value) { /* CGPointValue, CGSizeValue, CGRectValue: stret, r0 = result, r1 = self */
    id self = c->r[1];
    const char *sel = rt_sel_name(c->r[2]);
    uint32_t n = strstr(sel, "Rect") ? 16 : 8;
    memcpy(rt_mem + c->r[0], rt_mem + self + V_DATA, n);
}
M(v_get_value) { id self = SELF; memcpy(rt_mem + ARG(0), rt_mem + self + V_DATA, value_size(rt_ld32(self + V_KIND))); }
M(v_is_equal) {
    id self = SELF, o = ARG(0);
    if (o == self) { RET(1); return; }
    if (!o || !rt_is_kind(o, cls_value) || rt_ld32(o + V_KIND) != rt_ld32(self + V_KIND)) { RET(0); return; }
    RET(!memcmp(rt_mem + self + V_DATA, rt_mem + o + V_DATA, value_size(rt_ld32(self + V_KIND))));
}
M(n_description) {
    id self = SELF;
    if (is_num(self)) { char t[64]; num_string(self, t, sizeof t); RET(rt_nsstring(t)); return; }
    sb b = {0};
    sb_putc(&b, '<');
    for (uint32_t k = 0; k < value_size(rt_ld32(self + V_KIND)); k++) sb_printf(&b, "%02x", rt_mem[self + V_DATA + k]);
    sb_putc(&b, '>');
    RET(rt_nsstring(b.p));
    free(b.p);
}

/* NSNull */
M(null_null) { RET(null_singleton); }
M(null_description) { RET(rt_nsstring("<null>")); }
M(null_keep) { (void)c; } /* the singleton is never freed */

/* ================================================================================================================ */
/* NSData                                                                                                           */
/* ================================================================================================================ */
static id data_file(cpu_t *c, id self, id path) {
    size_t n;
    uint8_t *d = file_read(rt_nsstring_utf8(path), &n);
    if (!d) { rt_release(c, self); return 0; }
    data_fill(self, d, (uint32_t)n);
    free(d);
    return self;
}
static id data_cls(cpu_t *c) { return SELF; }

M(dt_data) { RET(rt_autorelease(data_fill(rt_objc_alloc(data_cls(c)), "", 0))); }
M(dt_with_bytes) { id d = rt_objc_alloc(data_cls(c)); uint32_t p = ARG(0), n = p ? ARG(1) : 0; RET(rt_autorelease(data_fill(d, p ? G(p) : "", n))); }
M(dt_with_bytes_nocopy) { /* dataWithBytesNoCopy:length:(freeWhenDone:) — default frees */
    id d = rt_objc_alloc(data_cls(c));
    int free_when_done = strstr(rt_sel_name(c->r[1]), "freeWhenDone") ? (int)(ARG(2) & 0xff) : 1;
    rt_st32(d + D_BYTES, ARG(0));
    rt_st32(d + D_LEN, ARG(1));
    rt_st32(d + D_CAP, ARG(1));
    rt_st32(d + D_OWNED, (uint32_t)free_when_done);
    RET(rt_autorelease(d));
}
M(dt_with_data) {
    id d = rt_objc_alloc(data_cls(c)), o = ARG(0);
    RET(rt_autorelease(data_fill(d, o ? G(data_bytes(o)) : "", o ? data_len(o) : 0)));
}
M(dt_with_file) {
    id d = data_file(c, rt_objc_alloc(data_cls(c)), ARG(0));
    RET(d ? rt_autorelease(d) : 0);
}
M(dt_with_length) { id d = rt_objc_alloc(data_cls(c)); data_fill(d, "", 0); data_set_len(d, ARG(0)); RET(rt_autorelease(d)); }
M(dt_with_capacity) { id d = rt_objc_alloc(data_cls(c)); data_reserve(d, ARG(0) ? ARG(0) : 1); RET(rt_autorelease(d)); }
/* The path of a file URL, or 0 (http and other schemes are the network's business: nothing is reachable). */
static id url_file_path(cpu_t *c, id url) {
    if (!url || !rt_responds(url, "isFileURL") || !(rt_send(c, url, "isFileURL", 0) & 0xff)) return 0;
    return rt_send(c, url, "path", 0);
}
M(dt_with_url) { /* dataWithContentsOfURL:(options:error:) */
    id path = url_file_path(c, ARG(0)), d = 0;
    if (path) d = data_file(c, rt_objc_alloc(data_cls(c)), path);
    else LOG_ONCE("collections: NSData contentsOfURL: not a file URL (returns nil)");
    if (strstr(rt_sel_name(c->r[1]), "error:")) out_obj(ARG(2), 0);
    RET(d ? rt_autorelease(d) : 0);
}

M(dti_init) { data_fill(SELF, "", 0); }
M(dti_bytes) { id self = SELF; uint32_t p = ARG(0), n = p ? ARG(1) : 0; RET(data_fill(self, p ? G(p) : "", n)); }
M(dti_bytes_nocopy) {
    id self = SELF;
    int free_when_done = strstr(rt_sel_name(c->r[1]), "freeWhenDone") ? (int)(ARG(2) & 0xff) : 1;
    rt_st32(self + D_BYTES, ARG(0));
    rt_st32(self + D_LEN, ARG(1));
    rt_st32(self + D_CAP, ARG(1));
    rt_st32(self + D_OWNED, (uint32_t)free_when_done);
    RET(self);
}
M(dti_data) { id self = SELF, o = ARG(0); RET(data_fill(self, o ? G(data_bytes(o)) : "", o ? data_len(o) : 0)); }
M(dti_file) { id self = SELF; RET(data_file(c, self, ARG(0))); }
M(dti_length) { id self = SELF; data_fill(self, "", 0); data_set_len(self, ARG(0)); RET(self); }
M(dti_capacity) { id self = SELF; data_reserve(self, ARG(0) ? ARG(0) : 1); RET(self); }
M(dti_url) {
    id self = SELF, path = url_file_path(c, ARG(0));
    if (!path) LOG_ONCE("collections: NSData initWithContentsOfURL: not a file URL (returns nil)");
    if (strstr(rt_sel_name(c->r[1]), "error:")) out_obj(ARG(2), 0);
    if (!path) { rt_release(c, self); RET(0); return; }
    RET(data_file(c, self, path));
}

M(dt_bytes) { RET(data_bytes(SELF)); }
M(dt_length) { RET(data_len(SELF)); }
M(dt_get_bytes) { /* getBytes: , getBytes:length:, getBytes:range: */
    id self = SELF;
    const char *sel = rt_sel_name(c->r[1]);
    uint32_t dst = ARG(0), loc = 0, n = data_len(self);
    if (!strcmp(sel, "getBytes:length:")) n = ARG(1) < n ? ARG(1) : n;
    else if (!strcmp(sel, "getBytes:range:")) {
        loc = ARG(1) < n ? ARG(1) : n;
        n = ARG(2) < n - loc ? ARG(2) : n - loc;
    }
    if (n) memcpy(rt_mem + dst, rt_mem + data_bytes(self) + loc, n);
}
M(dt_subdata) {
    id self = SELF;
    uint32_t n = data_len(self), loc = ARG(0) < n ? ARG(0) : n, len = ARG(1) < n - loc ? ARG(1) : n - loc;
    id d = rt_objc_alloc(cls_data);
    RET(rt_autorelease(data_fill(d, rt_mem + data_bytes(self) + loc, len)));
}
M(dt_is_equal) {
    id self = SELF, o = ARG(0);
    if (o == self) { RET(1); return; }
    if (!o || !rt_is_kind(o, cls_data) || data_len(o) != data_len(self)) { RET(0); return; }
    RET(!data_len(self) || !memcmp(rt_mem + data_bytes(self), rt_mem + data_bytes(o), data_len(self)));
}
M(dt_hash) {
    id self = SELF;
    uint32_t h = 2166136261u, n = data_len(self), p = data_bytes(self);
    for (uint32_t k = 0; k < n && k < 80; k++) h = (h ^ rt_mem[p + k]) * 16777619u;
    RET(h);
}
M(dt_write) {
    id self = SELF;
    const char *path = rt_nsstring_utf8(ARG(0));
    int atomic = ARG(1) & 0xff;
    if (!strcmp(rt_sel_name(c->r[1]), "writeToFile:options:error:")) { atomic = ARG(1) & 1; out_obj(ARG(2), 0); }
    RET(file_write(path, rt_mem + data_bytes(self), data_len(self), atomic));
}
M(dt_description) { RET(describe_string(c, SELF, 0)); }
M(dt_copy) {
    id self = SELF;
    if (rt_is_kind(self, cls_mdata) || !rt_ld32(self + D_OWNED)) RET(data_fill(rt_objc_alloc(cls_data), rt_mem + data_bytes(self), data_len(self)));
    else RET(rt_retain(self));
}
M(dt_mutable_copy) { id self = SELF; RET(data_fill(rt_objc_alloc(cls_mdata), rt_mem + data_bytes(self), data_len(self))); }
M(dt_dealloc) {
    id self = SELF;
    if (rt_ld32(self + D_OWNED)) rt_free(data_bytes(self));
    rt_objc_free(self);
}

/* NSMutableData */
M(mdt_mutable_bytes) { id self = SELF; if (!rt_ld32(self + D_OWNED)) data_reserve(self, data_len(self) ? data_len(self) : 1); RET(data_bytes(self)); }
M(mdt_append_bytes) { id self = SELF; uint32_t p = ARG(0), n = ARG(1); if (p) data_append(self, G(p), n); }
M(mdt_append_data) { id self = SELF, o = ARG(0); if (o) data_append(self, rt_mem + data_bytes(o), data_len(o)); }
M(mdt_set_length) { id self = SELF; data_set_len(self, ARG(0)); }
M(mdt_increase_length) { id self = SELF; data_set_len(self, data_len(self) + ARG(0)); }
M(mdt_set_data) { id self = SELF, o = ARG(0); data_fill(self, o ? G(data_bytes(o)) : "", o ? data_len(o) : 0); }
M(mdt_replace) { /* replaceBytesInRange:(NSRange)withBytes: (same length) */
    id self = SELF;
    uint32_t loc = ARG(0), len = ARG(1), src = ARG(2);
    if (loc + len > data_len(self)) data_set_len(self, loc + len);
    data_reserve(self, data_len(self));
    if (len && src) memmove(rt_mem + data_bytes(self) + loc, rt_mem + src, len);
}
M(mdt_reset) {
    id self = SELF;
    uint32_t loc = ARG(0), len = ARG(1);
    if (loc + len > data_len(self)) data_set_len(self, loc + len);
    data_reserve(self, data_len(self));
    memset(rt_mem + data_bytes(self) + loc, 0, len);
}

/* ================================================================================================================ */
/* NSCharacterSet                                                                                                   */
/* ================================================================================================================ */
M(cs_in_string) { id cs = rt_objc_alloc(SELF); cs_add_string(cs, S(ARG(0)), 1); RET(rt_autorelease(cs)); }
M(cs_in_range) { /* characterSetWithRange:(NSRange) */
    id cs = rt_objc_alloc(SELF);
    uint32_t loc = ARG(0), len = ARG(1);
    for (uint32_t ch = loc; ch < loc + len && ch < 256; ch++) cs_set(cs, ch, 1);
    if (loc + len > 256) rt_st32(cs + CS_FLAGS, 1);
    RET(rt_autorelease(cs));
}
#define STD_SET(fn, which) M(fn) { RET(cs_standard(which)); }
STD_SET(cs_whitespace, CS_WHITESPACE)
STD_SET(cs_whitespace_nl, CS_WHITESPACE_NL)
STD_SET(cs_newline, CS_NEWLINE)
STD_SET(cs_digits, CS_DIGITS)
STD_SET(cs_letters, CS_LETTERS)
STD_SET(cs_alnum, CS_ALNUM)
STD_SET(cs_punct, CS_PUNCT)
STD_SET(cs_upper, CS_UPPER)
STD_SET(cs_lower, CS_LOWER)
STD_SET(cs_control, CS_CONTROL)
STD_SET(cs_symbol, CS_SYMBOL)
M(cs_inverted) {
    id self = SELF, cs = rt_objc_alloc(cls_charset);
    for (uint32_t k = 0; k < 32; k++) rt_mem[cs + CS_BITS + k] = (uint8_t)~rt_mem[self + CS_BITS + k];
    rt_st32(cs + CS_FLAGS, rt_ld32(self + CS_FLAGS) ^ 1);
    RET(rt_autorelease(cs));
}
M(cs_is_member) { id self = SELF; RET(cs_has(self, ARG(0) & 0xffff)); }
M(cs_copy) {
    id self = SELF, cs = rt_objc_alloc(strstr(rt_sel_name(c->r[1]), "mutable") ? cls_mcharset : cls_charset);
    memcpy(rt_mem + cs + CS_BITS, rt_mem + self + CS_BITS, 36);
    RET(cs);
}
M(mcs_add_string) { id self = SELF; cs_add_string(self, S(ARG(0)), 1); }
M(mcs_remove_string) { id self = SELF; cs_add_string(self, S(ARG(0)), 0); }
M(mcs_add_range) {
    id self = SELF;
    uint32_t loc = ARG(0), len = ARG(1);
    for (uint32_t ch = loc; ch < loc + len && ch < 256; ch++) cs_set(self, ch, 1);
}
M(mcs_union) {
    id self = SELF, o = ARG(0);
    if (!o) return;
    for (uint32_t k = 0; k < 32; k++) rt_mem[self + CS_BITS + k] |= rt_mem[o + CS_BITS + k];
    rt_st32(self + CS_FLAGS, rt_ld32(self + CS_FLAGS) | rt_ld32(o + CS_FLAGS));
}
M(mcs_invert) {
    id self = SELF;
    for (uint32_t k = 0; k < 32; k++) rt_mem[self + CS_BITS + k] = (uint8_t)~rt_mem[self + CS_BITS + k];
    rt_st32(self + CS_FLAGS, rt_ld32(self + CS_FLAGS) ^ 1);
}

/* ================================================================================================================ */
/* NSScanner                                                                                                        */
/* ================================================================================================================ */
enum { SC_STRING = 4, SC_LOC = 8, SC_SKIP = 12, SC_ICASE = 16, SC_IVARS = 16 };

static const char *sc_text(id sc, uint32_t *n) {
    const char *s = S(rt_ld32(sc + SC_STRING));
    *n = (uint32_t)strlen(s);
    if (rt_ld32(sc + SC_LOC) > *n) rt_st32(sc + SC_LOC, *n);
    return s;
}
/* skip the characters to be skipped; returns the new location (stored) */
static uint32_t sc_skip(id sc) {
    uint32_t n, loc;
    const char *s = sc_text(sc, &n);
    id skip = rt_ld32(sc + SC_SKIP);
    for (loc = rt_ld32(sc + SC_LOC); loc < n && cs_has(skip, (uint8_t)s[loc]); loc++) { }
    rt_st32(sc + SC_LOC, loc);
    return loc;
}

/* NSScanner defaults: whitespace and newlines are skipped (the set is retained here and released in -dealloc), and
 * scanning is case-insensitive (caseSensitive is NO) */
static id sc_init(cpu_t *c, id sc, id str) {
    rt_st32(sc + SC_STRING, is_str(str) ? rt_send(c, str, "copy", 0) : rt_nsstring_new(""));
    rt_st32(sc + SC_SKIP, rt_retain(cs_standard(CS_WHITESPACE_NL)));
    rt_st32(sc + SC_ICASE, 1);
    return sc;
}
M(sc_with_string) { RET(rt_autorelease(sc_init(c, rt_objc_alloc(SELF), ARG(0)))); }
M(sc_init_string) { id self = SELF; RET(sc_init(c, self, ARG(0))); }
M(sc_string) { RET(rt_ld32(SELF + SC_STRING)); }
M(sc_location) { RET(rt_ld32(SELF + SC_LOC)); }
M(sc_set_location) { rt_st32(SELF + SC_LOC, ARG(0)); }
M(sc_skip_set) { RET(rt_ld32(SELF + SC_SKIP)); }
M(sc_set_skip) {
    id self = SELF, old = rt_ld32(self + SC_SKIP);
    rt_st32(self + SC_SKIP, rt_retain(ARG(0)));
    rt_release(c, old);
}
M(sc_set_case) { rt_st32(SELF + SC_ICASE, !(ARG(0) & 0xff)); }
M(sc_case) { RET(!rt_ld32(SELF + SC_ICASE)); }
M(sc_at_end) {
    id self = SELF;
    uint32_t n, saved = rt_ld32(self + SC_LOC);
    sc_text(self, &n);
    uint32_t loc = sc_skip(self);
    rt_st32(self + SC_LOC, saved);
    RET(loc >= n);
}

/* integers: scanInt:, scanInteger:, scanLongLong:, scanHexInt: */
static int sc_integer(id sc, int hex, int64_t *out) {
    uint32_t n, loc = sc_skip(sc);
    const char *s = sc_text(sc, &n);
    uint32_t k = loc;
    int neg = 0;
    if (!hex && k < n && (s[k] == '-' || s[k] == '+')) neg = s[k++] == '-';
    if (hex && k + 1 < n && s[k] == '0' && (s[k + 1] == 'x' || s[k + 1] == 'X') && isxdigit((uint8_t)s[k + 2])) k += 2;
    uint32_t start = k;
    uint64_t v = 0;
    int over = 0;
    while (k < n && (hex ? isxdigit((uint8_t)s[k]) : isdigit((uint8_t)s[k]))) {
        int d = isdigit((uint8_t)s[k]) ? s[k] - '0' : tolower((uint8_t)s[k]) - 'a' + 10;
        if (v > (UINT64_MAX - (uint64_t)d) / (hex ? 16 : 10)) over = 1;
        else v = v * (hex ? 16 : 10) + (uint64_t)d;
        k++;
    }
    if (k == start) return 0;
    rt_st32(sc + SC_LOC, k);
    if (over || (!hex && v > (uint64_t)INT64_MAX + neg)) v = neg ? (uint64_t)INT64_MAX + 1 : (hex ? UINT64_MAX : (uint64_t)INT64_MAX);
    *out = neg ? (int64_t)(0 - v) : (int64_t)v;
    return 1;
}
static int32_t clamp32(int64_t v) { return v > INT_MAX ? INT_MAX : v < INT_MIN ? INT_MIN : (int32_t)v; }
M(sc_int) { /* scanInt: and scanInteger: (NSInteger is 32-bit) */
    id self = SELF;
    uint32_t p = ARG(0);
    int64_t v;
    if (!sc_integer(self, 0, &v)) { RET(0); return; }
    if (p) rt_st32(p, (uint32_t)clamp32(v));
    RET(1);
}
M(sc_ll) {
    id self = SELF;
    uint32_t p = ARG(0);
    int64_t v;
    if (!sc_integer(self, 0, &v)) { RET(0); return; }
    if (p) { rt_st32(p, (uint32_t)v); rt_st32(p + 4, (uint32_t)((uint64_t)v >> 32)); }
    RET(1);
}
M(sc_hex) {
    id self = SELF;
    uint32_t p = ARG(0);
    int64_t v;
    if (!sc_integer(self, 1, &v)) { RET(0); return; }
    if (p) rt_st32(p, (uint64_t)v > 0xffffffffu ? 0xffffffffu : (uint32_t)v);
    RET(1);
}
static int sc_real(id sc, double *out) {
    uint32_t n, loc = sc_skip(sc);
    const char *s = sc_text(sc, &n);
    const char *p = s + loc;
    if (!(isdigit((uint8_t)*p) || ((*p == '-' || *p == '+' || *p == '.') && (isdigit((uint8_t)p[1]) || (p[1] == '.' && isdigit((uint8_t)p[2]))))))
        return 0;
    /* only decimal forms: no "inf", "nan" or hex floats */
    const char *q = p;
    if (*q == '-' || *q == '+') q++;
    while (isdigit((uint8_t)*q)) q++;
    if (*q == '.') { q++; while (isdigit((uint8_t)*q)) q++; }
    if ((*q == 'e' || *q == 'E') && (isdigit((uint8_t)q[1]) || ((q[1] == '-' || q[1] == '+') && isdigit((uint8_t)q[2])))) {
        q += 2;
        while (isdigit((uint8_t)*q)) q++;
    }
    char *t = malloc((size_t)(q - p) + 1);
    memcpy(t, p, (size_t)(q - p));
    t[q - p] = 0;
    *out = strtod(t, NULL);
    free(t);
    rt_st32(sc + SC_LOC, (uint32_t)(q - s));
    return 1;
}
M(sc_float) {
    id self = SELF;
    uint32_t p = ARG(0);
    double d;
    if (!sc_real(self, &d)) { RET(0); return; }
    float f = (float)d;
    if (p) memcpy(rt_mem + p, &f, 4);
    RET(1);
}
M(sc_double) {
    id self = SELF;
    uint32_t p = ARG(0);
    double d;
    if (!sc_real(self, &d)) { RET(0); return; }
    if (p) memcpy(rt_mem + p, &d, 8);
    RET(1);
}
M(sc_scan_string) { /* scanString:intoString: */
    id self = SELF;
    const char *want = S(ARG(0));
    uint32_t out = ARG(1), n, loc = sc_skip(self);
    const char *s = sc_text(self, &n);
    size_t w = strlen(want);
    int icase = rt_ld32(self + SC_ICASE);
    if (!w || loc + w > n || (icase ? strncasecmp(s + loc, want, w) : strncmp(s + loc, want, w))) { RET(0); return; }
    rt_st32(self + SC_LOC, loc + (uint32_t)w);
    if (out) out_obj(out, rt_autorelease(str_new_n(s + loc, w)));
    RET(1);
}
M(sc_up_to_string) { /* scanUpToString:intoString: */
    id self = SELF;
    const char *want = S(ARG(0));
    uint32_t out = ARG(1), n, loc = sc_skip(self);
    const char *s = sc_text(self, &n);
    if (loc >= n) { RET(0); return; }
    const char *hit = *want ? strstr(s + loc, want) : NULL;
    uint32_t end = hit ? (uint32_t)(hit - s) : n;
    if (end == loc) { RET(0); return; }
    rt_st32(self + SC_LOC, end);
    if (out) out_obj(out, rt_autorelease(str_new_n(s + loc, end - loc)));
    RET(1);
}
static void sc_set_scan(cpu_t *c, int in_set) { /* scanCharactersFromSet: / scanUpToCharactersFromSet: */
    id self = SELF, set = ARG(0);
    uint32_t out = ARG(1), n, loc = sc_skip(self);
    const char *s = sc_text(self, &n);
    uint32_t end = loc;
    while (end < n && cs_has(set, (uint8_t)s[end]) == in_set) end++;
    if (end == loc) { RET(0); return; }
    rt_st32(self + SC_LOC, end);
    if (out) out_obj(out, rt_autorelease(str_new_n(s + loc, end - loc)));
    RET(1);
}
M(sc_from_set) { sc_set_scan(c, 1); }
M(sc_up_to_set) { sc_set_scan(c, 0); }
M(sc_dealloc) {
    id self = SELF;
    rt_release(c, rt_ld32(self + SC_STRING));
    rt_release(c, rt_ld32(self + SC_SKIP));
    rt_objc_free(self);
}

/* ================================================================================================================ */
/* NSIndexPath                                                                                                      */
/* ================================================================================================================ */
M(ip_row_section) { uint32_t idx[2] = {ARG(1), ARG(0)}; RET(rt_autorelease(ip_new(idx, 2))); } /* forRow:inSection: */
M(ip_with_index) { uint32_t idx[1] = {ARG(0)}; RET(rt_autorelease(ip_new(idx, 1))); }
M(ip_with_indexes) {
    uint32_t p = ARG(0), n = ARG(1), idx[IP_MAX];
    for (uint32_t k = 0; k < n && k < IP_MAX; k++) idx[k] = rt_ld32(p + 4 * k);
    RET(rt_autorelease(ip_new(idx, n)));
}
M(ip_section) { RET(rt_ld32(SELF + IP_IDX)); }
M(ip_row) { RET(rt_ld32(SELF + IP_IDX + 4)); }
M(ip_length) { RET(rt_ld32(SELF + IP_LEN)); }
M(ip_index_at) {
    id self = SELF;
    uint32_t k = ARG(0);
    RET(k < rt_ld32(self + IP_LEN) ? rt_ld32(self + IP_IDX + 4 * k) : NSNotFound);
}
M(ip_adding) {
    id self = SELF;
    uint32_t n = rt_ld32(self + IP_LEN), idx[IP_MAX + 1];
    for (uint32_t k = 0; k < n; k++) idx[k] = rt_ld32(self + IP_IDX + 4 * k);
    idx[n] = ARG(0);
    RET(rt_autorelease(ip_new(idx, n + 1)));
}
M(ip_is_equal) { id self = SELF, o = ARG(0); RET(o && rt_is_kind(o, cls_indexpath) && !ip_cmp(self, o)); }
M(ip_compare) { id self = SELF, o = ARG(0); RET((uint32_t)(o && rt_is_kind(o, cls_indexpath) ? ip_cmp(self, o) : 1)); }
M(ip_hash) {
    id self = SELF;
    uint32_t h = 0;
    for (uint32_t k = 0; k < rt_ld32(self + IP_LEN); k++) h = h * 31 + rt_ld32(self + IP_IDX + 4 * k);
    RET(h);
}
M(ip_copy) { RET(rt_retain(SELF)); }
M(ip_description) {
    id self = SELF;
    sb b = {0};
    sb_printf(&b, "<NSIndexPath %#x> {length = %u, path = ", self, rt_ld32(self + IP_LEN));
    for (uint32_t k = 0; k < rt_ld32(self + IP_LEN); k++) sb_printf(&b, k ? " - %u" : "%u", rt_ld32(self + IP_IDX + 4 * k));
    sb_putc(&b, '}');
    RET(rt_nsstring(b.p));
    free(b.p);
}

/* ================================================================================================================ */
/* NSPredicate (minimal): "SELF <op>[c|d|cd] %@" or "SELF <op> 'literal'"                                           */
/* ================================================================================================================ */
enum { PR_OP = 4, PR_ARG = 8, PR_OPT = 12, PR_IVARS = 12 };
enum { OP_NONE, OP_MATCHES, OP_EQ, OP_NE, OP_CONTAINS, OP_BEGINS, OP_ENDS, OP_LIKE, OP_TRUE, OP_FALSE };

/* a small backtracking regular expression matcher (ICU subset): literals, ., [classes], \d \w \s escapes,
 * quantifiers * + ? {m} {m,} {m,n}, anchors ^ $. No groups or alternation. */
typedef struct { const char *re; int icase; int bad; } rx;

static int rx_class_escape(char e, uint8_t ch, int *matched) {
    switch (e) {
    case 'd': *matched = isdigit(ch) != 0; return 1;
    case 'D': *matched = !isdigit(ch); return 1;
    case 'w': *matched = isalnum(ch) || ch == '_'; return 1;
    case 'W': *matched = !(isalnum(ch) || ch == '_'); return 1;
    case 's': *matched = isspace(ch) != 0; return 1;
    case 'S': *matched = !isspace(ch); return 1;
    default: return 0;
    }
}
static char rx_escaped(char e) { return e == 'n' ? '\n' : e == 't' ? '\t' : e == 'r' ? '\r' : e; }

/* the length of the atom at re (0 at the end); *ok says whether ch matches it */
static int rx_atom(rx *x, const char *re, uint8_t ch, int *ok) {
    int icase = x->icase;
    uint8_t lc = (uint8_t)tolower(ch);
    if (*re == '(' || *re == ')' || *re == '|') { x->bad = 1; *ok = 0; return 1; }
    if (*re == '.') { *ok = ch != '\n'; return 1; }
    if (*re == '\\' && re[1]) {
        if (!rx_class_escape(re[1], ch, ok)) {
            char e = rx_escaped(re[1]);
            *ok = icase ? lc == (uint8_t)tolower((uint8_t)e) : ch == (uint8_t)e;
        }
        return 2;
    }
    if (*re == '[') {
        const char *p = re + 1;
        int neg = *p == '^';
        if (neg) p++;
        int hit = 0, first = 1;
        while (*p && (*p != ']' || first)) {
            first = 0;
            uint8_t lo;
            if (*p == '\\' && p[1]) {
                int m;
                if (rx_class_escape(p[1], ch, &m)) { hit |= m; p += 2; continue; }
                lo = (uint8_t)rx_escaped(p[1]);
                p += 2;
            } else lo = (uint8_t)*p++;
            uint8_t hi = lo;
            if (*p == '-' && p[1] && p[1] != ']') {
                p++;
                if (*p == '\\' && p[1]) { hi = (uint8_t)rx_escaped(p[1]); p += 2; }
                else hi = (uint8_t)*p++;
            }
            if (ch >= lo && ch <= hi) hit = 1;
            if (icase && ((lc >= lo && lc <= hi) || ((uint8_t)toupper(ch) >= lo && (uint8_t)toupper(ch) <= hi))) hit = 1;
        }
        if (*p != ']') { x->bad = 1; *ok = 0; return (int)(p - re); }
        *ok = hit != neg;
        return (int)(p + 1 - re);
    }
    *ok = icase ? lc == (uint8_t)tolower((uint8_t)*re) : ch == (uint8_t)*re;
    return 1;
}

/* quantifier after an atom: *len its length, min/max repetitions */
static void rx_quant(const char *q, int *len, int *min, int *max) {
    *len = 0; *min = 1; *max = 1;
    if (*q == '*') { *len = 1; *min = 0; *max = INT_MAX; }
    else if (*q == '+') { *len = 1; *min = 1; *max = INT_MAX; }
    else if (*q == '?') { *len = 1; *min = 0; *max = 1; }
    else if (*q == '{' && isdigit((uint8_t)q[1])) {
        char *e;
        long a = strtol(q + 1, &e, 10), b = a;
        if (*e == ',') { b = isdigit((uint8_t)e[1]) ? strtol(e + 1, &e, 10) : INT_MAX; if (b == INT_MAX && *e == ',') e++; }
        if (*e != '}') return;
        *len = (int)(e + 1 - q); *min = (int)a; *max = (int)b;
    }
    if (*len && (q[*len] == '?' || q[*len] == '+')) (*len)++; /* lazy/possessive: treated as greedy */
}

static int rx_here(rx *x, const char *re, const char *s) {
    if (!*re) return !*s;
    if (*re == '$' && !re[1]) return !*s;
    if (*re == '^' && re == x->re) return rx_here(x, re + 1, s);
    int ok, alen = rx_atom(x, re, 0, &ok), qlen, min, max;
    if (x->bad) return 0;
    rx_quant(re + alen, &qlen, &min, &max);
    const char *rest = re + alen + qlen;
    int n = 0;
    while (n < max && s[n]) {
        rx_atom(x, re, (uint8_t)s[n], &ok);
        if (!ok) break;
        n++;
    }
    for (; n >= min; n--)
        if (rx_here(x, rest, s + n)) return 1;
    return 0;
}

static int regex_full_match(const char *re, const char *s, int icase) {
    rx x = {re, icase, 0};
    int r = rx_here(&x, re, s);
    if (x.bad) LOG_ONCE("collections: NSPredicate MATCHES: unsupported regular expression \"%s\"", re);
    return r && !x.bad;
}

/* LIKE: * and ? wildcards */
static int like_match(const char *p, const char *s, int icase) {
    for (; *p; p++, s++) {
        if (*p == '*') {
            for (const char *t = s;; t++) { if (like_match(p + 1, t, icase)) return 1; if (!*t) return 0; }
        }
        if (!*s) return 0;
        if (*p != '?' && (icase ? tolower((uint8_t)*p) != tolower((uint8_t)*s) : *p != *s)) return 0;
    }
    return !*s;
}

static const char *strcasestr_(const char *h, const char *n) {
    size_t k = strlen(n);
    for (; *h; h++) if (!strncasecmp(h, n, k)) return h;
    return k ? NULL : h;
}

M(pr_with_format) {
    const char *f = S(ARG(0));
    id p = rt_objc_alloc(cls_predicate);
    const char *q = f;
    while (isspace((uint8_t)*q)) q++;
    if (!strcasecmp(q, "TRUEPREDICATE")) { rt_st32(p + PR_OP, OP_TRUE); RET(rt_autorelease(p)); return; }
    if (!strcasecmp(q, "FALSEPREDICATE")) { rt_st32(p + PR_OP, OP_FALSE); RET(rt_autorelease(p)); return; }
    if (strncasecmp(q, "SELF", 4)) goto unsupported;
    q += 4;
    while (isspace((uint8_t)*q)) q++;
    static const struct { const char *name; int op; } ops[] = {
        {"MATCHES", OP_MATCHES}, {"==", OP_EQ}, {"!=", OP_NE}, {"<>", OP_NE}, {"=", OP_EQ}, {"CONTAINS", OP_CONTAINS},
        {"BEGINSWITH", OP_BEGINS}, {"ENDSWITH", OP_ENDS}, {"LIKE", OP_LIKE},
    };
    int op = OP_NONE;
    for (size_t k = 0; k < sizeof ops / sizeof *ops; k++) {
        size_t n = strlen(ops[k].name);
        if (!strncasecmp(q, ops[k].name, n)) { op = ops[k].op; q += n; break; }
    }
    if (op == OP_NONE) goto unsupported;
    uint32_t opt = 0;
    if (*q == '[') {
        for (q++; *q && *q != ']'; q++) if (*q == 'c' || *q == 'C') opt |= 1;
        if (*q == ']') q++;
    }
    while (isspace((uint8_t)*q)) q++;
    id arg;
    if (!strncmp(q, "%@", 2)) arg = rt_retain(ARG(1));
    else if (*q == '\'' || *q == '"') {
        const char *e = strchr(q + 1, *q);
        arg = str_new_n(q + 1, e ? (size_t)(e - q - 1) : strlen(q + 1));
    } else goto unsupported;
    rt_st32(p + PR_OP, (uint32_t)op);
    rt_st32(p + PR_ARG, arg);
    rt_st32(p + PR_OPT, opt);
    RET(rt_autorelease(p));
    return;
unsupported:
    rt_log("collections: NSPredicate format \"%s\" is not supported (evaluates to NO)", f);
    RET(rt_autorelease(p));
}

M(pr_evaluate) {
    id self = SELF, o = ARG(0), arg = rt_ld32(self + PR_ARG);
    uint32_t op = rt_ld32(self + PR_OP);
    int icase = rt_ld32(self + PR_OPT) & 1;
    if (op == OP_TRUE || op == OP_FALSE) { RET(op == OP_TRUE); return; }
    if (op == OP_NONE || !o) { RET(0); return; }
    if ((op == OP_EQ || op == OP_NE) && !is_str(o) && !is_str(arg)) { RET(obj_eq(c, o, arg) == (op == OP_EQ)); return; }
    char nb[64];
    const char *s, *a;
    if (is_num(o)) { num_string(o, nb, sizeof nb); s = nb; } else s = S(o);
    a = is_str(arg) ? S(arg) : rt_objc_describe(c, arg);
    char *acopy = strdup(a);
    int r = 0;
    size_t ns = strlen(s), na = strlen(acopy);
    switch (op) {
    case OP_MATCHES: r = regex_full_match(acopy, s, icase); break;
    case OP_EQ: r = icase ? !strcasecmp(s, acopy) : !strcmp(s, acopy); break;
    case OP_NE: r = icase ? strcasecmp(s, acopy) != 0 : strcmp(s, acopy) != 0; break;
    case OP_CONTAINS: r = (icase ? strcasestr_(s, acopy) : strstr(s, acopy)) != NULL; break;
    case OP_BEGINS: r = na <= ns && !(icase ? strncasecmp(s, acopy, na) : strncmp(s, acopy, na)); break;
    case OP_ENDS: r = na <= ns && !(icase ? strcasecmp(s + ns - na, acopy) : strcmp(s + ns - na, acopy)); break;
    case OP_LIKE: r = like_match(acopy, s, icase); break;
    }
    free(acopy);
    RET(r);
}
M(pr_dealloc) { id self = SELF; rt_release(c, rt_ld32(self + PR_ARG)); rt_objc_free(self); }

/* ================================================================================================================ */
/* NSString additions                                                                                               */
/* ================================================================================================================ */
static const char *SU(cpu_t *c) { return S(SELF); }

M(s_components_string) {
    const char *s = SU(c), *sep = S(ARG(0));
    size_t w = strlen(sep);
    id a = arr_alloc(cls_array);
    for (;;) {
        const char *hit = w ? strstr(s, sep) : NULL;
        size_t n = hit ? (size_t)(hit - s) : strlen(s);
        id part = str_new_n(s, n);
        arr_add(a, part);
        rt_release(c, part);
        if (!hit) break;
        s = hit + w;
    }
    RET(rt_autorelease(a));
}
M(s_components_set) {
    const char *s = SU(c);
    id set = ARG(0), a = arr_alloc(cls_array);
    for (;;) {
        const char *e = s;
        while (*e && !cs_has(set, (uint8_t)*e)) e++;
        id part = str_new_n(s, (size_t)(e - s));
        arr_add(a, part);
        rt_release(c, part);
        if (!*e) break;
        s = e + 1;
    }
    RET(rt_autorelease(a));
}
M(s_trim) {
    const char *s = SU(c);
    id set = ARG(0);
    size_t n = strlen(s), a = 0;
    while (a < n && cs_has(set, (uint8_t)s[a])) a++;
    while (n > a && cs_has(set, (uint8_t)s[n - 1])) n--;
    RET(rt_autorelease(str_new_n(s + a, n - a)));
}
M(s_range_of_set) { /* rangeOfCharacterFromSet: — stret: r0 result, r1 self, r2 _cmd, r3 the set */
    const char *s = S(c->r[1]);
    id set = c->r[3];
    uint32_t loc = NSNotFound, len = 0;
    for (uint32_t k = 0; s[k]; k++)
        if (cs_has(set, (uint8_t)s[k])) { loc = k; len = 1; break; }
    rt_st32(c->r[0], loc);
    rt_st32(c->r[0] + 4, len);
}
M(s_replace) { /* stringByReplacingOccurrencesOfString:withString: */
    const char *s = SU(c), *from = S(ARG(0)), *to = S(ARG(1));
    size_t w = strlen(from);
    if (!w) { RET(rt_autorelease(rt_nsstring_new(s))); return; }
    sb b = {0};
    sb_putn(&b, "", 0);
    for (const char *hit; (hit = strstr(s, from)); s = hit + w) {
        sb_putn(&b, s, (size_t)(hit - s));
        sb_puts(&b, to);
    }
    sb_puts(&b, s);
    RET(rt_nsstring(b.p));
    free(b.p);
}
M(s_localized_compare) {
    const char *a = SU(c), *b = S(ARG(0));
    int r = strcasecmp(a, b);
    if (!r) r = strcmp(a, b);
    RET((uint32_t)(r < 0 ? -1 : r > 0));
}
M(s_is_absolute) { RET(SU(c)[0] == '/' || SU(c)[0] == '~'); }
M(s_path_components) {
    const char *s = SU(c);
    id a = arr_alloc(cls_array);
    if (*s == '/') { id r = rt_nsstring_new("/"); arr_add(a, r); rt_release(c, r); }
    while (*s) {
        while (*s == '/') s++;
        if (!*s) break;
        const char *e = strchr(s, '/');
        size_t n = e ? (size_t)(e - s) : strlen(s);
        id part = str_new_n(s, n);
        arr_add(a, part);
        rt_release(c, part);
        s += n;
    }
    RET(rt_autorelease(a));
}
M(s_get_cstring_nomax) { /* getCString: (no length limit) */
    const char *s = SU(c);
    memcpy(rt_mem + ARG(0), s, strlen(s) + 1);
}
M(s_ll_value) { int64_t v = strtoll(SU(c), NULL, 10); c->r[0] = (uint32_t)v; c->r[1] = (uint32_t)((uint64_t)v >> 32); }

/* text from characters: initWithCharacters:length: / stringWithCharacters:length: (UTF-16 units) */
static char *utf16_units(uint32_t p, uint32_t n) {
    uint8_t *tmp = malloc(2 * (size_t)n + 2);
    if (n) memcpy(tmp, rt_mem + p, 2 * (size_t)n);
    char *t = decode_text(tmp, 2 * (size_t)n, ENC_UTF16LE, NULL);
    free(tmp);
    return t;
}
M(s_with_characters) {
    char *t = utf16_units(ARG(0), ARG(1));
    id s = rt_autorelease(str_init(c, rt_objc_alloc(SELF == rt_class("__NSCFConstantString") ? cls_string : SELF), t));
    free(t);
    RET(s);
}
M(s_init_characters) {
    id self = SELF;
    char *t = utf16_units(ARG(0), ARG(1));
    RET(str_init(c, self, t));
    free(t);
}

/* file contents: stringWithContentsOfFile:(encoding:|usedEncoding:)error: and the initializers */
static char *text_file(const char *gpath, uint32_t enc, uint32_t *used) {
    size_t n;
    uint8_t *d = file_read(gpath, &n);
    if (!d) return NULL;
    char *t = decode_text(d, n, enc, used);
    free(d);
    return t;
}
/* decode the arguments of a ...ContentsOfFile: selector; the encoding / error words follow the path */
static char *text_file_args(cpu_t *c, uint32_t *err_ptr) {
    const char *sel = rt_sel_name(c->r[1]);
    uint32_t enc = ENC_UTF8, used_ptr = 0, used = 0;
    *err_ptr = 0;
    if (strstr(sel, "usedEncoding:")) { used_ptr = ARG(1); *err_ptr = ARG(2); }
    else if (strstr(sel, "encoding:")) { enc = ARG(1); *err_ptr = ARG(2); }
    char *t = text_file(rt_nsstring_utf8(ARG(0)), enc, &used);
    if (t && used_ptr) rt_st32(used_ptr, used);
    return t;
}
M(s_with_file) {
    id cls = SELF == rt_class("__NSCFConstantString") ? cls_string : SELF;
    uint32_t err;
    char *t = text_file_args(c, &err);
    if (!t) { out_obj(err, 0); RET(0); return; }
    id s = str_init(c, rt_objc_alloc(cls), t);
    free(t);
    RET(rt_autorelease(s));
}
M(s_init_file) {
    id self = SELF;
    uint32_t err;
    char *t = text_file_args(c, &err);
    if (!t) { out_obj(err, 0); rt_release(c, self); RET(0); return; }
    RET(str_init(c, self, t));
    free(t);
}
M(s_init_data) { /* initWithData:encoding: */
    id self = SELF, d = ARG(0);
    uint32_t enc = ARG(1);
    char *t = d ? decode_text(rt_mem + data_bytes(d), data_len(d), enc, NULL) : strdup("");
    RET(str_init(c, self, t));
    free(t);
}
M(s_init_bytes_enc) { /* initWithBytes:length:encoding: with real decoding (foundation copies the bytes as is) */
    id self = SELF;
    uint32_t p = ARG(0), n = ARG(1), enc = ARG(2);
    char *t = decode_text(n ? rt_mem + p : (const uint8_t *)"", n, enc, NULL);
    RET(str_init(c, self, t));
    free(t);
}
M(s_data_using) { /* dataUsingEncoding:(allowLossyConversion:) */
    const char *s = SU(c);
    uint32_t enc = ARG(0);
    int lossy = strstr(rt_sel_name(c->r[1]), "allowLossy") ? (int)(ARG(1) & 0xff) : 0;
    size_t n;
    uint8_t *b = encode_text(s, enc, lossy, &n);
    if (!b) { RET(0); return; }
    id d = data_fill(rt_objc_alloc(cls_data), b, (uint32_t)n);
    free(b);
    RET(rt_autorelease(d));
}
M(s_write) { /* writeToFile:atomically:(encoding:error:) */
    id self = SELF;
    const char *path = rt_nsstring_utf8(ARG(0));
    int atomic = ARG(1) & 0xff;
    uint32_t enc = ENC_UTF8, err = 0;
    if (strstr(rt_sel_name(c->r[1]), "encoding:")) { enc = ARG(2); err = ARG(3); }
    size_t n;
    uint8_t *b = encode_text(S(self), enc, 0, &n);
    int ok = b && file_write(path, b, n, atomic);
    free(b);
    if (!ok) out_obj(err, 0);
    RET(ok);
}
M(s_property_list) {
    const char *s = SU(c);
    id r = plist_parse(c, (const uint8_t *)s, strlen(s));
    if (!r) rt_log("collections: -[NSString propertyList]: not a property list");
    RET(r ? rt_autorelease(r) : 0);
}
M(s_strings_file_format) { /* propertyListFromStringsFileFormat */
    const char *s = SU(c);
    ap x = {s, s + strlen(s), c, 0};
    RET(rt_autorelease(ap_dict_body(&x, 0)));
}

/* ================================================================================================================ */
/* the C API (rt.h)                                                                                                 */
/* ================================================================================================================ */
id rt_nsarray_new(const id *items, uint32_t n) { return arr_from(cls_marray, items, n); }
uint32_t rt_nsarray_count(id array) { return array && rt_is_kind(array, cls_array) ? arr_n(array) : 0; }
id rt_nsarray_at(id array, uint32_t k) { return k < rt_nsarray_count(array) ? arr_get(array, k) : 0; }
void rt_nsarray_add(id mutable_array, id item) {
    if (mutable_array && item && rt_is_kind(mutable_array, cls_array)) arr_add(mutable_array, item);
}
id rt_nsdict_new(void) { return dict_alloc(cls_mdict); }
id rt_nsdict_get(id dict, id key) { return dict && key && rt_is_kind(dict, cls_dict) ? h_get(dict, key) : 0; }
void rt_nsdict_set(id dict, id key, id value) {
    if (!dict || !key || !rt_is_kind(dict, cls_dict)) return;
    if (value) h_put(rt_thread_cpu(), dict, key, value);
    else h_remove(rt_thread_cpu(), dict, key);
}
uint32_t rt_nsdict_count(id dict) { return dict && rt_is_kind(dict, cls_dict) ? h_n(dict) : 0; }
id rt_nsdict_key_at(id dict, uint32_t k) { return k < rt_nsdict_count(dict) ? h_key(dict, k) : 0; }
id rt_nsnumber_new_int(int64_t v) { return num_new(v >= INT_MIN && v <= INT_MAX ? NK_INT : NK_LONGLONG, v, 0); }
id rt_nsnumber_new_double(double v) { return num_new(NK_DOUBLE, 0, v); }
id rt_nsnumber_new_bool(int v) { return num_new(NK_BOOL, v != 0, 0); }
int rt_is_nsnumber(id obj) { return is_num(obj); }
double rt_nsnumber_double(id num) { return is_num(num) ? num_d(num) : 0; }
int64_t rt_nsnumber_int(id num) { return is_num(num) ? num_i(num) : 0; }
id rt_nsdata_new(const void *bytes, uint32_t n) { return data_fill(rt_objc_alloc(cls_data), bytes ? bytes : "", bytes ? n : 0); }
uint32_t rt_nsdata_bytes(id data) { return data && rt_is_kind(data, cls_data) ? data_bytes(data) : 0; }
uint32_t rt_nsdata_len(id data) { return data && rt_is_kind(data, cls_data) ? data_len(data) : 0; }
int rt_is_nsstring(id obj) { return is_str(obj); }
int rt_is_nsarray(id obj) { return obj && rt_is_kind(obj, cls_array); }
int rt_is_nsdict(id obj) { return obj && rt_is_kind(obj, cls_dict); }

/* ================================================================================================================ */
/* class definitions                                                                                                */
/* ================================================================================================================ */
typedef struct { const char *sel; rt_hostfn fn; } mdef;

static void methods(id cls, const mdef *d, size_t n, int class_methods) {
    for (size_t k = 0; k < n; k++) {
        if (class_methods) rt_objc_cmethod(cls, d[k].sel, d[k].fn);
        else rt_objc_method(cls, d[k].sel, d[k].fn);
    }
}
#define METHODS(cls, list) methods(cls, list, sizeof list / sizeof *list, 0)
#define CMETHODS(cls, list) methods(cls, list, sizeof list / sizeof *list, 1)

/* add NSString methods foundation.c does not provide (never replace its own) */
static void string_methods(const mdef *d, size_t n, int class_methods) {
    for (size_t k = 0; k < n; k++) {
        id where = class_methods ? rt_object_class(cls_string) : cls_string;
        if (rt_lookup(where, rt_sel(d[k].sel))) continue;
        if (class_methods) rt_objc_cmethod(cls_string, d[k].sel, d[k].fn);
        else rt_objc_method(cls_string, d[k].sel, d[k].fn);
    }
}

void rt_collections_define(void) {
    cls_string = rt_class("NSString");
    if (!cls_string) cls_string = rt_objc_define("NSString", "NSObject", 12);

    cls_array = rt_objc_define("NSArray", "NSObject", A_IVARS);
    cls_marray = rt_objc_define("NSMutableArray", "NSArray", 0);
    cls_dict = rt_objc_define("NSDictionary", "NSObject", H_IVARS);
    cls_mdict = rt_objc_define("NSMutableDictionary", "NSDictionary", 0);
    cls_set = rt_objc_define("NSSet", "NSObject", H_IVARS);
    cls_mset = rt_objc_define("NSMutableSet", "NSSet", 0);
    cls_value = rt_objc_define("NSValue", "NSObject", V_IVARS);
    cls_number = rt_objc_define("NSNumber", "NSValue", 0);
    cls_null = rt_objc_define("NSNull", "NSObject", 0);
    cls_data = rt_objc_define("NSData", "NSObject", D_IVARS);
    cls_mdata = rt_objc_define("NSMutableData", "NSData", 0);
    cls_enum = rt_objc_define("NSEnumerator", "NSObject", E_IVARS);
    cls_charset = rt_objc_define("NSCharacterSet", "NSObject", CS_IVARS);
    cls_mcharset = rt_objc_define("NSMutableCharacterSet", "NSCharacterSet", 0);
    cls_scanner = rt_objc_define("NSScanner", "NSObject", SC_IVARS);
    cls_indexpath = rt_objc_define("NSIndexPath", "NSObject", IP_IVARS);
    cls_predicate = rt_objc_define("NSPredicate", "NSObject", PR_IVARS);

    static const char *const types[24] = {
        [NK_INT] = "i", [NK_UINT] = "I", [NK_DOUBLE] = "d", [NK_FLOAT] = "f", [NK_BOOL] = "c", [NK_CHAR] = "c",
        [NK_SHORT] = "s", [NK_LONGLONG] = "q", [NK_ULONGLONG] = "Q", [VK_POINTER] = "^v", [VK_OBJECT] = "@",
        [VK_POINT] = "{CGPoint=ff}", [VK_SIZE] = "{CGSize=ff}", [VK_RECT] = "{CGRect={CGPoint=ff}{CGSize=ff}}",
        [VK_RANGE] = "{_NSRange=II}",
    };
    for (int k = 0; k < 24; k++) objc_types[k] = rt_static_string(types[k] ? types[k] : "?");

    /* NSArray */
    static const mdef a_c[] = {
        {"array", a_array}, {"arrayWithObject:", a_with_object}, {"arrayWithObjects:", a_with_objects},
        {"arrayWithObjects:count:", a_with_objects_count}, {"arrayWithArray:", a_with_array},
        {"arrayWithContentsOfFile:", a_with_file}, {"arrayWithCapacity:", a_with_capacity},
    };
    static const mdef a_i[] = {
        {"init", a_init}, {"initWithObjects:", a_init_objects}, {"initWithObjects:count:", a_init_objects_count},
        {"initWithArray:", a_init_array}, {"initWithContentsOfFile:", a_init_file},
        {"initWithCapacity:", a_init_capacity}, {"count", a_count}, {"objectAtIndex:", a_object_at},
        {"lastObject", a_last}, {"firstObject", a_first}, {"indexOfObject:", a_index_of},
        {"indexOfObjectIdenticalTo:", a_index_identical}, {"containsObject:", a_contains},
        {"getObjects:", a_get_objects}, {"getObjects:range:", a_get_objects},
        {"objectEnumerator", a_object_enum}, {"reverseObjectEnumerator", a_reverse_enum},
        {"countByEnumeratingWithState:objects:count:", a_fast_enum}, {"arrayByAddingObject:", a_adding_object},
        {"arrayByAddingObjectsFromArray:", a_adding_array}, {"subarrayWithRange:", a_subarray},
        {"componentsJoinedByString:", a_joined}, {"isEqualToArray:", a_is_equal}, {"isEqual:", a_is_equal},
        {"hash", a_hash}, {"description", a_description}, {"descriptionWithLocale:", a_description},
        {"descriptionWithLocale:indent:", a_description_indent}, {"copy", a_copy}, {"copyWithZone:", a_copy},
        {"mutableCopy", a_mutable_copy}, {"mutableCopyWithZone:", a_mutable_copy},
        {"writeToFile:atomically:", a_write}, {"makeObjectsPerformSelector:", a_perform},
        {"makeObjectsPerformSelector:withObject:", a_perform}, {"sortedArrayUsingSelector:", a_sorted_sel},
        {"sortedArrayUsingFunction:context:", a_sorted_fn}, {"dealloc", a_dealloc},
    };
    static const mdef ma_i[] = {
        {"addObject:", ma_add}, {"addObjectsFromArray:", ma_add_array}, {"insertObject:atIndex:", ma_insert},
        {"removeObjectAtIndex:", ma_remove_at}, {"removeLastObject", ma_remove_last},
        {"removeObject:", ma_remove_object}, {"removeObjectIdenticalTo:", ma_remove_identical},
        {"removeObjectsInArray:", ma_remove_in_array}, {"removeAllObjects", ma_remove_all},
        {"replaceObjectAtIndex:withObject:", ma_replace}, {"exchangeObjectAtIndex:withObjectAtIndex:", ma_exchange},
        {"setArray:", ma_set_array}, {"sortUsingSelector:", ma_sort_sel}, {"sortUsingFunction:context:", ma_sort_fn},
    };
    CMETHODS(cls_array, a_c);
    METHODS(cls_array, a_i);
    METHODS(cls_marray, ma_i);

    /* NSDictionary */
    static const mdef d_c[] = {
        {"dictionary", d_dictionary}, {"dictionaryWithObject:forKey:", d_with_object_key},
        {"dictionaryWithObjects:forKeys:", d_with_objects_keys},
        {"dictionaryWithObjects:forKeys:count:", d_with_objects_keys_count},
        {"dictionaryWithObjectsAndKeys:", d_with_objects_and_keys}, {"dictionaryWithDictionary:", d_with_dictionary},
        {"dictionaryWithCapacity:", d_with_capacity}, {"dictionaryWithContentsOfFile:", d_with_file},
    };
    static const mdef d_i[] = {
        {"init", d_init}, {"initWithCapacity:", d_init}, {"initWithObjectsAndKeys:", d_init_objects_and_keys},
        {"initWithDictionary:", d_init_dictionary}, {"initWithObjects:forKeys:", d_init_objects_keys},
        {"initWithContentsOfFile:", d_init_file}, {"count", d_count}, {"objectForKey:", d_object_for_key},
        {"valueForKey:", d_object_for_key}, {"allKeys", d_all_keys}, {"allValues", d_all_values},
        {"allKeysForObject:", d_keys_for_object}, {"keyEnumerator", d_key_enum}, {"objectEnumerator", d_object_enum},
        {"countByEnumeratingWithState:objects:count:", d_fast_enum}, {"isEqualToDictionary:", d_is_equal},
        {"isEqual:", d_is_equal}, {"hash", d_hash}, {"description", d_description},
        {"descriptionWithLocale:", d_description}, {"descriptionWithLocale:indent:", d_description_indent},
        {"copy", d_copy}, {"copyWithZone:", d_copy}, {"mutableCopy", d_mutable_copy},
        {"mutableCopyWithZone:", d_mutable_copy}, {"writeToFile:atomically:", d_write}, {"dealloc", d_dealloc},
    };
    static const mdef md_i[] = {
        {"setObject:forKey:", md_set}, {"setValue:forKey:", md_set_value}, {"removeObjectForKey:", md_remove},
        {"removeObjectsForKeys:", md_remove_keys}, {"removeAllObjects", md_remove_all},
        {"addEntriesFromDictionary:", md_add_entries}, {"setDictionary:", md_set_dictionary},
    };
    CMETHODS(cls_dict, d_c);
    METHODS(cls_dict, d_i);
    METHODS(cls_mdict, md_i);

    /* NSSet */
    static const mdef st_c[] = {
        {"set", st_set}, {"setWithObject:", st_with_object}, {"setWithObjects:", st_with_objects},
        {"setWithArray:", st_with_array}, {"setWithSet:", st_with_set}, {"setWithCapacity:", st_set},
    };
    static const mdef st_i[] = {
        {"init", st_init}, {"initWithCapacity:", st_init}, {"initWithObjects:", st_init_objects},
        {"initWithArray:", st_init_array}, {"initWithSet:", st_init_set}, {"count", st_count},
        {"anyObject", st_any}, {"allObjects", st_all}, {"containsObject:", st_contains}, {"member:", st_member},
        {"objectEnumerator", st_enum}, {"countByEnumeratingWithState:objects:count:", st_fast_enum},
        {"setByAddingObject:", st_adding}, {"isEqualToSet:", st_is_equal}, {"isEqual:", st_is_equal},
        {"intersectsSet:", st_intersects}, {"hash", d_hash}, {"description", st_description},
        {"descriptionWithLocale:", st_description}, {"copy", st_copy}, {"copyWithZone:", st_copy},
        {"mutableCopy", st_mutable_copy}, {"mutableCopyWithZone:", st_mutable_copy},
        {"makeObjectsPerformSelector:", st_perform}, {"makeObjectsPerformSelector:withObject:", st_perform},
        {"dealloc", d_dealloc},
    };
    static const mdef mst_i[] = {
        {"addObject:", mst_add}, {"addObjectsFromArray:", mst_add_array}, {"unionSet:", mst_union},
        {"removeObject:", mst_remove}, {"removeAllObjects", mst_remove_all}, {"minusSet:", mst_minus},
        {"intersectSet:", mst_intersect},
    };
    CMETHODS(cls_set, st_c);
    METHODS(cls_set, st_i);
    METHODS(cls_mset, mst_i);

    /* NSEnumerator */
    static const mdef e_i[] = {
        {"nextObject", e_next}, {"allObjects", e_all}, {"countByEnumeratingWithState:objects:count:", e_fast_enum},
        {"dealloc", e_dealloc},
    };
    METHODS(cls_enum, e_i);

    /* NSValue and NSNumber */
    static const mdef v_c[] = {
        {"valueWithPointer:", v_pointer}, {"valueWithNonretainedObject:", v_object}, {"valueWithCGPoint:", v_point},
        {"valueWithCGSize:", v_size}, {"valueWithCGRect:", v_rect}, {"valueWithRange:", v_range},
    };
    static const mdef v_i[] = {
        {"pointerValue", v_pointer_value}, {"nonretainedObjectValue", v_pointer_value},
        {"CGPointValue", v_struct_value}, {"CGSizeValue", v_struct_value}, {"CGRectValue", v_struct_value},
        {"rangeValue", v_range_value}, {"getValue:", v_get_value}, {"objCType", v_obj_ctype},
        {"isEqualToValue:", v_is_equal}, {"isEqual:", v_is_equal}, {"hash", v_hash}, {"description", n_description},
        {"copy", n_copy}, {"copyWithZone:", n_copy},
    };
    static const mdef n_c[] = {
        {"numberWithInt:", n_int}, {"numberWithInteger:", n_int}, {"numberWithLong:", n_int},
        {"numberWithUnsignedInt:", n_uint}, {"numberWithUnsignedInteger:", n_uint}, {"numberWithUnsignedLong:", n_uint},
        {"numberWithChar:", n_char}, {"numberWithUnsignedChar:", n_uchar}, {"numberWithShort:", n_short},
        {"numberWithUnsignedShort:", n_ushort}, {"numberWithLongLong:", n_ll}, {"numberWithUnsignedLongLong:", n_ull},
        {"numberWithFloat:", n_float}, {"numberWithDouble:", n_double}, {"numberWithBool:", n_bool},
    };
    static const mdef n_i[] = {
        {"initWithInt:", ni_int}, {"initWithInteger:", ni_int}, {"initWithLong:", ni_int},
        {"initWithUnsignedInt:", ni_uint}, {"initWithUnsignedInteger:", ni_uint}, {"initWithUnsignedLong:", ni_uint},
        {"initWithChar:", ni_char}, {"initWithShort:", ni_short}, {"initWithLongLong:", ni_ll},
        {"initWithUnsignedLongLong:", ni_ull}, {"initWithFloat:", ni_float}, {"initWithDouble:", ni_double},
        {"initWithBool:", ni_bool}, {"intValue", n_int_value}, {"integerValue", n_int_value},
        {"longValue", n_int_value}, {"unsignedIntValue", n_uint_value}, {"unsignedIntegerValue", n_uint_value},
        {"unsignedLongValue", n_uint_value}, {"charValue", n_char_value}, {"unsignedCharValue", n_int_value},
        {"shortValue", n_short_value}, {"unsignedShortValue", n_int_value}, {"longLongValue", n_ll_value},
        {"unsignedLongLongValue", n_ll_value}, {"floatValue", n_float_value}, {"doubleValue", n_double_value},
        {"boolValue", n_bool_value}, {"stringValue", n_string_value}, {"description", n_description},
        {"descriptionWithLocale:", n_description}, {"isEqual:", n_is_equal}, {"isEqualToNumber:", n_is_equal},
        {"hash", n_hash}, {"compare:", n_compare},
    };
    CMETHODS(cls_value, v_c);
    METHODS(cls_value, v_i);
    CMETHODS(cls_number, n_c);
    METHODS(cls_number, n_i);

    /* NSNull */
    null_singleton = rt_objc_alloc(cls_null);
    rt_objc_cmethod(cls_null, "null", null_null);
    rt_objc_method(cls_null, "description", null_description);
    rt_objc_method(cls_null, "dealloc", null_keep);
    rt_objc_method(cls_null, "release", null_keep);
    rt_objc_method(cls_null, "retain", null_keep);
    rt_objc_method(cls_null, "autorelease", null_keep);

    /* NSData */
    static const mdef dt_c[] = {
        {"data", dt_data}, {"dataWithBytes:length:", dt_with_bytes}, {"dataWithBytesNoCopy:length:", dt_with_bytes_nocopy},
        {"dataWithBytesNoCopy:length:freeWhenDone:", dt_with_bytes_nocopy}, {"dataWithData:", dt_with_data},
        {"dataWithContentsOfFile:", dt_with_file}, {"dataWithContentsOfMappedFile:", dt_with_file},
        {"dataWithContentsOfURL:", dt_with_url}, {"dataWithContentsOfURL:options:error:", dt_with_url},
        {"dataWithLength:", dt_with_length}, {"dataWithCapacity:", dt_with_capacity},
    };
    static const mdef dt_i[] = {
        {"init", dti_init}, {"initWithBytes:length:", dti_bytes}, {"initWithBytesNoCopy:length:", dti_bytes_nocopy},
        {"initWithBytesNoCopy:length:freeWhenDone:", dti_bytes_nocopy}, {"initWithData:", dti_data},
        {"initWithContentsOfFile:", dti_file}, {"initWithContentsOfMappedFile:", dti_file},
        {"initWithContentsOfURL:", dti_url}, {"initWithContentsOfURL:options:error:", dti_url},
        {"initWithLength:", dti_length}, {"initWithCapacity:", dti_capacity}, {"bytes", dt_bytes},
        {"length", dt_length}, {"getBytes:", dt_get_bytes}, {"getBytes:length:", dt_get_bytes},
        {"getBytes:range:", dt_get_bytes}, {"subdataWithRange:", dt_subdata}, {"isEqualToData:", dt_is_equal},
        {"isEqual:", dt_is_equal}, {"hash", dt_hash}, {"writeToFile:atomically:", dt_write},
        {"writeToFile:options:error:", dt_write}, {"description", dt_description}, {"copy", dt_copy},
        {"copyWithZone:", dt_copy}, {"mutableCopy", dt_mutable_copy}, {"mutableCopyWithZone:", dt_mutable_copy},
        {"dealloc", dt_dealloc},
    };
    static const mdef mdt_i[] = {
        {"mutableBytes", mdt_mutable_bytes}, {"appendBytes:length:", mdt_append_bytes}, {"appendData:", mdt_append_data},
        {"setLength:", mdt_set_length}, {"increaseLengthBy:", mdt_increase_length}, {"setData:", mdt_set_data},
        {"replaceBytesInRange:withBytes:", mdt_replace}, {"resetBytesInRange:", mdt_reset},
    };
    CMETHODS(cls_data, dt_c);
    METHODS(cls_data, dt_i);
    METHODS(cls_mdata, mdt_i);

    /* NSCharacterSet */
    static const mdef cs_c[] = {
        {"characterSetWithCharactersInString:", cs_in_string}, {"characterSetWithRange:", cs_in_range},
        {"whitespaceCharacterSet", cs_whitespace}, {"whitespaceAndNewlineCharacterSet", cs_whitespace_nl},
        {"newlineCharacterSet", cs_newline}, {"decimalDigitCharacterSet", cs_digits},
        {"letterCharacterSet", cs_letters}, {"alphanumericCharacterSet", cs_alnum},
        {"punctuationCharacterSet", cs_punct}, {"uppercaseLetterCharacterSet", cs_upper},
        {"lowercaseLetterCharacterSet", cs_lower}, {"controlCharacterSet", cs_control},
        {"symbolCharacterSet", cs_symbol},
    };
    static const mdef cs_i[] = {
        {"invertedSet", cs_inverted}, {"characterIsMember:", cs_is_member}, {"copy", cs_copy},
        {"copyWithZone:", cs_copy}, {"mutableCopy", cs_copy}, {"mutableCopyWithZone:", cs_copy},
    };
    static const mdef mcs_i[] = {
        {"addCharactersInString:", mcs_add_string}, {"removeCharactersInString:", mcs_remove_string},
        {"addCharactersInRange:", mcs_add_range}, {"formUnionWithCharacterSet:", mcs_union}, {"invert", mcs_invert},
    };
    for (int k = 0; k < CS_NSTD; k++) cs_standard(k); /* made here, not lazily: no race between threads */
    CMETHODS(cls_charset, cs_c);
    METHODS(cls_charset, cs_i);
    METHODS(cls_mcharset, mcs_i);

    /* NSScanner */
    static const mdef sc_c[] = {{"scannerWithString:", sc_with_string}, {"localizedScannerWithString:", sc_with_string}};
    static const mdef sc_i[] = {
        {"initWithString:", sc_init_string}, {"string", sc_string}, {"scanLocation", sc_location},
        {"setScanLocation:", sc_set_location}, {"charactersToBeSkipped", sc_skip_set},
        {"setCharactersToBeSkipped:", sc_set_skip}, {"caseSensitive", sc_case}, {"setCaseSensitive:", sc_set_case},
        {"isAtEnd", sc_at_end}, {"scanInt:", sc_int}, {"scanInteger:", sc_int}, {"scanLongLong:", sc_ll},
        {"scanHexInt:", sc_hex}, {"scanFloat:", sc_float}, {"scanDouble:", sc_double},
        {"scanString:intoString:", sc_scan_string}, {"scanUpToString:intoString:", sc_up_to_string},
        {"scanCharactersFromSet:intoString:", sc_from_set}, {"scanUpToCharactersFromSet:intoString:", sc_up_to_set},
        {"dealloc", sc_dealloc},
    };
    CMETHODS(cls_scanner, sc_c);
    METHODS(cls_scanner, sc_i);

    /* NSIndexPath */
    static const mdef ip_c[] = {
        {"indexPathForRow:inSection:", ip_row_section}, {"indexPathWithIndex:", ip_with_index},
        {"indexPathWithIndexes:length:", ip_with_indexes},
    };
    static const mdef ip_i[] = {
        {"section", ip_section}, {"row", ip_row}, {"length", ip_length}, {"indexAtPosition:", ip_index_at},
        {"indexPathByAddingIndex:", ip_adding}, {"isEqual:", ip_is_equal}, {"compare:", ip_compare},
        {"hash", ip_hash}, {"copy", ip_copy}, {"copyWithZone:", ip_copy}, {"description", ip_description},
    };
    CMETHODS(cls_indexpath, ip_c);
    METHODS(cls_indexpath, ip_i);

    /* NSPredicate */
    rt_objc_cmethod(cls_predicate, "predicateWithFormat:", pr_with_format);
    rt_objc_method(cls_predicate, "evaluateWithObject:", pr_evaluate);
    rt_objc_method(cls_predicate, "dealloc", pr_dealloc);

    /* NSString additions */
    static const mdef s_c[] = {
        {"stringWithContentsOfFile:", s_with_file}, {"stringWithContentsOfFile:encoding:error:", s_with_file},
        {"stringWithContentsOfFile:usedEncoding:error:", s_with_file}, {"stringWithCharacters:length:", s_with_characters},
    };
    static const mdef s_i[] = {
        {"componentsSeparatedByString:", s_components_string},
        {"componentsSeparatedByCharactersInSet:", s_components_set}, {"stringByTrimmingCharactersInSet:", s_trim},
        {"rangeOfCharacterFromSet:", s_range_of_set},
        {"stringByReplacingOccurrencesOfString:withString:", s_replace}, {"localizedCompare:", s_localized_compare},
        {"localizedCaseInsensitiveCompare:", s_localized_compare}, {"isAbsolutePath", s_is_absolute},
        {"pathComponents", s_path_components}, {"getCString:", s_get_cstring_nomax}, {"longLongValue", s_ll_value},
        {"initWithCharacters:length:", s_init_characters}, {"initWithContentsOfFile:", s_init_file},
        {"initWithContentsOfFile:encoding:error:", s_init_file}, {"initWithContentsOfFile:usedEncoding:error:", s_init_file},
        {"initWithData:encoding:", s_init_data}, {"dataUsingEncoding:", s_data_using},
        {"dataUsingEncoding:allowLossyConversion:", s_data_using}, {"writeToFile:atomically:", s_write},
        {"writeToFile:atomically:encoding:error:", s_write}, {"propertyList", s_property_list},
        {"propertyListFromStringsFileFormat", s_strings_file_format},
    };
    string_methods(s_c, sizeof s_c / sizeof *s_c, 1);
    string_methods(s_i, sizeof s_i / sizeof *s_i, 0);
    /* foundation copies initWithBytes:length:encoding: bytes as they are; decode UTF-16 and Latin-1 here */
    rt_objc_method(cls_string, "initWithBytes:length:encoding:", s_init_bytes_enc);
}
