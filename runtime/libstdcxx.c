/* libstdc++ (Apple GCC 4.2, libstdc++.6, 32-bit ARM): std::string, red-black tree and list helpers,
 * std::ostringstream, C++ type info and __dynamic_cast, and the catch entry points.
 *
 * The game's own inline code works on the same objects, so every layout here is GCC 4.2's, in game memory:
 *
 *   std::string   one word: _M_p, the address of the characters. The _Rep sits in the 12 bytes before them:
 *                   p-12 _M_length, p-8 _M_capacity, p-4 _M_refcount
 *                 Copy-on-write: refcount is the number of EXTRA owners (0 = one owner); < 0 (-1) = leaked, i.e.
 *                 unshareable because a reference into the characters was handed out (non-const operator[]/at).
 *                 The shared empty string is the data import _ZNSs4_Rep20_S_empty_rep_storageE, 16 zeroed bytes;
 *                 empty strings point at its +12 and it is never freed nor counted. Reps come from rt_malloc,
 *                 sized like _S_create does (growth to 2x, page rounding for large strings).
 *   _Rb_tree_node_base  { color (0 red, 1 black), parent, left, right }; the tree header is a node whose parent is
 *                 the root, left the leftmost and right the rightmost node (ported from GCC's tree.cc).
 *   _List_node_base     { next, prev }.
 *   std::ostringstream (0xb4 bytes, built on the game's stack; inline code reads its vptr and the ios_base):
 *                 +0x00 basic_ostream vptr (vptr[-3] = 0x2c: offset of the virtual base basic_ios)
 *                 +0x04 basic_stringbuf: vptr, 6 get/put pointers, locale (0x20 bytes), _M_mode +0x20,
 *                       _M_string +0x24 (a std::string, so the text lives in game memory)
 *                 +0x2c basic_ios: ios_base { vptr, _M_precision 4, _M_width 8, _M_flags 0xc, _M_exception 0x10,
 *                       _M_streambuf_state 0x14, _M_callbacks 0x18, _M_word_zero 0x1c, _M_local_word[8] 0x24,
 *                       _M_word_size 0x64, _M_word 0x68, _M_ios_locale 0x6c }, then _M_tie 0x70, _M_fill 0x74,
 *                       _M_fill_init 0x75, _M_streambuf 0x78, _M_ctype 0x7c, _M_num_put 0x80, _M_num_get 0x84
 *                 The game sets width, flags (std::hex is an out-of-line game function) and fill inline, then
 *                 inserts integers; insertion formats like num_put and appends to _M_string. The put area stays
 *                 empty, so str() returns (a shared copy of) _M_string, as GCC's str() does when pptr() is 0.
 *   type info     type_info { vptr, name }; __si_class_type_info adds base_type; __vmi_class_type_info is
 *                 { vptr, name, flags, base_count, { base_type, offset_flags }[] } with offset_flags = offset << 8 |
 *                 2 (public) | 1 (virtual; then the offset locates the virtual-base offset in the vtable). The
 *                 _ZTVN10__cxxabiv1...E data imports are distinct zeroed blocks here; the image's type_info objects
 *                 point at block + 8, which tells the three kinds apart.
 *
 * Exceptions: nothing throws (__cxa_throw is not imported and libstdc++'s __throw_* end the process here), so the
 * catch entry points are only reached if that changes; they behave like the real ones would on an exception object.
 * The SjLj personality routines are referenced as data (stored into each function's SjLj context): they resolve
 * to host functions that stop the process if anything ever calls them.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rt.h"

#define A(k) rt_arg(c, k)
#define RET(v) rt_ret(c, (uint32_t)(v))
#define IMP(name) static void imp_##name(cpu_t *c)
#define REG(name) rt_import_register(#name, imp_##name)

#define NPOS 0xffffffffu
#define REP 12u                                  /* sizeof(_Rep) */
#define MAX_SIZE (((NPOS - REP) / 1u - 1u) / 4u)  /* _Rep::_S_max_size, basic_string::max_size() */

static uint32_t empty_storage;                    /* _S_empty_rep_storage (16 bytes) */
static uint32_t ti_vtables[3];                    /* class, si_class, vmi_class type_info vtable blocks */
static uint32_t personality_gxx, personality_objc;

/* ---- throwing: not supported, so a throw ends the process with the game's call chain ---------------------- */
static void cxx_throw(cpu_t *c, const char *what, const char *msg) {
    rt_log("C++ exception %s(\"%s\") thrown: exceptions are not supported", what, msg ? msg : "");
    if (c) rt_print_trace(c);
    rt_fatal("uncaught C++ exception %s: %s", what, msg ? msg : "");
}

/* ---- std::string ------------------------------------------------------------------------------------------- */
static uint32_t empty_p(void) { return empty_storage + REP; }
static uint32_t s_len(uint32_t p) { return rt_ld32(p - 12); }
static uint32_t s_cap(uint32_t p) { return rt_ld32(p - 8); }
static int32_t s_ref(uint32_t p) { return (int32_t)rt_ld32(p - 4); }
static int32_t *s_refp(uint32_t p) { return (int32_t *)(rt_mem + p - 4); }
static int s_shared(uint32_t p) { return s_ref(p) > 0; }
static int s_leaked(uint32_t p) { return s_ref(p) < 0; }

/* a host copy of game characters, so a source inside the string being changed survives reallocation */
static char *hcopy(const void *src, uint32_t n) {
    char *b = malloc(n ? n : 1);
    if (!b) rt_fatal("out of host memory");
    if (n) memcpy(b, src, n);
    return b;
}

static void check_length(cpu_t *c, uint32_t p, uint32_t n1, uint32_t n2, const char *s) {
    if (MAX_SIZE - (s_len(p) - n1) < n2) cxx_throw(c, "length_error", s);
}
static uint32_t check_pos(cpu_t *c, uint32_t p, uint32_t pos, const char *s) {
    if (pos > s_len(p)) cxx_throw(c, "out_of_range", s);
    return pos;
}
static uint32_t limit(uint32_t p, uint32_t pos, uint32_t off) {
    uint32_t rest = s_len(p) - pos;
    return off < rest ? off : rest;
}

/* _Rep::_S_create: a rep with room for `cap` characters (refcount 0, length unset); returns the characters */
static uint32_t rep_create(cpu_t *c, uint32_t cap, uint32_t old_cap) {
    if (cap > MAX_SIZE) cxx_throw(c, "length_error", "basic_string::_S_create");
    const uint32_t pagesize = 4096, malloc_header = 16;
    if (cap > old_cap && cap < 2 * old_cap) cap = 2 * old_cap;
    uint32_t size = cap + 1 + REP;
    if (size + malloc_header > pagesize && cap > old_cap) {
        cap += pagesize - (size + malloc_header) % pagesize;
        if (cap > MAX_SIZE) cap = MAX_SIZE;
        size = cap + 1 + REP;
    }
    uint32_t r = rt_malloc(size);
    if (!r) cxx_throw(c, "bad_alloc", "std::bad_alloc");
    rt_st32(r + 4, cap);
    rt_st32(r + 8, 0);
    return r + REP;
}

/* _M_set_length_and_sharable */
static void set_length(uint32_t p, uint32_t n) {
    if (p == empty_p()) return;
    rt_st32(p - 4, 0);
    rt_st32(p - 12, n);
    rt_mem[p + n] = 0;
}

/* _M_dispose: drop one owner; the last one frees the rep (a leaked rep, refcount -1, has a single owner) */
static void rep_dispose(uint32_t p) {
    if (p == empty_p()) return;
    if (__atomic_fetch_add(s_refp(p), -1, __ATOMIC_ACQ_REL) <= 0) rt_free(p - REP);
}

/* _M_clone: a private copy with room for `extra` more characters */
static uint32_t rep_clone(cpu_t *c, uint32_t p, uint32_t extra) {
    uint32_t n = s_len(p);
    uint32_t q = rep_create(c, n + extra, s_cap(p));
    if (n) memcpy(rt_mem + q, rt_mem + p, n);
    set_length(q, n);
    return q;
}

/* _M_grab: share the rep (or copy a leaked one) */
static uint32_t rep_grab(cpu_t *c, uint32_t p) {
    if (s_leaked(p)) return rep_clone(c, p, 0);
    if (p != empty_p()) __atomic_fetch_add(s_refp(p), 1, __ATOMIC_ACQ_REL);
    return p;
}

/* a new rep holding n characters (_S_construct): the empty rep when n is 0 */
static uint32_t rep_from(cpu_t *c, const char *src, uint32_t n) {
    if (!n) return empty_p();
    uint32_t q = rep_create(c, n, 0);
    memcpy(rt_mem + q, src, n);
    set_length(q, n);
    return q;
}

/* _M_mutate(pos, len1, len2): replace len1 characters at pos by len2 uninitialized ones, unsharing as needed */
static void s_mutate(cpu_t *c, uint32_t s, uint32_t pos, uint32_t len1, uint32_t len2) {
    uint32_t p = rt_ld32(s);
    uint32_t old = s_len(p), new_size = old + len2 - len1, how_much = old - pos - len1;
    if (new_size > s_cap(p) || s_shared(p)) {
        uint32_t q = rep_create(c, new_size, s_cap(p));
        if (pos) memcpy(rt_mem + q, rt_mem + p, pos);
        if (how_much) memcpy(rt_mem + q + pos + len2, rt_mem + p + pos + len1, how_much);
        rep_dispose(p);
        rt_st32(s, q);
        p = q;
    } else if (how_much && len1 != len2) {
        memmove(rt_mem + p + pos + len2, rt_mem + p + pos + len1, how_much);
    }
    set_length(p, new_size);
}

/* _M_leak: make the characters private and unshareable (a reference into them is being handed out) */
static void s_leak(cpu_t *c, uint32_t s) {
    uint32_t p = rt_ld32(s);
    if (s_leaked(p) || p == empty_p()) return;
    if (s_shared(p)) s_mutate(c, s, 0, 0, 0);
    rt_st32(rt_ld32(s) - 4, (uint32_t)-1);
}

static void s_reserve(cpu_t *c, uint32_t s, uint32_t res) {
    uint32_t p = rt_ld32(s);
    if (res != s_cap(p) || s_shared(p)) {
        if (res > MAX_SIZE) cxx_throw(c, "length_error", "basic_string::reserve");
        if (res < s_len(p)) res = s_len(p);
        uint32_t q = rep_clone(c, p, res - s_len(p));
        rep_dispose(p);
        rt_st32(s, q);
    }
}

/* append n characters from a host buffer (already copied out of game memory) */
static void s_append(cpu_t *c, uint32_t s, const char *src, uint32_t n) {
    if (!n) return;
    uint32_t p = rt_ld32(s);
    check_length(c, p, 0, n, "basic_string::append");
    uint32_t len = s_len(p) + n;
    if (len > s_cap(p) || s_shared(p)) s_reserve(c, s, len);
    p = rt_ld32(s);
    memcpy(rt_mem + p + s_len(p), src, n);
    set_length(p, len);
}

static void s_append_game(cpu_t *c, uint32_t s, uint32_t src, uint32_t n) {
    char *b = hcopy(rt_mem + src, n);
    s_append(c, s, b, n);
    free(b);
}

static void s_assign_game(cpu_t *c, uint32_t s, uint32_t src, uint32_t n) {
    uint32_t p = rt_ld32(s);
    check_length(c, p, s_len(p), n, "basic_string::assign");
    char *b = hcopy(rt_mem + src, n);
    s_mutate(c, s, 0, s_len(p), n);
    if (n) memcpy(rt_mem + rt_ld32(s), b, n);
    free(b);
}

static void s_assign_str(cpu_t *c, uint32_t s, uint32_t other) {
    uint32_t p = rt_ld32(s), q = rt_ld32(other);
    if (p == q) return;
    uint32_t t = rep_grab(c, q);
    rep_dispose(p);
    rt_st32(s, t);
}

static void s_insert_game(cpu_t *c, uint32_t s, uint32_t pos, uint32_t src, uint32_t n) {
    uint32_t p = rt_ld32(s);
    check_pos(c, p, pos, "basic_string::insert");
    check_length(c, p, 0, n, "basic_string::insert");
    char *b = hcopy(rt_mem + src, n);
    s_mutate(c, s, pos, 0, n);
    if (n) memcpy(rt_mem + rt_ld32(s) + pos, b, n);
    free(b);
}

static int s_compare(uint32_t p, const char *o, uint32_t on) {
    uint32_t n = s_len(p), k = n < on ? n : on;
    int r = memcmp(rt_mem + p, o, k);
    if (!r) r = (int)(n - on);
    return r;
}

/* constructors (Darwin ARM constructors return void; r0 = this is left as is) */
IMP(_ZNSsC1Ev) { rt_st32(A(0), empty_p()); RET(A(0)); }
IMP(_ZNSsC1ERKSs) { rt_st32(A(0), rep_grab(c, rt_ld32(A(1)))); RET(A(0)); }
IMP(_ZNSsC1EPKcRKSaIcE) {
    uint32_t src = A(1);
    if (!src) { rt_log("std::string(NULL): logic_error in libstdc++; constructing an empty string"); rt_print_trace(c); }
    uint32_t n = src ? (uint32_t)strlen(rt_str(src)) : 0;
    rt_st32(A(0), rep_from(c, src ? rt_str(src) : "", n));
    RET(A(0));
}
IMP(_ZNSsC1EPKcmRKSaIcE) {
    uint32_t src = A(1), n = A(2);
    if (!src && n) { rt_log("std::string(NULL, %u): logic_error in libstdc++; constructing an empty string", n); n = 0; }
    rt_st32(A(0), rep_from(c, n ? (const char *)(rt_mem + src) : "", n));
    RET(A(0));
}
IMP(_ZNSsD1Ev) { rep_dispose(rt_ld32(A(0))); RET(A(0)); }
IMP(_ZNSsD2Ev) { rep_dispose(rt_ld32(A(0))); RET(A(0)); }

/* accessors */
IMP(_ZNKSs5c_strEv) { RET(rt_ld32(A(0))); }
IMP(_ZNKSs6lengthEv) { RET(s_len(rt_ld32(A(0)))); }
IMP(_ZNSsixEm) { s_leak(c, A(0)); RET(rt_ld32(A(0)) + A(1)); }
IMP(_ZNSs2atEm) {
    if (A(1) >= s_len(rt_ld32(A(0)))) cxx_throw(c, "out_of_range", "basic_string::at");
    s_leak(c, A(0));
    RET(rt_ld32(A(0)) + A(1));
}

/* find(const char *s, size_type pos) */
IMP(_ZNKSs4findEPKcm) {
    uint32_t p = rt_ld32(A(0)), size = s_len(p), pos = A(2);
    const char *s = rt_str(A(1)), *d = (const char *)(rt_mem + p);
    uint32_t n = (uint32_t)strlen(s);
    if (!n) { RET(pos <= size ? pos : NPOS); return; }
    if (n <= size)
        for (; pos <= size - n; pos++)
            if (d[pos] == s[0] && !memcmp(d + pos + 1, s + 1, n - 1)) { RET(pos); return; }
    RET(NPOS);
}

/* substr(pos, n) const: r0 = result, r1 = this */
IMP(_ZNKSs6substrEmm) {
    uint32_t res = A(0), p = rt_ld32(A(1)), pos = A(2);
    check_pos(c, p, pos, "basic_string::substr");
    uint32_t n = limit(p, pos, A(3));
    char *b = hcopy(rt_mem + p + pos, n);
    rt_st32(res, rep_from(c, b, n));
    free(b);
    RET(res);
}

IMP(_ZNKSs7compareEPKc) { const char *o = rt_str(A(1)); RET(s_compare(rt_ld32(A(0)), o, (uint32_t)strlen(o))); }
IMP(_ZNKSs7compareERKSs) {
    uint32_t q = rt_ld32(A(1));
    RET(s_compare(rt_ld32(A(0)), (const char *)(rt_mem + q), s_len(q)));
}

/* modifiers: each returns *this */
IMP(_ZNSs6appendEPKcm) { s_append_game(c, A(0), A(1), A(2)); RET(A(0)); }
IMP(_ZNSs6appendERKSs) { uint32_t q = rt_ld32(A(1)); s_append_game(c, A(0), q, s_len(q)); RET(A(0)); }
IMP(_ZNSs6appendEmc) {
    uint32_t s = A(0), n = A(1);
    if (n) {
        char *b = malloc(n);
        if (!b) rt_fatal("out of host memory");
        memset(b, (int)(A(2) & 0xff), n);
        s_append(c, s, b, n);
        free(b);
    }
    RET(s);
}
IMP(_ZNSs6assignEPKcm) { s_assign_game(c, A(0), A(1), A(2)); RET(A(0)); }
IMP(_ZNSs6assignERKSs) { s_assign_str(c, A(0), A(1)); RET(A(0)); }
IMP(_ZNSsaSEPKc) { s_assign_game(c, A(0), A(1), (uint32_t)strlen(rt_str(A(1)))); RET(A(0)); }
IMP(_ZNSsaSERKSs) { s_assign_str(c, A(0), A(1)); RET(A(0)); }
/* insert(pos1, const string &str, pos2, n) */
IMP(_ZNSs6insertEmRKSsmm) {
    uint32_t q = rt_ld32(A(2)), pos2 = A(3);
    check_pos(c, q, pos2, "basic_string::insert");
    s_insert_game(c, A(0), A(1), q + pos2, limit(q, pos2, rt_arg(c, 4)));
    RET(A(0));
}
IMP(_ZNSs6resizeEmc) {
    uint32_t s = A(0), n = A(1), size = s_len(rt_ld32(s));
    if (n > MAX_SIZE) cxx_throw(c, "length_error", "basic_string::resize");
    if (size < n) {
        char *b = malloc(n - size);
        if (!b) rt_fatal("out of host memory");
        memset(b, (int)(A(2) & 0xff), n - size);
        s_append(c, s, b, n - size);
        free(b);
    } else if (n < size) {
        s_mutate(c, s, n, size - n, 0);
    }
}
IMP(_ZNSs7reserveEm) { s_reserve(c, A(0), A(1)); }
IMP(_ZNSs9push_backEc) { char ch = (char)(A(1) & 0xff); s_append(c, A(0), &ch, 1); }

static uint32_t resolve_string(const char *name) {
    return strcmp(name, "_ZNSs4_Rep20_S_empty_rep_storageE") ? 0 : empty_storage;
}

/* ---- std::allocator<char>, ios_base::Init: nothing to do ---------------------------------------------------- */
IMP(_ZNSaIcEC1Ev) { RET(A(0)); }
IMP(_ZNSaIcED1Ev) { RET(A(0)); }
IMP(_ZNSt8ios_base4InitC1Ev) { RET(A(0)); }
IMP(_ZNSt8ios_base4InitD1Ev) { RET(A(0)); }

/* ---- __throw_* ----------------------------------------------------------------------------------------------- */
IMP(_ZSt17__throw_bad_allocv) { cxx_throw(c, "bad_alloc", "std::bad_alloc"); }
IMP(_ZSt20__throw_length_errorPKc) { cxx_throw(c, "length_error", rt_str(A(0))); }
IMP(_ZSt20__throw_out_of_rangePKc) { cxx_throw(c, "out_of_range", rt_str(A(0))); }

/* ---- red-black tree (GCC tree.cc on game addresses) ------------------------------------------------------- */
enum { RED = 0, BLACK = 1 };
#define COLOR(x) rt_ld32((x) + 0)
#define PARENT(x) rt_ld32((x) + 4)
#define LEFT(x) rt_ld32((x) + 8)
#define RIGHT(x) rt_ld32((x) + 12)
#define SET_COLOR(x, v) rt_st32((x) + 0, (v))
#define SET_PARENT(x, v) rt_st32((x) + 4, (v))
#define SET_LEFT(x, v) rt_st32((x) + 8, (v))
#define SET_RIGHT(x, v) rt_st32((x) + 12, (v))

static uint32_t rb_increment(uint32_t x) {
    if (RIGHT(x)) {
        x = RIGHT(x);
        while (LEFT(x)) x = LEFT(x);
    } else {
        uint32_t y = PARENT(x);
        while (x == RIGHT(y)) { x = y; y = PARENT(y); }
        if (RIGHT(x) != y) x = y;
    }
    return x;
}

static uint32_t rb_decrement(uint32_t x) {
    if (COLOR(x) == RED && PARENT(PARENT(x)) == x) {
        x = RIGHT(x); /* the header (end()): back to the rightmost node */
    } else if (LEFT(x)) {
        uint32_t y = LEFT(x);
        while (RIGHT(y)) y = RIGHT(y);
        x = y;
    } else {
        uint32_t y = PARENT(x);
        while (x == LEFT(y)) { x = y; y = PARENT(y); }
        x = y;
    }
    return x;
}

/* `root` is the address of the word holding the root (the header's parent field) */
static void rb_rotate_left(uint32_t x, uint32_t root) {
    uint32_t y = RIGHT(x);
    SET_RIGHT(x, LEFT(y));
    if (LEFT(y)) SET_PARENT(LEFT(y), x);
    SET_PARENT(y, PARENT(x));
    if (x == rt_ld32(root)) rt_st32(root, y);
    else if (x == LEFT(PARENT(x))) SET_LEFT(PARENT(x), y);
    else SET_RIGHT(PARENT(x), y);
    SET_LEFT(y, x);
    SET_PARENT(x, y);
}

static void rb_rotate_right(uint32_t x, uint32_t root) {
    uint32_t y = LEFT(x);
    SET_LEFT(x, RIGHT(y));
    if (RIGHT(y)) SET_PARENT(RIGHT(y), x);
    SET_PARENT(y, PARENT(x));
    if (x == rt_ld32(root)) rt_st32(root, y);
    else if (x == RIGHT(PARENT(x))) SET_RIGHT(PARENT(x), y);
    else SET_LEFT(PARENT(x), y);
    SET_RIGHT(y, x);
    SET_PARENT(x, y);
}

static void rb_insert_and_rebalance(int insert_left, uint32_t x, uint32_t p, uint32_t header) {
    uint32_t root = header + 4;
    SET_PARENT(x, p);
    SET_LEFT(x, 0);
    SET_RIGHT(x, 0);
    SET_COLOR(x, RED);
    if (insert_left) {
        SET_LEFT(p, x); /* also makes leftmost = x when p == header */
        if (p == header) { SET_PARENT(header, x); SET_RIGHT(header, x); }
        else if (p == LEFT(header)) SET_LEFT(header, x);
    } else {
        SET_RIGHT(p, x);
        if (p == RIGHT(header)) SET_RIGHT(header, x);
    }
    while (x != rt_ld32(root) && COLOR(PARENT(x)) == RED) {
        uint32_t xpp = PARENT(PARENT(x));
        if (PARENT(x) == LEFT(xpp)) {
            uint32_t y = RIGHT(xpp);
            if (y && COLOR(y) == RED) {
                SET_COLOR(PARENT(x), BLACK);
                SET_COLOR(y, BLACK);
                SET_COLOR(xpp, RED);
                x = xpp;
            } else {
                if (x == RIGHT(PARENT(x))) { x = PARENT(x); rb_rotate_left(x, root); }
                SET_COLOR(PARENT(x), BLACK);
                SET_COLOR(xpp, RED);
                rb_rotate_right(xpp, root);
            }
        } else {
            uint32_t y = LEFT(xpp);
            if (y && COLOR(y) == RED) {
                SET_COLOR(PARENT(x), BLACK);
                SET_COLOR(y, BLACK);
                SET_COLOR(xpp, RED);
                x = xpp;
            } else {
                if (x == LEFT(PARENT(x))) { x = PARENT(x); rb_rotate_right(x, root); }
                SET_COLOR(PARENT(x), BLACK);
                SET_COLOR(xpp, RED);
                rb_rotate_left(xpp, root);
            }
        }
    }
    SET_COLOR(rt_ld32(root), BLACK);
}

/* unlinks z and rebalances; returns the node the caller frees (z itself) */
static uint32_t rb_rebalance_for_erase(uint32_t z, uint32_t header) {
    uint32_t root = header + 4, leftmost = header + 8, rightmost = header + 12;
    uint32_t y = z, x, x_parent;
    if (!LEFT(y)) x = RIGHT(y);          /* z has at most one non-null child: y == z */
    else if (!RIGHT(y)) x = LEFT(y);     /* z has exactly one non-null child: y == z */
    else {                               /* z has two children: y = z's successor, x might be null */
        y = RIGHT(y);
        while (LEFT(y)) y = LEFT(y);
        x = RIGHT(y);
    }
    if (y != z) {
        /* relink y in place of z; y is z's successor */
        SET_PARENT(LEFT(z), y);
        SET_LEFT(y, LEFT(z));
        if (y != RIGHT(z)) {
            x_parent = PARENT(y);
            if (x) SET_PARENT(x, PARENT(y));
            SET_LEFT(PARENT(y), x); /* y must be a left child */
            SET_RIGHT(y, RIGHT(z));
            SET_PARENT(RIGHT(z), y);
        } else {
            x_parent = y;
        }
        if (rt_ld32(root) == z) rt_st32(root, y);
        else if (LEFT(PARENT(z)) == z) SET_LEFT(PARENT(z), y);
        else SET_RIGHT(PARENT(z), y);
        SET_PARENT(y, PARENT(z));
        uint32_t t = COLOR(y);
        SET_COLOR(y, COLOR(z));
        SET_COLOR(z, t);
        y = z; /* y now points to the node actually deleted */
    } else {
        x_parent = PARENT(y);
        if (x) SET_PARENT(x, PARENT(y));
        if (rt_ld32(root) == z) rt_st32(root, x);
        else if (LEFT(PARENT(z)) == z) SET_LEFT(PARENT(z), x);
        else SET_RIGHT(PARENT(z), x);
        if (rt_ld32(leftmost) == z) {
            if (!RIGHT(z)) rt_st32(leftmost, PARENT(z)); /* LEFT(z) is null too */
            else { uint32_t m = x; while (LEFT(m)) m = LEFT(m); rt_st32(leftmost, m); }
        }
        if (rt_ld32(rightmost) == z) {
            if (!LEFT(z)) rt_st32(rightmost, PARENT(z)); /* RIGHT(z) is null too */
            else { uint32_t m = x; while (RIGHT(m)) m = RIGHT(m); rt_st32(rightmost, m); }
        }
    }
    if (COLOR(y) != RED) {
        while (x != rt_ld32(root) && (!x || COLOR(x) == BLACK)) {
            if (x == LEFT(x_parent)) {
                uint32_t w = RIGHT(x_parent);
                if (COLOR(w) == RED) {
                    SET_COLOR(w, BLACK);
                    SET_COLOR(x_parent, RED);
                    rb_rotate_left(x_parent, root);
                    w = RIGHT(x_parent);
                }
                if ((!LEFT(w) || COLOR(LEFT(w)) == BLACK) && (!RIGHT(w) || COLOR(RIGHT(w)) == BLACK)) {
                    SET_COLOR(w, RED);
                    x = x_parent;
                    x_parent = PARENT(x_parent);
                } else {
                    if (!RIGHT(w) || COLOR(RIGHT(w)) == BLACK) {
                        SET_COLOR(LEFT(w), BLACK);
                        SET_COLOR(w, RED);
                        rb_rotate_right(w, root);
                        w = RIGHT(x_parent);
                    }
                    SET_COLOR(w, COLOR(x_parent));
                    SET_COLOR(x_parent, BLACK);
                    if (RIGHT(w)) SET_COLOR(RIGHT(w), BLACK);
                    rb_rotate_left(x_parent, root);
                    break;
                }
            } else {
                /* same as above, with right <-> left */
                uint32_t w = LEFT(x_parent);
                if (COLOR(w) == RED) {
                    SET_COLOR(w, BLACK);
                    SET_COLOR(x_parent, RED);
                    rb_rotate_right(x_parent, root);
                    w = LEFT(x_parent);
                }
                if ((!RIGHT(w) || COLOR(RIGHT(w)) == BLACK) && (!LEFT(w) || COLOR(LEFT(w)) == BLACK)) {
                    SET_COLOR(w, RED);
                    x = x_parent;
                    x_parent = PARENT(x_parent);
                } else {
                    if (!LEFT(w) || COLOR(LEFT(w)) == BLACK) {
                        SET_COLOR(RIGHT(w), BLACK);
                        SET_COLOR(w, RED);
                        rb_rotate_left(w, root);
                        w = LEFT(x_parent);
                    }
                    SET_COLOR(w, COLOR(x_parent));
                    SET_COLOR(x_parent, BLACK);
                    if (LEFT(w)) SET_COLOR(LEFT(w), BLACK);
                    rb_rotate_right(x_parent, root);
                    break;
                }
            }
        }
        if (x) SET_COLOR(x, BLACK);
    }
    return y;
}

IMP(_ZSt18_Rb_tree_incrementPSt18_Rb_tree_node_base) { RET(rb_increment(A(0))); }
IMP(_ZSt18_Rb_tree_incrementPKSt18_Rb_tree_node_base) { RET(rb_increment(A(0))); }
IMP(_ZSt18_Rb_tree_decrementPSt18_Rb_tree_node_base) { RET(rb_decrement(A(0))); }
/* (bool insert_left, node x, node p, header &) */
IMP(_ZSt29_Rb_tree_insert_and_rebalancebPSt18_Rb_tree_node_baseS0_RS_) {
    rb_insert_and_rebalance((A(0) & 0xff) != 0, A(1), A(2), A(3));
}
IMP(_ZSt28_Rb_tree_rebalance_for_erasePSt18_Rb_tree_node_baseRS_) { RET(rb_rebalance_for_erase(A(0), A(1))); }

/* ---- _List_node_base { next, prev } ------------------------------------------------------------------------ */
#define NEXT(x) rt_ld32((x) + 0)
#define PREV(x) rt_ld32((x) + 4)
#define SET_NEXT(x, v) rt_st32((x) + 0, (v))
#define SET_PREV(x, v) rt_st32((x) + 4, (v))

/* this->hook(position): insert this before position */
IMP(_ZNSt15_List_node_base4hookEPS_) {
    uint32_t t = A(0), pos = A(1);
    SET_NEXT(t, pos);
    SET_PREV(t, PREV(pos));
    SET_NEXT(PREV(pos), t);
    SET_PREV(pos, t);
}
IMP(_ZNSt15_List_node_base6unhookEv) {
    uint32_t t = A(0), next = NEXT(t), prev = PREV(t);
    SET_NEXT(prev, next);
    SET_PREV(next, prev);
}
/* this->transfer(first, last): move [first, last) before this */
IMP(_ZNSt15_List_node_base8transferEPS_S0_) {
    uint32_t t = A(0), first = A(1), last = A(2);
    if (t == last) return;
    SET_NEXT(PREV(last), t);
    SET_NEXT(PREV(first), last);
    SET_NEXT(PREV(t), first);
    uint32_t tmp = PREV(t);
    SET_PREV(t, PREV(last));
    SET_PREV(last, PREV(first));
    SET_PREV(first, tmp);
}

/* ---- std::ostringstream ------------------------------------------------------------------------------------ */
enum {
    OSS_SIZE = 0xb4, OSS_SB = 0x04, OSS_IOS = 0x2c,
    SB_MODE = 0x20, SB_STRING = 0x24,
    IOS_PRECISION = 0x04, IOS_WIDTH = 0x08, IOS_FLAGS = 0x0c, IOS_STATE = 0x14, IOS_LOCAL_WORD = 0x24,
    IOS_WORD_SIZE = 0x64, IOS_WORD = 0x68, IOS_FILL = 0x74, IOS_FILL_INIT = 0x75, IOS_STREAMBUF = 0x78,
};
enum { F_DEC = 0x2, F_HEX = 0x8, F_INTERNAL = 0x10, F_LEFT = 0x20, F_OCT = 0x40, F_SHOWBASE = 0x200,
       F_SHOWPOS = 0x800, F_SKIPWS = 0x1000, F_UPPERCASE = 0x4000, F_BASEFIELD = 0x4a, F_ADJUSTFIELD = 0xb0 };
enum { OUT_MODE = 0x10, BADBIT = 1, FAILBIT = 4 };

static uint32_t oss_vtbl, sb_vtbl, ios_vtbl; /* address points (vtable + 12 / + 8) */

static void oss_destroy(uint32_t obj) {
    uint32_t s = obj + OSS_SB + SB_STRING;
    rep_dispose(rt_ld32(s));
    rt_st32(s, empty_p());
}

/* the virtual destructors, should the game ever destroy a stream through its vtable */
static void oss_vdtor(cpu_t *c, uint8_t *m) { (void)m; oss_destroy(A(0)); }
/* The deleting destructors would hand the memory to ::operator delete, which the game defines itself (no _Znwm or
 * _ZdlPv import): only game code knows which allocator a heap stream came from, so the block is left alone. */
static void oss_delete_note(void) {
    static int once;
    if (!once++) rt_log("deleting destructor of a heap std::ostringstream: its storage is not freed");
}
static void oss_vdtor_delete(cpu_t *c, uint8_t *m) { (void)m; oss_destroy(A(0)); oss_delete_note(); }
static void oss_ios_vdtor(cpu_t *c, uint8_t *m) { (void)m; oss_destroy(A(0) - OSS_IOS); }
static void oss_ios_vdtor_delete(cpu_t *c, uint8_t *m) { (void)m; oss_destroy(A(0) - OSS_IOS); oss_delete_note(); }
static void sb_vdtor(cpu_t *c, uint8_t *m) { (void)m; oss_destroy(A(0) - OSS_SB); }

/* ostringstream(openmode) */
IMP(_ZNSt19basic_ostringstreamIcSt11char_traitsIcESaIcEEC1ESt13_Ios_Openmode) {
    uint32_t o = A(0), sb = o + OSS_SB, ios = o + OSS_IOS;
    memset(rt_mem + o, 0, OSS_SIZE);
    rt_st32(o, oss_vtbl);
    rt_st32(sb, sb_vtbl);
    rt_st32(sb + SB_MODE, A(1) | OUT_MODE);
    rt_st32(sb + SB_STRING, empty_p());
    rt_st32(ios, ios_vtbl);
    rt_st32(ios + IOS_PRECISION, 6);
    rt_st32(ios + IOS_FLAGS, F_SKIPWS | F_DEC);
    rt_st32(ios + IOS_WORD_SIZE, 8);
    rt_st32(ios + IOS_WORD, ios + IOS_LOCAL_WORD);
    rt_st32(ios + IOS_STREAMBUF, sb);
    RET(o);
}
IMP(_ZNSt19basic_ostringstreamIcSt11char_traitsIcESaIcEED1Ev) { oss_destroy(A(0)); RET(A(0)); }

/* basic_stringbuf::str() const: r0 = result string, r1 = the stringbuf */
IMP(_ZNKSt15basic_stringbufIcSt11char_traitsIcESaIcEE3strEv) {
    uint32_t res = A(0), sb = A(1);
    rt_st32(res, rep_grab(c, rt_ld32(sb + SB_STRING)));
    RET(res);
}

IMP(_ZNKSt9basic_iosIcSt11char_traitsIcEE5widenEc) { RET(A(1) & 0xff); } /* the "C" locale's ctype<char> */

/* ostream::_M_insert<long> with num_put<char>::_M_insert_int (GCC 4.2): base, sign, showbase, uppercase, width,
 * fill and adjustment, then the width goes back to 0. A stream that is not good() fails the sentry: failbit is
 * set and nothing (the width included) changes. */
static void ostream_insert(cpu_t *c, uint32_t os, int32_t v) {
    uint32_t ios = os + rt_ld32(rt_ld32(os) - 12); /* vptr[-3]: offset of the virtual base basic_ios */
    uint32_t flags = rt_ld32(ios + IOS_FLAGS), sb = rt_ld32(ios + IOS_STREAMBUF);
    uint32_t state = rt_ld32(ios + IOS_STATE);
    if (state || !sb) { rt_st32(ios + IOS_STATE, state | FAILBIT | (sb ? 0 : BADBIT)); return; }
    int32_t width = (int32_t)rt_ld32(ios + IOS_WIDTH);
    if (!rt_mem[ios + IOS_FILL_INIT]) { rt_mem[ios + IOS_FILL] = ' '; rt_mem[ios + IOS_FILL_INIT] = 1; }
    char fill = (char)rt_mem[ios + IOS_FILL];

    char digits[40], prefix[4];
    int nd = 0, np = 0;
    uint32_t basefield = flags & F_BASEFIELD;
    uint32_t base = basefield == F_HEX ? 16 : basefield == F_OCT ? 8 : 10;
    const char *set = (flags & F_UPPERCASE) ? "0123456789ABCDEF" : "0123456789abcdef";
    uint32_t u;
    if (base == 10) {
        u = v < 0 ? 0u - (uint32_t)v : (uint32_t)v;
        if (v < 0) prefix[np++] = '-';
        else if (v > 0 && (flags & F_SHOWPOS)) prefix[np++] = '+'; /* GCC 4.2 prints no '+' before 0 */
    } else {
        u = (uint32_t)v;
        if ((flags & F_SHOWBASE) && u) {
            prefix[np++] = '0';
            if (base == 16) prefix[np++] = (flags & F_UPPERCASE) ? 'X' : 'x';
        }
    }
    do { digits[nd++] = set[u % base]; u /= base; } while (u);

    /* internal adjustment pads after a sign or a 0x/0X, not after an octal 0 (__pad::_S_pad) */
    uint32_t adjust = flags & F_ADJUSTFIELD;
    int keep = adjust == F_INTERNAL && (base != 8) ? np : 0;
    int len = np + nd, pad = width > len ? width - len : 0;
    char *out = malloc((size_t)len + (size_t)pad + 1);
    if (!out) rt_fatal("out of host memory");
    int n = 0;
    for (int k = 0; k < keep; k++) out[n++] = prefix[k];
    if (adjust != F_LEFT) for (int k = 0; k < pad; k++) out[n++] = fill;
    for (int k = keep; k < np; k++) out[n++] = prefix[k];
    while (nd) out[n++] = digits[--nd];
    if (adjust == F_LEFT) for (int k = 0; k < pad; k++) out[n++] = fill;
    s_append(c, sb + SB_STRING, out, (uint32_t)n);
    free(out);
    rt_st32(ios + IOS_WIDTH, 0);
}

/* operator<<(int): hex and oct print the unsigned value, which a 32-bit long formatting does anyway */
IMP(_ZNSolsEi) { ostream_insert(c, A(0), (int32_t)A(1)); RET(A(0)); }
IMP(_ZNSo9_M_insertIlEERSoT_) { ostream_insert(c, A(0), (int32_t)A(1)); RET(A(0)); }

static void oss_init(void) {
    uint32_t dtor = rt_hostfn_add(oss_vdtor, "~ostringstream"), del = rt_hostfn_add(oss_vdtor_delete, "~ostringstream (delete)");
    uint32_t idtor = rt_hostfn_add(oss_ios_vdtor, "~ostringstream (basic_ios)");
    uint32_t idel = rt_hostfn_add(oss_ios_vdtor_delete, "~ostringstream (basic_ios, delete)");
    uint32_t sdtor = rt_hostfn_add(sb_vdtor, "~basic_stringbuf");
    /* a type_info for the stream (class_type_info kind; nothing casts it) */
    uint32_t ti = rt_calloc(1, 8);
    rt_st32(ti, ti_vtables[0] + 8);
    rt_st32(ti + 4, rt_static_string("St19basic_ostringstreamIcSt11char_traitsIcESaIcEE"));
    /* ostream part: { vbase offset, offset to top, type_info } then D1, D0 */
    uint32_t v = rt_calloc(8, 4);
    rt_st32(v + 0, OSS_IOS);
    rt_st32(v + 4, 0);
    rt_st32(v + 8, ti);
    rt_st32(v + 12, dtor);
    rt_st32(v + 16, del);
    oss_vtbl = v + 12;
    /* basic_ios part: { offset to top, type_info } then the destructor thunks */
    v = rt_calloc(8, 4);
    rt_st32(v + 0, (uint32_t)-OSS_IOS);
    rt_st32(v + 4, ti);
    rt_st32(v + 8, idtor);
    rt_st32(v + 12, idel);
    ios_vtbl = v + 8;
    /* stringbuf (a member, not a base, so offset to top 0): only the destructor is meaningful (the put area is
     * never used) */
    v = rt_calloc(20, 4);
    rt_st32(v + 0, 0);
    rt_st32(v + 4, ti);
    rt_st32(v + 8, sdtor);
    rt_st32(v + 12, sdtor);
    sb_vtbl = v + 8;
}

/* ---- type info and __dynamic_cast (Itanium C++ ABI) -------------------------------------------------------- */
enum { TI_CLASS, TI_SI, TI_VMI, TI_OTHER };
enum { VMI_VIRTUAL = 1, VMI_PUBLIC = 2 };

static int ti_kind(uint32_t ti) {
    uint32_t v = rt_ld32(ti) - 8;
    for (int k = 0; k < 3; k++)
        if (v == ti_vtables[k]) return k;
    return TI_OTHER;
}

/* type_info::operator==: the same object, or the same mangled name (a leading '*' marks a local type that
 * only compares by address) */
static int ti_eq(uint32_t a, uint32_t b) {
    if (a == b) return 1;
    if (!a || !b) return 0;
    const char *na = rt_str(rt_ld32(a + 4)), *nb = rt_str(rt_ld32(b + 4));
    if (!na || !nb || na[0] == '*' || nb[0] == '*') return 0;
    return !strcmp(na, nb);
}

typedef struct { uint32_t addr; int pub; } subobj;
typedef struct { uint32_t want; subobj hit[32]; int n; } search;

/* every subobject of type s->want inside the object of type ti at addr, with whether its path is public */
static void collect(search *s, uint32_t ti, uint32_t addr, int pub, int depth) {
    if (depth > 64) return;
    if (ti_eq(ti, s->want)) {
        for (int k = 0; k < s->n; k++)
            if (s->hit[k].addr == addr) { s->hit[k].pub |= pub; return; } /* a shared virtual base */
        if (s->n < 32) s->hit[s->n++] = (subobj){addr, pub};
        return;
    }
    switch (ti_kind(ti)) {
    case TI_SI:
        collect(s, rt_ld32(ti + 8), addr, pub, depth + 1);
        break;
    case TI_VMI: {
        uint32_t count = rt_ld32(ti + 12);
        for (uint32_t k = 0; k < count && k < 256; k++) {
            uint32_t base = rt_ld32(ti + 16 + 8 * k);
            int32_t of = (int32_t)rt_ld32(ti + 20 + 8 * k), off = of >> 8;
            if (of & VMI_VIRTUAL) off = (int32_t)rt_ld32(rt_ld32(addr) + (uint32_t)off);
            collect(s, base, addr + (uint32_t)off, pub && (of & VMI_PUBLIC), depth + 1);
        }
        break;
    }
    default:
        break;
    }
}

/* is (src_type at src) a public base subobject of (ti at addr)? */
static int is_public_base(uint32_t ti, uint32_t addr, uint32_t src_type, uint32_t src) {
    search s = {src_type, {{0, 0}}, 0};
    collect(&s, ti, addr, 1, 0);
    for (int k = 0; k < s.n; k++)
        if (s.hit[k].addr == src && s.hit[k].pub) return 1;
    return 0;
}

/* __dynamic_cast(src, src_type, dst_type, src2dst): src2dst >= 0 is the offset of src in a dst (a unique public
 * non-virtual base), -1 no hint, -2 src is not a public base of dst, -3 src is a multiple public base of dst */
IMP(__dynamic_cast) {
    uint32_t src = A(0), src_type = A(1), dst_type = A(2);
    int32_t hint = (int32_t)A(3);
    if (!src) { RET(0); return; }
    uint32_t vptr = rt_ld32(src);
    uint32_t whole = src + rt_ld32(vptr - 8), whole_type = rt_ld32(vptr - 4);
    if (!whole_type) { RET(0); return; }
    if (ti_eq(whole_type, dst_type)) { /* to the most derived object */
        RET(is_public_base(whole_type, whole, src_type, src) ? whole : 0);
        return;
    }
    search d = {dst_type, {{0, 0}}, 0};
    collect(&d, whole_type, whole, 1, 0);
    /* downcast: a dst containing src as a public base; it must be unique */
    uint32_t found = 0;
    int nfound = 0;
    if (hint != -2)
        for (int k = 0; k < d.n; k++) {
            if (hint >= 0 && d.hit[k].addr + (uint32_t)hint != src) continue;
            if (is_public_base(dst_type, d.hit[k].addr, src_type, src)) { found = d.hit[k].addr; nfound++; }
        }
    if (nfound == 1) { RET(found); return; }
    if (nfound > 1) { RET(0); return; }
    /* cross cast: src a public base of the whole object, which has exactly one public dst */
    if (is_public_base(whole_type, whole, src_type, src)) {
        uint32_t pub = 0;
        int npub = 0;
        for (int k = 0; k < d.n; k++)
            if (d.hit[k].pub) { pub = d.hit[k].addr; npub++; }
        if (npub == 1) { RET(pub); return; }
    }
    RET(0);
}

static uint32_t resolve_typeinfo(const char *name) {
    if (!strcmp(name, "_ZTVN10__cxxabiv117__class_type_infoE")) return ti_vtables[TI_CLASS];
    if (!strcmp(name, "_ZTVN10__cxxabiv120__si_class_type_infoE")) return ti_vtables[TI_SI];
    if (!strcmp(name, "_ZTVN10__cxxabiv121__vmi_class_type_infoE")) return ti_vtables[TI_VMI];
    return 0;
}

/* ---- catching -------------------------------------------------------------------------------------------------
 * The argument of __cxa_begin_catch / objc_begin_catch is the _Unwind_Exception header (24 bytes: exception
 * class 8, cleanup, private_1, private_2, padded to 8-byte alignment); the thrown C++ object follows it, and an
 * Objective-C exception keeps the object pointer in the word after it. */
#define UNWIND_HEADER 24u
static __thread int catch_depth;

IMP(__cxa_begin_catch) {
    uint32_t e = A(0);
    rt_log("__cxa_begin_catch(%#x): no exception can be in flight", e);
    catch_depth++;
    RET(e ? e + UNWIND_HEADER : 0);
}
IMP(__cxa_end_catch) { if (catch_depth > 0) catch_depth--; }
IMP(__cxa_rethrow) { cxx_throw(c, "(rethrown)", "__cxa_rethrow"); }
IMP(objc_begin_catch) {
    uint32_t e = A(0);
    rt_log("objc_begin_catch(%#x): no exception can be in flight", e);
    catch_depth++;
    RET(e ? rt_ld32(e + UNWIND_HEADER) : 0);
}
IMP(objc_end_catch) { if (catch_depth > 0) catch_depth--; }

/* the personality routines are only ever called by an unwinder, which does not exist here */
static void personality(cpu_t *c, uint8_t *m) {
    (void)m;
    rt_print_trace(c);
    rt_fatal("an SjLj personality routine was called: exception unwinding is not supported");
}

static uint32_t resolve_personality(const char *name) {
    if (!strcmp(name, "__gxx_personality_sj0")) return personality_gxx;
    if (!strcmp(name, "__objc_personality_v0")) return personality_objc;
    return 0;
}

/* ---- registration -------------------------------------------------------------------------------------------- */
static uint32_t resolve(const char *name) {
    uint32_t a = resolve_string(name);
    if (!a) a = resolve_typeinfo(name);
    if (!a) a = resolve_personality(name);
    return a;
}

void rt_libstdcxx_register(void) {
    empty_storage = rt_calloc(1, 16);
    for (int k = 0; k < 3; k++) ti_vtables[k] = rt_calloc(16, 4); /* offset to top, type_info, virtual functions */
    personality_gxx = rt_hostfn_add(personality, "__gxx_personality_sj0");
    personality_objc = rt_hostfn_add(personality, "__objc_personality_v0");
    oss_init();
    rt_data_resolver_add(resolve);

    REG(_ZNSsC1Ev); REG(_ZNSsC1ERKSs); REG(_ZNSsC1EPKcRKSaIcE); REG(_ZNSsC1EPKcmRKSaIcE);
    REG(_ZNSsD1Ev); REG(_ZNSsD2Ev);
    REG(_ZNKSs5c_strEv); REG(_ZNKSs6lengthEv); REG(_ZNSsixEm); REG(_ZNSs2atEm); REG(_ZNKSs4findEPKcm);
    REG(_ZNKSs6substrEmm); REG(_ZNKSs7compareEPKc); REG(_ZNKSs7compareERKSs);
    REG(_ZNSs6appendEPKcm); REG(_ZNSs6appendERKSs); REG(_ZNSs6appendEmc);
    REG(_ZNSs6assignEPKcm); REG(_ZNSs6assignERKSs); REG(_ZNSsaSEPKc); REG(_ZNSsaSERKSs);
    REG(_ZNSs6insertEmRKSsmm); REG(_ZNSs6resizeEmc); REG(_ZNSs7reserveEm); REG(_ZNSs9push_backEc);
    REG(_ZNSaIcEC1Ev); REG(_ZNSaIcED1Ev); REG(_ZNSt8ios_base4InitC1Ev); REG(_ZNSt8ios_base4InitD1Ev);
    REG(_ZSt17__throw_bad_allocv); REG(_ZSt20__throw_length_errorPKc); REG(_ZSt20__throw_out_of_rangePKc);
    REG(_ZSt18_Rb_tree_incrementPSt18_Rb_tree_node_base); REG(_ZSt18_Rb_tree_incrementPKSt18_Rb_tree_node_base);
    REG(_ZSt18_Rb_tree_decrementPSt18_Rb_tree_node_base);
    REG(_ZSt29_Rb_tree_insert_and_rebalancebPSt18_Rb_tree_node_baseS0_RS_);
    REG(_ZSt28_Rb_tree_rebalance_for_erasePSt18_Rb_tree_node_baseRS_);
    REG(_ZNSt15_List_node_base4hookEPS_); REG(_ZNSt15_List_node_base6unhookEv);
    REG(_ZNSt15_List_node_base8transferEPS_S0_);
    REG(_ZNSt19basic_ostringstreamIcSt11char_traitsIcESaIcEEC1ESt13_Ios_Openmode);
    REG(_ZNSt19basic_ostringstreamIcSt11char_traitsIcESaIcEED1Ev);
    REG(_ZNKSt15basic_stringbufIcSt11char_traitsIcESaIcEE3strEv);
    REG(_ZNKSt9basic_iosIcSt11char_traitsIcEE5widenEc);
    REG(_ZNSolsEi); REG(_ZNSo9_M_insertIlEERSoT_);
    REG(__dynamic_cast);
    REG(__cxa_begin_catch); REG(__cxa_end_catch); REG(__cxa_rethrow); REG(objc_begin_catch); REG(objc_end_catch);
}
