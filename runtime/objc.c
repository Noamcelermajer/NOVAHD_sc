/* The Objective-C runtime (modern ABI, 32-bit iOS layouts) for the translated executable.
 *
 * Classes, metaclasses, method lists and categories stay where the compiler put them in game memory; this file
 * only builds lookup tables. System classes (NSObject, NSString, UIView, ...) are created in game memory with
 * the same class_t/class_ro_t layout, so game classes inherit from them through ordinary superclass pointers;
 * their methods are host functions (game addresses in the host-function range).
 *
 * Selectors are game addresses of unique name strings. At load, every selector reference and every method name
 * of the game's method lists is rewritten to the one canonical address for its name.
 *
 * objc_msgSend looks up (class of the receiver, selector) and continues in the method with the caller's register
 * state untouched, as the original does: a translated method returns straight to the caller.
 *
 * Layouts (32-bit):
 *   class_t        { isa, superclass, cache, vtable, data -> class_ro_t }
 *   class_ro_t     { flags, instanceStart, instanceSize, ivarLayout, name, baseMethods, baseProtocols, ivars,
 *                    weakIvarLayout, baseProperties }
 *   method_list_t  { entsize | flags, count, method_t[count] }  method_t { name, types, imp }
 *   category_t     { name, cls, instanceMethods, classMethods, protocols, instanceProperties }
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rt.h"

#define RO_META 1u
#define RO_ROOT 2u

/* ---- a small hash map: 64-bit keys (0 = empty, ~0 = deleted) to 64-bit values ---------------------- */
typedef struct { uint64_t *keys, *vals; uint32_t cap, used; } map64;

static uint64_t mix(uint64_t k) {
    k ^= k >> 33; k *= 0xff51afd7ed558ccdull; k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ull; k ^= k >> 33;
    return k;
}

static int map_get(map64 *m, uint64_t key, uint64_t *val) {
    if (!m->cap) return 0;
    for (uint32_t i = (uint32_t)mix(key) & (m->cap - 1);; i = (i + 1) & (m->cap - 1)) {
        if (m->keys[i] == key) { if (val) *val = m->vals[i]; return 1; }
        if (m->keys[i] == 0) return 0;
    }
}

static void map_put(map64 *m, uint64_t key, uint64_t val);

static void map_grow(map64 *m) {
    map64 old = *m;
    m->cap = old.cap ? old.cap * 2 : 1024;
    m->keys = calloc(m->cap, 8);
    m->vals = calloc(m->cap, 8);
    m->used = 0;
    for (uint32_t i = 0; i < old.cap; i++)
        if (old.keys[i] && old.keys[i] != ~0ull) map_put(m, old.keys[i], old.vals[i]);
    free(old.keys);
    free(old.vals);
}

static void map_put(map64 *m, uint64_t key, uint64_t val) {
    if ((m->used + 1) * 4 >= m->cap * 3) map_grow(m);
    uint32_t i = (uint32_t)mix(key) & (m->cap - 1), tomb = ~0u;
    for (;; i = (i + 1) & (m->cap - 1)) {
        if (m->keys[i] == key) { m->vals[i] = val; return; }
        if (m->keys[i] == ~0ull && tomb == ~0u) tomb = i;
        if (m->keys[i] == 0) break;
    }
    if (tomb != ~0u) i = tomb; else m->used++;
    m->keys[i] = key;
    m->vals[i] = val;
}

static void map_del(map64 *m, uint64_t key) {
    if (!m->cap) return;
    for (uint32_t i = (uint32_t)mix(key) & (m->cap - 1);; i = (i + 1) & (m->cap - 1)) {
        if (m->keys[i] == key) { m->keys[i] = ~0ull; return; }
        if (m->keys[i] == 0) return;
    }
}

static void map_clear(map64 *m) {
    if (m->cap) { memset(m->keys, 0, 8ull * m->cap); m->used = 0; }
}

static volatile int objc_lock_word;
static void lk(void) { while (__atomic_exchange_n(&objc_lock_word, 1, __ATOMIC_ACQUIRE)) { } }
static void ulk(void) { __atomic_store_n(&objc_lock_word, 0, __ATOMIC_RELEASE); }

/* ---- selectors ----------------------------------------------------------------------------------------- */
typedef struct selent { const char *name; SEL sel; struct selent *next; } selent;
static selent *sel_buckets[8192];

static uint32_t str_hash(const char *s) {
    uint32_t h = 2166136261u;
    while (*s) h = (h ^ (uint8_t)*s++) * 16777619u;
    return h;
}

/* the canonical selector for a name; `have` is a game address that already holds the name (0: copy it) */
static SEL sel_intern(const char *name, uint32_t have) {
    uint32_t b = str_hash(name) & 8191;
    lk();
    for (selent *e = sel_buckets[b]; e; e = e->next)
        if (!strcmp(e->name, name)) { ulk(); return e->sel; }
    ulk();
    SEL s = have ? have : rt_static_string(name);
    lk();
    for (selent *e = sel_buckets[b]; e; e = e->next) /* lost a race: use the winner */
        if (!strcmp(e->name, name)) { ulk(); return e->sel; }
    selent *e = malloc(sizeof *e);
    e->name = rt_str(s);
    e->sel = s;
    e->next = sel_buckets[b];
    sel_buckets[b] = e;
    ulk();
    return s;
}

SEL rt_sel(const char *name) { return sel_intern(name, 0); }
const char *rt_sel_name(SEL s) { return s ? rt_str(s) : "(null)"; }

/* ---- classes ------------------------------------------------------------------------------------------- */
typedef struct clsinfo {
    id cls, meta;
    const char *name;
    int host;                 /* defined by the runtime */
    int initialized;          /* +initialize sent */
    uint32_t lists[2][16];    /* category method lists: [0] instance, [1] class; later ones win */
    int nlists[2];
} clsinfo;

static clsinfo *classes[4096];
static int nclasses;
static map64 class_index;     /* class or metaclass address -> index + 1 (high bit set for the metaclass) */
static map64 host_methods;    /* (class << 32 | sel) -> IMP of a host method */
static map64 method_cache;    /* (class << 32 | sel) -> IMP | 1 << 32 (0 IMP: not found) */
static id root_class, root_meta;
static uint32_t empty_word;   /* a zero word: objc_empty_cache, objc_empty_vtable */

static clsinfo *info_of(id cls, int *is_meta) {
    uint64_t v;
    lk();
    int got = map_get(&class_index, cls, &v);
    ulk();
    if (!got) return NULL;
    if (is_meta) *is_meta = (int)(v >> 63);
    return classes[(v & 0xFFFFFFFF) - 1];
}

static clsinfo *register_class(id cls, id meta, const char *name, int host) {
    if (nclasses >= 4096) rt_fatal("too many classes");
    clsinfo *ci = calloc(1, sizeof *ci);
    ci->cls = cls;
    ci->meta = meta;
    ci->name = name;
    ci->host = host;
    lk();
    classes[nclasses++] = ci;
    map_put(&class_index, cls, (uint64_t)nclasses);
    map_put(&class_index, meta, (uint64_t)nclasses | (1ull << 63));
    ulk();
    return ci;
}

static inline id superclass_of(id cls) { return rt_ld32(cls + 4); }
static inline uint32_t ro_of(id cls) { return rt_ld32(cls + 16) & ~3u; }

id rt_class(const char *name) {
    for (int k = 0; k < nclasses; k++)
        if (!strcmp(classes[k]->name, name)) return classes[k]->cls;
    return 0;
}

const char *rt_class_name(id cls) {
    clsinfo *ci = info_of(cls, NULL);
    return ci ? ci->name : "?";
}

static int is_class_object(id obj) {
    int meta = 0;
    clsinfo *ci = info_of(obj, &meta);
    return ci && !meta;
}

id rt_object_class(id obj) { return obj ? rt_ld32(obj) : 0; }

int rt_is_kind(id obj, id cls) {
    for (id c = rt_object_class(obj); c; c = superclass_of(c))
        if (c == cls) return 1;
    return 0;
}

/* a class_t + metaclass pair in game memory for a runtime-defined class */
id rt_objc_define(const char *name, const char *super, uint32_t ivar_bytes) {
    id existing = rt_class(name);
    if (existing) return existing;
    id sup = 0;
    if (super) {
        sup = rt_class(super);
        if (!sup) rt_fatal("class %s: superclass %s is not defined yet", name, super);
    }
    uint32_t blk = rt_calloc(1, 20 + 20 + 40 + 40);
    id cls = blk, meta = blk + 20;
    uint32_t ro = blk + 40, mro = blk + 80, nm = rt_static_string(name);
    uint32_t start = sup ? rt_ld32(ro_of(sup) + 8) : 0;
    uint32_t size = (sup ? start : 4) + ((ivar_bytes + 3) & ~3u);
    rt_st32(ro + 0, sup ? 0 : RO_ROOT);
    rt_st32(ro + 4, sup ? start : 0);
    rt_st32(ro + 8, size);
    rt_st32(ro + 16, nm);
    rt_st32(mro + 0, RO_META | (sup ? 0 : RO_ROOT));
    rt_st32(mro + 4, 20);
    rt_st32(mro + 8, 20);
    rt_st32(mro + 16, nm);
    if (!sup) {
        rt_st32(cls + 0, meta);
        rt_st32(cls + 4, 0);
        rt_st32(meta + 0, meta);
        rt_st32(meta + 4, cls); /* the root metaclass inherits the root class's instance methods */
        root_class = cls;
        root_meta = meta;
    } else {
        rt_st32(cls + 0, meta);
        rt_st32(cls + 4, sup);
        rt_st32(meta + 0, root_meta);
        rt_st32(meta + 4, rt_ld32(sup)); /* the superclass's metaclass */
    }
    for (id c = cls; c <= meta; c += 20) {
        rt_st32(c + 8, empty_word); /* cache: unused by this runtime */
        rt_st32(c + 12, 0);
    }
    rt_st32(cls + 16, ro);
    rt_st32(meta + 16, mro);
    register_class(cls, meta, rt_str(nm), 1);
    return cls;
}

static void add_host_method(id cls, const char *sel, rt_hostfn fn, const char *kind) {
    char name[160];
    snprintf(name, sizeof name, "%c[%s %s]", kind[0], rt_class_name(cls), sel);
    uint32_t imp = rt_hostfn_add(fn, strdup(name));
    SEL s = rt_sel(sel); /* before taking the lock: interning takes it too */
    lk();
    map_put(&host_methods, ((uint64_t)cls << 32) | s, imp);
    map_clear(&method_cache);
    ulk();
}

void rt_objc_method(id cls, const char *sel, rt_hostfn fn) { add_host_method(cls, sel, fn, "-"); }
void rt_objc_cmethod(id cls, const char *sel, rt_hostfn fn) { add_host_method(rt_ld32(cls), sel, fn, "+"); }

/* ---- lookup -------------------------------------------------------------------------------------------- */
static uint32_t scan_list(uint32_t ml, SEL sel) {
    if (!ml) return 0;
    uint32_t entsize = rt_ld32(ml) & ~3u, count = rt_ld32(ml + 4);
    if (entsize < 12) entsize = 12;
    for (uint32_t k = 0; k < count; k++) {
        uint32_t m = ml + 8 + k * entsize;
        if (rt_ld32(m) == sel) return rt_ld32(m + 8);
    }
    return 0;
}

uint32_t rt_lookup(id cls, SEL sel) {
    uint64_t key = ((uint64_t)cls << 32) | sel, v;
    lk();
    int hit = map_get(&method_cache, key, &v);
    ulk();
    if (hit) return (uint32_t)v;
    uint32_t imp = 0;
    for (id c = cls; c && !imp; c = superclass_of(c)) {
        lk();
        if (map_get(&host_methods, ((uint64_t)c << 32) | sel, &v)) imp = (uint32_t)v;
        ulk();
        if (imp) break;
        int meta = 0;
        clsinfo *ci = info_of(c, &meta);
        if (ci)
            for (int k = ci->nlists[meta] - 1; k >= 0 && !imp; k--) imp = scan_list(ci->lists[meta][k], sel);
        if (!imp) imp = scan_list(rt_ld32(ro_of(c) + 20), sel);
    }
    lk();
    map_put(&method_cache, key, imp | (1ull << 32));
    ulk();
    return imp;
}

static void unrecognized(id cls, SEL sel, id obj) {
    static map64 seen;
    uint64_t key = ((uint64_t)cls << 32) | sel;
    lk();
    int was = map_get(&seen, key, NULL);
    if (!was) map_put(&seen, key, 1);
    ulk();
    if (!was) {
        int meta = 0;
        clsinfo *ci = info_of(cls, &meta);
        rt_log("objc: %c[%s %s] not implemented (returns 0)", meta ? '+' : '-', ci ? ci->name : "?", rt_sel_name(sel));
    }
    (void)obj;
}

/* +initialize, sent before the first message to a class (superclasses first) */
static void ensure_initialized(cpu_t *c, id cls) {
    int meta = 0;
    clsinfo *ci = info_of(cls, &meta);
    if (!ci || ci->initialized) return;
    ci->initialized = 1;
    id sup = superclass_of(ci->cls);
    if (sup) ensure_initialized(c, sup);
    static SEL s_init;
    if (!s_init) s_init = rt_sel("initialize");
    uint32_t imp = rt_lookup(ci->meta, s_init);
    if (imp) rt_call(c, imp, 2, ci->cls, s_init);
}

static uint32_t lookup_for_send(cpu_t *c, id cls, SEL sel) {
    int meta = 0;
    clsinfo *ci = info_of(cls, &meta);
    if (ci && !ci->initialized) ensure_initialized(c, ci->cls);
    return rt_lookup(cls, sel);
}

uint32_t rt_send(cpu_t *c, id obj, const char *sel, int nargs, ...) {
    if (!obj) return 0;
    SEL s = rt_sel(sel);
    id cls = rt_ld32(obj);
    uint32_t imp = lookup_for_send(c, cls, s);
    if (!imp) { unrecognized(cls, s, obj); return 0; }
    uint32_t words[16] = {obj, s};
    va_list ap;
    va_start(ap, nargs);
    for (int k = 0; k < nargs && k < 14; k++) words[2 + k] = va_arg(ap, uint32_t);
    va_end(ap);
    return rt_callv(c, imp, 2 + nargs, words);
}

int rt_responds(id obj, const char *sel) {
    return obj && rt_lookup(rt_ld32(obj), rt_sel(sel)) != 0;
}

/* ---- message sending (imports) ------------------------------------------------------------------------- */
/* Continue in the method with the caller's state: its return lands at the caller's LR. */
static void tail_to(cpu_t *c, uint32_t imp) {
    rc_dispatch(c, rt_mem, imp);
    rt_import_tail = 1; /* set after the call: nested imports reset it */
}

static void imp_objc_msgSend(cpu_t *c) {
    id self = c->r[0];
    SEL sel = c->r[1];
    if (!self) { c->r[0] = 0; c->r[1] = 0; return; } /* messages to nil return 0 */
    id cls = rt_ld32(self);
    uint32_t imp = lookup_for_send(c, cls, sel);
    if (!imp) { unrecognized(cls, sel, self); c->r[0] = 0; c->r[1] = 0; return; }
    if (rt_verbose > 1) rt_log("send -[%s %s]", rt_class_name(cls), rt_sel_name(sel));
    tail_to(c, imp);
}

/* objc_msgSendSuper2(struct objc_super *, SEL, ...): super = { receiver, current class }; the search starts at
 * the current class's superclass */
static void imp_objc_msgSendSuper2(cpu_t *c) {
    uint32_t sup = c->r[0];
    SEL sel = c->r[1];
    id self = rt_ld32(sup), cur = rt_ld32(sup + 4);
    c->r[0] = self;
    if (!self) { c->r[1] = 0; return; }
    uint32_t imp = lookup_for_send(c, superclass_of(cur), sel);
    if (!imp) { unrecognized(superclass_of(cur), sel, self); c->r[0] = 0; return; }
    tail_to(c, imp);
}

/* objc_msgSend_stret(void *result, id self, SEL, ...): the result goes to memory */
static void imp_objc_msgSend_stret(cpu_t *c) {
    id self = c->r[1];
    SEL sel = c->r[2];
    if (!self) return;
    id cls = rt_ld32(self);
    uint32_t imp = lookup_for_send(c, cls, sel);
    if (!imp) { unrecognized(cls, sel, self); return; }
    tail_to(c, imp);
}

/* objc_setProperty(self, _cmd, offset, newValue, atomic, shouldCopy) */
static void imp_objc_setProperty(cpu_t *c) {
    id self = c->r[0], val = c->r[3];
    uint32_t off = c->r[2], copy = rt_arg(c, 5);
    if (copy && val) val = rt_send(c, val, "copy", 0);
    else val = rt_retain(val);
    id old = rt_ld32(self + off);
    rt_st32(self + off, val);
    rt_release(c, old);
}

static void imp_objc_enumerationMutation(cpu_t *c) { rt_log("objc: collection mutated while being enumerated"); (void)c; }

/* ---- object lifetime ----------------------------------------------------------------------------------- */
static map64 retain_counts; /* object -> extra retains (count - 1) */
static map64 host_state;    /* object -> host pointer */

id rt_objc_alloc(id cls) {
    uint32_t size = rt_ld32(ro_of(cls) + 8);
    if (size < 4) size = 4;
    id obj = rt_calloc(1, size);
    rt_st32(obj, cls);
    return obj;
}

id rt_retain(id obj) {
    if (!obj || is_class_object(obj)) return obj;
    uint64_t v = 0;
    lk();
    map_get(&retain_counts, obj, &v);
    map_put(&retain_counts, obj, v + 1);
    ulk();
    return obj;
}

static uint32_t retain_count(id obj) {
    uint64_t v = 0;
    lk();
    map_get(&retain_counts, obj, &v);
    ulk();
    return (uint32_t)v + 1;
}

void rt_release(cpu_t *c, id obj) {
    if (!obj || is_class_object(obj)) return;
    uint64_t v = 0;
    lk();
    int has = map_get(&retain_counts, obj, &v);
    if (has && v > 1) map_put(&retain_counts, obj, v - 1);
    else if (has && v == 1) map_del(&retain_counts, obj);
    ulk();
    if (!has) rt_send(c, obj, "dealloc", 0);
}

void *rt_objc_state(id obj, size_t size) {
    uint64_t v;
    lk();
    if (map_get(&host_state, obj, &v)) { ulk(); return (void *)(uintptr_t)v; }
    void *p = calloc(1, size);
    map_put(&host_state, obj, (uint64_t)(uintptr_t)p);
    ulk();
    return p;
}

void *rt_objc_state_peek(id obj) {
    uint64_t v = 0;
    lk();
    int got = map_get(&host_state, obj, &v);
    ulk();
    return got ? (void *)(uintptr_t)v : NULL;
}

void rt_objc_free(id obj) {
    if (!obj) return;
    uint64_t v;
    lk();
    if (map_get(&host_state, obj, &v)) { free((void *)(uintptr_t)v); map_del(&host_state, obj); }
    map_del(&retain_counts, obj);
    ulk();
    if (obj >= RT_HEAP_BASE) rt_free(obj);
}

/* autorelease pools: a stack per thread; each pool collects objects and releases them when drained */
typedef struct pool { id obj; uint32_t *items; uint32_t n, cap; } pool;
static __thread pool *pools;
static __thread int npools, cap_pools;

static void pool_push(id obj) {
    if (npools == cap_pools) {
        cap_pools = cap_pools ? cap_pools * 2 : 8;
        pools = realloc(pools, sizeof(pool) * (size_t)cap_pools);
    }
    pools[npools++] = (pool){obj, NULL, 0, 0};
}

static void pool_pop(cpu_t *c, id obj) {
    while (npools > 0) {
        pool p = pools[--npools];
        for (uint32_t k = 0; k < p.n; k++) rt_release(c, p.items[k]);
        free(p.items);
        if (p.obj == obj) break;
    }
}

id rt_autorelease(id obj) {
    if (!obj || is_class_object(obj)) return obj;
    if (!npools) {
        static int warned;
        if (!warned++) rt_log("objc: autorelease with no pool in place (leaked)");
        return obj;
    }
    pool *p = &pools[npools - 1];
    if (p->n == p->cap) {
        p->cap = p->cap ? p->cap * 2 : 64;
        p->items = realloc(p->items, 4 * (size_t)p->cap);
    }
    p->items[p->n++] = obj;
    return obj;
}

/* ---- description (for %@ and NSLog) ---------------------------------------------------------------------- */
const char *rt_objc_describe(cpu_t *c, id obj) {
    static __thread char buf[2048];
    if (!obj) return "(null)";
    id d = rt_send(c, obj, "description", 0);
    const char *s = d ? rt_nsstring_utf8(d) : NULL;
    if (!s) {
        snprintf(buf, sizeof buf, "<%s: %#x>", rt_class_name(rt_object_class(obj)), obj);
        return buf;
    }
    snprintf(buf, sizeof buf, "%s", s);
    return buf;
}

/* ---- NSObject -------------------------------------------------------------------------------------------- */
#define SELF c->r[0]
#define ARG(k) rt_arg(c, (k) + 2) /* method arguments after self and _cmd */
#define M(name) static void name(cpu_t *c, uint8_t *m)

M(o_alloc) { (void)m; rt_ret(c, rt_objc_alloc(SELF)); }
M(o_new) { (void)m; id o = rt_objc_alloc(SELF); rt_ret(c, rt_send(c, o, "init", 0)); }
M(o_self) { (void)m; (void)c; }
M(o_nop_class) { (void)m; (void)c; }
M(o_retain) { (void)m; rt_retain(SELF); }
M(o_release) { (void)m; rt_release(c, SELF); }
M(o_autorelease) { (void)m; rt_autorelease(SELF); }
M(o_retain_count) { (void)m; rt_ret(c, is_class_object(SELF) ? 0x7fffffffu : retain_count(SELF)); }
M(o_dealloc) { (void)m; rt_objc_free(SELF); }
M(o_class) { (void)m; rt_ret(c, rt_ld32(SELF)); }
M(o_class_class) { (void)m; (void)c; } /* +class: the class itself */
M(o_superclass) { (void)m; rt_ret(c, superclass_of(rt_ld32(SELF))); }
M(o_class_superclass) { (void)m; rt_ret(c, superclass_of(SELF)); }
M(o_is_kind) { (void)m; rt_ret(c, rt_is_kind(SELF, ARG(0))); }
M(o_is_member) { (void)m; rt_ret(c, rt_ld32(SELF) == ARG(0)); }
M(o_responds) { (void)m; rt_ret(c, rt_lookup(rt_ld32(SELF), ARG(0)) != 0); }
M(o_instances_respond) { (void)m; rt_ret(c, rt_lookup(SELF, ARG(0)) != 0); }
M(o_conforms) { (void)m; rt_ret(c, 1); } /* protocol checks: the game asks this of its own delegates */
M(o_is_equal) { (void)m; rt_ret(c, SELF == ARG(0)); }
M(o_hash) { (void)m; rt_ret(c, SELF >> 2); }
M(o_zone) { (void)m; rt_ret(c, 0); }
M(o_copy) { (void)m; rt_ret(c, rt_send(c, SELF, "copyWithZone:", 1, 0)); }
M(o_mutable_copy) { (void)m; rt_ret(c, rt_send(c, SELF, "mutableCopyWithZone:", 1, 0)); }
M(o_description) {
    (void)m;
    char b[160];
    if (is_class_object(SELF)) snprintf(b, sizeof b, "%s", rt_class_name(SELF));
    else snprintf(b, sizeof b, "<%s: %#x>", rt_class_name(rt_ld32(SELF)), SELF);
    rt_ret(c, rt_nsstring(b));
}
M(o_perform) {
    (void)m;
    uint32_t imp = lookup_for_send(c, rt_ld32(SELF), ARG(0));
    if (!imp) { unrecognized(rt_ld32(SELF), ARG(0), SELF); rt_ret(c, 0); return; }
    rt_ret(c, rt_call(c, imp, 4, SELF, ARG(0), ARG(1), ARG(2)));
}
/* performSelectorOnMainThread:withObject:waitUntilDone: and performSelector:withObject:afterDelay: run now for
 * the moment; the run loop (uikit.c) will queue them. */
M(o_perform_main) {
    (void)m;
    uint32_t imp = lookup_for_send(c, rt_ld32(SELF), ARG(0));
    if (imp) rt_call(c, imp, 3, SELF, ARG(0), ARG(1));
}
M(o_initialize) { (void)m; (void)c; }
M(o_cancel_previous) { (void)m; (void)c; }

/* NSAutoreleasePool */
M(p_init) { (void)m; pool_push(SELF); }
M(p_drain) { (void)m; pool_pop(c, SELF); rt_objc_free(SELF); }
M(p_add) { (void)m; rt_autorelease(ARG(0)); }
M(p_retain) { (void)m; (void)c; }

/* ---- the data imports this file provides ------------------------------------------------------------------ */
static uint32_t eh_type_id;

static uint32_t resolve(const char *name) {
    const char *p;
    if (!strncmp(name, "OBJC_CLASS_$_", 13) || !strncmp(name, "OBJC_METACLASS_$_", 17)) {
        int meta = name[5] == 'M';
        p = name + (meta ? 17 : 13);
        id cls = rt_class(p);
        if (!cls) {
            cls = rt_objc_define(p, "NSObject", 0);
            rt_log("objc: class %s is not implemented yet (empty subclass of NSObject)", p);
        }
        return meta ? rt_ld32(cls) : cls;
    }
    if (!strcmp(name, "__CFConstantStringClassReference")) return rt_class("__NSCFConstantString");
    if (!strcmp(name, "_objc_empty_cache") || !strcmp(name, "_objc_empty_vtable")) return empty_word;
    if (!strcmp(name, "OBJC_EHTYPE_id")) return eh_type_id;
    return 0;
}

/* ---- load ------------------------------------------------------------------------------------------------ */
void rt_objc_define_root(void);

static void canonicalize_list(uint32_t ml) {
    if (!ml) return;
    uint32_t entsize = rt_ld32(ml) & ~3u, count = rt_ld32(ml + 4);
    if (entsize < 12) entsize = 12;
    for (uint32_t k = 0; k < count; k++) {
        uint32_t mt = ml + 8 + k * entsize, name = rt_ld32(mt);
        rt_st32(mt, sel_intern(rt_str(name), name));
    }
}

static void register_import(void);

void rt_objc_init(void) {
    /* selector references first: their strings become the canonical names */
    uint32_t a = rt_objc_sections[RT_OBJC_SELREFS][0], n = rt_objc_sections[RT_OBJC_SELREFS][1] / 4;
    for (uint32_t k = 0; k < n; k++) {
        uint32_t ref = a + 4 * k, name = rt_ld32(ref);
        rt_st32(ref, sel_intern(rt_str(name), name));
    }
    /* the game's classes and metaclasses */
    a = rt_objc_sections[RT_OBJC_CLASSLIST][0];
    n = rt_objc_sections[RT_OBJC_CLASSLIST][1] / 4;
    for (uint32_t k = 0; k < n; k++) {
        id cls = rt_ld32(a + 4 * k), meta = rt_ld32(cls);
        canonicalize_list(rt_ld32(ro_of(cls) + 20));
        canonicalize_list(rt_ld32(ro_of(meta) + 20));
        clsinfo *ci = register_class(cls, meta, rt_str(rt_ld32(ro_of(cls) + 16)), 0);
        id sup = superclass_of(cls);
        clsinfo *si = info_of(sup, NULL);
        uint32_t start = rt_ld32(ro_of(cls) + 4);
        if (si && si->host && rt_ld32(ro_of(sup) + 8) > start)
            rt_log("objc: %s: superclass %s is larger (%u) than its instance start (%u)", ci->name, si->name,
                   rt_ld32(ro_of(sup) + 8), start);
        if (!sup || !si) rt_log("objc: class %s has no known superclass (%#x)", ci->name, sup);
    }
    /* categories */
    a = rt_objc_sections[RT_OBJC_CATLIST][0];
    n = rt_objc_sections[RT_OBJC_CATLIST][1] / 4;
    for (uint32_t k = 0; k < n; k++) {
        uint32_t cat = rt_ld32(a + 4 * k);
        id cls = rt_ld32(cat + 4);
        clsinfo *ci = info_of(cls, NULL);
        if (!ci) { rt_log("objc: category %s on an unknown class %#x", rt_str(rt_ld32(cat)), cls); continue; }
        for (int meta = 0; meta < 2; meta++) {
            uint32_t ml = rt_ld32(cat + 8 + 4 * meta);
            if (!ml || ci->nlists[meta] >= 16) continue;
            canonicalize_list(ml);
            ci->lists[meta][ci->nlists[meta]++] = ml;
        }
    }
    lk();
    map_clear(&method_cache);
    ulk();
    rt_log("objc: %d classes (%u from the game), %u selector references", nclasses,
           rt_objc_sections[RT_OBJC_CLASSLIST][1] / 4, rt_objc_sections[RT_OBJC_SELREFS][1] / 4);
}

/* +load of the game's classes and categories, in list order */
void rt_objc_load(void) {
    cpu_t *c = rt_thread_cpu();
    SEL s = rt_sel("load");
    uint32_t a = rt_objc_sections[RT_OBJC_CLASSLIST][0], n = rt_objc_sections[RT_OBJC_CLASSLIST][1] / 4;
    for (uint32_t k = 0; k < n; k++) {
        id cls = rt_ld32(a + 4 * k);
        uint32_t imp = scan_list(rt_ld32(ro_of(rt_ld32(cls)) + 20), s);
        if (imp) rt_call(c, imp, 2, cls, s);
    }
    a = rt_objc_sections[RT_OBJC_CATLIST][0];
    n = rt_objc_sections[RT_OBJC_CATLIST][1] / 4;
    for (uint32_t k = 0; k < n; k++) {
        uint32_t cat = rt_ld32(a + 4 * k);
        uint32_t imp = scan_list(rt_ld32(cat + 12), s);
        if (imp) rt_call(c, imp, 2, rt_ld32(cat + 4), s);
    }
}

/* NSObject and NSAutoreleasePool, the data import resolver and the message-sending imports. Called first, before
 * any other class is defined and before the image's bound words are patched. */
void rt_objc_define_root(void) {
    empty_word = rt_calloc(1, 16);
    eh_type_id = rt_calloc(1, 16);
    id o = rt_objc_define("NSObject", NULL, 0);
    struct { const char *sel; rt_hostfn fn; } inst[] = {
        {"init", o_self}, {"self", o_self}, {"retain", o_retain}, {"release", o_release},
        {"autorelease", o_autorelease}, {"retainCount", o_retain_count}, {"dealloc", o_dealloc},
        {"class", o_class}, {"superclass", o_superclass}, {"isKindOfClass:", o_is_kind},
        {"isMemberOfClass:", o_is_member}, {"respondsToSelector:", o_responds}, {"conformsToProtocol:", o_conforms},
        {"isEqual:", o_is_equal}, {"hash", o_hash}, {"zone", o_zone}, {"copy", o_copy},
        {"mutableCopy", o_mutable_copy}, {"description", o_description}, {"performSelector:", o_perform},
        {"performSelector:withObject:", o_perform}, {"performSelector:withObject:withObject:", o_perform},
        {"performSelectorOnMainThread:withObject:waitUntilDone:", o_perform_main},
        {"performSelector:withObject:afterDelay:", o_perform_main},
    };
    for (size_t k = 0; k < sizeof inst / sizeof *inst; k++) rt_objc_method(o, inst[k].sel, inst[k].fn);
    struct { const char *sel; rt_hostfn fn; } cls[] = {
        {"alloc", o_alloc}, {"allocWithZone:", o_alloc}, {"new", o_new}, {"class", o_class_class},
        {"superclass", o_class_superclass}, {"initialize", o_initialize}, {"load", o_initialize},
        {"instancesRespondToSelector:", o_instances_respond},
        {"cancelPreviousPerformRequestsWithTarget:", o_cancel_previous},
        {"cancelPreviousPerformRequestsWithTarget:selector:object:", o_cancel_previous},
    };
    for (size_t k = 0; k < sizeof cls / sizeof *cls; k++) rt_objc_cmethod(o, cls[k].sel, cls[k].fn);
    /* class objects answer retain/release/autorelease too (the root metaclass inherits NSObject's instance
     * methods), and is_class_object makes those no-ops */
    (void)o_nop_class;

    id p = rt_objc_define("NSAutoreleasePool", "NSObject", 0);
    rt_objc_method(p, "init", p_init);
    rt_objc_method(p, "drain", p_drain);
    rt_objc_method(p, "release", p_drain);
    rt_objc_method(p, "retain", p_retain);
    rt_objc_method(p, "addObject:", p_add);
    rt_objc_cmethod(p, "addObject:", p_add);

    rt_data_resolver_add(resolve);
    register_import();
}

static void register_import(void) {
    rt_import_register("objc_msgSend", imp_objc_msgSend);
    rt_import_register("objc_msgSendSuper2", imp_objc_msgSendSuper2);
    rt_import_register("objc_msgSend_stret", imp_objc_msgSend_stret);
    rt_import_register("objc_setProperty", imp_objc_setProperty);
    rt_import_register("objc_enumerationMutation", imp_objc_enumerationMutation);
}
