/* Calling conventions, calls into game code, host functions, import dispatch, diagnostics. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rt.h"

int rt_verbose;

#ifdef __ANDROID__
#include <android/log.h>
void rt_log(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    __android_log_vprint(ANDROID_LOG_INFO, "novahd", fmt, ap);
    va_end(ap);
}

void rt_fatal(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    __android_log_vprint(ANDROID_LOG_FATAL, "novahd", fmt, ap);
    va_end(ap);
    abort();
}
#else
void rt_log(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
    fflush(stderr);
}

void rt_fatal(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("fatal: ", stderr);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
    fflush(stderr);
    abort();
}
#endif

/* ---- path aliases: the app bundle and its Documents folder ----------------------------------------- */
char rt_bundle_path[512], rt_home_path[512];
static struct { char *from, *to; size_t n; } aliases[8];
static int nalias;

void rt_path_alias(const char *from, const char *to) {
    if (nalias >= 8) return;
    aliases[nalias].from = strdup(from);
    aliases[nalias].to = strdup(to);
    aliases[nalias].n = strlen(from);
    nalias++;
}

/* The game's working directory (a game path). iOS starts apps in "/"; the game chdir()s to its bundle and then
 * opens its data with relative names (sprites.pack, ...). */
char rt_cwd[512];

#ifdef _WIN32
#define RT_CASE_FALLBACK 0 /* Windows file systems are case-insensitive already */
#else
#define RT_CASE_FALLBACK 1
#endif

#if RT_CASE_FALLBACK
#include <dirent.h>
#include <pthread.h>
#include <strings.h>
#include <sys/stat.h>
/* iOS (HFS+) is case-insensitive, Android is not: when a path does not exist as written, look up each component
 * in its directory ignoring case. Results (including misses) are cached. */
static struct ci_ent { char *key, *val; } ci_cache[1024];
static int ci_count;
static pthread_mutex_t ci_lock = PTHREAD_MUTEX_INITIALIZER;

static int ci_exists(const char *p) { struct stat st; return stat(p, &st) == 0; }

static void ci_resolve(const char *path, char *out, size_t cap) {
    snprintf(out, cap, "%s", path);
    if (ci_exists(path)) return;
    pthread_mutex_lock(&ci_lock);
    for (int k = 0; k < ci_count; k++)
        if (!strcmp(ci_cache[k].key, path)) { snprintf(out, cap, "%s", ci_cache[k].val); pthread_mutex_unlock(&ci_lock); return; }
    pthread_mutex_unlock(&ci_lock);
    char cur[1024] = "";
    const char *p = path;
    int ok = 1;
    while (*p) {
        while (*p == '/') p++;
        if (!*p) break;
        const char *e = p;
        while (*e && *e != '/') e++;
        char comp[256];
        size_t n = (size_t)(e - p);
        if (n >= sizeof comp) { ok = 0; break; }
        memcpy(comp, p, n); comp[n] = 0;
        char next[1024];
        snprintf(next, sizeof next, "%s/%s", cur, comp);
        if (!ci_exists(next)) {
            DIR *d = opendir(cur[0] ? cur : "/");
            int found = 0;
            if (d) {
                struct dirent *de;
                while ((de = readdir(d)))
                    if (!strcasecmp(de->d_name, comp)) { snprintf(next, sizeof next, "%s/%s", cur, de->d_name); found = 1; break; }
                closedir(d);
            }
            if (!found) { ok = 0; break; }
        }
        snprintf(cur, sizeof cur, "%s", next);
        p = e;
    }
    char res[1024];
    snprintf(res, sizeof res, "%s", ok ? cur : path);
    pthread_mutex_lock(&ci_lock);
    if (ci_count < 1024) { ci_cache[ci_count].key = strdup(path); ci_cache[ci_count].val = strdup(res); ci_count++; }
    pthread_mutex_unlock(&ci_lock);
    snprintf(out, cap, "%s", res);
}
#endif

const char *rt_host_path(const char *path) {
    static __thread char buf[1024], abs[1024];
    if (path[0] != '/') { /* relative: against the game's working directory (the bundle until chdir says otherwise) */
        snprintf(abs, sizeof abs, "%s/%s", rt_cwd[0] ? rt_cwd : rt_bundle_path, path);
        path = abs;
    }
    for (int k = 0; k < nalias; k++)
        if (!strncmp(path, aliases[k].from, aliases[k].n)) {
            snprintf(buf, sizeof buf, "%s%s", aliases[k].to, path + aliases[k].n);
#if RT_CASE_FALLBACK
            char fixed[1024];
            ci_resolve(buf, fixed, sizeof fixed);
            snprintf(buf, sizeof buf, "%s", fixed);
#endif
            return buf;
        }
#if RT_CASE_FALLBACK
    ci_resolve(path, buf, sizeof buf);
    return buf;
#else
    return path;
#endif
}

/* ---- arguments (ARM softfp): words 0-3 in r0-r3, then the caller's stack ----------------------- */
uint32_t rt_arg(cpu_t *c, int k) { return k < 4 ? c->r[k] : rt_ld32(c->r[13] + 4 * (k - 4)); }

double rt_darg(cpu_t *c, int k) {
    uint64_t u = (uint64_t)rt_arg(c, k) | ((uint64_t)rt_arg(c, k + 1) << 32);
    double d;
    memcpy(&d, &u, 8);
    return d;
}

float rt_farg(cpu_t *c, int k) {
    uint32_t u = rt_arg(c, k);
    float f;
    memcpy(&f, &u, 4);
    return f;
}

void rt_dret(cpu_t *c, double v) {
    uint64_t u;
    memcpy(&u, &v, 8);
    c->r[0] = (uint32_t)u;
    c->r[1] = (uint32_t)(u >> 32);
}

/* ---- calls into game code ----------------------------------------------------------------------
 * The current state is saved, the arguments are placed per the ABI, LR points at the return sentinel, and
 * the translated function runs as an ordinary C call. Afterwards the caller's state comes back. */
uint32_t rt_callv(cpu_t *c, uint32_t fn, int nargs, const uint32_t *words) {
    cpu_t saved = *c;
    uint32_t sp = (c->r[13] - 64) & ~7u; /* leave the caller's red zone alone */
    if (nargs > 4) {
        sp -= ((nargs - 4) * 4 + 7) & ~7u;
        for (int k = 4; k < nargs; k++) rt_st32(sp + 4 * (k - 4), words[k]);
    }
    for (int k = 0; k < 4 && k < nargs; k++) c->r[k] = words[k];
    c->r[13] = sp;
    c->r[14] = RT_RETURN_SENTINEL;
    rc_dispatch(c, rt_mem, fn);
    uint32_t result = c->r[0];
    uint32_t fault = c->fault;
    if (c->r[15] != RT_RETURN_SENTINEL && !fault)
        rt_log("call to %#x came back to %#x", fn, c->r[15]);
    if (fault) {
        rt_log("fault %u in a call to %#x (%s); pc %#x (%s)", fault, fn, rt_func_name(fn, NULL), c->r[15],
               rt_func_name(c->r[15], NULL));
        rt_print_trace(c);
    }
    *c = saved;
    c->fault = fault;
    return result;
}

uint32_t rt_call(cpu_t *c, uint32_t fn, int nargs, ...) {
    uint32_t words[16] = {0};
    va_list ap;
    va_start(ap, nargs);
    for (int k = 0; k < nargs && k < 16; k++) words[k] = va_arg(ap, uint32_t);
    va_end(ap);
    return rt_callv(c, fn, nargs, words);
}

/* ---- host functions ------------------------------------------------------------------------------ */
static rt_hostfn hostfns[RT_HOSTFN_MAX];
static const char *hostfn_names[RT_HOSTFN_MAX];
static uint32_t hostfn_count = 1; /* slot 0 is the return sentinel */

uint32_t rt_hostfn_add(rt_hostfn fn, const char *name) {
    if (hostfn_count >= RT_HOSTFN_MAX) rt_fatal("too many host functions");
    hostfns[hostfn_count] = fn;
    hostfn_names[hostfn_count] = name;
    return RT_HOSTFN_BASE + 4 * hostfn_count++;
}

__thread uint32_t rt_current_hostfn;

void rc_hostcall(cpu_t *c, uint8_t *m, uint32_t slot) {
    if (slot == 0) { c->r[15] = RT_RETURN_SENTINEL; return; } /* a computed jump to the sentinel: just return */
    if (slot >= hostfn_count) { rt_log("call to unknown host function slot %u", slot); c->fault = RC_FAULT_DISPATCH; return; }
    if (rt_verbose > 1) rt_log("hostfn %s", hostfn_names[slot]);
    uint32_t outer = rt_current_hostfn;
    rt_current_hostfn = RT_HOSTFN_BASE + 4 * slot;
    hostfns[slot](c, m);
    rt_current_hostfn = outer;
    c->r[15] = c->r[14];
}

/* ---- imports ------------------------------------------------------------------------------------- */
static rt_import_fn imports[1024];
static uint8_t warned[1024];
__thread int rt_import_tail;

uint32_t rt_import_slot(const char *name) {
    for (uint32_t k = 0; k < rt_import_count; k++)
        if (!strcmp(rt_import_names[k], name)) return k;
    return ~0u;
}

void rt_import_register(const char *name, rt_import_fn fn) {
    uint32_t k = rt_import_slot(name);
    if (k != ~0u) imports[k] = fn;
}

void rt_imports_init(void) {
    rt_libc_register();
    rt_pthread_register();
    rt_cxx_register();
    rt_libstdcxx_register();
    rt_system_register();
    rt_gl_register();
    rt_openal_register();
    rt_graphics_register();
    rt_offline_register();
    rt_uikit_register();
    uint32_t missing = 0;
    for (uint32_t k = 0; k < rt_import_count; k++) missing += !imports[k];
    rt_log("imports: %u of %u implemented", rt_import_count - missing, rt_import_count);
}

void rc_import(cpu_t *c, uint8_t *m, uint32_t slot) {
    (void)m;
    if (slot < rt_import_count && imports[slot]) {
        if (rt_verbose > 2) rt_log("import %s", rt_import_names[slot]);
        rt_import_tail = 0;
        imports[slot](c);
        if (rt_import_tail) { rt_import_tail = 0; return; } /* continued in game code: c holds the final state */
    } else {
        if (slot < 1024 && !warned[slot]) {
            warned[slot] = 1;
            rt_log("unimplemented import %s (returns 0)", slot < rt_import_count ? rt_import_names[slot] : "?");
        }
        c->r[0] = 0;
    }
    c->r[15] = c->r[14];
}

/* ---- data imports ---------------------------------------------------------------------------------- */
static rt_data_resolver resolvers[16];
static int nresolvers;

void rt_data_resolver_add(rt_data_resolver fn) { if (nresolvers < 16) resolvers[nresolvers++] = fn; }

void rt_data_imports_bind(void) {
    uint32_t *value = calloc(rt_import_count, 4);
    uint32_t bound = 0, unresolved = 0;
    for (uint32_t k = 0; k < rt_import_count; k++)
        for (int r = 0; r < nresolvers && !value[k]; r++) value[k] = resolvers[r](rt_import_names[k]);
    for (uint32_t k = 0; k < rt_bind_count; k++) {
        const rt_bind *b = &rt_binds[k];
        if (value[b->slot]) { rt_st32(b->addr, value[b->slot] + b->addend); bound++; }
        else if (b->addend || (strncmp(rt_import_names[b->slot], "OBJC_", 5) == 0)) unresolved++;
    }
    rt_log("data imports: %u words bound, %u left on import slots", bound, unresolved);
    if (rt_verbose) { /* function imports nobody registered (data symbols are not listed) */
        uint32_t nmiss = 0;
        for (uint32_t k = 0; k < rt_import_count; k++)
            if (!imports[k] && !value[k]) { rt_log("import missing: %s", rt_import_names[k]); nmiss++; }
        rt_log("imports missing: %u functions", nmiss);
    }
    free(value);
}

/* ---- threads: one CPU state per host thread ------------------------------------------------------ */
static __thread cpu_t *tl_cpu;

cpu_t *rt_thread_cpu(void) {
    if (!tl_cpu) {
        tl_cpu = calloc(1, sizeof(cpu_t));
        uint32_t stack = rt_malloc(1u << 20);
        tl_cpu->r[13] = stack + (1u << 20) - 16;
        tl_cpu->memsize = 0xFFFFFFFFu;
        tl_cpu->budget = 0xFFFFFFFFu;
        tl_cpu->tls = rt_calloc(1, 4096);
    }
    return tl_cpu;
}

/* ---- function names and the game call chain ------------------------------------------------------ */
const char *rt_func_name(uint32_t addr, uint32_t *offset) {
    uint32_t lo = 0, hi = rt_func_count;
    while (lo < hi) { /* last function starting at or below addr */
        uint32_t mid = (lo + hi) / 2;
        if (rt_func_addrs[mid] <= addr) lo = mid + 1; else hi = mid;
    }
    if (!lo) { if (offset) *offset = addr; return "?"; }
    if (offset) *offset = addr - rt_func_addrs[lo - 1];
    return rt_func_names[lo - 1];
}

void rt_print_trace(cpu_t *c) {
    if (!c) return;
    uint32_t d = c->depth;
    /* entries above the current depth are the frames that just returned (the faulting chain, innermost last) */
    rt_log("game call chain at depth %u (checked builds; frames above the depth already returned):", d);
    for (uint32_t k = d + 12; k >= 1 && k + 24 > d + 12; k--) {
        uint32_t fn = c->trace[k & 63];
        if (!fn) continue;
        rt_log("  %c%3u %#010x %s", k > d ? '^' : ' ', k, fn, rt_func_name(fn, NULL));
    }
}
