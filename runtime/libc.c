/* libSystem imports with iOS 3.x (Darwin, 32-bit ARM) layouts.
 *
 * Game memory holds the game's view; the host's libc does the work. Layouts that differ from Android's bionic:
 *   FILE         opaque to the game here (it calls fileno/fread/...; no getc macros are used): a 88-byte block in
 *                game memory, mapped to a host FILE* by address; __stdoutp points at the stdout block
 *   struct stat  96 bytes (32-bit inode): st_mode at 8 (16 bits), st_size at 48 (64 bits)
 *   dirent       d_ino 4, d_reclen 2, d_type 1, d_namlen 1, d_name[256] at 8
 *   errno        through __error(), a per-thread word in game memory
 * Paths: game paths under the bundle and home folders map to host folders (rt_path_alias).
 */
#include <ctype.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>

#ifdef _WIN32
#include <direct.h>
#include <windows.h>
#include <io.h>
#else
#include <dirent.h>
#include <sys/time.h>
#include <unistd.h>
#endif

#include "rt.h"

#define A(k) rt_arg(c, k)
#define S(k) rt_str(rt_arg(c, k))
#define RET(v) rt_ret(c, (uint32_t)(v))
#define IMP(name) static void imp_##name(cpu_t *c)
#define REG(name) rt_import_register(#name, imp_##name)

/* ---- errno ---------------------------------------------------------------------------------------------------- */
static __thread uint32_t errno_word;
static uint32_t errno_addr(void) {
    if (!errno_word) errno_word = rt_calloc(1, 4);
    return errno_word;
}
static void set_errno(uint32_t e) { rt_st32(errno_addr(), e); }
IMP(__error) { RET(errno_addr()); }

/* ---- memory and strings ----------------------------------------------------------------------------------------- */
IMP(memcpy) { memmove(G(A(0)), G(A(1)), A(2)); RET(A(0)); }
IMP(memmove) { memmove(G(A(0)), G(A(1)), A(2)); RET(A(0)); }
IMP(memset) { memset(G(A(0)), (int)A(1), A(2)); RET(A(0)); }
IMP(bzero) { memset(G(A(0)), 0, A(1)); }
IMP(memcmp) { RET(memcmp(G(A(0)), G(A(1)), A(2))); }
IMP(strlen) { RET(strlen(S(0))); }
IMP(strcmp) { RET(strcmp(S(0), S(1))); }
IMP(strncmp) { RET(strncmp(S(0), S(1), A(2))); }
IMP(strcasecmp) { RET(strcasecmp(S(0), S(1))); }
IMP(strncasecmp) { RET(strncasecmp(S(0), S(1), A(2))); }
IMP(strcpy) { strcpy((char *)G(A(0)), S(1)); RET(A(0)); }
IMP(strncpy) { strncpy((char *)G(A(0)), S(1), A(2)); RET(A(0)); }
IMP(strcat) { strcat((char *)G(A(0)), S(1)); RET(A(0)); }
IMP(strlcpy) {
    const char *s = S(1);
    size_t n = strlen(s), cap = A(2);
    if (cap) { size_t k = n < cap - 1 ? n : cap - 1; memcpy(G(A(0)), s, k); ((char *)G(A(0)))[k] = 0; }
    RET(n);
}
IMP(strchr) { const char *p = strchr(S(0), (int)A(1)); RET(p ? rt_guest_addr(p) : 0); }
IMP(strrchr) { const char *p = strrchr(S(0), (int)A(1)); RET(p ? rt_guest_addr(p) : 0); }
IMP(strstr) { const char *p = strstr(S(0), S(1)); RET(p ? rt_guest_addr(p) : 0); }
IMP(wcslen) { uint32_t p = A(0), n = 0; while (rt_ld32(p + 4 * n)) n++; RET(n); }
IMP(wcscpy) { uint32_t d = A(0), s = A(1), k = 0; do { rt_st32(d + 4 * k, rt_ld32(s + 4 * k)); } while (rt_ld32(s + 4 * k++)); RET(d); }
IMP(wcsncpy) {
    uint32_t d = A(0), s = A(1), n = A(2), k = 0;
    for (; k < n && rt_ld32(s + 4 * k); k++) rt_st32(d + 4 * k, rt_ld32(s + 4 * k));
    for (; k < n; k++) rt_st32(d + 4 * k, 0);
    RET(d);
}
IMP(wcscmp) {
    uint32_t a = A(0), b = A(1);
    for (;; a += 4, b += 4) {
        uint32_t x = rt_ld32(a), y = rt_ld32(b);
        if (x != y || !x) { RET(x < y ? -1 : x > y); return; }
    }
}
IMP(__tolower) { RET(tolower((int)A(0))); }

/* ---- numbers ------------------------------------------------------------------------------------------------------ */
IMP(atoi) { RET(atoi(S(0))); }
IMP(atof) { rt_dret(c, atof(S(0))); }
IMP(strtol) {
    char *end;
    long v = strtol(S(0), &end, (int)A(2));
    if (A(1)) rt_st32(A(1), rt_guest_addr(end));
    RET((int32_t)v);
}
IMP(__divsi3) { int32_t a = (int32_t)A(0), b = (int32_t)A(1); RET(b ? (b == -1 ? (uint32_t)-(int64_t)a : (uint32_t)(a / b)) : 0); }
IMP(__modsi3) { int32_t a = (int32_t)A(0), b = (int32_t)A(1); RET(b && b != -1 ? (uint32_t)(a % b) : 0); }
IMP(__udivsi3) { RET(A(1) ? A(0) / A(1) : 0); }
IMP(__umodsi3) { RET(A(1) ? A(0) % A(1) : 0); }

static uint32_t rand_state = 1;
IMP(rand) { rand_state = rand_state * 1103515245u + 12345u; RET((rand_state >> 1) & 0x7fffffff); }
IMP(srand) { rand_state = A(0); }

/* math: doubles in two argument words (iOS: no alignment), floats in one */
#define D1(fn) IMP(fn) { rt_dret(c, fn(rt_darg(c, 0))); }
#define D2(fn) IMP(fn) { rt_dret(c, fn(rt_darg(c, 0), rt_darg(c, 2))); }
#define F1(fn) IMP(fn) { rt_fret(c, fn(rt_farg(c, 0))); }
#define F2(fn) IMP(fn) { rt_fret(c, fn(rt_farg(c, 0), rt_farg(c, 1))); }
D1(sin) D1(cos) D1(tan) D1(asin) D1(acos) D1(atan) D2(atan2) D2(pow) D2(fmod)
F1(sinf) F1(cosf) F1(tanf) F1(atanf) F1(acosf) F1(floorf) F1(ceilf) F1(roundf) F2(fmodf)

/* ---- formatting ---------------------------------------------------------------------------------------------------- */
static int fmt_to(cpu_t *c, uint32_t dst, uint32_t cap, uint32_t fmt, int first, uint32_t va) {
    rt_args a = {c, first, va};
    char tmp[4096];
    int n = rt_vformat(tmp, sizeof tmp, rt_str(fmt), &a);
    if (dst && cap) {
        uint32_t k = (uint32_t)n < cap - 1 ? (uint32_t)n : cap - 1;
        if (k > sizeof tmp - 1) k = sizeof tmp - 1;
        memcpy(rt_mem + dst, tmp, k);
        rt_mem[dst + k] = 0;
    }
    return n;
}
IMP(sprintf) { RET(fmt_to(c, A(0), 0x7fffffff, A(1), 2, 0)); }
IMP(__sprintf_chk) { RET(fmt_to(c, A(0), A(2) ? A(2) : 0x7fffffff, A(3), 4, 0)); } /* (dst, flag, size, fmt, ...) */
IMP(snprintf) { RET(fmt_to(c, A(0), A(1), A(2), 3, 0)); }
IMP(vsprintf) { RET(fmt_to(c, A(0), 0x7fffffff, A(1), 0, A(2))); }
IMP(sscanf) { rt_args a = {c, 2, 0}; RET(rt_vscan(S(0), S(1), &a)); }

static void out_text(const char *s) { fputs(s, stdout); fflush(stdout); }
IMP(printf) { rt_args a = {c, 1, 0}; char t[4096]; int n = rt_vformat(t, sizeof t, S(0), &a); out_text(t); RET(n); }
IMP(puts) { out_text(S(0)); out_text("\n"); RET(0); }
IMP(putchar) { char t[2] = {(char)A(0), 0}; out_text(t); RET(A(0)); }
IMP(perror) { rt_log("perror: %s", S(0)); }

/* ---- FILE ------------------------------------------------------------------------------------------------------------ */
#define MAXF 256
static FILE *files[MAXF];
static uint32_t file_addr[MAXF];
static uint32_t stdout_block, stderr_block, stdoutp_word;

static FILE *host_file(uint32_t g) {
    for (int k = 0; k < MAXF; k++) if (file_addr[k] == g && g) return files[k];
    return NULL;
}
static uint32_t wrap_file(FILE *f) {
    for (int k = 0; k < MAXF; k++)
        if (!file_addr[k]) { files[k] = f; file_addr[k] = rt_calloc(1, 88); return file_addr[k]; }
    fclose(f);
    return 0;
}
static void unwrap_file(uint32_t g) {
    for (int k = 0; k < MAXF; k++)
        if (file_addr[k] == g) { file_addr[k] = 0; files[k] = NULL; rt_free(g); }
}

IMP(fopen) {
    const char *path = rt_host_path(S(0));
    FILE *f = fopen(path, S(1));
    if (rt_verbose) rt_log("fopen %s (%s): %s", S(0), S(1), f ? "ok" : "missing");
    if (!f) { set_errno(2); RET(0); return; }
    RET(wrap_file(f));
}
IMP(fclose) { FILE *f = host_file(A(0)); if (f && f != stdout && f != stderr) { fclose(f); unwrap_file(A(0)); } RET(0); }
IMP(fread) { FILE *f = host_file(A(3)); RET(f ? fread(G(A(0)), 1, (size_t)A(1) * A(2), f) / (A(1) ? A(1) : 1) : 0); }
IMP(fwrite) { FILE *f = host_file(A(3)); RET(f ? fwrite(G(A(0)), 1, (size_t)A(1) * A(2), f) / (A(1) ? A(1) : 1) : 0); }
IMP(fseek) { FILE *f = host_file(A(0)); RET(f ? fseek(f, (long)(int32_t)A(1), (int)A(2)) : -1); } /* off_t is 64-bit: low word in r1 */
IMP(ftell) { FILE *f = host_file(A(0)); RET(f ? (uint32_t)ftell(f) : (uint32_t)-1); }
IMP(fileno) { FILE *f = host_file(A(0)); RET(f ? (uint32_t)fileno(f) : (uint32_t)-1); }
IMP(fprintf) {
    FILE *f = host_file(A(0));
    rt_args a = {c, 2, 0};
    char t[4096];
    int n = rt_vformat(t, sizeof t, S(1), &a);
    if (f) { fputs(t, f); fflush(f); }
    RET(n);
}
IMP(vfprintf) {
    FILE *f = host_file(A(0));
    rt_args a = {c, 0, A(2)};
    char t[4096];
    int n = rt_vformat(t, sizeof t, S(1), &a);
    if (f) { fputs(t, f); fflush(f); }
    RET(n);
}
IMP(write) {
    if (A(0) == 1 || A(0) == 2) { fwrite(G(A(1)), 1, A(2), A(0) == 1 ? stdout : stderr); RET(A(2)); return; }
    RET(-1);
}
IMP(close) { RET(0); }

/* struct stat, Darwin 32-bit (96 bytes) */
static void put_stat(uint32_t g, const struct stat *st) {
    memset(G(g), 0, 96);
    uint16_t mode = (uint16_t)((st->st_mode & S_IFDIR) ? 0040755 : 0100644);
    memcpy(rt_mem + g + 8, &mode, 2);
    uint64_t size = (uint64_t)st->st_size;
    memcpy(rt_mem + g + 48, &size, 8);
    uint32_t t = (uint32_t)st->st_mtime;
    rt_st32(g + 24, t);
    rt_st32(g + 32, t);
    rt_st32(g + 40, t);
    rt_st32(g + 64, 4096);
}
IMP(stat) {
    struct stat st;
    if (stat(rt_host_path(S(0)), &st)) { set_errno(2); RET(-1); return; }
    put_stat(A(1), &st);
    RET(0);
}
IMP(remove) { RET(remove(rt_host_path(S(0))) ? -1 : 0); }
IMP(rename) { char from[1024]; snprintf(from, sizeof from, "%s", rt_host_path(S(0))); RET(rename(from, rt_host_path(S(1))) ? -1 : 0); }
IMP(chdir) { RET(0); }
IMP(getcwd) { const char *p = rt_bundle_path; size_t n = strlen(p); if (A(0) && n < A(1)) memcpy(G(A(0)), p, n + 1); RET(A(0)); }
IMP(realpath$DARWIN_EXTSN) {
    const char *p = S(0);
    uint32_t dst = A(1) ? A(1) : rt_malloc(1024);
    strncpy((char *)G(dst), p, 1023);
    RET(dst);
}

/* directories: a host listing copied into a Darwin dirent per entry */
typedef struct { char **names; int n, pos; uint32_t ent; } gdir;
static gdir *dirs[64];
static uint32_t dir_addr[64];
IMP(opendir) {
    const char *path = rt_host_path(S(0));
    gdir *d = calloc(1, sizeof *d);
#ifdef _WIN32
    char pat[1100];
    snprintf(pat, sizeof pat, "%s/*", path);
    WIN32_FIND_DATAA fd;
    HANDLE h = FindFirstFileA(pat, &fd);
    if (h == INVALID_HANDLE_VALUE) { free(d); set_errno(2); RET(0); return; }
    do {
        d->names = realloc(d->names, sizeof(char *) * (size_t)(d->n + 1));
        d->names[d->n++] = strdup(fd.cFileName);
    } while (FindNextFileA(h, &fd));
    FindClose(h);
#else
    DIR *h = opendir(path);
    if (!h) { free(d); set_errno(2); RET(0); return; }
    for (struct dirent *e; (e = readdir(h));) {
        d->names = realloc(d->names, sizeof(char *) * (size_t)(d->n + 1));
        d->names[d->n++] = strdup(e->d_name);
    }
    closedir(h);
#endif
    d->ent = rt_calloc(1, 264);
    for (int k = 0; k < 64; k++)
        if (!dir_addr[k]) { dirs[k] = d; dir_addr[k] = d->ent; RET(d->ent); return; }
    RET(0);
}
IMP(readdir) {
    for (int k = 0; k < 64; k++)
        if (dir_addr[k] == A(0) && A(0)) {
            gdir *d = dirs[k];
            if (d->pos >= d->n) { RET(0); return; }
            const char *nm = d->names[d->pos++];
            uint32_t e = d->ent;
            memset(G(e), 0, 264);
            rt_st32(e, (uint32_t)d->pos);
            uint16_t reclen = 264;
            memcpy(rt_mem + e + 4, &reclen, 2);
            rt_mem[e + 6] = 8; /* DT_REG; the game checks names, not types */
            rt_mem[e + 7] = (uint8_t)strlen(nm);
            strncpy((char *)rt_mem + e + 8, nm, 255);
            RET(e);
            return;
        }
    RET(0);
}
IMP(closedir) {
    for (int k = 0; k < 64; k++)
        if (dir_addr[k] == A(0) && A(0)) {
            gdir *d = dirs[k];
            for (int j = 0; j < d->n; j++) free(d->names[j]);
            free(d->names);
            rt_free(d->ent);
            free(d);
            dir_addr[k] = 0;
        }
    RET(0);
}

/* ---- memory allocation ------------------------------------------------------------------------------------------------ */
IMP(malloc) { RET(rt_malloc(A(0))); }
IMP(calloc) { RET(rt_calloc(A(0), A(1))); }
IMP(realloc) { RET(rt_realloc(A(0), A(1))); }
IMP(free) { rt_free(A(0)); }

/* ---- time ------------------------------------------------------------------------------------------------------------- */
static double now_seconds(void) {
#ifdef _WIN32
    FILETIME ft;
    GetSystemTimePreciseAsFileTime(&ft);
    uint64_t t = ((uint64_t)ft.dwHighDateTime << 32) | ft.dwLowDateTime;
    return (double)(t - 116444736000000000ull) / 1e7;
#else
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (double)tv.tv_sec + tv.tv_usec / 1e6;
#endif
}
IMP(time) { uint32_t t = (uint32_t)now_seconds(); if (A(0)) rt_st32(A(0), t); RET(t); }
IMP(gettimeofday) {
    double t = now_seconds();
    if (A(0)) { rt_st32(A(0), (uint32_t)t); rt_st32(A(0) + 4, (uint32_t)((t - (uint32_t)t) * 1e6)); }
    RET(0);
}
IMP(CFAbsoluteTimeGetCurrent) { rt_dret(c, now_seconds() - 978307200.0); } /* seconds since 2001-01-01 */
static void sleep_us(uint64_t us) {
#ifdef _WIN32
    Sleep((DWORD)(us / 1000));
#else
    usleep((useconds_t)us);
#endif
}
IMP(usleep) { sleep_us(A(0)); RET(0); }
IMP(nanosleep) { sleep_us((uint64_t)rt_ld32(A(0)) * 1000000 + rt_ld32(A(0) + 4) / 1000); RET(0); }
IMP(sched_yield) { sleep_us(0); RET(0); }

/* struct tm: 11 ints plus tm_gmtoff and tm_zone (44 bytes) */
static void put_tm(uint32_t g, const struct tm *t) {
    int v[9] = {t->tm_sec, t->tm_min, t->tm_hour, t->tm_mday, t->tm_mon, t->tm_year, t->tm_wday, t->tm_yday, t->tm_isdst};
    for (int k = 0; k < 9; k++) rt_st32(g + 4 * k, (uint32_t)v[k]);
    rt_st32(g + 36, 0);
    rt_st32(g + 40, 0);
}
IMP(localtime_r) {
    time_t t = (time_t)(int32_t)rt_ld32(A(0));
    struct tm tmv;
#ifdef _WIN32
    localtime_s(&tmv, &t);
#else
    localtime_r(&t, &tmv);
#endif
    put_tm(A(1), &tmv);
    RET(A(1));
}
IMP(mktime) {
    struct tm t = {0};
    uint32_t g = A(0);
    t.tm_sec = (int)rt_ld32(g); t.tm_min = (int)rt_ld32(g + 4); t.tm_hour = (int)rt_ld32(g + 8);
    t.tm_mday = (int)rt_ld32(g + 12); t.tm_mon = (int)rt_ld32(g + 16); t.tm_year = (int)rt_ld32(g + 20);
    t.tm_isdst = -1;
    RET((uint32_t)mktime(&t));
}

/* ---- system ------------------------------------------------------------------------------------------------------------ */
IMP(exit) { rt_log("game called exit(%d)", (int)A(0)); exit((int)A(0)); }
IMP(__assert_rtn) { rt_fatal("assertion failed: %s, %s:%d (%s)", S(3), S(1), (int)A(2), S(0)); }
IMP(sigaction) { RET(0); }
/* sysctlbyname(name, oldp, oldlenp, newp, newlen): the device model the game asks for */
IMP(sysctlbyname) {
    const char *n = S(0), *v = NULL;
    if (!strcmp(n, "hw.machine")) v = "iPad1,1";
    else if (!strcmp(n, "hw.model")) v = "K48AP";
    if (!v) {
        if (!strcmp(n, "hw.memsize") || !strcmp(n, "hw.physmem")) {
            if (A(1)) rt_st32(A(1), 256u << 20);
            if (A(2)) rt_st32(A(2), 4);
            RET(0);
            return;
        }
        rt_log("sysctlbyname %s: unknown", n);
        RET(-1);
        return;
    }
    uint32_t len = (uint32_t)strlen(v) + 1;
    if (A(1) && A(2) && rt_ld32(A(2)) >= len) memcpy(G(A(1)), v, len);
    if (A(2)) rt_st32(A(2), len);
    RET(0);
}
/* uname: 5 fields of 256 bytes */
IMP(uname) {
    const char *f[5] = {"Darwin", "iPad", "10.3.1", "Darwin Kernel Version 10.3.1", "iPad1,1"};
    for (int k = 0; k < 5; k++) { memset(G(A(0) + 256 * k), 0, 256); strcpy((char *)G(A(0) + 256 * k), f[k]); }
    RET(0);
}
IMP(gethostname) { strncpy((char *)G(A(0)), "iPad", A(1)); RET(0); }
IMP(mach_host_self) { RET(1); }
IMP(host_page_size) { rt_st32(A(1), 4096); RET(0); }
/* host_statistics(host, HOST_VM_INFO, info, count): free/active/inactive/wired page counts */
IMP(host_statistics) {
    uint32_t info = A(2);
    rt_st32(info + 0, 16384); /* free: 64 MB */
    rt_st32(info + 4, 8192);
    rt_st32(info + 8, 8192);
    rt_st32(info + 12, 8192);
    RET(0);
}
IMP(CC_MD5) { memset(G(A(2)), 0, 16); RET(A(2)); } /* used for a device identifier hash */

/* ---- data imports ---------------------------------------------------------------------------------------------------- */
static uint32_t resolve(const char *name) {
    if (!strcmp(name, "__stdoutp")) return stdoutp_word;
    return 0;
}

void rt_libc_register(void) {
    stdout_block = wrap_file(stdout);
    stderr_block = wrap_file(stderr);
    stdoutp_word = rt_calloc(1, 4);
    rt_st32(stdoutp_word, stdout_block);
    rt_data_resolver_add(resolve);
    REG(__error);
    REG(memcpy); REG(memmove); REG(memset); REG(bzero); REG(memcmp); REG(strlen); REG(strcmp); REG(strncmp);
    REG(strcasecmp); REG(strncasecmp); REG(strcpy); REG(strncpy); REG(strcat); REG(strlcpy); REG(strchr);
    REG(strrchr); REG(strstr); REG(wcslen); REG(wcscpy); REG(wcsncpy); REG(wcscmp); REG(__tolower);
    REG(atoi); REG(atof); REG(strtol); REG(__divsi3); REG(__modsi3); REG(__udivsi3); REG(__umodsi3); REG(rand);
    REG(srand);
    REG(sin); REG(cos); REG(tan); REG(asin); REG(acos); REG(atan); REG(atan2); REG(pow); REG(fmod);
    REG(sinf); REG(cosf); REG(tanf); REG(atanf); REG(acosf); REG(floorf); REG(ceilf); REG(roundf); REG(fmodf);
    REG(sprintf); REG(__sprintf_chk); REG(snprintf); REG(vsprintf); REG(sscanf); REG(printf); REG(puts);
    REG(putchar); REG(perror);
    REG(fopen); REG(fclose); REG(fread); REG(fwrite); REG(fseek); REG(ftell); REG(fileno); REG(fprintf);
    REG(vfprintf); REG(write); REG(close); REG(stat); REG(remove); REG(rename); REG(chdir); REG(getcwd);
    REG(realpath$DARWIN_EXTSN); REG(opendir); REG(readdir); REG(closedir);
    REG(malloc); REG(calloc); REG(realloc); REG(free);
    REG(time); REG(gettimeofday); REG(CFAbsoluteTimeGetCurrent); REG(usleep); REG(nanosleep); REG(sched_yield);
    REG(localtime_r); REG(mktime);
    REG(exit); REG(__assert_rtn); REG(sigaction); REG(sysctlbyname); REG(uname); REG(gethostname);
    REG(mach_host_self); REG(host_page_size); REG(host_statistics); REG(CC_MD5);
    (void)stderr_block;
}
