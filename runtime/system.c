/* Foundation system services, the run loop, notifications and the CoreFoundation imports the game uses.
 *
 * Classes: NSBundle, NSFileManager, NSUserDefaults, NSDate, NSDateFormatter, NSLocale, NSTimer, NSRunLoop,
 * NSThread, NSNotificationCenter, NSNotification, NSAssertionHandler. C imports: NSSearchPathForDirectoriesInDomains
 * and the CF functions (CF objects are the NS objects: toll-free bridging).
 *
 * Layouts and choices:
 *   NSDate          { isa, double t } at offset 4 (4-byte aligned as on iOS armv6): seconds since 2001-01-01 UTC
 *                   (CFAbsoluteTime). Every other class here keeps its data in host state (rt_objc_state).
 *   Run loops       one per thread (NSRunLoop objects made on demand). A loop holds its scheduled timers (retained).
 *                   The main loop also holds the queue of performSelector:...afterDelay: requests
 *                   (rt_runloop_perform_later, callable from any thread). rt_runloop_run_once(c), which UIKit calls
 *                   every display frame, fires the main loop's due timers, then the due queued requests, inside an
 *                   autorelease pool. Secondary threads run their own loop through -run, -runUntilDate:,
 *                   -runMode:beforeDate: or CFRunLoopRunInMode, which sleep in short steps until something is due.
 *                   Times inside the run loop are rt_now() (monotonic); NSDate converts at the boundary.
 *   Timers          fire target/selector with the timer as argument; a repeating timer is rescheduled before the
 *                   callout (missed periods are skipped, as Cocoa does), a one-shot timer is invalidated after it.
 *                   A timer retains its target and userInfo until invalidated.
 *   NSThread        detachNewThreadSelector:toTarget:withObject: starts a real host thread with its own cpu_t
 *                   (rt_thread_cpu) and an autorelease pool around the entry method. +exit longjmps out of it.
 *   Notifications   delivered synchronously on the posting thread; observers are not retained (Cocoa semantics).
 *                   An observer removed while a post is under way is not called any more.
 *   NSUserDefaults  persisted as an XML plist at <home>/Library/Preferences/com.gameloft.NovaiPad.plist, written
 *                   after every change (the game never calls -synchronize). Lookups fall back to registerDefaults:
 *                   and then to the global domain (AppleLanguages = ("en"), AppleLocale = "en_US"), which the game
 *                   reads to pick its language.
 *   Plists          read here in both formats (Info.plist in the bundle is a binary plist), written as XML.
 *   CFArray         CFArrayCreateMutable makes a private array class: with NULL callbacks (Reachability passes
 *                   NULL) the values are raw pointers, not retained, so it cannot be an NSMutableArray. It also
 *                   answers count/objectAtIndex:/addObject:/removeAllObjects for code that treats it as an NSArray.
 *   Paths           the game sees rt_bundle_path and rt_home_path; every file access goes through rt_host_path.
 * One mutex protects the run loops, the perform queue and the observer list; it is never held while game code or
 * a -dealloc can run.
 */
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>

#ifdef _WIN32
#include <direct.h>
#include <windows.h>
#else
#include <dirent.h>
#include <pthread.h>
#include <sys/time.h>
#include <unistd.h>
#endif

#include "rt.h"

#define SELF c->r[0]
#define ARG(k) rt_arg(c, (k) + 2)
#define M(name) static void name(cpu_t *c, uint8_t *m)
#define IMP(name) static void imp_##name(cpu_t *c)
#define REG(name) rt_import_register(#name, imp_##name)

#define PREFS_FILE "/Library/Preferences/com.gameloft.NovaiPad.plist"
#define BUNDLE_ID "com.gameloft.NovaiPad"
#define DISTANT_FUTURE 63113904000.0 /* 4001-01-01 */
#define DISTANT_PAST (-63114076800.0) /* 0001-01-01 */
#define UNIX_TO_CF 978307200.0

static id cls_bundle, cls_fileman, cls_defaults, cls_date, cls_datefmt, cls_locale, cls_timer, cls_runloop,
    cls_thread, cls_center, cls_note, cls_assert, cls_cfarray, cls_fileurl;
static id the_bundle, the_fileman, the_defaults, the_locale, the_center, the_assert, main_thread_obj;

/* ---- host services: lock, clocks, sleeping, threads --------------------------------------------------------- */
#ifdef _WIN32
static SRWLOCK sys_mutex = SRWLOCK_INIT;
static void lock(void) { AcquireSRWLockExclusive(&sys_mutex); }
static void unlock(void) { ReleaseSRWLockExclusive(&sys_mutex); }
double rt_now(void) {
    static LARGE_INTEGER freq;
    LARGE_INTEGER t;
    if (!freq.QuadPart) QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&t);
    return (double)t.QuadPart / (double)freq.QuadPart;
}
static double wall_unix(void) {
    FILETIME ft;
    GetSystemTimePreciseAsFileTime(&ft);
    uint64_t t = ((uint64_t)ft.dwHighDateTime << 32) | ft.dwLowDateTime;
    return (double)(t - 116444736000000000ull) / 1e7;
}
static void sleep_s(double s) {
    if (s <= 0) return;
    Sleep((DWORD)(s * 1000.0 + 0.5));
}
#else
static pthread_mutex_t sys_mutex = PTHREAD_MUTEX_INITIALIZER;
static void lock(void) { pthread_mutex_lock(&sys_mutex); }
static void unlock(void) { pthread_mutex_unlock(&sys_mutex); }
double rt_now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec / 1e9;
}
static double wall_unix(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (double)tv.tv_sec + tv.tv_usec / 1e6;
}
static void sleep_s(double s) {
    if (s <= 0) return;
    struct timespec ts = {(time_t)s, (long)((s - (double)(time_t)s) * 1e9)};
    nanosleep(&ts, NULL);
}
#endif

static double cf_now(void) { return wall_unix() - UNIX_TO_CF; } /* CFAbsoluteTime */
static double mono_from_cf(double t) { return rt_now() + (t - cf_now()); }

static __thread int tl_is_main; /* set on the thread that runs rt_system_define */

/* log a message once per distinct text */
static void log_once(const char *fmt, ...) {
    static uint32_t seen[512];
    static int nseen;
    char buf[512];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    uint32_t h = 2166136261u;
    for (const char *p = buf; *p; p++) h = (h ^ (uint8_t)*p) * 16777619u;
    lock();
    for (int k = 0; k < nseen; k++)
        if (seen[k] == h) { unlock(); return; }
    if (nseen < 512) seen[nseen++] = h;
    unlock();
    rt_log("%s", buf);
}

/* ---- small object helpers -------------------------------------------------------------------------------------- */
static const char *S(id s) { return rt_nsstring_utf8(s); } /* NULL for nil or a non-string */
static id str_auto(const char *s) { return rt_nsstring(s); }

static id pool_new(cpu_t *c) {
    id p = rt_class("NSAutoreleasePool");
    return p ? rt_send(c, rt_send(c, p, "alloc", 0), "init", 0) : 0;
}
static void pool_drain(cpu_t *c, id p) { if (p) rt_send(c, p, "drain", 0); }

/* [target sel:arg] for a selector held as a SEL */
static void callout(cpu_t *c, id target, SEL sel, id arg) {
    if (!target || !sel) return;
    uint32_t imp = rt_lookup(rt_object_class(target), sel);
    if (!imp) {
        log_once("system: %s does not respond to %s (callout dropped)", rt_class_name(rt_object_class(target)),
                 rt_sel_name(sel));
        return;
    }
    rt_call(c, imp, 3, target, sel, arg);
}

static void set_bool_out(uint32_t p, int v) { if (p) rt_mem[p] = (uint8_t)(v ? 1 : 0); }
static void clear_error(uint32_t errp) { if (errp) rt_st32(errp, 0); }

/* an autoreleased NSArray from host ids that are +1 (the array takes them over) */
static id array_take(cpu_t *c, id *items, uint32_t n) {
    id a = rt_nsarray_new(items, n);
    for (uint32_t k = 0; k < n; k++) rt_release(c, items[k]);
    return a;
}

/* ---- dates: civil calendar arithmetic (proleptic Gregorian) ---------------------------------------------------- */
static int64_t days_from_civil(int64_t y, int m, int d) {
    y -= m <= 2;
    int64_t era = (y >= 0 ? y : y - 399) / 400;
    int64_t yoe = y - era * 400;
    int64_t doy = (153 * (m + (m > 2 ? -3 : 9)) + 2) / 5 + d - 1;
    int64_t doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + doe - 719468;
}

static void civil_from_days(int64_t z, int *y, int *m, int *d) {
    z += 719468;
    int64_t era = (z >= 0 ? z : z - 146096) / 146097;
    int64_t doe = z - era * 146097;
    int64_t yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    int64_t doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    int64_t mp = (5 * doy + 2) / 153;
    *d = (int)(doy - (153 * mp + 2) / 5 + 1);
    *m = (int)(mp < 10 ? mp + 3 : mp - 9);
    *y = (int)(yoe + era * 400 + (*m <= 2));
}

typedef struct { int y, mo, d, h, mi, s, ms, wday, gmtoff; } civil;

/* the host's offset from UTC (seconds) at a Unix time */
static int local_offset(int64_t unix_t) {
    time_t tt = (time_t)unix_t;
    struct tm tm;
#ifdef _WIN32
    if (localtime_s(&tm, &tt)) return 0;
#else
    if (!localtime_r(&tt, &tm)) return 0;
#endif
    int64_t local = days_from_civil(tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday) * 86400 + tm.tm_hour * 3600 +
                    tm.tm_min * 60 + tm.tm_sec;
    return (int)(local - unix_t);
}

static civil civil_of(double cf, int local) {
    double u = cf + UNIX_TO_CF;
    double fl = u < 0 ? (double)(int64_t)u - ((double)(int64_t)u != u) : (double)(int64_t)u;
    int64_t secs = (int64_t)fl;
    civil r;
    r.ms = (int)((u - fl) * 1000.0);
    r.gmtoff = local ? local_offset(secs) : 0;
    secs += r.gmtoff;
    int64_t days = secs >= 0 ? secs / 86400 : -((-secs + 86399) / 86400);
    int64_t rem = secs - days * 86400;
    civil_from_days(days, &r.y, &r.mo, &r.d);
    r.h = (int)(rem / 3600);
    r.mi = (int)(rem / 60 % 60);
    r.s = (int)(rem % 60);
    r.wday = (int)(((days % 7) + 11) % 7); /* 1970-01-01 was a Thursday; 0 = Sunday */
    return r;
}

static double cf_of_civil(const civil *v, int local) {
    int64_t secs = days_from_civil(v->y, v->mo, v->d) * 86400 + v->h * 3600 + v->mi * 60 + v->s;
    if (local) secs -= local_offset(secs);
    return (double)secs - UNIX_TO_CF + v->ms / 1000.0;
}

/* ---- NSDate ---------------------------------------------------------------------------------------------------- */
static double date_val(id d) {
    double t = 0;
    if (d && rt_is_kind(d, cls_date)) memcpy(&t, rt_mem + d + 4, 8);
    return t;
}
static id date_init(id d, double t) { memcpy(rt_mem + d + 4, &t, 8); return d; }
static id date_new(double t) { return date_init(rt_objc_alloc(cls_date), t); }
static id date_auto(double t) { return rt_autorelease(date_new(t)); }

M(d_date) { rt_ret(c, date_auto(cf_now())); }
M(d_since_now) { rt_ret(c, date_auto(cf_now() + rt_darg(c, 2))); }
M(d_since_1970) { rt_ret(c, date_auto(rt_darg(c, 2) - UNIX_TO_CF)); }
M(d_since_ref) { rt_ret(c, date_auto(rt_darg(c, 2))); }
M(d_future) { rt_ret(c, date_auto(DISTANT_FUTURE)); }
M(d_past) { rt_ret(c, date_auto(DISTANT_PAST)); }
M(d_class_ref_now) { rt_dret(c, cf_now()); }
M(d_init) { date_init(SELF, cf_now()); }
M(d_init_since_now) { date_init(SELF, cf_now() + rt_darg(c, 2)); }
M(d_init_since_ref) { date_init(SELF, rt_darg(c, 2)); }
M(d_init_since_1970) { date_init(SELF, rt_darg(c, 2) - UNIX_TO_CF); }
M(d_init_since_date) { date_init(SELF, date_val(ARG(2)) + rt_darg(c, 2)); } /* initWithTimeInterval:sinceDate: */
M(d_ref) { rt_dret(c, date_val(SELF)); }
M(d_1970) { rt_dret(c, date_val(SELF) + UNIX_TO_CF); }
M(d_now) { rt_dret(c, date_val(SELF) - cf_now()); }
M(d_since_date) { rt_dret(c, date_val(SELF) - date_val(ARG(0))); }
M(d_adding) { rt_ret(c, date_auto(date_val(SELF) + rt_darg(c, 2))); }
M(d_compare) {
    double a = date_val(SELF), b = date_val(ARG(0));
    rt_ret(c, a < b ? 0xffffffffu : a > b ? 1u : 0u);
}
M(d_equal) { rt_ret(c, ARG(0) && rt_is_kind(ARG(0), cls_date) && date_val(SELF) == date_val(ARG(0))); }
M(d_earlier) { rt_ret(c, date_val(SELF) <= date_val(ARG(0)) ? SELF : ARG(0)); }
M(d_later) { rt_ret(c, date_val(SELF) >= date_val(ARG(0)) ? SELF : ARG(0)); }
M(d_hash) { rt_ret(c, (uint32_t)(int64_t)date_val(SELF)); }
M(d_copy) { rt_ret(c, rt_retain(SELF)); }
M(d_description) {
    civil v = civil_of(date_val(SELF), 0);
    char b[64];
    snprintf(b, sizeof b, "%04d-%02d-%02d %02d:%02d:%02d +0000", v.y, v.mo, v.d, v.h, v.mi, v.s);
    rt_ret(c, str_auto(b));
}

/* ---- NSDateFormatter (Unicode date patterns, local time zone, en_US names) -------------------------------------- */
typedef struct { char fmt[128]; int date_style, time_style; } datefmt_state;

static const char *const month_names[] = {"January", "February", "March", "April", "May", "June", "July",
                                          "August", "September", "October", "November", "December"};
static const char *const day_names[] = {"Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"};

static void out_add(char *out, size_t cap, size_t *n, const char *s) {
    for (; *s && *n + 1 < cap; s++) out[(*n)++] = *s;
    out[*n] = 0;
}
static void out_num(char *out, size_t cap, size_t *n, int v, int width) {
    char b[24];
    snprintf(b, sizeof b, "%0*d", width, v);
    out_add(out, cap, n, b);
}

static void format_date(const char *fmt, double cf, char *out, size_t cap) {
    civil v = civil_of(cf, 1);
    size_t n = 0;
    out[0] = 0;
    for (const char *p = fmt; *p;) {
        char ch = *p;
        if (ch == '\'') { /* quoted literal; '' is a quote */
            p++;
            if (*p == '\'') { out_add(out, cap, &n, "'"); p++; continue; }
            while (*p && !(*p == '\'' && p[1] != '\'')) {
                if (*p == '\'') p++;
                char t[2] = {*p++, 0};
                out_add(out, cap, &n, t);
            }
            if (*p) p++;
            continue;
        }
        if (!((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z'))) {
            char t[2] = {ch, 0};
            out_add(out, cap, &n, t);
            p++;
            continue;
        }
        int run = 0;
        while (p[run] == ch) run++;
        p += run;
        int h12 = v.h % 12 ? v.h % 12 : 12;
        char b[64];
        switch (ch) {
        case 'y': case 'Y': case 'u':
            if (run == 2) out_num(out, cap, &n, v.y % 100, 2);
            else out_num(out, cap, &n, v.y, run);
            break;
        case 'M': case 'L':
            if (run >= 4) out_add(out, cap, &n, month_names[v.mo - 1]);
            else if (run == 3) { snprintf(b, sizeof b, "%.3s", month_names[v.mo - 1]); out_add(out, cap, &n, b); }
            else out_num(out, cap, &n, v.mo, run);
            break;
        case 'd': out_num(out, cap, &n, v.d, run); break;
        case 'D': out_num(out, cap, &n, (int)(days_from_civil(v.y, v.mo, v.d) - days_from_civil(v.y, 1, 1) + 1), run); break;
        case 'E': case 'e': case 'c':
            if (run >= 4) out_add(out, cap, &n, day_names[v.wday]);
            else if ((ch == 'e' || ch == 'c') && run <= 2) out_num(out, cap, &n, v.wday + 1, run);
            else { snprintf(b, sizeof b, "%.3s", day_names[v.wday]); out_add(out, cap, &n, b); }
            break;
        case 'H': out_num(out, cap, &n, v.h, run); break;
        case 'k': out_num(out, cap, &n, v.h ? v.h : 24, run); break;
        case 'h': out_num(out, cap, &n, h12, run); break;
        case 'K': out_num(out, cap, &n, v.h % 12, run); break;
        case 'm': out_num(out, cap, &n, v.mi, run); break;
        case 's': out_num(out, cap, &n, v.s, run); break;
        case 'S': {
            int ms = v.ms;
            if (run == 1) out_num(out, cap, &n, ms / 100, 1);
            else if (run == 2) out_num(out, cap, &n, ms / 10, 2);
            else { out_num(out, cap, &n, ms, 3); for (int k = 3; k < run; k++) out_add(out, cap, &n, "0"); }
            break;
        }
        case 'a': out_add(out, cap, &n, v.h < 12 ? "AM" : "PM"); break;
        case 'Z': case 'z': case 'v': case 'V': case 'O': case 'x': case 'X': {
            int off = v.gmtoff, neg = off < 0;
            if (neg) off = -off;
            if (ch == 'Z' && run <= 3) snprintf(b, sizeof b, "%c%02d%02d", neg ? '-' : '+', off / 3600, off / 60 % 60);
            else snprintf(b, sizeof b, "GMT%c%02d:%02d", neg ? '-' : '+', off / 3600, off / 60 % 60);
            out_add(out, cap, &n, b);
            break;
        }
        case 'G': out_add(out, cap, &n, "AD"); break;
        default:
            for (int k = 0; k < run; k++) { char t[2] = {ch, 0}; out_add(out, cap, &n, t); }
        }
    }
}

/* parse a date with the same pattern (numeric fields, month names, AM/PM); returns 0 on a mismatch */
static int parse_date(const char *fmt, const char *s, double *cf) {
    civil v = {2001, 1, 1, 0, 0, 0, 0, 0, 0};
    int pm = -1;
    for (const char *p = fmt; *p;) {
        char ch = *p;
        if (ch == '\'') {
            p++;
            while (*p && *p != '\'') { if (*s++ != *p++) return 0; }
            if (*p) p++;
            continue;
        }
        if (!((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z'))) {
            if (*s != ch) return 0;
            s++, p++;
            continue;
        }
        int run = 0;
        while (p[run] == ch) run++;
        p += run;
        if ((ch == 'M' || ch == 'L') && run >= 3) {
            int got = 0;
            for (int k = 0; k < 12 && !got; k++) {
                size_t len = run == 3 ? 3 : strlen(month_names[k]);
                if (!strncmp(s, month_names[k], len)) { v.mo = k + 1; s += len; got = 1; }
            }
            if (!got) return 0;
            continue;
        }
        if (ch == 'E') {
            int got = 0;
            for (int k = 0; k < 7 && !got; k++) {
                size_t len = run <= 3 ? 3 : strlen(day_names[k]);
                if (!strncmp(s, day_names[k], len)) { s += len; got = 1; }
            }
            if (!got) return 0;
            continue;
        }
        if (ch == 'a') {
            if (!strncmp(s, "AM", 2)) pm = 0;
            else if (!strncmp(s, "PM", 2)) pm = 1;
            else return 0;
            s += 2;
            continue;
        }
        if (ch == 'Z' || ch == 'z') { /* skip an offset or a GMT+hh:mm */
            while (*s && *s != ' ') s++;
            continue;
        }
        int val = 0, digits = 0, max = run >= 2 ? run : (ch == 'y' || ch == 'Y' || ch == 'u') ? 4 : 2;
        while (*s >= '0' && *s <= '9' && digits < max) val = val * 10 + (*s++ - '0'), digits++;
        if (!digits) return 0;
        switch (ch) {
        case 'y': case 'Y': case 'u': v.y = run == 2 ? 2000 + val : val; break;
        case 'M': case 'L': v.mo = val; break;
        case 'd': v.d = val; break;
        case 'H': case 'k': v.h = val % 24; break;
        case 'h': case 'K': v.h = val % 12; break;
        case 'm': v.mi = val; break;
        case 's': v.s = val; break;
        case 'S': v.ms = digits == 1 ? val * 100 : digits == 2 ? val * 10 : val; break;
        default: break;
        }
    }
    if (pm == 1) v.h = v.h % 12 + 12;
    if (*s) return 0;
    *cf = cf_of_civil(&v, 1);
    return 1;
}

static datefmt_state *dfs(id f) { return rt_objc_state(f, sizeof(datefmt_state)); }

static const char *style_pattern(const datefmt_state *st, char *buf, size_t cap) {
    static const char *const dp[] = {"", "M/d/yy", "MMM d, yyyy", "MMMM d, yyyy", "EEEE, MMMM d, yyyy"};
    static const char *const tp[] = {"", "h:mm a", "h:mm:ss a", "h:mm:ss a z", "h:mm:ss a zzzz"};
    int ds = st->date_style >= 0 && st->date_style <= 4 ? st->date_style : 0;
    int ts = st->time_style >= 0 && st->time_style <= 4 ? st->time_style : 0;
    snprintf(buf, cap, "%s%s%s", dp[ds], ds && ts ? (ds >= 3 ? " 'at' " : ", ") : "", tp[ts]);
    return buf;
}

static const char *pattern_of(id f, char *buf, size_t cap) {
    datefmt_state *st = dfs(f);
    return st->fmt[0] ? st->fmt : style_pattern(st, buf, cap);
}

M(df_init) { dfs(SELF); }
M(df_set_format) {
    const char *f = S(ARG(0));
    snprintf(dfs(SELF)->fmt, sizeof dfs(SELF)->fmt, "%s", f ? f : "");
}
M(df_format) { rt_ret(c, str_auto(dfs(SELF)->fmt)); }
M(df_set_date_style) { dfs(SELF)->date_style = (int)ARG(0); }
M(df_set_time_style) { dfs(SELF)->time_style = (int)ARG(0); }
M(df_ignore) { (void)c; } /* setLocale:, setTimeZone:, setFormatterBehavior:, ... */
M(df_string_from_date) {
    char pat[128], out[256];
    if (!ARG(0)) { rt_ret(c, 0); return; }
    format_date(pattern_of(SELF, pat, sizeof pat), date_val(ARG(0)), out, sizeof out);
    rt_ret(c, str_auto(out));
}
M(df_date_from_string) {
    char pat[128];
    const char *s = S(ARG(0));
    double t;
    rt_ret(c, s && parse_date(pattern_of(SELF, pat, sizeof pat), s, &t) ? date_auto(t) : 0);
}

/* ---- NSLocale: en_US ------------------------------------------------------------------------------------------- */
static id locale_value(const char *key) {
    static const struct { const char *k1, *k2, *v; } t[] = {
        {"kCFLocaleCountryCodeKey", "NSLocaleCountryCode", "US"},
        {"kCFLocaleLanguageCodeKey", "NSLocaleLanguageCode", "en"},
        {"kCFLocaleIdentifierKey", "NSLocaleIdentifier", "en_US"},
        {"kCFLocaleCurrencyCodeKey", "NSLocaleCurrencyCode", "USD"},
        {"kCFLocaleCurrencySymbolKey", "NSLocaleCurrencySymbol", "$"},
        {"kCFLocaleDecimalSeparatorKey", "NSLocaleDecimalSeparator", "."},
        {"kCFLocaleGroupingSeparatorKey", "NSLocaleGroupingSeparator", ","},
        {"kCFLocaleMeasurementSystemKey", "NSLocaleMeasurementSystem", "U.S."},
    };
    if (!key) return 0;
    for (size_t k = 0; k < sizeof t / sizeof *t; k++)
        if (!strcmp(key, t[k].k1) || !strcmp(key, t[k].k2)) return str_auto(t[k].v);
    if (!strcmp(key, "kCFLocaleUsesMetricSystemKey") || !strcmp(key, "NSLocaleUsesMetricSystem"))
        return rt_autorelease(rt_nsnumber_new_bool(0));
    log_once("NSLocale: objectForKey:%s (nil)", key);
    return 0;
}

M(loc_current) { rt_ret(c, the_locale); }
M(loc_init_ident) { if (SELF != the_locale) rt_objc_free(SELF); rt_ret(c, rt_retain(the_locale)); }
M(loc_object) { rt_ret(c, locale_value(S(ARG(0)))); }
M(loc_ident) { rt_ret(c, str_auto("en_US")); }
M(loc_display_name) { rt_ret(c, ARG(1)); } /* displayNameForKey:value: */
M(loc_preferred) { id e = rt_nsstring_new("en"); rt_ret(c, rt_autorelease(array_take(c, &e, 1))); }
M(loc_available) { id e = rt_nsstring_new("en_US"); rt_ret(c, rt_autorelease(array_take(c, &e, 1))); }
M(singleton_dealloc) { (void)c; } /* shared objects survive an extra release */
M(ret_self) { (void)c; }

/* ---- host file system helpers (host paths) --------------------------------------------------------------------- */
static void host_of(const char *gpath, char *out, size_t cap) { snprintf(out, cap, "%s", rt_host_path(gpath)); }

static int hstat(const char *hpath, int *is_dir, uint64_t *size, double *mtime) {
    struct stat st;
    char b[1024];
    size_t n = strlen(hpath);
    if (n > 1 && n < sizeof b && (hpath[n - 1] == '/' || hpath[n - 1] == '\\')) {
        /* "dir/" (NSTemporaryDirectory ends in a slash): the Windows CRT's stat fails on a trailing separator */
        memcpy(b, hpath, n + 1);
        while (n > 1 && (b[n - 1] == '/' || b[n - 1] == '\\') && b[n - 2] != ':') b[--n] = 0;
        hpath = b;
    }
    if (stat(hpath, &st)) return 0;
    if (is_dir) *is_dir = (st.st_mode & S_IFMT) == S_IFDIR;
    if (size) *size = (uint64_t)st.st_size;
    if (mtime) *mtime = (double)st.st_mtime - UNIX_TO_CF;
    return 1;
}

static int hmkdir(const char *hpath) {
#ifdef _WIN32
    return _mkdir(hpath) == 0;
#else
    return mkdir(hpath, 0755) == 0;
#endif
}

static int hmkdirs(const char *hpath) {
    char b[1024];
    int dir;
    snprintf(b, sizeof b, "%s", hpath);
    size_t n = strlen(b);
    while (n > 1 && (b[n - 1] == '/' || b[n - 1] == '\\')) b[--n] = 0;
    for (char *p = b + 1; *p; p++)
        if (*p == '/' || *p == '\\') {
            char keep = *p;
            *p = 0;
            if (!(hstat(b, &dir, NULL, NULL) && dir) && !(p[-1] == ':')) hmkdir(b);
            *p = keep;
        }
    if (hstat(b, &dir, NULL, NULL)) return dir;
    return hmkdir(b);
}

/* the names in a directory (not . and ..); NULL if it is no directory. Free with free_list. */
static char **hlist(const char *hpath, int *count) {
    char **v = NULL;
    int n = 0, cap = 0;
#ifdef _WIN32
    char pat[1100];
    snprintf(pat, sizeof pat, "%s\\*", hpath);
    WIN32_FIND_DATAA fd;
    HANDLE h = FindFirstFileA(pat, &fd);
    if (h == INVALID_HANDLE_VALUE) { *count = 0; return NULL; }
    do {
        const char *nm = fd.cFileName;
#else
    DIR *d = opendir(hpath);
    if (!d) { *count = 0; return NULL; }
    struct dirent *e;
    while ((e = readdir(d))) {
        const char *nm = e->d_name;
#endif
        if (!strcmp(nm, ".") || !strcmp(nm, "..")) continue;
        if (n == cap) { cap = cap ? cap * 2 : 16; v = realloc(v, sizeof *v * (size_t)cap); }
        v[n++] = strdup(nm);
#ifdef _WIN32
    } while (FindNextFileA(h, &fd));
    FindClose(h);
#else
    }
    closedir(d);
#endif
    if (!v) v = malloc(sizeof *v);
    *count = n;
    return v;
}
static void free_list(char **v, int n) {
    for (int k = 0; k < n; k++) free(v[k]);
    free(v);
}

static int hremove_tree(const char *hpath) {
    int dir;
    if (!hstat(hpath, &dir, NULL, NULL)) return 0;
    if (!dir) return remove(hpath) == 0;
    int n;
    char **v = hlist(hpath, &n);
    for (int k = 0; k < n; k++) {
        char sub[1100];
        snprintf(sub, sizeof sub, "%s/%s", hpath, v[k]);
        hremove_tree(sub);
    }
    free_list(v, n);
#ifdef _WIN32
    return _rmdir(hpath) == 0;
#else
    return rmdir(hpath) == 0;
#endif
}

static int hcopy_tree(const char *from, const char *to) {
    int dir;
    if (!hstat(from, &dir, NULL, NULL)) return 0;
    if (dir) {
        if (!hmkdir(to)) return 0;
        int n, ok = 1;
        char **v = hlist(from, &n);
        for (int k = 0; k < n; k++) {
            char a[1100], b[1100];
            snprintf(a, sizeof a, "%s/%s", from, v[k]);
            snprintf(b, sizeof b, "%s/%s", to, v[k]);
            ok &= hcopy_tree(a, b);
        }
        free_list(v, n);
        return ok;
    }
    FILE *in = fopen(from, "rb");
    if (!in) return 0;
    FILE *out = fopen(to, "wb");
    if (!out) { fclose(in); return 0; }
    char buf[65536];
    size_t got;
    int ok = 1;
    while ((got = fread(buf, 1, sizeof buf, in)) > 0) ok &= fwrite(buf, 1, got, out) == got;
    fclose(in);
    return (fclose(out) == 0) & ok;
}

static uint8_t *hread(const char *hpath, size_t *len) {
    FILE *f = fopen(hpath, "rb");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n < 0) { fclose(f); return NULL; }
    uint8_t *b = malloc((size_t)n + 1);
    *len = fread(b, 1, (size_t)n, f);
    b[*len] = 0;
    fclose(f);
    return b;
}

static int hwrite(const char *hpath, const void *p, size_t n) {
    FILE *f = fopen(hpath, "wb");
    if (!f) return 0;
    int ok = fwrite(p, 1, n, f) == n;
    return (fclose(f) == 0) & ok;
}

/* ---- property lists: reading (binary and XML) ------------------------------------------------------------------ */
static const char b64[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

static id utf8_string(const char *p, size_t n) {
    char *t = malloc(n + 1);
    memcpy(t, p, n);
    t[n] = 0;
    id s = rt_nsstring_new(t);
    free(t);
    return s;
}

/* a growable host vector of ids */
typedef struct { id *v; uint32_t n, cap; } idvec;
static void vec_push(idvec *a, id x) {
    if (a->n == a->cap) { a->cap = a->cap ? a->cap * 2 : 8; a->v = realloc(a->v, sizeof(id) * a->cap); }
    a->v[a->n++] = x;
}

/* binary plist (bplist00) */
typedef struct { const uint8_t *b; size_t n; int osz, rsz; uint64_t nobj, otab; int depth; } bplist;

static uint64_t be_uint(const uint8_t *p, int n) {
    uint64_t v = 0;
    for (int k = 0; k < n; k++) v = v << 8 | p[k];
    return v;
}

static id bp_object(cpu_t *c, bplist *bp, uint64_t ref);

/* the element count of an object at `off`, and where its contents start */
static int bp_count(bplist *bp, size_t off, uint64_t *count, size_t *start) {
    uint8_t lo = bp->b[off] & 15;
    if (lo != 15) { *count = lo; *start = off + 1; return 1; }
    if (off + 2 > bp->n || (bp->b[off + 1] >> 4) != 1) return 0;
    int sz = 1 << (bp->b[off + 1] & 15);
    if (off + 2 + (size_t)sz > bp->n) return 0;
    *count = be_uint(bp->b + off + 2, sz > 8 ? 8 : sz);
    *start = off + 2 + (size_t)sz;
    return 1;
}

static id bp_object(cpu_t *c, bplist *bp, uint64_t ref) {
    if (ref >= bp->nobj || bp->depth > 64) return 0;
    size_t ent = (size_t)(bp->otab + ref * (uint64_t)bp->osz);
    if (ent + (size_t)bp->osz > bp->n) return 0;
    size_t off = (size_t)be_uint(bp->b + ent, bp->osz);
    if (off >= bp->n) return 0;
    uint8_t mk = bp->b[off], hi = mk >> 4, lo = mk & 15;
    uint64_t count;
    size_t start;
    switch (hi) {
    case 0x0:
        if (mk == 8 || mk == 9) return rt_nsnumber_new_bool(mk == 9);
        return 0;
    case 0x1: {
        int sz = 1 << lo;
        if (off + 1 + (size_t)sz > bp->n) return 0;
        uint64_t v = be_uint(bp->b + off + 1 + (sz > 8 ? sz - 8 : 0), sz > 8 ? 8 : sz);
        return rt_nsnumber_new_int((int64_t)v); /* 1-4 bytes are unsigned, 8 signed, 16: the low 8 */
    }
    case 0x2: case 0x3: {
        int sz = hi == 3 ? 8 : 1 << lo;
        if (off + 1 + (size_t)sz > bp->n) return 0;
        uint64_t v = be_uint(bp->b + off + 1, sz);
        double d;
        if (sz == 4) { uint32_t u = (uint32_t)v; float f; memcpy(&f, &u, 4); d = f; }
        else memcpy(&d, &v, 8);
        return hi == 3 ? date_new(d) : rt_nsnumber_new_double(d);
    }
    case 0x4:
        if (!bp_count(bp, off, &count, &start) || start + count > bp->n) return 0;
        return rt_nsdata_new(bp->b + start, (uint32_t)count);
    case 0x5:
        if (!bp_count(bp, off, &count, &start) || start + count > bp->n) return 0;
        return utf8_string((const char *)bp->b + start, (size_t)count);
    case 0x6: {
        if (!bp_count(bp, off, &count, &start) || start + 2 * count > bp->n) return 0;
        char *t = malloc((size_t)count * 3 + 1), *o = t;
        for (uint64_t k = 0; k < count; k++) {
            uint32_t u = (uint32_t)be_uint(bp->b + start + 2 * k, 2);
            if (u >= 0xd800 && u < 0xdc00 && k + 1 < count) { /* surrogate pair */
                uint32_t l = (uint32_t)be_uint(bp->b + start + 2 * (k + 1), 2);
                if (l >= 0xdc00 && l < 0xe000) { u = 0x10000 + ((u - 0xd800) << 10) + (l - 0xdc00); k++; }
            }
            if (u < 0x80) *o++ = (char)u;
            else if (u < 0x800) { *o++ = (char)(0xc0 | u >> 6); *o++ = (char)(0x80 | (u & 63)); }
            else if (u < 0x10000) {
                *o++ = (char)(0xe0 | u >> 12); *o++ = (char)(0x80 | ((u >> 6) & 63)); *o++ = (char)(0x80 | (u & 63));
            } else {
                *o++ = (char)(0xf0 | u >> 18); *o++ = (char)(0x80 | ((u >> 12) & 63));
                *o++ = (char)(0x80 | ((u >> 6) & 63)); *o++ = (char)(0x80 | (u & 63));
            }
        }
        *o = 0;
        id s = rt_nsstring_new(t);
        free(t);
        return s;
    }
    case 0x8:
        if (off + 2 + lo > bp->n) return 0;
        return rt_nsnumber_new_int((int64_t)be_uint(bp->b + off + 1, lo + 1));
    case 0xA: {
        if (!bp_count(bp, off, &count, &start) || start + count * (uint64_t)bp->rsz > bp->n) return 0;
        idvec items = {0};
        bp->depth++;
        for (uint64_t k = 0; k < count; k++) {
            id x = bp_object(c, bp, be_uint(bp->b + start + k * (uint64_t)bp->rsz, bp->rsz));
            if (x) vec_push(&items, x);
        }
        bp->depth--;
        id a = array_take(c, items.v, items.n);
        free(items.v);
        return a;
    }
    case 0xD: {
        if (!bp_count(bp, off, &count, &start) || start + 2 * count * (uint64_t)bp->rsz > bp->n) return 0;
        id d = rt_nsdict_new();
        bp->depth++;
        for (uint64_t k = 0; k < count; k++) {
            id key = bp_object(c, bp, be_uint(bp->b + start + k * (uint64_t)bp->rsz, bp->rsz));
            id val = bp_object(c, bp, be_uint(bp->b + start + (count + k) * (uint64_t)bp->rsz, bp->rsz));
            if (key && val) rt_nsdict_set(d, key, val);
            if (key) rt_release(c, key);
            if (val) rt_release(c, val);
        }
        bp->depth--;
        return d;
    }
    default:
        return 0;
    }
}

static id parse_bplist(cpu_t *c, const uint8_t *b, size_t n) {
    if (n < 8 + 32 || memcmp(b, "bplist0", 7)) return 0;
    const uint8_t *t = b + n - 32;
    bplist bp = {b, n, t[6], t[7], be_uint(t + 8, 8), be_uint(t + 24, 8), 0};
    if (bp.osz < 1 || bp.osz > 8 || bp.rsz < 1 || bp.rsz > 8 || bp.otab >= n) return 0;
    return bp_object(c, &bp, be_uint(t + 16, 8));
}

/* XML plist */
typedef struct { const char *p, *end; int depth; } xmlp;

static void xml_skip(xmlp *x) { /* whitespace, comments, <?...?>, <!...> */
    for (;;) {
        while (x->p < x->end && (*x->p == ' ' || *x->p == '\t' || *x->p == '\r' || *x->p == '\n')) x->p++;
        if (x->p + 4 <= x->end && !strncmp(x->p, "<!--", 4)) {
            const char *e = strstr(x->p, "-->");
            x->p = e ? e + 3 : x->end;
        } else if (x->p + 2 <= x->end && (!strncmp(x->p, "<?", 2) || !strncmp(x->p, "<!", 2))) {
            const char *e = memchr(x->p, '>', (size_t)(x->end - x->p));
            x->p = e ? e + 1 : x->end;
        } else return;
    }
}

/* read a tag: name into `name`; returns 1 open, 2 close, 3 empty (<x/>), 0 none */
static int xml_tag(xmlp *x, char *name, size_t cap) {
    xml_skip(x);
    if (x->p >= x->end || *x->p != '<') return 0;
    const char *e = memchr(x->p, '>', (size_t)(x->end - x->p));
    if (!e) return 0;
    const char *q = x->p + 1;
    int kind = 1;
    if (*q == '/') kind = 2, q++;
    size_t n = 0;
    while (q < e && *q != ' ' && *q != '/' && *q != '\t' && *q != '\n' && n + 1 < cap) name[n++] = *q++;
    name[n] = 0;
    if (e[-1] == '/') kind = 3;
    x->p = e + 1;
    return kind;
}

/* text up to the next '<', with entities decoded (host malloc) */
static char *xml_text(xmlp *x) {
    const char *s = x->p;
    while (x->p < x->end && *x->p != '<') x->p++;
    size_t n = (size_t)(x->p - s);
    char *t = malloc(n + 1), *o = t;
    for (const char *q = s; q < x->p;) {
        if (*q == '&') {
            const char *semi = memchr(q, ';', (size_t)(x->p - q));
            if (semi) {
                size_t len = (size_t)(semi - q - 1);
                const char *ent = q + 1;
                uint32_t u = 0;
                if (len == 2 && !strncmp(ent, "lt", 2)) u = '<';
                else if (len == 2 && !strncmp(ent, "gt", 2)) u = '>';
                else if (len == 3 && !strncmp(ent, "amp", 3)) u = '&';
                else if (len == 4 && !strncmp(ent, "quot", 4)) u = '"';
                else if (len == 4 && !strncmp(ent, "apos", 4)) u = '\'';
                else if (len > 1 && ent[0] == '#') u = (uint32_t)strtoul(ent + 1 + (ent[1] == 'x'), NULL, ent[1] == 'x' ? 16 : 10);
                if (u) {
                    if (u < 0x80) *o++ = (char)u;
                    else if (u < 0x800) { *o++ = (char)(0xc0 | u >> 6); *o++ = (char)(0x80 | (u & 63)); }
                    else { *o++ = (char)(0xe0 | u >> 12); *o++ = (char)(0x80 | ((u >> 6) & 63)); *o++ = (char)(0x80 | (u & 63)); }
                    q = semi + 1;
                    continue;
                }
            }
        }
        *o++ = *q++;
    }
    *o = 0;
    return t;
}

static int xml_close(xmlp *x, const char *want) {
    char nm[32];
    const char *save = x->p;
    if (xml_tag(x, nm, sizeof nm) == 2 && !strcmp(nm, want)) return 1;
    x->p = save;
    return 0;
}

static uint8_t *b64_decode(const char *s, size_t *len) {
    size_t n = strlen(s);
    uint8_t *out = malloc(n / 4 * 3 + 4);
    uint32_t acc = 0;
    int bits = 0;
    size_t k = 0;
    for (; *s; s++) {
        const char *p = *s && *s != '=' ? strchr(b64, *s) : NULL;
        if (!p) continue;
        acc = acc << 6 | (uint32_t)(p - b64);
        bits += 6;
        if (bits >= 8) { bits -= 8; out[k++] = (uint8_t)(acc >> bits); }
    }
    *len = k;
    return out;
}

static double parse_iso_date(const char *s) { /* 2001-01-01T00:00:00Z */
    civil v = {2001, 1, 1, 0, 0, 0, 0, 0, 0};
    sscanf(s, "%d-%d-%dT%d:%d:%d", &v.y, &v.mo, &v.d, &v.h, &v.mi, &v.s);
    return cf_of_civil(&v, 0);
}

static id xml_value(cpu_t *c, xmlp *x);

static id xml_value_tag(cpu_t *c, xmlp *x, const char *nm, int kind) {
    if (!strcmp(nm, "true") || !strcmp(nm, "false")) {
        if (kind == 1) xml_close(x, nm);
        return rt_nsnumber_new_bool(nm[0] == 't');
    }
    if (!strcmp(nm, "dict")) {
        id d = rt_nsdict_new();
        if (kind == 3) return d;
        x->depth++;
        for (;;) {
            char k[32];
            const char *save = x->p;
            int t = xml_tag(x, k, sizeof k);
            if (t == 2 || t == 0) break;
            if (strcmp(k, "key")) { x->p = save; id junk = xml_value(c, x); if (junk) rt_release(c, junk); else break; continue; }
            char *keytext = t == 3 ? strdup("") : xml_text(x);
            if (t == 1) xml_close(x, "key");
            id key = rt_nsstring_new(keytext);
            free(keytext);
            id val = xml_value(c, x);
            if (val) { rt_nsdict_set(d, key, val); rt_release(c, val); }
            rt_release(c, key);
            if (!val) break;
        }
        x->depth--;
        return d;
    }
    if (!strcmp(nm, "array")) {
        idvec items = {0};
        if (kind == 1) {
            x->depth++;
            for (;;) {
                if (xml_close(x, "array")) break;
                id v = xml_value(c, x);
                if (!v) break;
                vec_push(&items, v);
            }
            x->depth--;
        }
        id a = array_take(c, items.v, items.n);
        free(items.v);
        return a;
    }
    char *text = kind == 3 ? strdup("") : xml_text(x);
    if (kind == 1) xml_close(x, nm);
    id r = 0;
    if (!strcmp(nm, "string") || !strcmp(nm, "key")) r = rt_nsstring_new(text);
    else if (!strcmp(nm, "integer")) r = rt_nsnumber_new_int(strtoll(text, NULL, 10));
    else if (!strcmp(nm, "real")) r = rt_nsnumber_new_double(strtod(text, NULL));
    else if (!strcmp(nm, "date")) r = date_new(parse_iso_date(text));
    else if (!strcmp(nm, "data")) {
        size_t n;
        uint8_t *b = b64_decode(text, &n);
        r = rt_nsdata_new(b, (uint32_t)n);
        free(b);
    } else r = rt_nsstring_new(text); /* unknown element: keep its text */
    free(text);
    return r;
}

static id xml_value(cpu_t *c, xmlp *x) {
    char nm[32];
    if (x->depth > 64) return 0;
    int kind = xml_tag(x, nm, sizeof nm);
    if (kind != 1 && kind != 3) return 0;
    return xml_value_tag(c, x, nm, kind);
}

static id parse_xml_plist(cpu_t *c, const char *s, size_t n) {
    xmlp x = {s, s + n, 0};
    char nm[32];
    for (;;) {
        int kind = xml_tag(&x, nm, sizeof nm);
        if (!kind) return 0;
        if (kind == 1 && !strcmp(nm, "plist")) return xml_value(c, &x);
        if (kind != 2) return xml_value_tag(c, &x, nm, kind); /* a bare value without <plist> */
    }
}

/* a property list file (host path) as a +1 object, or 0 */
static id read_plist(cpu_t *c, const char *hpath) {
    size_t n;
    uint8_t *b = hread(hpath, &n);
    if (!b) return 0;
    id r = n >= 8 && !memcmp(b, "bplist", 6) ? parse_bplist(c, b, n) : parse_xml_plist(c, (const char *)b, n);
    free(b);
    return r;
}

/* ---- property lists: writing XML ------------------------------------------------------------------------------- */
typedef struct { char *p; size_t n, cap; } sbuf;
static void sb_add(sbuf *b, const char *s, size_t n) {
    if (b->n + n + 1 > b->cap) {
        while (b->n + n + 1 > b->cap) b->cap = b->cap ? b->cap * 2 : 4096;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->n, s, n);
    b->n += n;
    b->p[b->n] = 0;
}
static void sb_str(sbuf *b, const char *s) { sb_add(b, s, strlen(s)); }
static void sb_indent(sbuf *b, int d) { for (int k = 0; k < d; k++) sb_add(b, "\t", 1); }
static void sb_escaped(sbuf *b, const char *s) {
    for (; *s; s++) {
        if (*s == '<') sb_str(b, "&lt;");
        else if (*s == '>') sb_str(b, "&gt;");
        else if (*s == '&') sb_str(b, "&amp;");
        else sb_add(b, s, 1);
    }
}

static void write_value(cpu_t *c, sbuf *b, id v, int d) {
    char t[64];
    sb_indent(b, d);
    if (!v) { sb_str(b, "<string></string>\n"); return; }
    if (rt_is_nsstring(v)) {
        sb_str(b, "<string>");
        sb_escaped(b, S(v));
        sb_str(b, "</string>\n");
    } else if (rt_is_nsnumber(v)) {
        double dv = rt_nsnumber_double(v);
        int64_t iv = rt_nsnumber_int(v);
        if ((double)iv == dv) snprintf(t, sizeof t, "<integer>%lld</integer>\n", (long long)iv);
        else snprintf(t, sizeof t, "<real>%.17g</real>\n", dv);
        sb_str(b, t);
    } else if (rt_is_kind(v, cls_date)) {
        civil cv = civil_of(date_val(v), 0);
        snprintf(t, sizeof t, "<date>%04d-%02d-%02dT%02d:%02d:%02dZ</date>\n", cv.y, cv.mo, cv.d, cv.h, cv.mi, cv.s);
        sb_str(b, t);
    } else if (rt_is_nsarray(v)) {
        uint32_t n = rt_nsarray_count(v);
        if (!n) { sb_str(b, "<array/>\n"); return; }
        sb_str(b, "<array>\n");
        for (uint32_t k = 0; k < n; k++) write_value(c, b, rt_nsarray_at(v, k), d + 1);
        sb_indent(b, d);
        sb_str(b, "</array>\n");
    } else if (rt_is_nsdict(v)) {
        uint32_t n = rt_nsdict_count(v);
        if (!n) { sb_str(b, "<dict/>\n"); return; }
        sb_str(b, "<dict>\n");
        for (uint32_t k = 0; k < n; k++) {
            id key = rt_nsdict_key_at(v, k);
            const char *ks = S(key);
            sb_indent(b, d + 1);
            sb_str(b, "<key>");
            sb_escaped(b, ks ? ks : rt_objc_describe(c, key));
            sb_str(b, "</key>\n");
            write_value(c, b, rt_nsdict_get(v, key), d + 1);
        }
        sb_indent(b, d);
        sb_str(b, "</dict>\n");
    } else if (rt_class("NSData") && rt_is_kind(v, rt_class("NSData"))) {
        const uint8_t *p = G(rt_nsdata_bytes(v));
        uint32_t n = rt_nsdata_len(v);
        sb_str(b, "<data>");
        for (uint32_t k = 0; k < n; k += 3) {
            uint32_t w = (uint32_t)p[k] << 16 | (k + 1 < n ? (uint32_t)p[k + 1] << 8 : 0) | (k + 2 < n ? p[k + 2] : 0);
            char q[4] = {b64[w >> 18], b64[(w >> 12) & 63], k + 1 < n ? b64[(w >> 6) & 63] : '=', k + 2 < n ? b64[w & 63] : '='};
            sb_add(b, q, 4);
        }
        sb_str(b, "</data>\n");
    } else {
        sb_str(b, "<string>");
        sb_escaped(b, rt_objc_describe(c, v));
        sb_str(b, "</string>\n");
    }
}

static int write_plist(cpu_t *c, const char *hpath, id root) {
    sbuf b = {0};
    sb_str(&b, "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
               "<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n"
               "<plist version=\"1.0\">\n");
    write_value(c, &b, root, 0);
    sb_str(&b, "</plist>\n");
    int ok = hwrite(hpath, b.p, b.n);
    free(b.p);
    return ok;
}

/* ---- NSBundle (the main bundle only) --------------------------------------------------------------------------- */
static id info_dict;

static id bundle_info(cpu_t *c) {
    if (!info_dict) {
        char gp[1024];
        snprintf(gp, sizeof gp, "%s/Info.plist", rt_bundle_path);
        info_dict = read_plist(c, rt_host_path(gp));
        if (!info_dict || !rt_is_nsdict(info_dict)) {
            rt_log("NSBundle: cannot read %s; using a minimal info dictionary", gp);
            info_dict = rt_nsdict_new();
            id k = rt_nsstring_new("CFBundleIdentifier"), v = rt_nsstring_new(BUNDLE_ID);
            rt_nsdict_set(info_dict, k, v);
            rt_release(c, k);
            rt_release(c, v);
        }
    }
    return info_dict;
}

static int game_exists(const char *gpath, int *is_dir) { return hstat(rt_host_path(gpath), is_dir, NULL, NULL); }

/* a resource in the bundle: <dir>/<file>, then en.lproj/<dir>/<file>; NULL if absent */
static int find_resource(const char *name, const char *type, const char *dir, char *out, size_t cap) {
    char file[512];
    if (type && *type) snprintf(file, sizeof file, "%s.%s", name, type[0] == '.' ? type + 1 : type);
    else snprintf(file, sizeof file, "%s", name);
    const char *base = rt_bundle_path;
    const char *where[] = {"", "en.lproj/", "English.lproj/"};
    for (int k = 0; k < 3; k++) {
        if (dir && *dir) snprintf(out, cap, "%s/%s%s/%s", base, where[k], dir, file);
        else snprintf(out, cap, "%s/%s%s", base, where[k], file);
        int is_dir = 0;
        if (game_exists(out, &is_dir)) return 1;
    }
    return 0;
}

M(b_main) { rt_ret(c, the_bundle); }
M(b_path) { rt_ret(c, str_auto(rt_bundle_path)); }
M(b_exec_path) {
    char p[1024];
    snprintf(p, sizeof p, "%s/NovaHD", rt_bundle_path);
    rt_ret(c, str_auto(p));
}
M(b_path_for) {
    const char *name = S(ARG(0));
    char p[1024];
    rt_ret(c, name && find_resource(name, S(ARG(1)), NULL, p, sizeof p) ? str_auto(p) : 0);
}
M(b_path_for_dir) {
    const char *name = S(ARG(0));
    char p[1024];
    rt_ret(c, name && find_resource(name, S(ARG(1)), S(ARG(2)), p, sizeof p) ? str_auto(p) : 0);
}
M(b_paths_for_type) { /* pathsForResourcesOfType:inDirectory: */
    const char *type = S(ARG(0)), *dir = S(ARG(1));
    char gdir[1024];
    if (dir && *dir) snprintf(gdir, sizeof gdir, "%s/%s", rt_bundle_path, dir);
    else snprintf(gdir, sizeof gdir, "%s", rt_bundle_path);
    int n;
    char **v = hlist(rt_host_path(gdir), &n);
    idvec items = {0};
    for (int k = 0; k < n; k++) {
        const char *dot = strrchr(v[k], '.');
        if (type && *type && !(dot && !strcmp(dot + 1, type[0] == '.' ? type + 1 : type))) continue;
        char p[1100];
        snprintf(p, sizeof p, "%s/%s", gdir, v[k]);
        vec_push(&items, rt_nsstring_new(p));
    }
    if (v) free_list(v, n);
    rt_ret(c, rt_autorelease(array_take(c, items.v, items.n)));
    free(items.v);
}
M(b_info) { rt_ret(c, bundle_info(c)); }
M(b_info_key) { rt_ret(c, ARG(0) ? rt_nsdict_get(bundle_info(c), ARG(0)) : 0); }
M(b_identifier) {
    id k = rt_nsstring_new("CFBundleIdentifier");
    id v = rt_nsdict_get(bundle_info(c), k);
    rt_release(c, k);
    rt_ret(c, v ? v : str_auto(BUNDLE_ID));
}
M(b_localizations) {
    int n;
    char **v = hlist(rt_host_path(rt_bundle_path), &n);
    idvec items = {0};
    for (int k = 0; k < n; k++) {
        size_t len = strlen(v[k]);
        if (len > 6 && !strcmp(v[k] + len - 6, ".lproj")) {
            v[k][len - 6] = 0;
            vec_push(&items, rt_nsstring_new(v[k]));
        }
    }
    if (v) free_list(v, n);
    rt_ret(c, rt_autorelease(array_take(c, items.v, items.n)));
    free(items.v);
}
M(b_preferred) { id e = rt_nsstring_new("en"); rt_ret(c, rt_autorelease(array_take(c, &e, 1))); }
M(b_dev_localization) { rt_ret(c, str_auto("English")); }
M(b_localized_string) { /* localizedStringForKey:value:table: */
    const char *v = S(ARG(1));
    rt_ret(c, v && *v ? ARG(1) : ARG(0));
}
M(b_load) { rt_ret(c, 1); }

/* a file URL for the bundle: NSURL when another module implements it, else a private class */
typedef struct { id path; } fileurl_state;
static id file_url_new(cpu_t *c, const char *path) {
    id nsurl = rt_class("NSURL");
    if (nsurl && nsurl != cls_fileurl && rt_responds(nsurl, "fileURLWithPath:")) {
        id s = rt_nsstring_new(path);
        id u = rt_send(c, nsurl, "fileURLWithPath:", 1, s);
        rt_release(c, s);
        if (u) return rt_retain(u);
    }
    id u = rt_objc_alloc(cls_fileurl);
    ((fileurl_state *)rt_objc_state(u, sizeof(fileurl_state)))->path = rt_nsstring_new(path);
    return u;
}
static id file_url_path(cpu_t *c, id u) { /* not retained */
    if (!u) return 0;
    if (rt_object_class(u) == cls_fileurl) return ((fileurl_state *)rt_objc_state(u, sizeof(fileurl_state)))->path;
    return rt_responds(u, "path") ? rt_send(c, u, "path", 0) : 0;
}
M(fu_path) { rt_ret(c, file_url_path(c, SELF)); }
M(fu_absolute) {
    char b[1100];
    const char *p = S(file_url_path(c, SELF));
    snprintf(b, sizeof b, "file://localhost%s", p ? p : "");
    rt_ret(c, str_auto(b));
}
M(fu_is_file) { rt_ret(c, 1); }
M(fu_dealloc) {
    fileurl_state *st = rt_objc_state_peek(SELF);
    if (st && st->path) rt_release(c, st->path);
    rt_objc_free(SELF);
}
M(b_bundle_url) { rt_ret(c, rt_autorelease(file_url_new(c, rt_bundle_path))); }

/* ---- NSFileManager --------------------------------------------------------------------------------------------- */
static int host_arg(cpu_t *c, int k, char *out, size_t cap) { /* method argument k as a host path */
    const char *g = S(ARG(k));
    if (!g) return 0;
    host_of(g, out, cap);
    return 1;
}

M(fm_default) { rt_ret(c, the_fileman); }
M(fm_exists) {
    char h[1024];
    rt_ret(c, host_arg(c, 0, h, sizeof h) && hstat(h, NULL, NULL, NULL));
}
M(fm_exists_dir) {
    char h[1024];
    int dir = 0, ok = host_arg(c, 0, h, sizeof h) && hstat(h, &dir, NULL, NULL);
    if (ARG(1)) set_bool_out(ARG(1), ok && dir);
    rt_ret(c, ok);
}
M(fm_create_dir) { /* createDirectoryAtPath:attributes: */
    char h[1024];
    rt_ret(c, host_arg(c, 0, h, sizeof h) && hmkdirs(h));
}
M(fm_create_dir_ex) { /* createDirectoryAtPath:withIntermediateDirectories:attributes:error: */
    char h[1024];
    int dir = 0, ok = 0;
    clear_error(ARG(3));
    if (host_arg(c, 0, h, sizeof h)) {
        if (ARG(1) & 0xff) ok = hmkdirs(h);
        else ok = !hstat(h, &dir, NULL, NULL) && hmkdir(h);
    }
    rt_ret(c, ok);
}
static int fm_remove_path(cpu_t *c) {
    char h[1024];
    return host_arg(c, 0, h, sizeof h) && hremove_tree(h);
}
/* The ...:error: forms clear *error; the older ...:handler: forms take a handler OBJECT in that word, and the
 * single-argument forms have no such word at all (r3 is garbage), so they must not write through it. */
M(fm_remove) { clear_error(ARG(1)); rt_ret(c, fm_remove_path(c)); }  /* removeItemAtPath:error: */
M(fm_remove_handler) { rt_ret(c, fm_remove_path(c)); }              /* removeFileAtPath:handler: */
static id dir_contents(cpu_t *c, const char *gpath, int recursive) {
    char h[1024];
    host_of(gpath, h, sizeof h);
    int n;
    char **v = hlist(h, &n);
    if (!v) return 0;
    idvec items = {0};
    for (int k = 0; k < n; k++) {
        vec_push(&items, rt_nsstring_new(v[k]));
        if (recursive) {
            char sub[1100];
            int dir = 0;
            snprintf(sub, sizeof sub, "%s/%s", gpath, v[k]);
            if (game_exists(sub, &dir) && dir) {
                id inner = dir_contents(c, sub, 1);
                for (uint32_t j = 0; j < rt_nsarray_count(inner); j++) {
                    char rel[1100];
                    snprintf(rel, sizeof rel, "%s/%s", v[k], S(rt_nsarray_at(inner, j)));
                    vec_push(&items, rt_nsstring_new(rel));
                }
            }
        }
    }
    free_list(v, n);
    id a = rt_autorelease(array_take(c, items.v, items.n));
    free(items.v);
    return a;
}
M(fm_contents) { /* contentsOfDirectoryAtPath:error: */
    const char *g = S(ARG(0));
    clear_error(ARG(1));
    rt_ret(c, g ? dir_contents(c, g, 0) : 0);
}
M(fm_dir_contents) { const char *g = S(ARG(0)); rt_ret(c, g ? dir_contents(c, g, 0) : 0); } /* directoryContentsAtPath: */
M(fm_subpaths_error) { /* subpathsOfDirectoryAtPath:error: */
    const char *g = S(ARG(0));
    clear_error(ARG(1));
    rt_ret(c, g ? dir_contents(c, g, 1) : 0);
}
M(fm_subpaths) { const char *g = S(ARG(0)); rt_ret(c, g ? dir_contents(c, g, 1) : 0); } /* subpathsAtPath: */
static void dict_put(cpu_t *c, id d, const char *key, id val) { /* val is +1 */
    id k = rt_nsstring_new(key);
    rt_nsdict_set(d, k, val);
    rt_release(c, k);
    rt_release(c, val);
}
static void attributes(cpu_t *c) {
    char h[1024];
    int dir = 0;
    uint64_t size = 0;
    double mt = 0;
    if (!host_arg(c, 0, h, sizeof h) || !hstat(h, &dir, &size, &mt)) { rt_ret(c, 0); return; }
    id d = rt_nsdict_new();
    dict_put(c, d, "NSFileSize", rt_nsnumber_new_int((int64_t)size));
    dict_put(c, d, "NSFileType", rt_nsstring_new(dir ? "NSFileTypeDirectory" : "NSFileTypeRegular"));
    dict_put(c, d, "NSFileModificationDate", date_new(mt));
    dict_put(c, d, "NSFileCreationDate", date_new(mt));
    dict_put(c, d, "NSFilePosixPermissions", rt_nsnumber_new_int(dir ? 0755 : 0644));
    rt_ret(c, rt_autorelease(d));
}
M(fm_attributes) { clear_error(ARG(1)); attributes(c); }  /* attributesOfItemAtPath:error: */
M(fm_file_attributes) { attributes(c); }                   /* fileAttributesAtPath:traverseLink: */
static int fm_copy_paths(cpu_t *c) {
    char a[1024], b[1024];
    return host_arg(c, 0, a, sizeof a) && host_arg(c, 1, b, sizeof b) && !hstat(b, NULL, NULL, NULL) &&
           hcopy_tree(a, b);
}
static int fm_move_paths(cpu_t *c) {
    char a[1024], b[1024];
    return host_arg(c, 0, a, sizeof a) && host_arg(c, 1, b, sizeof b) && !hstat(b, NULL, NULL, NULL) &&
           rename(a, b) == 0;
}
M(fm_copy) { clear_error(ARG(2)); rt_ret(c, fm_copy_paths(c)); } /* copyItemAtPath:toPath:error: */
M(fm_copy_handler) { rt_ret(c, fm_copy_paths(c)); }             /* copyPath:toPath:handler: */
M(fm_move) { clear_error(ARG(2)); rt_ret(c, fm_move_paths(c)); } /* moveItemAtPath:toPath:error: */
M(fm_move_handler) { rt_ret(c, fm_move_paths(c)); }             /* movePath:toPath:handler: */
M(fm_create_file) { /* createFileAtPath:contents:attributes: */
    char h[1024];
    id data = ARG(1);
    if (!host_arg(c, 0, h, sizeof h)) { rt_ret(c, 0); return; }
    rt_ret(c, data ? hwrite(h, G(rt_nsdata_bytes(data)), rt_nsdata_len(data)) : hwrite(h, "", 0));
}
M(fm_contents_at) {
    char h[1024];
    size_t n;
    uint8_t *b = host_arg(c, 0, h, sizeof h) ? hread(h, &n) : NULL;
    rt_ret(c, b ? rt_autorelease(rt_nsdata_new(b, (uint32_t)n)) : 0);
    free(b);
}
M(fm_readable) {
    char h[1024];
    rt_ret(c, host_arg(c, 0, h, sizeof h) && hstat(h, NULL, NULL, NULL));
}
M(fm_cwd) { rt_ret(c, str_auto(rt_bundle_path)); }
M(fm_chdir) { rt_ret(c, 1); }
M(fm_fsrep) { rt_ret(c, ARG(0) ? rt_send(c, ARG(0), "fileSystemRepresentation", 0) : 0); }
M(fm_string_fsrep) { /* stringWithFileSystemRepresentation:length: */
    const char *p = rt_str(ARG(0));
    rt_ret(c, p ? rt_autorelease(utf8_string(p, ARG(1))) : 0);
}

/* ---- NSUserDefaults -------------------------------------------------------------------------------------------- */
static id defaults_values, defaults_registered, defaults_global;

static void defaults_path(char *out, size_t cap) {
    char gp[1024];
    snprintf(gp, sizeof gp, "%s%s", rt_home_path, PREFS_FILE);
    host_of(gp, out, cap);
}

static void defaults_load(cpu_t *c) {
    if (defaults_values) return;
    char h[1024];
    defaults_path(h, sizeof h);
    id loaded = read_plist(c, h);
    defaults_values = rt_nsdict_new();
    if (loaded && rt_is_nsdict(loaded))
        for (uint32_t k = 0; k < rt_nsdict_count(loaded); k++) {
            id key = rt_nsdict_key_at(loaded, k);
            rt_nsdict_set(defaults_values, key, rt_nsdict_get(loaded, key));
        }
    if (loaded) rt_release(c, loaded);
    defaults_registered = rt_nsdict_new();
    defaults_global = rt_nsdict_new();
    const char *langs[] = {"en", "fr", "de", "ja", "it", "es"};
    id items[6];
    for (int k = 0; k < 6; k++) items[k] = rt_nsstring_new(langs[k]);
    dict_put(c, defaults_global, "AppleLanguages", array_take(c, items, 6));
    dict_put(c, defaults_global, "AppleLocale", rt_nsstring_new("en_US"));
    id one = rt_nsstring_new("en");
    dict_put(c, defaults_global, "NSLanguages", array_take(c, &one, 1));
}

static int defaults_save(cpu_t *c) {
    char h[1024], dir[1024];
    defaults_path(h, sizeof h);
    snprintf(dir, sizeof dir, "%s", h);
    char *slash = strrchr(dir, '/');
    if (slash) { *slash = 0; hmkdirs(dir); }
    int ok = write_plist(c, h, defaults_values);
    if (!ok) log_once("NSUserDefaults: cannot write %s", h);
    return ok;
}

static id defaults_get(cpu_t *c, id key) {
    defaults_load(c);
    if (!key) return 0;
    id v = rt_nsdict_get(defaults_values, key);
    if (!v) v = rt_nsdict_get(defaults_registered, key);
    if (!v) v = rt_nsdict_get(defaults_global, key);
    return v;
}

static void defaults_set(cpu_t *c, id key, id val) { /* val is borrowed; 0 removes */
    defaults_load(c);
    if (!key) return;
    if (val) rt_nsdict_set(defaults_values, key, val);
    else rt_send(c, defaults_values, "removeObjectForKey:", 1, key);
    defaults_save(c);
}

static double defaults_number(cpu_t *c, id key) {
    id v = defaults_get(c, key);
    if (!v) return 0;
    if (rt_is_nsnumber(v)) return rt_nsnumber_double(v);
    if (rt_is_nsstring(v)) {
        const char *s = S(v);
        if (!strcmp(s, "YES") || !strcmp(s, "true")) return 1;
        return atof(s);
    }
    return 0;
}

M(ud_standard) { defaults_load(c); rt_ret(c, the_defaults); }
M(ud_object) { id v = defaults_get(c, ARG(0)); rt_ret(c, v ? rt_autorelease(rt_retain(v)) : 0); }
M(ud_set_object) { defaults_set(c, ARG(1), ARG(0)); }
M(ud_remove) { defaults_set(c, ARG(0), 0); }
M(ud_integer) { rt_ret(c, (uint32_t)(int32_t)(int64_t)defaults_number(c, ARG(0))); }
M(ud_bool) { rt_ret(c, defaults_number(c, ARG(0)) != 0); }
M(ud_float) { rt_fret(c, (float)defaults_number(c, ARG(0))); }
M(ud_double) { rt_dret(c, defaults_number(c, ARG(0))); }
M(ud_string) {
    id v = defaults_get(c, ARG(0));
    if (v && rt_is_nsnumber(v)) {
        char b[64];
        double d = rt_nsnumber_double(v);
        if (d == (double)(int64_t)d) snprintf(b, sizeof b, "%lld", (long long)(int64_t)d);
        else snprintf(b, sizeof b, "%g", d);
        rt_ret(c, str_auto(b));
        return;
    }
    rt_ret(c, v && rt_is_nsstring(v) ? rt_autorelease(rt_retain(v)) : 0);
}
M(ud_array) { id v = defaults_get(c, ARG(0)); rt_ret(c, v && rt_is_nsarray(v) ? rt_autorelease(rt_retain(v)) : 0); }
M(ud_dict) { id v = defaults_get(c, ARG(0)); rt_ret(c, v && rt_is_nsdict(v) ? rt_autorelease(rt_retain(v)) : 0); }
M(ud_data) {
    id v = defaults_get(c, ARG(0)), nsdata = rt_class("NSData");
    rt_ret(c, v && nsdata && rt_is_kind(v, nsdata) ? rt_autorelease(rt_retain(v)) : 0);
}
M(ud_set_integer) { id n = rt_nsnumber_new_int((int32_t)ARG(0)); defaults_set(c, ARG(1), n); rt_release(c, n); }
M(ud_set_bool) { id n = rt_nsnumber_new_bool(ARG(0) & 0xff); defaults_set(c, ARG(1), n); rt_release(c, n); }
M(ud_set_float) { id n = rt_nsnumber_new_double(rt_farg(c, 2)); defaults_set(c, ARG(1), n); rt_release(c, n); }
M(ud_set_double) { id n = rt_nsnumber_new_double(rt_darg(c, 2)); defaults_set(c, ARG(2), n); rt_release(c, n); }
M(ud_register) {
    defaults_load(c);
    id d = ARG(0);
    if (!d || !rt_is_nsdict(d)) return;
    for (uint32_t k = 0; k < rt_nsdict_count(d); k++) {
        id key = rt_nsdict_key_at(d, k);
        rt_nsdict_set(defaults_registered, key, rt_nsdict_get(d, key));
    }
}
M(ud_synchronize) { defaults_load(c); rt_ret(c, defaults_save(c)); }
M(ud_representation) {
    defaults_load(c);
    id r = rt_nsdict_new();
    id layers[] = {defaults_global, defaults_registered, defaults_values};
    for (int l = 0; l < 3; l++)
        for (uint32_t k = 0; k < rt_nsdict_count(layers[l]); k++) {
            id key = rt_nsdict_key_at(layers[l], k);
            rt_nsdict_set(r, key, rt_nsdict_get(layers[l], key));
        }
    rt_ret(c, rt_autorelease(r));
}
M(ud_nop) { (void)c; }

/* ---- run loops and timers -------------------------------------------------------------------------------------- */
typedef struct runloop { id obj; id *timers; int n, cap; } runloop;
typedef struct {
    double interval, fire_at; /* fire_at in rt_now() time */
    id target, info;
    SEL sel;
    int repeats, valid;
    runloop *loop;            /* the loop it is scheduled in (which retains it) */
} timer_state;
typedef struct { id target, arg; SEL sel; double at; } perform_req;

static runloop main_loop;
static __thread runloop *tl_loop;
static perform_req *performs;
static int nperf, capperf;

static timer_state *tst(id t) { return rt_objc_state(t, sizeof(timer_state)); }

static runloop *current_loop(void) {
    if (tl_is_main) return &main_loop;
    if (!tl_loop) tl_loop = calloc(1, sizeof(runloop));
    return tl_loop;
}

static id loop_object(runloop *l) {
    lock();
    if (!l->obj) {
        unlock();
        id o = rt_objc_alloc(cls_runloop);
        *(runloop **)rt_objc_state(o, sizeof(runloop *)) = l;
        lock();
        if (!l->obj) l->obj = o;
        else { unlock(); rt_objc_free(o); lock(); }
    }
    id r = l->obj;
    unlock();
    return r;
}
static runloop *loop_of(id o) {
    runloop **p = o ? rt_objc_state_peek(o) : NULL;
    return p ? *p : current_loop();
}

static void timer_schedule(runloop *l, id t) {
    timer_state *st = tst(t);
    lock();
    if (st->valid && !st->loop) {
        if (l->n == l->cap) { l->cap = l->cap ? l->cap * 2 : 8; l->timers = realloc(l->timers, sizeof(id) * (size_t)l->cap); }
        l->timers[l->n++] = rt_retain(t);
        st->loop = l;
    }
    unlock();
}

static void timer_invalidate(cpu_t *c, id t) {
    timer_state *st = tst(t);
    lock();
    if (!st->valid) { unlock(); return; }
    st->valid = 0;
    int scheduled = 0;
    runloop *l = st->loop;
    if (l)
        for (int k = 0; k < l->n; k++)
            if (l->timers[k] == t) { memmove(l->timers + k, l->timers + k + 1, sizeof(id) * (size_t)(l->n - k - 1)); l->n--; scheduled = 1; break; }
    st->loop = NULL;
    id target = st->target, info = st->info;
    st->target = st->info = 0;
    unlock();
    if (target) rt_release(c, target);
    if (info) rt_release(c, info);
    if (scheduled) rt_release(c, t);
}

/* fire what is due in a loop (and, for the main loop, the queued performs); returns how many callouts ran and
 * stores the seconds until the next one is due in *next */
static int loop_run_once(cpu_t *c, runloop *l, double *next) {
    double now = rt_now();
    int fired = 0;
    id *due = NULL;
    int ndue = 0;
    lock();
    for (int k = 0; k < l->n; k++) {
        timer_state *st = rt_objc_state_peek(l->timers[k]);
        if (!st || !st->valid || st->fire_at > now) continue;
        if (st->repeats) {
            st->fire_at += st->interval;
            if (st->fire_at <= now) st->fire_at = now + st->interval;
        } else {
            st->fire_at = 1e300; /* not again, even from a nested run */
        }
        if (!due) due = malloc(sizeof(id) * (size_t)l->n);
        due[ndue++] = rt_retain(l->timers[k]);
    }
    /* take the due queued performs in the same critical section, so the pool decision below sees them (nperf
     * may change under another thread at any time) */
    perform_req *run = NULL;
    int nrun = 0;
    if (l == &main_loop)
        for (int k = 0; k < nperf;) {
            if (performs[k].at <= now) {
                if (!run) run = malloc(sizeof *run * (size_t)nperf);
                run[nrun++] = performs[k];
                memmove(performs + k, performs + k + 1, sizeof *performs * (size_t)(nperf - k - 1));
                nperf--;
            } else k++;
        }
    unlock();
    id pool = ndue || nrun ? pool_new(c) : 0;
    for (int k = 0; k < ndue; k++) {
        timer_state *st = tst(due[k]);
        if (st->valid) {
            callout(c, st->target, st->sel, due[k]);
            fired++;
            if (!st->repeats) timer_invalidate(c, due[k]);
        }
        rt_release(c, due[k]);
    }
    free(due);
    for (int k = 0; k < nrun; k++) {
        callout(c, run[k].target, run[k].sel, run[k].arg);
        fired++;
        rt_release(c, run[k].target);
        if (run[k].arg) rt_release(c, run[k].arg);
    }
    free(run);
    pool_drain(c, pool);
    if (next) {
        double soonest = 1e300;
        lock();
        for (int k = 0; k < l->n; k++) {
            timer_state *st = rt_objc_state_peek(l->timers[k]);
            if (st && st->valid && st->fire_at < soonest) soonest = st->fire_at;
        }
        if (l == &main_loop)
            for (int k = 0; k < nperf; k++)
                if (performs[k].at < soonest) soonest = performs[k].at;
        unlock();
        *next = soonest >= 1e300 ? 1e9 : soonest - rt_now() > 0 ? soonest - rt_now() : 0;
    }
    return fired;
}

static int loop_has_work(runloop *l) {
    lock();
    int r = l->n > 0 || (l == &main_loop && nperf > 0);
    unlock();
    return r;
}

/* run the loop until something fired or the deadline (rt_now time) passed; sleeps in short steps so timers added
 * by other threads are seen. Returns the number of callouts. */
static int loop_wait_and_run(cpu_t *c, runloop *l, double deadline) {
    for (;;) {
        double next;
        int fired = loop_run_once(c, l, &next);
        if (fired) return fired;
        double left = deadline - rt_now();
        if (left <= 0) return 0;
        double step = next < left ? next : left;
        if (step > 0.05) step = 0.05;
        if (step < 0.001) step = 0.001;
        sleep_s(step);
    }
}

double rt_runloop_run_once(cpu_t *c) {
    double next;
    loop_run_once(c, &main_loop, &next);
    return next;
}

void rt_runloop_perform_later(id target, SEL sel, id arg, double delay) {
    if (!target) return;
    rt_retain(target);
    if (arg) rt_retain(arg);
    perform_req r = {target, arg, sel, rt_now() + (delay > 0 ? delay : 0)};
    lock();
    if (nperf == capperf) {
        capperf = capperf ? capperf * 2 : 16;
        performs = realloc(performs, sizeof *performs * (size_t)capperf);
    }
    performs[nperf++] = r;
    unlock();
}

/* Not in rt.h (yet): drop queued requests for a target, for +cancelPreviousPerformRequestsWithTarget: (all
 * selectors) and ...WithTarget:selector:object: (match_sel set: only that selector and argument). Returns how many
 * were dropped. */
int rt_runloop_cancel_performs(cpu_t *c, id target, SEL sel, id arg, int match_sel);
int rt_runloop_cancel_performs(cpu_t *c, id target, SEL sel, id arg, int match_sel) {
    perform_req *gone = NULL;
    int ngone = 0;
    lock();
    for (int k = 0; k < nperf;) {
        perform_req *r = &performs[k];
        if (r->target == target && (!match_sel || (r->sel == sel && r->arg == arg))) {
            if (!gone) gone = malloc(sizeof *gone * (size_t)nperf);
            gone[ngone++] = *r;
            memmove(performs + k, performs + k + 1, sizeof *performs * (size_t)(nperf - k - 1));
            nperf--;
        } else k++;
    }
    unlock();
    for (int k = 0; k < ngone; k++) {
        rt_release(c, gone[k].target);
        if (gone[k].arg) rt_release(c, gone[k].arg);
    }
    free(gone);
    return ngone;
}

/* NSTimer */
static id timer_setup(id t, double interval, id target, SEL sel, id info, int repeats, double fire_at) {
    timer_state *st = tst(t);
    if (interval <= 0) interval = 0.0001;
    st->interval = interval;
    st->fire_at = fire_at;
    st->target = rt_retain(target);
    st->info = info ? rt_retain(info) : 0;
    st->sel = sel;
    st->repeats = repeats;
    st->valid = 1;
    return t;
}
/* (double interval in words 2-3, target, selector, userInfo, repeats) */
static id timer_from_args(cpu_t *c) {
    double iv = rt_darg(c, 2);
    return timer_setup(rt_objc_alloc(cls_timer), iv, ARG(2), ARG(3), ARG(4), ARG(5) & 0xff,
                       rt_now() + (iv > 0 ? iv : 0.0001));
}
M(t_scheduled) {
    id t = timer_from_args(c);
    timer_schedule(current_loop(), t);
    rt_ret(c, rt_autorelease(t));
}
M(t_timer) { rt_ret(c, rt_autorelease(timer_from_args(c))); }
M(t_init_fire_date) { /* initWithFireDate:interval:target:selector:userInfo:repeats: (interval in words 3-4) */
    double iv = rt_darg(c, 3);
    double at = ARG(0) ? mono_from_cf(date_val(ARG(0))) : rt_now() + iv;
    timer_setup(SELF, iv, ARG(3), ARG(4), ARG(5), ARG(6) & 0xff, at);
}
M(t_invalidate) { timer_invalidate(c, SELF); }
M(t_is_valid) { rt_ret(c, tst(SELF)->valid); }
M(t_fire) {
    timer_state *st = tst(SELF);
    if (!st->valid) return;
    rt_retain(SELF);
    callout(c, st->target, st->sel, SELF);
    if (!st->repeats) timer_invalidate(c, SELF);
    rt_release(c, SELF);
}
M(t_user_info) { rt_ret(c, tst(SELF)->info); }
M(t_fire_date) { timer_state *st = tst(SELF); rt_ret(c, date_auto(cf_now() + (st->fire_at - rt_now()))); }
M(t_set_fire_date) { tst(SELF)->fire_at = mono_from_cf(date_val(ARG(0))); }
M(t_interval) { timer_state *st = tst(SELF); rt_dret(c, st->repeats ? st->interval : 0); }
M(t_dealloc) {
    timer_state *st = rt_objc_state_peek(SELF);
    if (st) {
        if (st->target) rt_release(c, st->target);
        if (st->info) rt_release(c, st->info);
    }
    rt_objc_free(SELF);
}

/* NSRunLoop */
M(rl_current) { rt_ret(c, loop_object(current_loop())); }
M(rl_main) { rt_ret(c, loop_object(&main_loop)); }
M(rl_add_timer) { if (ARG(0)) timer_schedule(loop_of(SELF), ARG(0)); }
M(rl_run) {
    runloop *l = loop_of(SELF);
    if (l != current_loop()) { log_once("NSRunLoop: -run on another thread's run loop"); return; }
    if (l == &main_loop) { loop_run_once(c, l, NULL); log_once("NSRunLoop: -run on the main thread runs one pass"); return; }
    while (loop_has_work(l)) loop_wait_and_run(c, l, rt_now() + 3600);
    sleep_s(0.01); /* nothing scheduled: return (as Cocoa does) without letting a caller's loop spin hot */
}
M(rl_run_until) {
    runloop *l = loop_of(SELF);
    double deadline = mono_from_cf(date_val(ARG(0)));
    if (!loop_has_work(l)) { /* Cocoa returns at once; a short nap keeps polling loops cool */
        double left = deadline - rt_now();
        sleep_s(left < 0.01 ? left : 0.01);
        return;
    }
    while (rt_now() < deadline && loop_has_work(l)) loop_wait_and_run(c, l, deadline);
}
M(rl_run_mode) { /* runMode:beforeDate: */
    runloop *l = loop_of(SELF);
    if (!loop_has_work(l)) {
        double left = mono_from_cf(date_val(ARG(1))) - rt_now();
        sleep_s(left < 0.01 ? left : 0.01);
        rt_ret(c, 0);
        return;
    }
    loop_wait_and_run(c, l, mono_from_cf(date_val(ARG(1))));
    rt_ret(c, 1);
}
M(rl_mode) { rt_ret(c, str_auto("kCFRunLoopDefaultMode")); }
M(rl_dealloc) { (void)c; } /* run loops live as long as their thread (forever) */

/* ---- NSThread -------------------------------------------------------------------------------------------------- */
typedef struct {
    id target, arg, name, dict;
    SEL sel;
    int is_main, started, finished, cancelled;
    double priority;
    jmp_buf *exit_jmp;
} thread_state;
static __thread id tl_thread;

static thread_state *ths(id t) { return rt_objc_state(t, sizeof(thread_state)); }

static id thread_current(void) {
    if (!tl_thread) {
        if (tl_is_main && main_thread_obj) tl_thread = main_thread_obj;
        else {
            tl_thread = rt_objc_alloc(cls_thread);
            ths(tl_thread)->priority = 0.5;
            ths(tl_thread)->started = 1;
        }
    }
    return tl_thread;
}

#ifdef _WIN32
static DWORD WINAPI thread_entry(void *p)
#else
static void *thread_entry(void *p)
#endif
{
    id th = (id)(uintptr_t)p;
    cpu_t *c = rt_thread_cpu();
    tl_thread = th;
    thread_state *st = ths(th);
    jmp_buf jb;
    st->exit_jmp = &jb;
    id pool = pool_new(c);
    if (!setjmp(jb)) callout(c, st->target, st->sel, st->arg);
    pool_drain(c, pool);
    id target = st->target, arg = st->arg;
    st->target = st->arg = 0;
    st->exit_jmp = NULL;
    st->finished = 1;
    if (target) rt_release(c, target);
    if (arg) rt_release(c, arg);
    rt_release(c, th); /* the running thread's reference */
    return 0;
}

static int thread_start(id th) {
    thread_state *st = ths(th);
    if (st->started) return 1;
    st->started = 1;
    rt_retain(th);
    if (rt_verbose) rt_log("NSThread: starting -[%s %s]", rt_class_name(rt_object_class(st->target)), rt_sel_name(st->sel));
#ifdef _WIN32
    HANDLE h = CreateThread(NULL, 16u << 20, thread_entry, (void *)(uintptr_t)th, STACK_SIZE_PARAM_IS_A_RESERVATION, NULL);
    if (!h) { rt_log("NSThread: CreateThread failed"); st->started = 0; rt_release(rt_thread_cpu(), th); return 0; }
    CloseHandle(h);
#else
    pthread_t h;
    pthread_attr_t at;
    pthread_attr_init(&at);
    pthread_attr_setstacksize(&at, 16u << 20);
    pthread_attr_setdetachstate(&at, PTHREAD_CREATE_DETACHED);
    int e = pthread_create(&h, &at, thread_entry, (void *)(uintptr_t)th);
    pthread_attr_destroy(&at);
    if (e) { rt_log("NSThread: pthread_create failed (%d)", e); st->started = 0; rt_release(rt_thread_cpu(), th); return 0; }
#endif
    return 1;
}

static void thread_setup(id th, id target, SEL sel, id arg) {
    thread_state *st = ths(th);
    st->target = rt_retain(target);
    st->arg = arg ? rt_retain(arg) : 0;
    st->sel = sel;
    st->priority = 0.5;
}

M(th_detach) { /* +detachNewThreadSelector:toTarget:withObject: */
    if (!ARG(1)) return;
    id th = rt_objc_alloc(cls_thread);
    thread_setup(th, ARG(1), ARG(0), ARG(2));
    thread_start(th);
    rt_release(c, th); /* a running thread keeps its own reference */
}
M(th_init_target) { thread_setup(SELF, ARG(0), ARG(1), ARG(2)); } /* initWithTarget:selector:object: */
M(th_start) { if (ths(SELF)->target) thread_start(SELF); }
M(th_current) { rt_ret(c, thread_current()); }
M(th_main) { rt_ret(c, main_thread_obj); }
M(th_is_main_class) { rt_ret(c, tl_is_main); }
M(th_is_main) { rt_ret(c, ths(SELF)->is_main); }
M(th_multi) { rt_ret(c, 1); }
M(th_sleep) { sleep_s(rt_darg(c, 2)); }
M(th_sleep_until) { sleep_s(date_val(ARG(0)) - cf_now()); }
M(th_set_priority_class) { ths(thread_current())->priority = rt_darg(c, 2); rt_ret(c, 1); }
M(th_priority_class) { rt_dret(c, ths(thread_current())->priority); }
M(th_set_priority) { ths(SELF)->priority = rt_darg(c, 2); }
M(th_priority) { rt_dret(c, ths(SELF)->priority); }
M(th_exit) {
    thread_state *st = ths(thread_current());
    if (!st->exit_jmp) { rt_log("NSThread: +exit outside a detached thread (ignored)"); return; }
    longjmp(*st->exit_jmp, 1); /* only host C frames and translated code lie in between */
}
M(th_name) { rt_ret(c, ths(SELF)->name); }
M(th_set_name) {
    thread_state *st = ths(SELF);
    id old = st->name;
    st->name = ARG(0) ? rt_retain(ARG(0)) : 0;
    if (old) rt_release(c, old);
}
M(th_dict) {
    thread_state *st = ths(SELF);
    if (!st->dict) st->dict = rt_nsdict_new();
    rt_ret(c, st->dict);
}
M(th_cancel) { ths(SELF)->cancelled = 1; }
M(th_is_cancelled) { rt_ret(c, ths(SELF)->cancelled); }
M(th_is_executing) { thread_state *st = ths(SELF); rt_ret(c, st->started && !st->finished); }
M(th_is_finished) { rt_ret(c, ths(SELF)->finished); }
M(th_dealloc) {
    thread_state *st = rt_objc_state_peek(SELF);
    if (st && st->is_main) return;
    if (st) {
        if (st->target) rt_release(c, st->target);
        if (st->arg) rt_release(c, st->arg);
        if (st->name) rt_release(c, st->name);
        if (st->dict) rt_release(c, st->dict);
    }
    rt_objc_free(SELF);
}

/* ---- NSNotification, NSNotificationCenter ---------------------------------------------------------------------- */
typedef struct { id name, object, info; } note_state;
typedef struct { id observer; SEL sel; char *name; id object; uint32_t serial; } observer_t;
static observer_t *observers;
static int nobs, capobs;
static uint32_t obs_serial;

static note_state *nst(id n) { return rt_objc_state(n, sizeof(note_state)); }

static id note_new(id name, id object, id info) {
    id n = rt_objc_alloc(cls_note);
    note_state *st = nst(n);
    st->name = name ? rt_retain(name) : 0;
    st->object = object ? rt_retain(object) : 0;
    st->info = info ? rt_retain(info) : 0;
    return n;
}

M(n_with_name) { rt_ret(c, rt_autorelease(note_new(ARG(0), ARG(1), 0))); }
M(n_with_name_info) { rt_ret(c, rt_autorelease(note_new(ARG(0), ARG(1), ARG(2)))); }
M(n_init) { /* initWithName:object:userInfo: */
    note_state *st = nst(SELF);
    st->name = ARG(0) ? rt_retain(ARG(0)) : 0;
    st->object = ARG(1) ? rt_retain(ARG(1)) : 0;
    st->info = ARG(2) ? rt_retain(ARG(2)) : 0;
}
M(n_name) { rt_ret(c, nst(SELF)->name); }
M(n_object) { rt_ret(c, nst(SELF)->object); }
M(n_user_info) { rt_ret(c, nst(SELF)->info); }
M(n_description) {
    char b[300];
    const char *nm = S(nst(SELF)->name);
    snprintf(b, sizeof b, "NSConcreteNotification %#x {name = %s}", SELF, nm ? nm : "(null)");
    rt_ret(c, str_auto(b));
}
M(n_dealloc) {
    note_state *st = rt_objc_state_peek(SELF);
    if (st) {
        if (st->name) rt_release(c, st->name);
        if (st->object) rt_release(c, st->object);
        if (st->info) rt_release(c, st->info);
    }
    rt_objc_free(SELF);
}

static void post(cpu_t *c, id note) {
    note_state *st = nst(note);
    const char *name = S(st->name);
    observer_t *hit = NULL;
    int nhit = 0;
    lock();
    for (int k = 0; k < nobs; k++) {
        observer_t *o = &observers[k];
        if (o->name && (!name || strcmp(o->name, name))) continue;
        if (o->object && o->object != st->object) continue;
        if (!hit) hit = malloc(sizeof *hit * (size_t)nobs);
        hit[nhit++] = *o;
    }
    unlock();
    if (rt_verbose > 1) rt_log("NSNotificationCenter: %s -> %d observer(s)", name ? name : "(nil)", nhit);
    for (int k = 0; k < nhit; k++) {
        int still = 0;
        lock();
        for (int j = 0; j < nobs && !still; j++) still = observers[j].serial == hit[k].serial;
        unlock();
        if (still) callout(c, hit[k].observer, hit[k].sel, note);
    }
    free(hit);
}

void rt_notify(cpu_t *c, const char *name, id object, id user_info) {
    if (!name) return;
    id nm = rt_nsstring_new(name);
    id note = note_new(nm, object, user_info);
    post(c, note);
    rt_release(c, note);
    rt_release(c, nm);
}

M(nc_default) { rt_ret(c, the_center); }
M(nc_add) { /* addObserver:selector:name:object: */
    if (!ARG(0) || !ARG(1)) return;
    const char *name = S(ARG(2));
    lock();
    if (nobs == capobs) { capobs = capobs ? capobs * 2 : 32; observers = realloc(observers, sizeof *observers * (size_t)capobs); }
    observers[nobs++] = (observer_t){ARG(0), ARG(1), name ? strdup(name) : NULL, ARG(3), ++obs_serial};
    unlock();
}
static void remove_observers(id observer, const char *name, id object, int filter) {
    lock();
    for (int k = 0; k < nobs;) {
        observer_t *o = &observers[k];
        int match = o->observer == observer;
        if (filter && match && name && !(o->name && !strcmp(o->name, name))) match = 0;
        if (filter && match && object && o->object != object) match = 0;
        if (match) {
            free(o->name);
            memmove(observers + k, observers + k + 1, sizeof *observers * (size_t)(nobs - k - 1));
            nobs--;
        } else k++;
    }
    unlock();
}
M(nc_remove) { remove_observers(ARG(0), NULL, 0, 0); }
M(nc_remove_named) { remove_observers(ARG(0), S(ARG(1)), ARG(2), 1); }
M(nc_post) { if (ARG(0)) post(c, ARG(0)); }
static void post_named(cpu_t *c, id name, id object, id info) {
    id note = note_new(name, object, info);
    post(c, note);
    rt_release(c, note);
}
M(nc_post_name) { post_named(c, ARG(0), ARG(1), 0); }
M(nc_post_name_info) { post_named(c, ARG(0), ARG(1), ARG(2)); }

/* ---- NSAssertionHandler ---------------------------------------------------------------------------------------- */
static void assertion(cpu_t *c, const char *where, id file, uint32_t line, id desc, int first_arg) {
    char msg[1024];
    const char *f = S(desc);
    if (f) {
        rt_args a = {c, first_arg, 0};
        rt_vformat(msg, sizeof msg, f, &a);
    } else snprintf(msg, sizeof msg, "(no description)");
    const char *fs = S(file);
    rt_log("NSAssertionHandler: *** Assertion failure in %s, %s:%u: %s (continuing)", where, fs ? fs : "?", line, msg);
}
M(as_current) { rt_ret(c, the_assert); }
M(as_method) { /* handleFailureInMethod:object:file:lineNumber:description:, varargs from word 7 */
    char where[300];
    id obj = ARG(1);
    snprintf(where, sizeof where, "-[%s %s]", obj ? rt_class_name(rt_object_class(obj)) : "nil", ARG(0) && rt_sel_name(ARG(0)) ? rt_sel_name(ARG(0)) : "?");
    assertion(c, where, ARG(2), ARG(3), ARG(4), 7);
}
M(as_function) { /* handleFailureInFunction:file:lineNumber:description:, varargs from word 6 */
    const char *fn = S(ARG(0));
    assertion(c, fn ? fn : "?", ARG(1), ARG(2), ARG(3), 6);
}

/* ---- the private CFArray (CFArrayCreateMutable) ---------------------------------------------------------------- */
typedef struct { uint32_t *v; uint32_t n, cap; int retains; } cfarray_state;
static cfarray_state *cfa(id a) { return rt_objc_state(a, sizeof(cfarray_state)); }
static int is_cfarray(id a) { return a && rt_object_class(a) == cls_cfarray; }

static void cfa_append(id a, uint32_t v) {
    cfarray_state *st = cfa(a);
    if (st->n == st->cap) { st->cap = st->cap ? st->cap * 2 : 8; st->v = realloc(st->v, 4 * st->cap); }
    st->v[st->n++] = st->retains && v ? rt_retain(v) : v;
}
static void cfa_clear(cpu_t *c, id a) {
    cfarray_state *st = cfa(a);
    uint32_t n = st->n, *v = st->v;
    st->v = NULL;
    st->n = st->cap = 0;
    if (st->retains)
        for (uint32_t k = 0; k < n; k++) if (v[k]) rt_release(c, v[k]);
    free(v);
}
M(ca_count) { rt_ret(c, cfa(SELF)->n); }
M(ca_at) { cfarray_state *st = cfa(SELF); rt_ret(c, ARG(0) < st->n ? st->v[ARG(0)] : 0); }
M(ca_add) { cfa_append(SELF, ARG(0)); }
M(ca_clear) { cfa_clear(c, SELF); }
M(ca_dealloc) { cfa_clear(c, SELF); rt_objc_free(SELF); }

/* ---- C imports ------------------------------------------------------------------------------------------------- */
#define A(k) rt_arg(c, k)
#define RET(v) rt_ret(c, (uint32_t)(v))

IMP(NSSearchPathForDirectoriesInDomains) {
    const char *sub;
    switch (A(0)) {
    case 9: sub = "/Documents"; break;
    case 5: sub = "/Library"; break;
    case 13: sub = "/Library/Caches"; break;
    case 14: sub = "/Library/Application Support"; break;
    case 1: sub = "/Applications"; break;
    case 12: sub = "/Desktop"; break;
    case 15: sub = "/Downloads"; break;
    default:
        log_once("NSSearchPathForDirectoriesInDomains: directory %u (empty array)", A(0));
        RET(rt_autorelease(rt_nsarray_new(NULL, 0)));
        return;
    }
    char gp[1024], h[1024];
    snprintf(gp, sizeof gp, "%s%s", rt_home_path, sub);
    host_of(gp, h, sizeof h);
    hmkdirs(h);
    id s = rt_nsstring_new(gp);
    RET(rt_autorelease(array_take(c, &s, 1)));
}
IMP(NSHomeDirectory) { RET(str_auto(rt_home_path)); }
IMP(NSTemporaryDirectory) {
    char gp[1024], h[1024];
    snprintf(gp, sizeof gp, "%s/tmp/", rt_home_path);
    host_of(gp, h, sizeof h);
    hmkdirs(h);
    RET(str_auto(gp));
}

IMP(CFBundleGetMainBundle) { RET(the_bundle); }
IMP(CFBundleCopyBundleURL) { RET(A(0) ? file_url_new(c, rt_bundle_path) : 0); }
IMP(CFBundleCopyResourcesDirectoryURL) { RET(A(0) ? file_url_new(c, rt_bundle_path) : 0); }
IMP(CFURLCopyFileSystemPath) { id p = file_url_path(c, A(0)); RET(p ? rt_retain(p) : 0); }
IMP(CFStringGetCString) { /* (string, buffer, size, encoding) */
    const char *s = S(A(0));
    uint32_t dst = A(1), cap = A(2);
    if (!s || !dst || !cap) { RET(0); return; }
    size_t n = strlen(s);
    if (n + 1 > cap) { RET(0); return; }
    memcpy(rt_mem + dst, s, n + 1);
    RET(1);
}
IMP(CFStringGetLength) { RET(rt_nsstring_len(A(0))); }
IMP(CFRelease) { if (A(0)) rt_release(c, A(0)); }
IMP(CFRetain) { RET(rt_retain(A(0))); }

IMP(CFArrayCreateMutable) { /* (allocator, capacity, callbacks): NULL callbacks keep raw, unretained values */
    id a = rt_objc_alloc(cls_cfarray);
    cfa(a)->retains = A(2) != 0;
    RET(a);
}
IMP(CFArrayAppendValue) {
    id a = A(0);
    if (is_cfarray(a)) cfa_append(a, A(1));
    else if (a) rt_send(c, a, "addObject:", 1, A(1));
}
IMP(CFArrayGetCount) { id a = A(0); RET(is_cfarray(a) ? cfa(a)->n : rt_nsarray_count(a)); }
IMP(CFArrayGetValueAtIndex) {
    id a = A(0);
    uint32_t k = A(1);
    if (is_cfarray(a)) { cfarray_state *st = cfa(a); RET(k < st->n ? st->v[k] : 0); }
    else RET(rt_nsarray_at(a, k));
}
IMP(CFArrayRemoveAllValues) {
    id a = A(0);
    if (is_cfarray(a)) cfa_clear(c, a);
    else if (a) rt_send(c, a, "removeAllObjects", 0);
}
IMP(CFDictionaryGetValue) {
    id d = A(0);
    if (!d) { RET(0); return; }
    RET(rt_is_nsdict(d) ? rt_nsdict_get(d, A(1)) : rt_send(c, d, "objectForKey:", 1, A(1)));
}
IMP(CFNumberGetValue) { /* (number, CFNumberType, valuePtr) */
    id n = A(0);
    uint32_t p = A(2);
    if (!n || !p || !rt_is_nsnumber(n)) { RET(0); return; }
    int64_t i = rt_nsnumber_int(n);
    double d = rt_nsnumber_double(n);
    switch (A(1)) {
    case 1: case 7: rt_mem[p] = (uint8_t)i; break;                                 /* SInt8, char */
    case 2: case 8: { uint16_t v = (uint16_t)i; memcpy(rt_mem + p, &v, 2); break; } /* SInt16, short */
    case 3: case 9: case 10: case 14: case 15: rt_st32(p, (uint32_t)i); break;        /* 32-bit ints, CFIndex */
    case 4: case 11: memcpy(rt_mem + p, &i, 8); break;                               /* SInt64, long long */
    case 5: case 12: case 16: { float f = (float)d; memcpy(rt_mem + p, &f, 4); break; } /* Float32, float, CGFloat */
    case 6: case 13: memcpy(rt_mem + p, &d, 8); break;                               /* Float64, double */
    default: RET(0); return;
    }
    RET(1);
}
IMP(CFRunLoopRunInMode) { /* (mode, double seconds in words 1-2, returnAfterSourceHandled) */
    double secs = rt_darg(c, 1);
    runloop *l = current_loop();
    int fired = secs > 0 ? loop_wait_and_run(c, l, rt_now() + secs) : loop_run_once(c, l, NULL);
    RET(fired && (A(3) & 0xff) ? 4 : 3); /* kCFRunLoopRunHandledSource : kCFRunLoopRunTimedOut */
}
IMP(CFRunLoopGetCurrent) { RET(loop_object(current_loop())); }
IMP(CFRunLoopGetMain) { RET(loop_object(&main_loop)); }
M(rl_get_cf) { (void)c; } /* -getCFRunLoop: the CFRunLoop is the NSRunLoop */

/* ---- data imports ---------------------------------------------------------------------------------------------- */
static uint32_t data_word(uint32_t value) {
    uint32_t w = rt_calloc(1, 4);
    rt_st32(w, value);
    return w;
}

static uint32_t resolve(const char *name) {
    static const struct { const char *name, *value; } strings[] = {
        {"kCFRunLoopDefaultMode", "kCFRunLoopDefaultMode"}, {"kCFRunLoopCommonModes", "kCFRunLoopCommonModes"},
        {"NSDefaultRunLoopMode", "kCFRunLoopDefaultMode"}, {"NSRunLoopCommonModes", "kCFRunLoopCommonModes"},
        {"NSLocaleCountryCode", "kCFLocaleCountryCodeKey"}, {"NSLocaleLanguageCode", "kCFLocaleLanguageCodeKey"},
        {"NSLocaleIdentifier", "kCFLocaleIdentifierKey"}, {"NSLocaleCurrencyCode", "kCFLocaleCurrencyCodeKey"},
        {"NSLocaleCurrencySymbol", "kCFLocaleCurrencySymbolKey"},
        {"NSLocaleDecimalSeparator", "kCFLocaleDecimalSeparatorKey"},
        {"NSLocaleGroupingSeparator", "kCFLocaleGroupingSeparatorKey"},
        {"NSLocaleUsesMetricSystem", "kCFLocaleUsesMetricSystemKey"},
        {"NSLocaleMeasurementSystem", "kCFLocaleMeasurementSystemKey"},
        {"NSFileSize", "NSFileSize"}, {"NSFileType", "NSFileType"},
        {"NSFileModificationDate", "NSFileModificationDate"}, {"NSFileCreationDate", "NSFileCreationDate"},
        {"NSFileTypeDirectory", "NSFileTypeDirectory"}, {"NSFileTypeRegular", "NSFileTypeRegular"},
        {"NSFilePosixPermissions", "NSFilePosixPermissions"},
        {"NSCurrentLocaleDidChangeNotification", "kCFLocaleCurrentLocaleDidChangeNotification"},
        {"NSThreadWillExitNotification", "NSThreadWillExitNotification"},
        {"NSWillBecomeMultiThreadedNotification", "NSWillBecomeMultiThreadedNotification"},
        {"NSUserDefaultsDidChangeNotification", "NSUserDefaultsDidChangeNotification"},
    };
    for (size_t k = 0; k < sizeof strings / sizeof *strings; k++)
        if (!strcmp(name, strings[k].name)) return data_word(rt_nsstring_new(strings[k].value));
    if (!strcmp(name, "kCFAllocatorDefault") || !strcmp(name, "kCFAllocatorSystemDefault") ||
        !strcmp(name, "kCFAllocatorMalloc"))
        return data_word(0); /* NULL is the default allocator */
    if (!strcmp(name, "kCFTypeArrayCallBacks") || !strcmp(name, "kCFTypeDictionaryKeyCallBacks") ||
        !strcmp(name, "kCFTypeDictionaryValueCallBacks"))
        return rt_calloc(1, 24); /* only compared against NULL here: non-NULL means "retain the values" */
    return 0;
}

/* ---- definitions ----------------------------------------------------------------------------------------------- */
typedef struct { const char *sel; rt_hostfn fn; } mdef;
static void methods(id cls, const mdef *v, size_t n, int class_side) {
    for (size_t k = 0; k < n; k++) (class_side ? rt_objc_cmethod : rt_objc_method)(cls, v[k].sel, v[k].fn);
}
#define METHODS(cls, side, ...) do { static const mdef v_[] = {__VA_ARGS__}; methods(cls, v_, sizeof v_ / sizeof *v_, side); } while (0)

void rt_system_define(void) {
    tl_is_main = 1;
    tl_loop = &main_loop;

    cls_date = rt_objc_define("NSDate", "NSObject", 8);
    METHODS(cls_date, 1, {"date", d_date}, {"dateWithTimeIntervalSinceNow:", d_since_now},
            {"dateWithTimeIntervalSince1970:", d_since_1970}, {"dateWithTimeIntervalSinceReferenceDate:", d_since_ref},
            {"distantFuture", d_future}, {"distantPast", d_past}, {"timeIntervalSinceReferenceDate", d_class_ref_now});
    METHODS(cls_date, 0, {"init", d_init}, {"initWithTimeIntervalSinceNow:", d_init_since_now},
            {"initWithTimeIntervalSinceReferenceDate:", d_init_since_ref},
            {"initWithTimeIntervalSince1970:", d_init_since_1970}, {"initWithTimeInterval:sinceDate:", d_init_since_date},
            {"timeIntervalSinceReferenceDate", d_ref}, {"timeIntervalSince1970", d_1970}, {"timeIntervalSinceNow", d_now},
            {"timeIntervalSinceDate:", d_since_date}, {"dateByAddingTimeInterval:", d_adding},
            {"addTimeInterval:", d_adding}, {"compare:", d_compare}, {"isEqualToDate:", d_equal}, {"isEqual:", d_equal},
            {"earlierDate:", d_earlier}, {"laterDate:", d_later}, {"hash", d_hash}, {"copy", d_copy},
            {"copyWithZone:", d_copy}, {"description", d_description});

    cls_datefmt = rt_objc_define("NSDateFormatter", "NSObject", 0);
    METHODS(cls_datefmt, 0, {"init", df_init}, {"setDateFormat:", df_set_format}, {"dateFormat", df_format},
            {"setDateStyle:", df_set_date_style}, {"setTimeStyle:", df_set_time_style}, {"setLocale:", df_ignore},
            {"setTimeZone:", df_ignore}, {"setFormatterBehavior:", df_ignore}, {"setLenient:", df_ignore},
            {"stringFromDate:", df_string_from_date}, {"dateFromString:", df_date_from_string});

    cls_locale = rt_objc_define("NSLocale", "NSObject", 0);
    the_locale = rt_objc_alloc(cls_locale);
    METHODS(cls_locale, 1, {"currentLocale", loc_current}, {"systemLocale", loc_current},
            {"autoupdatingCurrentLocale", loc_current}, {"preferredLanguages", loc_preferred},
            {"availableLocaleIdentifiers", loc_available});
    METHODS(cls_locale, 0, {"objectForKey:", loc_object}, {"localeIdentifier", loc_ident},
            {"initWithLocaleIdentifier:", loc_init_ident}, {"displayNameForKey:value:", loc_display_name},
            {"dealloc", singleton_dealloc});

    cls_fileurl = rt_objc_define("_RTFileURL", "NSObject", 0);
    METHODS(cls_fileurl, 0, {"path", fu_path}, {"relativePath", fu_path}, {"absoluteString", fu_absolute},
            {"description", fu_absolute}, {"isFileURL", fu_is_file}, {"dealloc", fu_dealloc});

    cls_bundle = rt_objc_define("NSBundle", "NSObject", 0);
    the_bundle = rt_objc_alloc(cls_bundle);
    METHODS(cls_bundle, 1, {"mainBundle", b_main}, {"bundleForClass:", b_main}, {"bundleWithPath:", b_main},
            {"bundleWithIdentifier:", b_main});
    METHODS(cls_bundle, 0, {"bundlePath", b_path}, {"resourcePath", b_path}, {"executablePath", b_exec_path},
            {"pathForResource:ofType:", b_path_for}, {"pathForResource:ofType:inDirectory:", b_path_for_dir},
            {"pathsForResourcesOfType:inDirectory:", b_paths_for_type}, {"infoDictionary", b_info},
            {"localizedInfoDictionary", b_info}, {"objectForInfoDictionaryKey:", b_info_key},
            {"bundleIdentifier", b_identifier}, {"localizations", b_localizations},
            {"preferredLocalizations", b_preferred}, {"developmentLocalization", b_dev_localization},
            {"localizedStringForKey:value:table:", b_localized_string}, {"load", b_load}, {"isLoaded", b_load},
            {"bundleURL", b_bundle_url}, {"dealloc", singleton_dealloc});

    cls_fileman = rt_objc_define("NSFileManager", "NSObject", 0);
    the_fileman = rt_objc_alloc(cls_fileman);
    METHODS(cls_fileman, 1, {"defaultManager", fm_default});
    METHODS(cls_fileman, 0, {"fileExistsAtPath:", fm_exists}, {"fileExistsAtPath:isDirectory:", fm_exists_dir},
            {"isReadableFileAtPath:", fm_readable}, {"isWritableFileAtPath:", fm_readable},
            {"isDeletableFileAtPath:", fm_readable}, {"isExecutableFileAtPath:", fm_readable},
            {"createDirectoryAtPath:attributes:", fm_create_dir},
            {"createDirectoryAtPath:withIntermediateDirectories:attributes:error:", fm_create_dir_ex},
            {"removeItemAtPath:error:", fm_remove}, {"removeFileAtPath:handler:", fm_remove_handler},
            {"contentsOfDirectoryAtPath:error:", fm_contents}, {"directoryContentsAtPath:", fm_dir_contents},
            {"subpathsAtPath:", fm_subpaths}, {"subpathsOfDirectoryAtPath:error:", fm_subpaths_error},
            {"attributesOfItemAtPath:error:", fm_attributes}, {"fileAttributesAtPath:traverseLink:", fm_file_attributes},
            {"copyItemAtPath:toPath:error:", fm_copy}, {"copyPath:toPath:handler:", fm_copy_handler},
            {"moveItemAtPath:toPath:error:", fm_move}, {"movePath:toPath:handler:", fm_move_handler},
            {"createFileAtPath:contents:attributes:", fm_create_file}, {"contentsAtPath:", fm_contents_at},
            {"currentDirectoryPath", fm_cwd}, {"changeCurrentDirectoryPath:", fm_chdir},
            {"fileSystemRepresentationWithPath:", fm_fsrep},
            {"stringWithFileSystemRepresentation:length:", fm_string_fsrep}, {"dealloc", singleton_dealloc});

    cls_defaults = rt_objc_define("NSUserDefaults", "NSObject", 0);
    the_defaults = rt_objc_alloc(cls_defaults);
    METHODS(cls_defaults, 1, {"standardUserDefaults", ud_standard}, {"resetStandardUserDefaults", ud_nop});
    METHODS(cls_defaults, 0, {"init", ret_self}, {"objectForKey:", ud_object}, {"valueForKey:", ud_object},
            {"setObject:forKey:", ud_set_object}, {"setValue:forKey:", ud_set_object},
            {"removeObjectForKey:", ud_remove}, {"integerForKey:", ud_integer}, {"boolForKey:", ud_bool},
            {"floatForKey:", ud_float}, {"doubleForKey:", ud_double}, {"stringForKey:", ud_string},
            {"arrayForKey:", ud_array}, {"stringArrayForKey:", ud_array}, {"dictionaryForKey:", ud_dict},
            {"dataForKey:", ud_data}, {"setInteger:forKey:", ud_set_integer}, {"setBool:forKey:", ud_set_bool},
            {"setFloat:forKey:", ud_set_float}, {"setDouble:forKey:", ud_set_double},
            {"registerDefaults:", ud_register}, {"synchronize", ud_synchronize},
            {"dictionaryRepresentation", ud_representation}, {"dealloc", singleton_dealloc});

    cls_timer = rt_objc_define("NSTimer", "NSObject", 0);
    METHODS(cls_timer, 1, {"scheduledTimerWithTimeInterval:target:selector:userInfo:repeats:", t_scheduled},
            {"timerWithTimeInterval:target:selector:userInfo:repeats:", t_timer});
    METHODS(cls_timer, 0, {"initWithFireDate:interval:target:selector:userInfo:repeats:", t_init_fire_date},
            {"invalidate", t_invalidate}, {"isValid", t_is_valid}, {"fire", t_fire}, {"userInfo", t_user_info},
            {"fireDate", t_fire_date}, {"setFireDate:", t_set_fire_date}, {"timeInterval", t_interval},
            {"dealloc", t_dealloc});

    cls_runloop = rt_objc_define("NSRunLoop", "NSObject", 0);
    METHODS(cls_runloop, 1, {"currentRunLoop", rl_current}, {"mainRunLoop", rl_main});
    METHODS(cls_runloop, 0, {"addTimer:forMode:", rl_add_timer}, {"run", rl_run}, {"runUntilDate:", rl_run_until},
            {"runMode:beforeDate:", rl_run_mode}, {"currentMode", rl_mode}, {"getCFRunLoop", rl_get_cf},
            {"dealloc", rl_dealloc});
    loop_object(&main_loop);

    cls_thread = rt_objc_define("NSThread", "NSObject", 0);
    main_thread_obj = rt_objc_alloc(cls_thread);
    ths(main_thread_obj)->is_main = 1;
    ths(main_thread_obj)->started = 1;
    ths(main_thread_obj)->priority = 0.5;
    tl_thread = main_thread_obj;
    METHODS(cls_thread, 1, {"detachNewThreadSelector:toTarget:withObject:", th_detach},
            {"currentThread", th_current}, {"mainThread", th_main}, {"isMainThread", th_is_main_class},
            {"isMultiThreaded", th_multi}, {"sleepForTimeInterval:", th_sleep}, {"sleepUntilDate:", th_sleep_until},
            {"setThreadPriority:", th_set_priority_class}, {"threadPriority", th_priority_class}, {"exit", th_exit});
    METHODS(cls_thread, 0, {"initWithTarget:selector:object:", th_init_target}, {"start", th_start},
            {"isMainThread", th_is_main}, {"name", th_name}, {"setName:", th_set_name},
            {"threadDictionary", th_dict}, {"cancel", th_cancel}, {"isCancelled", th_is_cancelled},
            {"isExecuting", th_is_executing}, {"isFinished", th_is_finished},
            {"setThreadPriority:", th_set_priority}, {"threadPriority", th_priority}, {"dealloc", th_dealloc});

    cls_note = rt_objc_define("NSNotification", "NSObject", 0);
    METHODS(cls_note, 1, {"notificationWithName:object:", n_with_name},
            {"notificationWithName:object:userInfo:", n_with_name_info});
    METHODS(cls_note, 0, {"initWithName:object:userInfo:", n_init}, {"name", n_name}, {"object", n_object},
            {"userInfo", n_user_info}, {"description", n_description}, {"dealloc", n_dealloc});

    cls_center = rt_objc_define("NSNotificationCenter", "NSObject", 0);
    the_center = rt_objc_alloc(cls_center);
    METHODS(cls_center, 1, {"defaultCenter", nc_default});
    METHODS(cls_center, 0, {"addObserver:selector:name:object:", nc_add}, {"removeObserver:", nc_remove},
            {"removeObserver:name:object:", nc_remove_named}, {"postNotification:", nc_post},
            {"postNotificationName:object:", nc_post_name},
            {"postNotificationName:object:userInfo:", nc_post_name_info}, {"dealloc", singleton_dealloc});

    cls_assert = rt_objc_define("NSAssertionHandler", "NSObject", 0);
    the_assert = rt_objc_alloc(cls_assert);
    METHODS(cls_assert, 1, {"currentHandler", as_current});
    METHODS(cls_assert, 0, {"handleFailureInMethod:object:file:lineNumber:description:", as_method},
            {"handleFailureInFunction:file:lineNumber:description:", as_function}, {"dealloc", singleton_dealloc});

    cls_cfarray = rt_objc_define("__RTCFArray", "NSObject", 0);
    METHODS(cls_cfarray, 0, {"count", ca_count}, {"objectAtIndex:", ca_at}, {"addObject:", ca_add},
            {"removeAllObjects", ca_clear}, {"dealloc", ca_dealloc});

    rt_data_resolver_add(resolve);
}

void rt_system_register(void) {
    REG(NSSearchPathForDirectoriesInDomains);
    REG(NSHomeDirectory);
    REG(NSTemporaryDirectory);
    REG(CFBundleGetMainBundle);
    REG(CFBundleCopyBundleURL);
    REG(CFBundleCopyResourcesDirectoryURL);
    REG(CFURLCopyFileSystemPath);
    REG(CFStringGetCString);
    REG(CFStringGetLength);
    REG(CFRelease);
    REG(CFRetain);
    REG(CFArrayCreateMutable);
    REG(CFArrayAppendValue);
    REG(CFArrayGetCount);
    REG(CFArrayGetValueAtIndex);
    REG(CFArrayRemoveAllValues);
    REG(CFDictionaryGetValue);
    REG(CFNumberGetValue);
    REG(CFRunLoopRunInMode);
    REG(CFRunLoopGetCurrent);
    REG(CFRunLoopGetMain);
}
