/* C++ runtime imports (Apple GCC 4.2: libstdc++.6, libgcc_s, SjLj exceptions).
 *
 * Done here: static-initializer guards (thread-safe, as GCC 4.2's guard.cc), atexit, the SjLj frame registry,
 * pure virtual calls.
 * Exceptions are not supported (__cxa_throw is not imported: the game only catches what libstdc++ or Objective-C
 * throw, and nothing here throws). libstdc++ itself (std::string, ostringstream, _Rb_tree, type info,
 * __dynamic_cast, the catch entry points and the personality routines) is in libstdcxx.c.
 */
#include <pthread.h>
#include <stdio.h>
#include <string.h>

#include "rt.h"

#define A(k) rt_arg(c, k)
#define RET(v) rt_ret(c, (uint32_t)(v))
#define IMP(name) static void imp_##name(cpu_t *c)
#define REG(name) rt_import_register(#name, imp_##name)

/* __cxa_guard_acquire(guard): 1 if the caller must run the initializer. Darwin GCC 4.2 uses the first byte of
 * the guard as "initialized" (the game's inline fast path tests it with ldrsb before calling here) and the
 * second byte as "initialization in progress". As in GCC 4.2's guard.cc, one process-wide recursive mutex is
 * taken by an acquire that returns 1 and held until the matching release/abort, so two game threads cannot both
 * run the same initializer, and a thread that finds the initializer running elsewhere waits for it. */
static pthread_mutex_t guard_mx;
static pthread_once_t guard_once = PTHREAD_ONCE_INIT;
static void guard_mx_init(void) {
    pthread_mutexattr_t a;
    pthread_mutexattr_init(&a);
    pthread_mutexattr_settype(&a, PTHREAD_MUTEX_RECURSIVE);
    pthread_mutex_init(&guard_mx, &a);
    pthread_mutexattr_destroy(&a);
}
IMP(__cxa_guard_acquire) {
    uint8_t *g = rt_mem + A(0);
    if (__atomic_load_n(&g[0], __ATOMIC_ACQUIRE)) { RET(0); return; }
    pthread_once(&guard_once, guard_mx_init);
    pthread_mutex_lock(&guard_mx);
    if (g[0]) { pthread_mutex_unlock(&guard_mx); RET(0); return; }
    if (g[1]) { /* the same thread re-entered its own initializer: __gnu_cxx::recursive_init in GCC */
        rt_print_trace(c);
        rt_fatal("recursive initialization of a function-local static (guard %#x)", A(0));
    }
    g[1] = 1;
    RET(1); /* the mutex stays held until __cxa_guard_release / __cxa_guard_abort */
}
IMP(__cxa_guard_release) {
    uint8_t *g = rt_mem + A(0);
    g[1] = 0;
    __atomic_store_n(&g[0], 1, __ATOMIC_RELEASE);
    pthread_once(&guard_once, guard_mx_init);
    pthread_mutex_unlock(&guard_mx);
}
IMP(__cxa_guard_abort) {
    rt_mem[A(0) + 1] = 0;
    pthread_once(&guard_once, guard_mx_init);
    pthread_mutex_unlock(&guard_mx);
}
IMP(__cxa_atexit) { RET(0); } /* destructors at exit: the process just ends */
IMP(__cxa_pure_virtual) { rt_print_trace(c); rt_fatal("pure virtual function called"); }

/* SjLj: each function with cleanups registers a context { prev, call_site, data[4], personality, lsda, jbuf }
 * on entry and unregisters it on exit. Keep the per-thread chain so a future throw can walk it. */
static __thread uint32_t sjlj_top;
IMP(_Unwind_SjLj_Register) { rt_st32(A(0), sjlj_top); sjlj_top = A(0); }
IMP(_Unwind_SjLj_Unregister) { sjlj_top = rt_ld32(A(0)); }
IMP(_Unwind_SjLj_Resume) { rt_print_trace(c); rt_fatal("C++ exception unwinding (_Unwind_SjLj_Resume) is not implemented"); }

void rt_cxx_register(void) {
    REG(__cxa_guard_acquire);
    REG(__cxa_guard_release);
    REG(__cxa_guard_abort);
    REG(__cxa_atexit);
    REG(__cxa_pure_virtual);
    REG(_Unwind_SjLj_Register);
    REG(_Unwind_SjLj_Unregister);
    REG(_Unwind_SjLj_Resume);
}
