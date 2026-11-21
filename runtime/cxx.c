/* C++ runtime imports (Apple GCC 4.2: libstdc++.6, libgcc_s, SjLj exceptions).
 *
 * Done here: static-initializer guards, atexit, the SjLj frame registry, pure virtual calls.
 * Not yet (logged when called): exceptions (__cxa_throw is not imported: the game only catches what libstdc++ or
 * Objective-C throw), and the std::string / ostringstream / _Rb_tree functions of libstdc++, which need the GCC 4.2
 * layouts (docs/PLAN.md, M3).
 */
#include <stdio.h>
#include <string.h>

#include "rt.h"

#define A(k) rt_arg(c, k)
#define RET(v) rt_ret(c, (uint32_t)(v))
#define IMP(name) static void imp_##name(cpu_t *c)
#define REG(name) rt_import_register(#name, imp_##name)

/* __cxa_guard_acquire(guard): 1 if the caller must run the initializer. The first byte of the 32-bit guard
 * is set once the object is initialized (ARM EABI uses bit 0; GCC 4.2 on Darwin the first byte). One game
 * thread initializes statics, so no waiting is needed. */
IMP(__cxa_guard_acquire) { RET(rt_mem[A(0)] == 0); }
IMP(__cxa_guard_release) { rt_mem[A(0)] = 1; }
IMP(__cxa_guard_abort) { (void)c; }
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
