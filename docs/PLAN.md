# Plan: from the translated executable to a playable APK

The translation (milestone 1) is the part shared with NOVA3_sc. What remains is the platform: N.O.V.A. 3 expected
Android (libc, GLES2, OpenSL, a JVM); N.O.V.A. HD expects iOS 3.2. The same rules apply: keep the original 32-bit
memory layout, implement imports as host functions that read the 32-bit ABI, verify against the original, log
every unknown import, selector and class once.

## M2: the Objective-C runtime

- **Game classes.** Read `__objc_classlist`, `__objc_catlist`, `__objc_selrefs`, `__objc_classrefs` and
  `__objc_superrefs` at load. Class, metaclass and method list structures stay where the compiler put them
  (`class_t`, `class_ro_t`, `method_t` with the iOS 32-bit layout); the runtime only builds lookup tables.
- **System classes.** Host-implemented classes get `class_t` structures in game memory (so `isa`, `superclass` and
  `[x class]` work) whose methods point into the host-function range (`RT_HOSTFN_BASE`, as JNI tables in NOVA3_sc).
  Game classes that subclass `UIView`, `UIViewController` or `NSObject` are linked to them through the bound
  superclass pointers that `macho.py` already resolves.
- **objc_msgSend / objc_msgSendSuper2 / objc_msgSend_stret.** Look up (class, selector string) in a cache; call the
  translated IMP through `rc_dispatch`, or the host method. Unknown selector on a host class: log once, return nil.
- **Objects.** Allocated in game memory with the runtime's allocator. Retain counts in a side table (`retain`,
  `release`, `autorelease`, `NSAutoreleasePool` drains).
- **Constant strings.** `__cfstring` entries (`isa` = `__CFConstantStringClassReference`, flags, pointer, length)
  are valid `NSString` objects as they are; host `NSString` methods read that layout and create the same layout.
- **Exceptions.** `objc_begin_catch`/`objc_end_catch` and `_Unwind_SjLj_*` with SjLj semantics: the game registers
  its frames; a throw walks the registered list and resumes at the landing pad through the translated code's
  dispatcher.

Reference for behaviour (not code): touchHLE, an open-source HLE emulator for iPhone OS 2-3 apps, solves the same
problem with an emulated CPU.

## M3: libSystem, libstdc++, frameworks

- libc from NOVA3_sc's `runtime/libc.c` and `printf.c`, with Darwin layouts: `FILE` (88 bytes, `__stdoutp`),
  `struct stat` (96 bytes), `dirent` (`d_namlen`), errno via `__error()`, BSD `sockaddr_in` (`sin_len`),
  `sysctlbyname("hw.machine")` = `iPad1,1`.
- libstdc++ (Apple GCC 4.2): `std::string` is copy-on-write with a `_Rep` header (length, capacity, refcount) before
  the characters and a shared `_S_empty_rep_storage`; `_Rb_tree` helpers and `_List_node_base` are small algorithms;
  `basic_ostringstream` keeps GCC 4.2's object size and vtable.
- UIKit: `UIApplicationMain` creates the app delegate (class named by the call, no nib in this app), sends
  `applicationDidFinishLaunching:`, then runs the loop: `NSTimer`/`performSelector` callbacks, touches as `UITouch`
  sets to the game view's `touchesBegan/Moved/Ended:withEvent:` in 1024x768 points, `UIAccelerometer` from the
  Android accelerometer.
- EAGL: `EAGLContext` -> EGL context (GLES 1.1); `renderbufferStorage:fromDrawable:` binds the window surface;
  `presentRenderbuffer:` = `eglSwapBuffers`. The game's framebuffer object is the default framebuffer.
- OpenGL ES 1.1: generated shims as in NOVA3_sc's `gen_gl.py` (client-side arrays become guest pointers).
- OpenAL: OpenAL Soft built for Android; `alBufferData` copies from game memory.
- Files: the `.app` folder becomes the bundle path (`CFBundleCopyBundleURL`, `[NSBundle mainBundle]`);
  `Documents/` maps to the Android app's files folder.

## M4: boot, first frame, Android

1. Constructors (`__mod_init_func`), then `start` -> `main` -> `UIApplicationMain`.
2. First frame on the Windows host runner (NOVA3_sc's `host_main.c` with ANGLE, which supports GLES 1.1).
3. Touch, accelerometer, audio.
4. `NativeActivity` APK from NOVA3_sc's `android_main.c`, landscape, 1024x768 render target scaled to the screen.

## Other Gameloft iOS games

Nothing in `macho.py` or the lifter is specific to N.O.V.A. HD. Another game of the same era (armv6/armv7,
iOS 3-4, Objective-C shell around a C++ engine) needs: a decrypted thin executable (`lipo -thin armv6` or
`armv7`; armv7 adds Thumb-2, which the lifter does not handle yet), its own import list (most of the runtime
carries over), and its own platform quirks list.
