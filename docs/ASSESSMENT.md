# Assessment: N.O.V.A. HD 1.0.6 (iOS 3.2)

The checks from section 1 of NOVA3_sc's `docs/RECOMP-PLAYBOOK.md`, applied to the iOS executable.

| Check | Result |
|---|---|
| Container | `NovaHD`: thin Mach-O, `MH_EXECUTE`, CPU 12 subtype 6 (armv6), 4.4 MB; iPad only (`UIDeviceFamily = [2]`), landscape |
| Encryption | `LC_ENCRYPTION_INFO` present, `cryptid = 0`: the code is readable as shipped |
| Layout | `__TEXT` 0x1000-0x3c3000 (`__text` 3.75 MB), `__DATA` 0x3c3000-0x402000; not position independent, so it loads at its link addresses |
| Binding | `LC_DYLD_INFO_ONLY` (compressed), 378 symbol stubs (4 bytes, `ldr pc, [pc, #imm]`), 403 non-lazy pointers, 5,578 bound data words |
| Symbols | 702 exported, 1 local: the executable is stripped of private symbols. Function starts come from discovery (below) |
| ARM vs Thumb | 16,580 functions found, 392 Thumb (Thumb-1 only: armv6 has no Thumb-2). Thumb code is the multiplayer/networking layer (`GLXPlayerMP*`, `DataPacket`) and some STL instantiations |
| Instruction mix | ARM: plain integer + VFPv2 single and double precision (`vmla.f32`, `vdiv.f32`, `vcvt.*`, `vsqrt`). No NEON. A handful of ARMv6 media instructions (`rev16`, `uxtb16`) |
| Exceptions | C++ and Objective-C use SjLj (`_Unwind_SjLj_Register/Resume`, `__gxx_personality_sj0`): setjmp/longjmp style, so no unwinder tables to emulate |

## Imports (484)

| Group | Count | Plan |
|---|---|---|
| libSystem (libc, math, sockets, mach) | 140 | NOVA3_sc's `libc.c` with Darwin layouts (`FILE`, `struct stat`, `dirent`, BSD `sockaddr`) |
| OpenGL ES 1.1 | 101 | pass through to Android `libGLESv1_CM` (ANGLE on Windows) |
| Objective-C classes and runtime | 82 | a small ObjC runtime: `objc_msgSend` dispatches to translated game methods or host-implemented system classes |
| libstdc++ (Apple GCC 4.2) | 58 | host implementations that keep libstdc++'s 32-bit layouts (copy-on-write `std::string`, `_Rb_tree` helpers, `ostringstream`) |
| CoreGraphics | 26 | bitmap contexts for text/image rendering into textures |
| OpenAL | 23 | OpenAL Soft (pointer translation only) |
| CoreFoundation | 16 | small: bundle path, arrays, run loop, `CFAbsoluteTimeGetCurrent` |
| pthread | 11 | NOVA3_sc's `pthread.c` |
| UIKit / Foundation functions | 14 | `UIApplicationMain`, `NSLog`, `NSSearchPathForDirectoriesInDomains`, ... |
| SystemConfiguration, AudioToolbox, libgcc | 13 | reachability always "online over Wi-Fi" or stubbed; `AudioSession*` stubbed |

Objective-C classes the game uses from the system: `UIApplication`, `UIWindow`, `UIView`, `UIViewController`,
`UIScreen`, `UIDevice`, `UIAccelerometer`, `EAGLContext`, `CAEAGLLayer`, `NSString`, `NSArray`, `NSDictionary`,
`NSNumber`, `NSData`, `NSUserDefaults`, `NSFileManager`, `NSBundle`, `NSTimer`, `NSRunLoop`, `NSThread`,
`NSAutoreleasePool`, `NSLocale`, `NSDate`; and, for features that can be stubbed at first, `MPMoviePlayerViewController`
(intro video `NOVA.m4v`), `MPMusicPlayerController` (iPod music), `GKSession`/`NSNetService` (local multiplayer),
`UIWebView`/`NSURLConnection` (Gameloft's in-game ads in `igpdata`), `UIAlertView`, `UITextField`.

## Function discovery

The executable keeps only exported symbols (667 in `__text`), so `macho.py` finds the rest by recursive descent:
seeds are the symbols, the entry point, `__mod_init_func`, and every word in the data segments or in a literal
pool that points into `__text` (vtables, Objective-C method lists, callbacks). A seed from data is kept only if it
decodes, starts with an unconditional instruction and is not inside another function's literal pool. Words no
descent reaches are data. Result: 16,580 functions, 2.37 MB of the 3.75 MB of `__text` reached as code; the
rest is literal pools and jump tables (to be confirmed by running the game: the dispatcher logs any address it
does not know).

Branches into the middle of another function's range then make 7,400 more entries (as in NOVA3_sc's `entries`):
24,040 in all.
