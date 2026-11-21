/* Windows host front end: a Win32 window with an OpenGL ES 1 context from ANGLE, the boot sequence of the
 * recompiled executable, and the display loop UIApplicationMain hands over to (rt_platform_run).
 *
 *   novahd_runner <NovaHD.app folder> [--image image.bin] [--home folder] [--angle folder] [--headless]
 *                 [--offscreen] [--frames N] [--tap FRAME:X:Y]... [--drag FRAME:X0:Y0:X1:Y1:FRAMES]...
 *                 [--shot FRAME:path.bmp]... [-v|-vv|-vvv]
 *
 * Paths. The game sees its bundle at /var/mobile/Applications/NOVAHD/NovaHD.app and its home (Documents,
 * Library, tmp) at /var/mobile/Applications/NOVAHD; rt_path_alias maps both to host folders: the bundle to the .app
 * folder given on the command line, the home to --home (default "home", created with Documents, Library,
 * Library/Caches and tmp inside, as the iOS installer would). argv[0] of the game is the bundle's executable path.
 *
 * Boot order (main below). The host classes are defined first (the data imports point at them), then the GL
 * resolver is set, then the imports and their data are bound, the game's classes are registered (rt_objc_init),
 * +load runs, the static constructors (__mod_init_func) run, and finally the game's main(argc, argv).
 * main() calls UIApplicationMain, which launches the delegate and calls rt_platform_run; that never returns (the
 * process exits from it when the app quits), as UIApplicationMain never returns on iOS.
 *
 * Display. The window is a resizable top-level window whose client area starts at 1024x768 (the iPad in
 * landscape). The GL surface lives in a child window that keeps the 4:3 aspect and is centred in the client area
 * (letterboxing; the bars are the parent's black background). With ANGLE's EGL_ANGLE_window_fixed_size the surface
 * stays 1024x768 pixels whatever the child's size, and ANGLE stretches it to the child when presenting; without
 * that extension the child stays exactly 1024x768 (centred, clipped when the window is smaller). Either way the
 * game always sees a 1024x768 drawable (rt_platform_size).
 *   --offscreen  renders into a 1024x768 pbuffer instead and never shows the window (unattended runs with --shot).
 *   --headless   (or no ANGLE found) runs without GL: rt_gl_getproc stays NULL and gles1.c's shims do nothing, so
 *                boot and logic tests still work. The frame loop and scripted input run the same way.
 *
 * ANGLE. libEGL.dll and libGLESv2.dll come from --angle <folder>, else from the folder of the executable. The
 * folder is also added to the DLL search path (libGLESv2.dll loads d3dcompiler_47.dll by name). The context is
 * OpenGL ES 1 (EGL_CONTEXT_CLIENT_VERSION 1, which ANGLE implements on its ES3 front end); the config asks for
 * RGBA8, depth 24 + stencil 8, falling back to depth 24, depth 16 + stencil 8, depth 16, and finally to configs that
 * do not advertise EGL_OPENGL_ES_BIT. rt_gl_getproc is eglGetProcAddress, with GetProcAddress(libGLESv2.dll) as
 * the fallback. The context is current on the thread that runs main(), the game's main thread.
 *
 * Input (rt_platform_run, once per frame after pumping the Win32 messages):
 *   - left mouse button     finger 0, in 1024x768 landscape points (the letterbox and any stretch undone);
 *   - right mouse button    finger 1 at the mirrored position (1024 - x, 768 - y), to try two-finger controls;
 *   - Escape quits; P pauses/resumes the app (rt_uikit_pause / rt_uikit_resume); closing the window quits.
 *   - --tap FRAME:X:Y       began at FRAME, ended at FRAME + 2, at (X, Y) points;
 *   - --drag FRAME:X0:Y0:X1:Y1:FRAMES   began at (X0, Y0) at FRAME, moved linearly every frame, ended at (X1, Y1)
 *                           at FRAME + FRAMES.
 *   Scripted touches take finger 0, or the next finger number not held by another scripted touch when they
 *   overlap (so a drag and a tap at the same time are two fingers).
 * Pacing: one rt_uikit_frame per 1/60 s (QueryPerformanceCounter; Sleep for the bulk, then a short spin), with the
 * swap interval at 0 so the monitor's refresh rate does not change the game's speed. --frames N quits after N
 * frames. --shot FRAME:path.bmp writes the back buffer (glReadPixels through rt_gl_getproc) to a 32-bit BMP at the
 * first swap made during or after FRAME, before that swap. A summary goes to stderr at exit.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>

#include "rt.h"

void rt_objc_define_root(void); /* objc.c: NSObject and the root metaclass (not in rt.h's public list) */

#define GAME_HOME "/var/mobile/Applications/NOVAHD"
#define GAME_BUNDLE GAME_HOME "/NovaHD.app"
#define SCREEN_W 1024 /* the iPad screen in landscape, in points (= pixels on the iPad 1) */
#define SCREEN_H 768

#if defined(_WIN32) && !defined(_WIN64)
#define EGL_API __stdcall
#else
#define EGL_API
#endif

/* ---- EGL (loaded at run time from ANGLE's libEGL.dll) ---------------------------------------------------------- */
typedef void *EGLDisplay, *EGLConfig, *EGLSurface, *EGLContext;
typedef int32_t EGLint;
#define EGL_NONE 0x3038
#define EGL_RED_SIZE 0x3024
#define EGL_GREEN_SIZE 0x3023
#define EGL_BLUE_SIZE 0x3022
#define EGL_ALPHA_SIZE 0x3021
#define EGL_DEPTH_SIZE 0x3025
#define EGL_STENCIL_SIZE 0x3026
#define EGL_SURFACE_TYPE 0x3033
#define EGL_RENDERABLE_TYPE 0x3040
#define EGL_PBUFFER_BIT 0x0001
#define EGL_WINDOW_BIT 0x0004
#define EGL_OPENGL_ES_BIT 0x0001
#define EGL_EXTENSIONS 0x3055
#define EGL_WIDTH 0x3057
#define EGL_HEIGHT 0x3056
#define EGL_CONTEXT_CLIENT_VERSION 0x3098
#define EGL_FIXED_SIZE_ANGLE 0x3201 /* EGL_ANGLE_window_fixed_size */

static EGLDisplay (EGL_API *eglGetDisplay)(void *);
static unsigned (EGL_API *eglInitialize)(EGLDisplay, EGLint *, EGLint *);
static unsigned (EGL_API *eglChooseConfig)(EGLDisplay, const EGLint *, EGLConfig *, EGLint, EGLint *);
static EGLSurface (EGL_API *eglCreateWindowSurface)(EGLDisplay, EGLConfig, HWND, const EGLint *);
static EGLSurface (EGL_API *eglCreatePbufferSurface)(EGLDisplay, EGLConfig, const EGLint *);
static EGLContext (EGL_API *eglCreateContext)(EGLDisplay, EGLConfig, EGLContext, const EGLint *);
static unsigned (EGL_API *eglMakeCurrent)(EGLDisplay, EGLSurface, EGLSurface, EGLContext);
static unsigned (EGL_API *eglSwapBuffers)(EGLDisplay, EGLSurface);
static unsigned (EGL_API *eglSwapInterval)(EGLDisplay, EGLint);
static EGLint (EGL_API *eglGetError)(void);
static const char *(EGL_API *eglQueryString)(EGLDisplay, EGLint);
static void *(EGL_API *eglGetProcAddress)(const char *);

static HMODULE egl_dll, gles_dll;
static volatile DWORD ctx_owner; /* the thread the EGL context is current on (one at a time); 0 = nobody */
static EGLDisplay dpy;
static EGLSurface surf;
static EGLContext ctx;

static void *getproc(const char *name) {
    void *p = eglGetProcAddress(name);
    return p ? p : (void *)GetProcAddress(gles_dll, name);
}

/* ---- options and run state --------------------------------------------------------------------------------------- */
enum { MODE_HEADLESS, MODE_WINDOW, MODE_OFFSCREEN };
static int mode = MODE_HEADLESS;
static int fixed_size;              /* EGL_ANGLE_window_fixed_size: the surface is 1024x768 at any window size */
static int max_frames;              /* --frames N (0: until quit) */
static int frame;                   /* rt_uikit_frame calls so far */
static int quit, paused;
static const char *quit_reason = "main() returned";
static unsigned long long swaps, touches_sent, shots_written;
static LARGE_INTEGER qpf, t_start;
static double loop_start = -1;     /* elapsed() when the display loop started */

#define MAX_SCRIPT 64
typedef struct { int frame, x0, y0, x1, y1, len, finger; } script_touch; /* a tap is a drag of length 2 in place */
static script_touch script[MAX_SCRIPT];
static int nscript;
typedef struct { int frame, done; const char *path; } shot_req;
static shot_req shots[16];
static int nshots;

/* ---- window and mouse input -------------------------------------------------------------------------------------- */
static HWND top_win, view_win;
static int view_w = SCREEN_W, view_h = SCREEN_H; /* the child (GL) window's client size */

typedef struct { int phase, finger; float x, y; } touch_ev;
static touch_ev touch_q[256];
static int touch_n;
static int left_down, right_down;

/* moves of a finger with nothing queued after them are coalesced (only the latest position matters), so a burst of
 * WM_MOUSEMOVE between two frames cannot fill the queue and push out the ENDED that follows; a full queue drops
 * only further moves, never a began/ended/cancelled */
static void queue_touch(int phase, int finger, float x, float y) {
    if (phase == RT_TOUCH_MOVED) {
        for (int k = touch_n - 1; k >= 0; k--) {
            if (touch_q[k].finger != finger) continue;
            if (touch_q[k].phase == RT_TOUCH_MOVED) { touch_q[k].x = x; touch_q[k].y = y; return; }
            break;
        }
        if (touch_n >= 240) return;
    }
    if (touch_n < 256) { touch_q[touch_n].phase = phase; touch_q[touch_n].finger = finger; touch_q[touch_n].x = x; touch_q[touch_n].y = y; touch_n++; }
}

/* a mouse position in the GL child window -> screen points (undoes the stretch; clamped to the screen) */
static void mouse_points(LPARAM l, float *x, float *y) {
    float px = (float)(short)LOWORD(l), py = (float)(short)HIWORD(l);
    *x = px * SCREEN_W / (float)(view_w > 0 ? view_w : 1);
    *y = py * SCREEN_H / (float)(view_h > 0 ? view_h : 1);
    if (*x < 0) *x = 0;
    if (*x > SCREEN_W - 1) *x = SCREEN_W - 1;
    if (*y < 0) *y = 0;
    if (*y > SCREEN_H - 1) *y = SCREEN_H - 1;
}

/* centre the GL child in the parent's client area with the 4:3 aspect (or at its fixed 1024x768 size) */
static void layout_view(void) {
    if (!top_win || !view_win) return;
    RECT r;
    GetClientRect(top_win, &r);
    int cw = r.right - r.left, ch = r.bottom - r.top, w = SCREEN_W, h = SCREEN_H;
    if (fixed_size || mode == MODE_HEADLESS) {
        if (cw * SCREEN_H <= ch * SCREEN_W) { w = cw; h = cw * SCREEN_H / SCREEN_W; }
        else { h = ch; w = ch * SCREEN_W / SCREEN_H; }
        if (w < 1) w = 1;
        if (h < 1) h = 1;
    }
    view_w = w;
    view_h = h;
    MoveWindow(view_win, (cw - w) / 2, (ch - h) / 2, w, h, TRUE);
}

static LRESULT CALLBACK wndproc(HWND h, UINT msg, WPARAM w, LPARAM l) {
    float x, y;
    switch (msg) {
    case WM_CLOSE: quit = 1; quit_reason = "window closed"; return 0;
    case WM_SIZE: if (h == top_win) layout_view(); return 0;
    case WM_KEYDOWN:
        if (w == VK_ESCAPE) { quit = 1; quit_reason = "Escape"; }
        else if (w == 'P' && !(l & (1 << 30))) { paused = !paused; paused ? rt_log("host: pause") : rt_log("host: resume"); }
        return 0;
    }
    if (h == view_win) switch (msg) {
    case WM_LBUTTONDOWN:
        if (left_down) return 0;
        left_down = 1; SetCapture(h); mouse_points(l, &x, &y); queue_touch(RT_TOUCH_BEGAN, 0, x, y);
        return 0;
    case WM_LBUTTONUP:
        if (!left_down) return 0;
        left_down = 0; mouse_points(l, &x, &y); queue_touch(RT_TOUCH_ENDED, 0, x, y);
        if (!right_down) ReleaseCapture();
        return 0;
    case WM_RBUTTONDOWN:
        if (right_down) return 0;
        right_down = 1; SetCapture(h); mouse_points(l, &x, &y); queue_touch(RT_TOUCH_BEGAN, 1, SCREEN_W - x, SCREEN_H - y);
        return 0;
    case WM_RBUTTONUP:
        if (!right_down) return 0;
        right_down = 0; mouse_points(l, &x, &y); queue_touch(RT_TOUCH_ENDED, 1, SCREEN_W - x, SCREEN_H - y);
        if (!left_down) ReleaseCapture();
        return 0;
    case WM_MOUSEMOVE:
        mouse_points(l, &x, &y);
        if (left_down) queue_touch(RT_TOUCH_MOVED, 0, x, y);
        if (right_down) queue_touch(RT_TOUCH_MOVED, 1, SCREEN_W - x, SCREEN_H - y);
        return 0;
    case WM_CAPTURECHANGED: /* capture taken away (e.g. alt-tab while dragging): the touches are cancelled */
        if ((HWND)l != h) {
            if (left_down) queue_touch(RT_TOUCH_CANCELLED, 0, 0, 0);
            if (right_down) queue_touch(RT_TOUCH_CANCELLED, 1, 0, 0);
            left_down = right_down = 0;
        }
        return 0;
    }
    return DefWindowProcA(h, msg, w, l);
}

static void pump_messages(void) {
    MSG msg;
    while (PeekMessageA(&msg, NULL, 0, 0, PM_REMOVE)) {
        if (msg.message == WM_QUIT) { quit = 1; quit_reason = "WM_QUIT"; }
        TranslateMessage(&msg);
        DispatchMessageA(&msg);
    }
}

/* 0 when the windows cannot be created (the caller then runs headless) */
static int create_windows(int show) {
    HINSTANCE inst = GetModuleHandleA(NULL);
    WNDCLASSA wc = {0};
    wc.lpfnWndProc = wndproc;
    wc.hInstance = inst;
    wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)(COLOR_WINDOWTEXT + 1); /* black in the standard schemes: the letterbox bars */
    wc.lpszClassName = "novahd";
    RegisterClassA(&wc);
    wc.style = CS_OWNDC;
    wc.hbrBackground = NULL;
    wc.lpszClassName = "novahd_view";
    RegisterClassA(&wc);
    RECT r = {0, 0, SCREEN_W, SCREEN_H};
    AdjustWindowRect(&r, WS_OVERLAPPEDWINDOW, FALSE);
    top_win = CreateWindowA("novahd", "N.O.V.A. HD (recompiled)", WS_OVERLAPPEDWINDOW | WS_CLIPCHILDREN, CW_USEDEFAULT,
                            CW_USEDEFAULT, r.right - r.left, r.bottom - r.top, NULL, NULL, inst, NULL);
    view_win = CreateWindowA("novahd_view", "", WS_CHILD | WS_VISIBLE, 0, 0, SCREEN_W, SCREEN_H, top_win, NULL, inst, NULL);
    if (!top_win || !view_win) {
        rt_log("host: CreateWindow failed (%lu)", GetLastError());
        if (top_win) DestroyWindow(top_win);
        top_win = view_win = NULL;
        return 0;
    }
    layout_view();
    if (show) { ShowWindow(top_win, SW_SHOW); SetForegroundWindow(top_win); SetFocus(top_win); }
    return 1;
}

/* ---- ANGLE / EGL set-up ----------------------------------------------------------------------------------------- */
/* load libEGL.dll and libGLESv2.dll from dir; 0 when either is missing (the caller then runs headless) */
static int load_angle(const char *dir) {
    char path[MAX_PATH];
    snprintf(path, sizeof path, "%s\\libEGL.dll", dir);
    if (GetFileAttributesA(path) == INVALID_FILE_ATTRIBUTES) return 0;
    SetDllDirectoryA(dir); /* libGLESv2.dll loads d3dcompiler_47.dll by name */
    egl_dll = LoadLibraryA(path);
    snprintf(path, sizeof path, "%s\\libGLESv2.dll", dir);
    gles_dll = LoadLibraryA(path);
    if (!egl_dll || !gles_dll) { rt_log("host: cannot load ANGLE from %s (error %lu)", dir, GetLastError()); return 0; }
#define LOAD(fn) do { *(void **)&fn = (void *)GetProcAddress(egl_dll, #fn); if (!fn) { rt_log("host: libEGL.dll has no " #fn); return 0; } } while (0)
    LOAD(eglGetDisplay); LOAD(eglInitialize); LOAD(eglChooseConfig); LOAD(eglCreateWindowSurface);
    LOAD(eglCreatePbufferSurface); LOAD(eglCreateContext); LOAD(eglMakeCurrent); LOAD(eglSwapBuffers);
    LOAD(eglSwapInterval); LOAD(eglGetError); LOAD(eglQueryString); LOAD(eglGetProcAddress);
#undef LOAD
    return 1;
}

static int choose_config(EGLConfig *cfg) {
    static const int depth_stencil[][2] = {{24, 8}, {24, 0}, {16, 8}, {16, 0}};
    EGLint stype = mode == MODE_OFFSCREEN ? EGL_PBUFFER_BIT : EGL_WINDOW_BIT;
    for (int es_bit = 1; es_bit >= 0; es_bit--)
        for (int k = 0; k < 4; k++) {
            EGLint a[] = {EGL_RED_SIZE, 8, EGL_GREEN_SIZE, 8, EGL_BLUE_SIZE, 8, EGL_ALPHA_SIZE, 8,
                          EGL_DEPTH_SIZE, depth_stencil[k][0], EGL_STENCIL_SIZE, depth_stencil[k][1],
                          EGL_SURFACE_TYPE, stype, EGL_RENDERABLE_TYPE, EGL_OPENGL_ES_BIT, EGL_NONE};
            if (!es_bit) a[14] = EGL_NONE;
            EGLint n = 0;
            if (eglChooseConfig(dpy, a, cfg, 1, &n) && n > 0) {
                rt_log("host: EGL config RGBA8 depth %d stencil %d%s", depth_stencil[k][0], depth_stencil[k][1],
                       es_bit ? "" : " (without EGL_OPENGL_ES_BIT)");
                return 1;
            }
        }
    return 0;
}

/* returns 0 (and leaves GL off) when anything fails, so the run continues headless */
static int setup_gl(void) {
    EGLint major = 0, minor = 0;
    dpy = eglGetDisplay(NULL /* EGL_DEFAULT_DISPLAY */);
    if (!dpy || !eglInitialize(dpy, &major, &minor)) { rt_log("host: eglInitialize failed (%#x)", eglGetError()); return 0; }
    const char *ext = eglQueryString(dpy, EGL_EXTENSIONS);
    EGLConfig cfg;
    if (!choose_config(&cfg)) { rt_log("host: no suitable EGL config"); return 0; }
    if (mode == MODE_OFFSCREEN) {
        const EGLint pb[] = {EGL_WIDTH, SCREEN_W, EGL_HEIGHT, SCREEN_H, EGL_NONE};
        surf = eglCreatePbufferSurface(dpy, cfg, pb);
    } else {
        fixed_size = ext && strstr(ext, "EGL_ANGLE_window_fixed_size") != NULL;
        const EGLint fixed[] = {EGL_FIXED_SIZE_ANGLE, 1, EGL_WIDTH, SCREEN_W, EGL_HEIGHT, SCREEN_H, EGL_NONE};
        surf = eglCreateWindowSurface(dpy, cfg, view_win, fixed_size ? fixed : NULL);
        if (!surf && fixed_size) { fixed_size = 0; surf = eglCreateWindowSurface(dpy, cfg, view_win, NULL); }
        layout_view();
    }
    if (!surf) { rt_log("host: cannot create the EGL surface (%#x)", eglGetError()); return 0; }
    const EGLint ca[] = {EGL_CONTEXT_CLIENT_VERSION, 1, EGL_NONE};
    ctx = eglCreateContext(dpy, cfg, NULL, ca);
    if (!ctx) { rt_log("host: cannot create an OpenGL ES 1 context (%#x)", eglGetError()); return 0; }
    if (!eglMakeCurrent(dpy, surf, surf, ctx)) { rt_log("host: eglMakeCurrent failed (%#x)", eglGetError()); return 0; }
    ctx_owner = GetCurrentThreadId();
    eglSwapInterval(dpy, 0); /* pacing is ours (60 Hz), whatever the monitor's refresh rate */
    const char *(EGL_API *getstring)(unsigned) = (const char *(EGL_API *)(unsigned))getproc("glGetString");
    rt_log("host: EGL %d.%d, %s, %s%s", major, minor, getstring ? getstring(0x1F02 /* GL_VERSION */) : "?",
           mode == MODE_OFFSCREEN ? "pbuffer 1024x768" : "window 1024x768",
           mode == MODE_WINDOW ? (fixed_size ? " (fixed size, scaled)" : " (unscaled)") : "");
    return 1;
}

/* ---- screenshots ------------------------------------------------------------------------------------------------- */
static void save_bmp(const char *path) {
    void (EGL_API *readpixels)(int, int, int, int, unsigned, unsigned, void *) =
        (void (EGL_API *)(int, int, int, int, unsigned, unsigned, void *))(rt_gl_getproc ? rt_gl_getproc("glReadPixels") : NULL);
    if (!readpixels) { rt_log("host: no GL, screenshot %s skipped", path); return; }
    int w = SCREEN_W, h = SCREEN_H;
    uint8_t *px = malloc((size_t)w * h * 4);
    if (!px) return;
    readpixels(0, 0, w, h, 0x1908 /* GL_RGBA */, 0x1401 /* GL_UNSIGNED_BYTE */, px);
    FILE *f = fopen(path, "wb");
    if (!f) { rt_log("host: cannot write %s", path); free(px); return; }
    uint32_t size = 54 + (uint32_t)w * h * 4;
    uint8_t hd[54] = {'B', 'M'};
    memcpy(hd + 2, &size, 4);
    hd[10] = 54; hd[14] = 40;
    memcpy(hd + 18, &w, 4);
    memcpy(hd + 22, &h, 4); /* positive height: rows bottom-up, as glReadPixels returns them */
    hd[26] = 1; hd[28] = 32;
    fwrite(hd, 1, 54, f);
    for (int k = 0; k < w * h; k++) { uint8_t t = px[4 * k]; px[4 * k] = px[4 * k + 2]; px[4 * k + 2] = t; } /* RGBA -> BGRA */
    fwrite(px, 4, (size_t)w * h, f);
    fclose(f);
    free(px);
    shots_written++;
    rt_log("host: frame %d: screenshot written to %s", frame, path);
}

/* ---- the platform interface (rt.h) ------------------------------------------------------------------------------- */
void rt_platform_size(int *width, int *height) {
    if (width) *width = SCREEN_W;
    if (height) *height = SCREEN_H;
}

/* -presentRenderbuffer: (through rt_gl_present): screenshots due at this frame, then the swap */
void rt_platform_swap(void) {
    for (int k = 0; k < nshots; k++)
        if (!shots[k].done && frame >= shots[k].frame) { shots[k].done = 1; save_bmp(shots[k].path); }
    swaps++;
    if (surf && !eglSwapBuffers(dpy, surf)) {
        static int logged;
        if (!logged++) rt_log("host: eglSwapBuffers failed (%#x)", eglGetError());
    }
}

static double elapsed(void) {
    LARGE_INTEGER t;
    QueryPerformanceCounter(&t);
    return (double)(t.QuadPart - t_start.QuadPart) / (double)qpf.QuadPart;
}

static void summary(void) {
    double s = elapsed();
    double ls = loop_start >= 0 ? s - loop_start : 0;
    rt_log("host: %s after %d frames, %.1f s (%.1f frames/s in the display loop), %llu swaps, %llu touches, %llu screenshots, %s",
           quit_reason, frame, s, ls > 0 ? frame / ls : 0.0, swaps, touches_sent, shots_written,
           mode == MODE_HEADLESS ? "headless" : mode == MODE_OFFSCREEN ? "offscreen" : "window");
    for (int k = 0; k < nshots; k++)
        if (!shots[k].done) rt_log("host: screenshot %s (frame %d) was not taken (no swap that late)", shots[k].path, shots[k].frame);
}

/* scripted touches for this frame: each is a began/moved.../ended sequence over its frames */
static void run_script(cpu_t *c) {
    for (int k = 0; k < nscript; k++) {
        script_touch *t = &script[k];
        int i = frame - t->frame;
        if (i < 0 || i > t->len) continue;
        if (i == 0) { /* take the lowest finger not held by another scripted touch */
            unsigned used = 0;
            /* held: began at or before this frame (an earlier entry that begins this same frame has already taken
             * its finger) and not ended before this frame (one ending this frame still holds it) */
            for (int j = 0; j < nscript; j++)
                if (j != k && script[j].finger >= 0 && frame >= script[j].frame && frame <= script[j].frame + script[j].len)
                    used |= 1u << script[j].finger;
            t->finger = 0;
            while (t->finger < 31 && (used & (1u << t->finger))) t->finger++;
        }
        float x = t->x0 + (float)(t->x1 - t->x0) * i / (float)t->len, y = t->y0 + (float)(t->y1 - t->y0) * i / (float)t->len;
        int phase = i == 0 ? RT_TOUCH_BEGAN : i == t->len ? RT_TOUCH_ENDED : RT_TOUCH_MOVED;
        if (phase == RT_TOUCH_MOVED && t->x0 == t->x1 && t->y0 == t->y1) continue; /* a tap does not move */
        if (rt_verbose) rt_log("host: frame %d: scripted touch %d finger %d (%.0f, %.0f)", frame, phase, t->finger, x, y);
        rt_uikit_touch(c, phase, t->finger, x, y);
        touches_sent++;
    }
}

void rt_platform_make_current(void) {
    if (mode == MODE_HEADLESS || !ctx) return;
    DWORD me = GetCurrentThreadId();
    if (ctx_owner == me) return;
    for (int waited = 0; ctx_owner && ctx_owner != me; waited++) { /* the main thread releases it at the loop start */
        if (waited == 2000) rt_log("host: thread %lu waits for the GL context held by thread %lu", me, ctx_owner);
        Sleep(1);
    }
    if (eglMakeCurrent(dpy, surf, surf, ctx)) ctx_owner = me;
    else rt_log("host: eglMakeCurrent on thread %lu failed (%#x)", me, eglGetError());
}

static void release_context(void) {
    if (mode == MODE_HEADLESS || !ctx || ctx_owner != GetCurrentThreadId()) return;
    eglMakeCurrent(dpy, NULL, NULL, NULL);
    ctx_owner = 0;
}

void rt_platform_run(cpu_t *c) {
    release_context(); /* the game's render thread takes the context from here on */
    rt_log("host: display loop (%s%s)", mode == MODE_HEADLESS ? "headless" : mode == MODE_OFFSCREEN ? "offscreen" : "window",
           max_frames ? ", limited frames" : "");
    const double period = 1.0 / 60.0;
    HANDLE wait_timer = CreateWaitableTimerExW(NULL, NULL, 0x00000002 /* CREATE_WAITABLE_TIMER_HIGH_RESOLUTION */,
                                               TIMER_ALL_ACCESS);
    if (!wait_timer && rt_verbose) rt_log("host: no high-resolution timer, pacing with Sleep");
    double next = loop_start = elapsed();
    int was_paused = 0;
    while (!quit && (max_frames == 0 || frame < max_frames)) {
        if (top_win) pump_messages();
        if (quit) break;
        if (paused != was_paused) { was_paused = paused; paused ? rt_uikit_pause(c) : rt_uikit_resume(c); }
        for (int k = 0; k < touch_n; k++) rt_uikit_touch(c, touch_q[k].phase, touch_q[k].finger, touch_q[k].x, touch_q[k].y);
        touches_sent += (unsigned)touch_n;
        touch_n = 0;
        run_script(c);
        rt_uikit_frame(c);
        if (c->fault) { quit_reason = "game fault"; rt_log("host: frame %d: game fault %u", frame, c->fault); break; }
        if (frame == 0) rt_log("host: first frame done");
        frame++;
        /* pace to 60 Hz: wait for most of the remaining time, spin the last ~1.5 ms; drop the backlog after a long
         * frame. Sleep() has the 15.6 ms system tick by default (we do not call winmm's timeBeginPeriod), so it would
         * overshoot a 16.7 ms frame; a high-resolution waitable timer (Windows 10 1803+) waits to ~0.5 ms. */
        next += period;
        double now = elapsed();
        if (now > next + 0.25) next = now;
        while ((now = elapsed()) < next) {
            double wait = next - now;
            if (wait <= 0.0015) continue;
            if (wait_timer) {
                LARGE_INTEGER due;
                due.QuadPart = -(LONGLONG)((wait - 0.001) * 1e7); /* relative, in 100 ns units */
                if (SetWaitableTimer(wait_timer, &due, 0, NULL, NULL, FALSE)) WaitForSingleObject(wait_timer, 100);
            } else if (wait > 0.017)
                Sleep((DWORD)((wait - 0.017) * 1000.0)); /* coarse tick: sleep only what cannot overshoot */
            else
                Sleep(0);
        }
    }
    if (!quit && max_frames && frame >= max_frames) quit_reason = "frame limit";
    summary();
    fflush(stderr);
    fflush(stdout);
    exit(c->fault ? 1 : 0);
}

/* ---- crash reports: a host access violation inside game memory names the game address --------------------------
 * The vectored handler sees first-chance exceptions, including access violations that D3D drivers and ANGLE raise
 * and handle themselves; so it reports only faults inside the game's 4 GB window (nobody handles those) and leaves
 * host addresses to the unhandled-exception filter, which runs only when the process is really going down. */
static volatile LONG reported;

static LONG CALLBACK on_exception(EXCEPTION_POINTERS *e) {
    if (e->ExceptionRecord->ExceptionCode != EXCEPTION_ACCESS_VIOLATION) return EXCEPTION_CONTINUE_SEARCH;
    uintptr_t a = (uintptr_t)e->ExceptionRecord->ExceptionInformation[1];
    if (!rt_mem || a < (uintptr_t)rt_mem || a >= (uintptr_t)rt_mem + (1ull << 32)) return EXCEPTION_CONTINUE_SEARCH;
    if (InterlockedIncrement(&reported) > 4) return EXCEPTION_CONTINUE_SEARCH;
    const char *what = e->ExceptionRecord->ExceptionInformation[0] ? "write to" : "read of";
    rt_log("crash: %s game address %#llx (unmapped game memory) at frame %d", what, (unsigned long long)(a - (uintptr_t)rt_mem), frame);
    rt_print_trace(rt_thread_cpu());
    return EXCEPTION_CONTINUE_SEARCH;
}

static LONG WINAPI on_unhandled(EXCEPTION_POINTERS *e) {
    DWORD code = e->ExceptionRecord->ExceptionCode;
    if (code == EXCEPTION_ACCESS_VIOLATION) {
        uintptr_t a = (uintptr_t)e->ExceptionRecord->ExceptionInformation[1];
        if (!(rt_mem && a >= (uintptr_t)rt_mem && a < (uintptr_t)rt_mem + (1ull << 32))) /* game ones: reported above */
            rt_log("crash: %s host address %p at %p, frame %d", e->ExceptionRecord->ExceptionInformation[0] ? "write to" : "read of",
                   (void *)a, e->ExceptionRecord->ExceptionAddress, frame);
    } else
        rt_log("crash: exception %#lx at %p, frame %d", (unsigned long)code, e->ExceptionRecord->ExceptionAddress, frame);
    fflush(stderr);
    return EXCEPTION_CONTINUE_SEARCH;
}

/* ---- command line and boot ----------------------------------------------------------------------------------------- */
static void usage(const char *exe) {
    fprintf(stderr,
            "usage: %s <NovaHD.app folder> [--image image.bin] [--home folder] [--angle folder] [--headless]\n"
            "       [--offscreen] [--frames N] [--tap FRAME:X:Y] [--drag FRAME:X0:Y0:X1:Y1:FRAMES]\n"
            "       [--shot FRAME:path.bmp] [-v|-vv|-vvv]\n", exe);
}

static void make_dir(const char *base, const char *sub) {
    char p[MAX_PATH];
    snprintf(p, sizeof p, "%s%s%s", base, sub[0] ? "\\" : "", sub);
    CreateDirectoryA(p, NULL); /* fails harmlessly when it exists */
}

int main(int argc, char **argv) {
    const char *app = NULL, *image = "image.bin", *home = "home", *angle = NULL;
    int headless = 0, offscreen = 0;
    for (int k = 1; k < argc; k++) {
        const char *a = argv[k], *v = k + 1 < argc ? argv[k + 1] : NULL;
        if (!strcmp(a, "--image") && v) image = argv[++k];
        else if (!strcmp(a, "--home") && v) home = argv[++k];
        else if (!strcmp(a, "--angle") && v) angle = argv[++k];
        else if (!strcmp(a, "--headless")) headless = 1;
        else if (!strcmp(a, "--offscreen")) offscreen = 1;
        else if (!strcmp(a, "--frames") && v) max_frames = atoi(argv[++k]);
        else if (!strcmp(a, "--tap") && v) {
            int f, x, y;
            k++;
            if (sscanf(v, "%d:%d:%d", &f, &x, &y) != 3) { fprintf(stderr, "bad --tap %s (FRAME:X:Y)\n", v); return 2; }
            if (nscript < MAX_SCRIPT) script[nscript++] = (script_touch){f, x, y, x, y, 2, -1};
        } else if (!strcmp(a, "--drag") && v) {
            int f, x0, y0, x1, y1, n;
            k++;
            if (sscanf(v, "%d:%d:%d:%d:%d:%d", &f, &x0, &y0, &x1, &y1, &n) != 6) {
                fprintf(stderr, "bad --drag %s (FRAME:X0:Y0:X1:Y1:FRAMES)\n", v);
                return 2;
            }
            if (n < 1) n = 1;
            if (nscript < MAX_SCRIPT) script[nscript++] = (script_touch){f, x0, y0, x1, y1, n, -1};
        } else if (!strcmp(a, "--shot") && v) {
            const char *colon = strchr(v, ':');
            k++;
            if (!colon || colon == v) { fprintf(stderr, "bad --shot %s (FRAME:path.bmp)\n", v); return 2; }
            if (nshots < 16) { shots[nshots].frame = atoi(v); shots[nshots].path = colon + 1; nshots++; }
        } else if (a[0] == '-' && a[1] == 'v' && strspn(a + 1, "v") == strlen(a + 1)) rt_verbose = (int)strlen(a) - 1;
        else if (a[0] == '-') { fprintf(stderr, "unknown option %s\n", a); usage(argv[0]); return 2; }
        else app = a;
    }
    if (!app) { usage(argv[0]); return 2; }
    QueryPerformanceFrequency(&qpf);
    QueryPerformanceCounter(&t_start);
    AddVectoredExceptionHandler(1, on_exception);
    SetUnhandledExceptionFilter(on_unhandled);

    /* paths: the bundle and the home folder (with the folders iOS creates in an app's home) */
    snprintf(rt_bundle_path, sizeof rt_bundle_path, "%s", GAME_BUNDLE);
    snprintf(rt_home_path, sizeof rt_home_path, "%s", GAME_HOME);
    rt_path_alias(GAME_BUNDLE, app);
    rt_path_alias(GAME_HOME, home);
    make_dir(home, "");
    make_dir(home, "Documents");
    make_dir(home, "Library");
    make_dir(home, "Library\\Caches");
    make_dir(home, "tmp");

    /* ANGLE: --angle, else next to the executable; none (or --headless) -> no GL */
    char exe_dir[MAX_PATH];
    DWORD n = GetModuleFileNameA(NULL, exe_dir, sizeof exe_dir);
    if (n == 0 || n >= sizeof exe_dir) strcpy(exe_dir, ".");
    else { char *s = strrchr(exe_dir, '\\'); if (s) *s = 0; }
    if (!headless) {
        const char *dir = angle ? angle : exe_dir;
        if (load_angle(dir)) mode = offscreen ? MODE_OFFSCREEN : MODE_WINDOW;
        else rt_log("host: no ANGLE (libEGL.dll, libGLESv2.dll) in %s: running without GL", dir);
    }
    if (mode != MODE_HEADLESS) {
        if (!create_windows(mode == MODE_WINDOW) || !setup_gl()) {
            rt_log("host: GL set-up failed: running without GL");
            mode = MODE_HEADLESS;
            surf = NULL;
            if (top_win) DestroyWindow(top_win);
            top_win = view_win = NULL;
        }
    }

    /* game memory; the host classes (the data imports point at them); the imports and their data; the game's
     * classes, +load and the static constructors; then the game's main() */
    if (rt_mem_init(image)) { rt_log("host: cannot load the image %s", image); return 1; }
    rt_objc_define_root();
    rt_foundation_define();
    rt_collections_define();
    rt_system_define();
    rt_uikit_define();
    rt_graphics_define();
    rt_offline_define();
    rt_gl_getproc = mode == MODE_HEADLESS ? NULL : getproc;
    rt_imports_init();
    rt_data_imports_bind();
    rt_objc_init();

    cpu_t *c = rt_thread_cpu();
    rt_objc_load();
    for (uint32_t k = 0; k < rt_init_func_count; k++) {
        rt_call(c, rt_init_funcs[k], 0);
        if (c->fault) { rt_log("host: constructor %#x faulted (%u)", rt_init_funcs[k], c->fault); return 1; }
    }
    rt_log("host: %u static constructors done", rt_init_func_count);

    char argv0[600];
    snprintf(argv0, sizeof argv0, "%s/NovaHD", rt_bundle_path);
    uint32_t gargv = rt_calloc(2, 4); /* argv[0], NULL */
    rt_st32(gargv, rt_static_string(argv0));
    uint32_t r = rt_call(c, rt_main, 2, 1, gargv);
    rt_log("host: main returned %u (fault %u)", r, c->fault);
    if (c->fault) quit_reason = "game fault";
    summary();
    return c->fault ? 1 : 0;
}
