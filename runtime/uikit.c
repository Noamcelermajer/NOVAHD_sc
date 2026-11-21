/* UIKit, QuartzCore and EAGL classes: enough of them for UIApplicationMain to launch the game's delegate.
 *
 * The device is an iPad (1024x768 landscape, iPhone OS 3.2). Views keep their frame in host state; the run loop,
 * touches, timers, the accelerometer and the GL surface come in M3 (docs/PLAN.md). Selectors nobody implements
 * are logged once by objc.c and return 0, which is the list of what to add next.
 */
#include <stdio.h>
#include <string.h>

#include "rt.h"

#define SELF c->r[0]
#define ARG(k) rt_arg(c, (k) + 2)
#define M(name) static void name(cpu_t *c, uint8_t *m)

typedef struct { float x, y, w, h; } rect;
typedef struct { rect frame; id layer, superview, delegate, root; } view_state;

static id app_object, app_delegate, screen_object, device_object, accel_object;

static void put_rect(uint32_t g, rect r) { memcpy(rt_mem + g, &r, 16); }
static float fword(uint32_t w) { float f; memcpy(&f, &w, 4); return f; }

/* ---- small shared implementations ------------------------------------------------------------------------------ */
M(ret_self) { (void)m; (void)c; }
M(ret_zero) { (void)m; rt_ret(c, 0); }
M(ret_one) { (void)m; rt_ret(c, 1); }

/* ---- UIApplication -------------------------------------------------------------------------------------------- */
M(app_shared) { (void)m; rt_ret(c, app_object); }
M(app_delegate_get) { (void)m; rt_ret(c, app_delegate); }
M(app_delegate_set) { (void)m; app_delegate = ARG(0); }
M(app_orientation) { (void)m; rt_ret(c, 3); } /* UIInterfaceOrientationLandscapeRight */
M(app_open_url) { (void)m; rt_log("UIApplication openURL: %s", rt_objc_describe(c, ARG(0))); rt_ret(c, 0); }

/* UIApplicationMain(argc, argv, principalClassName, delegateClassName) */
static void imp_UIApplicationMain(cpu_t *c) {
    const char *dname = rt_nsstring_utf8(rt_arg(c, 3));
    rt_log("UIApplicationMain: delegate class %s", dname ? dname : "(from the main nib)");
    app_object = rt_objc_alloc(rt_class("UIApplication"));
    id dcls = dname ? rt_class(dname) : 0;
    if (!dcls) rt_fatal("UIApplicationMain: no delegate class %s", dname ? dname : "?");
    id d = rt_send(c, rt_send(c, dcls, "alloc", 0), "init", 0);
    app_delegate = d;
    if (rt_responds(d, "application:didFinishLaunchingWithOptions:")) {
        rt_log("UIApplicationMain: -[%s application:didFinishLaunchingWithOptions:]", dname);
        rt_send(c, d, "application:didFinishLaunchingWithOptions:", 2, app_object, 0);
    } else if (rt_responds(d, "applicationDidFinishLaunching:")) {
        rt_log("UIApplicationMain: -[%s applicationDidFinishLaunching:]", dname);
        rt_send(c, d, "applicationDidFinishLaunching:", 1, app_object);
    }
    rt_log("UIApplicationMain: launch finished (the run loop comes in M3)");
    rt_ret(c, 0);
}

/* ---- UIDevice, UIScreen ---------------------------------------------------------------------------------------- */
M(dev_current) { (void)m; rt_ret(c, device_object); }
M(dev_model) { (void)m; rt_ret(c, rt_nsstring("iPad")); }
M(dev_system_name) { (void)m; rt_ret(c, rt_nsstring("iPhone OS")); }
M(dev_system_version) { (void)m; rt_ret(c, rt_nsstring("3.2")); }
M(dev_udid) { (void)m; rt_ret(c, rt_nsstring("0000000000000000000000000000000000000000")); }
M(dev_idiom) { (void)m; rt_ret(c, 1); } /* UIUserInterfaceIdiomPad */
M(dev_orientation) { (void)m; rt_ret(c, 3); }
M(scr_main) { (void)m; rt_ret(c, screen_object); }
M(scr_bounds) { (void)m; put_rect(c->r[0], (rect){0, 0, 768, 1024}); } /* stret: r0 is the result */
M(scr_scale) { (void)m; rt_fret(c, 1.0f); }

/* ---- UIView and friends ------------------------------------------------------------------------------------------ */
static view_state *vs(id v) { return rt_objc_state(v, sizeof(view_state)); }
M(view_init_frame) { /* initWithFrame:(CGRect) in four argument words */
    (void)m;
    vs(SELF)->frame = (rect){fword(ARG(0)), fword(ARG(1)), fword(ARG(2)), fword(ARG(3))};
}
M(view_frame) { (void)m; put_rect(c->r[0], vs(c->r[1])->frame); }
M(view_bounds) { (void)m; rect r = vs(c->r[1])->frame; r.x = r.y = 0; put_rect(c->r[0], r); }
M(view_set_frame) { (void)m; vs(SELF)->frame = (rect){fword(ARG(0)), fword(ARG(1)), fword(ARG(2)), fword(ARG(3))}; }
M(view_layer_class) { (void)m; rt_ret(c, rt_class("CALayer")); }
M(view_layer) {
    (void)m;
    view_state *s = vs(SELF);
    if (!s->layer) {
        id lc = rt_send(c, rt_object_class(SELF), "layerClass", 0);
        s->layer = rt_send(c, rt_send(c, lc ? lc : rt_class("CALayer"), "alloc", 0), "init", 0);
    }
    rt_ret(c, s->layer);
}
M(view_add_subview) { (void)m; id sub = ARG(0); if (sub) vs(sub)->superview = SELF; rt_retain(sub); }
M(view_superview) { (void)m; rt_ret(c, vs(SELF)->superview); }
M(vc_view) {
    (void)m;
    view_state *s = vs(SELF);
    if (!s->root) {
        if (rt_responds(SELF, "loadView")) rt_send(c, SELF, "loadView", 0);
        if (!s->root) s->root = rt_send(c, rt_objc_alloc(rt_class("UIView")), "initWithFrame:", 4, 0, 0, 0x44800000u /*1024*/, 0x44400000u /*768*/);
    }
    rt_ret(c, s->root);
}
M(vc_set_view) { (void)m; vs(SELF)->root = rt_retain(ARG(0)); }

/* ---- EAGL --------------------------------------------------------------------------------------------------------- */
static id current_context;
M(eagl_init_api) { (void)m; rt_log("EAGLContext initWithAPI:%u", ARG(0)); }
M(eagl_set_current) { (void)m; current_context = ARG(0); rt_ret(c, 1); }
M(eagl_current) { (void)m; rt_ret(c, current_context); }

/* ---- UIAccelerometer ---------------------------------------------------------------------------------------------- */
M(acc_shared) { (void)m; rt_ret(c, accel_object); }
M(acc_set_delegate) { (void)m; vs(SELF)->delegate = ARG(0); }

static void def(const char *name, const char *super, uint32_t ivars) { rt_objc_define(name, super, ivars); }
static void im(const char *cls, const char *sel, rt_hostfn fn) { rt_objc_method(rt_class(cls), sel, fn); }
static void cm(const char *cls, const char *sel, rt_hostfn fn) { rt_objc_cmethod(rt_class(cls), sel, fn); }

void rt_uikit_define(void) {
    /* instance sizes match the instanceStart of the game's subclasses (EAGLView 36, view controllers 120, ...) */
    def("UIResponder", "NSObject", 0);
    def("UIApplication", "UIResponder", 0);
    def("UIView", "UIResponder", 32);
    def("UIWindow", "UIView", 0);
    def("UIControl", "UIView", 0);
    def("UIButton", "UIControl", 88);
    def("UIImageView", "UIView", 4);
    def("UILabel", "UIView", 0);
    def("UIScrollView", "UIView", 0);
    def("UITableView", "UIScrollView", 0);
    def("UITextField", "UIControl", 0);
    def("UITextView", "UIScrollView", 0);
    def("UIWebView", "UIView", 0);
    def("UIActivityIndicatorView", "UIView", 0);
    def("UIAlertView", "UIView", 0);
    def("UIViewController", "UIResponder", 116);
    def("UINavigationController", "UIViewController", 80);
    def("UITabBarController", "UIViewController", 0);
    def("UIDevice", "NSObject", 0);
    def("UIScreen", "NSObject", 0);
    def("UIAccelerometer", "NSObject", 0);
    def("UIColor", "NSObject", 0);
    def("UIFont", "NSObject", 0);
    def("UIImage", "NSObject", 0);
    def("CALayer", "NSObject", 0);
    def("CAEAGLLayer", "CALayer", 0);
    def("EAGLContext", "NSObject", 0);

    im("UIApplication", "delegate", app_delegate_get);
    im("UIApplication", "setDelegate:", app_delegate_set);
    cm("UIApplication", "sharedApplication", app_shared);
    im("UIApplication", "statusBarOrientation", app_orientation);
    im("UIApplication", "openURL:", app_open_url);
    const char *app_noops[] = {"setStatusBarHidden:", "setStatusBarHidden:animated:", "setStatusBarOrientation:",
                               "setStatusBarOrientation:animated:", "setIdleTimerDisabled:",
                               "registerForRemoteNotificationTypes:", "setApplicationIconBadgeNumber:"};
    for (size_t k = 0; k < sizeof app_noops / sizeof *app_noops; k++) im("UIApplication", app_noops[k], ret_self);

    cm("UIDevice", "currentDevice", dev_current);
    im("UIDevice", "model", dev_model);
    im("UIDevice", "localizedModel", dev_model);
    im("UIDevice", "name", dev_model);
    im("UIDevice", "systemName", dev_system_name);
    im("UIDevice", "systemVersion", dev_system_version);
    im("UIDevice", "uniqueIdentifier", dev_udid);
    im("UIDevice", "userInterfaceIdiom", dev_idiom);
    im("UIDevice", "orientation", dev_orientation);
    im("UIDevice", "beginGeneratingDeviceOrientationNotifications", ret_self);
    im("UIDevice", "endGeneratingDeviceOrientationNotifications", ret_self);
    im("UIDevice", "isMultitaskingSupported", ret_zero);
    cm("UIScreen", "mainScreen", scr_main);
    im("UIScreen", "bounds", scr_bounds);
    im("UIScreen", "applicationFrame", scr_bounds);
    im("UIScreen", "scale", scr_scale);

    im("UIView", "initWithFrame:", view_init_frame);
    im("UIView", "frame", view_frame);
    im("UIView", "bounds", view_bounds);
    im("UIView", "setFrame:", view_set_frame);
    cm("UIView", "layerClass", view_layer_class);
    im("UIView", "layer", view_layer);
    im("UIView", "addSubview:", view_add_subview);
    im("UIView", "superview", view_superview);
    const char *view_noops[] = {"setMultipleTouchEnabled:", "setUserInteractionEnabled:", "setBackgroundColor:",
                                "setHidden:", "setAlpha:", "setOpaque:", "setNeedsDisplay", "setNeedsLayout",
                                "removeFromSuperview", "bringSubviewToFront:", "setExclusiveTouch:",
                                "setContentScaleFactor:", "setAutoresizingMask:", "setTransform:", "setCenter:"};
    for (size_t k = 0; k < sizeof view_noops / sizeof *view_noops; k++) im("UIView", view_noops[k], ret_self);
    im("UIWindow", "makeKeyAndVisible", ret_self);
    im("UIWindow", "makeKeyWindow", ret_self);
    im("UIViewController", "view", vc_view);
    im("UIViewController", "setView:", vc_set_view);
    im("UIViewController", "initWithNibName:bundle:", ret_self);
    im("UIViewController", "shouldAutorotateToInterfaceOrientation:", ret_one);
    im("CALayer", "setOpaque:", ret_self);
    im("CAEAGLLayer", "setDrawableProperties:", ret_self);

    im("EAGLContext", "initWithAPI:", eagl_init_api);
    cm("EAGLContext", "setCurrentContext:", eagl_set_current);
    cm("EAGLContext", "currentContext", eagl_current);
    im("EAGLContext", "renderbufferStorage:fromDrawable:", ret_one);
    im("EAGLContext", "presentRenderbuffer:", ret_one);

    cm("UIAccelerometer", "sharedAccelerometer", acc_shared);
    im("UIAccelerometer", "setDelegate:", acc_set_delegate);
    im("UIAccelerometer", "setUpdateInterval:", ret_self);

    device_object = rt_objc_alloc(rt_class("UIDevice"));
    screen_object = rt_objc_alloc(rt_class("UIScreen"));
    accel_object = rt_objc_alloc(rt_class("UIAccelerometer"));
}

void rt_uikit_register(void) {
    rt_import_register("UIApplicationMain", imp_UIApplicationMain);
}
