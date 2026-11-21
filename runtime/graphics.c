/* CoreGraphics, UIGraphics, UIImage, UIColor and UIFont: a small software renderer for the few things the game
 * draws with Quartz (IGP/GLLive icons uploaded as GL textures, a reflection with a gradient mask, a resize, a
 * solid-colour placeholder), PNG decoding and encoding, and a baseline JPEG encoder.
 *
 * How the game uses it (from the disassembly):
 *   - texture upload (sub_1b1060, sub_33fb50): [UIImage imageWithData:] / file -> CGImage -> CGBitmapContextCreate(
 *     malloc'd w*h*4 buffer, pow2 w, pow2 h, 8, 4*w, CGImageGetColorSpace(img), kCGImageAlphaPremultipliedLast) ->
 *     CGContextDrawImage(ctx, {0, 0, w, h}, img) (stretched to the pow2 size) -> glTexImage2D(RGBA).
 *   - +[GLLiveUtil ResizeImage:iWidth:iHeight:] (sub_33fdd0): UIGraphicsBeginImageContext, ScaleCTM(1, -1),
 *     TranslateCTM(0, -h), DrawImage, UIGraphicsGetImageFromCurrentImageContext.
 *   - reflectedImage:withHeight: (sub_1a54ec/sub_1a2e84): an RGB context (NULL data, bytesPerRow 0, 0x2002 =
 *     32Little | PremultipliedFirst), a DeviceGray gradient mask (CGGradientCreateWithColorComponents,
 *     CGContextDrawLinearGradient, options kCGGradientDrawsAfterEndLocation), CGImageCreateWithMask.
 *   - UIGraphicsBeginImageContext + SetRGBFillColor + FillRect for a plain background image.
 *
 * Objects. Every CG object is an instance of a host class (CGContext, CGImage, CGColorSpace, CGGradient; subclasses
 * of NSObject) so CFRelease/CFRetain (system module) work through -retain/-release, and -dealloc frees what the
 * object owns. All per-object data lives in host state (rt_objc_state), never in ivars: uikit.c may define
 * UIImage/UIColor/UIFont first with no ivars, and rt_objc_define then returns its class.
 *   CGColorSpace  two immortal singletons (DeviceRGB, DeviceGray); retain/release are no-ops.
 *   CGImage       host RGBA8 pixels, premultiplied alpha, row 0 = the top of the image; a "gray" flag (images made
 *                 from gray contexts, i.e. masks) and an "alpha" flag. Decoded PNGs (grey ones included) are RGB:
 *                 the game builds its texture context with the image's colour space and premultiplied alpha,
 *                 which CG only accepts for RGB.
 *   CGContext     a bitmap in GAME memory (the game reads it back for glTexImage2D), its pixel format (8 bits per
 *                 component; gray, RGB or alpha-only; any CGImageAlphaInfo; 32-bit little-endian byte order),
 *                 the CTM and the fill colour. NULL data is allocated with rt_calloc and freed with the context.
 *   CGGradient    up to 16 stops of gray+alpha or RGBA components.
 *   UIImage       holds a retained CGImage. UIColor holds RGBA floats; -CGColor returns the UIColor itself (it is a
 *                 valid CF object to retain/release; nothing the game imports reads a CGColor). UIFont holds a
 *                 name and point size and answers metrics for Helvetica.
 *
 * Coordinates. CG's device space has its origin at the bottom-left, y up; row 0 of a bitmap is the TOP row, so
 * the pixel at (x, row) has its centre at device (x + 0.5, height - row - 0.5). An image drawn into a rect has its
 * first (top) row at the rect's maximum y. A UIGraphics image context starts with the UIKit CTM (origin top-left,
 * y down: [1 0 0 -1 0 h]), and -[UIImage drawInRect:] draws upright in it (image top at the rect's minimum y).
 * Drawing walks the destination pixels, maps each centre back through the inverse CTM, and composites source-over
 * with premultiplied alpha; images are sampled bilinearly (exact at 1:1).
 *
 * Images: PNG is decoded here (zlib inflate written out below; bit depths 1/2/4/8/16, grey, grey+alpha, RGB, RGBA,
 * palette with tRNS; Apple's CgBI variant used by iOS bundles: raw deflate, BGRA premultiplied). Interlaced PNG
 * and JPEG decoding are not supported (logged, nil). UIImagePNGRepresentation writes an RGBA PNG with zlib stored
 * blocks; UIImageJPEGRepresentation writes baseline JPEG (4:4:4, the standard luminance tables for all
 * components).
 *
 * NSString's UIKit additions -sizeWithFont: and -sizeWithFont:constrainedToSize:lineBreakMode: are here as well,
 * because they need the font metrics.
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "rt.h"

#define SELF c->r[0]
#define ARG(k) rt_arg(c, (k) + 2)
#define FARG(k) rt_farg(c, (k) + 2)
#define M(name) static void name(cpu_t *c, uint8_t *m)
#define A(k) rt_arg(c, k)
#define F(k) rt_farg(c, k)
#define IMP(name) static void imp_##name(cpu_t *c)
#define REG(name) rt_import_register(#name, imp_##name)

#define LOG_ONCE(...) do { static int once_; if (!once_++) rt_log(__VA_ARGS__); } while (0)

static id cls_context, cls_image, cls_space, cls_gradient, cls_uiimage, cls_uicolor, cls_uifont;
static id space_rgb, space_gray;

static void put_f32(uint32_t g, float v) { memcpy(rt_mem + g, &v, 4); }
static float get_f32(uint32_t g) { float v; memcpy(&v, rt_mem + g, 4); return v; }
static uint8_t to_byte(float v) { return v <= 0 ? 0 : v >= 1 ? 255 : (uint8_t)(v * 255.0f + 0.5f); }

/* ---- affine transforms: point' = (a x + c y + tx, b x + d y + ty), the CGAffineTransform layout ------------- */
typedef struct { float a, b, c, d, tx, ty; } xform;

static const xform identity = {1, 0, 0, 1, 0, 0};

static xform x_concat(xform t1, xform t2) { /* t1 then t2 */
    xform r;
    r.a = t1.a * t2.a + t1.b * t2.c;
    r.b = t1.a * t2.b + t1.b * t2.d;
    r.c = t1.c * t2.a + t1.d * t2.c;
    r.d = t1.c * t2.b + t1.d * t2.d;
    r.tx = t1.tx * t2.a + t1.ty * t2.c + t2.tx;
    r.ty = t1.tx * t2.b + t1.ty * t2.d + t2.ty;
    return r;
}
static xform x_rotation(float angle) {
    float s = sinf(angle), co = cosf(angle);
    return (xform){co, s, -s, co, 0, 0};
}
static int x_invert(xform t, xform *out) {
    float det = t.a * t.d - t.b * t.c;
    if (fabsf(det) < 1e-12f) return 0;
    out->a = t.d / det;
    out->b = -t.b / det;
    out->c = -t.c / det;
    out->d = t.a / det;
    out->tx = (t.c * t.ty - t.d * t.tx) / det;
    out->ty = (t.b * t.tx - t.a * t.ty) / det;
    return 1;
}
static void x_apply(xform t, float x, float y, float *ox, float *oy) {
    *ox = t.a * x + t.c * y + t.tx;
    *oy = t.b * x + t.d * y + t.ty;
}
static xform x_read(cpu_t *c, int k) { /* six consecutive argument words */
    return (xform){F(k), F(k + 1), F(k + 2), F(k + 3), F(k + 4), F(k + 5)};
}
static void x_write(uint32_t g, xform t) { memcpy(rt_mem + g, &t, 24); }

/* ---- object state ------------------------------------------------------------------------------------------- */
typedef struct { int gray; } space_state;

typedef struct {
    int w, h;
    int gray;   /* made from a gray context (masks) */
    int alpha;  /* has meaningful alpha */
    uint8_t *px; /* host RGBA8, premultiplied, w*h*4, row 0 = top */
} image_state;

typedef struct {
    uint32_t data;  /* game address of the bitmap */
    int owns;       /* allocated here (data was NULL) */
    int w, h, bpr, bpp;
    int ncomp;      /* 3 RGB, 1 gray, 0 alpha only */
    int oc[3], oa;  /* byte offsets of the colour components and alpha (-1: none) inside a pixel */
    int oskip;      /* offset of a skipped (X) byte, -1 if none */
    int premul;     /* alpha is premultiplied (else straight) */
    xform ctm;
    float fill[4];  /* straight RGBA */
} ctx_state;

#define GRAD_MAX 16
typedef struct { int gray, n; float comp[GRAD_MAX][4]; float loc[GRAD_MAX]; } grad_state;

typedef struct { id cg; } uiimage_state;
typedef struct { float r, g, b, a; } color_state;
typedef struct { float size; int bold, italic; char name[64]; } font_state;

static space_state *SS(id o) { return rt_objc_state(o, sizeof(space_state)); }
static image_state *IS(id o) { return rt_objc_state(o, sizeof(image_state)); }
static ctx_state *CS(id o) { return rt_objc_state(o, sizeof(ctx_state)); }
static grad_state *GS(id o) { return rt_objc_state(o, sizeof(grad_state)); }
static uiimage_state *UIS(id o) { return rt_objc_state(o, sizeof(uiimage_state)); }
static color_state *COL(id o) { return rt_objc_state(o, sizeof(color_state)); }
static font_state *FS(id o) { return rt_objc_state(o, sizeof(font_state)); }

static int is_a(id o, id cls) { return o && rt_is_kind(o, cls); }
static image_state *image_of(id img) { return is_a(img, cls_image) ? IS(img) : NULL; }
static ctx_state *ctx_of(id ctx) {
    if (is_a(ctx, cls_context)) return CS(ctx);
    if (ctx) LOG_ONCE("graphics: a CG function got %s instead of a CGContext", rt_class_name(rt_object_class(ctx)));
    return NULL;
}

/* a new CGImage (+1) owning `px` (host malloc, RGBA premultiplied) */
static id image_new(int w, int h, uint8_t *px, int gray, int alpha) {
    id img = rt_objc_alloc(cls_image);
    image_state *s = IS(img);
    s->w = w;
    s->h = h;
    s->px = px;
    s->gray = gray;
    s->alpha = alpha;
    return img;
}

M(image_dealloc) {
    (void)m;
    image_state *s = rt_objc_state_peek(SELF);
    if (s) free(s->px);
    rt_objc_free(SELF);
}
M(ctx_dealloc) {
    (void)m;
    ctx_state *s = rt_objc_state_peek(SELF);
    if (s && s->owns && s->data) rt_free(s->data);
    rt_objc_free(SELF);
}
M(uiimage_dealloc) {
    (void)m;
    uiimage_state *s = rt_objc_state_peek(SELF);
    id cg = s ? s->cg : 0;
    if (s) s->cg = 0;
    rt_release(c, cg);
    rt_objc_free(SELF);
}
M(obj_nop) { (void)m; (void)c; }       /* immortal objects: retain, release, dealloc */
M(obj_self) { (void)m; (void)c; }       /* returns self (r0 unchanged) */

/* ---- bitmap pixels ------------------------------------------------------------------------------------------ */
static uint8_t *px_at(ctx_state *s, int x, int row) { return rt_mem + s->data + (uint32_t)row * (uint32_t)s->bpr + (uint32_t)(x * s->bpp); }

/* premultiplied RGBA in [0, 1] */
static void px_get(ctx_state *s, int x, int row, float p[4]) {
    const uint8_t *q = px_at(s, x, row);
    float a = s->oa >= 0 ? q[s->oa] / 255.0f : 1.0f;
    if (s->ncomp == 3) {
        for (int k = 0; k < 3; k++) p[k] = q[s->oc[k]] / 255.0f;
    } else if (s->ncomp == 1) {
        p[0] = p[1] = p[2] = q[s->oc[0]] / 255.0f;
    } else {
        p[0] = p[1] = p[2] = 0;
    }
    if (s->ncomp && s->oa >= 0 && !s->premul)
        for (int k = 0; k < 3; k++) p[k] *= a;
    p[3] = a;
}

static void px_put(ctx_state *s, int x, int row, const float p[4]) {
    uint8_t *q = px_at(s, x, row);
    float a = p[3], col[3] = {p[0], p[1], p[2]};
    if (s->oa >= 0 && !s->premul && a > 0)
        for (int k = 0; k < 3; k++) col[k] /= a;
    if (s->ncomp == 3) {
        for (int k = 0; k < 3; k++) q[s->oc[k]] = to_byte(col[k]);
    } else if (s->ncomp == 1) {
        q[s->oc[0]] = to_byte(0.299f * col[0] + 0.587f * col[1] + 0.114f * col[2]);
    }
    if (s->oa >= 0) q[s->oa] = to_byte(a);
    if (s->oskip >= 0) q[s->oskip] = 255;
}

/* source-over with a premultiplied source */
static void px_blend(ctx_state *s, int x, int row, const float src[4]) {
    if (src[3] >= 1.0f) { px_put(s, x, row, src); return; }
    if (src[3] <= 0 && src[0] <= 0 && src[1] <= 0 && src[2] <= 0) return;
    float d[4];
    px_get(s, x, row, d);
    float k = 1.0f - src[3];
    for (int i = 0; i < 4; i++) d[i] = src[i] + d[i] * k;
    px_put(s, x, row, d);
}

/* set up the pixel format; 0 when unsupported */
static int ctx_format(ctx_state *s, int ncomp, uint32_t info) {
    uint32_t ainfo = info & 0x1f, order = info & 0x7000;
    s->ncomp = ncomp;
    s->oa = s->oskip = -1;
    s->oc[0] = s->oc[1] = s->oc[2] = -1;
    s->premul = ainfo == 1 || ainfo == 2 || ainfo == 7;
    if (info & 0x100) { LOG_ONCE("graphics: float bitmap contexts are not supported"); return 0; }
    if (order == 0x1000 || order == 0x3000) { LOG_ONCE("graphics: 16-bit byte orders are not supported"); return 0; }
    if (ncomp == 0) { /* kCGImageAlphaOnly */
        s->bpp = 1;
        s->oa = 0;
        return 1;
    }
    if (ainfo == 7) { LOG_ONCE("graphics: alpha-only bitmap with a colour space"); return 0; }
    int first = ainfo == 2 || ainfo == 4 || ainfo == 6;
    int has_alpha = ainfo >= 1 && ainfo <= 4, skip = ainfo == 5 || ainfo == 6;
    if (ncomp == 3) {
        if (ainfo == 0) { /* not accepted by real CG; harmless to support */
            s->bpp = 3;
            for (int k = 0; k < 3; k++) s->oc[k] = k;
            return 1;
        }
        s->bpp = 4;
        int o = first ? 1 : 0, ox = first ? 0 : 3;
        for (int k = 0; k < 3; k++) s->oc[k] = o + k;
        if (has_alpha) s->oa = ox;
        if (skip) s->oskip = ox;
        if (order == 0x2000) { /* 32-bit little endian: the bytes of each pixel are reversed */
            for (int k = 0; k < 3; k++) s->oc[k] = 3 - s->oc[k];
            if (s->oa >= 0) s->oa = 3 - s->oa;
            if (s->oskip >= 0) s->oskip = 3 - s->oskip;
        }
        return 1;
    }
    /* gray */
    if (ainfo == 0) { s->bpp = 1; s->oc[0] = 0; return 1; }
    s->bpp = 2; /* gray + alpha (or skip), lenient */
    s->oc[0] = first ? 1 : 0;
    if (has_alpha) s->oa = first ? 0 : 1;
    if (skip) s->oskip = first ? 0 : 1;
    return 1;
}

/* a new context (+1) over game memory at `data` (0: allocate) */
static id ctx_new(uint32_t data, int w, int h, int bpr, int ncomp, uint32_t info) {
    ctx_state tmp;
    memset(&tmp, 0, sizeof tmp);
    if (!ctx_format(&tmp, ncomp, info)) return 0;
    if (!bpr) bpr = w * tmp.bpp;
    if (bpr < w * tmp.bpp) {
        rt_log("graphics: CGBitmapContextCreate: bytesPerRow %d is too small for %d pixels", bpr, w);
        return 0;
    }
    if (!data) {
        data = rt_calloc((uint32_t)h, (uint32_t)bpr);
        if (!data) return 0;
        tmp.owns = 1;
    }
    tmp.data = data;
    tmp.w = w;
    tmp.h = h;
    tmp.bpr = bpr;
    tmp.ctm = identity;
    tmp.fill[3] = 1.0f; /* opaque black */
    id ctx = rt_objc_alloc(cls_context);
    *CS(ctx) = tmp;
    return ctx;
}

/* ---- drawing ------------------------------------------------------------------------------------------------ */
typedef struct { float x, y, w, h; } rectf;

static rectf rect_std(rectf r) {
    if (r.w < 0) { r.x += r.w; r.w = -r.w; }
    if (r.h < 0) { r.y += r.h; r.h = -r.h; }
    return r;
}

/* the destination pixels whose centres can fall inside user-space rect r: [x0, x1) x [row0, row1) */
static void device_bounds(ctx_state *s, rectf r, int *x0, int *x1, int *row0, int *row1) {
    float xs[4], ys[4];
    x_apply(s->ctm, r.x, r.y, &xs[0], &ys[0]);
    x_apply(s->ctm, r.x + r.w, r.y, &xs[1], &ys[1]);
    x_apply(s->ctm, r.x, r.y + r.h, &xs[2], &ys[2]);
    x_apply(s->ctm, r.x + r.w, r.y + r.h, &xs[3], &ys[3]);
    float minx = xs[0], maxx = xs[0], miny = ys[0], maxy = ys[0];
    for (int k = 1; k < 4; k++) {
        if (xs[k] < minx) minx = xs[k];
        if (xs[k] > maxx) maxx = xs[k];
        if (ys[k] < miny) miny = ys[k];
        if (ys[k] > maxy) maxy = ys[k];
    }
    float fx0 = floorf(minx), fx1 = ceilf(maxx), fy0 = floorf(miny), fy1 = ceilf(maxy);
    *x0 = fx0 < 0 ? 0 : fx0 > s->w ? s->w : (int)fx0;
    *x1 = fx1 < 0 ? 0 : fx1 > s->w ? s->w : (int)fx1;
    /* device y in [fy0, fy1) covers rows h - fy1 .. h - fy0 - 1 */
    float r0 = (float)s->h - fy1, r1 = (float)s->h - fy0;
    *row0 = r0 < 0 ? 0 : r0 > s->h ? s->h : (int)r0;
    *row1 = r1 < 0 ? 0 : r1 > s->h ? s->h : (int)r1;
}

static void fill_rect(ctx_state *s, rectf r) {
    r = rect_std(r);
    xform inv;
    if (!x_invert(s->ctm, &inv) || r.w <= 0 || r.h <= 0) return;
    float a = s->fill[3], src[4] = {s->fill[0] * a, s->fill[1] * a, s->fill[2] * a, a};
    int x0, x1, row0, row1;
    device_bounds(s, r, &x0, &x1, &row0, &row1);
    for (int row = row0; row < row1; row++)
        for (int x = x0; x < x1; x++) {
            float ux, uy;
            x_apply(inv, x + 0.5f, (float)s->h - row - 0.5f, &ux, &uy);
            if (ux >= r.x && ux < r.x + r.w && uy >= r.y && uy < r.y + r.h) px_blend(s, x, row, src);
        }
}

/* bilinear sample at continuous pixel coordinates (pixel centres at k + 0.5), clamped to the edges */
static void sample(const image_state *im, float fx, float fy, float out[4]) {
    fx -= 0.5f;
    fy -= 0.5f;
    if (fx < 0) fx = 0;
    if (fy < 0) fy = 0;
    if (fx > im->w - 1) fx = (float)(im->w - 1);
    if (fy > im->h - 1) fy = (float)(im->h - 1);
    int x0 = (int)fx, y0 = (int)fy;
    int x1 = x0 + 1 < im->w ? x0 + 1 : x0, y1 = y0 + 1 < im->h ? y0 + 1 : y0;
    float tx = fx - x0, ty = fy - y0;
    const uint8_t *p00 = im->px + ((size_t)y0 * im->w + x0) * 4, *p01 = im->px + ((size_t)y0 * im->w + x1) * 4;
    const uint8_t *p10 = im->px + ((size_t)y1 * im->w + x0) * 4, *p11 = im->px + ((size_t)y1 * im->w + x1) * 4;
    for (int k = 0; k < 4; k++) {
        float top = p00[k] + (p01[k] - p00[k]) * tx, bot = p10[k] + (p11[k] - p10[k]) * tx;
        out[k] = (top + (bot - top) * ty) / 255.0f;
    }
}

/* draw `im` into r; flipped = 0: CG convention (image top at the rect's max y), 1: UIKit (top at min y) */
static void draw_image(ctx_state *s, rectf r, const image_state *im, int flipped) {
    r = rect_std(r);
    xform inv;
    if (!im || !im->px || im->w <= 0 || im->h <= 0) return;
    if (!x_invert(s->ctm, &inv) || r.w <= 0 || r.h <= 0) return;
    int x0, x1, row0, row1;
    device_bounds(s, r, &x0, &x1, &row0, &row1);
    float sx = im->w / r.w, sy = im->h / r.h;
    for (int row = row0; row < row1; row++)
        for (int x = x0; x < x1; x++) {
            float ux, uy, p[4];
            x_apply(inv, x + 0.5f, (float)s->h - row - 0.5f, &ux, &uy);
            if (!(ux >= r.x && ux < r.x + r.w && uy >= r.y && uy < r.y + r.h)) continue;
            float u = (ux - r.x) * sx, v = flipped ? (uy - r.y) * sy : (r.y + r.h - uy) * sy;
            sample(im, u, v, p);
            px_blend(s, x, row, p);
        }
}

static void gradient_at(const grad_state *g, float t, float out[4]) {
    int n = g->n;
    float col[4];
    if (t <= g->loc[0]) memcpy(col, g->comp[0], sizeof col);
    else if (t >= g->loc[n - 1]) memcpy(col, g->comp[n - 1], sizeof col);
    else {
        int k = 0;
        while (k + 1 < n - 1 && t > g->loc[k + 1]) k++;
        float span = g->loc[k + 1] - g->loc[k], f = span > 0 ? (t - g->loc[k]) / span : 0;
        for (int i = 0; i < 4; i++) col[i] = g->comp[k][i] + (g->comp[k + 1][i] - g->comp[k][i]) * f;
    }
    float a = col[3];
    out[0] = col[0] * a;
    out[1] = col[1] * a;
    out[2] = col[2] * a;
    out[3] = a;
}

static void draw_linear_gradient(ctx_state *s, const grad_state *g, float sx, float sy, float ex, float ey, uint32_t options) {
    xform inv;
    if (!g->n || !x_invert(s->ctm, &inv)) return;
    float dx = ex - sx, dy = ey - sy, len2 = dx * dx + dy * dy;
    for (int row = 0; row < s->h; row++)
        for (int x = 0; x < s->w; x++) {
            float ux, uy, p[4];
            x_apply(inv, x + 0.5f, (float)s->h - row - 0.5f, &ux, &uy);
            float t = len2 > 0 ? ((ux - sx) * dx + (uy - sy) * dy) / len2 : 0;
            if (t < 0) { if (!(options & 1)) continue; t = 0; }  /* kCGGradientDrawsBeforeStartLocation */
            if (t > 1) { if (!(options & 2)) continue; t = 1; }  /* kCGGradientDrawsAfterEndLocation */
            gradient_at(g, t, p);
            px_blend(s, x, row, p);
        }
}

/* a CGImage (+1) with a copy of the context's pixels */
static id ctx_image(ctx_state *s) {
    uint8_t *px = malloc((size_t)s->w * s->h * 4 + 4);
    if (!px) return 0;
    for (int row = 0; row < s->h; row++)
        for (int x = 0; x < s->w; x++) {
            float p[4];
            px_get(s, x, row, p);
            uint8_t *q = px + ((size_t)row * s->w + x) * 4;
            for (int k = 0; k < 4; k++) q[k] = to_byte(p[k]);
        }
    return image_new(s->w, s->h, px, s->ncomp == 1, s->oa >= 0);
}

/* ---- UIGraphics image contexts --------------------------------------------------------------------------- */
/* UIKit keeps the image-context stack per thread (the game resizes GLLive images on its loading threads), so
 * the stack is thread-local: each host thread sees only the contexts it began. */
#define UIG_MAX 16
static __thread id uig_stack[UIG_MAX];
static __thread int uig_depth;

static id uig_current(void) { return uig_depth ? uig_stack[uig_depth - 1] : 0; }

/* ---- CoreGraphics imports ----------------------------------------------------------------------------------- */
/* CGBitmapContextCreate(data, width, height, bitsPerComponent, bytesPerRow, space, bitmapInfo) */
IMP(CGBitmapContextCreate) {
    uint32_t data = A(0), w = A(1), h = A(2), bpc = A(3), bpr = A(4), info = A(6);
    id space = A(5);
    int ncomp;
    if (!space) ncomp = 0;
    else if (is_a(space, cls_space)) ncomp = SS(space)->gray ? 1 : 3;
    else { rt_log("graphics: CGBitmapContextCreate: not a colour space"); rt_ret(c, 0); return; }
    if (bpc != 8) { rt_log("graphics: CGBitmapContextCreate: %u bits per component is not supported", bpc); rt_ret(c, 0); return; }
    if (!w || !h || w > 16384 || h > 16384) { rt_log("graphics: CGBitmapContextCreate: bad size %ux%u", w, h); rt_ret(c, 0); return; }
    if (!ncomp && (info & 0x1f) != 7) { rt_log("graphics: CGBitmapContextCreate: no colour space"); rt_ret(c, 0); return; }
    id ctx = ctx_new(data, (int)w, (int)h, (int)bpr, ncomp, info);
    if (!ctx) rt_log("graphics: CGBitmapContextCreate: unsupported format (components %d, info 0x%x)", ncomp, info);
    rt_ret(c, ctx);
}
IMP(CGBitmapContextCreateImage) {
    ctx_state *s = ctx_of(A(0));
    rt_ret(c, s ? ctx_image(s) : 0);
}
IMP(CGContextRelease) { rt_release(c, A(0)); }
IMP(CGContextSetRGBFillColor) {
    ctx_state *s = ctx_of(A(0));
    if (!s) return;
    s->fill[0] = F(1);
    s->fill[1] = F(2);
    s->fill[2] = F(3);
    s->fill[3] = F(4);
}
IMP(CGContextFillRect) { /* (ctx, CGRect) */
    ctx_state *s = ctx_of(A(0));
    if (s) fill_rect(s, (rectf){F(1), F(2), F(3), F(4)});
}
IMP(CGContextScaleCTM) {
    ctx_state *s = ctx_of(A(0));
    if (!s) return;
    float sx = F(1), sy = F(2);
    s->ctm.a *= sx;
    s->ctm.b *= sx;
    s->ctm.c *= sy;
    s->ctm.d *= sy;
}
IMP(CGContextTranslateCTM) {
    ctx_state *s = ctx_of(A(0));
    if (!s) return;
    float tx = F(1), ty = F(2);
    xform t = s->ctm;
    s->ctm.tx = t.a * tx + t.c * ty + t.tx;
    s->ctm.ty = t.b * tx + t.d * ty + t.ty;
}
IMP(CGContextDrawImage) { /* (ctx, CGRect, image) */
    ctx_state *s = ctx_of(A(0));
    image_state *im = image_of(A(5));
    if (s && im) draw_image(s, (rectf){F(1), F(2), F(3), F(4)}, im, 0);
}
/* CGGradientCreateWithColorComponents(space, components, locations, count) */
IMP(CGGradientCreateWithColorComponents) {
    id space = A(0);
    uint32_t comps = A(1), locs = A(2), n = A(3);
    if (!is_a(space, cls_space) || !comps || n < 1) { rt_ret(c, 0); return; }
    if (n > GRAD_MAX) { rt_log("graphics: gradient with %u stops (keeping %d)", n, GRAD_MAX); n = GRAD_MAX; }
    id g = rt_objc_alloc(cls_gradient);
    grad_state *s = GS(g);
    s->gray = SS(space)->gray;
    s->n = (int)n;
    int per = s->gray ? 2 : 4;
    for (uint32_t k = 0; k < n; k++) {
        float v[4];
        for (int i = 0; i < per; i++) v[i] = get_f32(comps + 4 * (k * per + i));
        if (s->gray) { s->comp[k][0] = s->comp[k][1] = s->comp[k][2] = v[0]; s->comp[k][3] = v[1]; }
        else memcpy(s->comp[k], v, sizeof v);
        s->loc[k] = locs ? get_f32(locs + 4 * k) : (n > 1 ? (float)k / (float)(n - 1) : 0.0f);
    }
    rt_ret(c, g);
}
/* CGContextDrawLinearGradient(ctx, gradient, CGPoint start, CGPoint end, options) */
IMP(CGContextDrawLinearGradient) {
    ctx_state *s = ctx_of(A(0));
    id g = A(1);
    if (!s || !is_a(g, cls_gradient)) return;
    draw_linear_gradient(s, GS(g), F(2), F(3), F(4), F(5), A(6));
}
IMP(CGColorSpaceCreateDeviceRGB) { rt_ret(c, space_rgb); }
IMP(CGColorSpaceCreateDeviceGray) { rt_ret(c, space_gray); }
IMP(CGColorSpaceRelease) { (void)c; } /* the colour spaces are immortal singletons */

IMP(CGImageGetWidth) { image_state *s = image_of(A(0)); rt_ret(c, s ? (uint32_t)s->w : 0); }
IMP(CGImageGetHeight) { image_state *s = image_of(A(0)); rt_ret(c, s ? (uint32_t)s->h : 0); }
IMP(CGImageGetColorSpace) { image_state *s = image_of(A(0)); rt_ret(c, !s ? 0 : s->gray ? space_gray : space_rgb); }
IMP(CGImageRelease) { rt_release(c, A(0)); }

/* CGImageCreateWithMask(image, mask): a gray mask image's samples act as alpha (white = opaque); the mask is
 * scaled to the image */
IMP(CGImageCreateWithMask) {
    image_state *im = image_of(A(0)), *mk = image_of(A(1));
    if (!im || !mk || !im->px || !mk->px) { rt_ret(c, 0); return; }
    if (!mk->gray) LOG_ONCE("graphics: CGImageCreateWithMask with a non-gray mask (using its luminance)");
    uint8_t *px = malloc((size_t)im->w * im->h * 4 + 4);
    if (!px) { rt_ret(c, 0); return; }
    for (int y = 0; y < im->h; y++) {
        int my = (int)((int64_t)y * mk->h / im->h);
        for (int x = 0; x < im->w; x++) {
            int mx = (int)((int64_t)x * mk->w / im->w);
            const uint8_t *mp = mk->px + ((size_t)my * mk->w + mx) * 4;
            /* the mask's colour is premultiplied by its own alpha: undo that to get the sample */
            uint32_t lum = (mp[0] * 77u + mp[1] * 150u + mp[2] * 29u) >> 8;
            if (mp[3] && mp[3] < 255) lum = lum * 255u / mp[3];
            if (lum > 255) lum = 255;
            const uint8_t *sp = im->px + ((size_t)y * im->w + x) * 4;
            uint8_t *dp = px + ((size_t)y * im->w + x) * 4;
            for (int k = 0; k < 4; k++) dp[k] = (uint8_t)((sp[k] * lum + 127) / 255);
        }
    }
    rt_ret(c, image_new(im->w, im->h, px, im->gray, 1));
}

/* CGAffineTransform results (24 bytes) come back through the hidden pointer in r0. The arguments are read
 * before the result is written: the game passes the same buffer for both (sub_170c40). */
IMP(CGAffineTransformMakeRotation) { uint32_t out = A(0); x_write(out, x_rotation(F(1))); }
IMP(CGAffineTransformMakeScale) { uint32_t out = A(0); x_write(out, (xform){F(1), 0, 0, F(2), 0, 0}); }
IMP(CGAffineTransformMakeTranslation) { uint32_t out = A(0); x_write(out, (xform){1, 0, 0, 1, F(1), F(2)}); }
IMP(CGAffineTransformConcat) { uint32_t out = A(0); xform t1 = x_read(c, 1), t2 = x_read(c, 7); x_write(out, x_concat(t1, t2)); }
IMP(CGAffineTransformRotate) { /* (t, angle): rotate the user space of t, i.e. rotation then t */
    uint32_t out = A(0);
    xform t = x_read(c, 1);
    float angle = F(7);
    x_write(out, x_concat(x_rotation(angle), t));
}
/* CGRectOffset(rect, dx, dy) -> CGRect through r0 */
IMP(CGRectOffset) {
    uint32_t out = A(0);
    float r[4] = {F(1) + F(5), F(2) + F(6), F(3), F(4)};
    memcpy(rt_mem + out, r, 16);
}

/* ---- UIGraphics ----------------------------------------------------------------------------------------- */
static void uig_begin(float w, float h) {
    int iw = (int)ceilf(w), ih = (int)ceilf(h);
    if (iw <= 0 || ih <= 0 || iw > 16384 || ih > 16384) {
        rt_log("graphics: UIGraphicsBeginImageContext: bad size %gx%g", w, h);
        iw = ih = 1;
    }
    id ctx = ctx_new(0, iw, ih, 0, 3, 1 /* kCGImageAlphaPremultipliedLast */);
    if (ctx) CS(ctx)->ctm = (xform){1, 0, 0, -1, 0, (float)ih}; /* UIKit coordinates: origin top-left, y down */
    if (uig_depth == UIG_MAX) { rt_log("graphics: UIGraphics context stack overflow"); rt_release(rt_thread_cpu(), ctx); return; }
    uig_stack[uig_depth++] = ctx;
}
IMP(UIGraphicsBeginImageContext) { (void)c; uig_begin(F(0), F(1)); } /* (CGSize) */
IMP(UIGraphicsGetCurrentContext) { rt_ret(c, uig_current()); }
IMP(UIGraphicsEndImageContext) {
    if (!uig_depth) { LOG_ONCE("graphics: UIGraphicsEndImageContext without a context"); return; }
    id ctx = uig_stack[--uig_depth];
    rt_release(c, ctx);
}

static id uiimage_with_cg(id cg) { /* +1 UIImage retaining cg */
    id ui = rt_objc_alloc(cls_uiimage);
    UIS(ui)->cg = rt_retain(cg);
    return ui;
}

IMP(UIGraphicsGetImageFromCurrentImageContext) {
    id ctx = uig_current();
    ctx_state *s = ctx ? CS(ctx) : NULL;
    id cg = s ? ctx_image(s) : 0;
    if (!cg) { rt_ret(c, 0); return; }
    id ui = uiimage_with_cg(cg);
    rt_release(c, cg);
    rt_ret(c, rt_autorelease(ui));
}

/* ---- inflate (RFC 1951) ----------------------------------------------------------------------------------- */
typedef struct {
    const uint8_t *in;
    size_t inlen, inpos;
    uint32_t bitbuf;
    int bitcnt, err;
    uint8_t *out;
    size_t outlen, outpos;
} inflater;

typedef struct { short count[16]; short symbol[288]; } huffman;

static int inf_bits(inflater *s, int need) {
    uint32_t val = s->bitbuf;
    while (s->bitcnt < need) {
        if (s->inpos >= s->inlen) { s->err = 1; return 0; }
        val |= (uint32_t)s->in[s->inpos++] << s->bitcnt;
        s->bitcnt += 8;
    }
    s->bitbuf = need < 32 ? val >> need : 0;
    s->bitcnt -= need;
    return (int)(val & ((1u << need) - 1));
}

static int inf_decode(inflater *s, const huffman *h) {
    int code = 0, first = 0, index = 0;
    for (int len = 1; len <= 15; len++) {
        code |= inf_bits(s, 1);
        if (s->err) return -1;
        int count = h->count[len];
        if (code - count < first) return h->symbol[index + (code - first)];
        index += count;
        first += count;
        first <<= 1;
        code <<= 1;
    }
    return -1;
}

/* canonical code from lengths: < 0 over-subscribed, 0 complete, > 0 incomplete */
static int inf_construct(huffman *h, const short *length, int n) {
    short offs[16];
    for (int len = 0; len <= 15; len++) h->count[len] = 0;
    for (int sym = 0; sym < n; sym++) h->count[length[sym]]++;
    if (h->count[0] == n) return 0;
    int left = 1;
    for (int len = 1; len <= 15; len++) {
        left <<= 1;
        left -= h->count[len];
        if (left < 0) return left;
    }
    offs[1] = 0;
    for (int len = 1; len < 15; len++) offs[len + 1] = (short)(offs[len] + h->count[len]);
    for (int sym = 0; sym < n; sym++)
        if (length[sym]) h->symbol[offs[length[sym]]++] = (short)sym;
    return left;
}

static int inf_codes(inflater *s, const huffman *lencode, const huffman *distcode) {
    static const short lbase[29] = {3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99,
                                    115, 131, 163, 195, 227, 258};
    static const short lext[29] = {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0};
    static const short dbase[30] = {1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025,
                                    1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577};
    static const short dext[30] = {0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12,
                                   12, 13, 13};
    for (;;) {
        int sym = inf_decode(s, lencode);
        if (sym < 0) return -1;
        if (sym < 256) {
            if (s->outpos >= s->outlen) return -2;
            s->out[s->outpos++] = (uint8_t)sym;
        } else if (sym == 256) {
            return 0;
        } else {
            sym -= 257;
            if (sym >= 29) return -1;
            int len = lbase[sym] + inf_bits(s, lext[sym]);
            sym = inf_decode(s, distcode);
            if (sym < 0 || sym >= 30) return -1;
            size_t dist = (size_t)(dbase[sym] + inf_bits(s, dext[sym]));
            if (s->err || dist > s->outpos) return -1;
            if (s->outpos + (size_t)len > s->outlen) return -2;
            for (int k = 0; k < len; k++, s->outpos++) s->out[s->outpos] = s->out[s->outpos - dist];
        }
    }
}

static int inf_stored(inflater *s) {
    s->bitbuf = 0;
    s->bitcnt = 0;
    if (s->inpos + 4 > s->inlen) return -1;
    unsigned len = s->in[s->inpos] | (unsigned)s->in[s->inpos + 1] << 8;
    unsigned nlen = s->in[s->inpos + 2] | (unsigned)s->in[s->inpos + 3] << 8;
    s->inpos += 4;
    if (len != (~nlen & 0xffffu)) return -1;
    if (s->inpos + len > s->inlen) return -1;
    if (s->outpos + len > s->outlen) return -2;
    memcpy(s->out + s->outpos, s->in + s->inpos, len);
    s->inpos += len;
    s->outpos += len;
    return 0;
}

static int inf_fixed(inflater *s) {
    huffman lencode, distcode;
    short lengths[288];
    int k = 0;
    for (; k < 144; k++) lengths[k] = 8;
    for (; k < 256; k++) lengths[k] = 9;
    for (; k < 280; k++) lengths[k] = 7;
    for (; k < 288; k++) lengths[k] = 8;
    inf_construct(&lencode, lengths, 288);
    for (k = 0; k < 30; k++) lengths[k] = 5;
    inf_construct(&distcode, lengths, 30);
    return inf_codes(s, &lencode, &distcode);
}

static int inf_dynamic(inflater *s) {
    static const short order[19] = {16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15};
    short lengths[320];
    huffman lencode, distcode;
    int nlen = inf_bits(s, 5) + 257, ndist = inf_bits(s, 5) + 1, ncode = inf_bits(s, 4) + 4;
    if (s->err || nlen > 286 || ndist > 30) return -1;
    int index;
    for (index = 0; index < ncode; index++) lengths[order[index]] = (short)inf_bits(s, 3);
    for (; index < 19; index++) lengths[order[index]] = 0;
    if (s->err || inf_construct(&lencode, lengths, 19) != 0) return -1;
    index = 0;
    while (index < nlen + ndist) {
        int sym = inf_decode(s, &lencode);
        if (sym < 0) return -1;
        if (sym < 16) {
            lengths[index++] = (short)sym;
        } else {
            int len = 0, rep;
            if (sym == 16) {
                if (index == 0) return -1;
                len = lengths[index - 1];
                rep = 3 + inf_bits(s, 2);
            } else if (sym == 17) {
                rep = 3 + inf_bits(s, 3);
            } else {
                rep = 11 + inf_bits(s, 7);
            }
            if (s->err || index + rep > nlen + ndist) return -1;
            while (rep--) lengths[index++] = (short)len;
        }
    }
    if (lengths[256] == 0) return -1;
    int err = inf_construct(&lencode, lengths, nlen);
    if (err < 0 || (err > 0 && nlen - lencode.count[0] != 1)) return -1;
    err = inf_construct(&distcode, lengths + nlen, ndist);
    if (err < 0 || (err > 0 && ndist - distcode.count[0] != 1)) return -1;
    return inf_codes(s, &lencode, &distcode);
}

/* raw deflate into out[0..outlen); returns the bytes produced or -1 */
static long inflate_raw(const uint8_t *in, size_t inlen, uint8_t *out, size_t outlen) {
    inflater s;
    memset(&s, 0, sizeof s);
    s.in = in;
    s.inlen = inlen;
    s.out = out;
    s.outlen = outlen;
    int last;
    do {
        last = inf_bits(&s, 1);
        int type = inf_bits(&s, 2);
        if (s.err) return -1;
        int r = type == 0 ? inf_stored(&s) : type == 1 ? inf_fixed(&s) : type == 2 ? inf_dynamic(&s) : -1;
        if (r == -2) return (long)s.outpos; /* more data than the image needs: keep what fits */
        if (r < 0 || s.err) return -1;
    } while (!last);
    return (long)s.outpos;
}

/* ---- PNG decoding ----------------------------------------------------------------------------------------- */
static uint32_t be32(const uint8_t *p) { return (uint32_t)p[0] << 24 | (uint32_t)p[1] << 16 | (uint32_t)p[2] << 8 | p[3]; }

static int paeth(int a, int b, int c) {
    int p = a + b - c, pa = abs(p - a), pb = abs(p - b), pc = abs(p - c);
    return pa <= pb && pa <= pc ? a : pb <= pc ? b : c;
}

/* sample k of a row at bit depth bd (16-bit samples keep their high byte; low depths scale to 0-255 unless
 * `raw` asks for the index) */
static int png_sample(const uint8_t *row, int k, int bd, int raw) {
    switch (bd) {
    case 8: return row[k];
    case 16: return row[2 * k];
    default: {
        int per = 8 / bd, shift = 8 - bd * (k % per + 1), v = (row[k / per] >> shift) & ((1 << bd) - 1);
        return raw ? v : v * 255 / ((1 << bd) - 1);
    }
    }
}
static int png_sample16(const uint8_t *row, int k, int bd) { /* the full value, for tRNS colour keys */
    if (bd == 16) return row[2 * k] << 8 | row[2 * k + 1];
    return png_sample(row, k, bd, 1);
}

/* decode a PNG into a new CGImage (+1), or 0 */
static id png_decode(const uint8_t *p, size_t n, const char *what) {
    if (n < 8 || memcmp(p, "\x89PNG\r\n\x1a\n", 8)) return 0;
    uint32_t w = 0, h = 0;
    int bd = 0, ct = -1, interlace = 0, cgbi = 0, have_ihdr = 0;
    uint8_t plte[256][4];
    int nplte = 0, has_trns = 0, trns_key[3] = {-1, -1, -1};
    for (int k = 0; k < 256; k++) { plte[k][0] = plte[k][1] = plte[k][2] = 0; plte[k][3] = 255; }
    uint8_t *idat = NULL;
    size_t nidat = 0;
    size_t pos = 8;
    while (pos + 12 <= n) {
        uint32_t len = be32(p + pos);
        const uint8_t *type = p + pos + 4, *d = p + pos + 8;
        if (len > n - pos - 12) break;
        if (!memcmp(type, "CgBI", 4)) cgbi = 1;
        else if (!memcmp(type, "IHDR", 4) && len >= 13) {
            w = be32(d);
            h = be32(d + 4);
            bd = d[8];
            ct = d[9];
            interlace = d[12];
            have_ihdr = 1;
        } else if (!memcmp(type, "PLTE", 4)) {
            nplte = (int)(len / 3 > 256 ? 256 : len / 3);
            for (int k = 0; k < nplte; k++) { plte[k][0] = d[3 * k]; plte[k][1] = d[3 * k + 1]; plte[k][2] = d[3 * k + 2]; }
        } else if (!memcmp(type, "tRNS", 4)) {
            has_trns = 1;
            if (ct == 3) for (uint32_t k = 0; k < len && k < 256; k++) plte[k][3] = d[k];
            else if (ct == 0 && len >= 2) trns_key[0] = d[0] << 8 | d[1];
            else if (ct == 2 && len >= 6) for (int k = 0; k < 3; k++) trns_key[k] = d[2 * k] << 8 | d[2 * k + 1];
        } else if (!memcmp(type, "IDAT", 4)) {
            uint8_t *grown = realloc(idat, nidat + len + 1);
            if (!grown) { free(idat); return 0; }
            idat = grown;
            memcpy(idat + nidat, d, len);
            nidat += len;
        } else if (!memcmp(type, "IEND", 4)) {
            break;
        }
        pos += 12 + len;
    }
    int channels = ct == 0 ? 1 : ct == 2 ? 3 : ct == 3 ? 1 : ct == 4 ? 2 : ct == 6 ? 4 : 0;
    int bd_ok = bd == 8 || bd == 16 || ((ct == 0 || ct == 3) && (bd == 1 || bd == 2 || bd == 4));
    if (!have_ihdr || !channels || !bd_ok || (ct == 3 && bd == 16)) {
        rt_log("graphics: %s: unsupported PNG (colour type %d, depth %d)", what, ct, bd);
        free(idat);
        return 0;
    }
    if (interlace) { rt_log("graphics: %s: interlaced PNG is not supported", what); free(idat); return 0; }
    if (!w || !h || w > 8192 || h > 8192 || !idat) { rt_log("graphics: %s: bad PNG (%ux%u)", what, w, h); free(idat); return 0; }
    size_t bpp_bits = (size_t)channels * bd, rowbytes = (w * bpp_bits + 7) / 8, fbpp = bpp_bits < 8 ? 1 : bpp_bits / 8;
    size_t rawlen = (rowbytes + 1) * h;
    uint8_t *raw = malloc(rawlen);
    if (!raw) { free(idat); return 0; }
    long got;
    if (cgbi) got = inflate_raw(idat, nidat, raw, rawlen);
    else if (nidat >= 2 && (idat[0] & 0x0f) == 8 && !(idat[1] & 0x20)) got = inflate_raw(idat + 2, nidat - 2, raw, rawlen);
    else got = -1;
    free(idat);
    if (got < (long)rawlen) {
        if (got < 0) { rt_log("graphics: %s: corrupt PNG data", what); free(raw); return 0; }
        rt_log("graphics: %s: PNG data is short (%ld of %zu bytes)", what, got, rawlen);
        memset(raw + got, 0, rawlen - (size_t)got);
    }
    /* undo the row filters in place */
    for (uint32_t y = 0; y < h; y++) {
        uint8_t *row = raw + y * (rowbytes + 1), *cur = row + 1;
        const uint8_t *prev = y ? raw + (y - 1) * (rowbytes + 1) + 1 : NULL;
        int f = row[0];
        for (size_t i = 0; i < rowbytes; i++) {
            int a = i >= fbpp ? cur[i - fbpp] : 0, b = prev ? prev[i] : 0, cc = (prev && i >= fbpp) ? prev[i - fbpp] : 0;
            switch (f) {
            case 0: break;
            case 1: cur[i] = (uint8_t)(cur[i] + a); break;
            case 2: cur[i] = (uint8_t)(cur[i] + b); break;
            case 3: cur[i] = (uint8_t)(cur[i] + ((a + b) >> 1)); break;
            case 4: cur[i] = (uint8_t)(cur[i] + paeth(a, b, cc)); break;
            default: if (i == 0) LOG_ONCE("graphics: %s: bad PNG filter %d", what, f); break;
            }
        }
    }
    uint8_t *px = malloc((size_t)w * h * 4);
    if (!px) { free(raw); return 0; }
    int alpha = ct == 4 || ct == 6 || has_trns;
    for (uint32_t y = 0; y < h; y++) {
        const uint8_t *row = raw + y * (rowbytes + 1) + 1;
        for (uint32_t x = 0; x < w; x++) {
            uint8_t *q = px + ((size_t)y * w + x) * 4;
            int r, g, b, a = 255;
            switch (ct) {
            case 0:
                r = g = b = png_sample(row, (int)x, bd, 0);
                if (trns_key[0] >= 0 && png_sample16(row, (int)x, bd) == trns_key[0]) a = 0;
                break;
            case 2:
                r = png_sample(row, 3 * (int)x, bd, 0);
                g = png_sample(row, 3 * (int)x + 1, bd, 0);
                b = png_sample(row, 3 * (int)x + 2, bd, 0);
                if (trns_key[0] >= 0 && png_sample16(row, 3 * (int)x, bd) == trns_key[0] &&
                    png_sample16(row, 3 * (int)x + 1, bd) == trns_key[1] && png_sample16(row, 3 * (int)x + 2, bd) == trns_key[2])
                    a = 0;
                break;
            case 3: {
                int k = png_sample(row, (int)x, bd, 1);
                r = plte[k][0]; g = plte[k][1]; b = plte[k][2]; a = plte[k][3];
                break;
            }
            case 4:
                r = g = b = png_sample(row, 2 * (int)x, bd, 0);
                a = png_sample(row, 2 * (int)x + 1, bd, 0);
                break;
            default:
                r = png_sample(row, 4 * (int)x, bd, 0);
                g = png_sample(row, 4 * (int)x + 1, bd, 0);
                b = png_sample(row, 4 * (int)x + 2, bd, 0);
                a = png_sample(row, 4 * (int)x + 3, bd, 0);
                break;
            }
            if (cgbi) { /* BGRA, already premultiplied */
                int t = r; r = b; b = t;
                q[0] = (uint8_t)r; q[1] = (uint8_t)g; q[2] = (uint8_t)b; q[3] = (uint8_t)a;
            } else {
                q[0] = (uint8_t)((r * a + 127) / 255);
                q[1] = (uint8_t)((g * a + 127) / 255);
                q[2] = (uint8_t)((b * a + 127) / 255);
                q[3] = (uint8_t)a;
            }
        }
    }
    free(raw);
    return image_new((int)w, (int)h, px, 0, alpha);
}

/* a CGImage (+1) from encoded bytes */
static id image_decode(const uint8_t *p, size_t n, const char *what) {
    if (n >= 8 && !memcmp(p, "\x89PNG", 4)) return png_decode(p, n, what);
    if (n >= 3 && p[0] == 0xff && p[1] == 0xd8 && p[2] == 0xff) {
        rt_log("graphics: %s: JPEG decoding is not supported (nil image)", what);
        return 0;
    }
    rt_log("graphics: %s: unknown image format (%zu bytes)", what, n);
    return 0;
}

static id image_from_file(const char *path) {
    const char *host = rt_host_path(path);
    FILE *f = fopen(host, "rb");
    if (!f) { if (rt_verbose) rt_log("graphics: no image file %s", path); return 0; }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    id img = 0;
    uint8_t *buf = n > 0 ? malloc((size_t)n) : NULL;
    if (buf && fread(buf, 1, (size_t)n, f) == (size_t)n) img = image_decode(buf, (size_t)n, path);
    free(buf);
    fclose(f);
    return img;
}

/* ---- PNG and JPEG encoding -------------------------------------------------------------------------------- */
typedef struct { uint8_t *p; size_t n, cap; } buf;

static void b_put(buf *b, const void *d, size_t n) {
    if (b->n + n > b->cap) {
        size_t cap = b->cap ? b->cap * 2 : 4096;
        while (cap < b->n + n) cap *= 2;
        uint8_t *q = realloc(b->p, cap);
        if (!q) return;
        b->p = q;
        b->cap = cap;
    }
    memcpy(b->p + b->n, d, n);
    b->n += n;
}
static void b_byte(buf *b, uint8_t v) { b_put(b, &v, 1); }
static void b_be16(buf *b, uint32_t v) { uint8_t t[2] = {(uint8_t)(v >> 8), (uint8_t)v}; b_put(b, t, 2); }
static void b_be32(buf *b, uint32_t v) { uint8_t t[4] = {(uint8_t)(v >> 24), (uint8_t)(v >> 16), (uint8_t)(v >> 8), (uint8_t)v}; b_put(b, t, 4); }

static uint32_t crc32_of(const uint8_t *p, size_t n) {
    uint32_t table[256]; /* built per call (cheap): no lazily-initialised global shared between threads */
    for (uint32_t k = 0; k < 256; k++) {
        uint32_t v = k;
        for (int i = 0; i < 8; i++) v = v & 1 ? 0xedb88320u ^ (v >> 1) : v >> 1;
        table[k] = v;
    }
    uint32_t crc = 0xffffffffu;
    for (size_t k = 0; k < n; k++) crc = table[(crc ^ p[k]) & 0xff] ^ (crc >> 8);
    return crc ^ 0xffffffffu;
}

static void png_chunk(buf *b, const char *type, const uint8_t *d, size_t n) {
    b_be32(b, (uint32_t)n);
    size_t start = b->n;
    b_put(b, type, 4);
    if (n) b_put(b, d, n);
    b_be32(b, b->p ? crc32_of(b->p + start, n + 4) : 0);
}

/* RGBA (straight alpha) or RGB, 8 bits, zlib stored blocks */
static id png_encode(const image_state *im) {
    int ch = im->alpha ? 4 : 3;
    size_t rowlen = (size_t)im->w * ch + 1, rawlen = rowlen * im->h;
    uint8_t *raw = malloc(rawlen);
    if (!raw) return 0;
    for (int y = 0; y < im->h; y++) {
        uint8_t *row = raw + y * rowlen;
        row[0] = 0;
        for (int x = 0; x < im->w; x++) {
            const uint8_t *s = im->px + ((size_t)y * im->w + x) * 4;
            uint8_t *d = row + 1 + (size_t)x * ch;
            int a = s[3];
            for (int k = 0; k < 3; k++) { /* back to straight alpha */
                int v = s[k];
                if (im->alpha && a < 255) v = a ? (s[k] * 255 + a / 2) / a : 0;
                d[k] = (uint8_t)(v > 255 ? 255 : v);
            }
            if (ch == 4) d[3] = (uint8_t)a;
        }
    }
    buf z = {0};
    b_byte(&z, 0x78);
    b_byte(&z, 0x01);
    uint32_t s1 = 1, s2 = 0;
    for (size_t k = 0; k < rawlen; k++) { s1 = (s1 + raw[k]) % 65521u; s2 = (s2 + s1) % 65521u; }
    for (size_t off = 0; off < rawlen;) { /* rawlen > 0: at least one row */
        size_t len = rawlen - off > 65535 ? 65535 : rawlen - off;
        b_byte(&z, off + len >= rawlen ? 1 : 0); /* BFINAL on the last block, BTYPE 00 (stored) */
        uint8_t hdr[4] = {(uint8_t)len, (uint8_t)(len >> 8), (uint8_t)~len, (uint8_t)(~len >> 8)};
        b_put(&z, hdr, 4);
        b_put(&z, raw + off, len);
        off += len;
    }
    b_be32(&z, s2 << 16 | s1);
    free(raw);

    buf b = {0};
    b_put(&b, "\x89PNG\r\n\x1a\n", 8);
    uint8_t ihdr[13];
    uint32_t w = (uint32_t)im->w, h = (uint32_t)im->h;
    uint8_t t[8] = {(uint8_t)(w >> 24), (uint8_t)(w >> 16), (uint8_t)(w >> 8), (uint8_t)w,
                    (uint8_t)(h >> 24), (uint8_t)(h >> 16), (uint8_t)(h >> 8), (uint8_t)h};
    memcpy(ihdr, t, 8);
    ihdr[8] = 8;
    ihdr[9] = (uint8_t)(ch == 4 ? 6 : 2);
    ihdr[10] = ihdr[11] = ihdr[12] = 0;
    png_chunk(&b, "IHDR", ihdr, 13);
    png_chunk(&b, "IDAT", z.p, z.n);
    png_chunk(&b, "IEND", NULL, 0);
    free(z.p);
    id data = b.p ? rt_nsdata_new(b.p, (uint32_t)b.n) : 0;
    free(b.p);
    return data;
}

/* baseline JPEG: YCbCr 4:4:4, one quantisation table and the standard luminance Huffman tables (JPEG spec K.3)
 * shared by the three components */
static const uint8_t jpg_zigzag[64] = {0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48,
                                       41, 34, 27, 20, 13, 6, 7, 14, 21, 28, 35, 42, 49, 56, 57, 50, 43, 36, 29, 22,
                                       15, 23, 30, 37, 44, 51, 58, 59, 52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55,
                                       62, 63};
static const uint8_t jpg_lum_q[64] = {16, 11, 10, 16, 24, 40, 51, 61, 12, 12, 14, 19, 26, 58, 60, 55,
                                      14, 13, 16, 24, 40, 57, 69, 56, 14, 17, 22, 29, 51, 87, 80, 62,
                                      18, 22, 37, 56, 68, 109, 103, 77, 24, 35, 55, 64, 81, 104, 113, 92,
                                      49, 64, 78, 87, 103, 121, 120, 101, 72, 92, 95, 98, 112, 100, 103, 99};
static const uint8_t jpg_dc_bits[16] = {0, 1, 5, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0};
static const uint8_t jpg_dc_vals[12] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11};
static const uint8_t jpg_ac_bits[16] = {0, 2, 1, 3, 3, 2, 4, 3, 5, 5, 4, 4, 0, 0, 1, 0x7d};
static const uint8_t jpg_ac_vals[162] = {
    0x01, 0x02, 0x03, 0x00, 0x04, 0x11, 0x05, 0x12, 0x21, 0x31, 0x41, 0x06, 0x13, 0x51, 0x61, 0x07, 0x22, 0x71, 0x14,
    0x32, 0x81, 0x91, 0xa1, 0x08, 0x23, 0x42, 0xb1, 0xc1, 0x15, 0x52, 0xd1, 0xf0, 0x24, 0x33, 0x62, 0x72, 0x82, 0x09,
    0x0a, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a,
    0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x63, 0x64, 0x65,
    0x66, 0x67, 0x68, 0x69, 0x6a, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88,
    0x89, 0x8a, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9,
    0xaa, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca,
    0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea,
    0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa};

typedef struct {
    buf *b;
    uint32_t acc;
    int n;
    uint16_t dc_code[12], ac_code[256];
    uint8_t dc_len[12], ac_len[256];
    float cosv[8][8]; /* DCT basis, filled by jpeg_encode (per call: no shared lazily-initialised table) */
} jpg_writer;

static void jpg_bits(jpg_writer *w, uint32_t code, int len) {
    w->acc = (w->acc << len) | (code & ((1u << len) - 1));
    w->n += len;
    while (w->n >= 8) {
        uint8_t v = (uint8_t)(w->acc >> (w->n - 8));
        b_byte(w->b, v);
        if (v == 0xff) b_byte(w->b, 0);
        w->n -= 8;
    }
    w->acc &= (1u << w->n) - 1;
}

static void jpg_table(const uint8_t *bits, const uint8_t *vals, uint16_t *codes, uint8_t *lens) {
    int code = 0, k = 0;
    for (int len = 1; len <= 16; len++) {
        for (int i = 0; i < bits[len - 1]; i++, k++) {
            codes[vals[k]] = (uint16_t)code++;
            lens[vals[k]] = (uint8_t)len;
        }
        code <<= 1;
    }
}

static int jpg_category(int v) { int a = v < 0 ? -v : v, n = 0; while (a) { n++; a >>= 1; } return n; }

static void jpg_block(jpg_writer *w, const float in[64], const float qt[64], int *prev_dc) {
    const float (*cosv)[8] = (const float (*)[8])w->cosv;
    float tmp[64], coef[64];
    for (int y = 0; y < 8; y++) /* rows */
        for (int u = 0; u < 8; u++) {
            float s = 0;
            for (int x = 0; x < 8; x++) s += in[y * 8 + x] * cosv[x][u];
            tmp[y * 8 + u] = s * (u ? 0.5f : 0.35355339f);
        }
    for (int u = 0; u < 8; u++) /* columns */
        for (int v = 0; v < 8; v++) {
            float s = 0;
            for (int y = 0; y < 8; y++) s += tmp[y * 8 + u] * cosv[y][v];
            coef[v * 8 + u] = s * (v ? 0.5f : 0.35355339f);
        }
    int q[64];
    for (int k = 0; k < 64; k++) {
        int nat = jpg_zigzag[k];
        q[k] = (int)lroundf(coef[nat] / qt[nat]);
    }
    int diff = q[0] - *prev_dc, cat = jpg_category(diff);
    *prev_dc = q[0];
    jpg_bits(w, w->dc_code[cat], w->dc_len[cat]);
    if (cat) jpg_bits(w, (uint32_t)(diff < 0 ? diff + (1 << cat) - 1 : diff), cat);
    int run = 0;
    for (int k = 1; k < 64; k++) {
        if (!q[k]) { run++; continue; }
        while (run > 15) { jpg_bits(w, w->ac_code[0xf0], w->ac_len[0xf0]); run -= 16; }
        cat = jpg_category(q[k]);
        if (cat > 10) cat = 10, q[k] = q[k] < 0 ? -1023 : 1023;
        int sym = run << 4 | cat;
        jpg_bits(w, w->ac_code[sym], w->ac_len[sym]);
        jpg_bits(w, (uint32_t)(q[k] < 0 ? q[k] + (1 << cat) - 1 : q[k]), cat);
        run = 0;
    }
    if (run) jpg_bits(w, w->ac_code[0], w->ac_len[0]);
}

static id jpeg_encode(const image_state *im, float quality) {
    int qual = (int)lroundf(quality * 100.0f);
    if (qual < 1) qual = 1;
    if (qual > 100) qual = 100;
    int scale = qual < 50 ? 5000 / qual : 200 - 2 * qual;
    float qt[64];
    uint8_t qz[64];
    for (int k = 0; k < 64; k++) {
        int v = (jpg_lum_q[k] * scale + 50) / 100;
        v = v < 1 ? 1 : v > 255 ? 255 : v;
        qt[k] = (float)v;
    }
    for (int k = 0; k < 64; k++) qz[k] = (uint8_t)qt[jpg_zigzag[k]];
    buf b = {0};
    static const uint8_t app0[18] = {0xff, 0xe0, 0, 16, 'J', 'F', 'I', 'F', 0, 1, 1, 0, 0, 1, 0, 1, 0, 0};
    b_byte(&b, 0xff); b_byte(&b, 0xd8);
    b_put(&b, app0, sizeof app0);
    b_byte(&b, 0xff); b_byte(&b, 0xdb); b_be16(&b, 67); b_byte(&b, 0); b_put(&b, qz, 64);
    b_byte(&b, 0xff); b_byte(&b, 0xc0); b_be16(&b, 17); b_byte(&b, 8);
    b_be16(&b, (uint32_t)im->h); b_be16(&b, (uint32_t)im->w); b_byte(&b, 3);
    for (int k = 1; k <= 3; k++) { b_byte(&b, (uint8_t)k); b_byte(&b, 0x11); b_byte(&b, 0); }
    b_byte(&b, 0xff); b_byte(&b, 0xc4); b_be16(&b, 2 + 17 + 12 + 17 + 162);
    b_byte(&b, 0x00); b_put(&b, jpg_dc_bits, 16); b_put(&b, jpg_dc_vals, 12);
    b_byte(&b, 0x10); b_put(&b, jpg_ac_bits, 16); b_put(&b, jpg_ac_vals, 162);
    b_byte(&b, 0xff); b_byte(&b, 0xda); b_be16(&b, 12); b_byte(&b, 3);
    for (int k = 1; k <= 3; k++) { b_byte(&b, (uint8_t)k); b_byte(&b, 0x00); }
    b_byte(&b, 0); b_byte(&b, 63); b_byte(&b, 0);

    jpg_writer w;
    memset(&w, 0, sizeof w);
    w.b = &b;
    for (int x = 0; x < 8; x++)
        for (int u = 0; u < 8; u++) w.cosv[x][u] = cosf((2 * x + 1) * u * 3.14159265f / 16.0f);
    jpg_table(jpg_dc_bits, jpg_dc_vals, w.dc_code, w.dc_len);
    jpg_table(jpg_ac_bits, jpg_ac_vals, w.ac_code, w.ac_len);
    int dc[3] = {0, 0, 0};
    for (int by = 0; by < im->h; by += 8)
        for (int bx = 0; bx < im->w; bx += 8) {
            float blk[3][64];
            for (int y = 0; y < 8; y++)
                for (int x = 0; x < 8; x++) {
                    int sx = bx + x < im->w ? bx + x : im->w - 1, sy = by + y < im->h ? by + y : im->h - 1;
                    const uint8_t *s = im->px + ((size_t)sy * im->w + sx) * 4; /* premultiplied: over black */
                    float r = s[0], g = s[1], bl = s[2];
                    blk[0][y * 8 + x] = 0.299f * r + 0.587f * g + 0.114f * bl - 128.0f;
                    blk[1][y * 8 + x] = -0.168736f * r - 0.331264f * g + 0.5f * bl;
                    blk[2][y * 8 + x] = 0.5f * r - 0.418688f * g - 0.081312f * bl;
                }
            for (int k = 0; k < 3; k++) jpg_block(&w, blk[k], qt, &dc[k]);
        }
    if (w.n) jpg_bits(&w, 0x7f, 8 - w.n); /* pad with ones */
    b_byte(&b, 0xff); b_byte(&b, 0xd9);
    id data = b.p ? rt_nsdata_new(b.p, (uint32_t)b.n) : 0;
    free(b.p);
    return data;
}

static image_state *uiimage_cg_state(id ui) {
    if (!is_a(ui, cls_uiimage)) return NULL;
    uiimage_state *s = rt_objc_state_peek(ui);
    return s ? image_of(s->cg) : NULL;
}
IMP(UIImagePNGRepresentation) {
    image_state *im = uiimage_cg_state(A(0));
    id data = im && im->px ? png_encode(im) : 0;
    rt_ret(c, data ? rt_autorelease(data) : 0);
}
IMP(UIImageJPEGRepresentation) { /* (image, CGFloat quality) */
    image_state *im = uiimage_cg_state(A(0));
    id data = im && im->px ? jpeg_encode(im, F(1)) : 0;
    rt_ret(c, data ? rt_autorelease(data) : 0);
}

/* ---- UIImage ---------------------------------------------------------------------------------------------- */
/* an initializer's result: self holding cg (+1 consumed), or nil (self released) */
static void init_with(cpu_t *c, id cg) {
    id self = SELF;
    if (!cg) { rt_release(c, self); rt_ret(c, 0); return; }
    uiimage_state *s = UIS(self);
    id old = s->cg;
    s->cg = cg;
    rt_release(c, old);
    rt_ret(c, self);
}
static id uiimage_new_or_nil(id cg) { /* autoreleased UIImage consuming cg (+1), or nil */
    if (!cg) return 0;
    id ui = rt_objc_alloc(cls_uiimage);
    UIS(ui)->cg = cg;
    return rt_autorelease(ui);
}
static id cg_from_data(id data, const char *what) {
    uint32_t bytes = rt_nsdata_bytes(data), n = rt_nsdata_len(data);
    if (!data || !bytes || !n) return 0;
    return image_decode(rt_mem + bytes, n, what);
}
static id cg_from_path(id path) {
    const char *p = rt_nsstring_utf8(path);
    return p && *p ? image_from_file(p) : 0;
}

M(ui_image_named) {
    (void)m;
    const char *name = rt_nsstring_utf8(ARG(0));
    if (!name || !*name) { rt_ret(c, 0); return; }
    char path[1024];
    snprintf(path, sizeof path, "%s/%s", rt_bundle_path, name);
    id cg = image_from_file(path);
    if (!cg && !strchr(name, '.')) {
        snprintf(path, sizeof path, "%s/%s.png", rt_bundle_path, name);
        cg = image_from_file(path);
    }
    if (!cg) rt_log("graphics: +[UIImage imageNamed:%s]: not found", name);
    rt_ret(c, uiimage_new_or_nil(cg));
}
M(ui_image_with_file) { (void)m; rt_ret(c, uiimage_new_or_nil(cg_from_path(ARG(0)))); }
M(ui_image_with_data) { (void)m; rt_ret(c, uiimage_new_or_nil(cg_from_data(ARG(0), "+[UIImage imageWithData:]"))); }
M(ui_image_with_cg) { (void)m; id cg = ARG(0); rt_ret(c, image_of(cg) ? uiimage_new_or_nil(rt_retain(cg)) : 0); }
M(ui_init_file) { (void)m; init_with(c, cg_from_path(ARG(0))); }
M(ui_init_data) { (void)m; init_with(c, cg_from_data(ARG(0), "-[UIImage initWithData:]")); }
M(ui_init_cg) { (void)m; id cg = ARG(0); init_with(c, image_of(cg) ? rt_retain(cg) : 0); }
M(ui_cgimage) { (void)m; uiimage_state *s = rt_objc_state_peek(SELF); rt_ret(c, s ? s->cg : 0); }
M(ui_size) { /* stret: r0 result, r1 self */
    (void)m;
    image_state *im = uiimage_cg_state(c->r[1]);
    put_f32(c->r[0], im ? (float)im->w : 0);
    put_f32(c->r[0] + 4, im ? (float)im->h : 0);
}
M(ui_scale) { (void)m; rt_fret(c, 1.0f); }
M(ui_orientation) { (void)m; rt_ret(c, 0); } /* UIImageOrientationUp */
M(ui_stretchable) { (void)m; (void)c; }   /* stretchableImageWithLeftCapWidth:topCapHeight: -> self */
static void ui_draw(cpu_t *c, rectf r) {
    image_state *im = uiimage_cg_state(SELF);
    id ctx = uig_current();
    if (!ctx) { LOG_ONCE("graphics: -[UIImage draw...] with no current context"); return; }
    if (im) draw_image(CS(ctx), r, im, 1);
}
M(ui_draw_in_rect) { (void)m; ui_draw(c, (rectf){FARG(0), FARG(1), FARG(2), FARG(3)}); }
M(ui_draw_at_point) {
    (void)m;
    image_state *im = uiimage_cg_state(SELF);
    if (im) ui_draw(c, (rectf){FARG(0), FARG(1), (float)im->w, (float)im->h});
}

/* ---- UIColor ---------------------------------------------------------------------------------------------- */
static id color_new(float r, float g, float b, float a) { /* +1 */
    id o = rt_objc_alloc(cls_uicolor);
    color_state *s = COL(o);
    s->r = r; s->g = g; s->b = b; s->a = a;
    return o;
}
/* shared colours (+[UIColor blackColor], ...) are made once and kept */
typedef struct { const char *sel; float r, g, b, a; id obj; } named_color;
static named_color named_colors[] = {
    {"blackColor", 0, 0, 0, 1, 0}, {"whiteColor", 1, 1, 1, 1, 0}, {"clearColor", 0, 0, 0, 0, 0},
    {"grayColor", 0.5f, 0.5f, 0.5f, 1, 0}, {"darkGrayColor", 1 / 3.0f, 1 / 3.0f, 1 / 3.0f, 1, 0},
    {"lightGrayColor", 2 / 3.0f, 2 / 3.0f, 2 / 3.0f, 1, 0}, {"redColor", 1, 0, 0, 1, 0}, {"greenColor", 0, 1, 0, 1, 0},
    {"blueColor", 0, 0, 1, 1, 0}, {"yellowColor", 1, 1, 0, 1, 0}, {"cyanColor", 0, 1, 1, 1, 0},
    {"magentaColor", 1, 0, 1, 1, 0}, {"orangeColor", 1, 0.5f, 0, 1, 0}, {"purpleColor", 0.5f, 0, 0.5f, 1, 0},
    {"brownColor", 0.6f, 0.4f, 0.2f, 1, 0}, {"groupTableViewBackgroundColor", 0.77f, 0.8f, 0.84f, 1, 0},
};
M(col_named) {
    (void)m;
    const char *sel = rt_sel_name(c->r[1]);
    for (size_t k = 0; k < sizeof named_colors / sizeof *named_colors; k++) {
        named_color *n = &named_colors[k];
        if (sel && !strcmp(sel, n->sel)) {
            id obj = __atomic_load_n(&n->obj, __ATOMIC_ACQUIRE);
            if (!obj) { /* first use; two threads may race: the loser releases its copy */
                id made = color_new(n->r, n->g, n->b, n->a), expected = 0;
                if (__atomic_compare_exchange_n(&n->obj, &expected, made, 0, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) obj = made;
                else { rt_release(c, made); obj = expected; }
            }
            rt_ret(c, obj);
            return;
        }
    }
    rt_ret(c, 0);
}
M(col_rgba) { (void)m; rt_ret(c, rt_autorelease(color_new(FARG(0), FARG(1), FARG(2), FARG(3)))); }
M(col_white) { (void)m; float w = FARG(0); rt_ret(c, rt_autorelease(color_new(w, w, w, FARG(1)))); }
M(col_init_rgba) { (void)m; color_state *s = COL(SELF); s->r = FARG(0); s->g = FARG(1); s->b = FARG(2); s->a = FARG(3); }
M(col_init_white) { (void)m; color_state *s = COL(SELF); s->r = s->g = s->b = FARG(0); s->a = FARG(1); }
M(col_with_alpha) { (void)m; color_state *s = COL(SELF); rt_ret(c, rt_autorelease(color_new(s->r, s->g, s->b, FARG(0)))); }
M(col_set_fill) {
    (void)m;
    id ctx = uig_current();
    if (!ctx) return;
    color_state *s = COL(SELF);
    ctx_state *cs = CS(ctx);
    cs->fill[0] = s->r; cs->fill[1] = s->g; cs->fill[2] = s->b; cs->fill[3] = s->a;
}

/* ---- UIFont ----------------------------------------------------------------------------------------------- */
static id font_new(const char *name, float size, int bold, int italic) { /* autoreleased */
    id o = rt_objc_alloc(cls_uifont);
    font_state *s = FS(o);
    snprintf(s->name, sizeof s->name, "%s", name);
    s->size = size > 0 ? size : 12.0f;
    s->bold = bold || strstr(name, "Bold") != NULL;
    s->italic = italic || strstr(name, "Oblique") != NULL || strstr(name, "Italic") != NULL;
    return rt_autorelease(o);
}
M(font_system) { (void)m; rt_ret(c, font_new("Helvetica", FARG(0), 0, 0)); }
M(font_bold) { (void)m; rt_ret(c, font_new("Helvetica-Bold", FARG(0), 1, 0)); }
M(font_italic) { (void)m; rt_ret(c, font_new("Helvetica-Oblique", FARG(0), 0, 1)); }
M(font_named) { /* fontWithName:size: (real UIKit returns nil for unknown names; every name is accepted here) */
    (void)m;
    const char *name = rt_nsstring_utf8(ARG(0));
    rt_ret(c, font_new(name && *name ? name : "Helvetica", FARG(1), 0, 0));
}
M(font_label_size) { (void)m; rt_fret(c, 17.0f); }
M(font_button_size) { (void)m; rt_fret(c, 18.0f); }
M(font_system_size) { (void)m; rt_fret(c, 14.0f); }
M(font_small_size) { (void)m; rt_fret(c, 12.0f); }
M(font_with_size) { (void)m; font_state *s = FS(SELF); rt_ret(c, font_new(s->name, FARG(0), s->bold, s->italic)); }
M(font_point_size) { (void)m; rt_fret(c, FS(SELF)->size); }
M(font_name) { (void)m; rt_ret(c, rt_nsstring(FS(SELF)->name)); }
M(font_family) { (void)m; rt_ret(c, rt_nsstring("Helvetica")); }
M(font_ascender) { (void)m; rt_fret(c, FS(SELF)->size * 0.77f); }
M(font_descender) { (void)m; rt_fret(c, FS(SELF)->size * -0.23f); }
M(font_cap_height) { (void)m; rt_fret(c, FS(SELF)->size * 0.717f); }
M(font_x_height) { (void)m; rt_fret(c, FS(SELF)->size * 0.523f); }
M(font_line_height) { (void)m; rt_fret(c, ceilf(FS(SELF)->size * 1.2f)); }
M(font_leading) { (void)m; rt_fret(c, ceilf(FS(SELF)->size * 1.2f)); }

/* Helvetica advance widths in em, roughly by character class */
static float char_em(unsigned char ch) {
    if (ch == ' ') return 0.278f;
    if (ch >= '0' && ch <= '9') return 0.556f;
    if (strchr("il.,:;'|!", ch)) return 0.24f;
    if (strchr("jft()[]/-", ch)) return 0.3f;
    if (ch == 'r') return 0.333f;
    if (ch == 'm') return 0.833f;
    if (ch == 'w') return 0.722f;
    if (ch == 'M' || ch == 'W') return 0.86f;
    if (ch == 'I') return 0.278f;
    if (ch >= 'A' && ch <= 'Z') return 0.667f;
    if (ch >= 'a' && ch <= 'z') return 0.53f;
    if (ch >= 0x80 && (ch & 0xc0) == 0x80) return 0; /* UTF-8 continuation bytes */
    return 0.584f;
}
static float text_width(const char *s, size_t n, const font_state *f) {
    float w = 0;
    for (size_t k = 0; k < n; k++) w += char_em((unsigned char)s[k]);
    return w * f->size * (f->bold ? 1.06f : 1.0f);
}

/* -[NSString sizeWithFont:]: CGSize via stret (r0 result, r1 self, r3 font) */
static font_state default_font = {17.0f, 0, 0, "Helvetica"};
static const font_state *font_arg(id font) { return is_a(font, cls_uifont) ? FS(font) : &default_font; }

M(str_size_with_font) {
    (void)m;
    const char *s = rt_nsstring_utf8(c->r[1]);
    const font_state *f = font_arg(c->r[3]);
    float w = 0;
    if (s) { const char *nl = strchr(s, '\n'); w = text_width(s, nl ? (size_t)(nl - s) : strlen(s), f); }
    put_f32(c->r[0], ceilf(w));
    put_f32(c->r[0] + 4, ceilf(f->size * 1.2f));
}
/* sizeWithFont:constrainedToSize:lineBreakMode: (r3 font, CGSize in words 4-5, the mode in word 6):
 * greedy word wrap */
M(str_size_constrained) {
    (void)m;
    const char *s = rt_nsstring_utf8(c->r[1]);
    const font_state *f = font_arg(c->r[3]);
    float maxw = rt_farg(c, 4), maxh = rt_farg(c, 5), lh = ceilf(f->size * 1.2f);
    uint32_t mode = rt_arg(c, 6);
    if (maxw <= 0) maxw = 1e9f;
    float widest = 0, line = 0;
    int lines = s && *s ? 1 : 0;
    size_t k = 0, n = s ? strlen(s) : 0;
    while (k < n) {
        if (s[k] == '\n') { if (line > widest) widest = line; line = 0; lines++; k++; continue; }
        size_t e = k;
        if (mode == 1) e = k + 1; /* character wrap */
        else { while (e < n && s[e] != ' ' && s[e] != '\n') e++; if (e < n && s[e] == ' ') e++; }
        float ww = text_width(s + k, e - k, f);
        if (line > 0 && line + ww > maxw) { if (line > widest) widest = line; line = 0; lines++; }
        line += ww;
        k = e;
    }
    if (line > widest) widest = line;
    if (widest > maxw) widest = maxw;
    int maxlines = maxh > 0 ? (int)(maxh / lh) : 1 << 20;
    if (maxlines < 1) maxlines = 1;
    if (lines > maxlines) lines = maxlines;
    put_f32(c->r[0], ceilf(widest));
    put_f32(c->r[0] + 4, lines * lh);
}

/* ---- data imports ---------------------------------------------------------------------------------------- */
static uint32_t zero_block, identity_block;

static uint32_t resolve(const char *name) {
    if (!strcmp(name, "CGPointZero") || !strcmp(name, "CGRectZero") || !strcmp(name, "CGSizeZero")) {
        if (!zero_block) zero_block = rt_calloc(1, 32);
        return zero_block;
    }
    if (!strcmp(name, "CGAffineTransformIdentity")) {
        if (!identity_block) { identity_block = rt_calloc(1, 24); x_write(identity_block, identity); }
        return identity_block;
    }
    if (!strcmp(name, "CGRectNull")) {
        static uint32_t null_rect;
        if (!null_rect) {
            null_rect = rt_calloc(1, 16);
            put_f32(null_rect, INFINITY);
            put_f32(null_rect + 4, INFINITY);
        }
        return null_rect;
    }
    return 0;
}

/* ---- registration ---------------------------------------------------------------------------------------- */
static void im(id cls, const char *sel, rt_hostfn fn) { rt_objc_method(cls, sel, fn); }
static void cm(id cls, const char *sel, rt_hostfn fn) { rt_objc_cmethod(cls, sel, fn); }

void rt_graphics_define(void) {
    cls_context = rt_objc_define("CGContext", "NSObject", 0);
    cls_image = rt_objc_define("CGImage", "NSObject", 0);
    cls_space = rt_objc_define("CGColorSpace", "NSObject", 0);
    cls_gradient = rt_objc_define("CGGradient", "NSObject", 0);
    cls_uiimage = rt_objc_define("UIImage", "NSObject", 0);
    cls_uicolor = rt_objc_define("UIColor", "NSObject", 0);
    cls_uifont = rt_objc_define("UIFont", "NSObject", 0);

    im(cls_context, "dealloc", ctx_dealloc);
    im(cls_image, "dealloc", image_dealloc);
    im(cls_space, "retain", obj_self);
    im(cls_space, "release", obj_nop);
    im(cls_space, "autorelease", obj_self);
    im(cls_space, "dealloc", obj_nop);
    space_rgb = rt_objc_alloc(cls_space);
    space_gray = rt_objc_alloc(cls_space);
    SS(space_rgb)->gray = 0;
    SS(space_gray)->gray = 1;

    cm(cls_uiimage, "imageNamed:", ui_image_named);
    cm(cls_uiimage, "imageWithContentsOfFile:", ui_image_with_file);
    cm(cls_uiimage, "imageWithData:", ui_image_with_data);
    cm(cls_uiimage, "imageWithCGImage:", ui_image_with_cg);
    cm(cls_uiimage, "imageWithCGImage:scale:orientation:", ui_image_with_cg);
    im(cls_uiimage, "initWithContentsOfFile:", ui_init_file);
    im(cls_uiimage, "initWithData:", ui_init_data);
    im(cls_uiimage, "initWithCGImage:", ui_init_cg);
    im(cls_uiimage, "CGImage", ui_cgimage);
    im(cls_uiimage, "size", ui_size);
    im(cls_uiimage, "scale", ui_scale);
    im(cls_uiimage, "imageOrientation", ui_orientation);
    im(cls_uiimage, "stretchableImageWithLeftCapWidth:topCapHeight:", ui_stretchable);
    im(cls_uiimage, "drawInRect:", ui_draw_in_rect);
    im(cls_uiimage, "drawAtPoint:", ui_draw_at_point);
    im(cls_uiimage, "dealloc", uiimage_dealloc);

    for (size_t k = 0; k < sizeof named_colors / sizeof *named_colors; k++) cm(cls_uicolor, named_colors[k].sel, col_named);
    cm(cls_uicolor, "colorWithRed:green:blue:alpha:", col_rgba);
    cm(cls_uicolor, "colorWithWhite:alpha:", col_white);
    im(cls_uicolor, "initWithRed:green:blue:alpha:", col_init_rgba);
    im(cls_uicolor, "initWithWhite:alpha:", col_init_white);
    im(cls_uicolor, "colorWithAlphaComponent:", col_with_alpha);
    im(cls_uicolor, "CGColor", obj_self);
    im(cls_uicolor, "set", col_set_fill);
    im(cls_uicolor, "setFill", col_set_fill);
    im(cls_uicolor, "setStroke", obj_nop);

    cm(cls_uifont, "systemFontOfSize:", font_system);
    cm(cls_uifont, "boldSystemFontOfSize:", font_bold);
    cm(cls_uifont, "italicSystemFontOfSize:", font_italic);
    cm(cls_uifont, "fontWithName:size:", font_named);
    cm(cls_uifont, "labelFontSize", font_label_size);
    cm(cls_uifont, "buttonFontSize", font_button_size);
    cm(cls_uifont, "systemFontSize", font_system_size);
    cm(cls_uifont, "smallSystemFontSize", font_small_size);
    im(cls_uifont, "fontWithSize:", font_with_size);
    im(cls_uifont, "pointSize", font_point_size);
    im(cls_uifont, "fontName", font_name);
    im(cls_uifont, "familyName", font_family);
    im(cls_uifont, "ascender", font_ascender);
    im(cls_uifont, "descender", font_descender);
    im(cls_uifont, "capHeight", font_cap_height);
    im(cls_uifont, "xHeight", font_x_height);
    im(cls_uifont, "lineHeight", font_line_height);
    im(cls_uifont, "leading", font_leading);

    id nsstring = rt_class("NSString");
    if (nsstring) {
        im(nsstring, "sizeWithFont:", str_size_with_font);
        im(nsstring, "sizeWithFont:constrainedToSize:lineBreakMode:", str_size_constrained);
    }

    rt_data_resolver_add(resolve);
}

void rt_graphics_register(void) {
    REG(CGBitmapContextCreate); REG(CGBitmapContextCreateImage); REG(CGContextRelease);
    REG(CGContextSetRGBFillColor); REG(CGContextFillRect); REG(CGContextScaleCTM); REG(CGContextTranslateCTM);
    REG(CGContextDrawImage); REG(CGContextDrawLinearGradient); REG(CGGradientCreateWithColorComponents);
    REG(CGColorSpaceCreateDeviceRGB); REG(CGColorSpaceCreateDeviceGray); REG(CGColorSpaceRelease);
    REG(CGImageGetWidth); REG(CGImageGetHeight); REG(CGImageGetColorSpace); REG(CGImageRelease);
    REG(CGImageCreateWithMask);
    REG(CGAffineTransformMakeRotation); REG(CGAffineTransformMakeScale); REG(CGAffineTransformMakeTranslation);
    REG(CGAffineTransformConcat); REG(CGAffineTransformRotate); REG(CGRectOffset);
    REG(UIGraphicsBeginImageContext); REG(UIGraphicsGetCurrentContext); REG(UIGraphicsEndImageContext);
    REG(UIGraphicsGetImageFromCurrentImageContext); REG(UIImagePNGRepresentation); REG(UIImageJPEGRepresentation);
}
