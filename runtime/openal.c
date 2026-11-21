/* OpenAL 1.1 and AudioSession for the game, over a software mixer (no host OpenAL library).
 *
 * Output: one 44100 Hz stereo int16 stream (rt_audio_open), pulled by the backend's own thread (waveOut feeder on
 * Windows, the AAudio callback on Android). Every AL entry point and the pull take one lock (al_lock), so the
 * game's threads and the audio thread never see a half-updated source.
 *
 * How the game uses it (from the call sites in the executable):
 *   - alcOpenDevice(NULL); alcCreateContext(dev, NULL); alcMakeContextCurrent(ctx); alDistanceModel(...)
 *   - buffer data only through the extension alBufferDataStatic, fetched with alcGetProcAddress(NULL,
 *     "alBufferDataStatic") (alBufferData itself is not imported); formats MONO16 / STEREO16. A static buffer
 *     REFERENCES game memory (the data is read at mix time and never copied), exactly like Apple's extension.
 *   - alSourcei: AL_BUFFER, AL_LOOPING, AL_SOURCE_RELATIVE; alSourcef: AL_GAIN, AL_REFERENCE_DISTANCE,
 *     AL_ROLLOFF_FACTOR, AL_MAX_DISTANCE; alSource3f/alSourcefv: AL_POSITION; alListenerfv: AL_POSITION and
 *     AL_ORIENTATION; alGetSourcei: AL_SOURCE_STATE, AL_BUFFERS_QUEUED, AL_BUFFERS_PROCESSED;
 *     streaming with alSourceQueueBuffers / alSourceUnqueueBuffers.
 *   More of the 1.1 enums are accepted than the game uses (pitch, gains, offsets, velocity, ...).
 *
 * Objects:
 *   buffer  id = index + 1 into bufs[]; holds either a game address (static) or a host copy (alBufferData through
 *           alcGetProcAddress), plus the format and frequency; resampled to 44100 Hz at mix time (linear
 *           interpolation, step = freq * pitch / 44100).
 *   source  id = index + 1 into srcs[]; a queue of buffer ids (AL_BUFFER sets a queue of one), the index of the
 *           playing entry and a 32.32 fixed-point frame position in it. Entries before the playing index are
 *           "processed"; a stopped source has all entries processed; a looping source wraps and processes none.
 *   device/context  small zeroed blocks in game memory (the game only stores and passes them back). One device
 *           and one context exist at a time; destroying the context deletes its sources, closing the device
 *           deletes the buffers and closes the output stream.
 *
 * Spatialization: mono sources only (as in OpenAL, stereo buffers play unspatialized). Distance gain by the
 * selected model (default AL_INVERSE_DISTANCE_CLAMPED), stereo balance from the source direction projected on the
 * listener's right vector (at x up). Gains ramp across each mixed chunk to avoid clicks.
 *
 * Calling convention: float arguments are raw bits in argument words (rt_farg); vectors are game pointers to
 * 32-bit floats; alGet* results are written through game pointers.
 */
#include <math.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#include <windows.h>
#else
#include <pthread.h>
#endif

#include "rt.h"

#define A(k) rt_arg(c, k)
#define F(k) rt_farg(c, k)
#define RET(v) rt_ret(c, (uint32_t)(v))
#define IMP(name) static void imp_##name(cpu_t *c)
#define REG(name) rt_import_register(#name, imp_##name)

/* ---- AL / ALC enums ------------------------------------------------------------------------------------------- */
enum {
    AL_NONE = 0, AL_FALSE = 0, AL_TRUE = 1,
    AL_SOURCE_RELATIVE = 0x202, AL_CONE_INNER_ANGLE = 0x1001, AL_CONE_OUTER_ANGLE = 0x1002, AL_PITCH = 0x1003,
    AL_POSITION = 0x1004, AL_DIRECTION = 0x1005, AL_VELOCITY = 0x1006, AL_LOOPING = 0x1007, AL_BUFFER = 0x1009,
    AL_GAIN = 0x100A, AL_MIN_GAIN = 0x100D, AL_MAX_GAIN = 0x100E, AL_ORIENTATION = 0x100F,
    AL_SOURCE_STATE = 0x1010, AL_INITIAL = 0x1011, AL_PLAYING = 0x1012, AL_PAUSED = 0x1013, AL_STOPPED = 0x1014,
    AL_BUFFERS_QUEUED = 0x1015, AL_BUFFERS_PROCESSED = 0x1016,
    AL_REFERENCE_DISTANCE = 0x1020, AL_ROLLOFF_FACTOR = 0x1021, AL_CONE_OUTER_GAIN = 0x1022,
    AL_MAX_DISTANCE = 0x1023, AL_SEC_OFFSET = 0x1024, AL_SAMPLE_OFFSET = 0x1025, AL_BYTE_OFFSET = 0x1026,
    AL_SOURCE_TYPE = 0x1027, AL_STATIC = 0x1028, AL_STREAMING = 0x1029, AL_UNDETERMINED = 0x1030,
    AL_FORMAT_MONO8 = 0x1100, AL_FORMAT_MONO16 = 0x1101, AL_FORMAT_STEREO8 = 0x1102, AL_FORMAT_STEREO16 = 0x1103,
    AL_NO_ERROR = 0, AL_INVALID_NAME = 0xA001, AL_INVALID_ENUM = 0xA002, AL_INVALID_VALUE = 0xA003,
    AL_INVALID_OPERATION = 0xA004, AL_OUT_OF_MEMORY = 0xA005,
    AL_INVERSE_DISTANCE = 0xD001, AL_INVERSE_DISTANCE_CLAMPED = 0xD002, AL_LINEAR_DISTANCE = 0xD003,
    AL_LINEAR_DISTANCE_CLAMPED = 0xD004, AL_EXPONENT_DISTANCE = 0xD005, AL_EXPONENT_DISTANCE_CLAMPED = 0xD006,
};

#define OUT_RATE 44100
#define MAX_BUFFERS 4096
#define MAX_SOURCES 256
#define MAX_QUEUE 64
#define CHUNK 512 /* frames mixed per pass */

/* ---- lock ----------------------------------------------------------------------------------------------------- */
#ifdef _WIN32
static CRITICAL_SECTION lock_cs;
static volatile LONG lock_ready;
static void al_lock(void) {
    if (lock_ready != 2) {
        if (InterlockedCompareExchange(&lock_ready, 1, 0) == 0) { InitializeCriticalSection(&lock_cs); lock_ready = 2; }
        else while (lock_ready != 2) Sleep(0);
    }
    EnterCriticalSection(&lock_cs);
}
static void al_unlock(void) { LeaveCriticalSection(&lock_cs); }
#else
static pthread_mutex_t lock_mx = PTHREAD_MUTEX_INITIALIZER;
static void al_lock(void) { pthread_mutex_lock(&lock_mx); }
static void al_unlock(void) { pthread_mutex_unlock(&lock_mx); }
#endif

/* ---- state ---------------------------------------------------------------------------------------------------- */
typedef struct {
    int used;
    uint32_t data;        /* game address of the samples (static buffers) */
    uint8_t *copy;        /* or a host copy (alBufferData) */
    uint32_t bytes, frames, freq;
    int channels, bits;
} albuffer;

typedef struct {
    int used;
    int state;            /* AL_INITIAL / PLAYING / PAUSED / STOPPED */
    int looping, relative, type;
    float gain, pitch, min_gain, max_gain;
    float ref_dist, max_dist, rolloff;
    float pos[3], vel[3], dir[3];
    float cone_inner, cone_outer, cone_outer_gain;
    uint32_t queue[MAX_QUEUE];
    int nqueue, cur;      /* entries before cur are processed */
    uint64_t frac;        /* frame position in queue[cur], 32.32 fixed point */
    float last_l, last_r; /* gains applied at the end of the previous chunk (ramps) */
    int fresh;            /* no previous gain yet: start the ramp at the target */
} alsource;

static albuffer bufs[MAX_BUFFERS];
static alsource srcs[MAX_SOURCES];
static float lis_pos[3], lis_vel[3], lis_at[3] = {0, 0, -1}, lis_up[3] = {0, 1, 0}, lis_gain = 1.0f;
static int distance_model = AL_INVERSE_DISTANCE_CLAMPED;
static float doppler_factor = 1.0f, speed_of_sound = 343.3f;
static int al_error;
static uint32_t device_addr, context_addr, current_context;
static void *stream;

static void set_error(int e) { if (!al_error) al_error = e; }

static albuffer *buffer_get(uint32_t id) {
    return id && id <= MAX_BUFFERS && bufs[id - 1].used ? &bufs[id - 1] : NULL;
}
static alsource *source_get(uint32_t id) {
    return id && id <= MAX_SOURCES && srcs[id - 1].used ? &srcs[id - 1] : NULL;
}
static float rd_f(uint32_t a) { float f; memcpy(&f, rt_mem + a, 4); return f; }

static const uint8_t *buffer_bytes(const albuffer *b) {
    return b->copy ? b->copy : (b->data ? rt_mem + b->data : NULL);
}

static int buffer_in_use(uint32_t id) {
    for (int k = 0; k < MAX_SOURCES; k++)
        if (srcs[k].used)
            for (int q = 0; q < srcs[k].nqueue; q++)
                if (srcs[k].queue[q] == id) return 1;
    return 0;
}

static void source_reset(alsource *s) {
    memset(s, 0, sizeof *s);
    s->used = 1;
    s->state = AL_INITIAL;
    s->type = AL_UNDETERMINED;
    s->gain = 1.0f; s->pitch = 1.0f; s->min_gain = 0.0f; s->max_gain = 1.0f;
    s->ref_dist = 1.0f; s->max_dist = 3.4e38f; s->rolloff = 1.0f;
    s->cone_inner = 360.0f; s->cone_outer = 360.0f; s->cone_outer_gain = 0.0f;
    s->fresh = 1;
}

/* the frames of the queue's playing entry, 0 if the entry is missing or empty */
static const albuffer *source_buffer(const alsource *s) {
    if (s->cur >= s->nqueue) return NULL;
    return buffer_get(s->queue[s->cur]);
}

static int source_processed(const alsource *s) {
    if (s->state == AL_STOPPED) return s->nqueue;
    if (s->state == AL_INITIAL || s->looping) return 0;
    return s->cur < s->nqueue ? s->cur : s->nqueue;
}

/* ---- mixer ---------------------------------------------------------------------------------------------------- */
static float sample_at(const albuffer *b, const uint8_t *d, uint32_t frame, int ch) {
    if (frame >= b->frames) return 0.0f;
    int c = b->channels == 2 ? ch : 0;
    if (b->bits == 16) {
        int16_t v;
        memcpy(&v, d + (size_t)frame * b->channels * 2 + c * 2, 2);
        return v * (1.0f / 32768.0f);
    }
    return ((int)d[(size_t)frame * b->channels + c] - 128) * (1.0f / 128.0f);
}

static float clampf(float v, float lo, float hi) { return v < lo ? lo : v > hi ? hi : v; }

/* distance attenuation and stereo balance of a source, for this chunk */
static void source_gains(const alsource *s, int stereo_buffer, float *gl, float *gr) {
    float g = s->gain, pan = 0.0f;
    if (!stereo_buffer) {
        float rel[3];
        for (int k = 0; k < 3; k++) rel[k] = s->relative ? s->pos[k] : s->pos[k] - lis_pos[k];
        float d = sqrtf(rel[0] * rel[0] + rel[1] * rel[1] + rel[2] * rel[2]);
        float ref = s->ref_dist, mx = s->max_dist, ro = s->rolloff, dg = 1.0f;
        switch (distance_model) {
        case AL_INVERSE_DISTANCE_CLAMPED: if (mx >= ref) d = clampf(d, ref, mx); /* fall through */
        case AL_INVERSE_DISTANCE:
            if (ref > 0.0f) { float den = ref + ro * (d - ref); dg = den > 0.0f ? ref / den : 1.0f; }
            break;
        case AL_LINEAR_DISTANCE_CLAMPED: if (mx >= ref) d = clampf(d, ref, mx); /* fall through */
        case AL_LINEAR_DISTANCE:
            if (mx != ref) dg = 1.0f - ro * (d - ref) / (mx - ref);
            break;
        case AL_EXPONENT_DISTANCE_CLAMPED: if (mx >= ref) d = clampf(d, ref, mx); /* fall through */
        case AL_EXPONENT_DISTANCE:
            if (ref > 0.0f && d > 0.0f) dg = powf(d / ref, -ro);
            break;
        default: break; /* AL_NONE */
        }
        g *= clampf(dg, 0.0f, 1.0f);
        if (d > 1e-4f) {
            /* right = at x up (listener frame); a relative source is already in the listener frame */
            float right[3];
            if (s->relative) { right[0] = 1; right[1] = 0; right[2] = 0; }
            else {
                right[0] = lis_at[1] * lis_up[2] - lis_at[2] * lis_up[1];
                right[1] = lis_at[2] * lis_up[0] - lis_at[0] * lis_up[2];
                right[2] = lis_at[0] * lis_up[1] - lis_at[1] * lis_up[0];
                float n = sqrtf(right[0] * right[0] + right[1] * right[1] + right[2] * right[2]);
                if (n > 1e-6f) for (int k = 0; k < 3; k++) right[k] /= n;
                else { right[0] = 1; right[1] = 0; right[2] = 0; }
            }
            pan = clampf((rel[0] * right[0] + rel[1] * right[1] + rel[2] * right[2]) / d, -1.0f, 1.0f);
        }
    }
    g = clampf(g, s->min_gain, s->max_gain) * lis_gain;
    /* balance: the near side stays at full gain, the far side fades (a centred sound plays at unity) */
    *gl = g * (pan > 0.0f ? 1.0f - pan * 0.8f : 1.0f);
    *gr = g * (pan < 0.0f ? 1.0f + pan * 0.8f : 1.0f);
}

/* mix n frames of one source into acc (stereo floats) */
static void mix_source(alsource *s, float *acc, int n) {
    const albuffer *b0 = source_buffer(s);
    int stereo = b0 && b0->channels == 2;
    float tl, tr;
    source_gains(s, stereo, &tl, &tr);
    if (s->fresh) { s->last_l = tl; s->last_r = tr; s->fresh = 0; }
    float l0 = s->last_l, r0 = s->last_r, dl = (tl - l0) / n, dr = (tr - r0) / n;
    s->last_l = tl; s->last_r = tr;
    float pitch = s->pitch > 0.0f ? s->pitch : 1.0f;
    int i = 0;
    int guard = 0; /* empty buffers in a looping queue must not spin forever */
    while (i < n && s->state == AL_PLAYING) {
        const albuffer *b = source_buffer(s);
        const uint8_t *d = b ? buffer_bytes(b) : NULL;
        if (!b || !d || !b->frames) {
            /* missing/empty entry: skip it */
            if (++guard > MAX_QUEUE + 1) { s->state = AL_STOPPED; break; }
            s->cur++;
            s->frac = 0;
            if (s->cur >= s->nqueue) {
                if (s->looping && s->nqueue) s->cur = 0;
                else { s->state = AL_STOPPED; s->cur = s->nqueue; break; }
            }
            continue;
        }
        guard = 0;
        uint64_t step = (uint64_t)((double)b->freq * pitch / OUT_RATE * 4294967296.0);
        if (!step) step = 1;
        for (; i < n; i++) {
            uint32_t f = (uint32_t)(s->frac >> 32);
            if (f >= b->frames) break;
            float t = (float)(uint32_t)s->frac * (1.0f / 4294967296.0f);
            float gl = l0 + dl * i, gr = r0 + dr * i;
            if (b->channels == 2) {
                float a = sample_at(b, d, f, 0), bb = sample_at(b, d, f + 1 < b->frames ? f + 1 : f, 0);
                float c2 = sample_at(b, d, f, 1), dd = sample_at(b, d, f + 1 < b->frames ? f + 1 : f, 1);
                acc[2 * i] += (a + (bb - a) * t) * gl;
                acc[2 * i + 1] += (c2 + (dd - c2) * t) * gr;
            } else {
                float a = sample_at(b, d, f, 0), bb = sample_at(b, d, f + 1 < b->frames ? f + 1 : f, 0);
                float v = a + (bb - a) * t;
                acc[2 * i] += v * gl;
                acc[2 * i + 1] += v * gr;
            }
            s->frac += step;
        }
        if ((uint32_t)(s->frac >> 32) >= b->frames) {
            /* end of this entry: the next one, wrap when looping, else stop */
            s->frac -= (uint64_t)b->frames << 32;
            if ((uint32_t)(s->frac >> 32) >= b->frames) s->frac = 0;
            s->cur++;
            if (s->cur >= s->nqueue) {
                if (s->looping) s->cur = 0;
                else { s->state = AL_STOPPED; s->cur = s->nqueue; s->frac = 0; }
            }
            if (s->cur < s->nqueue) {
                const albuffer *nb = source_buffer(s);
                if (nb && (uint32_t)(s->frac >> 32) >= nb->frames) s->frac = 0;
            }
        }
    }
}

static void pull(void *user, int16_t *out, int frames) {
    (void)user;
    static float acc[CHUNK * 2];
    while (frames > 0) {
        int n = frames < CHUNK ? frames : CHUNK;
        memset(acc, 0, sizeof(float) * 2 * n);
        al_lock();
        for (int k = 0; k < MAX_SOURCES; k++)
            if (srcs[k].used && srcs[k].state == AL_PLAYING) mix_source(&srcs[k], acc, n);
        al_unlock();
        for (int i = 0; i < 2 * n; i++) {
            float v = acc[i] * 32767.0f;
            out[i] = (int16_t)(v > 32767.0f ? 32767 : v < -32768.0f ? -32768 : (int)v);
        }
        out += 2 * n;
        frames -= n;
    }
}

/* ---- buffers -------------------------------------------------------------------------------------------------- */
IMP(alGenBuffers) {
    int n = (int)A(0);
    uint32_t out = A(1);
    if (n < 0) { al_lock(); set_error(AL_INVALID_VALUE); al_unlock(); return; }
    al_lock();
    int made = 0;
    for (int k = 0; k < MAX_BUFFERS && made < n; k++)
        if (!bufs[k].used) {
            memset(&bufs[k], 0, sizeof bufs[k]);
            bufs[k].used = 1;
            rt_st32(out + 4 * made++, (uint32_t)k + 1);
        }
    if (made < n) {
        /* out of names: undo, like the real implementation does */
        for (int j = 0; j < made; j++) bufs[rt_ld32(out + 4 * j) - 1].used = 0;
        set_error(AL_OUT_OF_MEMORY);
        rt_log("openal: out of buffer names");
    }
    al_unlock();
}

IMP(alDeleteBuffers) {
    int n = (int)A(0);
    uint32_t ids = A(1);
    al_lock();
    if (n < 0) { set_error(AL_INVALID_VALUE); al_unlock(); return; }
    for (int j = 0; j < n; j++) {
        uint32_t id = rt_ld32(ids + 4 * j);
        if (id && !buffer_get(id)) { set_error(AL_INVALID_NAME); al_unlock(); return; }
        if (id && buffer_in_use(id)) { set_error(AL_INVALID_OPERATION); al_unlock(); return; }
    }
    for (int j = 0; j < n; j++) {
        uint32_t id = rt_ld32(ids + 4 * j);
        albuffer *b = buffer_get(id);
        if (!b) continue;
        free(b->copy);
        memset(b, 0, sizeof *b);
    }
    al_unlock();
}

static int format_info(uint32_t fmt, int *channels, int *bits) {
    switch (fmt) {
    case AL_FORMAT_MONO8: *channels = 1; *bits = 8; return 1;
    case AL_FORMAT_MONO16: *channels = 1; *bits = 16; return 1;
    case AL_FORMAT_STEREO8: *channels = 2; *bits = 8; return 1;
    case AL_FORMAT_STEREO16: *channels = 2; *bits = 16; return 1;
    }
    return 0;
}

/* alBufferData / alBufferDataStatic(buffer, format, data, size, freq): copy decides whether the samples are copied
 * (alBufferData) or referenced in game memory (the Apple extension) */
static void buffer_data(cpu_t *c, int copy) {
    uint32_t id = A(0), fmt = A(1), data = A(2), size = A(3), freq = A(4);
    int channels, bits;
    al_lock();
    albuffer *b = buffer_get(id);
    if (!b) { set_error(AL_INVALID_NAME); al_unlock(); return; }
    if (!format_info(fmt, &channels, &bits)) { set_error(AL_INVALID_ENUM); al_unlock(); return; }
    if (!freq || (size && !data)) { set_error(AL_INVALID_VALUE); al_unlock(); return; }
    if (buffer_in_use(id)) {
        /* refilling a queued buffer is an error in OpenAL; a buffer attached to a stopped source is allowed by
         * Apple's implementation, so only refuse when a playing source uses it */
        for (int k = 0; k < MAX_SOURCES; k++)
            if (srcs[k].used && srcs[k].state == AL_PLAYING)
                for (int q = 0; q < srcs[k].nqueue; q++)
                    if (srcs[k].queue[q] == id) { set_error(AL_INVALID_OPERATION); al_unlock(); return; }
    }
    free(b->copy);
    b->copy = NULL;
    b->data = 0;
    if (copy && size) {
        b->copy = malloc(size);
        if (!b->copy) { set_error(AL_OUT_OF_MEMORY); b->bytes = b->frames = 0; al_unlock(); return; }
        memcpy(b->copy, rt_mem + data, size);
    } else {
        b->data = data;
    }
    b->bytes = size;
    b->channels = channels;
    b->bits = bits;
    b->freq = freq;
    b->frames = size / (uint32_t)(channels * bits / 8);
    al_unlock();
}

static void hf_alBufferDataStatic(cpu_t *c, uint8_t *m) { (void)m; buffer_data(c, 0); }
static void hf_alBufferData(cpu_t *c, uint8_t *m) { (void)m; buffer_data(c, 1); }

/* ---- sources -------------------------------------------------------------------------------------------------- */
IMP(alGenSources) {
    int n = (int)A(0);
    uint32_t out = A(1);
    al_lock();
    if (n < 0) { set_error(AL_INVALID_VALUE); al_unlock(); return; }
    int made = 0;
    for (int k = 0; k < MAX_SOURCES && made < n; k++)
        if (!srcs[k].used) {
            source_reset(&srcs[k]);
            rt_st32(out + 4 * made++, (uint32_t)k + 1);
        }
    if (made < n) {
        for (int j = 0; j < made; j++) srcs[rt_ld32(out + 4 * j) - 1].used = 0;
        set_error(AL_OUT_OF_MEMORY);
        rt_log("openal: out of source names (%d asked)", n);
    }
    al_unlock();
}

IMP(alDeleteSources) {
    int n = (int)A(0);
    uint32_t ids = A(1);
    al_lock();
    if (n < 0) { set_error(AL_INVALID_VALUE); al_unlock(); return; }
    for (int j = 0; j < n; j++)
        if (!source_get(rt_ld32(ids + 4 * j))) { set_error(AL_INVALID_NAME); al_unlock(); return; }
    for (int j = 0; j < n; j++) {
        alsource *s = source_get(rt_ld32(ids + 4 * j));
        if (s) memset(s, 0, sizeof *s);
    }
    al_unlock();
}

/* offset setters/getters in frames of the playing entry */
static void source_seek_frames(alsource *s, double frames) {
    if (frames < 0) { set_error(AL_INVALID_VALUE); return; }
    /* walk the queue so an offset past the first buffer lands in a later one */
    int k = 0;
    while (k < s->nqueue) {
        const albuffer *b = buffer_get(s->queue[k]);
        uint32_t fr = b ? b->frames : 0;
        if (frames < fr) break;
        frames -= fr;
        k++;
    }
    if (k >= s->nqueue) { set_error(AL_INVALID_VALUE); return; }
    s->cur = k;
    s->frac = (uint64_t)(frames * 4294967296.0);
}

static double source_offset_frames(const alsource *s) {
    if (s->state != AL_PLAYING && s->state != AL_PAUSED) return 0.0;
    double f = 0.0;
    for (int k = 0; k < s->cur && k < s->nqueue; k++) {
        const albuffer *b = buffer_get(s->queue[k]);
        if (b) f += b->frames;
    }
    return f + s->frac / 4294967296.0;
}

static void source_setf(alsource *s, uint32_t p, float v) {
    switch (p) {
    case AL_GAIN: if (v < 0) set_error(AL_INVALID_VALUE); else s->gain = v; break;
    case AL_PITCH: if (v <= 0) set_error(AL_INVALID_VALUE); else s->pitch = v; break;
    case AL_MIN_GAIN: s->min_gain = clampf(v, 0, 1); break;
    case AL_MAX_GAIN: s->max_gain = clampf(v, 0, 1); break;
    case AL_REFERENCE_DISTANCE: if (v < 0) set_error(AL_INVALID_VALUE); else s->ref_dist = v; break;
    case AL_MAX_DISTANCE: if (v < 0) set_error(AL_INVALID_VALUE); else s->max_dist = v; break;
    case AL_ROLLOFF_FACTOR: if (v < 0) set_error(AL_INVALID_VALUE); else s->rolloff = v; break;
    case AL_CONE_INNER_ANGLE: s->cone_inner = v; break;
    case AL_CONE_OUTER_ANGLE: s->cone_outer = v; break;
    case AL_CONE_OUTER_GAIN: s->cone_outer_gain = v; break;
    case AL_SEC_OFFSET: {
        const albuffer *b = s->nqueue ? buffer_get(s->queue[0]) : NULL;
        source_seek_frames(s, (double)v * (b ? b->freq : OUT_RATE));
        break;
    }
    case AL_SAMPLE_OFFSET: source_seek_frames(s, v); break;
    case AL_BYTE_OFFSET: {
        const albuffer *b = s->nqueue ? buffer_get(s->queue[0]) : NULL;
        source_seek_frames(s, b ? (double)v / (b->channels * b->bits / 8) : 0);
        break;
    }
    case AL_SOURCE_RELATIVE: s->relative = v != 0.0f; break;
    case AL_LOOPING: s->looping = v != 0.0f; break;
    default: set_error(AL_INVALID_ENUM); break;
    }
}

static void source_set3f(alsource *s, uint32_t p, float x, float y, float z) {
    float *v = p == AL_POSITION ? s->pos : p == AL_VELOCITY ? s->vel : p == AL_DIRECTION ? s->dir : NULL;
    if (!v) { set_error(AL_INVALID_ENUM); return; }
    v[0] = x; v[1] = y; v[2] = z;
}

static void source_set_buffer(alsource *s, uint32_t id) {
    if (s->state == AL_PLAYING || s->state == AL_PAUSED) { set_error(AL_INVALID_OPERATION); return; }
    if (id && !buffer_get(id)) { set_error(AL_INVALID_VALUE); return; }
    s->nqueue = 0;
    s->cur = 0;
    s->frac = 0;
    if (id) { s->queue[0] = id; s->nqueue = 1; s->type = AL_STATIC; }
    else s->type = AL_UNDETERMINED;
}

IMP(alSourcei) {
    uint32_t p = A(1);
    int32_t v = (int32_t)A(2);
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) set_error(AL_INVALID_NAME);
    else switch (p) {
    case AL_BUFFER: source_set_buffer(s, (uint32_t)v); break;
    case AL_LOOPING: s->looping = v != 0; break;
    case AL_SOURCE_RELATIVE: s->relative = v != 0; break;
    case AL_SAMPLE_OFFSET: source_seek_frames(s, v); break;
    case AL_BYTE_OFFSET: case AL_SEC_OFFSET: case AL_REFERENCE_DISTANCE: case AL_MAX_DISTANCE:
    case AL_ROLLOFF_FACTOR: case AL_CONE_INNER_ANGLE: case AL_CONE_OUTER_ANGLE:
        source_setf(s, p, (float)v); break;
    default: set_error(AL_INVALID_ENUM); break;
    }
    al_unlock();
}

IMP(alSourcef) {
    uint32_t p = A(1);
    float v = F(2);
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) set_error(AL_INVALID_NAME);
    else source_setf(s, p, v);
    al_unlock();
}

IMP(alSource3f) {
    uint32_t p = A(1);
    float x = F(2), y = F(3), z = F(4);
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) set_error(AL_INVALID_NAME);
    else source_set3f(s, p, x, y, z);
    al_unlock();
}

IMP(alSourcefv) {
    uint32_t p = A(1), v = A(2);
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) set_error(AL_INVALID_NAME);
    else if (!v) set_error(AL_INVALID_VALUE);
    else if (p == AL_POSITION || p == AL_VELOCITY || p == AL_DIRECTION)
        source_set3f(s, p, rd_f(v), rd_f(v + 4), rd_f(v + 8));
    else source_setf(s, p, rd_f(v));
    al_unlock();
}

IMP(alGetSourcei) {
    uint32_t p = A(1), out = A(2);
    al_lock();
    alsource *s = source_get(A(0));
    int32_t v = 0;
    int ok = 1;
    if (!s) { set_error(AL_INVALID_NAME); ok = 0; }
    else if (!out) { set_error(AL_INVALID_VALUE); ok = 0; }
    else switch (p) {
    case AL_SOURCE_STATE: v = s->state; break;
    case AL_BUFFERS_QUEUED: v = s->nqueue; break;
    case AL_BUFFERS_PROCESSED: v = source_processed(s); break;
    case AL_BUFFER: v = s->type == AL_STATIC && s->nqueue ? (int32_t)s->queue[0]
                      : (s->cur < s->nqueue ? (int32_t)s->queue[s->cur] : 0); break;
    case AL_LOOPING: v = s->looping; break;
    case AL_SOURCE_RELATIVE: v = s->relative; break;
    case AL_SOURCE_TYPE: v = s->type; break;
    case AL_SAMPLE_OFFSET: v = (int32_t)source_offset_frames(s); break;
    case AL_BYTE_OFFSET: {
        const albuffer *b = source_buffer(s);
        v = (int32_t)source_offset_frames(s) * (b ? b->channels * b->bits / 8 : 2);
        break;
    }
    case AL_SEC_OFFSET: {
        const albuffer *b = source_buffer(s);
        v = b && b->freq ? (int32_t)(source_offset_frames(s) / b->freq) : 0;
        break;
    }
    case AL_REFERENCE_DISTANCE: v = (int32_t)s->ref_dist; break;
    case AL_MAX_DISTANCE: v = (int32_t)s->max_dist; break;
    case AL_ROLLOFF_FACTOR: v = (int32_t)s->rolloff; break;
    default: set_error(AL_INVALID_ENUM); ok = 0; break;
    }
    if (ok) rt_st32(out, (uint32_t)v);
    al_unlock();
}

static void source_play(alsource *s) {
    if (s->state == AL_PAUSED) { s->state = AL_PLAYING; return; }
    /* from initial/stopped/playing: (re)start at the beginning of the queue */
    s->cur = 0;
    s->frac = 0;
    s->fresh = 1;
    s->state = s->nqueue ? AL_PLAYING : AL_STOPPED;
}

IMP(alSourcePlay) {
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) set_error(AL_INVALID_NAME);
    else source_play(s);
    al_unlock();
}

IMP(alSourcePause) {
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) set_error(AL_INVALID_NAME);
    else if (s->state == AL_PLAYING) s->state = AL_PAUSED;
    al_unlock();
}

IMP(alSourceStop) {
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) set_error(AL_INVALID_NAME);
    else { s->state = AL_STOPPED; s->cur = s->nqueue; s->frac = 0; } /* from any state, AL_INITIAL included */
    al_unlock();
}

IMP(alSourceQueueBuffers) {
    int n = (int)A(1);
    uint32_t ids = A(2);
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) { set_error(AL_INVALID_NAME); al_unlock(); return; }
    if (n < 0) { set_error(AL_INVALID_VALUE); al_unlock(); return; }
    if (s->type == AL_STATIC) { set_error(AL_INVALID_OPERATION); al_unlock(); return; }
    if (s->nqueue + n > MAX_QUEUE) {
        rt_log("openal: source queue full (%d + %d)", s->nqueue, n);
        set_error(AL_OUT_OF_MEMORY);
        al_unlock();
        return;
    }
    for (int j = 0; j < n; j++)
        if (!buffer_get(rt_ld32(ids + 4 * j))) { set_error(AL_INVALID_NAME); al_unlock(); return; }
    /* a stopped source keeps all entries processed: new entries go after them, and a later alSourcePlay rewinds */
    for (int j = 0; j < n; j++) s->queue[s->nqueue++] = rt_ld32(ids + 4 * j);
    if (n) s->type = AL_STREAMING;
    al_unlock();
}

IMP(alSourceUnqueueBuffers) {
    int n = (int)A(1);
    uint32_t out = A(2);
    al_lock();
    alsource *s = source_get(A(0));
    if (!s) { set_error(AL_INVALID_NAME); al_unlock(); return; }
    if (n < 0 || n > source_processed(s) || (n && s->type != AL_STREAMING)) {
        set_error(AL_INVALID_VALUE);
        al_unlock();
        return;
    }
    for (int j = 0; j < n; j++) rt_st32(out + 4 * j, s->queue[j]);
    memmove(s->queue, s->queue + n, sizeof(uint32_t) * (size_t)(s->nqueue - n));
    s->nqueue -= n;
    s->cur -= n;
    if (s->cur < 0) s->cur = 0;
    if (!s->nqueue) s->type = AL_UNDETERMINED;
    al_unlock();
}

/* ---- listener and global state -------------------------------------------------------------------------------- */
IMP(alListenerfv) {
    uint32_t p = A(0), v = A(1);
    al_lock();
    if (!v) set_error(AL_INVALID_VALUE);
    else switch (p) {
    case AL_POSITION: { for (int k = 0; k < 3; k++) lis_pos[k] = rd_f(v + 4 * k); } break;
    case AL_VELOCITY: { for (int k = 0; k < 3; k++) lis_vel[k] = rd_f(v + 4 * k); } break;
    case AL_ORIENTATION:
        for (int k = 0; k < 3; k++) { lis_at[k] = rd_f(v + 4 * k); lis_up[k] = rd_f(v + 12 + 4 * k); }
        break;
    case AL_GAIN: lis_gain = rd_f(v) < 0 ? 0 : rd_f(v); break;
    default: set_error(AL_INVALID_ENUM); break;
    }
    al_unlock();
}

IMP(alDistanceModel) {
    uint32_t m = A(0);
    al_lock();
    if (m == AL_NONE || (m >= AL_INVERSE_DISTANCE && m <= AL_EXPONENT_DISTANCE_CLAMPED)) distance_model = (int)m;
    else set_error(AL_INVALID_VALUE);
    al_unlock();
}

IMP(alGetError) {
    al_lock();
    int e = al_error;
    al_error = AL_NO_ERROR;
    al_unlock();
    RET(e);
}

/* ---- ALC ------------------------------------------------------------------------------------------------------ */
IMP(alcOpenDevice) {
    al_lock();
    if (!device_addr) {
        device_addr = rt_calloc(1, 16);
        if (!stream) {
            stream = rt_audio_open(OUT_RATE, 2, pull, NULL);
            if (stream) rt_audio_start(stream);
            else rt_log("openal: no audio output; mixing into nothing");
        }
    }
    uint32_t d = device_addr;
    al_unlock();
    RET(d);
}

IMP(alcCloseDevice) {
    uint32_t d = A(0);
    void *st = NULL;
    al_lock();
    if (!d || d != device_addr) { al_unlock(); RET(0); return; }
    memset(srcs, 0, sizeof srcs);
    for (int k = 0; k < MAX_BUFFERS; k++) free(bufs[k].copy);
    memset(bufs, 0, sizeof bufs);
    rt_free(device_addr);
    device_addr = 0;
    if (context_addr) { rt_free(context_addr); context_addr = 0; current_context = 0; }
    st = stream;
    stream = NULL;
    al_unlock();
    /* outside the lock: the backend's thread may be waiting for it inside pull */
    if (st) { rt_audio_stop(st); rt_audio_close(st); }
    RET(1);
}

IMP(alcCreateContext) {
    uint32_t d = A(0);
    al_lock();
    uint32_t ctx = 0;
    if (d && d == device_addr) {
        if (!context_addr) {
            context_addr = rt_calloc(1, 16);
            /* a new context starts with default listener state */
            memset(lis_pos, 0, sizeof lis_pos);
            memset(lis_vel, 0, sizeof lis_vel);
            lis_at[0] = 0; lis_at[1] = 0; lis_at[2] = -1;
            lis_up[0] = 0; lis_up[1] = 1; lis_up[2] = 0;
            lis_gain = 1.0f;
            distance_model = AL_INVERSE_DISTANCE_CLAMPED;
            doppler_factor = 1.0f;
            speed_of_sound = 343.3f;
        }
        ctx = context_addr;
    } else {
        rt_log("openal: alcCreateContext on unknown device %#x", d);
    }
    al_unlock();
    RET(ctx);
}

IMP(alcMakeContextCurrent) {
    uint32_t ctx = A(0);
    al_lock();
    int ok = !ctx || ctx == context_addr;
    if (ok) current_context = ctx;
    al_unlock();
    RET(ok);
}

IMP(alcDestroyContext) {
    uint32_t ctx = A(0);
    al_lock();
    if (ctx && ctx == context_addr) {
        memset(srcs, 0, sizeof srcs); /* a context owns its sources */
        rt_free(context_addr);
        context_addr = 0;
        if (current_context == ctx) current_context = 0;
    }
    al_unlock();
}

/* registered once in rt_openal_register (single-threaded): rt_hostfn_add is not thread-safe, and the game asks for
 * the extension lazily from whichever thread first loads a sound */
static uint32_t fn_static, fn_data;

IMP(alcGetProcAddress) {
    const char *name = rt_str(A(1));
    uint32_t r = 0;
    if (name && !strcmp(name, "alBufferDataStatic")) {
        r = fn_static;
    } else if (name && !strcmp(name, "alBufferData")) {
        r = fn_data;
    } else {
        rt_log("openal: alcGetProcAddress(\"%s\") not provided", name ? name : "(null)");
    }
    RET(r);
}

/* ---- AudioSession (AudioToolbox): there is no session to manage; every call succeeds ------------------------- */
IMP(AudioSessionInitialize) { RET(0); }
IMP(AudioSessionSetProperty) { RET(0); }
IMP(AudioSessionSetActive) { RET(0); }
IMP(AudioSessionAddPropertyListener) { RET(0); }

void rt_openal_register(void) {
    (void)doppler_factor; (void)speed_of_sound; (void)lis_vel;
    if (!fn_static) fn_static = rt_hostfn_add(hf_alBufferDataStatic, "alBufferDataStatic");
    if (!fn_data) fn_data = rt_hostfn_add(hf_alBufferData, "alBufferData");
    REG(alGenBuffers); REG(alDeleteBuffers);
    REG(alGenSources); REG(alDeleteSources);
    REG(alSourcei); REG(alSourcef); REG(alSource3f); REG(alSourcefv); REG(alGetSourcei);
    REG(alSourcePlay); REG(alSourcePause); REG(alSourceStop);
    REG(alSourceQueueBuffers); REG(alSourceUnqueueBuffers);
    REG(alListenerfv); REG(alDistanceModel); REG(alGetError);
    REG(alcOpenDevice); REG(alcCloseDevice); REG(alcCreateContext); REG(alcMakeContextCurrent);
    REG(alcDestroyContext); REG(alcGetProcAddress);
    REG(AudioSessionInitialize); REG(AudioSessionSetProperty); REG(AudioSessionSetActive);
    REG(AudioSessionAddPropertyListener);
}
