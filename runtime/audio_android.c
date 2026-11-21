/* Android audio backend: an AAudio output stream (16-bit PCM, low-latency mode) whose data callback pulls from
 * the OpenAL mixer (openal.c). The pull mixes the playing sources under the mixer's lock and never calls game
 * code or allocates, so it is fit for AAudio's real-time callback; the lock is only held briefly by the game's
 * AL calls. If the device reports another sample rate AAudio resamples for us (the rate is requested, not
 * negotiated).
 *
 * Disconnects (headphones unplugged, Bluetooth route change) end an AAudio stream for good. AAudio forbids
 * closing a stream from its own error callback, so the callback starts a short-lived thread that closes the dead
 * stream and opens a new one with the same parameters. s->mx guards s->as against rt_audio_start/stop/close;
 * the data callback reads only the immutable fields and `running`, so it takes no lock. rt_audio_close waits for
 * a reopen in progress before freeing the stream. */
#include <aaudio/AAudio.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>

#include "rt.h"

typedef struct stream {
    AAudioStream *as;        /* NULL while a reopen is in progress or after a failed one */
    rt_audio_pull pull;
    void *user;
    int channels, rate;
    volatile int running;    /* pull from the mixer (else silence) */
    int started;             /* rt_audio_start was called: a reopened stream is started too */
    int closing, reopening;
    pthread_mutex_t mx;
    pthread_cond_t cv;
} stream;

static aaudio_data_callback_result_t on_data(AAudioStream *as, void *user, void *data, int32_t frames) {
    (void)as;
    stream *s = user;
    if (s->running) s->pull(s->user, data, frames);
    else memset(data, 0, (size_t)frames * s->channels * 2);
    return AAUDIO_CALLBACK_RESULT_CONTINUE;
}

static void on_error(AAudioStream *as, void *user, aaudio_result_t error);

static AAudioStream *open_stream(stream *s) {
    AAudioStreamBuilder *b;
    AAudioStream *as = NULL;
    if (AAudio_createStreamBuilder(&b) != AAUDIO_OK) return NULL;
    AAudioStreamBuilder_setFormat(b, AAUDIO_FORMAT_PCM_I16);
    AAudioStreamBuilder_setChannelCount(b, s->channels);
    AAudioStreamBuilder_setSampleRate(b, s->rate);
    AAudioStreamBuilder_setPerformanceMode(b, AAUDIO_PERFORMANCE_MODE_LOW_LATENCY);
    AAudioStreamBuilder_setSharingMode(b, AAUDIO_SHARING_MODE_SHARED);
    AAudioStreamBuilder_setDataCallback(b, on_data, s);
    AAudioStreamBuilder_setErrorCallback(b, on_error, s);
    aaudio_result_t r = AAudioStreamBuilder_openStream(b, &as);
    AAudioStreamBuilder_delete(b);
    if (r != AAUDIO_OK) {
        rt_log("audio: AAudio openStream failed: %s", AAudio_convertResultToText(r));
        return NULL;
    }
    rt_log("audio: AAudio stream %d Hz, %d channels", AAudioStream_getSampleRate(as), s->channels);
    return as;
}

/* close the dead stream and open a replacement (never on an AAudio callback thread) */
static void *reopen_thread(void *p) {
    stream *s = p;
    pthread_mutex_lock(&s->mx);
    AAudioStream *old = s->as;
    s->as = NULL;
    pthread_mutex_unlock(&s->mx);
    /* outside the lock: closing waits for the old stream's callbacks, and its error callback takes the lock */
    if (old) { AAudioStream_requestStop(old); AAudioStream_close(old); }
    AAudioStream *as = open_stream(s); /* rt_audio_close waits for us, so s stays valid */
    pthread_mutex_lock(&s->mx);
    if (as && !s->closing) {
        s->as = as;
        if (s->started) AAudioStream_requestStart(as);
        as = NULL;
    }
    if (as) {
        /* rt_audio_close came in while we were opening: drop the new stream before letting it free s (its
         * callbacks point at s), and outside the lock (its error callback takes it) */
        pthread_mutex_unlock(&s->mx);
        AAudioStream_close(as);
        pthread_mutex_lock(&s->mx);
    }
    s->reopening = 0;
    pthread_cond_broadcast(&s->cv);
    pthread_mutex_unlock(&s->mx);
    return NULL;
}

static void on_error(AAudioStream *as, void *user, aaudio_result_t error) {
    stream *s = user;
    rt_log("audio: AAudio stream error: %s", AAudio_convertResultToText(error));
    if (error != AAUDIO_ERROR_DISCONNECTED) return;
    pthread_mutex_lock(&s->mx);
    if (!s->closing && !s->reopening && s->as == as) {
        pthread_t th;
        pthread_attr_t at;
        pthread_attr_init(&at);
        pthread_attr_setdetachstate(&at, PTHREAD_CREATE_DETACHED);
        s->reopening = 1;
        if (pthread_create(&th, &at, reopen_thread, s) != 0) {
            s->reopening = 0;
            rt_log("audio: cannot start the reopen thread; sound stays off");
        }
        pthread_attr_destroy(&at);
    }
    pthread_mutex_unlock(&s->mx);
}

void *rt_audio_open(int rate, int channels, rt_audio_pull pull, void *user) {
    stream *s = calloc(1, sizeof *s);
    if (!s) return NULL;
    s->pull = pull;
    s->user = user;
    s->channels = channels;
    s->rate = rate;
    pthread_mutex_init(&s->mx, NULL);
    pthread_cond_init(&s->cv, NULL);
    s->as = open_stream(s);
    if (!s->as) {
        pthread_cond_destroy(&s->cv);
        pthread_mutex_destroy(&s->mx);
        free(s);
        return NULL;
    }
    return s;
}

void rt_audio_start(void *p) {
    stream *s = p;
    pthread_mutex_lock(&s->mx);
    s->running = 1;
    s->started = 1;
    if (s->as) AAudioStream_requestStart(s->as);
    pthread_mutex_unlock(&s->mx);
}

void rt_audio_stop(void *p) {
    stream *s = p;
    pthread_mutex_lock(&s->mx);
    s->running = 0;
    s->started = 0;
    if (s->as) AAudioStream_requestPause(s->as);
    pthread_mutex_unlock(&s->mx);
}

void rt_audio_close(void *p) {
    stream *s = p;
    pthread_mutex_lock(&s->mx);
    s->closing = 1;
    s->running = 0;
    while (s->reopening) pthread_cond_wait(&s->cv, &s->mx);
    AAudioStream *as = s->as;
    s->as = NULL;
    pthread_mutex_unlock(&s->mx);
    if (as) { AAudioStream_requestStop(as); AAudioStream_close(as); }
    pthread_cond_destroy(&s->cv);
    pthread_mutex_destroy(&s->mx);
    free(s);
}
