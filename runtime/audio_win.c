/* Windows audio backend (also used by the host runner on other desktop builds that link winmm): waveOut with four
 * blocks of 1024 frames in flight, refilled by a time-critical thread that pulls from the OpenAL mixer (openal.c).
 * Latency is about 4 x 23 ms at 44100 Hz. The pull takes the mixer's lock, so the feeder thread is the only
 * caller of it and never runs game code.
 * NOVAHD_AUDIO_WAV=<file> also records the stream into a WAV file (for checking audio without listening). */
#include <stdio.h>
#include <stdlib.h>
#include <windows.h>
#include <mmsystem.h>

#include "rt.h"

#define BLOCKS 4
#define FRAMES 1024

typedef struct stream {
    HWAVEOUT wo;
    HANDLE event, thread;
    WAVEHDR hdr[BLOCKS];
    int16_t *buf[BLOCKS];
    int channels, rate;
    rt_audio_pull pull;
    void *user;
    volatile int running, quit;
    FILE *wav;
    uint32_t wav_bytes;
} stream;

static void wav_header(stream *s) {
    uint32_t rate = (uint32_t)s->rate, ch = (uint32_t)s->channels, byte_rate = rate * ch * 2, size = s->wav_bytes;
    uint8_t h[44] = {'R', 'I', 'F', 'F'};
    uint32_t riff = 36 + size, fmt_len = 16, data_len = size;
    uint16_t pcm = 1, ch16 = (uint16_t)ch, align = (uint16_t)(ch * 2), bits = 16;
    memcpy(h + 4, &riff, 4); memcpy(h + 8, "WAVEfmt ", 8); memcpy(h + 16, &fmt_len, 4); memcpy(h + 20, &pcm, 2);
    memcpy(h + 22, &ch16, 2); memcpy(h + 24, &rate, 4); memcpy(h + 28, &byte_rate, 4); memcpy(h + 32, &align, 2);
    memcpy(h + 34, &bits, 2); memcpy(h + 36, "data", 4); memcpy(h + 40, &data_len, 4);
    fseek(s->wav, 0, SEEK_SET);
    fwrite(h, 1, 44, s->wav);
    fseek(s->wav, 0, SEEK_END);
    fflush(s->wav);
}

static void fill(stream *s, int k) {
    if (s->running) s->pull(s->user, s->buf[k], FRAMES);
    else memset(s->buf[k], 0, (size_t)FRAMES * s->channels * 2);
    if (s->wav && s->running) {
        fwrite(s->buf[k], 2, (size_t)FRAMES * s->channels, s->wav);
        s->wav_bytes += (uint32_t)(FRAMES * s->channels * 2);
        if ((s->wav_bytes / (FRAMES * s->channels * 2)) % 64 == 0) wav_header(s);
    }
    waveOutWrite(s->wo, &s->hdr[k], sizeof(WAVEHDR));
}

static DWORD WINAPI feeder(void *p) {
    stream *s = p;
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_TIME_CRITICAL);
    for (int k = 0; k < BLOCKS; k++) fill(s, k);
    while (!s->quit) {
        WaitForSingleObject(s->event, 50);
        for (int k = 0; k < BLOCKS; k++)
            if (s->hdr[k].dwFlags & WHDR_DONE) fill(s, k);
    }
    return 0;
}

void *rt_audio_open(int rate, int channels, rt_audio_pull pull, void *user) {
    stream *s = calloc(1, sizeof *s);
    if (!s) return NULL;
    s->rate = rate;
    s->channels = channels;
    s->pull = pull;
    s->user = user;
    s->event = CreateEventA(NULL, FALSE, FALSE, NULL);
    WAVEFORMATEX f = {WAVE_FORMAT_PCM, (WORD)channels, (DWORD)rate, (DWORD)(rate * channels * 2), (WORD)(channels * 2), 16, 0};
    if (waveOutOpen(&s->wo, WAVE_MAPPER, &f, (DWORD_PTR)s->event, 0, CALLBACK_EVENT) != MMSYSERR_NOERROR) {
        rt_log("audio: waveOutOpen failed (%d Hz, %d channels)", rate, channels);
        CloseHandle(s->event);
        free(s);
        return NULL;
    }
    for (int k = 0; k < BLOCKS; k++) {
        s->buf[k] = calloc((size_t)FRAMES * channels, 2);
        if (!s->buf[k]) rt_fatal("audio: out of memory");
        s->hdr[k].lpData = (LPSTR)s->buf[k];
        s->hdr[k].dwBufferLength = (DWORD)(FRAMES * channels * 2);
        waveOutPrepareHeader(s->wo, &s->hdr[k], sizeof(WAVEHDR));
    }
    const char *wav = getenv("NOVAHD_AUDIO_WAV");
    if (wav && (s->wav = fopen(wav, "wb"))) wav_header(s);
    s->thread = CreateThread(NULL, 0, feeder, s, 0, NULL);
    if (!s->thread) rt_log("audio: CreateThread failed; no sound");
    return s;
}

void rt_audio_start(void *p) { ((stream *)p)->running = 1; }
void rt_audio_stop(void *p) { ((stream *)p)->running = 0; }

void rt_audio_close(void *p) {
    stream *s = p;
    s->quit = 1;
    SetEvent(s->event);
    /* wait for the feeder for good: it may be inside pull (waiting for the mixer lock) and must not touch s after
     * it is freed. openal.c calls this outside its lock, so the wait always ends. */
    if (s->thread) WaitForSingleObject(s->thread, INFINITE);
    waveOutReset(s->wo);
    for (int k = 0; k < BLOCKS; k++) waveOutUnprepareHeader(s->wo, &s->hdr[k], sizeof(WAVEHDR));
    waveOutClose(s->wo);
    if (s->wav) { wav_header(s); fclose(s->wav); }
    if (s->thread) CloseHandle(s->thread);
    CloseHandle(s->event);
    for (int k = 0; k < BLOCKS; k++) free(s->buf[k]);
    free(s);
}
