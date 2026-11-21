/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

/* A sender and a receiver in one program, through the interface for C: a
 * capture device that makes a ramp and a playback device, each a loop that
 * calls unisono once for every 256 frames at the pace of the clock. Prints
 * how many of the frames played in the last second were of the stream, and
 * the largest distance of a frame played from the ramp. */

#include <stdio.h>
#include <string.h>
#include <time.h>

#include "unisono.h"

enum { RATE = 48000, CYCLE = 256, CHANNELS = 2 };

/* Waits until the clock reads `time`. */
static void wait_until(int64_t time) {
    for (;;) {
        int64_t left = time - unisono_clock();
        if (left <= 0) {
            return;
        }
        struct timespec nap = {left / 1000000000, left % 1000000000};
        nanosleep(&nap, NULL);
    }
}

int main(void) {
    char error[200] = "";

    unisono_receiver_settings listening;
    unisono_receiver_defaults(&listening);
    listening.listen = "127.0.0.1:0";
    unisono_receiver *receiver =
        unisono_receiver_start(&listening, error, sizeof error);
    if (receiver == NULL) {
        fprintf(stderr, "receiver: %s\n", error);
        return 1;
    }

    char to[32];
    snprintf(to, sizeof to, "127.0.0.1:%u",
             (unsigned)unisono_receiver_port(receiver));
    const char *receivers[] = {to};
    unisono_sender_settings sending;
    unisono_sender_defaults(&sending);
    sending.receivers = receivers;
    sending.receiver_count = 1;
    sending.cycle_frames = CYCLE;
    sending.choose_level = 0;
    unisono_sender *sender = unisono_sender_start(&sending, error, sizeof error);
    if (sender == NULL) {
        fprintf(stderr, "sender: %s\n", error);
        return 1;
    }

    /* A setting that cannot be used is refused, with the reason. */
    sending.bits = 12;
    if (unisono_sender_start(&sending, error, sizeof error) != NULL ||
        strstr(error, "16 or 24") == NULL) {
        fprintf(stderr, "a sample of 12 bits was taken: %s\n", error);
        return 1;
    }

    static float captured[CYCLE * CHANNELS];
    static float played[CYCLE * CHANNELS];
    const int64_t start = unisono_clock();
    const int cycles = 3 * RATE / CYCLE;
    long of_stream = 0;
    double furthest = 0.0;
    for (int cycle = 0; cycle < cycles; cycle++) {
        const uint64_t position = (uint64_t)cycle * CYCLE;
        const int64_t time = start + (int64_t)(position * 1000000000 / RATE);
        /* The capture device hands over a cycle when its last frame is
         * captured; the frame counted `i` is the sample `(i + 1) / 2^23`. */
        wait_until(time + (int64_t)CYCLE * 1000000000 / RATE);
        for (int i = 0; i < CYCLE; i++) {
            float sample = (float)(position + i + 1) / 8388608.0f;
            captured[i * CHANNELS] = sample;
            captured[i * CHANNELS + 1] = -sample;
        }
        unisono_sender_capture(sender, captured, CYCLE, position, time);
        /* The playback device asks for a cycle 4 ms before it plays it. */
        const int64_t leaves = time + (int64_t)CYCLE * 1000000000 / RATE + 4000000;
        unisono_receiver_play(receiver, played, CYCLE, position, leaves);
        if (cycle < 2 * RATE / CYCLE) {
            continue;
        }
        for (int i = 0; i < CYCLE; i++) {
            float left = played[i * CHANNELS];
            if (left == 0.0f) {
                continue;
            }
            /* The frame that is due: captured the level, 30 ms, before this
             * one leaves the device. */
            double frame = (double)left * 8388608.0 - 1.0;
            double due = (double)(position + i) +
                         ((double)CYCLE / RATE + 0.004 - 0.030) * RATE;
            double off = frame - due;
            if (off < 0) {
                off = -off;
            }
            if (off < 48.0) {
                of_stream++;
                if (off > furthest) {
                    furthest = off;
                }
            }
        }
    }
    unisono_sender_stop(sender);
    unisono_receiver_stop(receiver);
    printf("of-stream %ld furthest %.3f\n", of_stream, furthest);
    return 0;
}
