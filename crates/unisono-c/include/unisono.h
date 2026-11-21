/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

/* unisono for programs written in C.
 *
 * A sender is handed the frames that a capture device captured, cycle after
 * cycle, and sends them to its receivers. A receiver fills the frames that a
 * playback device is about to play. Both are meant to be called from the
 * device's own cycle: `unisono_sender_capture` and `unisono_receiver_play`
 * do not wait, do not allocate and do not enter the kernel. Each sender and
 * each receiver runs one thread of its own for the network.
 *
 * Frames are interleaved samples of type `float` between -1 and 1. With each
 * cycle the caller gives the device's count of frames at the first frame of
 * the cycle, which goes up by one for each frame from wherever it started,
 * and the time at which that frame was captured, or leaves the playback
 * device, on the clock that `unisono_clock` reads. The better these two
 * numbers are, the better the receivers play together.
 *
 * A sender or a receiver is used by one thread at a time. */

#ifndef UNISONO_H
#define UNISONO_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The clock that every time is on: the host's clock that no one adjusts, in
 * nanoseconds. */
int64_t unisono_clock(void);

/* What a sender is set up with. `unisono_sender_defaults` fills in all but
 * the receivers. */
typedef struct unisono_sender_settings {
    /* Where to send from, as "address:port"; NULL for any. */
    const char *bind;
    /* The receivers, each as "address:port"; at least 1 and at most 4096. */
    const char *const *receivers;
    size_t receiver_count;
    /* The stream's number, which its receivers are set up with as well. */
    uint16_t stream;
    /* Frames per second (1 to 1000000), and samples in a frame (at least 1). */
    uint32_t rate;
    uint8_t channels;
    /* Bits of a sample on the wire: 16 or 24. */
    uint8_t bits;
    /* Frames in a packet; header plus payload must fit within 9000 bytes. */
    uint16_t packet_frames;
    /* The most frames that one call of `unisono_sender_capture` hands over;
     * the 64-buffer capture ring (`64 * cycle_frames * channels * sizeof(float)`)
     * must not exceed 64 MiB. */
    uint32_t cycle_frames;
    /* The latency that receivers hold at the start, in nanoseconds. */
    int64_t level;
    /* Not zero: the latency is chosen from what the receivers report. */
    int choose_level;
    /* Not zero: packets are kept for a second, to be sent again to a
     * receiver that asks for frames it misses. */
    int protection;
} unisono_sender_settings;

/* A sender that runs. */
typedef struct unisono_sender unisono_sender;

/* Fills `settings` with what the `unisono` program takes when nothing is
 * said: stream 1, 48000 frames a second, two channels, 24 bits, packets of
 * 240 frames, cycles of up to 4096 frames, a latency of 30 ms that is
 * chosen from the receivers' reports, and protection. No receivers. */
void unisono_sender_defaults(unisono_sender_settings *settings);

/* Starts a sender. NULL if the settings are not usable or the socket cannot
 * be had; `error`, if not NULL, then holds the reason, in at most
 * `error_size` bytes with the zero that ends it. */
unisono_sender *unisono_sender_start(const unisono_sender_settings *settings,
                                     char *error, size_t error_size);

/* Hands over the `frame_count` frames at `frames` that the capture device
 * captured in one cycle. `position` is the device's count of frames at the
 * first of them and `time` when that frame was captured. Calls with a NULL or
 * misaligned pointer, `frame_count == 0`, or a byte size exceeding
 * `PTRDIFF_MAX` are ignored without error. */
void unisono_sender_capture(unisono_sender *sender, const float *frames,
                            size_t frame_count, uint64_t position,
                            int64_t time);

/* Stops a sender and frees it. */
void unisono_sender_stop(unisono_sender *sender);

/* What a receiver is set up with. */
typedef struct unisono_receiver_settings {
    /* Where to receive, as "address:port"; with port 0 the system chooses
     * the port, and `unisono_receiver_port` says which. */
    const char *listen;
    /* The stream's number. */
    uint16_t stream;
    /* A number that tells this receiver from the others of the stream. */
    uint64_t identity;
    /* Frames per second (1 to 1000000), and samples in a frame (at least 1). */
    uint32_t rate;
    uint8_t channels;
} unisono_receiver_settings;

/* A receiver that runs. */
typedef struct unisono_receiver unisono_receiver;

/* Fills `settings` with stream 1, identity 1, 48000 frames a second and two
 * channels. No address. */
void unisono_receiver_defaults(unisono_receiver_settings *settings);

/* Starts a receiver. NULL on failure, with the reason in `error` as for a
 * sender. */
unisono_receiver *unisono_receiver_start(
    const unisono_receiver_settings *settings, char *error,
    size_t error_size);

/* The port that the receiver receives on. Must not be called concurrently
 * with `unisono_receiver_play` or `unisono_receiver_stop`. */
uint16_t unisono_receiver_port(const unisono_receiver *receiver);

/* Fills the `frame_count` frames at `frames` with what the playback device
 * is to play in one cycle. `frames` need not be initialized by the caller when
 * valid arguments are passed. `position` is the device's count of frames at
 * the first of them and `time` when that frame leaves the device. Frames for
 * which the stream has nothing are silence or a continuation of what was
 * played.
 *
 * If `receiver` or `frames` is NULL or misaligned, if `frame_count == 0`, or
 * if the byte size exceeds `PTRDIFF_MAX`, the call is ignored without error
 * and nothing is written to `frames`. */
void unisono_receiver_play(unisono_receiver *receiver, float *frames,
                           size_t frame_count, uint64_t position,
                           int64_t time);

/* Stops a receiver and frees it. */
void unisono_receiver_stop(unisono_receiver *receiver);

#ifdef __cplusplus
}
#endif

#endif
