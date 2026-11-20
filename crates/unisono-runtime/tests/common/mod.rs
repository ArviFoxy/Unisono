// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A sender for tests: the frames of a signal in packets, with the stamps
//! that a running sender gives them, and the loop that hands them to a
//! receiver between the cycles of its device.
//!
//! Times are whole nanoseconds. The sender's clock is the time of the test;
//! the receiver's clock reads `offset + s + s * skew / 10^9` when the
//! sender's reads `s`.

// Each test program uses a part of this.
#![allow(dead_code)]

use unisono_core::packet::{Audio, Format};
use unisono_core::player::Regulation;
use unisono_core::sender::{Sender, Settings as SenderSettings};
use unisono_dsp::Parameters;
use unisono_dsp::format::to_signed24;
use unisono_runtime::pump::{ReceiverPlayback, Settings};
use unisono_runtime::software::Output;

/// The receiver that the tests use: room for 4,096 frames, 64 samples of the
/// sender's clock, the arrivals of 8 packets.
pub(crate) type Listener = ReceiverPlayback<64, 64, 8>;

/// The number of samples in a frame.
pub(crate) const CHANNELS: usize = 2;

/// A sender and the link from it.
pub(crate) struct Line {
    pub(crate) rate: u32,
    /// Frames in a packet.
    pub(crate) packet: u16,
    /// Nanoseconds from the capture of a packet's last frame to its
    /// departure, and from its departure to its arrival.
    pub(crate) send: i64,
    pub(crate) delay: i64,
    /// The receiver's clock against the sender's.
    pub(crate) offset: i64,
    pub(crate) skew: i64,
    /// The sample of a channel of a frame.
    pub(crate) signal: fn(u64, usize) -> f32,
    /// The numbers of the packets that do not arrive.
    pub(crate) lost: Vec<u64>,
    /// Packets that arrive a second time: with the packet of the first
    /// number arrives a copy of the packet of the second.
    pub(crate) repeated: Vec<(u64, u64)>,
    /// The packets that have arrived, by their numbers.
    pub(crate) arrived: Vec<Sent>,
    pub(crate) sender: Sender,
    /// The number of the next packet.
    pub(crate) next: u64,
    /// The packet that was sent and has not arrived yet.
    pub(crate) under_way: Option<Sent>,
}

/// A packet on its way.
pub(crate) struct Sent {
    pub(crate) number: u64,
    pub(crate) header: Audio,
    pub(crate) payload: Vec<u8>,
    /// The receiver's clock at its arrival.
    pub(crate) arrival: i64,
}

impl Line {
    /// A sender of `rate` frames per second in packets of `packet` frames,
    /// whose receivers hold a latency of `level` nanoseconds.
    pub(crate) fn new(rate: u32, packet: u16, level: i64, signal: fn(u64, usize) -> f32) -> Line {
        let settings = SenderSettings {
            stream: 1,
            rate,
            channels: 2,
            format: Format::Signed24,
            span: 2_000,
            window: u32::from(packet) * 10,
            clock: 1,
        };
        Line {
            rate,
            packet,
            send: 500_000,
            delay: 1_000_000,
            offset: 3_600_000_000_000,
            skew: 0,
            signal,
            lost: Vec::new(),
            repeated: Vec::new(),
            arrived: Vec::new(),
            sender: Sender::new(settings, 7, level),
            next: 0,
            under_way: None,
        }
    }

    /// The sender's clock when it captured the frame with `index`.
    pub(crate) fn captured(&self, index: u64) -> i64 {
        i64::try_from(u128::from(index) * 1_000_000_000 / u128::from(self.rate)).unwrap_or(i64::MAX)
    }

    /// The receiver's clock when the sender's reads `time`.
    pub(crate) fn receiver_clock(&self, time: i64) -> i64 {
        let gained = i128::from(time) * i128::from(self.skew) / 1_000_000_000;
        self.offset + time + i64::try_from(gained).unwrap_or(0)
    }

    /// Sends the next packet.
    pub(crate) fn send(&mut self) -> Sent {
        let number = self.next;
        self.next += 1;
        let first = self.sender.next();
        let frames = u64::from(self.packet);
        let header = self.sender.packet(self.packet, self.captured(first), 0);
        let departure = self.captured(first + frames) + self.send;
        self.sender.departed(header.timeline, first, departure);
        let mut samples = Vec::new();
        for index in first..first + frames {
            for channel in 0..CHANNELS {
                samples.push((self.signal)(index, channel));
            }
        }
        let mut payload = vec![0u8; samples.len() * 3];
        to_signed24(&samples, &mut payload);
        Sent {
            number,
            header,
            payload,
            arrival: self.receiver_clock(departure + self.delay),
        }
    }
}

/// Settings of a receiver for a stream of `rate` frames per second, with a
/// gain of four per second, a limit of a thousandth and a jump beyond 240
/// frames.
pub(crate) fn settings(rate: u32, concealment: Parameters) -> Settings {
    Settings {
        stream: 1,
        rate,
        channels: 2,
        identity: 1,
        silence: 1_000_000_000,
        slope_limit: 200_000,
        regulation: Regulation {
            gain: 4 << 16,
            limit: 1_000_000,
            jump: 240,
        },
        concealment,
        block: 256,
    }
}

/// A concealment whose fades take no time: a frame comes out as it is or as
/// silence, which lets a test read every output sample exactly.
pub(crate) fn no_fades() -> Parameters {
    Parameters {
        fitted: 480,
        order: 32,
        fade_out: 0,
        fade_in: 0,
    }
}

/// Hands the packets of `line` to `listener` as they arrive, and runs the
/// cycles of `output` as they are due, up to the reading `until` of the
/// receiver's clock. Before each packet is made, `before` may change the
/// sender.
pub(crate) fn run(
    line: &mut Line,
    listener: &mut Listener,
    output: &mut Output,
    until: i64,
    mut before: impl FnMut(u64, &mut Sender),
) {
    loop {
        let sent = if let Some(sent) = line.under_way.take() {
            sent
        } else {
            before(line.next, &mut line.sender);
            line.send()
        };
        if sent.arrival <= output.due() {
            if sent.arrival > until {
                line.under_way = Some(sent);
                break;
            }
            if !line.lost.contains(&sent.number) {
                listener.packet(&sent.header, &sent.payload, sent.arrival);
            }
            for (with, copied) in &line.repeated {
                let copy = usize::try_from(*copied).ok();
                if let Some(copy) = copy.and_then(|number| line.arrived.get(number))
                    && *with == sent.number
                {
                    listener.packet(&copy.header, &copy.payload, sent.arrival);
                }
            }
            line.arrived.push(sent);
        } else {
            line.under_way = Some(sent);
            if output.due() > until {
                break;
            }
            output.cycle(listener);
        }
    }
}

/// The sample of a frame that says which frame it is: the index plus one, as
/// a 24-bit sample, on the first channel and its negative on the second. No
/// frame has the value of silence.
pub(crate) fn ramp(index: u64, channel: usize) -> f32 {
    // An index below 2^23 is exact as a 24-bit sample.
    #[allow(clippy::cast_precision_loss)]
    let value = (index + 1) as f32 / 8_388_608.0;
    if channel == 0 { value } else { -value }
}

/// The index of the frame that a sample of the first channel of [`ramp`]
/// came from, or `None` for silence and for a value that no frame has.
pub(crate) fn index_of(sample: f32) -> Option<u64> {
    let scaled = f64::from(sample) * 8_388_608.0;
    if scaled < 1.0 || scaled.fract() != 0.0 {
        return None;
    }
    // A whole number below 2^23.
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let index = scaled as u64 - 1;
    Some(index)
}
