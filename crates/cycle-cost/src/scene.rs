// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! A sender, a link and a receiver with its device, brought to the state
//! that a case measures.
//!
//! Times are whole nanoseconds. The receiver's clock is an hour ahead of the
//! sender's, a packet leaves half a millisecond after its last frame was
//! captured and takes a millisecond, and the receivers hold 20 ms.

use unisono_core::device::Device;
use unisono_core::packet::{Audio, Format};
use unisono_core::player::Regulation;
use unisono_core::sender::{Sender, Settings as SenderSettings};
use unisono_dsp::Parameters;
use unisono_dsp::format::to_signed24;
use unisono_runtime::audio::Playback;
use unisono_runtime::pump::{ReceiverPlayback, Settings};

const RATE: u32 = 48_000;
const CHANNELS: usize = 2;
const PACKET: u16 = 240;
const CYCLE: usize = 256;
const OFFSET: i64 = 3_600_000_000_000;
const SEND: i64 = 500_000;
const DELAY: i64 = 1_000_000;
const LEVEL: i64 = 20_000_000;
/// Packets in a window of the clock estimate.
const WINDOW: u64 = 64;

type Listener = ReceiverPlayback<64, 64, 8>;

/// The sender's clock when it captured the frame with `index`.
fn captured(index: u64) -> i64 {
    i64::try_from(u128::from(index) * 1_000_000_000 / u128::from(RATE)).unwrap_or(i64::MAX)
}

/// A stream and its receiver.
pub(crate) struct Scene {
    sender: Sender,
    listener: Box<Listener>,
    line: Device<64>,
    /// The number of the next packet and of the next cycle.
    packets: u64,
    cycles: u64,
    lost: fn(u64) -> bool,
    payload: Vec<u8>,
    samples: Vec<f32>,
    output: Vec<f32>,
}

impl Scene {
    /// A scene at its start, in which the packets for which `lost` holds do
    /// not arrive.
    fn new(lost: fn(u64) -> bool) -> Scene {
        let settings = SenderSettings {
            stream: 1,
            rate: RATE,
            channels: 2,
            format: Format::Signed24,
            // Longer than 64 windows, so that the memory of the estimate
            // fills.
            span: 30_000,
            window: u32::from(PACKET) * 64,
            clock: 1,
        };
        let listener = Listener::new(&Settings {
            stream: 1,
            rate: RATE,
            channels: 2,
            identity: 1,
            silence: 1_000_000_000,
            slope_limit: 200_000,
            regulation: Regulation {
                gain: 4 << 16,
                limit: 1_000_000,
                jump: 240,
            },
            concealment: Parameters::for_rate(RATE),
            block: CYCLE,
        });
        Scene {
            sender: Sender::new(settings, 7, LEVEL),
            listener: Box::new(listener),
            line: Device::new(RATE),
            packets: 0,
            cycles: 0,
            lost,
            payload: vec![0; usize::from(PACKET) * CHANNELS * 3],
            samples: vec![0.0; usize::from(PACKET) * CHANNELS],
            output: vec![0.0; CYCLE * CHANNELS],
        }
    }

    /// The receiver's clock when the next packet arrives.
    fn next_arrival(&self) -> i64 {
        let last = (self.packets + 1) * u64::from(PACKET);
        OFFSET + captured(last) + SEND + DELAY
    }

    /// The receiver's clock when the first frame of the next cycle leaves
    /// the device.
    fn next_cycle(&self) -> i64 {
        OFFSET + captured(self.cycles * CYCLE as u64)
    }

    /// Makes the next packet and, unless it is lost, hands it to the
    /// receiver.
    pub(crate) fn packet(&mut self) {
        let number = self.packets;
        let arrival = self.next_arrival();
        let first = self.sender.next();
        let header: Audio = self.sender.packet(PACKET, captured(first), 0);
        self.sender.departed(
            header.timeline,
            first,
            captured(first + u64::from(PACKET)) + SEND,
        );
        for (place, sample) in self.samples.iter_mut().enumerate() {
            // A tone of 1 kHz in the first channel and of 3 kHz in the
            // second.
            #[allow(clippy::cast_precision_loss)]
            let frame = (first + (place / CHANNELS) as u64) as f32;
            let tone = if place % CHANNELS == 0 {
                1_000.0
            } else {
                3_000.0
            };
            *sample = 0.5 * (std::f32::consts::TAU * tone * frame / 48_000.0).sin();
        }
        to_signed24(&self.samples, &mut self.payload);
        self.packets += 1;
        if !(self.lost)(number) {
            self.listener.packet(&header, &self.payload, arrival);
        }
    }

    /// Runs the next cycle of the device.
    pub(crate) fn cycle(&mut self) {
        let position = self.cycles * CYCLE as u64;
        let time = self.next_cycle();
        self.cycles += 1;
        self.listener.cycle(&mut self.output, position, time);
    }

    /// Gives the line of the device the report of the next cycle and asks it
    /// when that cycle begins and ends.
    pub(crate) fn device(&mut self) {
        let position = self.cycles * CYCLE as u64;
        self.line.observe(position, self.next_cycle());
        let begins = self.line.when(position);
        let ends = self.line.when(position + CYCLE as u64);
        std::hint::black_box((begins, ends));
    }

    /// Runs packets and cycles in the order of their times, as long as
    /// `more` holds.
    fn run_while(&mut self, more: impl Fn(&Scene) -> bool) {
        while more(self) {
            if self.next_arrival() <= self.next_cycle() {
                self.packet();
            } else {
                let position = self.cycles * CYCLE as u64;
                self.line.observe(position, self.next_cycle());
                self.cycle();
            }
        }
    }

    /// A scene that has run for two seconds, in which the packets for which
    /// `lost` holds do not arrive.
    pub(crate) fn running(lost: fn(u64) -> bool) -> Scene {
        let mut scene = Scene::new(lost);
        scene.run_while(|scene| scene.next_cycle() < OFFSET + 2_000_000_000);
        scene
    }

    /// A scene that has run until just before the first cycle in which the
    /// concealment has to make frames: twenty packets are lost after two
    /// seconds.
    pub(crate) fn at_first_concealed() -> Scene {
        let lost = |number: u64| (400..420).contains(&number);
        // Run once to find the cycle, then again up to it. At its start a
        // stream has frames to conceal too; those are left behind first.
        let settled = |scene: &Scene| scene.next_cycle() >= OFFSET + 1_900_000_000;
        let mut trial = Scene::new(lost);
        trial.run_while(|scene| !settled(scene));
        let before = trial.listener.totals().concealed;
        trial.run_while(|scene| scene.listener.totals().concealed == before);
        let first = trial.cycles - 1;
        let mut scene = Scene::new(lost);
        scene.run_while(|scene| scene.cycles < first || scene.next_arrival() <= scene.next_cycle());
        scene
    }

    /// A scene in which the next packet ends a window of the estimate of the
    /// sender's clock, and that estimate remembers as many samples as it
    /// can.
    pub(crate) fn before_window_end() -> Scene {
        let mut scene = Scene::new(|_| false);
        // The first packet of a window ends the window before it. After 70
        // windows the memory of 64 samples is full.
        scene.run_while(|scene| scene.packets < 70 * WINDOW + 1);
        while scene.next_cycle() < scene.next_arrival() {
            scene.cycle();
        }
        scene
    }
}
