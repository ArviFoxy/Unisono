// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Fixed-capacity PCM sample ring buffer indexed by stream frame number.
//!
//! Paired with `unisono_core::receiver::Receiver`, whose presence bitmap
//! covers a window of `64 * N` frames starting at the playhead. Frame `n` is
//! stored at slot `n % capacity`, so advancing the playhead requires no data
//! movement and distinct frames within the active window never collide.
//!
//! Occupancy is tracked exclusively by `Receiver`; callers write only indices
//! admitted by `Receiver` and read only indices reported as present.

use unisono_core::packet::Format;
use unisono_dsp::format::{from_signed16, from_signed24};

/// A ring of frames, each of `channels` samples.
#[derive(Clone, Debug)]
pub struct Store {
    channels: usize,
    capacity: usize,
    samples: Box<[f32]>,
}

impl Store {
    /// A store with room for `capacity` frames of `channels` samples, all
    /// silent.
    #[must_use]
    pub fn new(capacity: usize, channels: usize) -> Store {
        Store {
            channels,
            capacity,
            samples: vec![0.0; capacity.saturating_mul(channels)].into_boxed_slice(),
        }
    }

    /// A store for a receiver whose stretch has `64 * words` indices, which
    /// is `Receiver<N, M, K>` with `N = words`.
    #[must_use]
    pub fn for_stretch(words: usize, channels: usize) -> Store {
        Store::new(words.saturating_mul(64), channels)
    }

    /// The number of frames there is room for.
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// The number of samples in a frame.
    #[must_use]
    pub fn channels(&self) -> usize {
        self.channels
    }

    /// The samples of the frame with `index`, if the store has places.
    fn place(&mut self, index: u64) -> Option<&mut [f32]> {
        let place = usize::try_from(index.checked_rem(self.capacity as u64)?).ok()?;
        let from = place.checked_mul(self.channels)?;
        self.samples.get_mut(from..from.checked_add(self.channels)?)
    }

    /// Writes the frames in `frames`, interleaved, as the frames with the
    /// indices `first`, `first + 1` and so on. Indices beyond the largest
    /// are left out.
    pub fn write(&mut self, first: u64, frames: &[f32]) {
        if self.channels == 0 {
            return;
        }
        for (frame, offset) in frames.chunks_exact(self.channels).zip(0u64..) {
            let Some(index) = first.checked_add(offset) else {
                break;
            };
            if let Some(place) = self.place(index) {
                place.copy_from_slice(frame);
            }
        }
    }

    /// Reads the frames with the indices `first`, `first + 1` and so on into
    /// `frames`, interleaved. Where there is no such index, or no place, the
    /// frame is silent.
    pub fn read(&self, first: u64, frames: &mut [f32]) {
        if self.channels == 0 {
            return;
        }
        for (frame, offset) in frames.chunks_exact_mut(self.channels).zip(0u64..) {
            let held = first
                .checked_add(offset)
                .and_then(|index| index.checked_rem(self.capacity as u64))
                .and_then(|place| usize::try_from(place).ok())
                .and_then(|place| place.checked_mul(self.channels))
                .and_then(|from| self.samples.get(from..from.checked_add(self.channels)?));
            match held {
                Some(held) => frame.copy_from_slice(held),
                None => frame.fill(0.0),
            }
        }
    }

    /// Writes those frames of a packet for whose index `room` says there is
    /// room, and returns how many that were.
    ///
    /// `first` is the index of the packet's first frame and `payload` its
    /// samples, written as `format` says, frame after frame, each frame with
    /// as many samples as the store's frames have. Frames that `payload` has
    /// only a part of are left out.
    pub fn write_packet(
        &mut self,
        first: u64,
        format: Format,
        payload: &[u8],
        room: impl Fn(u64) -> bool,
    ) -> usize {
        let bytes = self.channels.saturating_mul(format.bytes());
        if bytes == 0 {
            return 0;
        }
        let mut written = 0;
        for (frame, offset) in payload.chunks_exact(bytes).zip(0u64..) {
            let Some(index) = first.checked_add(offset) else {
                break;
            };
            if !room(index) {
                continue;
            }
            if let Some(place) = self.place(index) {
                match format {
                    Format::Signed16 => from_signed16(frame, place),
                    Format::Signed24 => from_signed24(frame, place),
                };
                written += 1;
            }
        }
        written
    }
}

#[cfg(test)]
mod tests {
    use super::Store;
    use unisono_core::packet::Format;

    /// A wrong place for an index, or a frame that spills into the next,
    /// would return other samples than were written.
    #[test]
    fn a_frame_is_read_back_from_the_place_its_index_gives_it() {
        let mut store = Store::new(8, 2);
        store.write(5, &[0.5, -0.5, 0.25, -0.25]);
        let mut frames = [9.0f32; 6];
        store.read(4, &mut frames);
        assert_eq!(frames, [0.0, 0.0, 0.5, -0.5, 0.25, -0.25]);
    }

    /// The ring wraps: index 8 of eight places is place 0, and a run that
    /// crosses the end continues at the start.
    #[test]
    fn indices_a_capacity_apart_share_a_place_and_runs_wrap() {
        let mut store = Store::new(8, 1);
        store.write(6, &[1.0, 2.0, 3.0, 4.0]);
        let mut frames = [0.0f32; 4];
        store.read(6, &mut frames);
        assert_eq!(frames, [1.0, 2.0, 3.0, 4.0]);
        // Indices 8 and 9 took the places of 0 and 1.
        store.read(0, &mut frames[..2]);
        assert_eq!(frames[..2], [3.0, 4.0]);
    }

    /// Only the frames with room are written: a frame behind the playhead
    /// must not overwrite the frame a capacity further on.
    #[test]
    fn a_packet_is_written_only_where_there_is_room() {
        let mut store = Store::new(4, 2);
        store.write(4, &[0.125, 0.125]);
        // Four frames from index 0 on; there is room for indices 1 to 3.
        let payload: Vec<u8> = (0..4i16)
            .flat_map(|frame| {
                let left = (frame + 1) * 0x0800;
                let right = -left;
                [left.to_le_bytes(), right.to_le_bytes()].concat()
            })
            .collect();
        let written = store.write_packet(0, Format::Signed16, &payload, |index| {
            (1..4).contains(&index)
        });
        assert_eq!(written, 3);
        let mut frames = [0.0f32; 8];
        store.read(0, &mut frames);
        // Place 0 still holds the frame with index 4.
        assert_eq!(
            frames,
            [0.125, 0.125, 0.125, -0.125, 0.1875, -0.1875, 0.25, -0.25]
        );
    }

    #[test]
    fn samples_of_three_bytes_are_read_with_their_sign() {
        let mut store = Store::new(4, 1);
        let payload = [0x00, 0x00, 0xc0, 0x00, 0x00, 0x20];
        assert_eq!(
            store.write_packet(2, Format::Signed24, &payload, |_| true),
            2
        );
        let mut frames = [0.0f32; 2];
        store.read(2, &mut frames);
        assert_eq!(frames, [-0.5, 0.25]);
    }

    #[test]
    fn a_store_without_places_or_channels_holds_nothing() {
        let mut empty = Store::new(0, 2);
        empty.write(0, &[1.0, 1.0]);
        let mut frames = [5.0f32; 2];
        empty.read(0, &mut frames);
        assert_eq!(frames, [0.0, 0.0]);
        assert_eq!(
            empty.write_packet(0, Format::Signed16, &[0; 8], |_| true),
            0
        );
        let mut mute = Store::new(4, 0);
        mute.write(0, &[1.0]);
        assert_eq!(mute.write_packet(0, Format::Signed16, &[0; 8], |_| true), 0);
    }
}
