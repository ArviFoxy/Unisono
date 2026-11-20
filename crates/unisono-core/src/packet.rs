// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The audio packet: a header of fixed size, then the samples.
//!
//! Every number in the header is written least significant byte first. All
//! parties of a stream run the same version of the software, so there is one
//! layout and nothing to negotiate: a packet of another version is rejected.

/// The first four bytes of every packet: the letters `unis`.
pub const MAGIC: u64 = 0x7369_6e75;

/// The version of the layout.
pub const VERSION: u8 = 1;

/// The kind of a packet that carries audio.
pub const KIND_AUDIO: u8 = 1;

/// The size of the header of an audio packet, in bytes.
pub const HEADER: usize = 84;

/// The bit of the flags that says the packet carries the departure of an
/// earlier packet.
pub const FLAG_STAMPED: u16 = 1;

/// How one sample of one channel is written.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Format {
    /// Two bytes, signed, least significant first.
    Signed16,
    /// Three bytes, signed, least significant first.
    Signed24,
}

impl Format {
    /// The number of bytes of one sample of one channel.
    #[must_use]
    pub fn bytes(self) -> usize {
        match self {
            Format::Signed16 => 2,
            Format::Signed24 => 3,
        }
    }

    fn code(self) -> u8 {
        match self {
            Format::Signed16 => 1,
            Format::Signed24 => 2,
        }
    }

    fn from_code(code: u8) -> Option<Format> {
        match code {
            1 => Some(Format::Signed16),
            2 => Some(Format::Signed24),
            _ => None,
        }
    }
}

/// The header of an audio packet.
///
/// Times are in nanoseconds on the sender's clock; a frame is one sample of
/// every channel.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Audio {
    /// Which stream of the sender this is.
    pub stream: u16,
    /// Which run of the sender's capture device the indices count in. A
    /// restart of the device, or of the sender, starts another.
    pub timeline: u64,
    /// The index of the packet's first frame within the timeline.
    pub index: u64,
    /// When the first frame was captured.
    pub capture: i64,
    /// How much faster than `rate` the capture device runs against the
    /// sender's clock, in parts per billion.
    pub drift: i32,
    /// Frames per second.
    pub rate: u32,
    /// The number of frames in the packet.
    pub frames: u16,
    /// The number of channels.
    pub channels: u8,
    /// How a sample is written.
    pub format: Format,
    /// The latency that every receiver holds for the packet's first frame.
    pub level: i64,
    /// How the level changes from frame to frame, in nanoseconds per second
    /// of stream.
    pub level_slope: i32,
    /// How long a receiver remembers samples for its estimate of the
    /// sender's clock, in milliseconds.
    pub span: u32,
    /// The number of frames that make up one window of that estimate.
    pub window: u32,
    /// Bits that qualify the packet: [`FLAG_STAMPED`].
    pub flags: u16,
    /// The protection against loss that the packet carries; 0 is none.
    pub protection: u16,
    /// The index of the first frame of an earlier packet of this timeline,
    /// if the flags say that the packet carries one.
    pub stamped_index: u64,
    /// When that earlier packet left the sender.
    pub stamped_departure: i64,
}

/// Why a datagram is not an audio packet of this version.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rejected {
    /// It is shorter than a header.
    TooShort,
    /// It does not start with the letters `unis`.
    NotUnisono,
    /// It is of another version, which is given.
    Version(u8),
    /// It is of another kind, which is given.
    Kind(u8),
    /// It names a sample format that does not exist, which is given.
    Format(u8),
    /// Its length is not that of the header and the samples it announces.
    Length,
}

/// The number in the `count` bytes of `bytes` from `at`, least significant
/// first, for a `count` of at most 8. `None` if `bytes` ends before them.
fn read(bytes: &[u8], at: usize, count: usize) -> Option<u64> {
    let mut value = 0u64;
    let mut i = 0usize;
    while i < count {
        let Some(place) = at.checked_add(i) else {
            return None;
        };
        let Some(byte) = bytes.get(place) else {
            return None;
        };
        // `i` is below 8, so the shift is below 64 and fits 32 bits.
        #[allow(clippy::cast_possible_truncation)]
        let shift = (i as u32).wrapping_mul(8);
        value |= (*byte as u64).wrapping_shl(shift);
        i = i.saturating_add(1);
    }
    Some(value)
}

/// Writes the low `count` bytes of `value` into `bytes` from `at`, least
/// significant first, for a `count` of at most 8, and says whether `bytes`
/// had room for them.
fn write(bytes: &mut [u8], at: usize, count: usize, value: u64) -> bool {
    let mut i = 0usize;
    while i < count {
        let Some(place) = at.checked_add(i) else {
            return false;
        };
        let Some(slot) = bytes.get_mut(place) else {
            return false;
        };
        // `i` is below 8; the cast to a byte keeps the low eight bits, which
        // is what is wanted.
        #[allow(clippy::cast_possible_truncation)]
        let shift = (i as u32).wrapping_mul(8);
        #[allow(clippy::cast_possible_truncation)]
        let byte = value.wrapping_shr(shift) as u8;
        *slot = byte;
        i = i.saturating_add(1);
    }
    true
}

/// The number of bytes of the samples that a header announces.
fn payload(header: &Audio) -> usize {
    // At most 65,535 frames of 255 channels of 3 bytes: no wrapping.
    (header.frames as usize)
        .wrapping_mul(header.channels as usize)
        .wrapping_mul(header.format.bytes())
}

/// Reads the header of the audio packet in `bytes`. The samples follow the
/// header, from byte [`HEADER`] on.
///
/// # Errors
///
/// The reason why `bytes` is not an audio packet of this version.
// The casts below take a number that was read from exactly as many bytes as
// the field has, or turn an unsigned number of 64 or 32 bits into the signed
// number with the same bits.
#[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
pub fn parse_audio(bytes: &[u8]) -> Result<Audio, Rejected> {
    if bytes.len() < HEADER {
        return Err(Rejected::TooShort);
    }
    let (
        Some(magic),
        Some(version),
        Some(kind),
        Some(stream),
        Some(timeline),
        Some(index),
        Some(capture),
        Some(rate),
    ) = (
        read(bytes, 0, 4),
        read(bytes, 4, 1),
        read(bytes, 5, 1),
        read(bytes, 6, 2),
        read(bytes, 8, 8),
        read(bytes, 16, 8),
        read(bytes, 24, 8),
        read(bytes, 32, 4),
    )
    else {
        return Err(Rejected::TooShort);
    };
    let (
        Some(frames),
        Some(channels),
        Some(format),
        Some(level),
        Some(level_slope),
        Some(span),
        Some(window),
        Some(flags),
    ) = (
        read(bytes, 36, 2),
        read(bytes, 38, 1),
        read(bytes, 39, 1),
        read(bytes, 40, 8),
        read(bytes, 48, 4),
        read(bytes, 52, 4),
        read(bytes, 56, 4),
        read(bytes, 60, 2),
    )
    else {
        return Err(Rejected::TooShort);
    };
    let (Some(protection), Some(stamped_index), Some(stamped_departure), Some(drift)) = (
        read(bytes, 62, 2),
        read(bytes, 64, 8),
        read(bytes, 72, 8),
        read(bytes, 80, 4),
    ) else {
        return Err(Rejected::TooShort);
    };
    if magic != MAGIC {
        return Err(Rejected::NotUnisono);
    }
    if version != VERSION as u64 {
        return Err(Rejected::Version(version as u8));
    }
    if kind != KIND_AUDIO as u64 {
        return Err(Rejected::Kind(kind as u8));
    }
    let Some(format) = Format::from_code(format as u8) else {
        return Err(Rejected::Format(format as u8));
    };
    let header = Audio {
        stream: stream as u16,
        timeline,
        index,
        capture: capture as i64,
        drift: drift as u32 as i32,
        rate: rate as u32,
        frames: frames as u16,
        channels: channels as u8,
        format,
        level: level as i64,
        level_slope: level_slope as u32 as i32,
        span: span as u32,
        window: window as u32,
        flags: flags as u16,
        protection: protection as u16,
        stamped_index,
        stamped_departure: stamped_departure as i64,
    };
    if bytes.len().wrapping_sub(HEADER) != payload(&header) {
        return Err(Rejected::Length);
    }
    Ok(header)
}

/// Writes `header` into the first [`HEADER`] bytes of `bytes`, and returns
/// the length of the whole packet, header and samples. `None` if `bytes` is
/// shorter than a header.
// The casts turn a signed number into the unsigned number with the same bits.
#[allow(clippy::cast_sign_loss)]
pub fn write_audio(header: &Audio, bytes: &mut [u8]) -> Option<usize> {
    if bytes.len() < HEADER {
        return None;
    }
    // Every field is written whether or not an earlier one found room, so
    // that the function is a plain sequence of writes.
    let mut written = write(bytes, 0, 4, MAGIC);
    written &= write(bytes, 4, 1, VERSION as u64);
    written &= write(bytes, 5, 1, KIND_AUDIO as u64);
    written &= write(bytes, 6, 2, header.stream as u64);
    written &= write(bytes, 8, 8, header.timeline);
    written &= write(bytes, 16, 8, header.index);
    written &= write(bytes, 24, 8, header.capture as u64);
    written &= write(bytes, 32, 4, header.rate as u64);
    written &= write(bytes, 36, 2, header.frames as u64);
    written &= write(bytes, 38, 1, header.channels as u64);
    written &= write(bytes, 39, 1, header.format.code() as u64);
    written &= write(bytes, 40, 8, header.level as u64);
    written &= write(bytes, 48, 4, header.level_slope as u32 as u64);
    written &= write(bytes, 52, 4, header.span as u64);
    written &= write(bytes, 56, 4, header.window as u64);
    written &= write(bytes, 60, 2, header.flags as u64);
    written &= write(bytes, 62, 2, header.protection as u64);
    written &= write(bytes, 64, 8, header.stamped_index);
    written &= write(bytes, 72, 8, header.stamped_departure as u64);
    written &= write(bytes, 80, 4, header.drift as u32 as u64);
    if written {
        Some(HEADER.wrapping_add(payload(header)))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use std::vec;
    use std::vec::Vec;

    use super::{Audio, Format, HEADER, Rejected, parse_audio, write_audio};

    fn header() -> Audio {
        Audio {
            stream: 0x0102,
            timeline: 0x1112_1314_1516_1718,
            index: 0x2122_2324_2526_2728,
            capture: -0x3132_3334_3536_3738,
            drift: -0x5152_5354,
            rate: 48_000,
            frames: 4,
            channels: 2,
            format: Format::Signed24,
            level: 12_345_678,
            level_slope: -7,
            span: 11_000,
            window: 4096,
            flags: 0,
            protection: 0,
            stamped_index: 0x4142_4344_4546_4748,
            stamped_departure: -1,
        }
    }

    /// A packet with `header` and samples that are all zero.
    fn packet(header: &Audio) -> Vec<u8> {
        let mut bytes = vec![0u8; 4096];
        let length = write_audio(header, &mut bytes).expect("room for a header");
        bytes.truncate(length);
        bytes
    }

    #[test]
    fn the_bytes_of_a_header_are_where_the_layout_puts_them() {
        let bytes = packet(&header());
        assert_eq!(bytes.len(), HEADER + 4 * 2 * 3);
        assert_eq!(&bytes[0..4], b"unis");
        assert_eq!(bytes[4..8], [1, 1, 0x02, 0x01]);
        assert_eq!(
            bytes[8..16],
            [0x18, 0x17, 0x16, 0x15, 0x14, 0x13, 0x12, 0x11]
        );
        assert_eq!(bytes[32..36], 48_000u32.to_le_bytes());
        assert_eq!(bytes[36..40], [4, 0, 2, 2]);
        assert_eq!(bytes[48..52], (-7i32).to_le_bytes());
        assert_eq!(bytes[72..80], [0xff; 8]);
        assert_eq!(bytes[80..84], (-0x5152_5354i32).to_le_bytes());
    }

    #[test]
    fn a_written_header_is_read_back_as_it_was() {
        let original = header();
        assert_eq!(parse_audio(&packet(&original)), Ok(original));
        let other = Audio {
            format: Format::Signed16,
            channels: 255,
            frames: 1,
            capture: i64::MIN,
            drift: i32::MIN,
            level_slope: i32::MIN,
            ..original
        };
        assert_eq!(parse_audio(&packet(&other)), Ok(other));
    }

    #[test]
    fn what_is_not_an_audio_packet_is_rejected_with_the_reason() {
        let good = packet(&header());
        assert_eq!(parse_audio(&good[..HEADER - 1]), Err(Rejected::TooShort));
        assert_eq!(parse_audio(&[]), Err(Rejected::TooShort));
        let mut bytes = good.clone();
        bytes[0] = b'U';
        assert_eq!(parse_audio(&bytes), Err(Rejected::NotUnisono));
        let mut bytes = good.clone();
        bytes[4] = 2;
        assert_eq!(parse_audio(&bytes), Err(Rejected::Version(2)));
        let mut bytes = good.clone();
        bytes[5] = 9;
        assert_eq!(parse_audio(&bytes), Err(Rejected::Kind(9)));
        let mut bytes = good.clone();
        bytes[39] = 0;
        assert_eq!(parse_audio(&bytes), Err(Rejected::Format(0)));
        let mut bytes = good.clone();
        bytes.push(0);
        assert_eq!(parse_audio(&bytes), Err(Rejected::Length));
        assert_eq!(parse_audio(&good[..good.len() - 1]), Err(Rejected::Length));
    }

    #[test]
    fn a_header_is_not_written_where_there_is_no_room() {
        let mut short = [0u8; HEADER - 1];
        assert_eq!(write_audio(&header(), &mut short), None);
    }
}
