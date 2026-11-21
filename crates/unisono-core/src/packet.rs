// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! The packets of a stream: audio from the sender, reports from receivers,
//! and the sender's answers to reports.
//!
//! An audio packet is a header of fixed size, then the samples. A receiver
//! sends reports, and the sender answers each with the time at which it
//! arrived; the two stamps of a report tell the receiver about the path back
//! to the sender what the stamps of audio packets tell it about the path
//! from the sender.
//!
//! Every number is written least significant byte first. All parties of a
//! stream run the same version of the software, so there is one layout and
//! nothing to negotiate: a packet of another version is rejected.

/// The first four bytes of every packet: the letters `unis`.
pub const MAGIC: u64 = 0x7369_6e75;

/// The version of the layout.
pub const VERSION: u8 = 1;

/// The kind of a packet that carries audio.
pub const KIND_AUDIO: u8 = 1;

/// The kind of a report of a receiver.
pub const KIND_REPORT: u8 = 2;

/// The kind of the sender's answer to a report.
pub const KIND_ECHO: u8 = 3;

/// The size of the header of an audio packet, in bytes.
pub const HEADER: usize = 88;

/// The size of what a report says, in bytes. A report is padded beyond it to
/// the size of an audio packet, so that it meets the same delays.
pub const REPORT: usize = 32;

/// The size of the sender's answer to a report, in bytes.
pub const ECHO: usize = 32;

/// The bit of the flags that says the packet carries the departure of an
/// earlier packet.
pub const FLAG_STAMPED: u16 = 1;

/// All flag bits defined by this version.
const KNOWN_FLAGS: u16 = FLAG_STAMPED;

/// Smallest permitted `drift` or `level_slope`, in parts per billion /
/// nanoseconds per second: `1_000_000_000 + slope` must stay positive.
const MIN_SLOPE: i32 = -999_999_999;

/// How one sample of one channel is written.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
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
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
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
    /// Identifies the sender's clock instance: changes when the host reboots,
    /// stays constant across capture-device restarts on the same host.
    pub clock: u32,
}

/// Why a datagram is not an audio packet of this version.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
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
    /// Its sample rate is zero.
    Rate,
    /// Its channel count is zero.
    Channels,
    /// Its flags carry bits not defined by this version, which are given.
    Flags(u16),
    /// Its loss protection scheme is not supported, which is given.
    Protection(u16),
    /// Its capture drift or level slope would give a non-positive pace.
    Pace,
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

/// Checks that the semantic fields of an audio header are valid.
fn validate_audio(header: &Audio) -> Result<(), Rejected> {
    if header.rate == 0 {
        return Err(Rejected::Rate);
    }
    if header.channels == 0 {
        return Err(Rejected::Channels);
    }
    if (header.flags & KNOWN_FLAGS) != header.flags {
        return Err(Rejected::Flags(header.flags));
    }
    if header.protection != 0 {
        return Err(Rejected::Protection(header.protection));
    }
    if header.drift < MIN_SLOPE || header.level_slope < MIN_SLOPE {
        return Err(Rejected::Pace);
    }
    Ok(())
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
    let found = match kind(bytes) {
        Ok(found) => found,
        Err(reason) => return Err(reason),
    };
    if found != KIND_AUDIO {
        return Err(Rejected::Kind(found));
    }
    let (Some(stream), Some(timeline), Some(index), Some(capture), Some(rate), Some(frames)) = (
        read(bytes, 6, 2),
        read(bytes, 8, 8),
        read(bytes, 16, 8),
        read(bytes, 24, 8),
        read(bytes, 32, 4),
        read(bytes, 36, 2),
    ) else {
        return Err(Rejected::TooShort);
    };
    let (
        Some(channels),
        Some(format),
        Some(level),
        Some(level_slope),
        Some(span),
        Some(window),
        Some(flags),
    ) = (
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
    let (Some(protection), Some(stamped_index), Some(stamped_departure), Some(drift), Some(clock)) = (
        read(bytes, 62, 2),
        read(bytes, 64, 8),
        read(bytes, 72, 8),
        read(bytes, 80, 4),
        read(bytes, 84, 4),
    ) else {
        return Err(Rejected::TooShort);
    };
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
        clock: clock as u32,
    };
    if let Err(reason) = validate_audio(&header) {
        return Err(reason);
    }
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
    written &= write(bytes, 84, 4, header.clock as u64);
    if written {
        Some(HEADER.wrapping_add(payload(header)))
    } else {
        None
    }
}

/// A report of a receiver to the sender.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Report {
    /// Which stream of the sender the receiver plays.
    pub stream: u16,
    /// The timeline that the receiver follows.
    pub timeline: u64,
    /// A number that tells this receiver from the others.
    pub receiver: u64,
    /// The number of this report among the receiver's reports.
    pub sequence: u64,
}

/// The sender's answer to a report: when the report arrived.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Echo {
    /// Which stream of the sender this is.
    pub stream: u16,
    /// The receiver whose report this answers.
    pub receiver: u64,
    /// The number of the report among that receiver's reports.
    pub sequence: u64,
    /// The sender's clock when the report arrived.
    pub arrival: i64,
}

/// The kind of the packet in `bytes`, if it is a packet of this version:
/// [`KIND_AUDIO`], [`KIND_REPORT`], [`KIND_ECHO`], or a kind this version
/// does not know.
///
/// # Errors
///
/// The reason why `bytes` is not a packet of this version.
// The casts take numbers that were read from one byte.
#[allow(clippy::cast_possible_truncation)]
pub fn kind(bytes: &[u8]) -> Result<u8, Rejected> {
    let (Some(magic), Some(version), Some(kind)) =
        (read(bytes, 0, 4), read(bytes, 4, 1), read(bytes, 5, 1))
    else {
        return Err(Rejected::TooShort);
    };
    if magic != MAGIC {
        return Err(Rejected::NotUnisono);
    }
    if version != VERSION as u64 {
        return Err(Rejected::Version(version as u8));
    }
    Ok(kind as u8)
}

/// Reads the report in `bytes`. What follows its first [`REPORT`] bytes is
/// padding.
///
/// # Errors
///
/// The reason why `bytes` is not a report of this version.
// The casts take numbers that were read from exactly as many bytes as the
// field has.
#[allow(clippy::cast_possible_truncation)]
pub fn parse_report(bytes: &[u8]) -> Result<Report, Rejected> {
    let found = match kind(bytes) {
        Ok(found) => found,
        Err(reason) => return Err(reason),
    };
    if found != KIND_REPORT {
        return Err(Rejected::Kind(found));
    }
    let (Some(stream), Some(timeline), Some(receiver), Some(sequence)) = (
        read(bytes, 6, 2),
        read(bytes, 8, 8),
        read(bytes, 16, 8),
        read(bytes, 24, 8),
    ) else {
        return Err(Rejected::TooShort);
    };
    Ok(Report {
        stream: stream as u16,
        timeline,
        receiver,
        sequence,
    })
}

/// Writes `report` into `bytes` as a packet of `length` bytes, padded with
/// zeros, and returns the length. A `length` below [`REPORT`] counts as
/// [`REPORT`]. `None` if `bytes` is shorter than the packet.
pub fn write_report(report: &Report, bytes: &mut [u8], length: usize) -> Option<usize> {
    let length = if length < REPORT { REPORT } else { length };
    if bytes.len() < length {
        return None;
    }
    let mut written = write(bytes, 0, 4, MAGIC);
    written &= write(bytes, 4, 1, VERSION as u64);
    written &= write(bytes, 5, 1, KIND_REPORT as u64);
    written &= write(bytes, 6, 2, report.stream as u64);
    written &= write(bytes, 8, 8, report.timeline);
    written &= write(bytes, 16, 8, report.receiver);
    written &= write(bytes, 24, 8, report.sequence);
    let mut place = REPORT;
    while place < length {
        written &= write(bytes, place, 1, 0);
        place = place.saturating_add(1);
    }
    if written { Some(length) } else { None }
}

/// The most stretches whose needs one report carries.
pub const RECENT: usize = 11;

/// The size of the needs of [`RECENT`] stretches in a report, in bytes: the
/// newest stretch, how many are given, and the need of each.
pub const NEEDS: usize = 9 + 4 * RECENT;

/// What a need that is not known is written as.
pub const UNKNOWN_NEED: i32 = i32::MIN;

/// The largest need of each of the last stretches of a timeline, as a report
/// carries them after its first [`REPORT`] bytes.
///
/// A stretch is the frames of a timeline whose index, divided by the window
/// of the sender's clock estimate that the audio packets give, is the same.
/// The need of a frame is the latency at which it would just have been in
/// time to be played.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct Recent {
    /// The newest stretch given.
    pub newest: u64,
    /// How many stretches are given, back from the newest; at most
    /// [`RECENT`].
    pub count: u8,
    /// The largest need of stretch `newest - i` at place `i`, in
    /// microseconds, or [`UNKNOWN_NEED`] if no frame of it arrived.
    pub needs: [i32; RECENT],
}

impl Recent {
    /// No stretch.
    pub const NONE: Recent = Recent {
        newest: 0,
        count: 0,
        needs: [UNKNOWN_NEED; RECENT],
    };
}

/// Writes `recent` after the first [`REPORT`] bytes of the report in
/// `bytes`, and says whether there was room for it.
// The casts turn a signed number into the unsigned one with the same bits.
#[allow(clippy::cast_sign_loss)]
pub fn write_needs(recent: &Recent, bytes: &mut [u8]) -> bool {
    let count = if (recent.count as usize) < RECENT {
        recent.count as usize
    } else {
        RECENT
    };
    let mut written = write(bytes, REPORT, 8, recent.newest);
    // `count` is at most `RECENT`, which fits a byte.
    written &= write(bytes, REPORT.wrapping_add(8), 1, count as u64);
    let mut i = 0usize;
    while i < count {
        let need = match recent.needs.get(i) {
            Some(need) => *need,
            None => UNKNOWN_NEED,
        };
        // `i` is below `RECENT`: no wrapping.
        let at = REPORT.wrapping_add(9).wrapping_add(i.wrapping_mul(4));
        written &= write(bytes, at, 4, need as u32 as u64);
        i = i.saturating_add(1);
    }
    written
}

/// Reads the needs that the report in `bytes` carries after its first
/// [`REPORT`] bytes. A report that carries none, or fewer than it says,
/// gives as many as are there: padding of zeros gives none.
// The casts take a number that was read from exactly as many bytes as the
// field has, or turn an unsigned number into the signed one with the same
// bits.
#[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
#[must_use]
pub fn parse_needs(bytes: &[u8]) -> Recent {
    let (Some(newest), Some(said)) = (
        read(bytes, REPORT, 8),
        read(bytes, REPORT.wrapping_add(8), 1),
    ) else {
        return Recent::NONE;
    };
    let mut recent = Recent::NONE;
    recent.newest = newest;
    let said = if (said as usize) < RECENT {
        said as usize
    } else {
        RECENT
    };
    let mut i = 0usize;
    while i < said {
        let at = REPORT.wrapping_add(9).wrapping_add(i.wrapping_mul(4));
        let Some(need) = read(bytes, at, 4) else {
            break;
        };
        if let Some(slot) = recent.needs.get_mut(i) {
            *slot = need as u32 as i32;
        }
        i = i.saturating_add(1);
        recent.count = i as u8;
    }
    recent
}

/// Reads the sender's answer to a report in `bytes`.
///
/// # Errors
///
/// The reason why `bytes` is not such an answer of this version.
// The casts take a number that was read from exactly as many bytes as the
// field has, or turn an unsigned number into the signed one with the same
// bits.
#[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
pub fn parse_echo(bytes: &[u8]) -> Result<Echo, Rejected> {
    let found = match kind(bytes) {
        Ok(found) => found,
        Err(reason) => return Err(reason),
    };
    if found != KIND_ECHO {
        return Err(Rejected::Kind(found));
    }
    let (Some(stream), Some(receiver), Some(sequence), Some(arrival)) = (
        read(bytes, 6, 2),
        read(bytes, 8, 8),
        read(bytes, 16, 8),
        read(bytes, 24, 8),
    ) else {
        return Err(Rejected::TooShort);
    };
    if bytes.len() != ECHO {
        return Err(Rejected::Length);
    }
    Ok(Echo {
        stream: stream as u16,
        receiver,
        sequence,
        arrival: arrival as i64,
    })
}

/// Writes `echo` into the first [`ECHO`] bytes of `bytes` and returns that
/// length. `None` if `bytes` is shorter.
// The cast turns a signed number into the unsigned one with the same bits.
#[allow(clippy::cast_sign_loss)]
pub fn write_echo(echo: &Echo, bytes: &mut [u8]) -> Option<usize> {
    if bytes.len() < ECHO {
        return None;
    }
    let mut written = write(bytes, 0, 4, MAGIC);
    written &= write(bytes, 4, 1, VERSION as u64);
    written &= write(bytes, 5, 1, KIND_ECHO as u64);
    written &= write(bytes, 6, 2, echo.stream as u64);
    written &= write(bytes, 8, 8, echo.receiver);
    written &= write(bytes, 16, 8, echo.sequence);
    written &= write(bytes, 24, 8, echo.arrival as u64);
    if written { Some(ECHO) } else { None }
}

#[cfg(test)]
mod tests {
    use std::vec;
    use std::vec::Vec;

    use super::{
        Audio, ECHO, Echo, Format, HEADER, KIND_AUDIO, KIND_ECHO, KIND_REPORT, NEEDS, RECENT,
        REPORT, Recent, Rejected, Report, UNKNOWN_NEED, kind, parse_audio, parse_echo, parse_needs,
        parse_report, write_audio, write_echo, write_needs, write_report,
    };

    fn header() -> Audio {
        Audio {
            stream: 0x0102,
            timeline: 0x1112_1314_1516_1718,
            index: 0x2122_2324_2526_2728,
            capture: -0x3132_3334_3536_3738,
            drift: -51_525_354,
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
            clock: 0x6162_6364,
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
        assert_eq!(bytes[80..84], (-51_525_354i32).to_le_bytes());
        assert_eq!(bytes[84..88], 0x6162_6364u32.to_le_bytes());
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
            drift: -999_999_999,
            level_slope: -999_999_999,
            flags: super::FLAG_STAMPED,
            clock: u32::MAX,
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
        bytes[32..36].copy_from_slice(&0u32.to_le_bytes());
        assert_eq!(parse_audio(&bytes), Err(Rejected::Rate));
        let mut bytes = good.clone();
        bytes[38] = 0;
        assert_eq!(parse_audio(&bytes), Err(Rejected::Channels));
        let mut bytes = good.clone();
        bytes[60..62].copy_from_slice(&2u16.to_le_bytes());
        assert_eq!(parse_audio(&bytes), Err(Rejected::Flags(2)));
        let mut bytes = good.clone();
        bytes[62..64].copy_from_slice(&1u16.to_le_bytes());
        assert_eq!(parse_audio(&bytes), Err(Rejected::Protection(1)));
        let mut bytes = good.clone();
        bytes[80..84].copy_from_slice(&(-1_000_000_000i32).to_le_bytes());
        assert_eq!(parse_audio(&bytes), Err(Rejected::Pace));
        let mut bytes = good.clone();
        bytes[48..52].copy_from_slice(&i32::MIN.to_le_bytes());
        assert_eq!(parse_audio(&bytes), Err(Rejected::Pace));
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

    #[test]
    fn the_needs_of_a_report_are_read_back_from_its_padding() {
        let report = Report {
            stream: 1,
            timeline: 2,
            receiver: 3,
            sequence: 4,
        };
        let mut bytes = vec![0u8; REPORT + NEEDS];
        assert_eq!(write_report(&report, &mut bytes, 0), Some(REPORT));
        // Padding of zeros carries no needs.
        assert_eq!(parse_needs(&bytes).count, 0);
        let mut recent = Recent::NONE;
        recent.newest = 1 << 40;
        recent.count = 3;
        recent.needs[..3].copy_from_slice(&[-7, i32::MAX, UNKNOWN_NEED]);
        assert!(write_needs(&recent, &mut bytes));
        assert_eq!(parse_needs(&bytes), recent);
        assert_eq!(parse_report(&bytes), Ok(report));
        // A report cut short gives the needs that are in it.
        let cut = parse_needs(&bytes[..REPORT + 9 + 4]);
        assert_eq!((cut.count, cut.needs[0]), (1, -7));
        assert!(!write_needs(&recent, &mut bytes[..REPORT + 9 + 8]));
        // A count beyond the most is read as the most.
        recent.count = 200;
        assert!(write_needs(&recent, &mut bytes));
        assert_eq!(usize::from(parse_needs(&bytes).count), RECENT);
        const { assert!(REPORT + NEEDS <= HEADER) };
    }

    #[test]
    fn a_report_is_padded_and_read_back() {
        let report = Report {
            stream: 0x0102,
            timeline: 0x1112_1314_1516_1718,
            receiver: 0x2122_2324_2526_2728,
            sequence: 0x3132_3334_3536_3738,
        };
        let mut bytes = [0xaau8; 200];
        assert_eq!(write_report(&report, &mut bytes, 150), Some(150));
        assert_eq!(bytes[4..8], [1, 2, 0x02, 0x01]);
        assert_eq!(bytes[24..32], 0x3132_3334_3536_3738u64.to_le_bytes());
        // The padding is zero, and nothing beyond the packet is touched.
        assert!(bytes[REPORT..150].iter().all(|byte| *byte == 0));
        assert_eq!(bytes[150], 0xaa);
        assert_eq!(parse_report(&bytes[..150]), Ok(report));
        assert_eq!(kind(&bytes[..150]), Ok(KIND_REPORT));
        // A length below what a report says is brought up to it.
        assert_eq!(write_report(&report, &mut bytes, 0), Some(REPORT));
        assert_eq!(write_report(&report, &mut bytes[..REPORT - 1], 0), None);
        assert_eq!(parse_report(&bytes[..REPORT - 1]), Err(Rejected::TooShort));
    }

    #[test]
    fn an_answer_to_a_report_is_read_back() {
        let echo = Echo {
            stream: 7,
            receiver: u64::MAX,
            sequence: 99,
            arrival: -5,
        };
        let mut bytes = [0u8; ECHO];
        assert_eq!(write_echo(&echo, &mut bytes), Some(ECHO));
        assert_eq!(
            bytes[24..32],
            [0xfb, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]
        );
        assert_eq!(parse_echo(&bytes), Ok(echo));
        assert_eq!(kind(&bytes), Ok(KIND_ECHO));
        let mut long = [0u8; ECHO + 1];
        long[..ECHO].copy_from_slice(&bytes);
        assert_eq!(parse_echo(&long), Err(Rejected::Length));
    }

    #[test]
    fn a_packet_of_one_kind_is_not_read_as_another() {
        let audio = packet(&header());
        assert_eq!(kind(&audio), Ok(KIND_AUDIO));
        assert_eq!(parse_report(&audio), Err(Rejected::Kind(KIND_AUDIO)));
        assert_eq!(parse_echo(&audio), Err(Rejected::Kind(KIND_AUDIO)));
        let mut bytes = [0u8; ECHO];
        let echo = Echo {
            stream: 1,
            receiver: 2,
            sequence: 3,
            arrival: 4,
        };
        write_echo(&echo, &mut bytes);
        assert_eq!(parse_audio(&bytes), Err(Rejected::TooShort));
        assert_eq!(parse_report(&bytes), Err(Rejected::Kind(KIND_ECHO)));
        assert_eq!(kind(&[]), Err(Rejected::TooShort));
        bytes[0] = 0;
        assert_eq!(kind(&bytes), Err(Rejected::NotUnisono));
    }
}
