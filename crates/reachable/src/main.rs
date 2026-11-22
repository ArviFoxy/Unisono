// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Checks what the machine code of entry points of a shared library can
//! reach.
//!
//! Usage: `reachable LIBRARY ENTRY...`
//!
//! Follows every direct call, unconditional jump, conditional jump, linear
//! fallthrough, and relocation-backed indirect call or jump from the entry
//! points through the demangled disassembly that `objdump` produces. Fails
//! closed unless every reached function belongs to unisono, one of the
//! allowed memory functions, or one of the compiler's 128-bit arithmetic
//! helpers, and unless no reached unisono function enters the kernel, executes
//! a trap instruction, or branches through an unresolved pointer or
//! unsupported relocation.
//!
//! Only x86-64 ELF libraries are audited; unsupported architectures fail with
//! an explicit error rather than reporting zero problems.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Bound;
use std::process::{Command, ExitCode};

/// Functions outside unisono that the real-time code may reach.
const ALLOWED: &[&str] = &[
    "memcpy",
    "memmove",
    "memset",
    "memcmp",
    "bcmp",
    "__divti3",
    "__udivti3",
    "__modti3",
    "__umodti3",
    "__muloti4",
    "__udivmodti4",
    "__ashlti3",
    "__ashrti3",
    "__lshrti3",
    "__multi3",
];

/// Demangled crate and entry-point prefixes belonging to unisono's real-time path.
const OURS_PREFIXES: &[&str] = &[
    "realtime_",
    "unisono_core::",
    "unisono_dsp::",
    "unisono_runtime::",
    "unisono_realtime_audio::",
    "unisono_realtime_check::",
];

/// Relocation types permitted for GOT/function-pointer dispatch.
const ALLOWED_RELOCATIONS: &[&str] = &[
    "R_X86_64_GLOB_DAT",
    "R_X86_64_JUMP_SLOT",
    "R_X86_64_RELATIVE",
    "R_X86_64_64",
];

/// Whether `name` is a demangled function belonging to unisono.
///
/// Rejects standard-library generics instantiated over unisono types such as
/// `core::ptr::drop_in_place<unisono_...>` or
/// `<alloc::raw_vec::RawVec<unisono_...>>::grow_one`.
fn ours(name: &str) -> bool {
    let stripped = name.strip_prefix('<').unwrap_or(name);
    OURS_PREFIXES
        .iter()
        .any(|prefix| stripped.starts_with(prefix))
}

/// Whether a function outside unisono may be reached.
fn allowed(name: &str) -> bool {
    let bare = name.split('@').next().unwrap_or(name);
    ALLOWED.contains(&bare)
}

/// The output of `objdump` with `arguments` on `library`.
fn objdump(arguments: &[&str], library: &str) -> Result<String, String> {
    let output = Command::new("objdump")
        .args(arguments)
        .arg(library)
        .output()
        .map_err(|error| format!("running objdump: {error}"))?;
    if !output.status.success() {
        return Err(format!("objdump {arguments:?} {library} failed"));
    }
    String::from_utf8(output.stdout).map_err(|_| "objdump wrote what is not text".into())
}

/// Confirms `objdump -f` reports an x86-64 ELF library.
fn check_architecture(headers: &str) -> Result<(), String> {
    for line in headers.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("architecture:") {
            if trimmed.contains("i386:x86-64") {
                return Ok(());
            }
            return Err(format!(
                "unsupported architecture ({trimmed}); reachable audits x86-64 ELF libraries only"
            ));
        }
    }
    Err("could not determine architecture from objdump -f".into())
}

/// A hexadecimal number.
fn hex(text: &str) -> Option<u64> {
    u64::from_str_radix(text.trim_start_matches("0x"), 16).ok()
}

/// A disassembled function and its lines.
struct Function {
    name: String,
    lines: Vec<String>,
}

/// The functions of a disassembly, indexed by both start address and name.
struct Disassembly {
    by_addr: BTreeMap<u64, Function>,
    by_name: HashMap<String, Vec<u64>>,
}

impl Disassembly {
    fn read(text: &str) -> Disassembly {
        let mut by_addr: BTreeMap<u64, Function> = BTreeMap::new();
        let mut by_name: HashMap<String, Vec<u64>> = HashMap::new();
        let mut current: Option<u64> = None;
        for line in text.lines() {
            // "0000000000001234 <name>:" (including nested angle brackets).
            if let Some((address, rest)) = line.split_once(" <")
                && let Some(name) = rest.strip_suffix(">:")
                && let Some(start) = hex(address.trim())
            {
                by_addr.insert(
                    start,
                    Function {
                        name: name.to_string(),
                        lines: Vec::new(),
                    },
                );
                by_name.entry(name.to_string()).or_default().push(start);
                current = Some(start);
            } else if let Some(start) = current
                && !line.trim().is_empty()
                && let Some(function) = by_addr.get_mut(&start)
            {
                function.lines.push(line.to_string());
            }
        }
        Disassembly { by_addr, by_name }
    }

    /// The function that holds `address`: its start address and name.
    fn containing(&self, address: u64) -> Option<(u64, &str)> {
        self.by_addr
            .range(..=address)
            .next_back()
            .map(|(start, function)| (*start, function.name.as_str()))
    }

    /// The function immediately following `start` in address order.
    fn next_after(&self, start: u64) -> Option<u64> {
        self.by_addr
            .range((Bound::Excluded(start), Bound::Unbounded))
            .next()
            .map(|(next, _)| *next)
    }
}

/// One dynamic relocation entry from `objdump -R -C`.
struct Relocation {
    kind: String,
    target: String,
}

/// Parses virtual address ranges `[lo, hi)` that are immutable after dynamic
/// linking from `objdump -p`: `PT_GNU_RELRO` (`RELRO`) segments and
/// non-writable `LOAD` segments.
fn immutable_ranges(program_headers: &str) -> Vec<(u64, u64)> {
    let mut ranges = Vec::new();
    let mut pending: Option<(bool, u64)> = None;
    for line in program_headers.lines() {
        let trimmed = line.trim();
        if let Some((kind, rest)) = split_token(trimmed) {
            if kind == "RELRO" || kind == "LOAD" {
                let vaddr = rest
                    .split_whitespace()
                    .skip_while(|&tok| tok != "vaddr")
                    .nth(1)
                    .and_then(hex);
                pending = vaddr.map(|addr| (kind == "RELRO", addr));
                continue;
            }
            if kind == "filesz"
                && let Some((is_relro, vaddr)) = pending.take()
            {
                let tokens: Vec<&str> = trimmed.split_whitespace().collect();
                let memsz = tokens
                    .iter()
                    .position(|&tok| tok == "memsz")
                    .and_then(|pos| tokens.get(pos + 1))
                    .and_then(|val| hex(val));
                let flags = tokens
                    .iter()
                    .position(|&tok| tok == "flags")
                    .and_then(|pos| tokens.get(pos + 1))
                    .copied()
                    .unwrap_or("");
                let read_only = is_relro || !flags.contains('w');
                if read_only
                    && let Some(size) = memsz
                    && size > 0
                {
                    ranges.push((vaddr, vaddr.saturating_add(size)));
                }
            }
        }
    }
    ranges
}

/// Whether the 8-byte pointer slot at `slot` lies completely inside an
/// immutable (`PT_GNU_RELRO` or non-writable `LOAD`) segment.
fn slot_is_immutable(slot: u64, immutable: &[(u64, u64)]) -> bool {
    let Some(end) = slot.checked_add(8) else {
        return false;
    };
    immutable.iter().any(|&(lo, hi)| slot >= lo && end <= hi)
}

/// The table of addresses: relocation type and target for each offset.
fn table(text: &str) -> HashMap<u64, Relocation> {
    let mut table = HashMap::new();
    for line in text.lines() {
        let trimmed = line.trim();
        let Some((offset_str, after_offset)) = split_token(trimmed) else {
            continue;
        };
        let Some(offset) = hex(offset_str) else {
            continue;
        };
        let Some((kind, target)) = split_token(after_offset) else {
            continue;
        };
        let target = target.trim();
        if !target.is_empty() {
            table.insert(
                offset,
                Relocation {
                    kind: kind.to_string(),
                    target: target.to_string(),
                },
            );
        }
    }
    table
}

/// Splits the first whitespace-delimited token and the trimmed remainder.
fn split_token(text: &str) -> Option<(&str, &str)> {
    let trimmed = text.trim_start();
    if trimmed.is_empty() {
        return None;
    }
    match trimmed.find(char::is_whitespace) {
        Some(end) => Some((&trimmed[..end], trimmed[end..].trim_start())),
        None => Some((trimmed, "")),
    }
}

/// Whether `token` is an x86-64 instruction prefix printed before a mnemonic.
fn is_prefix(token: &str) -> bool {
    matches!(
        token,
        "bnd"
            | "notrack"
            | "rep"
            | "repz"
            | "repe"
            | "repne"
            | "repnz"
            | "lock"
            | "data16"
            | "addr32"
            | "cs"
            | "ds"
            | "es"
            | "fs"
            | "gs"
            | "ss"
            | "xacquire"
            | "xrelease"
            | "rex"
    ) || token.starts_with("rex.")
}

/// Parses an instruction line into `(mnemonic, operands)` after stripping prefixes.
fn parse_instruction(line: &str) -> Option<(&str, &str)> {
    let (address, body) = line.split_once(':')?;
    hex(address.trim())?;
    let mut rest = body.trim_start();
    loop {
        let (token, after) = split_token(rest)?;
        if is_prefix(token) && !after.is_empty() {
            rest = after;
        } else {
            return Some((token, after));
        }
    }
}

/// Strips x86-64 branch-prediction hint suffixes (`,pt` / `,pn`) that
/// `objdump` attaches to conditional jump mnemonics.
fn base_mnemonic(mnemonic: &str) -> &str {
    mnemonic
        .strip_suffix(",pt")
        .or_else(|| mnemonic.strip_suffix(",pn"))
        .unwrap_or(mnemonic)
}

/// Whether `mnemonic` enters the kernel, traps, halts, starts an RTM
/// transaction, fails to decode, or makes a far branch.
fn is_forbidden(mnemonic: &str) -> bool {
    matches!(
        base_mnemonic(mnemonic),
        "syscall"
            | "sysenter"
            | "sysret"
            | "sysretq"
            | "sysexit"
            | "int"
            | "int3"
            | "int1"
            | "into"
            | "icebp"
            | "iret"
            | "iretd"
            | "iretq"
            | "vmcall"
            | "vmmcall"
            | "svc"
            | "swi"
            | "hvc"
            | "smc"
            | "ecall"
            | "ud0"
            | "ud1"
            | "ud2"
            | "brk"
            | "hlt"
            | "xbegin"
            | "lcall"
            | "lcallw"
            | "lcallq"
            | "ljmp"
            | "ljmpw"
            | "ljmpq"
            | "(bad)"
            | ".byte"
    )
}

/// Whether `mnemonic` is a direct or indirect call, jump, or conditional branch.
///
/// Fails closed across all x86-64 branch families (including hinted jumps like
/// `je,pt` and 16-bit forms like `callw`/`jmpw`): no non-branch x86-64
/// mnemonic starts with `j`, `call`, or `loop`.
fn is_branch_or_call(mnemonic: &str) -> bool {
    let base = base_mnemonic(mnemonic);
    base.starts_with('j') || base.starts_with("call") || base.starts_with("loop")
}

/// Whether `mnemonic` is padding that does not terminate control flow.
fn is_nop(mnemonic: &str) -> bool {
    matches!(mnemonic, "nop" | "nopw" | "nopl" | "nopq")
}

/// Whether `mnemonic` prevents execution from falling through to the next function.
fn is_terminator(mnemonic: &str) -> bool {
    matches!(
        base_mnemonic(mnemonic),
        "ret" | "retw" | "retq" | "jmp" | "jmpw" | "jmpq"
    )
}

/// Parses a direct branch/call operand `ADDR <SYMBOL[+0xOFFSET][@plt]>`.
fn parse_direct_target(operands: &str) -> Option<(u64, &str)> {
    let (addr_str, rest) = split_token(operands)?;
    let addr = hex(addr_str)?;
    let inner = rest.trim().strip_prefix('<')?.strip_suffix('>')?;
    let without_offset = match inner.rsplit_once("+0x") {
        Some((base, offset)) if hex(offset).is_some() => base,
        _ => inner,
    };
    let bare = without_offset
        .strip_suffix("@plt")
        .unwrap_or(without_offset);
    if bare.is_empty() {
        return None;
    }
    Some((addr, bare))
}

/// Parses a RIP-relative indirect branch/call operand `*DISP(%rip) # SLOT ...`.
fn parse_indirect_slot(operands: &str) -> Option<u64> {
    let (operand, _) = split_token(operands)?;
    if !operand.starts_with('*') || !operand.contains("(%rip)") {
        return None;
    }
    let (_, comment) = operands.split_once('#')?;
    let (slot_str, _) = split_token(comment)?;
    hex(slot_str)
}

/// A pending node in the reachability graph.
enum Target {
    Address(u64),
    Name(String),
}

/// What the entry points reach that they may not, and how many functions of
/// unisono they reach.
fn check(
    disassembly: &Disassembly,
    table: &HashMap<u64, Relocation>,
    immutable: &[(u64, u64)],
    entries: &[String],
) -> (BTreeSet<String>, usize) {
    let mut problems = BTreeSet::new();
    let mut seen_addrs = BTreeSet::new();
    let mut seen_names = BTreeSet::new();
    let mut todo: Vec<Target> = entries.iter().cloned().map(Target::Name).collect();

    while let Some(target) = todo.pop() {
        let start = match target {
            Target::Address(addr) => addr,
            Target::Name(name) => {
                if !ours(&name) {
                    if !allowed(&name) {
                        problems.insert(format!("reaches {name}"));
                    }
                    continue;
                }
                if !seen_names.insert(name.clone()) {
                    continue;
                }
                match disassembly.by_name.get(&name).map(Vec::as_slice) {
                    None | Some([]) => {
                        problems.insert(format!("{name} is not in the library"));
                        continue;
                    }
                    Some([only]) => *only,
                    Some(_) => {
                        problems.insert(format!("{name} has duplicate definitions in the library"));
                        continue;
                    }
                }
            }
        };

        let Some(function) = disassembly.by_addr.get(&start) else {
            problems.insert(format!("address 0x{start:x} is not a function start"));
            continue;
        };
        let name = &function.name;
        if !ours(name) {
            if !allowed(name) {
                problems.insert(format!("reaches {name}"));
            }
            continue;
        }
        if !seen_addrs.insert(start) {
            continue;
        }

        audit_function(
            start,
            function,
            disassembly,
            table,
            immutable,
            &mut todo,
            &mut problems,
        );
    }

    (problems, seen_addrs.len())
}

/// Audits every instruction in one unisono function and queues its callees.
fn audit_function(
    start: u64,
    function: &Function,
    disassembly: &Disassembly,
    table: &HashMap<u64, Relocation>,
    immutable: &[(u64, u64)],
    todo: &mut Vec<Target>,
    problems: &mut BTreeSet<String>,
) {
    let name = &function.name;
    let mut last_real_mnemonic: Option<&str> = None;

    for line in &function.lines {
        let Some((mnemonic, operands)) = parse_instruction(line) else {
            continue;
        };
        if !is_nop(mnemonic) {
            last_real_mnemonic = Some(mnemonic);
        }
        if is_forbidden(mnemonic) {
            problems.insert(format!(
                "{name} executes forbidden instruction: {}",
                line.trim()
            ));
            continue;
        }
        if !is_branch_or_call(mnemonic) {
            continue;
        }
        if operands.starts_with('*') {
            audit_indirect(
                name,
                line,
                operands,
                disassembly,
                table,
                immutable,
                todo,
                problems,
            );
            continue;
        }
        let Some((target_addr, target_name)) = parse_direct_target(operands) else {
            problems.insert(format!(
                "{name} has unresolved direct branch: {}",
                line.trim()
            ));
            continue;
        };
        if let Some((dest_start, dest_name)) = disassembly.containing(target_addr) {
            if dest_name != target_name {
                problems.insert(format!(
                    "{name} direct branch target mismatch ({target_name} vs {dest_name}): {}",
                    line.trim()
                ));
            } else if dest_start != start {
                if !ours(dest_name) && target_addr != dest_start {
                    problems.insert(format!(
                        "{name} branches into middle of {dest_name}: {}",
                        line.trim()
                    ));
                } else {
                    todo.push(Target::Address(dest_start));
                }
            }
        } else if target_name == name {
            problems.insert(format!(
                "{name} branches outside library to 0x{target_addr:x}: {}",
                line.trim()
            ));
        } else {
            todo.push(Target::Name(target_name.to_string()));
        }
    }

    if let Some(last) = last_real_mnemonic
        && !is_terminator(last)
    {
        if let Some(next) = disassembly.next_after(start) {
            todo.push(Target::Address(next));
        } else {
            problems.insert(format!("{name} falls through past the end of the library"));
        }
    }
}

/// Resolves an immutable relocation-backed indirect branch/call or records a
/// failure.
#[allow(clippy::too_many_arguments)]
fn audit_indirect(
    name: &str,
    line: &str,
    operands: &str,
    disassembly: &Disassembly,
    table: &HashMap<u64, Relocation>,
    immutable: &[(u64, u64)],
    todo: &mut Vec<Target>,
    problems: &mut BTreeSet<String>,
) {
    let Some(slot) = parse_indirect_slot(operands) else {
        problems.insert(format!(
            "{name} branches through unresolved pointer: {}",
            line.trim()
        ));
        return;
    };
    if !slot_is_immutable(slot, immutable) {
        problems.insert(format!(
            "{name} branches through writable slot 0x{slot:x}: {}",
            line.trim()
        ));
        return;
    }
    let Some(reloc) = table.get(&slot) else {
        problems.insert(format!(
            "{name} branches through unmapped GOT slot 0x{slot:x}: {}",
            line.trim()
        ));
        return;
    };
    if !ALLOWED_RELOCATIONS.contains(&reloc.kind.as_str()) {
        problems.insert(format!(
            "{name} uses unsupported relocation {}: {}",
            reloc.kind,
            line.trim()
        ));
        return;
    }
    if let Some(address) = reloc.target.strip_prefix("*ABS*+") {
        if let Some((dest_start, _)) = hex(address).and_then(|addr| disassembly.containing(addr)) {
            todo.push(Target::Address(dest_start));
        } else {
            problems.insert(format!(
                "{name} branches to unresolved local address {}: {}",
                reloc.target,
                line.trim()
            ));
        }
    } else {
        let target = reloc
            .target
            .split('@')
            .next()
            .unwrap_or(&reloc.target)
            .to_string();
        todo.push(Target::Name(target));
    }
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let Some((library, entries)) = arguments.split_first() else {
        eprintln!("usage: reachable LIBRARY ENTRY...");
        return ExitCode::from(2);
    };
    if entries.is_empty() {
        eprintln!("usage: reachable LIBRARY ENTRY...");
        return ExitCode::from(2);
    }

    let read = objdump(&["-f"], library)
        .and_then(|headers| check_architecture(&headers))
        .and_then(|()| objdump(&["-p"], library))
        .and_then(|program_headers| {
            objdump(&["-d", "-C", "--no-show-raw-insn"], library)
                .map(|code| (program_headers, code))
        })
        .and_then(|(program_headers, code)| {
            objdump(&["-R", "-C"], library).map(|relocations| (program_headers, code, relocations))
        });
    let (program_headers, code, relocations) = match read {
        Ok(all) => all,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::from(2);
        }
    };

    let immutable = immutable_ranges(&program_headers);
    let (problems, reached) = check(
        &Disassembly::read(&code),
        &table(&relocations),
        &immutable,
        entries,
    );
    for problem in &problems {
        eprintln!("{problem}");
    }
    println!(
        "{} entry points reach {reached} functions of unisono",
        entries.len()
    );
    if problems.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Disassembly, check, check_architecture, immutable_ranges, ours, parse_direct_target,
        parse_indirect_slot, parse_instruction, table,
    };
    use std::collections::HashMap;

    const RELRO: &[(u64, u64)] = &[(0x5000, 0x5100)];

    #[test]
    fn ours_rejects_stdlib_generics_over_unisono_types() {
        assert!(ours("realtime_playback_cycle"));
        assert!(ours("unisono_core::timing::due"));
        assert!(ours("<unisono_core::device::Device<64>>::when"));
        assert!(ours(
            "<unisono_runtime::pump::ReceiverPlayback<64> as unisono_runtime::audio::Playback>::cycle"
        ));
        assert!(!ours(
            "core::ptr::drop_in_place<unisono_runtime::send::Sender>"
        ));
        assert!(!ours(
            "<alloc::raw_vec::RawVec<unisono_core::packet::Audio>>::grow_one"
        ));
        assert!(!ours("std::panicking::begin_panic<unisono_core::Error>"));
    }

    #[test]
    fn parses_prefixed_and_demangled_instructions() {
        assert_eq!(
            parse_instruction(
                "    8d95:\tbnd jmp 3d530 <<unisono_dsp::conceal::Concealment>::fill>"
            ),
            Some(("jmp", "3d530 <<unisono_dsp::conceal::Concealment>::fill>"))
        );
        assert_eq!(
            parse_direct_target("3d530 <<unisono_dsp::conceal::Concealment>::fill>"),
            Some((0x3d530, "<unisono_dsp::conceal::Concealment>::fill"))
        );
        assert_eq!(
            parse_direct_target("8da0 <realtime_cycle+0x20>"),
            Some((0x8da0, "realtime_cycle"))
        );
        assert_eq!(
            parse_direct_target("1040 <memcpy@plt>"),
            Some((0x1040, "memcpy"))
        );
        assert_eq!(
            parse_indirect_slot("*0x43e33(%rip)        # 4bfb0 <_DYNAMIC+0x258>"),
            Some(0x4bfb0)
        );
        assert_eq!(parse_indirect_slot("*%rax"), None);
        assert_eq!(parse_indirect_slot("*0x18(%rsi)"), None);
    }

    #[test]
    fn rejects_unsupported_architecture() {
        assert!(check_architecture("architecture: i386:x86-64, flags 0x150:\n").is_ok());
        assert!(check_architecture("architecture: aarch64, flags 0x150:\n").is_err());
        assert!(check_architecture("no architecture line\n").is_err());
    }

    #[test]
    fn catches_conditional_tail_jump_indirect_jump_traps_and_prefixes() {
        let code = "\
0000000000001000 <realtime_entry>:
    1000:\tbnd jne 2000 <core::panicking::panic>
    1006:\tnotrack jmp *%rax
    1009:\tint    $0x80
    100b:\tud2
    100d:\tret
0000000000002000 <core::panicking::panic>:
    2000:\tud2
";
        let disassembly = Disassembly::read(code);
        let (problems, _) = check(
            &disassembly,
            &HashMap::new(),
            RELRO,
            &["realtime_entry".into()],
        );
        assert!(
            problems
                .iter()
                .any(|p| p == "reaches core::panicking::panic")
        );
        assert!(problems.iter().any(|p| p.contains("unresolved pointer")));
        assert!(problems.iter().any(|p| p.contains("int    $0x80")));
        assert!(problems.iter().any(|p| p.contains("ud2")));
    }

    #[test]
    fn stops_recursion_at_allowed_intrinsics_with_ud2() {
        let code = "\
0000000000001000 <realtime_entry>:
    1000:\tcall   *0x10(%rip)        # 5000 <_DYNAMIC+0x10>
    1006:\tret
0000000000002000 <__divti3>:
    2000:\tud2
    2002:\tcall   3000 <compiler_builtins::int::u128_div_rem>
    2007:\tret
0000000000003000 <compiler_builtins::int::u128_div_rem>:
    3000:\tret
";
        let disassembly = Disassembly::read(code);
        let relocs = table("0000000000005000 R_X86_64_RELATIVE *ABS*+0x0000000000002000\n");
        let (problems, reached) = check(&disassembly, &relocs, RELRO, &["realtime_entry".into()]);
        assert_eq!(reached, 1);
        assert!(problems.is_empty(), "unexpected problems: {problems:?}");
    }

    #[test]
    fn rejects_irelative_unresolved_abs_and_linear_fallthrough() {
        let code = "\
0000000000001000 <realtime_entry>:
    1000:\tcall   *0x10(%rip)        # 5000 <resolver>
    1006:\tcall   *0x20(%rip)        # 5008 <bad_abs>
    100c:\tcall   9999
0000000000001012 <std::rt::bad_fallthrough>:
    1012:\tret
";
        let disassembly = Disassembly::read(code);
        let relocs = table(
            "\
0000000000005000 R_X86_64_IRELATIVE *ABS*+0x0000000000001012
0000000000005008 R_X86_64_RELATIVE  *ABS*+0x0000000000000001
",
        );
        let (problems, _) = check(&disassembly, &relocs, RELRO, &["realtime_entry".into()]);
        assert!(problems.iter().any(|p| p.contains("R_X86_64_IRELATIVE")));
        assert!(
            problems
                .iter()
                .any(|p| p.contains("unresolved local address"))
        );
        assert!(
            problems
                .iter()
                .any(|p| p.contains("unresolved direct branch"))
        );
        assert!(
            problems
                .iter()
                .any(|p| p == "reaches std::rt::bad_fallthrough")
        );
    }

    #[test]
    fn rejects_duplicate_reached_symbol() {
        let code = "\
0000000000001000 <realtime_entry>:
    1000:\tret
0000000000002000 <realtime_entry>:
    2000:\tret
";
        let disassembly = Disassembly::read(code);
        let (problems, _) = check(
            &disassembly,
            &HashMap::new(),
            RELRO,
            &["realtime_entry".into()],
        );
        assert!(problems.iter().any(|p| p.contains("duplicate definitions")));
    }

    #[test]
    fn rejects_writable_slot_hinted_branch_rarer_opcodes_mid_helper_and_label_mismatch() {
        let ph = "\
Program Header:
    LOAD off    0x0000000000002e38 vaddr 0x0000000000003e38 paddr 0x0000000000003e38 align 2**12
         filesz 0x00000000000001d8 memsz 0x00000000000001e0 flags rw-
   RELRO off    0x0000000000002e38 vaddr 0x0000000000003e38 paddr 0x0000000000003e38 align 2**0
         filesz 0x00000000000001c8 memsz 0x00000000000001c8 flags r--
";
        let immutable = immutable_ranges(ph);
        assert_eq!(immutable, vec![(0x3e38, 0x4000)]);

        let code = "\
0000000000001000 <realtime_entry>:
    1000:\tjmp    *0x2ef2(%rip)        # 4008 <hook>
    1006:\tje,pt  2000 <forbidden_fn>
    100c:\txbegin 2000 <forbidden_fn>
    1012:\tcallw  2000 <forbidden_fn>
    1018:\t(bad)
    101a:\tjmp    3008 <memcpy+0x8>
    1020:\tjmp    2000 <realtime_entry>
    1025:\tret
0000000000002000 <forbidden_fn>:
    2000:\tsyscall
    2002:\tret
0000000000003000 <memcpy>:
    3000:\tret
    3008:\tsyscall
";
        let disassembly = Disassembly::read(code);
        let relocs = table("0000000000004008 R_X86_64_RELATIVE *ABS*+0x0000000000001000\n");
        let (problems, _) = check(
            &disassembly,
            &relocs,
            &immutable,
            &["realtime_entry".into()],
        );
        assert!(
            problems.iter().any(|p| p.contains("writable slot 0x4008")),
            "{problems:?}"
        );
        assert!(
            problems.iter().any(|p| p == "reaches forbidden_fn"),
            "{problems:?}"
        );
        assert!(
            problems.iter().any(|p| p.contains("xbegin")),
            "{problems:?}"
        );
        assert!(problems.iter().any(|p| p.contains("(bad)")), "{problems:?}");
        assert!(
            problems.iter().any(|p| p.contains("middle of memcpy")),
            "{problems:?}"
        );
        assert!(
            problems.iter().any(|p| p.contains("target mismatch")),
            "{problems:?}"
        );
    }
}
