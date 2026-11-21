// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Checks what the machine code of entry points of a shared library can
//! reach.
//!
//! Usage: `reachable LIBRARY ENTRY...`
//!
//! Follows every call and jump from the entry points through the
//! disassembly that `objdump` gives, including calls through the table of
//! addresses, and fails unless every function reached is unisono's own, one
//! of the functions that copy, fill and compare memory, or one of the
//! compiler's helpers for arithmetic on 128-bit numbers; and unless none of
//! them enters the kernel or calls through a pointer that the table does not
//! resolve. A path to a panic, to the allocator, to a lock or to any library
//! reaches a function that is none of these, so the check fails on each.
//!
//! The standard library's start-up code is in such a library as well, since
//! it cannot be dropped, which is why the check follows calls from the entry
//! points rather than listing what the library holds.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::process::{Command, ExitCode};

/// Functions outside unisono that the code may reach.
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

/// Whether `name` is a function of unisono.
fn ours(name: &str) -> bool {
    name.contains("unisono") || name.starts_with("realtime_")
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

/// A hexadecimal number.
fn hex(text: &str) -> Option<u64> {
    u64::from_str_radix(text.trim_start_matches("0x"), 16).ok()
}

/// The functions of a disassembly: for each, its lines.
struct Disassembly {
    functions: HashMap<String, Vec<String>>,
    /// The functions by the address they start at.
    starts: BTreeMap<u64, String>,
}

impl Disassembly {
    fn read(text: &str) -> Disassembly {
        let mut functions: HashMap<String, Vec<String>> = HashMap::new();
        let mut starts = BTreeMap::new();
        let mut current: Option<String> = None;
        for line in text.lines() {
            // "0000000000001234 <name>:"
            if let Some((address, rest)) = line.split_once(" <")
                && let Some(name) = rest.strip_suffix(">:")
                && let Some(start) = hex(address)
            {
                starts.insert(start, name.to_string());
                functions.insert(name.to_string(), Vec::new());
                current = Some(name.to_string());
            } else if let Some(name) = &current
                && !line.trim().is_empty()
                && let Some(lines) = functions.get_mut(name)
            {
                lines.push(line.to_string());
            }
        }
        Disassembly { functions, starts }
    }

    /// The function that holds `address`.
    fn containing(&self, address: u64) -> Option<&String> {
        self.starts
            .range(..=address)
            .next_back()
            .map(|(_, name)| name)
    }
}

/// The table of addresses: what each of its entries points to, as `objdump
/// -R` names it.
fn table(text: &str) -> HashMap<u64, String> {
    let mut table = HashMap::new();
    for line in text.lines() {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if let [offset, _, target, ..] = parts.as_slice()
            && let Some(offset) = hex(offset)
        {
            table.insert(offset, (*target).to_string());
        }
    }
    table
}

/// The function that a direct call or jump in `line` goes to: the name in
/// `<name>` or `<name+0x10>` after the instruction.
fn direct(line: &str) -> Option<&str> {
    let instruction = line.split_once(':')?.1.trim_start();
    if !(instruction.starts_with("call") || instruction.starts_with("jmp")) {
        return None;
    }
    // A call through a pointer names its table entry in a comment, after
    // `#`; it is not a direct call.
    if instruction.split_whitespace().nth(1)?.starts_with('*') {
        return None;
    }
    let (_, rest) = instruction.split_once('<')?;
    let name = rest.split_once('>')?.0;
    Some(name.split_once('+').map_or(name, |(name, _)| name))
}

/// For a call or jump through a pointer in `line`: the entry of the table
/// it reads, if the instruction names one, or `None` when it names none.
fn indirect(line: &str) -> Option<(bool, Option<u64>)> {
    let instruction = line.split_once(':')?.1.trim_start();
    let call = instruction.starts_with("call");
    if !(call || instruction.starts_with("jmp")) {
        return None;
    }
    let operand = instruction.split_whitespace().nth(1)?;
    if !operand.starts_with('*') {
        return None;
    }
    let slot = instruction
        .split_once('#')
        .and_then(|(_, comment)| comment.split_whitespace().next())
        .and_then(hex);
    Some((call, slot))
}

/// Whether `line` enters the kernel.
fn enters_kernel(line: &str) -> bool {
    let Some((_, instruction)) = line.split_once(':') else {
        return false;
    };
    matches!(
        instruction.split_whitespace().next(),
        Some("syscall" | "sysenter" | "svc")
    )
}

/// What the entry points reach that they may not, and how many functions of
/// unisono they reach.
fn check(
    disassembly: &Disassembly,
    table: &HashMap<u64, String>,
    entries: &[String],
) -> (BTreeSet<String>, usize) {
    let mut problems = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut todo: Vec<String> = entries.to_vec();
    while let Some(name) = todo.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if !ours(&name) {
            if !allowed(&name) {
                problems.insert(format!("reaches {name}"));
            }
            continue;
        }
        let Some(lines) = disassembly.functions.get(&name) else {
            problems.insert(format!("{name} is not in the library"));
            continue;
        };
        for line in lines {
            if enters_kernel(line) {
                problems.insert(format!("{name} enters the kernel"));
            }
            if let Some(target) = direct(line) {
                if target != name {
                    todo.push(target.to_string());
                }
                continue;
            }
            let Some((call, slot)) = indirect(line) else {
                continue;
            };
            match slot.and_then(|slot| table.get(&slot)) {
                Some(target) => {
                    // "*ABS*+0x3eec0": a function of the library itself.
                    let resolved = match target.strip_prefix("*ABS*+") {
                        Some(address) => hex(address)
                            .and_then(|address| disassembly.containing(address))
                            .cloned(),
                        None => Some(target.split('@').next().unwrap_or(target).to_string()),
                    };
                    if let Some(resolved) = resolved {
                        todo.push(resolved);
                    }
                }
                // A jump through a table of the function's own branches.
                None if !call && slot.is_none() => {}
                None => {
                    problems.insert(format!("{name} calls through a pointer: {}", line.trim()));
                }
            }
        }
    }
    let reached = seen.iter().filter(|name| ours(name)).count();
    (problems, reached)
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let Some((library, entries)) = arguments.split_first() else {
        eprintln!("usage: reachable LIBRARY ENTRY...");
        return ExitCode::from(2);
    };
    let read = objdump(&["-d", "--no-show-raw-insn"], library)
        .and_then(|code| objdump(&["-R"], library).map(|relocations| (code, relocations)));
    let (code, relocations) = match read {
        Ok(both) => both,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::from(2);
        }
    };
    let (problems, reached) = check(&Disassembly::read(&code), &table(&relocations), entries);
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
    use super::{Disassembly, check, direct, indirect, table};
    use std::collections::HashMap;

    #[test]
    fn calls_are_read_from_lines_of_objdump() {
        assert_eq!(
            direct("    8d95:\tcall   3d530 <_RNvunisono_dsp7conceal4fill>"),
            Some("_RNvunisono_dsp7conceal4fill")
        );
        assert_eq!(
            direct("    8d95:\tjmp    8da0 <realtime_cycle+0x20>"),
            Some("realtime_cycle")
        );
        assert_eq!(
            indirect("    8177:\tcall   *0x43e33(%rip)        # 4bfb0 <_DYNAMIC+0x258>"),
            Some((true, Some(0x4bfb0)))
        );
        assert_eq!(indirect("    9000:\tjmp    *%rax"), Some((false, None)));
        assert_eq!(indirect("    9000:\tmov    %rax,%rbx"), None);
    }

    #[test]
    fn a_path_to_a_function_outside_unisono_is_found() {
        let code = "\
0000000000001000 <realtime_entry>:
    1000:\tcall   2000 <_RNvunisono_core4step>
    1005:\tcall   *0x10(%rip)        # 5000 <memset>
    100b:\tret
0000000000002000 <_RNvunisono_core4step>:
    2000:\tjmp    3000 <_RNvcore9panicking5panic>
0000000000003000 <_RNvcore9panicking5panic>:
    3000:\tud2
";
        let disassembly = Disassembly::read(code);
        let table = table("0000000000005000 R_X86_64_GLOB_DAT  memset\n");
        let (problems, reached) = check(&disassembly, &table, &["realtime_entry".into()]);
        assert_eq!(reached, 2);
        assert_eq!(
            problems.into_iter().collect::<Vec<_>>(),
            ["reaches _RNvcore9panicking5panic"]
        );
        let empty: HashMap<u64, String> = HashMap::new();
        let (problems, _) = check(&disassembly, &empty, &["realtime_entry".into()]);
        assert!(
            problems
                .iter()
                .any(|problem| problem.contains("calls through a pointer"))
        );
    }
}
