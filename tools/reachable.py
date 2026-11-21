#!/usr/bin/env python3
# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

"""Checks what the machine code of entry points of a shared object can reach.

Usage: reachable.py LIBRARY ENTRY...

Follows every call and jump from the entry points through the disassembly,
including calls through the table of addresses, and fails unless every
function reached is unisono's own, one of the functions that copy, fill and
compare memory, or one of the compiler's helpers for arithmetic on 128-bit
numbers; and unless none of them enters the kernel or calls through a
pointer that the table does not resolve. A path to a panic, to the
allocator, to a lock or to any library reaches a function that is none of
these, so the check fails on each of them.

The standard library's start-up code is in the library as well, since it
cannot be dropped, which is why the check follows calls from the entry
points rather than listing what the library contains.
"""

import re
import subprocess
import sys

ALLOWED = re.compile(
    r"^(memcpy|memmove|memset|memcmp|bcmp)(@plt)?$"
    r"|^__(u?(div|mod)ti3|muloti4|udivmodti4|ashlti3|ashrti3|lshrti3|multi3)$"
)


def ours(name):
    return "unisono" in name or name.startswith("realtime_")


def main(library, entries):
    disassembly = subprocess.run(
        ["objdump", "-d", "--no-show-raw-insn", library],
        capture_output=True, text=True, check=True,
    ).stdout.splitlines()
    relocations = subprocess.run(
        ["objdump", "-R", library], capture_output=True, text=True, check=True,
    ).stdout.splitlines()

    # The table of addresses: what each entry of it points to.
    table = {}
    for line in relocations:
        parts = line.split()
        if len(parts) >= 3 and re.fullmatch(r"[0-9a-f]+", parts[0]):
            table[int(parts[0], 16)] = parts[2]

    starts = {}
    functions = {}
    current = None
    for line in disassembly:
        header = re.match(r"^([0-9a-f]+) <(.*)>:$", line)
        if header:
            current = header.group(2)
            starts[int(header.group(1), 16)] = current
            functions[current] = []
        elif current is not None and line.strip():
            functions[current].append(line)
    ordered = sorted(starts)

    def containing(address):
        found = None
        for start in ordered:
            if start <= address:
                found = starts[start]
            else:
                break
        return found

    def resolve(target):
        relative = re.fullmatch(r"\*ABS\*\+0x([0-9a-f]+)", target)
        if relative:
            return containing(int(relative.group(1), 16))
        return target.split("@")[0]

    problems = []
    seen = set()
    todo = list(entries)
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        if not ours(name):
            if not ALLOWED.match(name):
                problems.append(f"reaches {name}")
            continue
        for line in functions.get(name, []):
            if re.search(r"\b(syscall|sysenter|svc)\b", line):
                problems.append(f"{name} enters the kernel")
            direct = re.search(r"\b(call|jmp)\s+[0-9a-f]+ <([^>+]+)(\+0x[0-9a-f]+)?>", line)
            if direct and direct.group(2) != name:
                todo.append(direct.group(2))
                continue
            indirect = re.search(r"\b(call|jmp)\s+\*", line)
            if not indirect:
                continue
            slot = re.search(r"#\s*([0-9a-f]+)", line)
            if indirect.group(1) == "jmp" and not slot:
                # A jump through a table of the function's own branches.
                continue
            target = table.get(int(slot.group(1), 16)) if slot else None
            if target is None:
                problems.append(f"{name} calls through a pointer: {line.strip()}")
            else:
                resolved = resolve(target)
                if resolved:
                    todo.append(resolved)
    for problem in sorted(set(problems)):
        print(problem, file=sys.stderr)
    ours_reached = sorted(name for name in seen if ours(name))
    print(f"{len(entries)} entry points reach {len(ours_reached)} functions of unisono")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2:]))
