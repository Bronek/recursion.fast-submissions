#!/usr/bin/env python3
"""Make compiler-emitted x86-64 assembly acceptable to the reference toolchain's GNU `as`
(UNTRUSTED helper for submitters; the harness never runs it).

  python3 harness/tools/asm-compat.py IN.s OUT.s

The rule (`harness/PROVER.md` §1) is that `prover/*.s` assembles with the `as` of the runner image
(`ubuntu-24.04`, GNU Binutils 2.42). Compilers newer than that image emit directives its `as`
rejects; this filter rewrites or drops them and changes nothing else:

* `.base64 "…"` (GCC ≥ 15 for string and table constants; binutils ≥ 2.43): rewritten as the same
  bytes in `.byte` lines;
* `.prefalign A, …` (LLVM 23): rewritten as `.p2align A`;
* DWARF line directives (`.file N …`, `.loc …`, `.loc_mark_labels`) and every line inside a
  `.debug_*` section are dropped: LLVM 23 emits DWARF-5 `.file N "dir" "file"` forms older `as`
  rejects, and they carry absolute host paths;
* a `.incbin` or `.include` directive is an error (the harness's build sees only the `.s` files).

The LLVM rules come from a submitted entry's assembly sanitizer, merged here with the GCC rule.
"""
import base64
import re
import sys

SECTION_SWITCH = re.compile(r'^\s*\.(section|text|data|bss|pushsection|popsection|previous)\b')
BASE64 = re.compile(r'^(\s*)\.base64\s+"([A-Za-z0-9+/=]*)"\s*$')


def section_name(line):
    m = re.match(r'^\s*\.(section|pushsection)\s+("?)([^",\s]+)', line)
    if m:
        return m.group(3)
    m = re.match(r'^\s*\.(text|data|bss)\b', line)
    return "." + m.group(1) if m else None


def convert(lines):
    out, stack, cur, prev, stats = [], [], ".text", ".text", {"base64": 0, "prefalign": 0, "dropped": 0}
    for line in lines:
        m = SECTION_SWITCH.match(line)
        if m:
            kind = m.group(1)
            if kind == "pushsection":
                stack.append(cur)
                prev, cur = cur, section_name(line)
            elif kind == "popsection":
                prev, cur = cur, stack.pop() if stack else ".text"
            elif kind == "previous":
                prev, cur = cur, prev
            else:
                prev, cur = cur, section_name(line)
            if cur and cur.startswith(".debug_"):
                stats["dropped"] += 1
                continue
            out.append(line)
            continue
        if cur and cur.startswith(".debug_"):
            stats["dropped"] += 1
            continue
        s = line.lstrip()
        if re.match(r'\.file\s+\d', s) or re.match(r'\.loc\b', s) or s.startswith(".loc_mark_labels"):
            stats["dropped"] += 1
            continue
        if re.match(r'\.(incbin|include)\b', s):
            raise SystemExit(f"asm-compat: forbidden directive: {s.strip()}")
        m = BASE64.match(line)
        if m:
            data = base64.b64decode(m.group(2), validate=True)
            for k in range(0, len(data), 16):
                out.append(f"{m.group(1)}.byte\t" + ",".join(str(b) for b in data[k:k + 16]) + "\n")
            stats["base64"] += 1
            continue
        m = re.match(r'(\s*)\.prefalign\s+(\d+)\s*,.*$', line)
        if m:
            line = f"{m.group(1)}.p2align\t{m.group(2)}\n"
            stats["prefalign"] += 1
        out.append(line)
    return out, stats


def main():
    if len(sys.argv) != 3:
        raise SystemExit("usage: asm-compat.py IN.s OUT.s")
    out, st = convert(open(sys.argv[1], encoding="utf-8").readlines())
    open(sys.argv[2], "w", encoding="utf-8").write("".join(out))
    print(f"asm-compat: {st['base64']} .base64 rewritten, {st['prefalign']} .prefalign rewritten, "
          f"{st['dropped']} debug lines dropped", file=sys.stderr)


if __name__ == "__main__":
    main()
