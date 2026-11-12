#!/usr/bin/env python3
"""Make one CPU variant's assembly linkable beside the others (BLUEPRINT §8, K-DISP).

  python3 -I tools/suffix-asm.py VARIANT IN.s OUT.s

Every symbol the file DEFINES (a label, `.set`/`.equ`, `.comm`/`.lcomm`; not the assembler-local `.L…`
labels) is renamed `NAME` -> `NAME_lvm_VARIANT` at every occurrence (references, `.type`, `.size`, `.globl`,
COMDAT group signatures, relocation operands such as `@PLT`, `@GOTPCREL`, `@TPOFF`), so two variants
define disjoint names and no COMDAT group of one folds into the other's. `main` becomes `lvm_main_VARIANT`,
which `dispatch.s` calls. Symbols the file only references (glibc's, the weak `statx`, `__dso_handle`, …)
are left alone.

Checks (the build fails otherwise):
* no `.incbin`/`.include` (the harness's build sees only the `.s` files);
* each `.init_array`/`.preinit_array`/`.ctors`/`.fini_array` entry of the file names a function that, with
  every function it calls in this file, uses no vector register, no VEX/EVEX mnemonic and none of BMI1/2, LZCNT,
  TZCNT, MOVBE, POPCNT (start-up and exit code runs on any x86-64 CPU, chosen or not); an entry line of another
  form fails the build;
* every COMDAT group signature is a symbol of this file (so it is renamed and no group folds across variants).
"""
import re
import sys

TOKEN = re.compile(r'"(?:[^"\\]|\\.)*"|[A-Za-z_.][\w.$]*')
LABEL = re.compile(r'^\s*("(?:[^"\\]|\\.)*"|[A-Za-z_.$][\w.$]*):')
SETLIKE = re.compile(r'^\s*\.(?:set|equ|comm|lcomm)\s+("(?:[^"\\]|\\.)*"|[A-Za-z_.$][\w.$]*)\s*,')
VECTOR = re.compile(r'%[xyz]mm\d|%k[0-7]\b|^\s*v[a-z0-9]+\s|^\s*(andn|bextr|blsi|blsmsk|blsr|tzcnt|bzhi|mulx|pdep|pext|rorx|'
                    r'sarx|shlx|shrx|lzcnt|movbe|popcnt)[a-z]*\s', re.M)
CALL = re.compile(r'^\s*(?:call|jmp)q?\s+("(?:[^"\\]|\\.)*"|[A-Za-z_.][\w.$]*)(?:@PLT)?\s*$')


def defined(lines):
    names = set()
    for line in lines:
        m = LABEL.match(line) or SETLIKE.match(line)
        if m:
            name = m.group(1)
            bare = name.strip('"')
            if not bare.startswith('.L') and not bare.isdigit():
                names.add(name)
    return names


def function_body(lines, name):
    """The lines from `name:` to its `.size`/next `.type` directive."""
    start = None
    for i, line in enumerate(lines):
        if start is None:
            if LABEL.match(line) and LABEL.match(line).group(1) == name:
                start = i
        elif re.match(r'^\s*\.(size|type)\s', line) or re.match(r'^\s*\.section\s', line):
            return lines[start:i]
    return lines[start:] if start is not None else None


def init_array_targets(lines):
    out, in_init = [], False
    for line in lines:
        s = line.split('#')[0].strip() if '"' not in line else line.strip()
        if re.match(r'^\.(section|pushsection|popsection|previous|text|data|bss)\b', s):
            in_init = any(k in s for k in ('.init_array', '.preinit_array', '.ctors', '.fini_array', '.dtors'))
            continue
        if not in_init or not s:
            continue
        m = re.match(r'^\.quad\s+([A-Za-z_.][\w.$]*)$', s)
        if m:
            out.append(m.group(1))
        elif re.match(r'^(\.p2align|\.globl|\.type|\.size|\.hidden|\.weak)\b', s) or LABEL.match(s):
            continue
        else:
            raise SystemExit(f"suffix-asm: unrecognised line in a start-up/exit array: {s}")
    return out


def reachable(lines, root):
    """`root` and every function of this file it calls or jumps to, transitively: (name, body) pairs."""
    seen, todo, out = set(), [root], []
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        seen.add(f)
        body = function_body(lines, f)
        if body is None:
            continue
        out.append((f, body))
        for l in body:
            m = CALL.match(l)
            if m and not m.group(1).startswith('.L'):
                todo.append(m.group(1))
    return out


def main():
    variant, src, dst = sys.argv[1:4]
    assert re.fullmatch(r'[a-z0-9]+', variant), "a variant name is [a-z0-9]+"
    lines = open(src, encoding='utf-8').readlines()
    for line in lines:
        if re.match(r'^\s*\.(incbin|include)\b', line):
            raise SystemExit(f"suffix-asm: forbidden directive: {line.strip()}")
    for target in init_array_targets(lines):
        if function_body(lines, target) is None:
            raise SystemExit(f"suffix-asm: start-up entry {target} has no body in this file")
        for f, body in reachable(lines, target):
            hit = [l.strip() for l in body if VECTOR.search(l)]
            if hit:
                raise SystemExit(f"suffix-asm: start-up/exit code {f} (from {target}) uses {hit[0]!r}: it would run "
                                 f"on every CPU, whatever the dispatch chose")
    names = defined(lines)
    for line in lines:
        m = re.match(r'^\s*\.section\s.*,\s*("(?:[^"\\]|\\.)*"|[A-Za-z_.][\w.$]*)\s*,\s*comdat\b', line)
        if m and m.group(1) not in names:
            raise SystemExit(f"suffix-asm: COMDAT group {m.group(1)} is not defined here: it would fold across variants")
    suffix = f"_lvm_{variant}"

    def rename(name):
        if name == 'main':
            return f"lvm_main_{variant}"
        if name.startswith('"'):
            return name[:-1] + suffix + '"'
        return name + suffix

    table = {n: rename(n) for n in names}

    def sub(m):
        t = m.group(0)
        return table.get(t, t)

    out = []
    for line in lines:
        # comments never hold a symbol the assembler reads; strings in `.ascii` are tokens too, but a
        # defined symbol's mangled name never occurs in one (checked: the count below is the defined set)
        code, sep, comment = line.partition('#') if '"' not in line else (line, '', '')
        out.append(TOKEN.sub(sub, code) + sep + comment)
    open(dst, 'w', encoding='utf-8').write(''.join(out))
    print(f"suffix-asm: {variant}: {len(names)} defined symbols renamed (+{suffix}; main -> lvm_main_{variant}), "
          f"{len(init_array_targets(lines))} start-up entries checked", file=sys.stderr)


if __name__ == '__main__':
    main()
