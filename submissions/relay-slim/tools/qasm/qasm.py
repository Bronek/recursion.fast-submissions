#!/usr/bin/env python3
"""Regenerate the node program's placement records and program blobs from the entry's Lean.

    qasm.py --org ORG --build BUILD [--out OUT] [--sets P8,P20] [--header FILE] [--check]

ORG is a built checkout of the core repository (the organiser's harness, `harness/org-setup.sh`,
builds it and its package tree). BUILD is a scratch directory outside the entry's root: the tool's
Lake tree goes there, and OUT (default BUILD/out) receives the four generated files. With --check,
each generated file is compared byte for byte with the one the entry ships. The exit status is 0
only if every set reached its fixed point with the frozen numbers (schedule, pubTab) and, with --check, every
file is identical; otherwise it is 1, after a FAILED line per reason. README.md has the details.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))  # the entry's root: tools/qasm/../..
SETS = {"P8": ("LvmQAsmData8.lean", "q-p8.blob"), "P20": ("LvmQAsmData20.lean", "q-p20.blob")}


def shipped(name):
    """Where the entry ships a generated file."""
    if name.endswith(".lean"):
        return os.path.join(ROOT, "lean", name)
    return os.path.join(ROOT, "prover", "src", "lvm", name)


def packages_dir(org):
    m = json.load(open(os.path.join(org, "lake-manifest.json")))
    return os.path.realpath(os.path.join(org, m.get("packagesDir") or ".lake/packages"))


def link(target, path):
    if os.path.islink(path):
        if os.readlink(path) == target:
            return
        os.unlink(path)
    os.symlink(target, path)


def tree(org, build):
    """The Lake tree: the entry's `lean/` and this directory linked in, ORG required by path, ORG's
    manifest reused (no `lake update`), as the harness's own entry tree does."""
    os.makedirs(build, exist_ok=True)
    shutil.copy(os.path.join(org, "lean-toolchain"), build)
    link(os.path.join(ROOT, "lean"), os.path.join(build, "entry"))
    link(HERE, os.path.join(build, "tool"))
    mods = sorted(f[:-5] for f in os.listdir(os.path.join(ROOT, "lean")) if f.endswith(".lean"))
    pk = packages_dir(org)
    q = lambda xs: "[" + ", ".join(json.dumps(x) for x in xs) + "]"  # noqa: E731
    with open(os.path.join(build, "lakefile.toml"), "w") as f:
        f.write(f'name = "qasmtree"\npackagesDir = {json.dumps(pk)}\n[[require]]\nname = "RecursionFast"\n'
                f'path = {json.dumps(org)}\n[[lean_lib]]\nname = "Entry"\nsrcDir = "entry"\nroots = {q(mods)}\n'
                '[[lean_lib]]\nname = "QAsmTool"\nsrcDir = "tool"\nroots = ["QAsmTool"]\n'
                '[[lean_exe]]\nname = "qasm"\nsrcDir = "tool"\nroot = "QAsmMain"\n')
    m = json.load(open(os.path.join(org, "lake-manifest.json")))
    for p in m["packages"]:
        p["inherited"] = True
    m["packages"].insert(0, {"type": "path", "scope": "", "name": "RecursionFast", "manifestFile": "lake-manifest.json",
                             "inherited": False, "dir": org, "configFile": "lakefile.toml"})
    m["name"], m["packagesDir"] = "qasmtree", pk
    json.dump(m, open(os.path.join(build, "lake-manifest.json"), "w"), indent=1)


def first_diff(a, b):
    """The first differing byte offset of two byte strings, or None."""
    for i, (x, y) in enumerate(zip(a, b)):
        if x != y:
            return i
    return None if len(a) == len(b) else min(len(a), len(b))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--org", required=True, help="a built checkout of the core repository")
    ap.add_argument("--build", required=True, help="a scratch directory for the Lake tree")
    ap.add_argument("--out", help="where the generated files go (default BUILD/out)")
    ap.add_argument("--sets", default="P8,P20", help="parameter sets, comma-separated (default P8,P20)")
    ap.add_argument("--header", default=os.path.join(HERE, "header.txt"), help="the record modules' header")
    ap.add_argument("--start", default="shipped", choices=["shipped", "empty"], help="the iteration's first record")
    ap.add_argument("--max-iter", default="8", help="the iteration's bound (default 8)")
    ap.add_argument("--check", action="store_true", help="compare the generated files with the shipped ones")
    a = ap.parse_args()
    sys.stdout.reconfigure(line_buffering=True)
    org, build = os.path.realpath(a.org), os.path.realpath(a.build)
    out = os.path.realpath(a.out or os.path.join(build, "out"))
    for d in (build, out):
        if os.path.commonpath([d, os.path.realpath(ROOT)]) == os.path.realpath(ROOT):
            sys.exit(f"{d} is inside the entry's root; build products must stay outside it")
    sets = a.sets.split(",")
    for s in sets:
        if s not in SETS:
            sys.exit(f"unknown set {s} (known: {', '.join(SETS)})")
    tree(org, build)
    if subprocess.run(["lake", "build", "qasm"], cwd=build).returncode != 0:
        sys.exit("lake build qasm failed")
    exe = os.path.join(build, ".lake", "build", "bin", "qasm")
    failed = []
    for s in sets:
        cmd = [exe, s, out, os.path.realpath(a.header), "--start", a.start, "--max-iter", a.max_iter]
        rc = subprocess.run(cmd).returncode
        if rc not in (0, 3, 5, 7):
            failed.append(f"{s}: qasm exited {rc}")
            continue
        if rc in (3, 7):
            failed.append(f"{s}: the frozen numbers (schedule, pubTab) differ")
        if rc in (5, 7):
            failed.append(f"{s}: the tables' columns pass a commitment's occupied lanes, or lie in C_rec")
        if a.check:
            for name in SETS[s]:
                got, want = open(os.path.join(out, name), "rb").read(), open(shipped(name), "rb").read()
                i = first_diff(got, want)
                if i is None:
                    print(f"{s}: {name} identical to {os.path.relpath(shipped(name), ROOT)}")
                else:
                    print(f"{s}: {name} differs from {os.path.relpath(shipped(name), ROOT)} from byte {i}: "
                          f"{got[i:i + 40]!r} instead of {want[i:i + 40]!r}")
                    failed.append(f"{s}: {name} differs")
    for f in failed:
        print(f"FAILED {f}")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
