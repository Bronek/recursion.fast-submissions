#!/usr/bin/env python3
"""Vendor leanVM's prover crates into this crate as modules (WP-4, BLUEPRINT §8).

  python3 -I tools/vendor.py LEANVM_ROOT OUT_DIR

Copies `crates/<c>/src/**.rs` of the crates below into `OUT_DIR/<c>/` (`lib.rs` becomes `mod.rs`)
and rewrites paths only, so a diff against leanVM shows nothing but these rewrites:

* `crate::` inside crate `c`            -> `crate::lv::c::`
* `<other>::` for a vendored crate      -> `crate::lv::<other>::`
* `tracing::`                           -> `crate::lv::tracing::` (a no-op shim, `lv/tracing.rs`)

Files that only serve leanVM's own tests or benches are not copied (`SKIP`). Every edit made to
the vendored code after this step is a WP-4 change and is listed in `lv/PATCHES.md`.
Run once; the result is committed (the build never runs this script).
"""
import os
import re
import sys

CRATES = ["primitives", "parallel", "fiat_shamir", "pcs", "keccak_gkr"]
SKIP = {
    ("primitives", "test_rng.rs"),          # rand (tests only)
    ("keccak_gkr", "batch_bench.rs"),       # bench crate + verifier (feature "bench")
    ("keccak_gkr", "tests.rs"),             # tests
    ("pcs", "ntt/tests.rs"),                # tests
}
NAMES = CRATES + ["tracing"]


def rewrite(text, crate):
    # one pass, so a rewritten path is never rewritten again
    pat = re.compile(r'(?<![\w:$])(crate|' + '|'.join(NAMES) + r')::')

    def sub(m):
        name = m.group(1)
        if name == "crate":
            return f"crate::lv::{crate}::"
        return f"crate::lv::{name}::"
    return pat.sub(sub, text)


def main():
    root, out = sys.argv[1], sys.argv[2]
    for crate in CRATES:
        src = os.path.join(root, "crates", crate, "src")
        for dirpath, _, files in os.walk(src):
            for f in sorted(files):
                if not f.endswith(".rs"):
                    continue
                rel = os.path.relpath(os.path.join(dirpath, f), src)
                if (crate, rel) in SKIP:
                    continue
                dst_rel = "mod.rs" if rel == "lib.rs" else rel
                dst = os.path.join(out, crate, dst_rel)
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                text = open(os.path.join(dirpath, f), encoding="utf-8").read()
                head = f"// Vendored from leanVM 0b850750 `crates/{crate}/src/{rel}` (tools/vendor.py; edits: lv/PATCHES.md).\n"
                open(dst, "w", encoding="utf-8").write(head + rewrite(text, crate))


if __name__ == "__main__":
    main()
