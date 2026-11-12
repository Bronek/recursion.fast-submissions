#!/usr/bin/env bash
# build-asm.sh [--dev] [--install] [WORK_DIR]
#
# Emit the prover crate in this directory as GNU-as files, one per CPU variant, and link them exactly as the
# runner does (PROVER.md §1): `gcc -static -O2 -pthread /build/*.s -o /build/prover -lm`, here in
# WORK_DIR/build (default ${TMPDIR:-/tmp}/lvm-asm). BLUEPRINT §8 (K-DISP: two variants behind a cpuid stub):
#
#   prover-v2.s   -C target-cpu=x86-64-v2                                         the portable fallback
#   prover-v4.s   -C target-cpu=x86-64-v4 +pclmulqdq,+vpclmulqdq,+gfni,+avx512vbmi  the evaluation machine
#   prover-v4p.s  -C target-cpu=x86-64-v4 +pclmulqdq          (AVX-512 machines without GFNI/VPCLMUL; the
#                 fallback when v4 fails `prover setup`'s self-test, WP-15a)
#   dispatch.s    the hand-written `main`: cpuid/XCR0, then `lvm_main_<v>`
#
# Per variant: one fat-LTO LLVM module (core/alloc/std and the crate; `--emit asm` prints the whole program,
# rustc runs LTO only when it also links, which cargo asks for), `-C llvm-args=-align-all-functions=4`, paths
# remapped; then tools/asm-compat.py (the organiser's rules for GNU as 2.42: DWARF `.file`/`.loc` and `.debug_*`
# dropped, `.prefalign` -> `.p2align`, `.base64` -> `.byte`, no `.incbin`/`.include`), then tools/suffix-asm.py
# (every defined symbol suffixed `_lvm_<v>`, `main` -> `lvm_main_<v>`, start-up code checked). Cargo's target
# directories are WORK_DIR/target-<v> (outside the entry); the build is offline (no dependencies).
# --install copies the production `.s` files beside this script (the submitted form).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
dev=0; install=0; work=""
for a in "$@"; do
  case "$a" in
    --dev) dev=1 ;;
    --install) install=1 ;;
    *) work=$a ;;
  esac
done
work=${work:-${TMPDIR:-/tmp}/lvm-asm}
mkdir -p "$work"
work=$(cd "$work" && pwd)

variants="v2 v4p v4"   # --dev is accepted and changes nothing (WP-15a: v4p ships)
flags_v2="-C target-cpu=x86-64-v2"
flags_v4="-C target-cpu=x86-64-v4 -C target-feature=+pclmulqdq,+vpclmulqdq,+gfni,+avx512vbmi"
flags_v4p="-C target-cpu=x86-64-v4 -C target-feature=+pclmulqdq"

emit() {
  local v=$1 flags_var="flags_$1" raw="$work/raw-$1.s"
  rm -f "$raw"
  # run from this directory so that rustup takes the toolchain of `rust-toolchain.toml`
  (cd "$here" && CARGO_TARGET_DIR="$work/target-$v" LVM_VARIANT="$v" cargo rustc --manifest-path "$here/Cargo.toml" \
    --release --offline --locked --bin lvm-prover \
    --config 'profile.release.lto="fat"' --config 'profile.release.codegen-units=1' \
    --config 'profile.release.panic="abort"' --config 'profile.release.debug=false' \
    --config 'profile.release.incremental=false' \
    -- --emit "asm=$raw" ${!flags_var} -C llvm-args=-align-all-functions=4 \
    --remap-path-prefix "$here=leanvm-inspired/prover" --remap-path-prefix "$HOME=~")
  if [ ! -s "$raw" ]; then
    # cargo skips rustc when the crate is fresh: rebuild from a clean target directory, once
    (cd "$here" && CARGO_TARGET_DIR="$work/target-$v" cargo clean --release --manifest-path "$here/Cargo.toml")
    (cd "$here" && CARGO_TARGET_DIR="$work/target-$v" LVM_VARIANT="$v" cargo rustc --manifest-path "$here/Cargo.toml" \
      --release --offline --locked --bin lvm-prover \
      --config 'profile.release.lto="fat"' --config 'profile.release.codegen-units=1' \
      --config 'profile.release.panic="abort"' --config 'profile.release.debug=false' \
      --config 'profile.release.incremental=false' \
      -- --emit "asm=$raw" ${!flags_var} -C llvm-args=-align-all-functions=4 \
      --remap-path-prefix "$here=leanvm-inspired/prover" --remap-path-prefix "$HOME=~")
    [ -s "$raw" ] || { echo "build-asm: rustc wrote no assembly for $v" >&2; exit 1; }
  fi
  python3 -I "$here/tools/asm-compat.py" "$raw" "$work/compat-$v.s"
  python3 -I "$here/tools/suffix-asm.py" "$v" "$work/compat-$v.s" "$work/prover-$v.s"
  rm -f "$work/compat-$v.s"
}

for v in $variants; do emit "$v"; done

mkdir -p "$work/build"
rm -f "$work"/build/*.s "$work/build/prover"
cp "$here/dispatch.s" "$work/build/dispatch.s"
for v in $variants; do cp "$work/prover-$v.s" "$work/build/prover-$v.s"; done
# the runner's link step, verbatim but for the directory (outside its sandbox)
(cd "$work/build" && /usr/bin/gcc -static -O2 -pthread "$work"/build/*.s -o "$work/build/prover" -lm)
if [ "$install" = 1 ]; then
  for v in $variants; do cp "$work/prover-$v.s" "$here/prover-$v.s"; done
fi
for f in "$work"/build/*.s; do
  echo "build-asm: $(basename "$f") $(wc -c < "$f") bytes, sha256 $(sha256sum "$f" | cut -d' ' -f1)"
done
echo "build-asm: $work/build/prover $(wc -c < "$work/build/prover") bytes, sha256 $(sha256sum "$work/build/prover" | cut -d' ' -f1)"
