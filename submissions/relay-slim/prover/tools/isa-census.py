#!/usr/bin/env python3
"""Which instruction-set extensions each CPU variant of the linked prover uses (K-DISP static check).

  objdump -d --no-show-raw-insn PROVER > PROVER.dis
  python3 -I tools/isa-census.py PROVER.dis [prover-v2.s]

Every instruction is attributed to the function it lies in, and the function to a variant by its suffix
(`_lvm_v2`, `_lvm_v4p`, `_lvm_v4`; `main` is dispatch.s; the rest is glibc/libgcc, not checked: glibc picks
its own string kernels by cpuid). An instruction is classified by mnemonic and registers into the
extension that introduced it. The rules (exit 1 on a breach):

* `main` (dispatch.s): baseline x86-64 only (and cpuid/xgetbv);
* v2: x86-64-v2 only, except inside the functions that carry `#[target_feature]` and are entered only
  after a `cpuid` check (ALLOWED_V2: the AVX-512F carry-less comb, PCLMULQDQ under `is_x86_feature_detected`,
  the AVX-512F x8 Keccak). objdump prints LLVM's `rep bsf` as `tzcnt` (the same bytes; without BMI1 the CPU
  runs them as `bsf`): it is counted as `repbsf`, after checking that prover-v2.s spells no `tzcnt`;
* every variant may run `cpuid` and `xgetbv` (std's feature detection; `xgetbv` only after OSXSAVE);
* v4p: at most x86-64-v4 + PCLMULQDQ;
* v4: at most x86-64-v4 + PCLMULQDQ + VPCLMULQDQ + GFNI + AVX512VBMI (exactly what dispatch.s checks).
"""
import collections
import re
import sys

LEVELS = {
    "v2": {"base", "sse", "sse2", "sse3", "ssse3", "sse4", "popcnt", "cx16"},
}
LEVELS["v3"] = LEVELS["v2"] | {"avx", "avx2", "bmi1", "bmi2", "fma", "f16c", "lzcnt", "movbe", "xsave"}
LEVELS["v4"] = LEVELS["v3"] | {"avx512"}
DETECT = {"cpuid", "xsave"}
ALLOW = {
    "main": LEVELS["v2"] | DETECT,
    "v2": LEVELS["v2"] | DETECT | {"repbsf"},
    "v4p": LEVELS["v4"] | DETECT | {"pclmul"},
    "v4": LEVELS["v4"] | DETECT | {"pclmul", "vpclmul", "gfni", "avx512vbmi"},
}
# v2 functions that run only after a run-time feature check (their own `#[target_feature]`)
ALLOWED_V2 = [
    (re.compile(r"software12clmul_avx512"), {"avx512", "avx2", "avx"}),
    (re.compile(r"gf2_646x86_645clmul|gf2_646x86_643mul"), {"pclmul", "avx"}),
    (re.compile(r"keccak18keccak_f_x8_avx512"), {"avx512", "avx2", "avx"}),
]

GFNI = re.compile(r"^v?gf2p8")
VBMI = re.compile(r"^(vpermb|vpermi2b|vpermt2b|vpmultishiftqb)$")
OTHER512 = {  # AVX-512 subsets the dispatch does not check
    "vbmi2": re.compile(r"^(vpcompress[bw]|vpexpand[bw]|vpshld|vpshrd)"),
    "vnni": re.compile(r"^vpdp(bu|ws)"),
    "bitalg": re.compile(r"^(vpopcnt[bw]|vpshufbitqmb)$"),
    "vpopcntdq": re.compile(r"^vpopcnt[dq]$"),
    "ifma": re.compile(r"^vpmadd52"),
    "bf16": re.compile(r"bf16"),
    "fp16": re.compile(r"ph$|^v.*sh$"),
}
AES = re.compile(r"^v?aes")
SHA = re.compile(r"^sha")
BMI1 = {"andn", "bextr", "blsi", "blsmsk", "blsr", "tzcnt"}
BMI2 = {"bzhi", "mulx", "pdep", "pext", "rorx", "sarx", "shlx", "shrx"}
ADX = {"adcx", "adox"}
SSE4_EXTRA = {"crc32"}
EVEX_ONLY = re.compile(r"^(vpternlog|vpermt2|vpermi2|vpcompress|vpexpand|vprolv|vprorv|vprol|vpror|vpmovm2|vpmov[qdw][bwd]|vpbroadcastm|"
                       r"vpcmpu?[bwdq]$|vpcmpu?[bwdq] |vpmovq2m|vpmovd2m|vpmovb2m|vpmovw2m|vpsravq|vpsraq|vpabsq|vpmaxsq|vpmaxuq|"
                       r"vpminsq|vpminuq|vpmullq|vpconflict|vplzcnt|vrcp14|vrsqrt14|vrndscale|vreduce|vrange|vfixupimm|vgetexp|vgetmant|"
                       r"vscalef|valign|vextract[if](32x4|64x2|32x8|64x4)|vinsert[if](32x4|64x2|32x8|64x4)|vshuf[if](32x4|64x2)|"
                       r"vbroadcast[if](32x[248]|64x[24])|vpermw|vpsllvw|vpsrlvw|vpsravw|vdbpsadbw|vpmovsx|vpmovzx|vptestn?m|"
                       r"vcvt.*2u|vcvtu|vpandn?[dq]|vpor[dq]|vpxor[dq]|vmovdqu(8|16|32|64)|vmovdqa(32|64)|vpblendm|vblendm|vpscatter|vscatter|vgatherpf|vscatterpf)")


def classify(mn, ops):
    """The extensions an instruction needs (a set of names; 'base' for plain x86-64)."""
    ext = set()
    if mn.startswith("k") and re.search(r"%k[0-7]", ops):
        return {"avx512"}
    if GFNI.match(mn):
        ext.add("gfni")
        if mn.startswith("v"):
            ext.add("avx512" if re.search(r"%zmm|%k[1-7]|\{", ops) else "avx")
        return ext
    if "pclmulqdq" in mn or mn.startswith("vpclmul") or mn.startswith("pclmul"):
        wide = re.search(r"%[yz]mm", ops)
        ext.add("vpclmul" if wide else "pclmul")
        if mn.startswith("v"):
            ext.add("avx512" if re.search(r"%zmm|%k[1-7]|\{|%[xy]mm(1[6-9]|2\d|3[01])", ops) else "avx")
        return ext
    if VBMI.match(mn):
        return {"avx512vbmi", "avx512"}
    for name, rx in OTHER512.items():
        if mn.startswith("v") and rx.search(mn):
            return {name}
    if AES.match(mn):
        return {"aes"}
    if SHA.match(mn) and not mn.startswith("shl") and not mn.startswith("shr"):
        return {"sha"}
    if mn in BMI1:
        return {"bmi1"}
    if mn in BMI2:
        return {"bmi2"}
    if mn in ADX:
        return {"adx"}
    if mn == "lzcnt":
        return {"lzcnt"}
    if mn == "movbe":
        return {"movbe"}
    if mn == "popcnt":
        return {"popcnt"}
    if mn in ("cpuid",):
        return {"cpuid"}
    if mn.startswith("xgetbv") or mn.startswith("xsave") or mn.startswith("xrstor"):
        return {"xsave"}
    if mn in SSE4_EXTRA:
        return {"sse4"}
    if mn.startswith("cmpxchg16b"):
        return {"cx16"}
    if mn.startswith("v"):
        if re.search(r"%zmm|%k[0-7]|\{1to|%[xy]mm(1[6-9]|2\d|3[01])\b", ops) or EVEX_ONLY.match(mn):
            return {"avx512"}
        if mn.startswith("vfmadd") or mn.startswith("vfmsub") or mn.startswith("vfnmadd") or mn.startswith("vfnmsub"):
            return {"fma"}
        if mn.startswith("vcvtph2ps") or mn.startswith("vcvtps2ph"):
            return {"f16c"}
        if re.search(r"%ymm", ops) and not re.match(r"^v(movap|movup|xorp|andp|orp|broadcastss|broadcastsd|perm2f128|insertf128|extractf128|zeroupper|addp|mulp|subp|divp|maxp|minp|cmpp|blendp|shufp|unpck|sqrtp|movmsk|testp)", mn):
            return {"avx2"}
        return {"avx"}
    # legacy SSE (classified loosely: all of SSE..SSE4.2 is in x86-64-v2)
    if re.search(r"%xmm", ops) or mn.startswith(("p", "movdq", "movap", "movup", "cvt", "pshuf", "punpck")):
        if mn in ("pclmulqdq",):
            return {"pclmul"}
        return {"sse"}
    return {"base"}


def main():
    path = sys.argv[1]
    if len(sys.argv) > 2:
        src = open(sys.argv[2], encoding="utf-8").read()
        assert not re.search(r"\btzcnt", src), "prover-v2.s spells tzcnt (BMI1)"
    func = None
    census = collections.defaultdict(collections.Counter)  # variant -> ext -> count
    funcs = collections.defaultdict(lambda: collections.defaultdict(collections.Counter))
    head = re.compile(r"^[0-9a-f]+ <(.+)>:$")
    insn = re.compile(r"^\s*[0-9a-f]+:\s+(?:(?:rex\.?\w*|data16|lock|rep[nez]*|notrack|bnd|cs|ds|ss|es|fs|gs)\s+)*([a-z][a-z0-9.]*)\s*(.*)$")
    for line in open(path, encoding="utf-8", errors="replace"):
        m = head.match(line)
        if m:
            func = m.group(1)
            continue
        m = insn.match(line)
        if not m or func is None:
            continue
        mn, ops = m.group(1), m.group(2)
        if mn.startswith("(bad)") or mn == "bad":
            continue
        if func == "main":
            var = "main"
        else:
            vm = re.search(r"_lvm_(v2|v4p|v4)(?:\+0x[0-9a-f]+)?$", func)
            if not vm:
                continue
            var = vm.group(1)
        exts = classify(mn, ops)
        if var == "v2" and mn == "tzcnt":
            exts = {"repbsf"}
        for e in exts:
            census[var][e] += 1
            funcs[var][func.split("+")[0]][e] += 1
    bad = []
    for var in ("main", "v2", "v4p", "v4"):
        if var not in census:
            continue
        exts = census[var]
        print(f"{var:5}: " + ", ".join(f"{e} {n}" for e, n in sorted(exts.items(), key=lambda x: -x[1])))
        allow = ALLOW[var]
        for f, ex in funcs[var].items():
            extra = set(ex) - allow
            if not extra:
                continue
            if var == "v2":
                ok = [a for rx, a in ALLOWED_V2 if rx.search(f)]
                if ok and extra <= set().union(*ok):
                    print(f"  v2 guarded: {f[:110]} uses {sorted(extra)}")
                    continue
            bad.append(f"{var}: {f[:120]} uses {sorted(extra)} (counts {dict(ex)})")
    if bad:
        print("BREACHES:")
        for b in bad[:60]:
            print("  " + b)
        print(f"  ({len(bad)} functions)")
        sys.exit(1)
    print("isa-census: every variant within its feature set")


if __name__ == "__main__":
    main()
