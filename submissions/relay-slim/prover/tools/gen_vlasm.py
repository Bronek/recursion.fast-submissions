#!/usr/bin/env python3
# Vendored from relay-echo (scaraven/recursion.fast-submissions PR #12, submissions/relay-echo/src/gen_vlasm.py,
# commit 7360e1c), licensed under the Apache License, Version 2.0 (see ../../LICENSE). Unmodified below this
# header; gen_chain_vl.py imports its gen_body() and KERNELS to write src/keccak_vl.rs.
"""Generates keccak_vlasm.inc: the chain d <- Keccak-256(0x43 || d), n times, with AVX-512F/VL, as one GCC
extended-asm statement whose registers are allocated here, in two kernels that differ only in chi.

Layout: one lane per xmm register, in its low qword; the high qword runs a second, independent chain
(chain2_NAME: step 1's two chains in one thread).  At the top of a step, lane x + 5y is in xmm(x + 5y);
xmm25..xmm29 hold theta's column parities, then its D[x]; two registers are free (xmm30 and xmm31 at the
top of a step); between steps the chain value is in xmm26..xmm29.  pi moves no data: it renames
registers.  Per round:

  theta  C[x] = XOR of the column (VPXORQ, VPXORQ, VPTERNLOGQ); D[x] = C[x-1] ^ ROL(C[x+1], 1) for all x,
         in place in the parity registers (five VPROLQ, five VPXORQ)
  then, one row of the new state at a time:
  theta  a ^= D[x] (VPXORQ) on the row's five source lanes
  rho    VPROLQ in place
  chi    avx512vl:  two copies, then five VPTERNLOGQ (a ^ (~b & c), imm 0xD2) in place;
         avx512vln: two outputs as VPANDNQ + VPXORQ into the free registers, three VPTERNLOGQ in place,
         no copy (the two input registers whose lanes moved are the next free ones)
  iota   VPXORQ with the round constant, at the end of the round

Round 0 skips the lanes that are zero in every chain step (all but 0..4 and 16), and round 23 computes only
the four digest lanes.  Usage: gen_vlasm.py > keccak_vlasm.inc; gen_vlasm.py --variants writes other
splits of chi, for benchmarks.
"""
import sys

RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
      0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
      0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
      0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
      0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
RHO = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
PC = [25, 26, 27, 28, 29]          # column parities, then D (see DREG)
SCRATCH = [30, 31]                 # the two free registers at the top of a step (see chi_row)
H = [26, 27, 28, 29]               # the chain value between steps (the parities are dead then)
K43, K100, K16 = 24, 25, 26        # rows of the constant table after the 24 round constants
# D[x] = C[x-1] ^ ROL(C[x+1], 1) in place: each C[j] is read rotated (by D[j-1]) and plain (by D[j+1]);
# the rotated copy is taken into a free register (f0, f1) before the plain read overwrites C[j]'s register.
D_STEPS = [('rol', 0, 1), ('rol', 2, 0), ('xor', 0, 0),     # D1 = C0 ^ R2 -> PC0
           ('rol', 3, 0), ('xor', 3, 1),                    # D4 = C3 ^ R0 -> PC3
           ('rol', 1, 1), ('xor', 1, 0),                    # D2 = C1 ^ R3 -> PC1
           ('rol', 4, 0), ('xor', 4, 1),                    # D0 = C4 ^ R1 -> PC4
           ('xor', 2, 0)]                                   # D3 = C2 ^ R4 -> PC2
DREG = {1: PC[0], 4: PC[3], 2: PC[1], 0: PC[4], 3: PC[2]}
# The kernels: name -> how many of each row's chi outputs are VPANDNQ + VPXORQ (0, 1 or 2; the rest are
# VPTERNLOGQ), row by row.
KERNELS = {'avx512vl': [0, 0, 0, 0, 0], 'avx512vln': [2, 2, 2, 2, 2]}


def x(r):
    return '%%%%xmm%d' % r


def mem(k):
    return '%d(%%[k])' % (16 * k)


def gen_body(chi_k):
    ins = []
    e = ins.append
    free = list(SCRATCH)

    def chi_row(b, outs, k):
        """chi on one row: e[j] = b[j] ^ (~b[j+1] & b[j+2]).  The first k outputs are VPANDNQ + VPXORQ into the
        two free registers, the others VPTERNLOGQ in place, so a row needs 2 - k copies of its inputs (into
        the free registers) to keep inputs that an in-place output overwrites.  Returns the outputs'
        registers; afterwards the free registers are the ones whose lanes moved."""
        f = list(free)
        orig = {}                               # b[j] after e[j] overwrote it in place
        for j in range(k, 2):                   # copies of b0 (and b1) for the outputs that read them late
            if outs == 5 or j == 0:
                e('vmovdqa64 %s, %s' % (x(b[j]), x(f[j])))
                orig[j] = f[j]
        res = list(b)
        for j in range(outs):
            s1, s2 = (j + 1) % 5, (j + 2) % 5
            r1, r2 = orig.get(s1, b[s1]) if s1 < j else b[s1], orig.get(s2, b[s2]) if s2 < j else b[s2]
            if j < k:
                e('vpandnq %s, %s, %s' % (x(r2), x(r1), x(f[j])))
                e('vpxorq %s, %s, %s' % (x(b[j]), x(f[j]), x(f[j])))
                res[j] = f[j]
            else:
                e('vpternlogq $0xD2, %s, %s, %s' % (x(r2), x(r1), x(b[j])))
        for j in range(2):                      # the new free registers
            free[j] = b[j] if j < k else f[j]
        return res

    # the step's input lanes from H: lane k = bytes 8k..8k+7 of 0x43 || d || 0x01 || 0 ... 0 || 0x80
    e('vpsllq $8, %s, %s' % (x(H[0]), x(0)))
    e('vporq %s, %s, %s' % (mem(K43), x(0), x(0)))
    for k in range(1, 4):
        e('vpsrlq $56, %s, %s' % (x(H[k - 1]), x(free[0])))
        e('vpsllq $8, %s, %s' % (x(H[k]), x(k)))
        e('vporq %s, %s, %s' % (x(free[0]), x(k), x(k)))
    e('vpsrlq $56, %s, %s' % (x(H[3]), x(4)))
    e('vporq %s, %s, %s' % (mem(K100), x(4), x(4)))
    e('vmovdqa64 %s, %s' % (mem(K16), x(16)))
    reg = list(range(25))                       # lane -> register
    zero = [not (i <= 4 or i == 16) for i in range(25)]
    for r in range(24):
        last = r == 23
        for c in range(5):                      # C[c]
            src = [reg[c + 5 * y] for y in range(5) if not zero[c + 5 * y]]
            if len(src) == 1:
                e('vmovdqa64 %s, %s' % (x(src[0]), x(PC[c])))
                continue
            e('vpxorq %s, %s, %s' % (x(src[1]), x(src[0]), x(PC[c])))
            rest = src[2:]
            if len(rest) % 2:
                e('vpxorq %s, %s, %s' % (x(rest[0]), x(PC[c]), x(PC[c])))
                rest = rest[1:]
            while rest:
                e('vpternlogq $0x96, %s, %s, %s' % (x(rest[1]), x(rest[0]), x(PC[c])))
                rest = rest[2:]
        for op, j, t in D_STEPS:
            if op == 'rol':
                e('vprolq $1, %s, %s' % (x(PC[j]), x(free[t])))
            else:
                e('vpxorq %s, %s, %s' % (x(free[t]), x(PC[j]), x(PC[j])))
        nreg = [None] * 25
        for yn in range(1 if last else 5):      # the last round keeps row 0's lanes 0..3
            b = []
            for xn in range(5):                 # new lane (xn, yn) is old lane (xo, xn) after theta, rho, pi
                xo = 3 * (yn - 3 * xn) % 5
                i = xo + 5 * xn
                if zero[i]:                     # a zero lane is D[xo], rotated straight into the lane
                    e('vprolq $%d, %s, %s' % (RHO[i], x(DREG[xo]), x(reg[i])))
                else:
                    e('vpxorq %s, %s, %s' % (x(DREG[xo]), x(reg[i]), x(reg[i])))
                    if RHO[i]:
                        e('vprolq $%d, %s, %s' % (RHO[i], x(reg[i]), x(reg[i])))
                b.append(reg[i])
            out = chi_row(b, 4 if last else 5, chi_k[yn])
            for xn in range(5):
                nreg[xn + 5 * yn] = out[xn]
        reg = nreg
        zero = [False] * 25
        e('vpxorq %s, %s, %s' % (mem(r), x(reg[0]), x(reg[0])))
    for k in range(4):                          # the digest lanes into H
        e('vmovdqa64 %s, %s' % (x(reg[k]), x(H[k])))
    return ins


def gen_fn(w, name, chi_k):
    """chain2_NAME (two chains, one per qword) and chain_NAME (one chain)."""
    ins = gen_body(chi_k)
    w('/* %s: %d instructions per step */' % (name, len(ins)))
    w('/* n steps of each of two chains: ia -> oa in the low qwords, ib -> ob in the high ones */')
    w('__attribute__((target("avx512f,avx512vl"))) static void chain2_%s(uint8_t oa[32], const uint8_t ia[32], '
      'uint8_t ob[32], const uint8_t ib[32], uint64_t n) {' % name)
    w('    uint64_t hv[4][2] __attribute__((aligned(16)));')
    w('    for (int i = 0; i < 4; i++) { memcpy(&hv[i][0], ia + 8 * i, 8); memcpy(&hv[i][1], ib + 8 * i, 8); }')
    w('    if (n) {')
    w('        __asm__ volatile(')
    for k in range(4):
        w('            "vmovdqu64 %d(%%[h]), %s\\n\\t"' % (16 * k, x(H[k])))
    w('            "1:\\n\\t"')
    for s in ins:
        w('            "%s\\n\\t"' % s)
    w('            "decq %[n]\\n\\t"')
    w('            "jnz 1b\\n\\t"')
    for k in range(4):
        w('            "vmovdqu64 %s, %d(%%[h])\\n\\t"' % (x(H[k]), 16 * k))
    w('            : [n] "+r"(n), "+m"(hv)')
    w('            : [h] "r"(hv), [k] "r"(vla_k)')
    w('            : "cc", ' + ', '.join('"xmm%d"' % i for i in range(32)) + ');')
    w('    }')
    w('    for (int i = 0; i < 4; i++) { memcpy(oa + 8 * i, &hv[i][0], 8); memcpy(ob + 8 * i, &hv[i][1], 8); }')
    w('}')
    w('__attribute__((target("avx512f,avx512vl"))) static void chain_%s(uint8_t out[32], const uint8_t in[32], '
      'uint64_t n) {' % name)
    w('    uint8_t spare[32];')
    w('    chain2_%s(out, in, spare, in, n);' % name)
    w('}')


def gen(kernels):
    out = []
    w = out.append
    w('/* generated by gen_vlasm.py (do not edit): the chain d <- Keccak-256(0x43 || d) with AVX-512F/VL, one lane')
    w('   per xmm register, two independent chains in the two qwords. */')
    w('static const uint64_t vla_k[27][2] __attribute__((aligned(16))) = {')
    for c in RC + [0x43, 0x100, 0x8000000000000000]:
        w('    {0x%016Xull, 0x%016Xull},' % (c, c))
    w('};')
    for name, chi_k in kernels.items():
        gen_fn(w, name, chi_k)
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    if '--variants' in sys.argv:                # bench-only: other splits of chi
        sys.stdout.write(gen({'vlk0': [0] * 5, 'vlk1': [1] * 5, 'vlk2': [2] * 5, 'vlk2alt': [2, 0, 2, 0, 2],
                              'vlk1alt': [1, 0, 1, 0, 1], 'vlk21': [2, 1, 2, 1, 2]}))
    else:
        sys.stdout.write(gen(KERNELS))
