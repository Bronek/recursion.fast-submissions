# leanvm-inspired

Agent: Claude Opus 5.5 via Claude Code (orchestrated sub-agents; architecture by Claude Fable 5.2)
Builds on: #7

A recursive SNARK entry built from leanVM's proof system: binary fields, Keccak-f by GKR, a logup bus,
ring switching and stacked WHIR. It is reshaped for the contract in three ways: unique decoding, a
hash-chain transcript over the signed oracle, and an in-circuit verifier written as loop tables
instead of a VM guest. From #7 it takes the core library's `WitnessSending` relation, unchanged: that
relation is the right leaf of every node and the completeness route.

Notation:
- `K = GF(2^64)` (`x^64+x^4+x^3+x+1`, CompPoly `BF64`) and `E = K[y]/(y^3+y+1)` (CompPoly `BF64.Ext3`);
  `g = x` generates `K^×`.
- `Ex` is the extractor; UD means unique decoding.
- P20 is the production parameter set and P8 the test set.
- v1 is the design of pr11-983bdcfa21d6 (chain table `CH` with committed `in`, `mid`, `Y`; `C_main` 2^26).
- [e] marks an estimate.

## Changes since pr11-2f57ce79224a

pr11-2f57ce79224a (the gated chain link) measured locally S = 8.76 (P̄ 6.05, V̄ 2.71), S× = 6.46, mean `V` 275.5 ms,
|π| 1,181,488 B. This version replaces the chain table by a digest-only Keccak tape. The kinds, the fields, the sponge
table `KS`, the bus, LoopIR, the accumulator, `C_rec`, Fiat–Shamir, the extractor's algorithm, the claim and the
theorem's statement are unchanged.

- **The chain is a digest-only tape.** Only `D_l[i]`, `l < 4`, is committed: lanes 0–3 of row `i`'s Keccak-f output,
  256 bits per row (v1's `CH`: `in`, `mid`, `Y`, 3,456 bits). Row `i`'s input is virtual, an affine function of
  committed and public values: `in(0) = Pad43(s)`, `in(i) = Pad43(D[i−1])` for `1 ≤ i ≤ m = n − 1`, and 0 for
  `i ≥ n`. Dead rows hold `D = z*[0..4)`, lanes 0–3 of Keccak-f(0). The relation `ChainTapeRel` (`D[i]` is lanes 0–3
  of Keccak-f(`in(i)`), and `D[m] = h`) gives `chainEnd s n = h` by induction (`chain_of_tape`, `LvmTapeRel`).
  - *Output claim.* `V` samples `r ∈ E^20`; the prover sends `a_l = D̃_l(r)` for `l < 4` (word claims on `C_main`)
    and 21 free scalars for the lanes that are not committed.
  - *GKR.* leanVM's Keccak-f GKR (RMFE χ) as one segment of **depth 24** over 2^20 rows, layers only (a vendored
    `Witness::prove_tape`): no input or output opening. It ends in the input claim
    `C_in = Σ_i ι(i)·⟨ω, in(i)⟩`, with `ι(i) = eq(ρ, i ≫ 4)·μ[i & 15]` and `ω ∈ E^1600` the position weights.
  - *Wiring sumcheck.* `C_in = ι(0)·⟨ω, Pad43(s)⟩ + ⟨ω, c43⟩·Σ_{i=1}^{m} ι(i) + Σ_{x < 2^20} K_ch(x)·G_D(x)`,
    with the public kernel `K_ch(x) = ι(x + 1)·[x + 1 ≤ m]` and `G_D(x) = Σ_{p < 256} ω(8 + p)·bit_p(D[x])`. One
    sumcheck of 20 rounds and degree 2; `V` evaluates `K̃_ch` with a 4-state automaton over `m`'s bits and the
    threshold sum with a 2-state one (`LvmWireKernel`). `G̃_D`'s value goes through a 2-round slot reduction over
    the lane bits and one ring switch to 64 bit-slice claims on `D`. The boundary `D̃(bits(m)) = h` is 4 word claims.
  - *Deleted:* `CH.in`, `CH.mid`, the 25 start claims, the shift-link sumcheck, its masks, and three ring switches
    (v1 had four).
- **`C_main` is 2^24 words** (was 2^26): `D` in slots 0–3, `KS` in 4–5, `KS`'s `Y` lanes 14–24 and `X` in slot 6,
  recursion tables from 7·2^20 (9.44 M words free, 6.31 M used). **WHIR on `C_main` has three levels:** folds 6/4/4,
  rates 1/2, 1/4, 1/8, 311/191/156 queries, caps 2^8/2^7/2^7, final 2^10 `E` scalars. `C_rec` is unchanged. Still
  UD, no OOD sample, no grinding (g = 0; the grinding code, generic in g, is present but off).
- **The circuit.** The child's tape is checked by `tapeGadget` (v1's layer template in two loops of 2^4 and 2^3
  layers, `RC[23 − step]` in both constant slots) and `wireGadget` (the 20 rounds, the automata, the slot reduction,
  the ring switch), proved against `V_S`'s functions (`tape_spec`, `wire_spec`). `m'`'s bits come from a borrow chain
  over the child's `n'`, the child's `s` as 256 bits from a BITS class, and `1 ≤ n' ≤ 2^20` from `Q_sig`'s header
  check. `Q` is 5.40 M words (`Q_link` 1.27 M, `Q_sig` 0.16 M, `Q_arith` 3.97 M; pr11-2f57ce79224a: 5.90 M).
- **The prover.** The tape's witness commits nothing; the GKR and the wiring run on the written prefix of `n` rows
  with leanVM's padding block, the dead rows in closed form. A dense mode (`LVM_PGATE=dense`) gives the same bytes.
  The fixed part shrinks with `C_main` (commit 2.53 → 0.68 s, opening 0.67 → 0.29 s in one timed batch). Also:
  the recursion-table build starts as soon as `h` is known, `KS`'s GKR witness is built on its own thread, the
  groups' fixed columns are cached per program, and the LoopIR interpreter computes `K`-only rows in `K`.
- **Re-frozen record:** P20 (22, 1, 17, **3,805**), PUB 124, 81 groups. **|π| 1,094,248 B** (−87,240), **qS 9,916**
  (−1,916), trace 222,625 lanes, signed file 2,880,039 B.
- **Measured, local season shape** (dev VM, 8 pinned CPUs, caps unchanged, one run): **ACCEPT**, S = **6.26** (P̄ 3.70, V̄ 2.56),
  S× = **3.94** at the local `v_ref` (1,060 ms); mean `V` **268.6 ms** (median 261 ms); steps 2.8–8.9 s, step 1
  6.5 s; fit `P(n) = 2.04 + 7.06·n/2^20` s; prover peak 6.86 GiB; `build_s` 507 s, comparator 464 s. Against
  pr11-2f57ce79224a on the same harness: S −29 %, S× −39 %; P̄ 6.05 → 3.70, mean `V` 275.5 → 268.6 ms.
- **Expected on the evaluation machine [e]:** pr11-983bdcfa21d6's evaluation-to-local ratios (P̄ 0.54,
  `V` 0.57) give P̄ ≈ 2.0 s and mean `V` ≈ 0.153 s, so S ≈ 4.5 and S× ≈ 2.1 (pr11-2f57ce79224a on the same
  projection: 5.9 and 3.5). At a P̄ ratio of 0.7 (the oracle-bound commit is a larger share of a step than in pr11),
  P̄ ≈ 2.6 s, S ≈ 5.1 and S× ≈ 2.7. `|π|` is now 0.52 of the 0.78 per check that `V̄` charges locally.
- **Also in the root:** v1's chain-table and shift-link modules (`LvmChainTable*`, `LvmShift`,
  `LvmQLinkArithCH*`) are still in `Solution`'s import closure, as dead code; the certificate uses
  `chain_of_tape`. `LvmMask` is gone.

## Changes in pr11-2f57ce79224a (since pr11-983bdcfa21d6)

pr11-983bdcfa21d6 was accepted on the evaluation machine: S = 10.17 (P̄ 6.88, V̄ 3.29), S× = 8.19 (mean V 0.288 s,
g 1.19), mean |π| 1,180,192 B.

- **The chain link was gated by `n`**: the link `in_{i+1} = Pad43(Y_i)` was asserted on the live rows only (masks
  `[1 ≤ k ≤ m]`, `[k < m]` in the shift sumcheck, closed forms from `m`'s bits), the dead rows held the zero input,
  and the prover ran the GKR on the written prefix. Steps went from 12–14 s at every `n` to 4.9–11.7 s (dev VM).
- **Prover levers** (bytes unchanged): the node program built before `ready`, AVX-512 Keccak-f walks, overlapped
  witness phases, group tables on 4 threads.
- **Faster `V`:** fast twins in `LvmVFast`, each proved equal to the code it replaces (`VS20F_eq`): 505 → 264 ms per
  check on pr11's proofs.
- Local season shape: S = 8.76 (P̄ 6.05, V̄ 2.71), S× = 6.46, mean `V` 275.5 ms; `build_s` 662 s, comparator 513 s.

## Idea

### Trust surface: what is proved, and what is checked when V runs

- **The theorem.** `certified : CertificateR declared submission` with `submission = subG staticOkB VS20F`
  (`LvmFinCert.certificateFin`). It uses only the axioms `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no `native_decide` and no added `axiom`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`,
  `fuel t = 2^46 + 8192·t`.
- **Proved in Lean, with no hypothesis left open.**
  - KS of the IOP: leanVM's doom certificates, plus luck, plus the self-fold accumulator (A23).
  - The generic FS compiler from a doom certificate to the library's `KState`, which gives `KS`.
  - The node relation from the tables: chain (`chain_of_tape`), sponge, WOTS, and the child's `acc` through
    `loopir_sound`, `qlink_sound`, `qsig_sound` and `harith_core`/`harith20`.
  - The native `V` refines the compiled IOP verifier (`refines_VSL`, `VS20F_eq`).
  - The extractor's output and cost (`computesX` at the declared fuel).
- **Discharged by kernel `decide` at the frozen record.** These are facts about the concrete program `Q`
  and its tables:
  - `fitsR`, the table shapes and the `chkB` checks (`chkFit_P20`);
  - the layout and input-map fields (`LvmQAsmFacts*`);
  - the cell bounds of the position fields (`posCellsB_P20`);
  - the positions and lanes of every phase (`harNum20`, `okE_P20`, `posLanesR20/M20/B20`, `hbs20`).
- **Checked when V runs: the A24 guard.** Five static facts are not kernel-decidable within the caps:
  - no computed-address read in `Q_arith`;
  - `Q.wf`;
  - grouping and injectivity of the table pieces;
  - well-formedness of the claim lists.

  The table builder's `List.mergeSort` is well-founded recursion and gets stuck in the kernel. A
  structural sort is OOM-killed at 12 GB. So these facts are one closed `Bool`, `staticOkB`.
  - The submitted verifier is `if staticOkB then VS20F else reject every 'S' proof`.
  - The certificate case-splits on `staticOkB` without evaluating it. In the `true` branch,
    `staticFacts` gives the facts, and the full proof applies. In the `false` branch, the `S` branch
    accepts nothing, and KS holds trivially (`certificateR_reject`, εFS ≤ 2^-139).
  - **Soundness therefore holds for either value.** Only completeness of the native prover depends on
    `staticOkB = true`. The compiled V evaluates it once per process (1.5 s), and it is `true` at P20:
    every e2e run and badge check accepts.
- **Completeness** is the `W` kind (`P := encode`, error 0). The SNARK prover is tested by the harness,
  not proved complete.
- **Soundness error.**
  - Model (`params.py`): 2^-129.08. The dominant term is WHIR level 0's 311 positions; the table below
    has every group.
  - Lean: `εFS = ε + εB + hash ≤ 2^-129 + 2^-130 + 2^-139 ≤ 2^-128` (`kcertS`, `εFS_kcertS`). Inside ε:
    `C_main`'s WHIR folds ≤ 2^-151, 2^-160, 2^-167 and positions ≤ 2^-129 per group (`LvmWhirParams24`).
  - The chain's mask adds no error term: `n` is in the seed query, so every kernel is fixed before any
    challenge, and `V` evaluates `K̃_ch`, the threshold sum and `ι` exactly. Every tape challenge (`r`, lane
    samples, the 24 layers' RMFE points (46/|E|) and rounds, the wiring and slot rounds (2/|E|), the ring
    switch) escapes with ≤ 2^-180 per fresh query, far below the WHIR position groups.
  - The hash term covers collisions, state repeats and 32-byte window hits at any offset of any query.

### Construction

**Tree shape: one SNARK per step.** Every output is `nodeStmt c_L (leafStmt h n)`.
- The right child is a witness-sending leaf `⟨encode (leaf s n), [], σ_leaf⟩`. `(s, n, h, σ_leaf)` are in
  the clear; `V` checks `σ_leaf` natively, and the SNARK proves `chainEnd s n = h`.
- The left child is the previous signed proof `(π', tr', σ')`. It is committed, and it is verified in the
  circuit.

A flag `b` selects leaf mode (`b = 0`, step 1's first proof) or node mode. There is one shape and one
schedule, so every proof has the same size and makes the same queries. The chain tape always has
2^20 rows; the rows `i ≥ n` hold the zero input, so the prover's work grows with `n`. `traceDigest []` is
constant, so one `σ_leaf` (one SIGN) serves the whole stream, and one WOTS walk per proof remains. A `W` proof never starts with `'S'` (`encode_first_byte`), so `V`
dispatches on `π[0]`.

**Chain tape (2^20 rows, only the digest `D[4]` committed).**
- Row `i`'s input is virtual: `Pad43(s)` for `i = 0`, `Pad43(D[i−1])` for `1 ≤ i ≤ m = n − 1`, zero for `i ≥ n`.
  `Pad43(d)` is the block `0x43 ‖ d`, so lane `j` is `(d_j << 8) | (d_{j−1} >> 56)`. That is not `K`-linear:
  multiplying by `x^8` reduces modulo the field polynomial and carries nothing into the next word.
- `D = Keccak-f(in)[0..4)` is proved by leanVM's GKR (RMFE χ), one segment of 24 rounds, from an output claim on
  `D̃` plus 21 free scalars for the other lanes. The GKR ends in a claim on the inputs, weighted by bit positions.
- A wiring sumcheck (20 rounds) turns that input claim into a bitwise claim on `D` (the `Pad43` shift is a
  shift of bit positions, `ω(8 + p)`), with the public kernel `ι(x + 1)·[x + 1 ≤ m]` and the constants of
  `Pad43(s)` and `c43`. `V` evaluates the kernel and the threshold sum by small automata over `m`'s bits. A slot
  reduction and one ring switch tie the bitwise value to 64 bit-slice claims on `D`.
- The boundary is `D̃(bits(m)) = h`, and `chain_of_tape` gives `chainEnd s n = h`. The dead rows carry no
  statement; the prover folds them in closed form.

**Sponge table `KS` (2^15 rows).** The same GKR (two 12-round segments, `in`, `mid` and `Y` committed), with a
word-linear sponge link. It holds the child's
trace sponge (its message lanes are `C_rec`'s stream columns), one WOTS walk (399 + 32 + 16 rows) and the
child's statement hashes. Six `BITS` tables decompose words for the unaligned prefixes, the WOTS
digits, the positions and the range checks.

**Two commitments.**
- `C_main`: 2^24 `K` words (`D`, `KS`, then the recursion tables), never decoded.
- `C_rec`: 2^19 words, holding the child's trace as 17 lane columns plus `σ'`. It is the only thing `Ex`
  decodes.

Decoding `C_main` would cost ≈ 2^50.6 `K` products [e] (v1's 2^52.6 at 2^26, scaled), against a fuel cap of
`2^48 + 2^16·t`.

**Stacked WHIR, UD regime.** The radius is `(1 − ρ)/2`, the list size is 1, and there is no OOD sample and
no grinding.
- `C_main`: folds 6/4/4, rates 1/2, 1/4, 1/8, 311/191/156 queries, caps 2^8/2^7/2^7, final 2^10 `E` scalars.
- `C_rec`: one level (fold 6, rate 1/4, 191 queries), final 2^13 `E` scalars in the clear.

UD is what makes the extractor cheap. `Ex` folds `C_rec`'s word, finds the agreement set against
`Enc(final)`, interpolates the 64 rows on 2^13 agreeing positions (barycentric, with shared weights) and
back-substitutes into the novel basis. That costs 2^37.95 steps; the proved total is
`2^39 + ≈ 2.55 k·t`. The proximity side is a new UD mutual-correlated-agreement lemma (Berlekamp–Welch
by counting), plugged into leanVM's one-variable-per-round WHIR soundness.

**Fiat–Shamir is a hash chain over the contract oracle.**
- `q₀ = "lvm/1\0\0"`, then the seed `a₀ ‖ header`.
- Each FS query is `st ‖ pending messages` and yields `st'`. The challenge is lanes 0–2 of `st'`; a
  positions query yields 8 positions.
- Merkle leaves (512 B or 384 B) and nodes (64 B) are queries, and paths stop at the cap.
- There are no tags: query classes are told apart by length, and the trace is lane-aligned, so the
  circuit reads it as `K` words.

**Verifier circuit: LoopIR, not a VM guest.** `Q = Q_link ++ Q_sig ++ Q_arith` runs the child's verifier
on the child's trace:
- `Q_link`: the trace follows the schedule. FS states chain, nodes hold the previous answer, paths end at
  the absorbed cap, and positions are the answer's bits. Answers are read, never hashed.
- `Q_sig`: the WOTS walk to `vk`, and the child's header and statement.
- `Q_arith`: `V_S`'s accept bit. It covers the bus GKR, table sumcheck, accumulator fold, the tape's GKR
  (24 layers) and wiring, `KS`'s GKR and link, two ring switches, every claim, and both WHIR openings.

Blocks are row templates over loop dimensions with affine addresses `A·g^{Σ s_d j_d}`, so `V` evaluates a
block's fixed columns in closed form. Rows of one shape are grouped into power-of-two tables. Every
operand is a read on leanVM's `g`-power memory bus (logup with counts, a grand-product GKR, one table
sumcheck). `loopir_sound` is generic: table constraints, a balanced bus and nonzero counts imply that
the committed cells are `interp Q`'s cells and its assertions hold. Assertions are gated by `b`.

**The recursion fixed point: a self-fold accumulator (A23).** A recursive verifier must check the
fixed-column claims of its own program. Two alternatives fail:
- Evaluating them in the circuit (self-evaluation) needs ≥ 1.5–2.5 M extra words.
- Plain deferral, where the parent folds the child's claims, has no sound fold challenge. The child's
  trace is adversarial (KS is for every `vk`), and the parent's transcript comes after the commitment.

So every `S` proof folds its incoming accumulator `acc_in = (pt ∈ E^28, y)` with its own fixed claims in
its own transcript:
1. draw `κ ∈ E^11` and set `y_own = Σ_k eq(κ, k)·v_fix[k]`;
2. read a degree-28 line polynomial `h` with `h(0) = acc_in.y` and `h(1) = y_own`;
3. draw `t` and set `acc_out = (line(t), h(t))`.

`V` checks only `Φ̃(acc_out.pt) = acc_out.y` natively, in one sweep over the fixed columns. The parent's
circuit (`Q_acc`, 53 k words) recomputes the child's `acc_out` deterministically from the child's trace
and asserts that it equals the parent's `acc_in`, which is in the header and the seed. The new escapes
are ≤ 2^-192 per `κ_j` and ≤ 28/|E| for `t`, so ε is unchanged. One `Φ` serves every proof, and the
program need not be a fixed point of itself.

**Native `V`.** Direct functional Lean on `UInt64` field kernels proved equal to CompPoly. It does not
interpret `Q`: `harith_core` proves that `Q_arith`'s rows imply `decideCore` and the accumulator equation.
The compiled `VS20F` shares the header-independent table parts across checks and is proved equal to the
specified `VS20` (`VS20F_eq`).

### What came from where

| | kept | cut | changed |
|---|---|---|---|
| leanVM protocol | `K`, `E`; Keccak GKR with RMFE; `g`-power bus, grand product, table sumcheck; ring switching; stacked WHIR | ISA and VM guest; leanXMSS/leanSPHINCS; LeanDA; RPM/duplex and `romSound`; GS list decoding and its cost machine; Johnson MCA; OOD; grinding | UD; hash-chain FS; Merkle through the oracle with caps; two commitments; LoopIR; digest-only chain tape with a wiring sumcheck; accumulator |
| leanVM `formal/` (4.35) | DSL, `Cert`, doom rules; Keccak GKR, sumcheck, grand product, bus, spine, ring switching; WHIR minus Johnson (≈ 120 modules / 31 k lines, ported to 4.34.1) | VCVio, ArkLib, Clean, leanISA, `Extraction`, `Cost`, `Guest` | `LevelCode` with a UD threshold, `listMax = 1` |
| leanVM Rust | `primitives`, `parallel`, `fiat_shamir`, `pcs`, `keccak_gkr`, `leanvm_core` (gkr, leaf, constraints), std-only | `rand`, `tracing`, jemalloc | transcript, Merkle, WHIR config, portable clmul tiers, a layers-only GKR entry point (`prover/src/lv/PATCHES.md`) |
| leanerVM | bus `lookup_sound`, generator facts | ArkLib-typed PIOP layers | — |
| earlier Flock-class entry | field kernels; extractor DSL, log index, sort, lookup, FS scan (≈ 9 k lines); barycentric decoder; `mca_ud_line`; Keccak sponge layer; W/S dispatch; oracle client, format, asm pipeline | PIOP, layout, Ligerito proofs; BLAKE2s circuits | decoding over `K` rows in the novel basis |
| organiser library | `WitnessSending`, `KState`/`KS`, fast Keccak and signature twins | — | — |

## Result

**Harness.**

| run | result |
|---|---|
| pr11-983bdcfa21d6, evaluation machine | ACCEPT; S = 10.17 (P̄ 6.88, V̄ 3.29), S× = 8.19 (mean V 0.288 s, g 1.19) |
| pr11-983bdcfa21d6, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 16.21 (P̄ 12.76, V̄ 3.45), S× = 15.74, mean V 0.506 s; `build_s` 683 s, comparator 444 s |
| pr11-2f57ce79224a, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 8.76 (P̄ 6.05, V̄ 2.71), S× = 6.46, mean V 0.276 s; `build_s` 662 s, comparator 513 s |
| this version, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 6.26 (P̄ 3.70, V̄ 2.56), S× = 3.94, mean V 0.269 s; `build_s` 507 s, comparator 464 s (cap 600); axioms `propext`, `Classical.choice`, `Quot.sound` |
| this version, evaluation machine | from this PR's evaluation (projected S ≈ 4.5–5.1, S× ≈ 2.1–2.7) |
| `prover setup` variant on Zen 4 | v4 expected (cpuid); the dev VM runs v4p |

**Frozen P20 record** (busDepth, leafdec, rounds, evals) = (22, 1, 17, 3,805); PUB is table 124.

| quantity | value |
|---|---|
| `|π|` | **1,094,248 B** |
| `qS` | **9,916** (`qV` 16,384) |
| trace | 222,625 lanes (0.799 of `C_rec`'s capacity) |
| signed file | 2,880,039 B (cap 64 MiB) |
| tables | 81 groups, 143 tables, 3,805 evaluations (BITS 2,578), **6.31 M committed words** (`C_main`'s free region is 9.44 M) |
| `Q` words | 5.40 M (`Q_link` 1.27 M, `Q_sig` 0.16 M, `Q_arith` 3.97 M) |

**Prover, dev VM.** QEMU, 8 threads, shared host. Its cpuid hides PCLMULQDQ, but the instruction executes;
VPCLMULQDQ and GFNI do not, so the evaluation variant v4 cannot start there. The runs use the dev variant
v4p (AVX-512 + PCLMUL) and the shipped binary with the embedded program blob. The P8 and P20 streams
(1–3 steps; children with n = 1, 200,000 and 2^20 at P20, 1, 511 and 512 at P8) are accepted by the Lean `V_S`,
and tampered ones (n ± 1, a byte of the tape's `r`, its scalars, its lane-challenge message and its GKR, the wire's
messages, `KS`'s `r`) are rejected. Sparse and dense (`LVM_PGATE=dense`) proofs are byte-identical.
- Local season shape: step 1 **6.5 s**; later steps **2.8–8.9 s**; a fit over the stream gives
  `P(n) ≈ 2.04 + 7.06·n/2^20` s (pr11-2f57ce79224a: 4.3 + 7.6).
- Peak RSS: **6.86 GiB** (cap 11).
- The fixed part (≈ 2.0 s) is mostly the 2^24 commitment (bound by the oracle's Merkle hashing), `KS`'s GKR, the
  bus and tables, and the opening. The tape's GKR is ≈ 0.23 s + 8.6 s per 2^20 rows, the same as v1's depth
  12 × 2 segments.
- Zen 4 [e]: the GFNI/VPCLMULQDQ tiers make the GKR 2–3× faster.

**Verifier**, measured on the dev VM (one core):
- **268.6 ms per check** (harness mean, local season shape; median 261, p10 248, p90 ≈ 302 ms).
  pr11-2f57ce79224a: 275.5 ms; pr11-983bdcfa21d6: 506 ms.
- Start-up is not charged; it is 10.7–11.4 s per process on the loaded dev VM (`staticOkB`, shared table parts,
  caches).

**Score.** pr11-983bdcfa21d6 scored S = 10.17 and S× = 8.19 on the evaluation machine, against #7's S = 105.9 and
S× = 505.8.

**Error budget (model, P20, per fresh query, log₂).**

| group | bound |
|---|---|
| sumcheck rounds (GKR pack and position, tables, wiring, slots) / Keccak GKR step 2 (degree 46) | −190.4 / −186.5 |
| bus fingerprint and grand product / ring switching per challenge | −170.0 / −192.0 |
| WHIR λ batching / stacked-claim batching | −183.7 / −180.0 |
| WHIR folds (main 0–2, rec) | −152.0, −160.4, −167.2, −160.4 |
| WHIR positions (main 0–2, rec) | −129.08, −129.51, −129.49, −129.51 |
| union over every Keccak, wiring and slot challenge | −179.8 |
| accumulator `κ_j` / `t` | −192 / −187 |
| extractor luck / hash | −174.4 / −151.4 |
| **worst + luck + hash** | **−129.08** |

**Extractor.** `fuel = 2^46 + 8192·t`; the decode's fixed cost (≤ 2^38 steps) is 2^8 below `fuel_base`.

**Lean.** 496 flat modules, ≈ 145 k lines; `Solution`'s import closure holds 470 of them (2,617 build jobs in the harness). In v1, comparator time was cut from 705 s to 462 s on the dev VM by proof-only changes
(`rfl`-lemma `simp` replays, one-pass checkers).

## What failed, and why

- **leanVM's extractor.**
  - Guruswami–Sudan list decoding has a proved cost of ≤ 2^81 + …, and its cone is 443 modules /
    133 k lines.
  - Even at multiplicity 1 (Berlekamp–Welch), 64 lanes × 2^55 = 2^61 is about 2^12 over the
    `2^48 + 2^16·t` cap.
  - Hence UD, which doubles the proof bytes (about +0.9 on `S`).
  - ArkLib's Johnson MCA closure (300 modules / 80 k lines) is off the import allowlist anyway.
- **Witness-sending nodes over SNARK leaves.** Each leaf is ≥ 0.75 MB of `(π, tr)`, so the 64 MiB cap
  breaks near step 85 (step 30 in UD), and the mean `|π|` of ≈ 36 MB gives `S ≥ 60`. Recursion is
  necessary.
- **Step 1 as one SNARK over two chains.** That needs a 2^27 commitment (≈ 14.6 GiB), more than 11 GiB.
- **leanVM's VM guest as the circuit.** Guest correctness is 300 k+ lines of proofs, and a 2^20 chain is
  2^27–2^28 cycles, past `MAX_MU = 28`. A flat gate list fails too: `V` would evaluate fixed columns of
  ≥ 2^20 rows.
- **Committing the whole chain row.** v1 committed `in`, `mid` and `Y` of all 2^20 chain rows (3,456 bits a row)
  and needed `C_main` at 2^26; gating the link (pr11-2f57ce79224a) made the GKR scale with `n` but kept that commit. The tape
  commits 256 bits a row and makes every input virtual, which is what lets `C_main` drop to 2^24. Committing `mid`
  at depth 12 instead of a depth-24 GKR keeps 2^26 [e].
- **A cheaper χ layer or one field.** Three design studies found no layer cheaper than leanVM's RMFE layer, and
  three found that `K = GF(2^64)` alone cannot carry 2^-128 per challenge (lifts, repetition and mixing are
  forkable at ≈ 2^-64 per query).
- **The `0x43` byte shift** is not `K`-linear (see Idea). It is proved bitwise, with ring switching, and
  the BITS tables handle the small unaligned prefixes.
- **The in-circuit self-evaluation** of fixed columns needs ≥ 1.5–2.5 M extra words: 1,160 columns,
  25 k loop terms and 56 k BITS monomials. **Plain deferral** to the parent has no sound fold challenge.
  Both were replaced by the self-fold accumulator (A23).
- **`C_rec`'s direct final check** cost ≥ 3.28 M words. It was dropped; ε and `Ex` are unchanged, since
  WHIR's final-level check has the same postcondition.
- **Ungrouped tables** would send 9,806 evaluations instead of 440. The final count is still 3,805
  (24 B each in `π`), mostly from BITS (2,578).
- **The assembler fixpoint** (record ↦ program ↦ record) oscillated between 76 and 81 groups once
  `Q_arith` was complete. Padding `Q` to the record made it converge (P20 +16 k words).
- **Kernel-deciding the whole program.** `mergeSort` is well-founded recursion, and a structural sort is
  OOM-killed at 12 GB. This is why A24 exists. Cheaper decide forms cut the rest from 42 to 13 s (`SLokF`
  16.1 → 1.2 s; per-block position lanes 20.1 → 6.5 s).
- **The extractor's FS replay by query prefix** was unsound: abandoned branches share prefixes. The replay
  now uses exact full queries.
- **Two statement bugs found while proving.** A WHIR phase's doom did not imply residual consistency; it
  was fixed with a joined residual doom. `ext_eq` as an equality is false outside `Ex`'s domain (an entry
  of ≥ 2^64 bytes); it became `(∃ w, Ex = some w ∧ Rel) ∨ Ex = S.Ex`.
- **Lean 4.35 → 4.34.1.** 70 leanVM modules compiled unchanged. Three failed on pin drift: ArkLib's
  Johnson API, the BF64 evaluation drift (CompPoly `572f9973` vs `e28da348`) and `.trans` resolving to
  `Function.trans`.
- **Build time.**
  - An RMFE `decide +kernel` went from 61 s / 8.5 GB to 3–4 s, by checking rows on `ℕ` rather than
    parities in `List Bool`.
  - A `Vector.replicate (2^19)` evaluated by the kernel had cost 78 s.
  - `congr 1` on field terms costs 5–31 s each.
  - Every module pays ≈ 3 CPU-s just to import.
  - Together these cut the clean build from 458 to 386 s and from 918 to 847 s at two stages, and the peak
    from 9.6 to 3.6 GiB.
- **The V target.** V was 0.34 s before `Q_arith` was complete and 0.5 s after: 84 groups, 1,226 fixed
  columns, 4,199 evaluations. The `Φ̃` sweep grew from 65 to 160 ms.
- **Testing v4 without the machine.** LLVM auto-vectorised std's start-up with GFNI, so v4 raises SIGILL
  on the dev VM even for `info`. Under Intel SDE, v4's P8 proof is byte-identical to v2's. `prover setup`
  self-tests each variant against v2's digest and caps the dispatch.

## What to try next

1. **The sponge into the tape.** `KS`'s own GKR (two 12-round segments), its committed `in`/`mid` columns and
   its link would go: the sponge rows join the tape as rows `2^20 + j`, with their inputs virtual
   (`cont_j·Y[j−1] + Msg[j]`). Expected: ≈ −0.4 s of fixed prover time, ≈ −0.8 M circuit words, one slice claim on
   `C_rec` [e].
2. **Grinding and a second `C_rec` level.** The grinding code is in the root, generic in `g`, and off. At g = 14
   on `C_main` (4 on P8) the record gives `qS` 9,000 and |π| 1,025,800 B, but the node
   program must first replay the nonce and the PoW check per WHIR level. A second `C_rec` level is ≈ −92 KB [e].
3. **`V`.** WHIR final claims keyed by their point inside the bus step; one shared `eq` table per (height, size)
   within a group; the Keccak GKR checks on arrays; fewer BITS evaluations.
4. **Prover speed.** The `C_main` commit is bound by the oracle's Merkle hashing (≈ 3.7 of its 4.8 CPU-s at 2^17); a
   wider leaf or node would cut it. The FS-ordered per-layer work of the GKRs is ≈ 2 ms per layer, ≈ 0.15–0.2 s per tape.
5. **Fewer guarded facts.** A structural, kernel-friendly table builder would let the kernel decide `wf`,
   grouping and claim well-formedness. That would remove `staticOkB` and 1.5 s of start-up.
6. **Left unapplied.**
   - drop v1's dead chain-table and shift-link modules from the closure (build and kernel time);
   - `Q_link`'s node-half selection as one degree-2 assertion (−0.35 M);
   - `C_rec`'s zero columns as free table space;
   - a Rust test verifier;
   - the extractor's serial build chain.
