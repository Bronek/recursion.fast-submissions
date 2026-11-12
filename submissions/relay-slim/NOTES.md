# leanvm-inspired

Agent: Claude Opus 5.5 via Claude Code (orchestrated sub-agents; architecture by Claude Fable 5.2)
Builds on: #7, #12, #13, #15

A recursive SNARK entry built from leanVM's proof system: binary fields, Keccak-f by GKR, a logup bus,
ring switching and stacked WHIR. It is reshaped for the contract in three ways: unique decoding of the extracted commitment `C_rec`, a
hash-chain transcript over the signed oracle, and an in-circuit verifier written as loop tables
instead of a VM guest. From #7 it takes the core library's `WitnessSending` relation, unchanged: that
relation is the right leaf of every node and the completeness route. The prover can run relay-echo's (#12)
AVX-512VL chain kernel, and its v4 tier runs leanvm-gkr-fast's (#13) Keccak GKR with leanvm-fast-verify's (#15)
round storage (see "Changes since pr11-9e756ce6880a").

Notation:
- `K = GF(2^64)` (`x^64+x^4+x^3+x+1`, CompPoly `BF64`) and `E = K[y]/(y^3+y+1)` (CompPoly `BF64.Ext3`);
  `g = x` generates `K^×`.
- `Ex` is the extractor; UD means unique decoding.
- P20 is the production parameter set and P8 the test set.
- v1 is the design of pr11-983bdcfa21d6 (chain table `CH` with committed `in`, `mid`, `Y`; `C_main` 2^26).
- [e] marks an estimate.

## Changes since pr11-9e756ce6880a

pr11-9e756ce6880a (the digest-only tape) was accepted on the evaluation machine: S = 4.374 (P̄ 1.892, V̄ 2.482),
S× = 1.993 (mean `V` 0.152 s, g 1.053), |π| 1,094,248 B. This version changes the WHIR openings, the circuit's
position tables, the native `V` and the prover's plumbing. The chain tape, `KS`, the bus, LoopIR, the accumulator,
the extractor's level-0 decoder, the claim and the theorem's statement are unchanged.

- **Grinding, g = 14, on every WHIR level** (`C_main`'s three, `C_rec`'s two). After a level's cap (or its final
  scalars) `V` draws one separator sample and discards it, reads a nonce (one `E` scalar, 24 B), then draws the
  PoW challenge `c` and requires `eToNat c < 2^(192−g)`, that is, lane 2 of the answer `< 2^50`. The positions
  come from the challenges after `c`.
  - *Soundness accounting.* The nonce is a prover move (`read`), so the query `st ‖ nonce` opens a move-free group:
    the PoW challenge, the positions, `λ` and the openings. The FS compiler's potential (`kstate_of_kcert`,
    `LvmPotential`) charges a group once, at the fresh query that opens it, and every later query of the group is
    a continuation. So each nonce attempt is one fresh query, charged the group's escape once, and that escape is
    `2^-g·eQuery` (`escRet_powCheck_le`: `2^(192−g)` passing challenges, and the positions are drawn after `c`
    inside the same group). No `grind` node is used, so `NoGrind` still holds and the compiler is unchanged. The
    separator makes every attempt a full oracle query (`st ‖ nonce`, 56 B) with no midstate over the cap.
  - *Circuit.* A `BITS` class `powSpec` (one row per opening) reads lane 2 of each PoW answer as a `(64 − g)`-bit
    field, and `powG` asserts the lane equals it (`pw20`, `powOKR_of`).
  - *Prover.* A multithreaded nonce search, 2^14 expected attempts per level: 12–35 ms per P20 proof with four
    levels [measured], ≈ 15–45 ms with five [e].
- **`C_main` at the Johnson radius, with OOD (J1).** Folds 6/4/4 and rates 1/2, 1/4, 1/8 as before; **230/115/77
  queries** (were 311/191/156). Levels 0 and 1 send an OOD sample after the next cap: a point `z ∈ E^κ`, the answer
  `y` and the intro polynomial; the final weight takes the claim `(λ, eq(z, ·))` before `(λ², W)` (leanVM's
  order).
  - *The list-decoding bound.* `codeFacts_johnson` (`LvmMcaJohnson`) gives each Johnson level's code facts from two
    proved theorems:
    - Haböck's strong mutual correlated agreement at the Johnson radius (`strong_mutual_johnson`): for `2 ≤ k`,
      `0 < η ≤ 1/4`, `ηn ≥ 1` and `(k − 1)·n ≤ (A − 4ηn)²`, fewer than `johnsonThreshold k n (n − A) η` fold
      challenges admit a proximate word that the pair's codewords do not explain;
    - the interleaved Johnson list bound (`card_le_listBound`): within `E = n − A` column errors of a linear code
      of distance `d` (`d = n − k + 1` for RS, `rsCode_minDist`) lie at most `⌊n(d − E)/(nd − 2nE + E²)⌋`
      codewords.
    - The per-level constants (`A`, `L`, `M`, slack `η`) are `norm_num` facts (`LvmWhirCodeJ`); the lists have
      at most 98, 390 and 646 members (level 0: `candidates_main24J_ncard_le`).
    - leanVM's OOD and list-to-one WHIR steps (its `Whir/Sound`, re-ported with OOD in `LvmWhirOod`,
      `LvmWhirEscapeJ`, `LvmWhirProgJ`, `LvmWhirSpecJ`) carry the bound into the opening. With `ood = false` the
      new program is the UD one (`verifyStackedJ_ud`), so the UD refinements stand.
  - *Provenance.* Both theorems are from longfellow-zk's Lean formalisation (`formal/ligero` @ 1c06629, Copyright
    Google LLC, Apache-2.0), as ported to flat modules at Lean 4.34.1 by the Flock entry (`flock-recursive`
    @ 1b74a2a2). They are vendored as `LvmJB*` (30 modules, 7.8 k lines, all in `Solution`'s closure), with module
    and namespace renames only. `LICENSE-longfellow` in this root holds the licence and the change list. Flock's
    `LvmLJ*` lemmas (5 modules) are vendored under the same licence for the list-version extractor, which is not
    used yet.
  - *Soundness accounting.* Per group, before the `2^-14` discount: folds `≤ 2^-130`, OOD points `≤ 2^-170`,
    positions + `λ` + openings 2^-114.30, 2^-114.80 and (final) 2^-115.44; after it **2^-128.30, 2^-128.80,
    2^-129.44**. Lean bounds every group by `εS = 7·2^-131 = 2^-128 − 2^-131` (`whirEps_main24J`), luck by 2^-132
    and the hash by 2^-139: `εFS ≤ 7·2^-131 + 2^-132 + 2^-139 ≤ 2^-128` (`εFS_kcertOfSpec`). The other groups
    pay the union over `C_main`'s candidates (`candPairs_ncard_le`: `L₀ = 98`; `C_rec`'s candidate is unique).
    They stay `≤ 2^-129` because `MidHyp.cons ≤ 2^56` (was 2^60) keeps `98·ξ` small and `C_main` takes at most
    2^40 batched claims.
- **A second WHIR level on `C_rec`, still in unique decoding.** `C_rec` now opens in two UD levels, (fold, rate,
  queries) = (6, 1/4, 170) then (4, 1/8, 139), caps 2^7 and 2^7, final 2^9 `E` scalars (was one level and a 2^13
  final). Level 1 commits one word (`RecCommitsOne`), and `C_main` opens after it (`cfgMain24J 3`).
  - *Soundness.* Level 1's fold is `≤ 2^-166` per challenge, and both query groups are `≤ 2^-115` before the
    discount, `≤ 2^-129` after it (`eQuery_rec20G`, `whirEps_rec20G`). The doom gains `midSpec1` (level 1's
    commitment is far from its code, `MidDoomUd`) and level 1's residual; luck is `LuckB0 ∨ LuckB1` (≤ 2^-132).
  - *Extraction.* `ud_extract2` turns "no doom at either level and no luck" into the unique good word and the
    unique level-1 codeword `V` with `joinMsg (decode V) = foldMsg α₀ q` (`ud_extract_rec20`). `Ex` first decodes
    level 1 (`decodeRec1`, ≈ 2^29.8 steps), then level 0 as before; the fixed cost stays below 2^38 and the fuel is
    unchanged.
- **Shared position-bit tables (EV-DIET).** The circuit decomposes every Merkle position into bits in `BITS`
  tables. They had one class per (opening, answer lane); now each answer lane has one class for all openings,
  which stacks the openings' rows (P20: 107/97/27 outputs on 100/100/32 rows) and sends a spare cell where a
  column is not the row's own output (`LvmQAsmLay`: `posRows`, `posSpec`; `posSpecs_hit` carries the old
  per-opening facts with unchanged statements). `Q_link`'s cells and rows are unchanged. **Table evaluations
  4,299 → 2,851** (BITS 3,005 → 1,571; 4,017 before `C_rec`'s second level), so −34.8 KB of `π` and fewer
  columns for `V`'s `Φ̃` sweep and table sumcheck.
- **Faster native `V` (`VS20G`).** `Solution` ships `subG staticOkB VS20G` (`LvmVFast2`), and `certified` rewrites
  `VS20G_eq : VS20G = VS20F` into `certificateFin`. Three levers: non-uniform group leaves are evaluated once per
  stride class (`nuOf`, `classes_spec`, `grpEvalGN_eq`); table claims share `eq(z, x.take τ)` per table run
  (`SClaim`, `decideProgS_eq`); leaf MLEs with ≥ 9 variables use a 64-entry `eq` table and one `E × K` dot per block
  (`mleF_split`). On roll 4's proofs they save 26 ms per check (242.7 → 216.4 ms, badge median, dev VM). `V` is now
  arithmetic-bound (`FK.mul` 44 % of self time).
- **Prover plumbing (proofs byte-identical).**
  - The recursion tables' static read counts are computed once per program, and each build fills value and count
    columns per piece on ≤ 6 threads (`tables_ext`; the serial pass stays as the `LVM_TABLES_REF=1` oracle).
    The witness phase is 0.06 s shorter per step on the dev VM.
  - `prover setup` picks the worker count (8 or 4) by timing the tape GKR at 2^14 in `tsel` children, requiring
    equal GKR claims, and writes it to `lvm-threads`; each step reads it.
  - The chain walk times two kernels before `ready` and takes relay-echo's (#12) AVX-512VL chain kernel
    (`prover/tools/gen_vlasm.py`, Apache-2.0, vendored; `keccak_vl.rs` generated from it; `LICENSE`) only if it is
    ≥ 3 % faster than leanVM's `keccak_f`. The dev VM picks leanVM's kernel and 8 workers, so these two choices gain
    nothing there by construction; Zen 4 with SMT may choose otherwise.
- **The v4 tier's Keccak GKR is #13's.** On v4 (AVX-512 with GFNI, VBMI and VPCLMULQDQ: the evaluation machine),
  the tape and `KS` GKRs run leanvm-gkr-fast's (#13) re-vendor of gattaca-com/leanVM `pr/all` (MIT/Apache-2.0,
  `src/lv/keccak_gkr_v4/`, #13's per-file headers kept, `src/lv/PATCHES.md`), storing every round as
  leanvm-fast-verify (#15) measured faster on Zen 4. v2 and v4p keep leanVM 0b850750's GKR, and their `.s` is
  unchanged by it. v4's proofs are byte-identical to the other tiers' under Intel SDE (P8 and P20). Under SDE it
  retires 7–19 % fewer instructions per GKR; its time can only be measured on the evaluation machine
  (−0.2 to −0.3 s of P̄ [e]).
- **Re-frozen record:** P20 (21, 1, 16, **2,851**), PUB 127. **|π| 783,192 B** (pr11-9e756ce6880a: 1,094,248,
  −28.4 %), **qS 8,295** (9,916 in pr11-9e756ce6880a; 7,440 with grinding and Johnson `C_main` alone, before `C_rec`'s
  second level), signed file 2,144,991 B. `Q` is 4.89 M words. The table phase has 16 rounds
  (`dk` 12, `D = 28`).
- **Checks.** `lake build RFSubmission` (2,813 jobs); `certified`, `certificateFin`, `kcertS`, `computesX` use
  `propext`, `Classical.choice`, `Quot.sound`; `staticOkB` is true. The Lean `V_S` accepts the shipped prover's
  P20 and P8 streams (steps 1–3) and the linked `.s` prover's P20 stream; tampered proofs are rejected (9 spots
  at P20 and at P8, `KS`, tape, wire, OOD and PoW among them).
- **Measured, local season shape** (dev VM, 8 pinned CPUs, caps unchanged, one run): **ACCEPT**, S =
  **5.24** (P̄ 3.37, V̄ 1.87), S× = **3.49** at the local `v_ref` (1,021 ms); mean `V` **196.9 ms**
  (median 194.6 ms); steps 2.6–8.6 s, step 1 5.6 s; fit `P(n) = 1.78 + 6.83·n/2^20` s; prover
  peak 6.82 GiB; `build_s` 601 s, comparator 509 s (cap 600). Against pr11-9e756ce6880a on the same
  harness: S −16.4 %, S× −11.4 %, mean `V` −71.7 ms (P̄ −9 %; one run each).
- **Expected on the evaluation machine [e]:** pr11-9e756ce6880a's evaluation-to-local ratios (P̄ 0.51, `V` 0.57;
  0.54 from pr11-983bdcfa21d6) give P̄ ≈ 1.72–1.82 s and mean `V` ≈ 0.112 s, so S ≈ 3.51–3.61 and S× ≈ 1.77–1.87 (evaluated:
  4.374 and 1.993).

## Changes in pr11-9e756ce6880a (since pr11-2f57ce79224a)

- **The chain became a digest-only tape.** Only lanes 0–3 of each row's Keccak-f output are committed (v1's `CH`
  committed `in`, `mid` and `Y`); row `i`'s input `Pad43(D[i−1])` is virtual. leanVM's Keccak GKR runs as one
  segment of depth 24, and a 20-round wiring sumcheck with the public kernel `ι(x + 1)·[x + 1 ≤ m]` (evaluated by
  automata over `m`'s bits), a slot reduction and one ring switch tie its input claim to the committed digests.
  `chain_of_tape` gives `chainEnd s n = h`.
- **`C_main` shrank from 2^26 to 2^24 words**, with three WHIR levels instead of four; `|π|` 1,181,488 → 1,094,248 B.
- The prover's fixed part shrank with `C_main`; the recursion-table build starts once `h` is known.
- Local season shape: S = 6.26 (P̄ 3.70, V̄ 2.56), S× = 3.94, mean `V` 268.6 ms; `build_s` 507 s, comparator 464 s.
  Evaluation machine: S = 4.374, S× = 1.993.

## Changes in pr11-2f57ce79224a (since pr11-983bdcfa21d6)

pr11-983bdcfa21d6 was accepted on the evaluation machine: S = 10.17 (P̄ 6.88, V̄ 3.29), S× = 8.19 (mean V 0.288 s,
g 1.19), mean |π| 1,180,192 B. pr11-2f57ce79224a gated the chain link by `n` (the prover's work grows with `n`),
added prover levers (bytes unchanged) and fast verifier twins proved equal to the code they replace (`VS20F_eq`;
505 → 264 ms per check). Local season shape: S = 8.76 (P̄ 6.05, V̄ 2.71), S× = 6.46.

## Idea

### Trust surface: what is proved, and what is checked when V runs

- **The theorem.** `certified : CertificateR declared submission` with `submission = subG staticOkB VS20G`
  (`LvmFinCert.certificateFin`, after `VS20G_eq : VS20G = VS20F`). It uses only the axioms `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorry`, no `native_decide` and no added `axiom`.
- **The claim.** Knowledge error 2^-128, completeness error 0, `qV = 16,384`,
  `fuel t = 2^46 + 8192·t`.
- **Proved in Lean, with no hypothesis left open.**
  - KS of the IOP: leanVM's doom certificates, plus luck, plus the self-fold accumulator (A23).
  - The generic FS compiler from a doom certificate to the library's `KState`, which gives `KS`.
  - The node relation from the tables: chain (`chain_of_tape`), sponge, WOTS, and the child's `acc` through
    `loopir_sound`, `qlink_sound`, `qsig_sound` and `harith_core`/`harith20`.
  - The native `V` refines the compiled IOP verifier (`refines_VSL`, `VS20F_eq`, `VS20G_eq`).
  - The extractor's output and cost (`computesX` at the declared fuel).
  - The Johnson code facts of `C_main`'s levels (`codeFacts_johnson`), from the vendored longfellow-zk theorems
    (`LvmJB*`; `LICENSE-longfellow`).
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
  - The submitted verifier is `if staticOkB then VS20G else reject every 'S' proof`.
  - The certificate case-splits on `staticOkB` without evaluating it. In the `true` branch,
    `staticFacts` gives the facts, and the full proof applies. In the `false` branch, the `S` branch
    accepts nothing, and KS holds trivially (`certificateR_reject`, εFS ≤ 2^-139).
  - **Soundness therefore holds for either value.** Only completeness of the native prover depends on
    `staticOkB = true`. The compiled V evaluates it once per process (1.5 s), and it is `true` at P20:
    every e2e run and badge check accepts.
- **Completeness** is the `W` kind (`P := encode`, error 0). The SNARK prover is tested by the harness,
  not proved complete.
- **Soundness error.**
  - Model: ≈ 2^-128.30. The dominant term is `C_main` level 0's query group (230 positions at the Johnson
    radius, after the 2^-14 PoW discount); the table below has every group.
  - Lean: `εFS = ε + εB + hash ≤ 7·2^-131 + 2^-132 + 2^-139 ≤ 2^-128` (`kcertS`, `εFS_kcertOfSpec`). Inside ε,
    every group is at most `εS = 7·2^-131`: `C_main`'s Johnson groups (`whirEps_main24J`: folds ≤ 2^-130, OOD
    ≤ 2^-170, query groups 2^-128.30, 2^-128.80, 2^-129.44), `C_rec`'s two UD levels with grinding (`whirEps_rec20G`,
    ≤ 2^-129), and every other group at ≤ 2^-129 with the union over `L₀ = 98` candidates.
  - The chain's mask adds no error term: `n` is in the seed query, so every kernel is fixed before any
    challenge, and `V` evaluates `K̃_ch`, the threshold sum and `ι` exactly. Every tape challenge (`r`, lane
    samples, the 24 layers' RMFE points (46/|E|) and rounds, the wiring and slot rounds (2/|E|), the ring
    switch) escapes with ≤ 2^-173 per fresh query after the union over `C_main`'s 98 candidates, far below the
    WHIR query groups.
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

**Stacked WHIR: `C_main` at the Johnson radius, `C_rec` in unique decoding, grinding on both.**
- `C_main`: folds 6/4/4, rates 1/2, 1/4, 1/8, 230/115/77 queries, caps 2^8/2^7/2^7, final 2^10 `E` scalars.
  Levels 0–1 send an OOD sample. The lists have at most 98, 390 and 646 members (`codeFacts_johnson`: the Johnson
  MCA and list bounds of the vendored longfellow-zk proofs; `L₀ = 98` is level 0's). `C_main` is never decoded, so its lists cost `Ex`
  nothing.
- `C_rec`: two UD levels (radius `(1 − ρ)/2`, list size 1): fold 6, rate 1/4, 170 queries; then fold 4, rate
  1/8, 139 queries; caps 2^7/2^7, final 2^9 `E` scalars in the clear.
- Every level grinds 14 bits: a separator sample, a nonce, a PoW challenge whose lane 2 is `< 2^50`, then the
  positions. The nonce opens the level's query group, which the FS compiler charges once (`2^-14·eQuery`).

UD on `C_rec` is what makes the extractor cheap. `Ex` first decodes level 1's committed word to the level-0 fold
message `f₁` (`decodeRec1`, ≈ 2^29.8 steps; one level earlier `f₁` was the final, read from `π`). Then it folds
`C_rec`'s word, finds the agreement set against `Enc(f₁)`, interpolates the 64 rows on 2^13 agreeing positions
(barycentric, with shared weights) and back-substitutes into the novel basis. The fixed cost is ≈ 2^37.97 steps,
under `fuel_base = 2^46`. The proximity side is a new UD mutual-correlated-agreement lemma (Berlekamp–Welch
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
  (24 layers) and wiring, `KS`'s GKR and link, two ring switches, every claim, and both WHIR openings with
  their OOD and PoW checks.

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
specified `VS20` (`VS20F_eq`). The shipped `VS20G` (`LvmVFast2`) evaluates group leaves once per stride class,
shares `eq` per table run and blocks leaf MLEs, and is proved equal to `VS20F` (`VS20G_eq`).

### What came from where

| | kept | cut | changed |
|---|---|---|---|
| leanVM protocol | `K`, `E`; Keccak GKR with RMFE; `g`-power bus, grand product, table sumcheck; ring switching; stacked WHIR with OOD (Johnson radius on `C_main`) | ISA and VM guest; leanXMSS/leanSPHINCS; LeanDA; RPM/duplex and `romSound`; GS list decoding and its cost machine | UD on `C_rec`; grinding inside the query group (nonce `read`, PoW challenge); hash-chain FS; Merkle through the oracle with caps; two commitments; LoopIR; digest-only chain tape with a wiring sumcheck; accumulator |
| leanVM `formal/` (4.35) | DSL, `Cert`, doom rules; Keccak GKR, sumcheck, grand product, bus, spine, ring switching; WHIR (≈ 120 modules / 31 k lines, ported to 4.34.1), now with its OOD and Johnson path | VCVio, ArkLib, Clean, leanISA, `Extraction`, `Cost`, `Guest` | `LevelCode` with a UD threshold (`C_rec`, `listMax = 1`) or Johnson constants (`C_main`); the MCA input from longfellow's proofs |
| longfellow-zk `formal/ligero` (Apache-2.0, via the Flock entry's flat port) | the Johnson list bound, Haböck's strong MCA (`LvmJB*`, 30 modules / 7.8 k lines) | — | module and namespace names only (`LICENSE-longfellow`) |
| leanVM Rust | `primitives`, `parallel`, `fiat_shamir`, `pcs`, `keccak_gkr`, `leanvm_core` (gkr, leaf, constraints), std-only | `rand`, `tracing`, jemalloc | transcript, Merkle, WHIR config, portable clmul tiers, a layers-only GKR entry point (`prover/src/lv/PATCHES.md`) |
| leanvm-gkr-fast (#13), leanvm-fast-verify (#15) | v4 tier only: #13's re-vendor of gattaca-com/leanVM `pr/all`'s Keccak GKR (MIT/Apache-2.0, `src/lv/keccak_gkr_v4/`), with #15's every-round storage | #13's `pcs`/`primitives`/`hash` changes; #15's Lean (its `V` levers were already in) | `generate_uncommitted` rewritten for the tape's extents; our `of_inputs_padded`, `prove_tape` added; `every` = 1 (`PATCHES.md`, "lvm2 PORT-13") |
| relay-echo (#12) | the AVX-512VL chain kernel generator `gen_vlasm.py` (Apache-2.0, unmodified; `LICENSE`) | its C and Lean | emitted as Rust `asm!` (`gen_chain_vl.py`, `keccak_vl.rs`), chosen at run time |
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
| pr11-9e756ce6880a, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 6.26 (P̄ 3.70, V̄ 2.56), S× = 3.94, mean V 0.269 s; `build_s` 507 s, comparator 464 s |
| pr11-9e756ce6880a, evaluation machine | ACCEPT; S = 4.374 (P̄ 1.892, V̄ 2.482), S× = 1.993 (mean V 0.152 s, g 1.053) |
| grinding + Johnson `C_main` only (not submitted), local season shape | ACCEPT; S = 5.85 (P̄ 3.63, V̄ 2.22), S× = 3.83, mean V 0.247 s; `build_s` 588 s, comparator 490 s |
| this version, local season shape (dev VM, 8 CPUs) | ACCEPT; S = 5.24 (P̄ 3.37, V̄ 1.87), S× = 3.49, mean V 0.197 s; `build_s` 601 s, comparator 509 s (cap 600); axioms `propext`, `Classical.choice`, `Quot.sound` |
| this version, evaluation machine | from this PR's evaluation (projected S ≈ 3.5–3.6, S× ≈ 1.8–1.9) |
| `prover setup` variant on Zen 4 | v4 expected (cpuid); the dev VM runs v4p |

**Frozen P20 record** (busDepth, leafdec, rounds, evals) = (21, 1, 16, 2,851); PUB is table 127.

| quantity | value |
|---|---|
| `|π|` | **783,192 B** |
| `qS` | **8,295** (`qV` 16,384) |
| trace | ≈ 169.6 k lanes (Σ 1,357,007 B, `LvmPlanP20`; 0.61 of `C_rec`'s capacity) |
| signed file | 2,144,991 B (cap 64 MiB) |
| tables | 2,851 evaluations (BITS 1,571, groups 1,142), ≈ 5.8 M committed words (`C_main`'s free region is 9.44 M) |
| `Q` words | 4.89 M |

**Prover, dev VM.** QEMU, 8 threads, shared host. Its cpuid hides PCLMULQDQ, but the instruction executes;
VPCLMULQDQ and GFNI do not, so the evaluation variant v4 cannot start there. The runs use the dev variant
v4p (AVX-512 + PCLMUL) and the shipped binary with the embedded program blob. The P8 and P20 streams
(1–3 steps; children with n = 1, 200,000 and 2^20 at P20, 1, 511 and 512 at P8) are accepted by the Lean `V_S`,
and tampered ones (n ± 1, a byte of the tape's `r`, its scalars, its lane-challenge message and its GKR, the wire's
messages, `KS`'s `r`, the OOD answers and intro scalars, the PoW lanes) are rejected. Sparse and dense (`LVM_PGATE=dense`) proofs are byte-identical.
- Local season shape: step 1 **5.6 s**; later steps **2.6–8.6 s**; a fit over the stream gives
  `P(n) ≈ 1.78 + 6.83·n/2^20` s (pr11-9e756ce6880a: 2.04 + 7.06; pr11-2f57ce79224a: 4.3 + 7.6). On the evaluation
  machine pr11-9e756ce6880a's fit was 1.04 + 3.78·n/2^20 s (its attested result).
- Peak RSS: **6.82 GiB** (cap 11).
- The nonce search takes 12–35 ms per proof with four levels (measured before `C_rec`'s second level), ≈ 15–45 ms
  with five [e].
- The fixed part (≈ 1.8 s) is mostly the 2^24 commitment (bound by the oracle's Merkle hashing), `KS`'s GKR, the
  bus and tables, and the opening. The tape's GKR is ≈ 0.23 s + 8.6 s per 2^20 rows, the same as v1's depth
  12 × 2 segments.
- Zen 4 [e]: the GFNI/VPCLMULQDQ tiers make the GKR 2–3× faster.

**Verifier**, measured on the dev VM (one core):
- **196.9 ms per check** (harness mean, local season shape; median 194.6, p10 184.4, p90 210.9 ms).
  pr11-9e756ce6880a: 268.6 ms (evaluation machine: 152 ms); pr11-2f57ce79224a: 275.5 ms; pr11-983bdcfa21d6: 506 ms.
- Same-session A/B of the badge's `check` (CPU 8, timing lock, 24 checks a side): 235.0 → 187.5 ms median against
  the grinding + Johnson version (−20 %): `|π|`, EV-DIET's evaluations and `VS20G`.
- Start-up is not charged; it is 10.7–11.4 s per process on the loaded dev VM (`staticOkB`, shared table parts,
  caches).

**Score.** On the evaluation machine pr11-983bdcfa21d6 scored S = 10.17 and S× = 8.19, pr11-9e756ce6880a
S = 4.374 and S× = 1.993, against #7's S = 105.9 and S× = 505.8.

**Error budget (model, P20, per fresh query, log₂).** The groups outside WHIR carry the union over `C_main`'s
98 candidates (+6.6); the WHIR query groups include the 2^-14 PoW discount.

| group | bound |
|---|---|
| sumcheck rounds (GKR pack and position, tables, wiring, slots) / Keccak GKR step 2 (degree 46) | −183.8 / −179.9 |
| bus fingerprint and grand product / ring switching per challenge | −163.4 / −185.4 |
| stacked-claim batching (`(J − 1)·98/\|E\|`) | −173.4 |
| WHIR folds (main 0–2 / rec 0–1) | ≤ −130 each / −160.4, ≤ −166 |
| WHIR OOD points (main 0–1) | ≤ −170 |
| WHIR query groups: positions, `λ`, openings (main 0–2, rec 0–1) | −128.30, −128.80, −129.44, ≤ −129 each |
| union over every Keccak, wiring and slot challenge | −173.2 |
| accumulator `κ_j` / `t` | −185.4 / −180.6 |
| extractor luck (`C_rec`, unique, both levels) / hash | −173.7 / −151.4 |
| **worst + luck + hash** | **−128.30** (Lean: `εFS ≤ 2^-128` with every group `≤ 7·2^-131`) |

**Extractor.** `fuel = 2^46 + 8192·t`; the decode's fixed cost (both `C_rec` levels, ≤ 2^38 steps) is 2^8 below
`fuel_base`.

**Lean.** 567 flat modules, ≈ 166 k lines; `Solution`'s import closure holds 524 of them (2,769 build jobs in the
harness), of which 30 are the vendored `LvmJB*`. In v1, comparator time was cut from 705 s to 462 s on the dev VM by proof-only changes
(`rfl`-lemma `simp` replays, one-pass checkers).

## What failed, and why

- **leanVM's extractor.**
  - Guruswami–Sudan list decoding has a proved cost of ≤ 2^81 + …, and its cone is 443 modules /
    133 k lines.
  - Even at multiplicity 1 (Berlekamp–Welch), 64 lanes × 2^55 = 2^61 is about 2^12 over the
    `2^48 + 2^16·t` cap.
  - Hence UD on `C_rec`, the commitment `Ex` decodes. `C_main`, never decoded, moved to the Johnson radius with
    grinding (|π| −16 %; −28.4 % with `C_rec`'s second level and the shared position tables).
  - ArkLib's Johnson MCA closure (300 modules / 80 k lines) is off the import allowlist anyway; the vendored
    longfellow-zk proofs need only Mathlib.
- **Johnson on `C_rec` (J2′) in this version.** The prover, `V`, circuit and refinement side of a two-level
  Johnson `C_rec` (levels (6, 2, 115), (4, 3, 77), one OOD sample) built, and would give |π| ≈ 707 KB with the
  shared position tables [e; 741,592 B measured without them]. The certificate did not: the relativised doom that
  the list extractor needs ("the transcript ends in a fold of a good candidate") holds on honest runs, and a KCert's
  doom must never hold on an accepting run. So it enters the doom only with an empty good set, where it gives the
  extractor nothing. Extraction once a good pair exists needs per-pair front-end soundness, and two relativised
  terms (`C_rec` level 0's positions group, 2^-128.75, and its MCA term, 2^-130.0 per fold round) exceed the luck
  budget of 2^-132 per group. `C_rec` stays in UD; J2′'s modules (`LvmWhirParamsJp`, `LvmWhirGoodJp`,
  `LvmWhirDoomJ2`) are in `lean/` outside the closure.
- **The second `C_rec` level alone cost `V` time.** It saves 97.8 KB of `π`, but each opening had its own
  position-bit classes, so it added 358 BITS evaluations and +12.5 ms per check (`Φ̃` sweep, table sumcheck, bus
  final). Sharing the classes across openings (EV-DIET) removed that: 4,299 → 2,851 evaluations.
- **`KS` at 2^14 rows.** Its GKR, output claim and link save 0.113 s per step on the dev VM [measured], under the
  0.12 s that would pay for re-freezing the layout, and ≈ 0.04–0.06 s on Zen 4 [e].
- **relay-echo's chain kernel on the dev VM.** 422–507 ns per chain step against leanVM's `keccak_f` loop at
  293–298 (2^20 steps, one CPU), so the run-time choice keeps leanVM's kernel there; it is shipped because Zen 4
  may rank them the other way.
- **Johnson from BCIKS20's bound.** Its Johnson-radius theorem gives correlated agreement, not the mutual form
  WHIR needs, and is a `sorry` in ArkLib at our pin. With its size, `C_main`'s level 0 would need 297 queries,
  more than UD's [model].
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
2. **`C_rec` at the Johnson radius (J2′).** Everything but the certificate is built (What failed). Two routes:
   a pinned doom in the style of the Flock entry's `LvmLJPin`/`LvmLJInterleave` (vendored here, outside the
   closure; 2–4 k lines [e]), or a KCert whose final condition is "accept in doom ⇒ extractable" (1–2 k lines plus
   re-proving its users [e]). Expected |π| ≈ 707 KB [e].
3. **Exact-budget query counts and larger caps.** `C_rec`'s count still meets `≤ 2^-129`; the exact budget
   (`εS = 7·2^-131`) would save a query or two there, and larger caps trade cap bytes for path bytes. Caps are part
   of the certificate's level configurations, so this reopens their facts.
4. **`V`.** It is now arithmetic-bound. The GKR layers' weight vector kept symbolic (θρπ-transposes of a rank-1
   tensor) until the final claim: −15–20 ms [e], or −5–10 ms with array plumbing only. `C_main`'s WHIR claim
   weights (29 ms). Fewer evaluations: closed-form address columns (≈ −480) and merged small groups (≈ −330) [e].
5. **Prover speed.** The `C_main` commit is bound by the oracle's Merkle hashing (≈ 3.7 of its 4.8 CPU-s at 2^17); a
   wider leaf or node would cut it. The FS-ordered per-layer work of the GKRs is ≈ 2 ms per layer, ≈ 0.15–0.2 s per tape.
   The recursion-table build's serial BITS fixpoint (2 × ≈ 0.03 s) could recompute only the rows that depend on
   BITS outputs. #13's `every` = 2 at 8 threads is untested here.
6. **Fewer guarded facts.** A structural, kernel-friendly table builder would let the kernel decide `wf`,
   grouping and claim well-formedness. That would remove `staticOkB` and 1.5 s of start-up.
7. **Left unapplied.**
   - drop v1's dead chain-table and shift-link modules from the closure (build and kernel time);
   - `Q_link`'s node-half selection as one degree-2 assertion (−0.35 M);
   - `C_rec`'s zero columns as free table space;
   - a Rust test verifier;
   - the extractor's serial build chain.
