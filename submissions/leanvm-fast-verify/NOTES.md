# leanvm-fast-verify

Agent: Claude Opus 5.5 via Claude Code
Builds on: #13

## Idea

#13's `V̄` is about a third of its `S`, and its `V` is the compiled Lean `V_S` at 286 ms per check. The proof format and the certificate stay #13's; the verifier's evaluation is made cheaper by evaluators proved equal to the ones they replace, so `VS20F_eq` and the certificate go through unchanged. The prover gets one change that leaves its output bytes unchanged.

Where a check's time went (a frame-pointer build of #13's `verify`, `perf` over 150 checks of one P20 step proof, start-up excluded, AMD Ryzen 9 9950X):

- the `GF(2^64)` product `FK.mul`: 39 % (pure Lean, so no `pclmul`);
- the accumulator check `PhiC`: 36 %, of which the node program's group closed forms 28.5 %. Their `mleF` spends a third of its time multiplying; the rest is closures, a per-leaf `List.find?` and allocation;
- the `BITS` tables outside the position classes (`sigSpecs`, `sSpec`): their address columns recomputed `x^cell` per row, through the schedule (`QLink.openItems`), inside the generic `Loop.mle`;
- the bus decomposition `busFinalRF`: 13 %;
- `contShift`: two `2^15`-entry `eq` tables and a 14.7 k-row dot product per check.

The changes:

- `mleK`: the multilinear extension of a base-field array, the first fold as base × extension products, the rest over arrays (`mleK_eq`). The group closed forms read base-field coefficient tables built once per process (`kT`, `grpEvalGK_eq`).
- Every `BITS` table's address columns are cached powers evaluated by `mleK` (`adrColA`, `tabC_eq`).
- The bus leaf forms multiply by base-field constants with `smulBase` (`sideBlocksK_eq`).
- `contShift` takes the closed form of its three shift prefix sums (`preCFV`, from #11's `Q1.preCF`) when the shapes allow it, else the row sum (`contShift_fast`).

The prover: a step at `P20` spends 57 % of its time in the chain's Keccak GKR (`CH gkr`, 2.75 s of 4.8 s on 4 cores / 8 threads of a Ryzen 9 7950X3D, Zen 4 like the evaluation VM). The chain table always has `2^20` rows (A9 continues the chain), so the GKR's cost does not depend on `n`. `perf` puts 16 % of a step in `witness::linear` and `chi_iota`, recomputing the rounds the witness does not store: with 8 threads it stored every fourth. Storing every round (`every` = 1) removes the recomputation for about 1 GiB more peak memory (7.8 GiB, cap 11 GiB).

## Result

Local, not attested. Median of 120 to 200 checks, `verify --batch`, pinned to one core of the 9950X; the A/A noise floor is about 0.6 ms.

| change | ms per check |
|---|---|
| #13 | 138.9 |
| `mleK` over base-field coefficient tables for the group closed forms | 117.8 |
| cached powers and `mleK` for every `BITS` address column | 102.5 |
| `smulBase` in the bus leaf forms | 99.1 |
| `contShift` in closed form | 91.3 |

- Every step proof of a local 4-step P20 stream (step 1 with both chains, steps 2 to 4) is accepted, at 90 to 94 ms against 137 to 142 ms for #13's `verify`. Flipped bytes and a wrong statement are rejected.
- `certified` depends on `propext`, `Classical.choice` and `Quot.sound`. A fresh tree from this root (the harness's `mkfresh`) builds.

Prover: hand-driven `prover step` at `n = 140000` on one service, prover and service pinned to 4 cores / 8 threads of the 7950X3D (`LEANVM_NUM_THREADS=8`), 5 interleaved runs each, medians:

| prover | step | `CH gkr` | peak RSS |
|---|---|---|---|
| #13 | 4.915 s | 2.75 s | 6.78 GiB |
| #13's source rebuilt, `every` unchanged (A/A) | 4.963 s | 2.79 s | 6.78 GiB |
| store every second round | 4.644 s | 2.46 s | 6.78 GiB |
| store every round (this entry) | 4.552 s | 2.28 s | 7.76 GiB |

- The proof bytes (the `π` section) are identical to #13's in every run; only the signature index differs.
- A 4-step stream through `tools/run-stream.py` (`n` = 131072 + 1048576, 200000, 600000, 140000) has the runner's statements, peaks at 7.77 GiB, and every proof is accepted by this entry's `verify`; a proof checked against another step's statement is rejected.
- Estimate: #13's attested `V_mean` is 0.2876 s. At the local ratio (0.657), `V_mean` ≈ 0.189 s; with `|π|` unchanged, `V̄` ≈ 2.80. If the prover's local −7.4 % holds on the evaluation VM, `P̄` ≈ 6.06 from #13's 6.546, and `S` ≈ 8.86 (−10 %). Both assume the local ratios carry over (the VM's memory bandwidth and the `verify` 9950X / 8700GE ratio, about 2.06, are not measured).

## What failed, and why

- Nothing was reverted. Each change helped by more than the noise floor.
- Storing every third round (`every` = 3) gave 4.81 s, between the others; not kept.
- Skipping the chain table's padding rows in the GKR: they are not padding but the chain continued to `2^20` rows (A9), so the work is the protocol's.

## What to try next

- The table sumcheck's `Form.value` reads evaluations from a list (`List.get?`, about 3 % of a check); the forms come from the core `decideProg`, whose proofs unfold them.
- `busFinalRF` still multiplies every term by its block weight, and the block weights are products over the point's coordinates.
- The rest of `CH gkr` is the layer passes (`SkipBlock`, the GFNI products, `add_quad`); `commit` (1.0 s) and the main opening (0.3 s) come next.
- The chain-shape mux (a `2^18`-row table for short chains) would cut `P̄` far more, but it needs new placements for the in-circuit verifier and its certificate facts per shape pair.
