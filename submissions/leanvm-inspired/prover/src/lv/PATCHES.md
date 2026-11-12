# Edits to the vendored leanVM code (leanVM 0b850750)

`tools/vendor.py` copies `crates/{primitives,parallel,fiat_shamir,pcs,keccak_gkr}/src` here and rewrites
paths only (`crate::` -> `crate::lv::<crate>::`, `<crate>::` -> `crate::lv::<crate>::`, `tracing::` -> the
shim). Not copied: `primitives/test_rng.rs` (rand), `keccak_gkr/{batch_bench,tests}.rs`, `pcs/ntt/tests.rs`.
Re-run it into an empty directory and `diff -r` against this one to see exactly the edits below.

| file | edit | why (BLUEPRINT) |
|---|---|---|
| `mod.rs`, `tracing.rs` | new: module root; `info_span!` shim (a named timer under `LVM_PROF=1`) | std-only (§8) |
| `fiat_shamir/transcript.rs` | `ProverState` replaced, leanVM's API kept: hash chain over the oracle (`q₀`, seed, `st‖msg`, positions `st`), length rule, body in schedule order, verifier trace, `hint_merkle` walks each path through the oracle and checks its cap node; `grind` accepts 0 only | §2.2, D6, D12 |
| `fiat_shamir/merkle.rs` | `open` takes `cap_log`: paths stop below the cap | §2.2 (caps) |
| `pcs/merkle.rs` | leaf and node hashes through the oracle (`oracle::hash_padded`, `oracle::hash_items`); `CutTree::cap`; `open` takes `cap_log`; leanVM's local leaf hasher kept as `hash_local` (unused) | §2.2, §8 |
| `pcs/whir.rs` | `Commitment { cap }`; `commit` and `ligero_commit_ext` take the cap; `add_root` -> `add_cap`; `hint_merkle(paths, cap)`; positions by `ProverState::sample_positions` (8 per query) instead of `⌊192/d⌋` per squeeze | §2.2, §3.1 |
| `pcs/whir_config.rs` | `ProverConfig::cap_logs`; `ud_config` (fold 6 then 4, `R_i = i + 1`, `t = ⌈129/−log₂((1+2^-R)/2)⌉`, final ≤ 2^8, no OOD, no grinding, caps 2^8/2^7) | §3.1 |
| `parallel/topology.rs` | default pool = every logical CPU (leanVM: one per physical core, 4 on the 4C/8T VM); `LEANVM_NUM_THREADS` still overrides | §8 (threads: 8) |
| `primitives/field/gf2_64.rs` | `software::clmul_fast`: run-time tiers pclmulqdq / AVX-512F byte comb / integer holes, for `mul_wide`'s portable path (`software::clmul`, the bit loop, stays the reference) | §8 (portable K product) |
| `primitives/field/gf2_64x3.rs` | the portable `F192` product uses `clmul_fast` | same |


WP-15a (the `S` proof on the Lean schedule, `src/lvm/`):

| file | edit | why |
|---|---|---|
| `fiat_shamir/transcript.rs` | caps wait like scalars until the next FS query; `sample` and the first positions query absorb `st ‖ pending`; no 19+1 split, no chunking (the length rule is the schedule's, `LvmSchedule.lengthRule`); `hint_merkle` asserts nothing is pending | the Lean driver (`LvmDriver.fsQuery`, `posLoop`, `openLoop`) |
| `pcs/whir.rs` | `recursive_prover_with_prepared_basis` takes `level_steps = 0`: the folded message in the clear after the L0 lane folds, then L0 positions, λ, openings, intro, tail rounds | `C_rec`, one level (BLUEPRINT §3.1, D7; Lean `levelI`) |
| `pcs/whir_config.rs` | `config_of_levels` (the record's folds, rates, caps, queries) | `C_main` and `C_rec` of `P20`/`P8` |
| `pcs/stack_open.rs`, `stack_open/basis.rs` | `open_mixed_whir_stacked`: claims in the verifier's order, one `λ`, ring claims each with its own block offset and its own map (sampled in its phase); `initial_basis` takes per-ring offsets | Lean `verifyStackedOpening`, `ringSwitch` |
| `pcs/ring_switch.rs` | `COMPOSITION_SHIFTS_LEN` exported | the per-claim maps |
| `pcs/merkle.rs` | the builder hashes leaves per block and every level above in `finish`, a whole level per batch over the threads (leaf digests of a cut tree kept until then) | "leaves then whole levels" (BLUEPRINT §8): ≈ 7.7× fewer oracle requests at `P20` |

Nothing else changed: the GKR (`keccak_gkr`), ring switching, stacked opening, NTT, sumcheck and field
kernels are leanVM's as written, selected at compile time per CPU variant (`build-asm.sh`).


WP-15b (the recursion tables: `leanvm_core/{gkr,leaf,constraints,transcript}.rs` vendored with `tools/vendor.py`'s path
rewrites; `leanvm_core/mod.rs` is new: `SECURITY_BITS`, `PAR_THRESHOLD`, `stage!`, `log2_*`, `witness::stack_offsets`
copied from leanVM's `lib.rs`/`witness.rs`):

| file | edit | why |
|---|---|---|
| `leanvm_core/constraints.rs` | `Air::sent`: only the first `sent` columns' evaluations are sent (leanVM: all) | an option for LoopIR fixed columns; **in use: all columns are sent** (`m3::SEND_FIXED = true`, which WP-9's `nativeTable`/`tableCheckR` expect); change only together with WP-9's V_S decision |

lvm2 P-GATE / S1-P (FA-2 stage S1, shipped since S1-P):

| file | edit | why |
|---|---|---|
| `keccak_gkr/mod.rs` | `OutputClaim::of_inputs_padded`: `of_inputs` with the padding rows' sum in closed form, `Keccak-f(0)·(1 − Σ_{i<len} eq(r, i))` | the same claim at work linear in the written rows; the default (`LVM_PGATE=dense` uses `of_inputs`) |

lvm2 T-P1 (S2, BLUEPRINT2 §2.2):

| file | edit | why |
|---|---|---|
| `keccak_gkr/witness.rs` | `Witness::generate_uncommitted`: `generate` without the committed column | the tape's inputs are virtual |
| `keccak_gkr/mod.rs` | `Witness::prove_tape`: lane samples, `depth` layers, the input claim returned (no output or input opening, no extra scalars); `pub use protocol::Claim` | the layers-only entry point the tape needs |

lvm2 PI-GRIND-P (grinding before each WHIR level's positions, `docs/lvm2/stages/PI-GRIND.md` Gate §2):

| file | edit | why |
|---|---|---|
| `fiat_shamir/transcript.rs` | `grind(g)`: `g = 0` as before (nothing); `g > 0`: a separating `sample` (`st ‖ pending`, discarded), the smallest nonce `(counter, 0, 0)` whose query `st ‖ nonce` answers with lane 2 `< 2^(64−g)` (searched in rounds over the oracle connections, class `Grind`, not in the trace), the nonce sent as one scalar, then the PoW `sample`; leanVM's check (low bits of limb 0 after absorbing the nonce) is not used | the PoW bits lie inside the challenge `E` (Gate §2a); one 56-byte query per attempt (§2b) |
| `pcs/whir.rs` | `C_rec`'s one-level path (`level_steps = 0`) calls `grind` after the final scalars, as the multi-level path does at every level | every level of both openings grinds |
| `pcs/whir_config.rs` | `config_of_levels(levels, grind)`: `grinding_bits = grind` at every level | the record's `grind` |

lvm2 JB-VQP J1 (`C_main` at the Johnson radius, `docs/lvm2/stages/JB-L.md` §3):

| file | edit | why |
|---|---|---|
| `pcs/whir_config.rs` | `config_of_levels(levels, grind, ood)`: with `ood`, `ood_samples = [0, 1, …, 1]` (leanVM's `send_ood` unchanged: after the next cap, `κ` samples, `y`, the intro's `(u_0, u_2)`; glued at `λ¹` before the queries' batch) | `C_main`'s `whirLevelsJ`; `C_rec` passes `false` |
| `pcs/whir.rs` | `final_claim_holds`: after the tail rounds, assert running claim = `f(r)·w(r)` (prover-only check, no byte changes) | the J1 self-check: a wrong OOD value or intro would break the batched sumcheck |


lvm2 PORT-13 (the v4 tier's GKR: leanvm-gkr-fast, PR #13, and leanvm-fast-verify, PR #15):

`keccak_gkr_v4/` is #13's `src/lv/keccak_gkr/` (09c572ca) byte for byte, then the edits below. #13 re-vendored it with
`tools/vendor.py` from leanVM `0b850750` plus `git diff 04fba039b edd857be9` of the crate, the
[gattaca-com/leanVM `pr/all`](https://github.com/gattaca-com/leanVM/tree/pr/all) branch (`04fba039b` is where `pr/all`
forked; MIT OR Apache-2.0); each file's first line says so. The `pr/all` commits in the crate are prover-only (their
messages state the proofs are unchanged); its new kernels are gated on `avx512vbmi` + `gfni`, and its fallback is 2.0×
slower than `0b850750`'s on AVX-512 + PCLMUL (`docs/lvm2/stages/PORT-13-15.md` §2). So `mod.rs` mounts
`keccak_gkr_v4/` as `keccak_gkr` only where `avx512f`, `avx512vbmi`, `gfni` and `vpclmulqdq` are compiled in (the v4
`.s`); v2 and v4p keep `keccak_gkr/` (`0b850750`). Both copies take the same callers and give the same proof bytes.
`primitives`, `parallel`, `fiat_shamir` and `pcs` stay `0b850750`'s: `pr/all`'s GKR compiles against them unchanged
(its other changes to those crates are additive or commit-side, not ported).

| file | edit | why |
|---|---|---|
| `mod.rs` | `keccak_gkr` from `keccak_gkr/` or, under the v4 features, `#[path = "keccak_gkr_v4/mod.rs"]` | v4 only |
| `keccak_gkr_v4/witness.rs` | `every(_) = 1`: every round stored (#15's value; `pr/all`: 4 at ≥ 8 threads, else 2) | #15 measured it faster on Zen 4 at 4C/8T; the memory is the 0b850750 copy's |
| `keccak_gkr_v4/witness.rs` | `Witness::generate_uncommitted` (T-P1's, above), rewritten for `pr/all`'s `Extent::new(first, blocks, depth)` and `slots()`, as `from_committed` runs its blocks | the tape |
| `keccak_gkr_v4/mod.rs` | `OutputClaim::of_inputs_padded` (P-GATE's) and `Witness::prove_tape` (T-P1's), copied unchanged; `pub use protocol::Claim` | the tape and the KS output claim |
