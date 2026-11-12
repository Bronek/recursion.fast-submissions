-- Ported from leanVM `formal/Statement/LeanVmVerifier.lean` (formal rev 40f877dc), Part 1 (lines 27-162), as `LvmVParams` for lvm (WP-2).
import LvmFields

/-!
# The WHIR parameters of leanVM's verifier (Part 1 of `Statement/LeanVmVerifier.lean`)

Split out of the verifier transcription: the level ladder and the query table of the deployed
(Johnson-regime) WHIR. lvm's unique-decoding parameters replace `queryTable` (WP-7); `Level` and
`ladder` are what the WHIR soundness modules read.
-/

section

/-! # Part 1: the constants

### The WHIR parameters

The constants are transcribed from `crates/pcs/src/whir_config.rs:38-86`, the ladder geometry from
its `derive_ladder` and `derive_ladder_shape` (`:252-301`), the stacking window from
`crates/leanvm_core/src/pcs.rs:49-51`, and the query counts from the Rust verifier's
`WHIR_QUERIES` and `derive_config` (`crates/verifier/src/whir.rs:10-63`), which carry them
verbatim. The specification describes the protocol these
parameters instantiate (Annex B, Protocol B.1, `doc/leanvm/body/b-polynomial-commitment-scheme.tex`)
and gives no numbers.

An opening of a stack of `2^μ` elements of `K` at rate `2^-R` runs a *ladder* of levels. Level 0
folds `initialFold = 6` variables; every later level folds `subsequentFold = 4`, or what remains,
until at most `residualMaxLog = 5` variables remain, which are sent in the clear. The rate
exponent of a level is the previous one plus the previous fold minus a domain reduction,
`initialReduction = 3` after level 0 and `subsequentReduction = 1` after every later level. Each
level opens `queries` positions after `queryGrindingBits = 17` bits of grinding; from level 1 on,
one out-of-domain sample binds the level's commitment (`whir_config.rs:106-114`;
`whir.rs:177-185`).

The query counts are the Rust's *output*, not its derivation: `optimize_johnson_level`
(`whir_config.rs:602-670`) minimises the queries of each level subject to the 128-bit
round-by-round targets of Annex B's Theorem B.2 under a floating-point MCA formula
(`paper_thm_ca_johnson_log_a`, `whir_config.rs:429-442`), and this module does not restate that
search. The table is the Rust verifier's `WHIR_QUERIES` (`whir.rs:17-23`), indexed by rate
exponent `1..4` and stack size `15..28`; outside that window `ladder` is `none`, as the verifier
rejects (`whir_queries`, `whir.rs:31-38`; the prover's `validate_log_inv_rate`,
`whir_config.rs:48-55`). `ladder` takes the stack size `μ`, as the verifier's `derive_config`
does (the PCS crate's API takes `m = μ + LOG_PACKING`, `crates/pcs/src/pack.rs:5`), and the rate
exponent is announced with the sizes.
-/

namespace LeanVM.Parameters.Whir

/-- Variables folded at level 0: the lane fold (`INITIAL_FOLDING_FACTOR`, `whir_config.rs:67`). -/
def initialFold : ℕ := 6

/-- Variables folded at every later level (`SUBSEQUENT_FOLDING_FACTOR`, `whir_config.rs:68`). -/
def subsequentFold : ℕ := 4

/-- Bits the Reed-Solomon domain shrinks by after level 0, so that the rate exponent rises by
`initialFold - initialReduction` (`RS_DOMAIN_INITIAL_REDUCTION_FACTOR`, `whir_config.rs:73`). -/
def initialReduction : ℕ := 3

/-- Bits the domain shrinks by after every later level (`RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR`,
`whir_config.rs:78`). -/
def subsequentReduction : ℕ := 1

/-- Folding stops once at most this many variables remain; the residual multilinear is sent in
the clear (`RESIDUAL_MAX_LOG`, `whir_config.rs:86`). -/
def residualMaxLog : ℕ := 5

/-- Grinding bits before each level's query positions are sampled (`QUERY_GRINDING_BITS`,
`whir_config.rs:60`). -/
def queryGrindingBits : ℕ := 17

/-- The smallest stack the PCS commits, a smaller witness padded up to it: `MIN_MU`
(`pcs.rs:49`; `MIN_STACKED_LOG`, `crates/verifier/src/layout.rs:87`). -/
def minLogStack : ℕ := 15

/-- The largest stack the PCS commits: `MAX_MU` (`pcs.rs:51`; `MAX_STACKED_LOG`,
`layout.rs:88`). -/
def maxLogStack : ℕ := 28

/-- One level of an opening: the number of sumcheck rounds it folds (`ℓ_i`), the rate exponent
of the code its commitment is in (`R_i`), and the number of positions queried (`t_i`), in the
notation of Annex B. -/
structure Level where
  /-- `ℓ_i`: the sumcheck rounds it folds. -/
  fold : ℕ
  /-- `R_i`: the rate exponent of its commitment's code. -/
  logInvRate : ℕ
  /-- `t_i`: the positions queried. -/
  queries : ℕ
  deriving DecidableEq

/-- The levels after the first, as pairs (fold, rate exponent): while more than `residualMaxLog`
variables remain, fold `subsequentFold` of them (or all that remain) at the rate exponent the
previous level's fold and the pending domain reduction give (`derive_ladder`,
`whir_config.rs:252-286`, with `derive_ladder_shape`'s rate rule, `:292-301`). `fuel` bounds the
recursion; every level folds at least one variable, so `remaining` fuel is enough. -/
def levelsFrom : (fuel remaining prevFold prevRate reduction : ℕ) → List (ℕ × ℕ)
  | 0, _, _, _, _ => []
  | fuel + 1, remaining, prevFold, prevRate, reduction =>
    if remaining ≤ residualMaxLog then []
    else
      let rate := prevRate + prevFold - reduction
      let fold := min subsequentFold remaining
      (fold, rate) :: levelsFrom fuel (remaining - fold) fold rate subsequentReduction

/-- The ladder geometry of a `μ`-variable stack at rate exponent `logInvRate`: level 0 folds
`initialFold` at that rate, then `levelsFrom` (`derive_config`, `whir.rs:43-56`). -/
def ladderShape (μ logInvRate : ℕ) : List (ℕ × ℕ) :=
  (initialFold, logInvRate) ::
    levelsFrom μ (μ - initialFold) initialFold logInvRate initialReduction

/-- The query counts `WHIR_QUERIES` of `whir.rs:17-23`, verbatim: row `R - 1` for the rate
exponent `R`, entry `μ - 15` for the stack size `μ`, one count per level. -/
def queryTable : List (List (List ℕ)) := [
  [[222, 55], [223, 56, 30], [223, 56, 31], [223, 56, 32], [223, 56, 32], [223, 56, 32, 22],
   [223, 56, 32, 22], [224, 56, 32, 23], [224, 56, 32, 23], [224, 56, 32, 23, 17],
   [224, 56, 32, 23, 17], [224, 56, 32, 23, 18], [225, 56, 32, 23, 18], [225, 56, 32, 23, 18, 14]],
  [[111, 45], [112, 45, 27], [112, 45, 28], [112, 45, 28], [112, 45, 28], [112, 45, 28, 20],
   [112, 45, 28, 20], [112, 45, 28, 21], [112, 45, 28, 21], [112, 45, 28, 21, 16],
   [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16], [112, 45, 28, 21, 16, 13]],
  [[75, 37], [75, 37, 24], [75, 37, 25], [75, 38, 25], [75, 38, 25], [75, 38, 25, 18],
   [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19], [75, 38, 25, 19, 15],
   [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15], [75, 38, 25, 19, 15, 13]],
  [[56, 32], [56, 32, 22], [56, 32, 22], [56, 32, 23], [56, 32, 23], [56, 32, 23, 17],
   [56, 32, 23, 17], [56, 32, 23, 18], [56, 32, 23, 18], [56, 32, 23, 18, 14],
   [56, 32, 23, 18, 14], [56, 32, 23, 18, 14], [56, 32, 23, 18, 15], [56, 32, 23, 18, 15, 12]]]

/-- The window the parameters are defined on: the stacking window and the rate range `1..4`
(`whir_queries`, `whir.rs:31-38`; the rate also `crates/verifier/src/lib.rs:228` and
`whir_config.rs:44-55`). -/
def Admissible (μ logInvRate : ℕ) : Prop :=
  minLogStack ≤ μ ∧ μ ≤ maxLogStack ∧ 1 ≤ logInvRate ∧ logInvRate ≤ 4

instance {μ logInvRate : ℕ} : Decidable (Admissible μ logInvRate) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The ladder of an admissible stack size and rate (`derive_config(log_n, log_inv_rate)`,
`whir.rs:40-63`): the geometry of `ladderShape` paired with the
tabulated query counts, level by level. `none` outside the window, and `none` if the table did
not have one count per level (`whir.rs:57`), so that no level is silently dropped. -/
def ladder (μ logInvRate : ℕ) : Option (List Level) :=
  if Admissible μ logInvRate then
    let geometry := ladderShape μ logInvRate
    let queries := (queryTable.getD (logInvRate - 1) []).getD (μ - minLogStack) []
    if geometry.length = queries.length then
      some (List.zipWith (fun (g : ℕ × ℕ) q ↦ ⟨g.1, g.2, q⟩) geometry queries)
    else none
  else none

end LeanVM.Parameters.Whir

end
