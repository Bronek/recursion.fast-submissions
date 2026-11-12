-- New for lvm2 (WP JB-L). The level loop `whirLevelsJ` is leanVM's `whirLevelsT`
-- (`formal/lean_vm/LeanVM/Protocol/Verifier/WhirTarget.lean`, formal rev 0b850750) with lvm's changes of
-- `whirLevelsUd` (`LvmWhirProg`: levels as a list, `per` positions per challenge, per-level commitment indices,
-- PI-GRIND's in-answer proof of work `grindPre g`/`powCheck g` in place of `grindProofOfWork`): it keeps
-- leanVM's out-of-domain step on every level with a next commitment, which `whirLevelsUd` dropped.
/-
  LeanVM.Protocol.Verifier (lvm2: WHIR with out-of-domain samples, the Johnson regime)
-/

import LvmWhirProg

/-!
# The WHIR opening with out-of-domain samples

In the Johnson regime a level's next oracle has a list of up to `L' > 1` candidates, so each level
with a next commitment samples an **out-of-domain point** on it (leanVM `crates/verifier/src/whir.rs`,
`verify_whir`, lines 170–190 at `40f877dc`; JB-DES §1.2). **The transcript of a level with a next
commitment** (`whirLevelsJ`, `ood = true`), after the level's `ℓ` fold rounds, with
`κ = μ − (folds so far)` the variables of the folded message:

1. `readCommitment` of the next oracle (its cap);
2. **the OOD point** `z ∈ E^κ`: `κ` challenges (`sampleChallenges κ`, coordinate `0` first);
3. **the OOD answer** `y`: one scalar (`readScalar`), the claimed `f̃(z)` of the folded message;
4. **the OOD intro polynomial**: `sumcheckRoundPoly 3 y none` (the scalars of the round
   polynomial whose `h(0) + h(1)` is `y`, as the query intro);
5. PI-GRIND's proof of work (`grindPre g`: separating challenge, nonce; `powCheck g`), nothing at
   `g = 0`;
6. the positions, `λ`, the openings and the query intro polynomial, as in `whirLevelsUd`;
7. **the glue** with powers of `λ`: the running claim `λ⁰`, the OOD claim `(eq(z, ·), y)` at `λ¹`,
   the consistency claim of position `q` at `λ^(2+q)` (`glueT λ s [ood, queries]`).

The final level is `whirLevelsUd`'s (no next oracle, no OOD). The root commitment (level `0`'s
oracle) gets no OOD sample: it is committed before the opening, and the stacked batching pays
`(J − 1)·L₀/|E|` instead.

`WhirConfig` is a `UdConfig` with the flag `ood`: `verifyWhirJ cfg` is `verifyWhirUd` when
`ood = false` (by definition: unique decoding, as v1 and `C_rec` in J1) and runs `whirLevelsJ`
when `ood = true` (Johnson). Rates, folds, query counts, grinding and the commitment indices stay
the configuration's.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.Compile Claims

section

/-- **The level loop with out-of-domain samples**: the final level is `whirLevelsUd`'s; a level
with a next commitment samples the OOD point on the next oracle and reads its answer and intro
polynomial before the proof of work, and glues the OOD claim at `λ¹` and the queries at
`λ^(2+q)`. -/
def whirLevelsJ (logN laneFolds per c₀ n₀ g : ℕ) (direct : Bool) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirStateT → VerifierProgram Unit
  | _, [], _ => VerifierProgram.fail
  | index, [level], s => whirLevelsUd logN laneFolds per c₀ n₀ g direct evaluateBasis index [level] s
  | index, level :: next :: rest, s => do
    let (s, levelFolds) ← foldRoundsT level.fold s []
    let messageLog := logN - s.folds.length
    VerifierProgram.readCommitment (messageLog - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
    let oodPoint ← VerifierProgram.sampleChallenges messageLog
    let oodValue ← VerifierProgram.readScalar
    let oodIntro ← sumcheckRoundPoly 3 oodValue none
    grindPre g
    powCheck g
    let queries ← samplePositions per (messageLog + level.logInvRate) level.queries
    let lam ← VerifierProgram.sampleChallenge
    let queryWeights := powers lam queries.length
    let words ← VerifierProgram.queryOpenings (cidx c₀ n₀ index) queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    whirLevelsJ logN laneFolds per c₀ n₀ g direct evaluateBasis (index + 1) (next :: rest)
      (glueT lam s [(oodValue, oodIntro, fun x ↦ eqEval oodPoint x),
        (enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)])

/-- **The configuration of a WHIR opening**: `UdConfig` and whether the levels with a next
commitment take an out-of-domain sample (`true`: the Johnson regime). -/
structure WhirConfig extends UdConfig where
  /-- One OOD sample per level with a next commitment. -/
  ood : Bool

/-- **The WHIR opening**: `verifyWhirUd` without OOD, `whirLevelsJ` with it. -/
def verifyWhirJ (cfg : WhirConfig) (target : E) (evaluateBasis : List E → E) :
    VerifierProgram Unit :=
  if cfg.ood then do
    let quad ← sumcheckRoundPoly 3 target none
    whirLevelsJ cfg.μ ((cfg.levels.head?.map (·.fold)).getD 0) cfg.per cfg.c₀ cfg.n₀ cfg.grind
      cfg.direct evaluateBasis 0 cfg.levels ⟨target, quad, [], []⟩
  else verifyWhirUd cfg.toUdConfig target evaluateBasis

/-- **The stacked opening** (`verifyStackedUd` with `verifyWhirJ`). -/
def verifyStackedJ (cfg : WhirConfig) (claims : List StackClaim) : VerifierProgram Unit := do
  let scales := powers (← VerifierProgram.sampleChallenge) claims.length
  verifyWhirJ cfg (dot scales (claims.map (·.2))) fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- Without OOD the opening is the unique-decoding one. -/
theorem verifyWhirJ_ud (cfg : WhirConfig) (h : cfg.ood = false) (target : E)
    (evaluateBasis : List E → E) :
    verifyWhirJ cfg target evaluateBasis = verifyWhirUd cfg.toUdConfig target evaluateBasis := by
  simp [verifyWhirJ, h]

/-- Without OOD the stacked opening is the unique-decoding one. -/
theorem verifyStackedJ_ud (cfg : WhirConfig) (h : cfg.ood = false) (claims : List StackClaim) :
    verifyStackedJ cfg claims = verifyStackedUd cfg.toUdConfig claims := by
  simp only [verifyStackedJ, verifyStackedUd, verifyWhirJ_ud cfg h]

/-- A one-level opening is the same with or without OOD. -/
theorem whirLevelsJ_one (logN laneFolds per c₀ n₀ g : ℕ) (direct : Bool) (evaluateBasis : List E → E)
    (index : ℕ) (level : Whir.Level) (s : WhirStateT) :
    whirLevelsJ logN laneFolds per c₀ n₀ g direct evaluateBasis index [level] s =
      whirLevelsUd logN laneFolds per c₀ n₀ g direct evaluateBasis index [level] s := by
  simp [whirLevelsJ]

end

end LeanVM.Protocol.Verifier
