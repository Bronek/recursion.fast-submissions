-- New for lvm2 (WP JB-L, J2): `whirLevelsJ` (LvmWhirProgJ) split at the final level's residual, as `LvmCertSRes`
-- splits `C_rec`'s unique-decoding opening there. No upstream template.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the WHIR opening with OOD samples, cut at the residual)
-/

import LvmWhirProgJ
import LvmWhirLevelFinal
import LvmWhirMidJ
import LvmWhirPathR

/-!
# The opening up to the residual

The relativised doom (`LvmWhirPathR`) ends at the final level's residual: an accepting run either
ends in a fold of a good candidate (`GoodRes`) or is in the residual's doom (`ResC`), from which the
final level's queries reject. This module cuts the program there.

* `whirPrefixJ logN per c₀ n₀ g i levels s`: `whirLevelsJ` up to and including the final level's
  residual read, returning the final level's fold state `r` and the residual `res`. A level with a
  next one is `whirLevelsJ`'s, recursing into `whirPrefixJ`; the final level is its fold rounds and
  the residual. It depends neither on the evaluation basis nor on `laneFolds` and `direct`.
* `finSuffixJ … i level (r, res)`: the rest of the final level (`finTail` after the residual).
* `whirLevelsJ_eq_prefix`: **`whirLevelsJ = whirPrefixJ >>= finSuffixJ`** (final index from
  `finInfo`, final level `levels.getLast`).
* `stackPrefixJ cfg claims`: the batching challenge `ρ`, the first round polynomial, `whirPrefixJ`;
  it returns `ρ` with the prefix's result (the suffix's evaluation basis is the batch under `ρ`).
  `verifyStackedJ_eq_prefix`: **`verifyStackedJ cfg claims = stackPrefixJ >>= suffix`** with OOD.
* `foldRoundsT_folds_prefix`: the fold rounds extend the fold challenges (a fact of every return).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram

section

/-! ## The program -/

/-- **The opening up to the residual**: `whirLevelsJ` cut after the final level's residual read,
returning the final level's fold state and the residual. -/
def whirPrefixJ (logN per c₀ n₀ g : ℕ) :
    ℕ → List Whir.Level → WhirStateT → VerifierProgram ((WhirStateT × List E) × List E)
  | _, [], _ => VerifierProgram.fail
  | _, [level], s =>
    (foldRoundsT level.fold s []).bind fun r ↦
      (readScalars (2 ^ (logN - r.1.folds.length))).bind fun res ↦ VerifierProgram.ret (r, res)
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
    whirPrefixJ logN per c₀ n₀ g (index + 1) (next :: rest)
      (glueT lam s [(oodValue, oodIntro, fun x ↦ eqEval oodPoint x),
        (enforced, intro, fun x ↦ Verifier.inducedWeight messageLog queries queryWeights x)])

section Program

variable (μ ℓ₀ per c₀ n₀ g : ℕ) (dir : Bool) (w : List E → E) (i : ℕ) (level next : Whir.Level)
  (rest : List Whir.Level)

/-- **The rest of the final level** after the residual: `finTail` after `readScalars`. -/
def finSuffixJ (a : (WhirStateT × List E) × List E) : VerifierProgram Unit :=
  (grindPre g).bind fun _ ↦ (powCheck g).bind fun _ ↦
  (samplePositions per (μ - a.1.1.folds.length + level.logInvRate) level.queries).bind fun qs ↦
  sampleChallenge.bind fun lam ↦ (queryOpenings (cidx c₀ n₀ i) qs).bind fun words ↦
    finFinish μ ℓ₀ dir w i level a.1 a.2 qs lam words

/-- After the query group of a level with a next level (prefix): the query intro polynomial,
then the next levels' prefix. -/
def midFinishPJ (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ)
    (lam : E) (words : List (List K)) : VerifierProgram ((WhirStateT × List E) × List E) :=
  (sumcheckRoundPoly 3 (enfOf i r.2 qs lam words) none).bind fun hq ↦
    whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) (glueMid μ i r z y hy qs lam words hq)

/-- After the fold rounds of a level with a next level (prefix). -/
def midTailPJ (r : WhirStateT × List E) : VerifierProgram ((WhirStateT × List E) × List E) :=
  (readCommitment (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)).bind
    fun _ ↦
  (sampleChallenges (μ - r.1.folds.length)).bind fun z ↦ readScalar.bind fun y ↦
  (sumcheckRoundPoly 3 y none).bind fun hy ↦
  (grindPre g).bind fun _ ↦ (powCheck g).bind fun _ ↦
  (samplePositions per (μ - r.1.folds.length + level.logInvRate) level.queries).bind fun qs ↦
  sampleChallenge.bind fun lam ↦ (queryOpenings (cidx c₀ n₀ i) qs).bind fun words ↦
    midFinishPJ μ per c₀ n₀ g i next rest r z y hy qs lam words

/-- **`whirPrefixJ` on a level with a next level, unfolded.** -/
theorem whirPrefixJ_mid (s : WhirStateT) :
    whirPrefixJ μ per c₀ n₀ g i (level :: next :: rest) s =
      (foldRoundsT level.fold s []).bind fun r ↦ midTailPJ μ per c₀ n₀ g i level next rest r :=
  rfl

/-- **`whirPrefixJ` on the final level, unfolded.** -/
theorem whirPrefixJ_one (s : WhirStateT) :
    whirPrefixJ μ per c₀ n₀ g i [level] s =
      (foldRoundsT level.fold s []).bind fun r ↦
        (readScalars (2 ^ (μ - r.1.folds.length))).bind fun res ↦ VerifierProgram.ret (r, res) :=
  rfl

/-- The prefix of a level with a next level followed by the suffix is the level. -/
theorem midTailPJ_bind (r : WhirStateT × List E)
    (hK : ∀ s', (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s').bind
        (finSuffixJ μ ℓ₀ per c₀ n₀ g dir w (finInfo (i + 1) 0 (next :: rest)).1
          ((next :: rest).getLast (List.cons_ne_nil _ _))) =
      whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s') :
    (midTailPJ μ per c₀ n₀ g i level next rest r).bind
        (finSuffixJ μ ℓ₀ per c₀ n₀ g dir w (finInfo (i + 1) 0 (next :: rest)).1
          ((next :: rest).getLast (List.cons_ne_nil _ _))) =
      midTailJ μ ℓ₀ per c₀ n₀ g dir w i level next rest r := by
  simp only [midTailPJ, midFinishPJ, midTailJ, midFinishJ, VerifierProgram.bind_assoc, hK]

end Program

/-- The final level's index does not depend on the fold challenges before it. -/
theorem finInfo_fst (i : ℕ) : ∀ (pre pre' : ℕ) (levels : List Whir.Level),
    (finInfo i pre levels).1 = (finInfo i pre' levels).1 := by
  intro pre pre' levels
  induction levels generalizing i pre pre' with
  | nil => rfl
  | cons level rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest => exact ih (i + 1) (pre + level.fold) (pre' + level.fold)

/-- **The opening is its prefix up to the residual, then the final level's suffix.** -/
theorem whirLevelsJ_eq_prefix (μ ℓ₀ per c₀ n₀ g : ℕ) (dir : Bool) (w : List E → E) :
    ∀ (index pre : ℕ) (levels : List Whir.Level) (hne : levels ≠ []) (s : WhirStateT),
      whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w index levels s =
        (whirPrefixJ μ per c₀ n₀ g index levels s).bind
          (finSuffixJ μ ℓ₀ per c₀ n₀ g dir w (finInfo index pre levels).1 (levels.getLast hne))
  | _, _, [], hne, _ => (hne rfl).elim
  | index, pre, [level], _, s => by
    rw [whirLevelsJ_one, whirLevels_fin, whirPrefixJ_one]
    simp only [finProg, finTail, finInfo, List.getLast_singleton, VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
    rfl
  | index, pre, level :: next :: rest, _, s => by
    rw [whirLevelsJ_mid, whirPrefixJ_mid, midProgJ, VerifierProgram.bind_assoc]
    have hfin : (finInfo index pre (level :: next :: rest)).1 = (finInfo (index + 1) 0 (next :: rest)).1 :=
      finInfo_fst (index + 1) (pre + level.fold) 0 (next :: rest)
    rw [hfin]
    congr 1
    funext r
    exact (midTailPJ_bind μ ℓ₀ per c₀ n₀ g dir w index level next rest r fun s' ↦
      (whirLevelsJ_eq_prefix μ ℓ₀ per c₀ n₀ g dir w (index + 1) 0 (next :: rest) _ s').symm).symm

/-! ## The stacked opening -/

/-- **The stacked opening up to the residual** (OOD): the batching challenge `ρ`, the first round
polynomial, the levels' prefix; returns `ρ` and the prefix's result. -/
def stackPrefixJ (cfg : WhirConfig) (claims : List StackClaim) :
    VerifierProgram (E × ((WhirStateT × List E) × List E)) :=
  sampleChallenge.bind fun ρ ↦
    (sumcheckRoundPoly 3 (dot (powers ρ claims.length) (claims.map (·.2))) none).bind fun quad ↦
      (whirPrefixJ cfg.μ cfg.per cfg.c₀ cfg.n₀ cfg.grind 0 cfg.levels
        ⟨dot (powers ρ claims.length) (claims.map (·.2)), quad, [], []⟩).bind fun a ↦
        VerifierProgram.ret (ρ, a)

/-- The suffix of the stacked opening: the final level after the residual, with the batch under
`ρ` as the evaluation basis. -/
def stackSuffixJ (cfg : WhirConfig) (claims : List StackClaim) (hne : cfg.levels ≠ [])
    (x : E × ((WhirStateT × List E) × List E)) : VerifierProgram Unit :=
  finSuffixJ cfg.μ ((cfg.levels.head?.map (·.fold)).getD 0) cfg.per cfg.c₀ cfg.n₀ cfg.grind
    cfg.direct (fun point ↦ dot (powers x.1 claims.length) (claims.map fun c ↦ c.1 point))
    (finInfo 0 0 cfg.levels).1 (cfg.levels.getLast hne) x.2

/-- **The stacked opening with OOD is its prefix up to the residual, then the suffix.** -/
theorem verifyStackedJ_eq_prefix (cfg : WhirConfig) (hood : cfg.ood = true) (hne : cfg.levels ≠ [])
    (claims : List StackClaim) :
    verifyStackedJ cfg claims = (stackPrefixJ cfg claims).bind (stackSuffixJ cfg claims hne) := by
  simp only [verifyStackedJ, verifyWhirJ, hood, ↓reduceIte, stackPrefixJ, stackSuffixJ, bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  congr 1
  funext ρ
  congr 1
  funext quad
  exact whirLevelsJ_eq_prefix _ _ _ _ _ _ _ _ 0 0 cfg.levels hne _

/-- The query group with the proof of work, for any continuation (`query_bindG` at any result
type). -/
theorem query_bindG' {β : Type} (per g c d t : ℕ)
    (k : List ℕ → E → List (List K) → VerifierProgram β) :
    ((powCheck g).bind fun _ ↦ (samplePositions per d t).bind fun qs ↦
      sampleChallenge.bind fun lam ↦ (queryOpenings c qs).bind fun words ↦ k qs lam words) =
      (queryFragG g per d t c).bind fun gg ↦ k gg.1 gg.2.1 gg.2.2 := by
  simp only [queryFragG, queryFrag, bind_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-! ## The fold rounds extend the fold challenges -/

variable {α β : Type}

/-- A return of a sequence splits into a return of its first part and one of its second
(`LvmCertSRes.after_bind_ret`, restated here to keep the import light). -/
theorem after_bind_ret' {p : VerifierProgram α} {f : α → VerifierProgram β} {l : List Ev} {b : β}
    (h : (p.bind f).after l = some (.ret b)) :
    ∃ a l₁ l₂, l = l₁ ++ l₂ ∧ p.after l₁ = some (.ret a) ∧ (f a).after l₂ = some (.ret b) := by
  rcases after_bind_cases f h with ⟨q, hq, he⟩ | ⟨a, l₁, l₂, rfl, h1, -, h2⟩
  · cases q with
    | ret a => exact ⟨a, l, [], by simp, hq, by simpa [after] using he.symm⟩
    | _ => simp [VerifierProgram.bind] at he
  · exact ⟨a, l₁, l₂, rfl, h1, h2⟩

/-- **Every return of the fold rounds extends the fold challenges.** -/
theorem foldRoundsT_folds_prefix : ∀ (n : ℕ) (s : WhirStateT) (lf : List E) {l : List Ev}
    {r : WhirStateT × List E}, (foldRoundsT n s lf).after l = some (.ret r) →
      s.folds <+: r.1.folds
  | 0, s, lf, l, r, h => by
    cases l with
    | nil => simp [foldRoundsT, VerifierProgram.after] at h; subst h; exact List.prefix_refl _
    | cons e es => cases e <;> simp [foldRoundsT, VerifierProgram.after] at h
  | n + 1, s, lf, l, r, h => by
    unfold foldRoundsT at h
    obtain ⟨c, l₁, l₂, -, -, h2⟩ := after_bind_ret' (p := sampleChallenge) h
    obtain ⟨quad, m₁, m₂, -, -, h4⟩ := after_bind_ret' h2
    exact (List.prefix_append _ _).trans (foldRoundsT_folds_prefix n _ _ h4)

end
end LeanVM.Protocol.Whir.Sound
