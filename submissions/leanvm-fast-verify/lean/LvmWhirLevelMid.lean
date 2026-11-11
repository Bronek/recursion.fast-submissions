-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/LevelMid.lean` (formal rev 40f877dc) as
-- `LvmWhirLevelMid` for lvm (WP-7). Changed for the unique-decoding regime: the level is lvm's (`whirLevelsUd`: no
-- out-of-domain step, no proof of work, positions `per` per challenge, the opening of commitment `cidx c₀ n₀ i`),
-- so `OodC` is cut, the glue `glueLv` has one claim (leanVM's final-level `glueFin`, here for every level) and
-- `GlueC` follows `MidC` directly. The doom predicates are leanVM's, read on the opening's view of the commitments.
/-
  LeanVM.Protocol.Whir.Sound.LevelMid

  A WHIR level with a next commitment in the unique-decoding regime: the fold rounds, the
  commitment of the next oracle, the query group with `λ`, and the glued claim handed to the next
  level.
-/

import LvmWhirProg
import LvmWhirGroupEscape

/-!
# A level with a next commitment

`whirLevelsUd μ ℓ₀ per c₀ n₀ dir w i (level :: next :: rest) s` (lvm's loop body) is, definitionally,
`midProg`: the fold rounds, then `midTail` (commitment, positions, `λ`, opening, query intro
polynomial, glue, next level).

Doom along the level (all functions of the opening's view `cs` of the commitments and of the
values in scope):

* `AfterFold r cs`: `A(i, ℓ)` for the state and challenges `r` returned by the fold rounds;
* `MidC r cs`: after the commitment of the next oracle (`cs = cs₀ ++ [next word]`);
* `GlueC r g cs`: after the query group `g = (positions, λ, rows)`: every member of the next list
  violates the glued claim; with the query intro polynomial this is `LevelPre` of the next level
  (`levelPre_next`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## The program -/

section Program

variable (μ ℓ₀ per c₀ n₀ : ℕ) (dir : Bool) (w : List E → E) (i : ℕ) (level next : Whir.Level)
  (rest : List Whir.Level)

/-- The enforced sum of a level's opened rows. -/
def enfOf (lf : List E) (qs : List ℕ) (lam : E) (words : List (List K)) : E :=
  enforcedSum (if i = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow) lf
    (powers lam qs.length)

/-- The state glued at the end of a level: the batched consistency claims with `λ` (leanVM's
final-level glue; lvm glues it on every level). -/
def glueLv (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) : WhirStateT :=
  glueT lam r.1 [(enfOf i r.2 qs lam words, hq,
    fun x ↦ Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x)]

/-- After the query group: the query intro polynomial, then the next level. -/
def midFinish (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K)) :
    VerifierProgram Unit :=
  (sumcheckRoundPoly 3 (enfOf i r.2 qs lam words) none).bind fun hq ↦
    whirLevelsUd μ ℓ₀ per c₀ n₀ dir w (i + 1) (next :: rest) (glueLv μ i r qs lam words hq)

/-- After the fold rounds. -/
def midTail (r : WhirStateT × List E) : VerifierProgram Unit :=
  (readCommitment (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)).bind
    fun _ ↦
  (samplePositions per (μ - r.1.folds.length + level.logInvRate) level.queries).bind fun qs ↦
  sampleChallenge.bind fun lam ↦ (queryOpenings (cidx c₀ n₀ i) qs).bind fun words ↦
    midFinish μ ℓ₀ per c₀ n₀ dir w i next rest r qs lam words

/-- The level, unfolded. -/
def midProg (s : WhirStateT) : VerifierProgram Unit :=
  (foldRoundsT level.fold s []).bind fun r ↦ midTail μ ℓ₀ per c₀ n₀ dir w i level next rest r

/-- **`whirLevelsUd` on a level with a next commitment is `midProg`.** -/
theorem whirLevels_mid (s : WhirStateT) :
    whirLevelsUd μ ℓ₀ per c₀ n₀ dir w i (level :: next :: rest) s =
      midProg μ ℓ₀ per c₀ n₀ dir w i level next rest s := rfl

/-- The query group as one fragment. -/
theorem query_bind (c d t : ℕ) (K : List ℕ → E → List (List K) → VerifierProgram Unit) :
    ((samplePositions per d t).bind fun qs ↦ sampleChallenge.bind fun lam ↦
      (queryOpenings c qs).bind fun words ↦ K qs lam words) =
      (queryFrag per d t c).bind fun g ↦ K g.1 g.2.1 g.2.2 := by
  simp only [queryFrag, bind_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

end Program

/-! ## Doom along the level -/

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)

/-- After the fold rounds. -/
def AfterFold (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (FoldInv μ ℓ₀ w i P ℓ pre r.1 r.2 cs ∧ ShapeOK i P ℓ cs) ∧ r.2.length = ℓ

/-- After the commitment of the next oracle. -/
def MidC (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ cs₀ W', cs = cs₀ ++ [(P'.κ + P'.R, 3 * 2 ^ ℓ', W')] ∧ WellShaped (3 * 2 ^ ℓ') W' ∧
    AfterFold μ ℓ₀ w i P ℓ pre r cs₀

/-- After the query group: every member of the next list violates the glued claim. -/
def GlueC (r : WhirStateT × List E) (g : List ℕ × E × List (List K))
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidC μ ℓ₀ w i P P' ℓ ℓ' pre r cs ∧
    Viol P' (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []))
      (glueLv μ i r g.1 g.2.1 g.2.2 []).target

end Doom

/-! ## Bookkeeping lemmas -/

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}

theorem afterFold_len {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFold μ ℓ₀ w i P ℓ pre r cs) : r.1.folds.length = pre + ℓ := by
  obtain ⟨⟨⟨hl, -⟩, -⟩, hr⟩ := h
  omega

theorem afterFold_κ {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFold μ ℓ₀ w i P ℓ pre r cs) : μ - r.1.folds.length = P.κ := by
  have := afterFold_len h
  obtain ⟨⟨⟨-, -, hκ, -⟩, -⟩, -⟩ := h
  omega

/-- The glued state's weight. -/
theorem glueLv_runW (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) :
    runW w ℓ₀ (glueLv μ i r qs lam words hq) = fun x ↦ runW w ℓ₀ r.1 x +
      1 * lam * Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x := by
  funext x
  rw [glueLv, glue_one]
  have := runW_glue w ℓ₀ r.1 [⟨1 * lam, r.1.folds.length, fun x ↦ Verifier.inducedWeight
    (μ - r.1.folds.length) qs (powers lam qs.length) x⟩] (by simp) x
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this
  exact this

/-- The glued state's target. -/
theorem glueLv_target (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) :
    (glueLv μ i r qs lam words hq).target = r.1.target + 1 * lam * enfOf i r.2 qs lam words := by
  rw [glueLv, glue_one]

/-- The glue keeps the folds. -/
theorem glueLv_folds (r : WhirStateT × List E) (qs : List ℕ) (lam : E) (words : List (List K))
    (hq : List E) : (glueLv μ i r qs lam words hq).folds = r.1.folds := by
  rw [glueLv, glue_one]

/-- The glued claims are well formed after the glue. -/
theorem gluedOK_glueLv {r : WhirStateT × List E} (hg : GluedOK μ r.1) (qs : List ℕ) (lam : E)
    (words : List (List K)) (hq : List E) : GluedOK μ (glueLv μ i r qs lam words hq) := by
  intro c hc
  rw [glueLv, glue_one] at hc ⊢
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with hc | rfl
  · exact hg c hc
  · exact ⟨le_rfl, isMultiaffine_inducedWeight _ _ _ (length_powers _ _)⟩

/-- The enforced sum of the rows of commitment `i` at in-range positions. -/
theorem enfOf_eq {cs : List (ℕ × ℕ × Word)} (hshape : ShapeOK i P ℓ cs) (lf : List E)
    (hlf : lf.length = ℓ) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n) (lam : E) :
    enfOf i lf qs lam (qs.map (wordOf cs i)) =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) *
        wordAt (fun v : Fin P.n ↦ foldsN lf (laneO i cs P.n) 0 v) qs[k] := by
  rw [enfOf, rows_eq]
  exact enforcedSum_eq i cs lf hlf qs hqs lam fun q _ ↦ length_wordOf hshape q

/-- **The next level's doom** from the glued doom and the query intro polynomial. -/
theorem levelPre_next (hP' : P'.κ + (pre + ℓ) + ℓ' = μ) (r : WhirStateT × List E)
    (g : List ℕ × E × List (List K)) (hq : List E) (cs : List (ℕ × ℕ × Word))
    (hglue : GlueC μ ℓ₀ w i P P' ℓ ℓ' pre r g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    LevelPre μ ℓ₀ w (i + 1) P' ℓ' (pre + ℓ) (glueLv μ i r g.1 g.2.1 g.2.2 hq) cs := by
  obtain ⟨⟨cs₀, W', rfl, hW', haf⟩, hviol⟩ := hglue
  have hlen := afterFold_len haf
  obtain ⟨⟨⟨-, -, -, hg, hquad, -⟩, hshape⟩, -⟩ := haf
  refine ⟨⟨?_, by simp, hP', gluedOK_glueLv hg _ _ _ _, ?_, ?_⟩, ?_⟩
  · rw [glueLv_folds]; simp [hlen]
  · rw [glueLv, glue_one]
    exact quadOK_zipWith hquad hhq _
  · have hr : runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 hq) =
        runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []) := by
      rw [glueLv_runW, glueLv_runW]
    have ht : (glueLv μ i r g.1 g.2.1 g.2.2 hq).target =
        (glueLv μ i r g.1 g.2.1 g.2.2 []).target := by
      rw [glueLv_target, glueLv_target]
    simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil, hr, ht]
    exact hviol
  · refine ⟨by simp [hshape.1], W', ?_, ?_⟩
    · rw [List.getElem?_append_right (by rw [hshape.1]), hshape.1, Nat.sub_self]
      simp [wdOf]
    · simpa [wdOf] using hW'

/-- After the commitment: the next oracle's word is appended. -/
theorem midC_of_commit {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)} {W : Word}
    (next : Whir.Level) (hℓ' : next.fold = ℓ') (hP' : P'.κ + (pre + ℓ) + ℓ' = μ)
    (hR' : P'.R = next.logInvRate) (h : AfterFold μ ℓ₀ w i P ℓ pre r cs)
    (hW : WellShaped (3 * 2 ^ next.fold) W) :
    MidC μ ℓ₀ w i P P' ℓ ℓ' pre r
      (cs ++ [(μ - r.1.folds.length - next.fold + next.logInvRate, 3 * 2 ^ next.fold, W)]) := by
  have hlen := afterFold_len h
  subst hℓ'
  refine ⟨cs, W, ?_, hW, h⟩
  congr 3
  omega

/-- The commitments after the next commitment, at index `i`. -/
theorem midC_word {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : MidC μ ℓ₀ w i P P' ℓ ℓ' pre r cs) :
    ∃ cs₀, cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs₀ i) ∧ wordOf cs i = wordOf cs₀ i ∧
      laneO i cs P.n = laneO i cs₀ P.n ∧ AfterFold μ ℓ₀ w i P ℓ pre r cs₀ := by
  obtain ⟨cs₀, W', rfl, -, haf⟩ := h
  have hsh := haf.1.2
  have hi : i < cs₀.length := by rw [hsh.1]; omega
  exact ⟨cs₀, shapeOK_append hsh _, wordOf_append _ _ hi, laneO_append _ _ hi _, haf⟩

/-- A level's word read through the view is the word of the commitment the level opens. -/
theorem commits_cidx {c₀ n₀ : ℕ} (hc : c₀ < n₀) {cs : List (ℕ × ℕ × Word)} {j ht wd : ℕ}
    {W : Word} (h : (viewC c₀ n₀ cs)[j]? = some (ht, wd, W)) :
    cs[cidx c₀ n₀ j]? = some (ht, wd, W) :=
  getElem?_viewC hc h

end Lemmas

end
end LeanVM.Protocol.Whir.Sound
