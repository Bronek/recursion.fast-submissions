-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/LevelMidSpec.lean` (formal rev 40f877dc) as
-- `LvmWhirLevelMidSpec` for lvm (WP-7). Changed for the unique-decoding regime: no out-of-domain group and no proof
-- of work (`hεO`, `hOlt`, `hεQ`'s `2^-17` go); the query group's escape is `eQueryUd`, its one candidate from the
-- next code's list bound `P'.listMax ≤ 1` (`MidHyp.hL'`); the predicates are read on the opening's view
-- `viewC c₀ n₀ (commits h)` and the opening is of commitment `cidx c₀ n₀ i`.
/-
  LeanVM.Protocol.Whir.Sound.LevelMidSpec

  The doom-calculus specification of a WHIR level with a next commitment, unique decoding.
-/

import LvmWhirProg
import LvmWhirLevelMid

/-!
# The specification of a level with a next commitment

`midSpec`: from `LevelPre` of level `i` (`A(i, 0)` for the running claim against the list of the
level's oracle, on the opening's view of the commitments), the level's groups escape with
probability at most

* `eFold P ℓ` at each fold challenge,
* `eQueryUd P P' t` at the query group (positions, `λ`, openings),

and the level hands `LevelPre` of level `i + 1` to the next level's specification `K`. The
hypotheses `MidHyp` are the arithmetic of the levels (the level's code has the message variables
left after its folds, the next code those after the next level's), the positions' width
(`1 ≤ per`, `per · (κ + R) ≤ 192`), the root's index (`c₀ < n₀`) and the next code's list bound
`listMax ≤ 1` (unique decoding: the query step's one candidate).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-- The arithmetic of a level with a next level. -/
structure MidHyp (μ ℓ₀ per c₀ n₀ : ℕ) (w : List E → E) (P P' : LevelCode)
    (level next : Whir.Level) (pre : ℕ) : Prop where
  hw : IsMultiaffine μ w
  hℓ₀ : ℓ₀ ≤ μ
  hP : P.κ + pre + level.fold = μ
  hP' : P'.κ + (pre + level.fold) + next.fold = μ
  hR : P.R = level.logInvRate
  hR' : P'.R = next.logInvRate
  hc : c₀ < n₀
  hper : 1 ≤ per
  hpd : per * (P.κ + P.R) ≤ 192
  hL' : P'.listMax ≤ 1

/-- A view in shape has a commitment. -/
theorem ne_nil_of_shapeOK {i ℓ : ℕ} {P : LevelCode} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) : cs ≠ [] := by
  intro hc; have := h.1; rw [hc] at this; simp at this

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P P' : LevelCode}
  {level next : Whir.Level} {rest : List Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- The query group of a level with a next level, followed by the query intro polynomial and
the next level. -/
noncomputable def midQuerySpec (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hQlt : eQueryUd P P' level.queries < 1)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec ((queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦ midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r gg.1 gg.2.1 gg.2.2)
      (fun h ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax ((2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries) 0 :=
  ((Spec.ofNoMove (p := queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i))
      (Pre := fun h ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ (commits h)))
      (Post := fun g h ↦ GlueC μ ℓ₀ w i P P' level.fold next.fold pre r g
        (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_queryFragG _ _ _ _ _).noMove
      ((grind_disc_le g _).trans_lt hQlt) fun h₀ hp ↦ by
        obtain ⟨cs₀, hW, -, -, haf⟩ := midC_word hp
        have hκm := afterFold_κ haf
        have hd : μ - r.1.folds.length + level.logInvRate = P.κ + P.R := by rw [hκm, H.hR]
        have hκ' : P.κ = next.fold + P'.κ := by have := H.hP; have := H.hP'; omega
        have hlf : r.2.length = level.fold := haf.2
        have hviol : Viol P (fun _ : Fin 0 → Bool ↦ fun v ↦ foldsN r.2 (laneO i cs₀ P.n) 0 v)
            (runW w ℓ₀ r.1) r.1.target := by
          have := haf.1.1.2.2.2.2.2
          rwa [hlf, Nat.sub_self, rowsOf_zero] at this
        have hW' := commits_cidx H.hc hW
        rw [hd]
        refine escRet_queryFragG_le_ud g hg P P' hκ' per level.queries (cidx c₀ n₀ i) H.hper H.hpd h₀
          hW' (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) P'.n)) _
          (runW w ℓ₀ r.1) r.1.target hviol ((P'.card_iList_le _).trans H.hL')
          (fun g cs ↦ GlueC μ ℓ₀ w i P P' level.fold next.fold pre r g (viewC c₀ n₀ cs))
          fun qs lam hr hlen hv ↦ ⟨hp, ?_⟩
        rw [glueLv_runW, glueLv_target, enfOf_eq haf.1.2 r.2 hlf qs hr lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun gg ↦
    (roundPolyInv (fun cs ↦ GlueC μ ℓ₀ w i P P' level.fold next.fold pre r gg (viewC c₀ n₀ cs))
        (enfOf i r.2 gg.1 gg.2.1 gg.2.2) (T := εmax) le_rfl).bind' fun hq ↦
      (K (glueLv μ i r gg.1 gg.2.1 gg.2.2 hq)).mono
        (fun h hp ↦ levelPre_next H.hP' r gg hq _ hp.2 hp.1) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl

/-- After the fold rounds of a level with a next level. -/
noncomputable def midTailSpec (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hQlt : eQueryUd P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec (midTail μ ℓ₀ per c₀ n₀ g dir w i level next rest r)
      (fun h ↦ AfterFold μ ℓ₀ w i P level.fold pre r (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax 0 0 :=
  (commitInv (fun cs ↦ AfterFold μ ℓ₀ w i P level.fold pre r (viewC c₀ n₀ cs))
      (fun cs ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ cs))
      (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
      (fun cs W h hW ↦ by
        rw [viewC_append (le_length_of_viewC (ne_nil_of_shapeOK h.1.2))]
        exact midC_of_commit next rfl H.hP' H.hR' h hW)
      (T := (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries) hεQ).bind' fun _ ↦
  (grindPreInv (fun cs ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ cs)) g
      hεQ).bind' fun _ ↦
  (midQuerySpec H hg hQlt K r).congr
    (query_bindG per g (cidx c₀ n₀ i) (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r qs lam words).symm

/-- **The specification of a level with a next level.** -/
noncomputable def midSpec (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hεF : eFold P level.fold ≤ εmax) (hQlt : eQueryUd P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (s : WhirStateT) :
    Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w i (level :: next :: rest) s)
      (fun h ↦ LevelPre μ ℓ₀ w i P level.fold pre s (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0 :=
  (((foldRoundsSpec μ ℓ₀ w i P level.fold pre (viewC c₀ n₀)
      (fun cs ↦ ShapeOK i P level.fold (viewC c₀ n₀ cs)) H.hw H.hℓ₀ hεF level.fold s []).bind'
      fun r ↦ midTailSpec H hg hQlt hεQ K r).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirLevels_mid μ ℓ₀ per c₀ n₀ g dir w i level next rest s).symm

end
end LeanVM.Protocol.Whir.Sound
