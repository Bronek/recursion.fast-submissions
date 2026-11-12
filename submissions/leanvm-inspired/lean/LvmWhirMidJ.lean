-- New for lvm2 (WP JB-L): a WHIR level with a next commitment and its out-of-domain sample, ported from leanVM
-- `formal/lean_vm/LeanVM/Protocol/Whir/Sound/{LevelMid,LevelMidSpec}.lean` (formal rev 0b850750) onto
-- LvmWhirLevelMidSpec/LvmWhirSpec (PI-GRIND). Changed against leanVM: the level is `whirLevelsJ`'s (positions `per`
-- per challenge, the opening of commitment `cidx c₀ n₀ i`, the doom read on the opening's view `viewC c₀ n₀`), and
-- the proof of work is PI-GRIND's in-answer `grindPre g`/`powCheck g` (the PoW challenge joins the query group, so
-- the query escape is `2^-g · eQuery`). Statements and proof structure are otherwise leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.MidJ

  The specification of a WHIR level with a next commitment in the Johnson regime: the fold rounds,
  the commitment of the next oracle, the out-of-domain group, the proof of work, the query group
  with `λ`, and the glued claim handed to the next level.
-/

import LvmWhirProgJ
import LvmWhirEscapeJ
import LvmWhirLevelMidSpec

/-!
# A level with a next commitment and an out-of-domain sample

`whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w i (level :: next :: rest) s` is, definitionally, `midProgJ`
(`whirLevelsJ_mid`): the fold rounds, then `midTailJ` (commitment, OOD point `z`, OOD answer `y`
and its intro polynomial, `grindPre g`, the query group with the proof of work, the query intro
polynomial, the glue `glueMid` of the OOD claim at `λ` and the queries at `λ²·λ^q`, next level).

* `escRet_queryFragG_le`: the query group with the proof of work escapes with probability at most
  `2^-g · eQuery P P' t`, given the doom before the positions and `OodSep` of the next list at `z`.
* Doom along the level: `AfterFold`, `MidC` (`LvmWhirLevelMid`), then `OodC r z cs` (the next list
  is separated at `z`), `GlueCJ r z y hy g cs` (every member of the next list violates the glued
  claim); `levelPre_nextJ` gives `LevelPre` of the next level.
* `midQuerySpecJ`, `midTailSpecJ`, `midSpecJ`: from `LevelPre` of level `i` (on the view), the
  level's groups escape with probability at most `eFold P ℓ` (fold challenges), `eOod P' κ` (OOD
  point) and `2^-g · eQuery P P' t` (query group), and the level hands `LevelPre` of level `i + 1`
  to the next levels' specification `K`. `MidHypJ` is `MidHyp` without the list bound.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## The query group with the proof of work -/

open Classical in
/-- **The query group of a level with a next commitment and an OOD sample, with the proof of
work.** -/
theorem escRet_queryFragG_le (g : ℕ) (hg : g ≤ 192) (P P' : LevelCode) {ℓ' : ℕ}
    (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ) (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFragG g per (P.κ + P.R) t c) ≤
      (2 : ENNReal)⁻¹ ^ g * eQuery P P' t := by
  refine escRet_powCheck_le g hg _ h₀ _ _ fun h hh ↦ ?_
  rw [← hh] at hW
  refine escRet_queryFrag_le P P' hκ per t c hper hpd h hW Q' C Φ σ z y hviol hsep
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

/-! ## The program -/

section Program

variable (μ ℓ₀ per c₀ n₀ g : ℕ) (dir : Bool) (w : List E → E) (i : ℕ) (level next : Whir.Level)
  (rest : List Whir.Level)

/-- The state glued at the end of a level with a next commitment: the OOD claim at `λ`, the
consistency claims at `λ²·λ^q`. -/
def glueMid (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ) (lam : E)
    (words : List (List K)) (hq : List E) : WhirStateT :=
  glueT lam r.1 [(y, hy, fun x ↦ eqEval z x), (enfOf i r.2 qs lam words, hq,
    fun x ↦ Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x)]

/-- After the query group: the query intro polynomial, then the next level. -/
def midFinishJ (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ)
    (lam : E) (words : List (List K)) : VerifierProgram Unit :=
  (sumcheckRoundPoly 3 (enfOf i r.2 qs lam words) none).bind fun hq ↦
    whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) (glueMid μ i r z y hy qs lam words hq)

/-- After the fold rounds. -/
def midTailJ (r : WhirStateT × List E) : VerifierProgram Unit :=
  (readCommitment (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)).bind
    fun _ ↦
  (sampleChallenges (μ - r.1.folds.length)).bind fun z ↦ readScalar.bind fun y ↦
  (sumcheckRoundPoly 3 y none).bind fun hy ↦
  (grindPre g).bind fun _ ↦ (powCheck g).bind fun _ ↦
  (samplePositions per (μ - r.1.folds.length + level.logInvRate) level.queries).bind fun qs ↦
  sampleChallenge.bind fun lam ↦ (queryOpenings (cidx c₀ n₀ i) qs).bind fun words ↦
    midFinishJ μ ℓ₀ per c₀ n₀ g dir w i next rest r z y hy qs lam words

/-- The level, unfolded. -/
def midProgJ (s : WhirStateT) : VerifierProgram Unit :=
  (foldRoundsT level.fold s []).bind fun r ↦ midTailJ μ ℓ₀ per c₀ n₀ g dir w i level next rest r

/-- **`whirLevelsJ` on a level with a next commitment is `midProgJ`.** -/
theorem whirLevelsJ_mid (s : WhirStateT) :
    whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w i (level :: next :: rest) s =
      midProgJ μ ℓ₀ per c₀ n₀ g dir w i level next rest s := rfl

end Program

/-! ## Doom along the level -/

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)

/-- After the out-of-domain point: the next list is separated at `z`. -/
def OodC (r : WhirStateT × List E) (z : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidC μ ℓ₀ w i P P' ℓ ℓ' pre r cs ∧ z.length = P.κ ∧
    OodSep P' (rowsOf ℓ' (laneO (i + 1) cs P'.n)) z

/-- After the query group: every member of the next list violates the glued claim. -/
def GlueCJ (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E)
    (g : List ℕ × E × List (List K)) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (QuadOK hy y ∧ OodC μ ℓ₀ w i P P' ℓ ℓ' pre r z cs) ∧
    Viol P' (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []))
      (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []).target

end Doom

/-! ## Bookkeeping lemmas -/

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}

/-- Gluing two claims: the out-of-domain claim with `λ`, the consistency claims with `λ²`
(leanVM's `glue_two`). -/
theorem glue_twoJ (lam : E) (s : WhirStateT) (y e : E) (hy he : List E) (wy we : List E → E) :
    glueT lam s [(y, hy, wy), (e, he, we)] =
      { target := s.target + 1 * lam * y + 1 * lam * lam * e
        quad := List.zipWith (fun q i ↦ q + 1 * lam * lam * i)
          (List.zipWith (fun q i ↦ q + 1 * lam * i) s.quad hy) he
        folds := s.folds
        glued := s.glued ++
          [⟨1 * lam, s.folds.length, wy⟩, ⟨1 * lam * lam, s.folds.length, we⟩] } := by
  simp [glueT]

/-- The glued state's weight. -/
theorem glueMid_runW (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ)
    (lam : E) (words : List (List K)) (hq : List E) :
    runW w ℓ₀ (glueMid μ i r z y hy qs lam words hq) = fun x ↦ runW w ℓ₀ r.1 x +
      1 * lam * eqEval z x + 1 * lam * lam *
        Verifier.inducedWeight (μ - r.1.folds.length) qs (powers lam qs.length) x := by
  funext x
  rw [glueMid, glue_twoJ]
  have := runW_glue w ℓ₀ r.1 [⟨1 * lam, r.1.folds.length, fun x ↦ eqEval z x⟩,
    ⟨1 * lam * lam, r.1.folds.length, fun x ↦ Verifier.inducedWeight (μ - r.1.folds.length) qs
      (powers lam qs.length) x⟩] (by simp) x
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this
  rw [← add_assoc] at this
  exact this

/-- The glued state's target. -/
theorem glueMid_target (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ)
    (lam : E) (words : List (List K)) (hq : List E) :
    (glueMid μ i r z y hy qs lam words hq).target =
      r.1.target + 1 * lam * y + 1 * lam * lam * enfOf i r.2 qs lam words := by
  rw [glueMid, glue_twoJ]

/-- **The next level's doom** from the glued doom and the query intro polynomial. -/
theorem levelPre_nextJ (hP' : P'.κ + (pre + ℓ) + ℓ' = μ) (r : WhirStateT × List E) (z : List E)
    (y : E) (hy : List E) (g : List ℕ × E × List (List K)) (hq : List E)
    (cs : List (ℕ × ℕ × Word)) (hglue : GlueCJ μ ℓ₀ w i P P' ℓ ℓ' pre r z y hy g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    LevelPre μ ℓ₀ w (i + 1) P' ℓ' (pre + ℓ) (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq) cs := by
  obtain ⟨⟨hhy, ⟨cs₀, W', rfl, hW', haf⟩, hz, -⟩, hviol⟩ := hglue
  have hlen := afterFold_len haf
  have hκm := afterFold_κ haf
  obtain ⟨⟨⟨-, -, -, hg, hquad, -⟩, hshape⟩, -⟩ := haf
  refine ⟨⟨?_, by simp, hP', ?_, ?_, ?_⟩, ?_⟩
  · rw [glueMid, glue_twoJ]; simp [hlen]
  · intro c hc
    rw [glueMid, glue_twoJ] at hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rw [glueMid, glue_twoJ]
    rcases hc with hc | rfl | rfl
    · exact hg c hc
    · refine ⟨le_rfl, ?_⟩
      rw [hκm, ← hz]
      exact isMultiaffine_eqEval z
    · exact ⟨le_rfl, isMultiaffine_inducedWeight _ _ _ (length_powers _ _)⟩
  · rw [glueMid, glue_twoJ]
    exact quadOK_zipWith (quadOK_zipWith hquad hhy _) hhq _
  · have hr : runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq) =
        runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []) := by
      rw [glueMid_runW, glueMid_runW]
    have ht : (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq).target =
        (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []).target := by
      rw [glueMid_target, glueMid_target]
    simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil, hr, ht]
    exact hviol
  · refine ⟨by simp [hshape.1], W', ?_, ?_⟩
    · rw [List.getElem?_append_right (by rw [hshape.1]), hshape.1, Nat.sub_self]
      simp [wdOf]
    · simpa [wdOf] using hW'

end Lemmas

/-! ## The specification -/

/-- The arithmetic of a level with a next level (`MidHyp` without the next code's list bound). -/
structure MidHypJ (μ ℓ₀ per c₀ n₀ : ℕ) (w : List E → E) (P P' : LevelCode)
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

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P P' : LevelCode}
  {level next : Whir.Level} {rest : List Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- The query group of a level with a next level, followed by the query intro polynomial and
the next level. -/
noncomputable def midQuerySpecJ (H : MidHypJ μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hQlt : eQuery P P' level.queries < 1)
    (K : ∀ s', Spec (whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E) :
    Spec ((queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦
          midFinishJ μ ℓ₀ per c₀ n₀ g dir w i next rest r z y hy gg.1 gg.2.1 gg.2.2)
      (fun h ↦ QuadOK hy y ∧
        OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax ((2 : ENNReal)⁻¹ ^ g * eQuery P P' level.queries) 0 :=
  ((Spec.ofNoMove (p := queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i))
      (Pre := fun h ↦ QuadOK hy y ∧
        OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (viewC c₀ n₀ (commits h)))
      (Post := fun gg h ↦ GlueCJ μ ℓ₀ w i P P' level.fold next.fold pre r z y hy gg
        (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_queryFragG _ _ _ _ _).noMove
      ((grind_disc_le g _).trans_lt hQlt) fun h₀ hp ↦ by
        obtain ⟨cs₀, hW, -, -, haf⟩ := midC_word hp.2.1
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
        refine escRet_queryFragG_le g hg P P' hκ' per level.queries (cidx c₀ n₀ i) H.hper H.hpd
          h₀ hW' (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) P'.n)) _
          (runW w ℓ₀ r.1) r.1.target z y hviol hp.2.2.2
          (fun gg cs ↦ GlueCJ μ ℓ₀ w i P P' level.fold next.fold pre r z y hy gg (viewC c₀ n₀ cs))
          fun qs lam hr hlen hv ↦ ⟨hp, ?_⟩
        rw [glueMid_runW, glueMid_target, enfOf_eq haf.1.2 r.2 hlf qs hr lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun gg ↦
    (roundPolyInv (fun cs ↦ GlueCJ μ ℓ₀ w i P P' level.fold next.fold pre r z y hy gg
        (viewC c₀ n₀ cs)) (enfOf i r.2 gg.1 gg.2.1 gg.2.2) (T := εmax) le_rfl).bind' fun hq ↦
      (K (glueMid μ i r z y hy gg.1 gg.2.1 gg.2.2 hq)).mono
        (fun h hp ↦ levelPre_nextJ H.hP' r z y hy gg hq _ hp.2 hp.1) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl

/-- After the fold rounds of a level with a next level: the commitment, the out-of-domain group
(`escRet_sampleN_le`), the OOD answer and intro polynomial, the moves before the proof of work,
and the query group. -/
noncomputable def midTailSpecJ (H : MidHypJ μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hεO : eOod P' P.κ ≤ εmax) (hOlt : eOod P' P.κ < 1) (hQlt : eQuery P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQuery P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec (midTailJ μ ℓ₀ per c₀ n₀ g dir w i level next rest r)
      (fun h ↦ AfterFold μ ℓ₀ w i P level.fold pre r (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax 0 0 :=
  (commitInv (fun cs ↦ AfterFold μ ℓ₀ w i P level.fold pre r (viewC c₀ n₀ cs))
      (fun cs ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ cs))
      (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
      (fun cs W h hW ↦ by
        rw [viewC_append (le_length_of_viewC (ne_nil_of_shapeOK h.1.2))]
        exact midC_of_commit next rfl H.hP' H.hR' h hW)
      (T := eOod P' P.κ) hεO).bind' fun _ ↦
  ((Spec.ofNoMove (p := sampleChallenges (μ - r.1.folds.length))
      (Pre := fun h ↦ MidC μ ℓ₀ w i P P' level.fold next.fold pre r (viewC c₀ n₀ (commits h)))
      (Post := fun z h ↦ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z
        (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_sampleN _).noMove hOlt fun h₀ hp ↦ by
        obtain ⟨cs₀, -, -, -, haf⟩ := midC_word hp
        have hκm := afterFold_κ haf
        have hκ : μ - r.1.folds.length = next.fold + P'.κ := by
          rw [hκm]; have := H.hP; have := H.hP'; omega
        have hκ1 : 1 ≤ μ - r.1.folds.length := by rw [hκm]; exact P.hκ
        refine (escRet_sampleN_le P' hκ hκ1
          (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) P'.n))
          (fun z cs ↦ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (viewC c₀ n₀ cs)) h₀
          fun z hz hsep ↦ ⟨hp, hz.trans hκm, hsep⟩).trans (by rw [hκm])).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun z ↦
  (readInv (fun cs ↦ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (viewC c₀ n₀ cs))
      (T := 0) zero_le).bind' fun y ↦
  (roundPolyInv (fun cs ↦ OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (viewC c₀ n₀ cs)) y
      (T := (2 : ENNReal)⁻¹ ^ g * eQuery P P' level.queries) hεQ).bind' fun hy ↦
  (grindPreInv (fun cs ↦ QuadOK hy y ∧
      OodC μ ℓ₀ w i P P' level.fold next.fold pre r z (viewC c₀ n₀ cs)) g hεQ).bind' fun _ ↦
  (midQuerySpecJ H hg hQlt K r z y hy).congr
    (query_bindG per g (cidx c₀ n₀ i) (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ midFinishJ μ ℓ₀ per c₀ n₀ g dir w i next rest r z y hy qs lam words).symm

/-- **The specification of a level with a next level** (Johnson regime). -/
noncomputable def midSpecJ (H : MidHypJ μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hεF : eFold P level.fold ≤ εmax) (hεO : eOod P' P.κ ≤ εmax) (hOlt : eOod P' P.κ < 1)
    (hQlt : eQuery P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQuery P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (s : WhirStateT) :
    Spec (whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w i (level :: next :: rest) s)
      (fun h ↦ LevelPre μ ℓ₀ w i P level.fold pre s (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0 :=
  (((foldRoundsSpec μ ℓ₀ w i P level.fold pre (viewC c₀ n₀)
      (fun cs ↦ ShapeOK i P level.fold (viewC c₀ n₀ cs)) H.hw H.hℓ₀ hεF level.fold s []).bind'
      fun r ↦ midTailSpecJ H hg hεO hOlt hQlt hεQ K r).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirLevelsJ_mid μ ℓ₀ per c₀ n₀ g dir w i level next rest s).symm

end
end LeanVM.Protocol.Whir.Sound
