-- New for lvm2 (X-REC2-CERT, stage S4): the doom of a WHIR level's next commitment created at that
-- commitment. Adapted from WP-7's `LvmWhirEscape` (`exists_agreeSet_ud`), `LvmWhirGroupEscape`
-- (`escRet_queryFrag_le_ud`) and `LvmWhirLevelMidSpec` (`midQuerySpec`, `midTailSpec`): the proofs
-- are theirs with the level's own doom (`Viol` of the folded word) replaced by the weaker `FarU`.
import LvmWhirDoom2

/-!
# The next commitment's doom

WP-7's query step (`exists_agreeSet_ud`) uses the level's doom (every member of the folded word's
list violates the running claim) only through one consequence: **every member `V` of the next
oracle's list that meets the running claim has a level-`i` encoding that agrees with the folded word
on fewer than `thr` columns** (`FarU`). Both the level's doom (`farU_of_viol`) and the level-1
commitment's doom of the extractor (`MidDoomUd`, `farU_of_midDoom`) imply it.

* `exists_agreeSet_far`, `escRet_queryFrag_le_far`: the query step and the query group's escape
  `eQueryUd` from `FarU`.
* `FarC`: after the commitment of the next oracle, the bookkeeping of the fold rounds (`FinBook`)
  and `FarU` of the next oracle's rows against the folded word. `GlueFarC`: after the query group,
  every member of the next list violates the glued claim; with the query intro polynomial it is
  `LevelPre` of the next level (`levelPre_next_far`).
* `midQuerySpecFar`: WP-7's `midQuerySpec` from `FarC`.
* **`midTailFarSpec`**: after the fold rounds, from no doom: the doom is created at the next
  commitment iff `FarC` holds (`Spec.commitP`), then the query group and the next level.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## The query step from `FarU` -/

/-- **Every member of the next list that meets the running claim is far** from the folded word
`C`: its level-`i` encoding agrees with `C` on fewer than `thr` columns. -/
def FarU (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ →
    (univ.filter fun x ↦ enc P.κ P.R (joinMsg hκ (decode P' V)) x = C x).card < P.thr

/-- The level's doom implies `FarU`. -/
theorem farU_of_viol (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) : FarU P P' hκ Q' C Φ σ := by
  intro V _ hclaim
  by_contra hlt
  exact viol_of_close P C Φ σ hviol _ (not_lt.mp hlt) (by rw [sum_joinMsg]; exact hclaim)

/-- The extractor's level-1 commitment doom implies `FarU`. -/
theorem farU_of_midDoom (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hD : MidDoomUd (R₀ := P.R) P.thr P' hκ C Q') : FarU P P' hκ Q' C Φ σ :=
  fun V hV _ ↦ hD V hV

/-- **The query step from `FarU`** (WP-7's `exists_agreeSet_ud`, same proof). -/
theorem exists_agreeSet_far (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hfar : FarU P P' hκ Q' C Φ σ) (hone : (iList P'.code P'.thr Q').card ≤ 1) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodUd P P' hκ Q' C Φ σ qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ
  · obtain ⟨V₀, hV₀, hclaim⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · exact Nat.succ_le_of_lt (hfar V₀ hV₀ hclaim)
    · intro hlt
      simp only [QueryGoodUd, not_forall, not_or, not_not, exists_prop, not_exists,
        not_and] at hqs
      obtain ⟨V, hV, -, hall⟩ := hqs
      have hVV : V = V₀ := Finset.card_le_one.mp hone _ hV _ hV₀
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV
    exact Or.inl fun h ↦ hex ⟨V, hV, h⟩

open Classical in
/-- **The query group's escape from `FarU`** (WP-7's `escRet_queryFrag_le_ud`, same proof). -/
theorem escRet_queryFrag_le_far (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hfar : FarU P P' hκ Q' C Φ σ)
    (hone : (iList P'.code P'.thr Q').card ≤ 1)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQueryUd P P' t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_far P P' hκ Q' C Φ σ hfar hone
  refine (retExp_queryFrag_le per (P.κ + P.R) t c hper hpd h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A)
    (((t * P'.listMax : ℕ) : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGoodUd P P' hκ Q' C Φ σ qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le_ud P P' hκ Q' C Φ σ qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦ ¬ Viol P' Q'
          (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
          (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact fun hv ↦ hlam (hJ qs lam hr hlen hv)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQueryUd]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

open Classical in
/-- **The query group's escape from `FarU`, with the proof of work** (S2J's PI-GRIND:
`escRet_queryFragG_le_ud`'s argument): `2^-g · eQueryUd`. -/
theorem escRet_queryFragG_le_far (g : ℕ) (hg : g ≤ 192) (P P' : LevelCode) {ℓ' : ℕ}
    (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ) (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hfar : FarU P P' hκ Q' C Φ σ)
    (hone : (iList P'.code P'.thr Q').card ≤ 1)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFragG g per (P.κ + P.R) t c) ≤
      (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' t := by
  refine escRet_powCheck_le g hg _ h₀ _ _ fun h hh ↦ ?_
  rw [← hh] at hW
  refine escRet_queryFrag_le_far P P' hκ per t c hper hpd h hW Q' C Φ σ hfar hone
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

/-! ## The doom after the next commitment -/

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)
  (hκ : P.κ = ℓ' + P'.κ)

/-- **After the commitment of the next oracle**: the fold rounds' bookkeeping and `FarU` of the
next oracle's rows against the folded word. -/
def FarC (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ cs₀ W', cs = cs₀ ++ [(P'.κ + P'.R, 3 * 2 ^ ℓ', W')] ∧ WellShaped (3 * 2 ^ ℓ') W' ∧
    FinBook μ i P ℓ pre r cs₀ ∧
    FarU P P' hκ (rowsOf ℓ' (laneO (i + 1) cs P'.n)) (foldedW i P r cs₀) (runW w ℓ₀ r.1)
      r.1.target

/-- After the query group: `FarC`, and every member of the next list violates the glued claim. -/
def GlueFarC (r : WhirStateT × List E) (g : List ℕ × E × List (List K))
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  FarC μ ℓ₀ w i P P' ℓ ℓ' pre hκ r cs ∧
    Viol P' (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueLv μ i r g.1 g.2.1 g.2.2 []))
      (glueLv μ i r g.1 g.2.1 g.2.2 []).target

end Doom

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}
  {hκ : P.κ = ℓ' + P'.κ}

/-- The commitments after the next commitment, at index `i`. -/
theorem farC_word {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : FarC μ ℓ₀ w i P P' ℓ ℓ' pre hκ r cs) :
    ∃ cs₀, cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs₀ i) ∧ FinBook μ i P ℓ pre r cs₀ := by
  obtain ⟨cs₀, W', rfl, -, hb, -⟩ := h
  exact ⟨cs₀, shapeOK_append hb.2.1 _, hb⟩

/-- **The next level's doom** from the glued doom and the query intro polynomial (WP-7's
`levelPre_next`, from the bookkeeping only). -/
theorem levelPre_next_far (hP' : P'.κ + (pre + ℓ) + ℓ' = μ) (r : WhirStateT × List E)
    (g : List ℕ × E × List (List K)) (hq : List E) (cs : List (ℕ × ℕ × Word))
    (hglue : GlueFarC μ ℓ₀ w i P P' ℓ ℓ' pre hκ r g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    LevelPre μ ℓ₀ w (i + 1) P' ℓ' (pre + ℓ) (glueLv μ i r g.1 g.2.1 g.2.2 hq) cs := by
  obtain ⟨⟨cs₀, W', rfl, hW', ⟨⟨hl, -, -, hg, hquad⟩, hshape, hlf⟩, -⟩, hviol⟩ := hglue
  have hlen : r.1.folds.length = pre + ℓ := by omega
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

end Lemmas

/-! ## The specifications -/

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P P' : LevelCode}
  {level next : Whir.Level} {rest : List Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- The query group of a level with a next level, from `FarC` (WP-7's `midQuerySpec`, with S2J's
proof of work). -/
noncomputable def midQuerySpecFar (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hκ : P.κ = next.fold + P'.κ) (hQlt : eQueryUd P P' level.queries < 1)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec ((queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦
          midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r gg.1 gg.2.1 gg.2.2)
      (fun h ↦ FarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax ((2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries) 0 :=
  ((Spec.ofNoMove (p := queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i))
      (Pre := fun h ↦ FarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r (viewC c₀ n₀ (commits h)))
      (Post := fun gg h ↦ GlueFarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r gg
        (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_queryFragG _ _ _ _ _).noMove
      ((grind_disc_le g _).trans_lt hQlt) fun h₀ hp ↦ by
        have hp' := hp
        obtain ⟨cs₀, W₁, hcs, -, hb, hfar⟩ := hp'
        have hW : (viewC c₀ n₀ (commits h₀))[i]? = some (P.κ + P.R, wdOf i level.fold,
            wordOf cs₀ i) := by rw [hcs]; exact shapeOK_append hb.2.1 _
        have hκm := finBook_κ hb
        have hd : μ - r.1.folds.length + level.logInvRate = P.κ + P.R := by rw [hκm, H.hR]
        have hlf : r.2.length = level.fold := hb.2.2
        have hW' := commits_cidx H.hc hW
        rw [hd]
        refine escRet_queryFragG_le_far g hg P P' hκ per level.queries (cidx c₀ n₀ i) H.hper H.hpd
          h₀ hW' (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) P'.n)) _
          (runW w ℓ₀ r.1) r.1.target hfar ((P'.card_iList_le _).trans H.hL')
          (fun gg cs ↦ GlueFarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r gg (viewC c₀ n₀ cs))
          fun qs lam hr hlen hv ↦ ⟨hp, ?_⟩
        rw [glueLv_runW, glueLv_target, enfOf_eq hb.2.1 r.2 hlf qs hr lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun gg ↦
    (roundPolyInv (fun cs ↦ GlueFarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r gg
        (viewC c₀ n₀ cs))
        (enfOf i r.2 gg.1 gg.2.1 gg.2.2) (T := εmax) le_rfl).bind' fun hq ↦
      (K (glueLv μ i r gg.1 gg.2.1 gg.2.2 hq)).mono
        (fun h hp ↦ levelPre_next_far H.hP' r gg hq _ hp.2 hp.1) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl

/-- **After the fold rounds of a level with a next level, from no doom**: the doom is created at
the next commitment iff `FarC` holds; then the moves before the proof of work (S2J's `grindPre`),
the query group with the proof of work and the next level (`K`). -/
noncomputable def midTailFarSpec (H : MidHyp μ ℓ₀ per c₀ n₀ w P P' level next pre) (hg : g ≤ 192)
    (hκ : P.κ = next.fold + P'.κ) (hQlt : eQueryUd P P' level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' level.queries ≤ εmax)
    (K : ∀ s', Spec (whirLevelsUd μ ℓ₀ per c₀ n₀ g dir w (i + 1) (next :: rest) s')
      (fun h ↦ LevelPre μ ℓ₀ w (i + 1) P' next.fold (pre + level.fold) s'
        (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax εmax 0)
    (r : WhirStateT × List E) :
    Spec (midTail μ ℓ₀ per c₀ n₀ g dir w i level next rest r) (fun _ ↦ False)
      (fun _ _ ↦ False) εmax 0 0 :=
  (Spec.commitP (Pre := fun _ ↦ False)
      (Post := fun _ h ↦ FarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r
        (viewC c₀ n₀ (commits h)))
      (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
      (fun _ _ h _ ↦ h.elim) hεQ).bind' fun _ ↦
  (grindPreInv (fun cs ↦ FarC μ ℓ₀ w i P P' level.fold next.fold pre hκ r (viewC c₀ n₀ cs)) g
      hεQ).bind' fun _ ↦
  (midQuerySpecFar H hg hκ hQlt K r).congr
    (query_bindG per g (cidx c₀ n₀ i) (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ midFinish μ ℓ₀ per c₀ n₀ g dir w i next rest r qs lam words).symm

end
end LeanVM.Protocol.Whir.Sound
