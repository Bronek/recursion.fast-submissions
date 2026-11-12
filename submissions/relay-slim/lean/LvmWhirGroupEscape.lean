-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/GroupEscape.lean` (formal rev 40f877dc) as
-- `LvmWhirGroupEscape` for lvm (WP-7). Changed for the unique-decoding regime: the out-of-domain group
-- (`escRet_sampleN_le`) is cut; `escRet_queryFrag_le` becomes `escRet_queryFrag_le_ud` (the one candidate from the
-- list bound, escape `eQueryUd`); the final level's group starts from the residual's doom `FinViol`
-- (`escRet_queryFrag_le_finViol`); the positions are `samplePositions per` of commitment index `c`.
/-
  LeanVM.Protocol.Whir.Sound.GroupEscape

  The escape expectations of a WHIR level's query group (positions, `λ`, openings), in the form
  `Spec.ofNoMove` consumes, on a level with a next commitment and on the final level.
-/


import LvmWhirDefs

/-!
# Escapes of the query group

* `escRet_queryFrag_le_ud`: the query group escapes the glued claim's doom with probability at most
  `eQueryUd P P' t = ((A − 1)/n)^t + t·L'/|E|`: the positions avoid the agreement set of the one
  candidate except with probability `((A − 1)/n)^t` (`exists_agreeSet_ud`,
  `retExp_queryFrag_le`), and then `λ` escapes at at most `t·L'` values (`card_lambda_bad_le_ud`).
* `escRet_queryFrag_le_finViol`: the final level's `((A − 1)/n)^t + t/|E|`, from the residual's
  doom (`exists_agreeSet_finViol`).

The groups' posts are functions of the values and of the commitments, which a group does not
change (`retExp_commits`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-- The average of an indicator is the fraction of its support. -/
theorem avg_ite_le (p : E → Prop) [DecidablePred p] :
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, (if p c then 0 else 1 : ENNReal) =
      (Fintype.card E : ENNReal)⁻¹ * ((univ.filter fun c ↦ ¬ p c).card : ENNReal) := by
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases h : p c <;> simp [h]

/-- The count of the positions in the agreement set. -/
theorem card_filter_mem {n : ℕ} (A : Finset (Fin n)) :
    (univ.filter fun j : Fin n ↦ ∀ h : (j : ℕ) < n, (⟨j, h⟩ : Fin n) ∈ A).card = A.card := by
  congr 1
  ext j
  simp

/-- `((|A|)/n)^t ≤ ((thr − 1)/n)^t` for `|A| + 1 ≤ thr`. -/
theorem pow_frac_le (P : LevelCode) (A : Finset (Fin P.n)) (hA : A.card + 1 ≤ P.thr) (t : ℕ) :
    ((A.card : ENNReal) / 2 ^ (P.κ + P.R)) ^ t ≤ (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t := by
  have hn : ((P.n : ℕ) : ENNReal) = 2 ^ (P.κ + P.R) := by simp [LevelCode.n]
  rw [hn]
  gcongr
  exact_mod_cast (show A.card ≤ P.thr - 1 by omega)

open Classical in
/-- **The query group of a level with a next commitment** (unique decoding). -/
theorem escRet_queryFrag_le_ud (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
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
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_ud P P' hκ Q' C Φ σ hviol hone
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
/-- **The query group of the final level**, from the residual's doom `FinViol`. -/
theorem escRet_queryFrag_le_finViol (P : LevelCode) (per t c : ℕ) (hper : 1 ≤ per)
    (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (hD : FinViol P C Φ σ G)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
          (bitsL x)) * G x ≠
        σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k] →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQueryFinal P t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_finViol P C Φ σ G hD
  refine (retExp_queryFrag_le per (P.κ + P.R) t c hper hpd h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) ((t : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGoodFinal P C Φ σ G qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le_final P C Φ σ G qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦
          ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
            (bitsL x)) * G x =
          σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        by_contra hne
        exact hlam (hJ qs lam hr hlen hne)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQueryFinal]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

end
end LeanVM.Protocol.Whir.Sound
