-- New for lvm2 (WP JB-L): the Johnson-regime instance of `CodeFacts` (`LvmMcaUd`), from the vendored longfellow
-- port (`LvmJB*`, Apache-2.0, `LICENSE-longfellow`). The glue from `rsCode` to JB's `RSeval`/`LinearCode` forms
-- follows Flock's PJB instance file (`docs/v4/flock-pcs/model/PJB-files/JBInstRS.lean` @ archive/pcs/AGG).
import LvmMcaUd
import LvmJBStrongMutual
import LvmJBCTInterleavedJohnson

/-!
# The code facts of a WHIR level at the Johnson radius

`CodeFacts (rsCode domain k) k A L M` (`LvmMcaUd`) is the per-level hypothesis of the WHIR
round-by-round analysis: uniqueness at `k` points, `k ≤ A`, a list bound `L` at agreement `A`, and
a per-row-pair MCA count `M` (the fold-list count is `|ρ|·M`). This module proves it at the
Johnson radius from two theorems of longfellow-zk's formalisation (vendored as `LvmJB*`):

* **the MCA count**: `JBAgreement.strong_mutual_johnson` (Haböck's strong mutual correlated
  agreement): for `2 ≤ k`, `0 < η ≤ 1/4`, `1 ≤ η n` and agreement `A = n − e` with
  `(k − 1) n ≤ (A − 4 η n)²`, fewer than `johnsonThreshold k n e η` challenges `z` admit an
  unexplained proximate. `mcaBad_hasUnexplainedProximate`: our `McaBad C A u₀ u₁ z` is such a
  challenge for `e = n − A`, so `M ≥ johnsonThreshold k n (n − A) η` bounds the MCA event;
* **the list bound**: `JB.CodingTheory.InterleavedJohnson.card_le_listBound` for any linear code
  of minimum distance `d` (here `d = n − k + 1`, `rsCode_minDist`), interleaved, column errors
  `E = n − A`: at most `listBound n d E = ⌊n (d − E) / (n d − 2 n E + E²)⌋` members.

`codeFacts_johnson` assembles them; the hypotheses are closed-form arithmetic on `n, k, A, η, L, M`,
checked per level by `norm_num` (`LvmWhirCodeJ`).
-/

namespace LeanVM.Protocol.Whir

open Finset Polynomial JBAgreement JB.CodingTheory JB.CodingTheory.InterleavedJohnson

section Johnson

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `rsCode` as JB's `LinearCode` on `Fin n` (the same submodule). -/
theorem rsCode_minDist {n : ℕ} (domain : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    HasMinimumDistanceAtLeast (rsCode domain k) (n - k + 1) := by
  refine ⟨by omega, fun c hc hc0 ↦ ?_⟩
  by_contra hlt
  apply hc0
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i ↦ c i = 0)
  have hw : weight c = (univ.filter fun i : Fin n ↦ ¬ c i = 0).card := rfl
  rw [card_univ, Fintype.card_fin] at hsplit
  refine eq_of_mem_code_of_agreeOn domain hc (Submodule.zero_mem _) (univ.filter fun i ↦ c i = 0)
    (by omega) fun x hx ↦ ?_
  exact (mem_filter.mp hx).2

/-- **Our MCA event is JB's**: an `McaBad` challenge at agreement `A` has an unexplained proximate
within distance `n − A`. -/
theorem mcaBad_hasUnexplainedProximate {n : ℕ} (domain : Fin n ↪ F) {k A : ℕ} (u₀ u₁ : Fin n → F)
    (z : F) (hk : 1 ≤ k) (h : McaBad (rsCode domain k) A u₀ u₁ z) :
    HasUnexplainedProximate domain u₀ u₁ k (n - A) z := by
  obtain ⟨S, hS, ⟨c, hc, hcS⟩, hno⟩ := h
  obtain ⟨p, hp, hpc⟩ := mem_rsCode_iff_eval.mp hc
  refine ⟨p, ?_, ?_, ?_⟩
  · rcases eq_or_ne p 0 with rfl | h0
    · simp; omega
    · exact (natDegree_lt_iff_degree_lt h0).2 hp
  · calc (disagree (fun x ↦ u₀ x + z * u₁ x) (RSeval domain p)).card ≤ Sᶜ.card :=
          card_le_card fun x hx ↦ mem_compl.mpr fun hxS ↦
            (mem_filter.mp hx).2 (by rw [RSeval_apply, hpc]; exact hcS x hxS)
      _ = n - S.card := by rw [card_compl, Fintype.card_fin]
      _ ≤ n - A := by omega
  · rintro p₀ p₁ h₀ h₁ ⟨-, hex⟩
    refine hno ⟨fun x ↦ p₀.eval (domain x), eval_mem_rsCode domain ?_,
      fun x ↦ p₁.eval (domain x), eval_mem_rsCode domain ?_, fun x hx ↦ hex x ?_⟩
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast h₀)
    · exact degree_le_natDegree.trans_lt (by exact_mod_cast h₁)
    · rw [hpc, hcS x hx]

open Classical in
/-- **The MCA count at the Johnson radius** (`strong_mutual_johnson`). -/
theorem card_mcaBad_le_johnson {n : ℕ} (domain : Fin n ↪ F) {k A M : ℕ} (η : ℝ)
    (hk2 : 2 ≤ k) (hAn : A ≤ n) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hηn : 1 ≤ η * n)
    (ht4 : 4 * η * n ≤ A) (hJ : ((k - 1 : ℕ) : ℝ) * n ≤ ((A : ℝ) - 4 * η * n) ^ 2)
    (hM : johnsonThreshold k n (n - A) η ≤ M) (u₀ u₁ : Fin n → F) :
    (univ.filter fun z ↦ McaBad (rsCode domain k) A u₀ u₁ z).card ≤ M := by
  have hsub : (univ.filter fun z ↦ McaBad (rsCode domain k) A u₀ u₁ z) ⊆
      univ.filter fun z ↦ HasUnexplainedProximate domain u₀ u₁ k (n - A) z := fun z hz ↦
    mem_filter.mpr ⟨mem_univ _,
      mcaBad_hasUnexplainedProximate domain u₀ u₁ z (by omega) (mem_filter.mp hz).2⟩
  have hnA : n - (n - A) = A := Nat.sub_sub_self hAn
  have hlt := strong_mutual_johnson (ι := Fin n) domain domain.injective u₀ u₁ k (n - A) η hk2 hη
    hη4 (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin, hnA])
    (by rwa [Fintype.card_fin, hnA])
  rw [Fintype.card_fin] at hlt
  have hc : ((univ.filter fun z ↦ McaBad (rsCode domain k) A u₀ u₁ z).card : ℝ) < M :=
    ((Nat.cast_le.mpr (card_le_card hsub)).trans_lt hlt).trans_le hM
  exact_mod_cast hc.le

/-- **The list bound at the Johnson radius** (`card_le_listBound`). -/
theorem card_iList_le_johnson {n : ℕ} (domain : Fin n ↪ F) {k A L : ℕ} (hk : 1 ≤ k) (hkA : k ≤ A)
    (hAn : A ≤ n) (hden : 0 < denominator n (n - k + 1) (n - A))
    (hL : listBound n (n - k + 1) (n - A) ≤ L) {ρ : Type} [Fintype ρ] (O : ρ → Fin n → F) :
    (iList (rsCode domain k) A O).card ≤ L := by
  refine (card_le_listBound (rsCode domain k) O (iList (rsCode domain k) A O)
    (rsCode_minDist domain hk (hkA.trans hAn)) (fun U hU ↦ ((mem_iList _ _ _ _).mp hU).1)
    (fun U hU ↦ ?_) (Nat.sub_le n A) (by omega) hden).trans hL
  obtain ⟨S, hS, hagree⟩ := ((mem_iList _ _ _ _).mp hU).2
  calc (matrixErrorCoordinates O U).card ≤ Sᶜ.card :=
        card_le_card fun x hx ↦ mem_compl.mpr fun hxS ↦ by
          obtain ⟨r, hr⟩ := (mem_filter.mp hx).2
          exact hr (hagree r x hxS)
    _ = n - S.card := by rw [card_compl, Fintype.card_fin]
    _ ≤ n - A := by omega

/-- **The code facts at the Johnson radius**: `RS[F, domain, k]` on `n` points at agreement
threshold `A`, with JB's slack `η`, list bound `L ≥ listBound n (n−k+1) (n−A)` and MCA count
`M ≥ johnsonThreshold k n (n−A) η`. -/
theorem codeFacts_johnson {n : ℕ} (domain : Fin n ↪ F) {k A L M : ℕ} (η : ℝ)
    (hk2 : 2 ≤ k) (hkA : k ≤ A) (hAn : A ≤ n) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hηn : 1 ≤ η * n)
    (ht4 : 4 * η * n ≤ A) (hJ : ((k - 1 : ℕ) : ℝ) * n ≤ ((A : ℝ) - 4 * η * n) ^ 2)
    (hM : johnsonThreshold k n (n - A) η ≤ M)
    (hden : 0 < denominator n (n - k + 1) (n - A)) (hL : listBound n (n - k + 1) (n - A) ≤ L) :
    CodeFacts (rsCode domain k) k A L M where
  uniq _ hc _ hc' S hS h := eq_of_mem_code_of_agreeOn domain hc hc' S hS h
  k_le_thr := hkA
  card_iList_le _ _ O := card_iList_le_johnson domain (by omega) hkA hAn hden hL O
  card_foldBad_le _ _ O := by
    classical
    refine card_foldBad_le_of_mca _
      (fun _ hc _ hc' S hS h ↦ eq_of_mem_code_of_agreeOn domain hc hc' S (hkA.trans hS) h)
      (fun u₀ u₁ ↦ ?_) O
    convert card_mcaBad_le_johnson domain η hk2 hAn hη hη4 hηn ht4 hJ hM u₀ u₁

end Johnson

end LeanVM.Protocol.Whir
