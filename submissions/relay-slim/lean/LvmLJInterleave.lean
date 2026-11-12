-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/LJInterleave.lean` @ 1b74a2a2 (archive/pcs/S1P) (Flock LJ1/LJ2, on the
-- longfellow port `LvmJB*`, Apache License 2.0, see `LICENSE-longfellow`). Changed: imports `JB*`/`LJ*`
-- renamed `LvmJB*`/`LvmLJ*`; nothing else.
-- LJ1: SJ §5.1 (L1) the interleaving lift `strong_mutual_johnson_interleaved`, statement verbatim from
-- SJStmts.lean. Proof: pack the `m` rows into one word over an extension `L ⊃ K` of degree `m` along a
-- `K`-basis, and apply PJB's `strong_mutual_johnson` over `L` at `algebraMap ∘ dom`.
import LvmLJDefs

open Polynomial Finset JBAgreement

namespace LJ

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Pack

variable {L : Type*} [Field L] [Algebra K L] {m : ℕ} (b : Module.Basis (Fin m) K L)

/-- `m` rows over `K` as one word over `L`. -/
noncomputable def packW (U : Fin m → ι → K) : ι → L := fun x => ∑ r, U r x • b r

/-- `m` polynomials over `K` as one polynomial over `L`. -/
noncomputable def packP (P : Fin m → K[X]) : L[X] := ∑ r, C (b r) * (P r).map (algebraMap K L)

/-- The `r`-th `K`-coordinate polynomial of a polynomial over `L`. -/
noncomputable def unpackP (p : L[X]) (r : Fin m) : K[X] :=
  ∑ j ∈ range (p.natDegree + 1), monomial j (b.repr (p.coeff j) r)

omit [Fintype K] [DecidableEq K] in
theorem smul_basis_eq (c : K) (r : Fin m) : b r * algebraMap K L c = c • b r := by
  rw [Algebra.smul_def, mul_comm]

omit [Fintype K] [DecidableEq K] in
theorem sum_smul_basis_iff {c c' : Fin m → K} : ∑ r, c r • b r = ∑ r, c' r • b r ↔ c = c' := by
  refine ⟨fun h => b.equivFun.symm.injective ?_, fun h => h ▸ rfl⟩
  simpa only [Module.Basis.equivFun_symm_apply] using h

omit [Fintype K] [DecidableEq K] in
theorem coeff_packP (P : Fin m → K[X]) (j : ℕ) : (packP b P).coeff j = ∑ r, (P r).coeff j • b r := by
  simp only [packP, finsetSum_coeff, coeff_C_mul, coeff_map, smul_basis_eq]

omit [Fintype K] [DecidableEq K] in
theorem coeff_unpackP (p : L[X]) (r : Fin m) (j : ℕ) : (unpackP b p r).coeff j = b.repr (p.coeff j) r := by
  simp only [unpackP, finsetSum_coeff, coeff_monomial, sum_ite_eq', mem_range]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero, Finsupp.coe_zero, Pi.zero_apply]

omit [Fintype K] [DecidableEq K] in
theorem packP_unpackP (p : L[X]) : packP b (unpackP b p) = p := by
  ext j
  rw [coeff_packP]
  simp only [coeff_unpackP]
  exact b.sum_repr (p.coeff j)

omit [Fintype K] [DecidableEq K] in
theorem packP_injective {P P' : Fin m → K[X]} (h : packP b P = packP b P') : P = P' := by
  funext r
  ext j
  have hj := congrArg (fun p => p.coeff j) h
  simp only [coeff_packP] at hj
  exact congrFun ((sum_smul_basis_iff b).1 hj) r

omit [Fintype K] [DecidableEq K] in
theorem natDegree_unpackP_lt {p : L[X]} {k : ℕ} (hp : p.natDegree < k) (r : Fin m) :
    (unpackP b p r).natDegree < k :=
  lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun _ hj =>
    (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (mem_range.1 hj))) hp

omit [Fintype K] [DecidableEq K] in
theorem natDegree_packP_lt {P : Fin m → K[X]} {k : ℕ} (hk : 1 ≤ k) (hP : ∀ r, (P r).natDegree < k) :
    (packP b P).natDegree < k := by
  have : (packP b P).natDegree ≤ k - 1 :=
    natDegree_sum_le_of_forall_le _ _ fun r _ =>
      (natDegree_C_mul_le _ _).trans ((natDegree_map_le).trans (by have := hP r; omega))
  omega

omit [Fintype K] [DecidableEq K] in
theorem eval_packP (P : Fin m → K[X]) (a : K) :
    (packP b P).eval (algebraMap K L a) = ∑ r, (P r).eval a • b r := by
  simp only [packP, eval_finsetSum, eval_mul, eval_C, eval_map_apply, smul_basis_eq]

omit [Fintype K] [DecidableEq K] in
theorem packP_line (P₀ P₁ : Fin m → K[X]) (z : K) :
    packP b (fun r => P₀ r + C z * P₁ r) = packP b P₀ + C (algebraMap K L z) * packP b P₁ := by
  ext j
  simp only [coeff_add, coeff_C_mul, coeff_packP, add_smul, mul_smul, sum_add_distrib, mul_sum,
    Algebra.smul_def z]

omit [Fintype K] [DecidableEq K] [DecidableEq ι] in
theorem packW_line (U₀ U₁ : Fin m → ι → K) (z : K) (x : ι) :
    packW b U₀ x + algebraMap K L z * packW b U₁ x = ∑ r, (U₀ r x + z * U₁ r x) • b r := by
  simp only [packW, add_smul, mul_smul, sum_add_distrib, mul_sum, Algebra.smul_def z]

/-- A row-wise unexplained proximate at `z ∈ K` packs to an unexplained proximate over `L`. -/
theorem hasUnexplainedProximate_pack [Fintype L] [DecidableEq L] (dom : ι → K) (U₀ U₁ : Fin m → ι → K)
    (k e : ℕ) (hk : 1 ≤ k) (z : K) (h : iHasUnexplainedProximate dom U₀ U₁ k e z) :
    HasUnexplainedProximate (fun x => algebraMap K L (dom x)) (packW b U₀) (packW b U₁) k e
      (algebraMap K L z) := by
  obtain ⟨P, hP, hcl, hun⟩ := h
  refine ⟨packP b P, natDegree_packP_lt b hk hP, ?_, ?_⟩
  · -- column disagreement is `L`-Hamming disagreement
    refine le_of_eq_of_le (congrArg Finset.card ?_) hcl
    ext x
    rw [mem_disagree, mem_colDisagree, RSeval_apply, packW_line, eval_packP, Ne,
      sum_smul_basis_iff, funext_iff]
    simp only [not_forall, evalRows]
  · intro p₀ p₁ hp₀ hp₁ hexp
    apply hun (unpackP b p₀) (unpackP b p₁) (natDegree_unpackP_lt b hp₀) (natDegree_unpackP_lt b hp₁)
    refine ⟨fun r => ?_, fun x hx r => ?_⟩
    · refine congrFun (packP_injective b (P' := fun r => unpackP b p₀ r + C z * unpackP b p₁ r) ?_) r
      rw [packP_line, packP_unpackP, packP_unpackP]
      exact hexp.1
    · have hL : packW b U₀ x + algebraMap K L z * packW b U₁ x
          = (packP b P).eval (algebraMap K L (dom x)) := by
        rw [packW_line, eval_packP, sum_smul_basis_iff]
        exact funext hx
      obtain ⟨h₀, h₁⟩ := hexp.2 x hL
      rw [← packP_unpackP b p₀, eval_packP] at h₀
      rw [← packP_unpackP b p₁, eval_packP] at h₁
      exact ⟨congrFun ((sum_smul_basis_iff b).1 h₀) r, congrFun ((sum_smul_basis_iff b).1 h₁) r⟩

end Pack

open scoped Classical in
/-- **(L1) The interleaving lift**: `strong_mutual_johnson` for `m`-row words, same hypotheses, same
threshold, challenges in `K` (proof: over an extension `L ⊃ K` of degree `m`, `(RS_K)^m ≅ RS_L`). -/
theorem strong_mutual_johnson_interleaved {m : ℕ}
    (dom : ι → K) (hdom : Function.Injective dom) (U₀ U₁ : Fin m → ι → K) (k e : ℕ) (η : ℝ)
    (hk2 : 2 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hηn : 1 ≤ η * (Fintype.card ι))
    (ht4 : 4 * η * (Fintype.card ι) ≤ ((Fintype.card ι - e : ℕ) : ℝ))
    (hJ : ((k - 1 : ℕ) : ℝ) * (Fintype.card ι)
        ≤ (((Fintype.card ι - e : ℕ) : ℝ) - 4 * η * (Fintype.card ι)) ^ 2) :
    ((univ.filter fun z => iHasUnexplainedProximate dom U₀ U₁ k e z).card : ℝ)
      < johnsonThreshold k (Fintype.card ι) e η := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- no rows: every proximate is explained, and the threshold is positive
    subst hm
    have hempty : (univ.filter fun z => iHasUnexplainedProximate dom U₀ U₁ k e z) = ∅ := by
      refine filter_false_of_mem fun z _ hz => ?_
      obtain ⟨P, _, _, hun⟩ := hz
      exact hun (fun _ => 0) (fun _ => 0) (fun r => r.elim0) (fun r => r.elim0)
        ⟨fun r => r.elim0, fun _ _ r => r.elim0⟩
    rw [hempty, card_empty, Nat.cast_zero]
    exact lt_of_le_of_lt (Nat.cast_nonneg _)
      (strong_mutual_johnson dom hdom 0 0 k e η hk2 hη hη4 hηn ht4 hJ)
  · let p := ringChar K
    let _ : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
    let _ : NeZero m := ⟨hm.ne'⟩
    let L := FiniteField.Extension K p m
    let _ : Fintype L := Fintype.ofFinite L
    let b : Module.Basis (Fin m) K L :=
      Module.finBasisOfFinrankEq K L (FiniteField.finrank_extension K p m)
    have hdom' : Function.Injective (fun x => algebraMap K L (dom x)) :=
      (algebraMap K L).injective.comp hdom
    have hL := strong_mutual_johnson (fun x => algebraMap K L (dom x)) hdom' (packW b U₀) (packW b U₁)
      k e η hk2 hη hη4 hηn ht4 hJ
    refine lt_of_le_of_lt ?_ hL
    exact_mod_cast card_le_card_of_injOn (algebraMap K L)
      (fun z hz => by
        have hz' := (mem_filter.1 (Finset.mem_coe.1 hz)).2
        exact Finset.mem_coe.2 (mem_filter.2 ⟨mem_univ _,
          hasUnexplainedProximate_pack b dom U₀ U₁ k e (by omega) z hz'⟩))
      (algebraMap K L).injective.injOn

end LJ
