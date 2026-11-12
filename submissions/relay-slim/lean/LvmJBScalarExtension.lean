-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBScalarExtension.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBEndToEnd
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.Finite.Extension

/-!
# Removing the slice field-size condition by scalar extension

The good slice may be selected after embedding the finite base field into a larger
finite extension.  The branch argument then returns an affine bucket over the
extension.  This file records the essential descent step: two distinct parameters
from the base field force the two affine polynomials to have base-field coefficients.
-/

namespace JBAgreement

open Polynomial Finset

section Descent

variable {F K : Type*} [Field F] [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An affine bucket obtained after scalar extension descends to the base field.

The extension bucket is assumed to use parameters in the image of `φ`.  Since it has
at least two elements, two distinct parameters determine `v₀` and `v₁`; solving the
two affine equations expresses them as maps of polynomials over `F`. -/
theorem descend_affine_bucket [DecidableEq F] [DecidableEq K]
    (φ : F →+* K) (hφ : Function.Injective φ)
    (k e : ℕ) (S : Finset F) (p : F → F[X])
    (SK : Finset K) (hSK : SK ⊆ S.image φ) (hSKcard : e + 1 < SK.card)
    (v₀ v₁ : K[X]) (hv₀ : v₀.natDegree < k) (hv₁ : v₁.natDegree < k)
    (hp : ∀ z ∈ S, φ z ∈ SK → (p z).map φ = v₀ + C (φ z) * v₁) :
    ∃ (w₀ w₁ : F[X]) (S' : Finset F), S' ⊆ S ∧ e + 1 < S'.card ∧
      w₀.natDegree < k ∧ w₁.natDegree < k ∧
      ∀ z ∈ S', p z = w₀ + C z * w₁ := by
  set S' : Finset F := S.filter fun z => φ z ∈ SK with hS'def
  have himage : S'.image φ = SK := by
    apply Finset.ext
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hz).2
    · intro hy
      obtain ⟨z, hzS, hzφ⟩ := Finset.mem_image.mp (hSK hy)
      refine Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzS, ?_⟩, hzφ⟩
      rwa [hzφ]
  have hcard : S'.card = SK.card := by
    rw [← himage, Finset.card_image_of_injective _ hφ]
  have htwo : 1 < S'.card := by omega
  letI : Fintype ↥S' := Fintype.ofFinite ↥S'
  obtain ⟨z₀, z₁, hz01⟩ := Fintype.exists_pair_of_one_lt_card (α := ↥S') (by simpa using htwo)
  have hz10 : (z₁ : F) ≠ (z₀ : F) := by
    intro h
    exact hz01 (Subtype.ext h.symm)
  have hzφ : φ (z₁ : F) - φ (z₀ : F) ≠ 0 := sub_ne_zero.mpr (hφ.ne hz10)
  set w₁ : F[X] := C ((z₁ : F) - z₀)⁻¹ * (p z₁ - p z₀) with hw₁
  set w₀ : F[X] := p z₀ - C (z₀ : F) * w₁ with hw₀
  have hz₀S : (z₀ : F) ∈ S := (Finset.mem_filter.mp z₀.property).1
  have hz₁S : (z₁ : F) ∈ S := (Finset.mem_filter.mp z₁.property).1
  have hz₀K : φ (z₀ : F) ∈ SK := (Finset.mem_filter.mp z₀.property).2
  have hz₁K : φ (z₁ : F) ∈ SK := (Finset.mem_filter.mp z₁.property).2
  have hp₀ := hp z₀ hz₀S hz₀K
  have hp₁ := hp z₁ hz₁S hz₁K
  have hmapw₁ : w₁.map φ = v₁ := by
    rw [hw₁, Polynomial.map_mul, Polynomial.map_C, map_inv₀, Polynomial.map_sub,
      hp₁, hp₀, map_sub]
    have hinv : (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
        (φ (z₁ : F) - φ (z₀ : F)) = 1 := inv_mul_cancel₀ hzφ
    have hCinv : C (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
        C (φ (z₁ : F) - φ (z₀ : F)) = (1 : K[X]) := by
      rw [← C_mul, hinv, C_1]
    calc
      C (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
          (v₀ + C (φ (z₁ : F)) * v₁ - (v₀ + C (φ (z₀ : F)) * v₁)) =
          C (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
            (C (φ (z₁ : F)) - C (φ (z₀ : F))) * v₁ := by ring
      _ =
          (C (φ (z₁ : F) - φ (z₀ : F))⁻¹ *
            C (φ (z₁ : F) - φ (z₀ : F))) * v₁ := by rw [C_sub]
      _ = v₁ := by rw [hCinv, one_mul]
  have hmapw₀ : w₀.map φ = v₀ := by
    rw [hw₀, Polynomial.map_sub, hp₀, Polynomial.map_mul, Polynomial.map_C, hmapw₁]
    ring
  have hw₀deg : w₀.natDegree < k := by
    rw [← natDegree_map_eq_of_injective hφ, hmapw₀]
    exact hv₀
  have hw₁deg : w₁.natDegree < k := by
    rw [← natDegree_map_eq_of_injective hφ, hmapw₁]
    exact hv₁
  refine ⟨w₀, w₁, S', Finset.filter_subset _ _, by simpa [hcard] using hSKcard,
    hw₀deg, hw₁deg, ?_⟩
  intro z hz
  have hzS := (Finset.mem_filter.mp hz).1
  have hzK := (Finset.mem_filter.mp hz).2
  apply Polynomial.map_injective φ hφ
  rw [hp z hzS hzK, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    hmapw₀, hmapw₁]

end Descent

section Lift

variable {F K : Type*} [Field F] [Field K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extend a polynomial family from `F` to `K`, using `invFun` away from the image.
Only values on the image are used by the scalar-extension argument. -/
noncomputable def extendPolyFamily (φ : F →+* K) (p : F → F[X]) : K → K[X] :=
  fun z => (p (Function.invFun φ z)).map φ

@[simp] theorem extendPolyFamily_apply (φ : F →+* K) (hφ : Function.Injective φ)
    (p : F → F[X]) (z : F) :
    extendPolyFamily φ p (φ z) = (p z).map φ := by
  simp [extendPolyFamily, Function.leftInverse_invFun hφ z]

/-- Specializing a trivariate polynomial commutes with scalar extension. -/
theorem eval_map_trivariate (φ : F →+* K) (Q : (F[X][X])[X]) (p : F[X]) (z : F) :
    (((Q.map (mapRingHom (mapRingHom φ))).map
        (mapRingHom (evalRingHom (φ z)))).eval (p.map φ)) =
      (((Q.map (mapRingHom (evalRingHom z))).eval p).map φ) := by
  have hspec :
      (Q.map (mapRingHom (mapRingHom φ))).map
          (mapRingHom (evalRingHom (φ z))) =
        (Q.map (mapRingHom (evalRingHom z))).map (mapRingHom φ) := by
    apply Polynomial.ext
    intro j
    simp only [coeff_map, coe_mapRingHom]
    apply Polynomial.ext
    intro i
    simp [coeff_map, eval_map_apply]
  rw [hspec]
  exact Polynomial.map_mapRingHom_eval_map φ
    (Q.map (mapRingHom (evalRingHom z))) p

variable [DecidableEq F] [Fintype K] [DecidableEq K]

/-- A sharp affine bucket after passing to any sufficiently large finite scalar
extension and descending it to the base field. -/
theorem exists_affine_bucket_of_GS_sharp_scalarExtension
    (φ : F →+* K) (hφ : Function.Injective φ)
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hfieldK : 2 * dY * dX < Fintype.card K)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ (v₀ v₁ : F[X]) (S' : Finset F), S' ⊆ S ∧ e + 1 < S'.card ∧
      v₀.natDegree < k ∧ v₁.natDegree < k ∧
      ∀ z ∈ S', p z = v₀ + C z * v₁ := by
  classical
  set SK : Finset K := S.image φ with hSK
  set pK : K → K[X] := extendPolyFamily φ p with hpK
  set domK : ι → K := fun x => φ (dom x) with hdomK
  set u₀K : ι → K := fun x => φ (u₀ x) with hu₀K
  set u₁K : ι → K := fun x => φ (u₁ x) with hu₁K
  set QK : (K[X][X])[X] := Q.map (mapRingHom (mapRingHom φ)) with hQK
  have hSKcard : SK.card = S.card := by
    rw [hSK, Finset.card_image_of_injective _ hφ]
  have hpK_apply : ∀ z : F, pK (φ z) = (p z).map φ := by
    intro z
    simp [hpK, extendPolyFamily_apply φ hφ]
  have hpdegK : ∀ z ∈ SK, (pK z).natDegree < k := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp (hSK ▸ hz)
    rw [hpK_apply]
    exact lt_of_le_of_lt natDegree_map_le (hpdeg z₀ hz₀)
  have hproxK : ∀ z ∈ SK,
      (disagree (fun x => u₀K x + z * u₁K x) (RSeval domK (pK z))).card ≤ e := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp (hSK ▸ hz)
    have hset : disagree (fun x => u₀K x + φ z₀ * u₁K x)
        (RSeval domK (pK (φ z₀))) =
          disagree (fun x => u₀ x + z₀ * u₁ x) (RSeval dom (p z₀)) := by
      ext x
      simp only [mem_disagree, RSeval_apply, hu₀K, hu₁K, hdomK, hpK_apply]
      rw [eval_map]
      simp only [eval₂_at_apply]
      rw [← φ.map_mul, ← φ.map_add, hφ.ne_iff]
    rw [hset]
    exact hprox z₀ hz₀
  have hQK0 : QK ≠ 0 := by
    intro h0
    have hφ₁ : Function.Injective (mapRingHom φ) := Polynomial.map_injective φ hφ
    have hφ₂ : Function.Injective (mapRingHom (mapRingHom φ)) :=
      Polynomial.map_injective (mapRingHom φ) hφ₁
    rw [hQK] at h0
    apply hQ0
    apply Polynomial.map_injective (mapRingHom (mapRingHom φ)) hφ₂
    simpa using h0
  have hQKY : QK.natDegree ≤ dY := le_trans natDegree_map_le hQY
  have hQKX : ∀ j, (QK.coeff j).natDegree ≤ dX := by
    intro j
    rw [hQK, coeff_map]
    exact le_trans natDegree_map_le (hQX j)
  have hQKZ : ∀ j i, ((QK.coeff j).coeff i).natDegree ≤ dZ := by
    intro j i
    rw [hQK, coeff_map]
    change (((Q.coeff j).map (mapRingHom φ)).coeff i).natDegree ≤ dZ
    rw [coeff_map]
    exact le_trans natDegree_map_le (hQZ j i)
  have hGSK : ∀ z ∈ SK,
      ((QK.map (mapRingHom (evalRingHom z))).eval (pK z)) = 0 := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp (hSK ▸ hz)
    rw [hpK_apply, hQK, eval_map_trivariate]
    simpa using congrArg (Polynomial.map φ) (hGS z₀ hz₀)
  obtain ⟨v₀K, v₁K, SK', hSK'SK, hSK'card, hv₀K, hv₁K, hpKaff⟩ :=
    exists_affine_bucket_of_GS_sharp domK (hφ.comp hdom) u₀K u₁K k e hk SK pK
      hpdegK hproxK QK hQK0 dX dY dZ hQKY hQKX hQKZ hGSK hfieldK hslack
      (by simpa [sharpGSBound, hSKcard] using hS)
  exact descend_affine_bucket φ hφ k e S p SK'
      (Finset.Subset.trans hSK'SK (by simp [hSK]))
      hSK'card v₀K v₁K hv₀K hv₁K (by
        intro z hzS hzK
        rw [← hpK_apply]
        exact hpKaff (φ z) hzK)

/-- **Sharp correlated agreement with no base-field size assumption.**

The proof passes to the canonical finite extension of degree `2*dY*dX+1`, applies
`exists_affine_bucket_of_GS_sharp_scalarExtension`, and descends the affine bucket.
Thus the former good-slice condition is an internal construction, not a hypothesis. -/
theorem exists_affine_bucket_of_GS_sharp_noFieldSize
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ (v₀ v₁ : F[X]) (S' : Finset F), S' ⊆ S ∧ e + 1 < S'.card ∧
      v₀.natDegree < k ∧ v₁.natDegree < k ∧
      ∀ z ∈ S', p z = v₀ + C z * v₁ := by
  let t : ℕ := 2 * dY * dX
  let n : ℕ := t + 1
  let pc := ringChar F
  letI hpcP : Fact pc.Prime := ⟨CharP.char_is_prime F pc⟩
  letI hn0 : NeZero n := ⟨by simp [n]⟩
  let K := FiniteField.Extension F pc n
  letI : Fintype K := Fintype.ofFinite K
  letI : DecidableEq K := Classical.decEq K
  let φ : F →+* K := algebraMap F K
  have hφ : Function.Injective φ := RingHom.injective φ
  have hcardK : Fintype.card K = Fintype.card F ^ n := by
    rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension]
    exact congrArg (· ^ n) Fintype.card_eq_nat_card.symm
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hpowbase : 2 ^ t ≤ Fintype.card F ^ t := Nat.pow_le_pow_left hq2 t
  have hpowstep : Fintype.card F ^ t ≤ Fintype.card F ^ n := by
    change Fintype.card F ^ t ≤ Fintype.card F ^ (t + 1)
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hfieldK : 2 * dY * dX < Fintype.card K := by
    rw [hcardK]
    exact lt_of_lt_of_le (by simpa [t] using t.lt_two_pow_self)
      (le_trans hpowbase hpowstep)
  exact exists_affine_bucket_of_GS_sharp_scalarExtension φ hφ dom hdom u₀ u₁ k e hk
    S p hpdeg hprox Q hQ0 dX dY dZ hQY hQX hQZ hGS hfieldK hslack hS

/-- Sharp correlated agreement over an arbitrary finite base field. -/
theorem correlatedAgreement_of_GS_sharp_noFieldSize
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hslack : 1 ≤ Fintype.card ι - e - k)
    (hS : dY * (e + 2) +
        (Fintype.card ι - k) * (4 * k * (dY * dZ) + dY) /
          (Fintype.card ι - e - k) +
        dZ + 3 * (dY * dZ) < S.card) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
      (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e ∧
      (∀ S₂ : Finset F, e + 1 < S₂.card →
        (∀ z ∈ S₂, (disagree (fun x => u₀ x + z * u₁ x)
            (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) →
        (S₂.filter fun z =>
          lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z
            ≠ corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e) := by
  obtain ⟨v₀, v₁, S', hS'S, hS'card, hv₀, hv₁, hpaff⟩ :=
    exists_affine_bucket_of_GS_sharp_noFieldSize dom hdom u₀ u₁ k e hk S p
      hpdeg hprox Q hQ0 dX dY dZ hQY hQX hQZ hGS hslack hS
  refine ⟨v₀, v₁, hv₀, hv₁, ?_, ?_⟩
  · refine correlatedAgreement_of_branch dom u₀ u₁ v₀ v₁ e S' hS'card ?_
    intro z hz
    have h := hprox z (hS'S hz)
    rw [hpaff z hz] at h
    exact h
  · intro S₂ hS₂ hagree
    exact mutual_correlatedAgreement dom u₀ u₁ v₀ v₁ e S₂ hS₂ hagree

end Lift

end JBAgreement
