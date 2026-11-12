-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBColumnBound.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBClearedJet
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The coordinate polynomials `ĝ_x` and the column bound

For each coordinate `x` of the evaluation domain the branch argument compares the
cleared jet with the received word:

  `ĝ_x = γ̂(dom x - x₀) - ξ^(2k) · (u₀ x + Z · u₁ x)  ∈  A = F[Z][T]`.

By construction `ĝ_x` vanishes at a branch point `(z, t_z)` exactly when the proximate
`p_z` agrees with the word at `x` (`clearedJet_spec_exp`), so `ĝ_x` converts the
agreement pattern into an algebraic incidence between `H` and `ĝ_x`.

Two things are needed about it, and both are here.

* **Size.**  `size_ghat_exp`: the `T`-degree and `Z`-height of `ĝ_x` are `O(r)` — a direct
  consequence of the ledger estimate.  With `mα = 1, mR = 0` for the `T`-degree and
  `mα = 0, mR = D_Z` for the `Z`-height this reads `O(r·D_Y)` and `O(r·D_Z)`, and it is
  what turns the column bound into `O(r·D_Y·D_Z)` rather than something involving `D_X`.

* **Divisibility.**  `dvd_of_resultant_eq_zero`: for an irreducible primitive branch
  factor `H`, a vanishing resultant forces `H ∣ ĝ_x` outright.  This is what upgrades the
  conclusion of the incidence count — "the resultant vanishes at more than `r`
  coordinates" — into the identity `Γ_k(dom x) = u₀ x + Z u₁ x` needed for interpolation.
  Gauss's lemma moves irreducibility to `F(Z)[T]`, `resultant_eq_zero_iff` produces a
  common factor there, and primality of `H` in the UFD `F[Z][T]` brings the divisibility
  back down without any denominator bookkeeping.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Size calculus -/

namespace SizeSystem

variable {A : Type*} [CommRing A] (SS : SizeSystem A)

theorem sub {g h : A} {m : ℕ} (hg : SS.P g m) (hh : SS.P h m) : SS.P (g - h) m := by
  rw [sub_eq_add_neg]
  exact SS.add hg (SS.neg hh)

/-- Evaluating a polynomial of degree at most `r` costs `r` times the size of the
argument. -/
theorem eval_le {γ : A[X]} {r mγ mw : ℕ} (hdeg : γ.natDegree ≤ r)
    (hc : ∀ i, SS.P (γ.coeff i) mγ) {w : A} (hw : SS.P w mw) :
    SS.P (γ.eval w) (mγ + r * mw) := by
  rw [eval_eq_sum_range' (n := r + 1) (by omega)]
  refine SS.sum _ _ fun i hi => ?_
  have hik : i ≤ r := by have := Finset.mem_range.mp hi; omega
  refine SS.mono (SS.mul (hc i) (SS.pow hw i)) ?_
  have : i * mw ≤ r * mw := Nat.mul_le_mul_right _ hik
  omega

end SizeSystem

/-! ### The coordinate polynomials -/

section Ghat

variable {A : Type*} [CommRing A]

/-- The coordinate polynomial with an explicit clearing exponent: the cleared jet
evaluated at the coordinate, minus the correspondingly cleared received value. -/
def ghatExp (γ : A[X]) (ξ : A) (E : ℕ) (w val : A) : A :=
  γ.eval w - ξ ^ E * val

/-- The coordinate polynomial `ĝ_x` for the generic odd clearing exponent `2r+1`. -/
def ghat (γ : A[X]) (ξ : A) (r : ℕ) (w val : A) : A :=
  ghatExp γ ξ (2 * r + 1) w val

/-- Size bound for a coordinate polynomial with an arbitrary clearing exponent. -/
theorem size_ghat_exp (SS : SizeSystem A) {γ : A[X]} {ξ w val : A}
    {r E mγ mw mξ mval m : ℕ}
    (hdeg : γ.natDegree ≤ r) (hc : ∀ i, SS.P (γ.coeff i) mγ)
    (hw : SS.P w mw) (hξ : SS.P ξ mξ) (hval : SS.P val mval)
    (h1 : mγ + r * mw ≤ m) (h2 : E * mξ + mval ≤ m) :
    SS.P (ghatExp γ ξ E w val) m := by
  refine SS.sub (SS.mono (SS.eval_le hdeg hc hw) h1)
    (SS.mono (SS.mul (SS.pow hξ _) hval) h2)

/-- **The size of `ĝ_x` is linear in `r`.**  Both instances matter: with the `T`-degree
size system this is `O(r·D_Y)`, with the `Z`-height size system `O(r·D_Z)`. -/
theorem size_ghat (SS : SizeSystem A) {γ : A[X]} {ξ w val : A} {r mγ mw mξ mval m : ℕ}
    (hdeg : γ.natDegree ≤ r) (hc : ∀ i, SS.P (γ.coeff i) mγ)
    (hw : SS.P w mw) (hξ : SS.P ξ mξ) (hval : SS.P val mval)
    (h1 : mγ + r * mw ≤ m) (h2 : (2 * r + 1) * mξ + mval ≤ m) :
    SS.P (ghat γ ξ r w val) m := by
  exact size_ghat_exp SS hdeg hc hw hξ hval h1 h2

end Ghat

/-! ### Sizes of the structural constants -/

section Slice

variable {A : Type*} [CommRing A]

/-- The `U = 0` slice of `P`, evaluated at `a₀`, costs one coefficient size plus `d`
substitutions. -/
theorem size_slice_eval (SS : SizeSystem A) (P : A[X][X]) (a₀ : A) {d mR mα : ℕ}
    (hd : P.natDegree ≤ d) (hP : ∀ j, SS.P ((P.coeff j).coeff 0) mR) (ha : SS.P a₀ mα) :
    SS.P ((P.map (evalRingHom 0)).eval a₀) (mR + d * mα) := by
  have hdeg : (P.map (evalRingHom 0)).natDegree < d + 1 :=
    lt_of_le_of_lt (le_trans natDegree_map_le hd) (by omega)
  rw [eval_eq_sum_range' hdeg]
  refine SS.sum _ _ fun j hj => ?_
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  have hcoeff : (P.map (evalRingHom 0)).coeff j = (P.coeff j).coeff 0 := by
    rw [coeff_map]
    simp [coeff_zero_eq_eval_zero]
  rw [hcoeff]
  refine SS.mono (SS.mul (hP j) (SS.pow ha j)) ?_
  have : j * mα ≤ d * mα := Nat.mul_le_mul_right _ hjd
  omega

/-- The obstruction constant `H₀ = R(x₀, a₀)` has size `mR + d·mα`. -/
theorem size_jetConst (SS : SizeSystem A) (R₀ : A[X][X]) (a₀ : A) {d mR mα : ℕ}
    (hd : R₀.natDegree ≤ d) (hR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR) (ha : SS.P a₀ mα) :
    SS.P (jetConst R₀ a₀) (mR + d * mα) :=
  size_slice_eval SS R₀ a₀ hd (fun j => hR j 0) ha

/-- The simple-root value `ξ` has size `mR + d·mα`: differentiating in `Y` only
multiplies coefficients by integers. -/
theorem size_xi (SS : SizeSystem A) (R₀ : A[X][X]) (a₀ : A) {d mR mα : ℕ}
    (hd : R₀.natDegree ≤ d) (hR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR) (ha : SS.P a₀ mα) :
    SS.P (xi R₀ a₀) (mR + d * mα) := by
  refine size_slice_eval SS (hasseDeriv 1 R₀) a₀ ?_ (fun j => ?_) ha
  · exact le_trans (natDegree_hasseDeriv_le R₀ 1) (le_trans (Nat.sub_le _ _) hd)
  · have hc : (hasseDeriv 1 R₀).coeff j = (j + 1).choose 1 • R₀.coeff (j + 1) := by
      rw [hasseDeriv_coeff, ← nsmul_eq_mul]
    rw [hc, coeff_smul]
    exact SS.nsmul (hR (j + 1) 0) _

/-- Sharp size of the simple-root coefficient: the first Hasse derivative lowers the
`Y`-degree by one, so evaluating it costs only `d-1` powers of the initial root. -/
theorem size_xi_refined (SS : SizeSystem A) (R₀ : A[X][X]) (a₀ : A) {d mR mα : ℕ}
    (hd : R₀.natDegree ≤ d) (hR : ∀ j i, SS.P ((R₀.coeff j).coeff i) mR)
    (ha : SS.P a₀ mα) :
    SS.P (xi R₀ a₀) (mR + (d - 1) * mα) := by
  refine size_slice_eval SS (hasseDeriv 1 R₀) a₀ ?_ (fun j => ?_) ha
  · exact le_trans (natDegree_hasseDeriv_le R₀ 1) (Nat.sub_le_sub_right hd 1)
  · have hc : (hasseDeriv 1 R₀).coeff j = (j + 1).choose 1 • R₀.coeff (j + 1) := by
      rw [hasseDeriv_coeff, ← nsmul_eq_mul]
    rw [hc, coeff_smul]
    exact SS.nsmul (hR (j + 1) 0) _

/-- An irreducible primitive polynomial is nonconstant. -/
theorem natDegree_pos_of_irreducible_of_isPrimitive {Rz : Type*} [CommRing Rz] {H : Rz[X]}
    (hirr : Irreducible H) (hprim : H.IsPrimitive) : 1 ≤ H.natDegree := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h0
  have hC : H = C (H.coeff 0) := eq_C_of_natDegree_eq_zero h0
  have hu : IsUnit (H.coeff 0) := hprim _ ⟨1, by rw [mul_one, ← hC]⟩
  exact hirr.not_isUnit (by rw [hC]; exact hu.map C)

end Slice

/-! ### From a vanishing resultant to divisibility -/

section Divisibility

variable {Rz : Type*} [CommRing Rz] [IsDomain Rz] [UniqueFactorizationMonoid Rz]
  [Nonempty (NormalizedGCDMonoid Rz)]

/-- **A vanishing resultant against an irreducible primitive factor forces divisibility.**

This is the exact converse the incidence count needs.  Over the fraction field a zero
resultant means the two polynomials are not coprime (`resultant_eq_zero_iff`); Gauss's
lemma keeps `H` irreducible there, so `H` divides `g` in `Frac(Rz)[T]`; clearing the
denominator of the cofactor and using that `H` is *prime* in the unique factorisation
domain `Rz[T]` — it cannot divide a nonzero constant, by degree — brings the divisibility
back to `Rz[T]`. -/
theorem dvd_of_resultant_eq_zero (H g : Rz[X]) (hprim : H.IsPrimitive)
    (hirr : Irreducible H) (hdeg : 1 ≤ H.natDegree)
    (hres : resultant H g H.natDegree g.natDegree = 0) :
    H ∣ g := by
  set K := FractionRing Rz
  set φ : Rz →+* K := algebraMap Rz K with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective Rz K
  have hdH : (H.map φ).natDegree = H.natDegree := natDegree_map_eq_of_injective hinj H
  have hdg : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj g
  have h0 : resultant (H.map φ) (g.map φ) = 0 := by
    rw [hdH, hdg, resultant_map_map, hres, map_zero]
  have hirrK : Irreducible (H.map φ) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
  have hdvdK : H.map φ ∣ g.map φ := by
    by_cases hdvd : H.map φ ∣ g.map φ
    · exact hdvd
    · exact ((resultant_eq_zero_iff.mp h0).2 (hirrK.coprime_iff_not_dvd.mpr hdvd)).elim
  obtain ⟨q', hq'⟩ := hdvdK
  -- Clear the denominator of the cofactor.
  obtain ⟨b, hb, hbq⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors Rz) (S := K) q'
  set q := IsLocalization.integerNormalization (nonZeroDivisors Rz) (S := K) q' with hq
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hsmul : b • q' = C (φ b) * q' := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hmul : (H * q).map φ = (C b * g).map φ := by
    rw [Polynomial.map_mul, Polynomial.map_mul, hbq, hsmul, map_C, hq']
    ring
  have hHq : H * q = C b * g := Polynomial.map_injective φ hinj hmul
  -- `H` is prime, and cannot divide a nonzero constant.
  have hprime : Prime H := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hdvdmul : H ∣ C b * g := ⟨q, hHq.symm⟩
  rcases hprime.dvd_or_dvd hdvdmul with hcb | hg
  · exfalso
    have hCb : (C b : Rz[X]) ≠ 0 := by simpa using hbne
    have := Polynomial.natDegree_le_of_dvd hcb hCb
    simp only [natDegree_C] at this
    omega
  · exact hg

end Divisibility

end JBAgreement
