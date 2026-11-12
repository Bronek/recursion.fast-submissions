-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBIntegral.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBJetLedger
import LvmJBJet

/-!
# Integral models: naturality, homogeneous evaluation, and uniqueness in `F[U]`

The finite-jet argument runs the recursion *generically*, over `K = Frac(F[Z][T])`, and
then reads off the answer at each branch point `(z, t_z)`.  Passing from the generic
statement to the specialised one is the only place where the two worlds meet, and this
file supplies the three tools that make the passage a formality.

## 1. Naturality

`xi` and `jetConst` are defined over an arbitrary commutative ring, and commute with any
coefficient homomorphism (`xi_map`, `jetConst_map`).  So the generic `ξ` and the
specialised `ξ(z, t_z)` are literally the same construction applied to two different
homomorphisms out of `A = F[Z][T]`, and no compatibility hypothesis has to be carried.

## 2. Homogeneous evaluation

Denominators are the obstacle: the generic jet lives over `K`, not over `A`, so it
cannot be pushed through a homomorphism `A → F` directly.  The fix is to clear them once
and for all.  For `P` of `Y`-degree at most `d`,

  `evalH P d c γ̂ = ∑_{j ≤ d} P_j · γ̂ʲ · c^(d-j)`

is the *homogenised* evaluation, a polynomial expression in the coefficients of `P`, in
`γ̂` and in `c`.  It is therefore natural in the coefficient ring (`evalH_map`), and it
computes the honest evaluation whenever the denominators can be divided out:

  `evalH P d c (C c * γ) = C (c ^ d) · P.eval γ`   (`evalH_C_mul`).

Reading the first identity forwards over `K` and backwards over `F` is exactly the
transfer we need — and it never mentions localisation, completions, or valuations.

## 3. Uniqueness modulo `U^{r+1}`

`eq_of_dvd_eval` is finite Hensel uniqueness in the only form the endgame needs, stated
directly in `F[U]`: two polynomials of degree at most `r`, with the same constant term,
both annihilating `R` modulo `U^{r+1}`, coincide as soon as `∂_Y R` is nonzero at the
base point.  Instead of a nilpotent-ideal argument it uses that `U` is prime in `F[U]`:
the difference `δ` satisfies `U^{r+1} ∣ δ · v` with `v(0) ≠ 0`, so `U^{r+1} ∣ δ`, so
`δ = 0` by degree.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Naturality of the structural constants -/

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Hasse derivatives commute with coefficient homomorphisms. -/
theorem hasseDeriv_map (φ : A →+* B) (P : A[X]) (n : ℕ) :
    (hasseDeriv n P).map φ = hasseDeriv n (P.map φ) := by
  apply Polynomial.ext
  intro i
  rw [coeff_map, hasseDeriv_coeff, hasseDeriv_coeff, coeff_map, map_mul, map_natCast]

/-- Taking the `U = 0` slice commutes with coefficient homomorphisms. -/
theorem map_evalRingHom_zero_comm (φ : A →+* B) (P : A[X][X]) :
    (P.map (mapRingHom φ)).map (evalRingHom 0) = (P.map (evalRingHom 0)).map φ := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro p
  simp

/-- **Naturality of `ξ`.**  The simple-root value of a specialised branch is the
specialisation of the generic simple-root value. -/
theorem xi_map (φ : A →+* B) (P : A[X][X]) (a : A) :
    xi (P.map (mapRingHom φ)) (φ a) = φ (xi P a) := by
  unfold xi
  rw [← hasseDeriv_map, map_evalRingHom_zero_comm, eval_map, eval₂_hom]

/-- **Naturality of the obstruction constant.** -/
theorem jetConst_map (φ : A →+* B) (P : A[X][X]) (a : A) :
    jetConst (P.map (mapRingHom φ)) (φ a) = φ (jetConst P a) := by
  unfold jetConst
  rw [map_evalRingHom_zero_comm, eval_map, eval₂_hom]

end Naturality

/-! ### Homogeneous evaluation -/

section EvalH

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The *homogenised* evaluation of `P` (of `Y`-degree at most `d`) at the "numerator"
`γ̂` over the "denominator" `c`:

  `evalH P d c γ̂ = ∑_{j ≤ d} P_j · γ̂ ^ j · c ^ (d - j)`.

Being a polynomial expression in the data, it survives every ring homomorphism; and when
`γ̂ = c · γ` it equals `c ^ d · P(γ)`. -/
noncomputable def evalH (P : A[X][X]) (d : ℕ) (c : A) (γ : A[X]) : A[X] :=
  ∑ j ∈ range (d + 1), P.coeff j * γ ^ j * C (c ^ (d - j))

/-- **Naturality of the homogenised evaluation.** -/
theorem evalH_map (φ : A →+* B) (P : A[X][X]) (d : ℕ) (c : A) (γ : A[X]) :
    evalH (P.map (mapRingHom φ)) d (φ c) (γ.map φ) = (evalH P d c γ).map φ := by
  unfold evalH
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow, map_C, ← map_pow,
    coeff_map]
  rfl

/-- **Homogenised evaluation computes the honest one.**  This is the bridge used twice:
forwards over `K` (where `γ̂` is the cleared generic jet) and backwards over `F` (where
dividing by `c ^ d ≠ 0` recovers the specialised jet). -/
theorem evalH_C_mul (P : A[X][X]) {d : ℕ} (hd : P.natDegree ≤ d) (c : A) (γ : A[X]) :
    evalH P d c (C c * γ) = C (c ^ d) * P.eval γ := by
  unfold evalH
  rw [eval_eq_sum_range' (n := d + 1) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjd : j ≤ d := by have := Finset.mem_range.mp hj; omega
  have hsplit : c ^ d = c ^ j * c ^ (d - j) := by
    rw [← pow_add]; congr 1; omega
  rw [mul_pow, ← C_pow, hsplit, C_mul]
  ring

end EvalH

/-! ### Finite Hensel uniqueness in `F[U]` -/

section Uniqueness

variable {F : Type*} [Field F]

/-- A polynomial with nonzero constant term is coprime to `X ^ n`. -/
theorem isCoprime_X_pow_of_coeff_zero_ne_zero {v : F[X]} (hv : v.coeff 0 ≠ 0) (n : ℕ) :
    IsCoprime ((X : F[X]) ^ n) v :=
  IsCoprime.pow_left ((Polynomial.irreducible_X).coprime_iff_not_dvd.mpr
    (fun h => hv (Polynomial.X_dvd_iff.mp h)))

/-- **Finite Hensel uniqueness, in the form used by the endgame.**

If `γ` and `π` both have degree at most `r`, share their constant term, both annihilate
`R` modulo `U ^ (r+1)`, and `∂_Y R` evaluated at `π` has nonzero constant term, then
`γ = π`.

The proof is the Taylor expansion `R(γ) - R(π) = δ · (∂_Y R(π) + c δ)` together with the
primality of `U`: the second factor has nonzero constant term, so all of `U ^ (r+1)`
must divide `δ`, which has degree at most `r`. -/
theorem eq_of_dvd_eval (R : F[X][X]) {γ π : F[X]} {r : ℕ}
    (hγ : γ.natDegree ≤ r) (hπ : π.natDegree ≤ r)
    (hconst : γ.coeff 0 = π.coeff 0)
    (hRγ : (X : F[X]) ^ (r + 1) ∣ R.eval γ)
    (hRπ : (X : F[X]) ^ (r + 1) ∣ R.eval π)
    (hunit : ((hasseDeriv 1 R).eval π).coeff 0 ≠ 0) :
    γ = π := by
  set δ : F[X] := γ - π with hδdef
  obtain ⟨c, hc⟩ := R.binomExpansion π δ
  have hπδ : π + δ = γ := by rw [hδdef]; ring
  rw [hπδ] at hc
  -- `R(γ) - R(π) = δ * v` with `v = ∂_Y R(π) + c δ`.
  set v : F[X] := (hasseDeriv 1 R).eval π + c * δ with hvdef
  have hfac : R.eval γ - R.eval π = δ * v := by
    rw [hc, hvdef, hasseDeriv_one]
    ring
  -- `δ` has zero constant term, so `v` has nonzero constant term.
  have hδ0 : δ.coeff 0 = 0 := by rw [hδdef, coeff_sub, hconst, sub_self]
  have hv0 : v.coeff 0 ≠ 0 := by
    rw [hvdef, coeff_add, mul_coeff_zero, hδ0, mul_zero, add_zero]
    exact hunit
  -- Divide out the coprime factor.
  have hdvd : (X : F[X]) ^ (r + 1) ∣ δ * v := by
    rw [← hfac]; exact dvd_sub hRγ hRπ
  have hδdvd : (X : F[X]) ^ (r + 1) ∣ δ :=
    (isCoprime_X_pow_of_coeff_zero_ne_zero hv0 (r + 1)).dvd_of_dvd_mul_right hdvd
  -- Degree forces `δ = 0`.
  refine eq_of_sub_dvd_of_degree_le (x₀ := (0 : F)) (r := r) ?_ ?_ ?_
  · exact natDegree_le_iff_degree_le.mp hγ
  · exact natDegree_le_iff_degree_le.mp hπ
  · simpa using hδdvd

end Uniqueness

end JBAgreement
