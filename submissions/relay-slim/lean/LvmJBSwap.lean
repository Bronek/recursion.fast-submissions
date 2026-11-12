-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBSwap.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBHeight

/-!
# Variable swaps, and degree bounds for factors

The branch-selection argument (§6.2) factors the Guruswami–Sudan interpolant
`Q ∈ F[Z][X][Y]` and runs the jet machinery on one prime factor.  All the size data of
the factor — its `Y`-degree, its `X`-degree, its `Z`-height — must be inherited from
`Q`.  For the `Y`-degree this is `natDegree_le_of_dvd`; for the other two variables it
is the same statement *after moving the variable to the outside*, which is what the
swap homomorphism of this file does.

`swap : R[X][Y] →+* R[Y][X]` exchanges the two polynomial layers.  It is a ring
homomorphism and an involution, hence injective; therefore divisibility transports
along it, and the inner degree of a factor is bounded by the inner degree of the
multiple.  Composing a `map` of the inner swap with an outer swap bubbles the innermost
variable of a triple tower to the outside (`zOut`).

The degree characterisations `isHeightLE_iff_natDegree_swap_le` and
`natDegree_swap_le_iff` translate between coefficientwise bounds (the form used by the
jet machinery) and outer `natDegree` bounds (the form `natDegree_le_of_dvd` provides).
-/

namespace JBAgreement

open Polynomial

variable {R : Type*} [CommSemiring R]

/-! ### The swap homomorphism -/

/-- Exchange the two variables of `R[X][Y]`. -/
noncomputable def swap (R : Type*) [CommSemiring R] : R[X][X] →+* R[X][X] :=
  eval₂RingHom (eval₂RingHom (C.comp C) X) (C X)

theorem swap_monomial_monomial (n m : ℕ) (a : R) :
    swap R (monomial n (monomial m a)) = monomial m (monomial n a) := by
  unfold swap
  rw [coe_eval₂RingHom, eval₂_monomial, coe_eval₂RingHom, eval₂_monomial]
  rw [RingHom.comp_apply]
  rw [← C_pow]
  calc (C (C a) * X ^ m) * C (X ^ n) = C (C a * X ^ n) * X ^ m := by
        rw [C_mul]; ring
    _ = monomial m (C a * X ^ n) := by rw [C_mul_X_pow_eq_monomial]
    _ = monomial m (monomial n a) := by rw [C_mul_X_pow_eq_monomial]

/-- The coefficient formula: `swap` transposes the coefficient matrix. -/
theorem coeff_coeff_swap (p : R[X][X]) (i j : ℕ) :
    ((swap R p).coeff i).coeff j = (p.coeff j).coeff i := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n q =>
      induction q using Polynomial.induction_on' with
      | add f g hf hg =>
          have : (monomial n (f + g) : R[X][X]) = monomial n f + monomial n g := by
            rw [map_add]
          rw [this, map_add]
          simp only [coeff_add]
          rw [hf, hg]
      | monomial m a =>
          rw [swap_monomial_monomial]
          simp only [coeff_monomial]
          split_ifs with h1 h2 h2 <;>
            simp_all [coeff_monomial, eq_comm]

/-- `swap` is an involution. -/
theorem swap_swap (p : R[X][X]) : swap R (swap R p) = p := by
  apply Polynomial.ext; intro i
  apply Polynomial.ext; intro j
  rw [coeff_coeff_swap, coeff_coeff_swap]

theorem swap_injective : Function.Injective (swap R) := by
  intro p q h
  rw [← swap_swap (R := R) p, h, swap_swap]

@[simp] theorem swap_eq_zero_iff {p : R[X][X]} : swap R p = 0 ↔ p = 0 := by
  constructor
  · intro h
    exact swap_injective (R := R) (a₂ := 0) (by simpa using h)
  · rintro rfl; exact map_zero _

/-! ### Degree characterisations -/

/-- Coefficientwise inner-degree bounds are outer-degree bounds after swapping. -/
theorem natDegree_swap_le_iff {p : R[X][X]} {m : ℕ} :
    (swap R p).natDegree ≤ m ↔ ∀ j, (p.coeff j).natDegree ≤ m := by
  constructor
  · intro h j
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i him
    have : (swap R p).coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h him)
    have h2 := coeff_coeff_swap p i j
    rw [this] at h2
    simpa using h2.symm
  · intro h
    rw [natDegree_le_iff_coeff_eq_zero]
    intro i him
    apply Polynomial.ext; intro j
    rw [coeff_coeff_swap]
    simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h j) him)]

/-- The height predicate of `Height.lean` is the swapped outer degree. -/
theorem isHeightLE_iff_natDegree_swap_le {p : R[X][X]} {m : ℕ} :
    IsHeightLE p m ↔ (swap R p).natDegree ≤ m :=
  ⟨fun h => natDegree_swap_le_iff.mpr h, fun h => natDegree_swap_le_iff.mp h⟩

/-! ### Degree bounds for factors, two variables -/

section TwoVar

variable {F : Type*} [Field F]

/-- The `Z`-height of a factor is at most the `Z`-height of the multiple.  Stated for
`F[Z][T]`; `IsHeightLE` is the coefficientwise `Z`-degree bound. -/
theorem isHeightLE_of_dvd {p q : F[X][X]} {m : ℕ} (hdvd : p ∣ q) (hq : q ≠ 0)
    (hht : IsHeightLE q m) : IsHeightLE p m := by
  rw [isHeightLE_iff_natDegree_swap_le] at hht ⊢
  refine le_trans (natDegree_le_of_dvd ?_ ?_) hht
  · exact map_dvd (swap F) hdvd
  · simpa using hq

/-- The `T`-degree of a factor is at most the `T`-degree of the multiple. -/
theorem natDegree_of_dvd {p q : F[X][X]} {m : ℕ} (hdvd : p ∣ q) (hq : q ≠ 0)
    (hdeg : q.natDegree ≤ m) : p.natDegree ≤ m :=
  le_trans (natDegree_le_of_dvd hdvd hq) hdeg

end TwoVar

/-! ### Degree bounds for factors, three variables

For `P ∣ Q` in `F[Z][X][Y]`, three bounds are inherited: the `Y`-degree (outer, no swap
needed), the `X`-degree (one outer swap), and the `Z`-height (bubble `Z` to the outside:
an inner swap under `map`, then an outer swap). -/

section ThreeVar

variable {F : Type*} [Field F]

/-- Move the innermost variable of `F[Z][X][Y]` to the outside. -/
noncomputable def zOut (F : Type*) [Field F] : F[X][X][X] →+* F[X][X][X] :=
  (swap (F[X])).comp (mapRingHom (swap F))

theorem zOut_injective : Function.Injective (zOut F) := by
  unfold zOut
  rw [RingHom.coe_comp]
  exact Function.Injective.comp (swap_injective (R := F[X]))
    (map_injective _ (swap_injective (R := F)))

theorem coeff_coeff_coeff_zOut (P : F[X][X][X]) (d j i : ℕ) :
    (((zOut F P).coeff d).coeff j).coeff i = (((P.coeff j).coeff i)).coeff d := by
  unfold zOut
  rw [RingHom.comp_apply]
  rw [coeff_coeff_swap]
  rw [coe_mapRingHom, coeff_map]
  rw [coeff_coeff_swap]

/-- The three-variable height characterisation: coefficientwise `Z`-degree bounds are
outer degree bounds after `zOut`. -/
theorem natDegree_zOut_le_iff {P : F[X][X][X]} {m : ℕ} :
    (zOut F P).natDegree ≤ m ↔ ∀ j i, ((P.coeff j).coeff i).natDegree ≤ m := by
  constructor
  · intro h j i
    rw [natDegree_le_iff_coeff_eq_zero]
    intro d hdm
    have h1 : (zOut F P).coeff d = 0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hdm)
    have h2 := coeff_coeff_coeff_zOut P d j i
    rw [h1] at h2
    simpa using h2.symm
  · intro h
    rw [natDegree_le_iff_coeff_eq_zero]
    intro d hdm
    apply Polynomial.ext; intro j
    apply Polynomial.ext; intro i
    rw [coeff_coeff_coeff_zOut]
    simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (h j i) hdm)]

/-- **`Z`-heights pass to factors** in `F[Z][X][Y]`. -/
theorem heightZ_of_dvd {P Q : F[X][X][X]} {m : ℕ} (hdvd : P ∣ Q) (hQ : Q ≠ 0)
    (h : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ m) :
    ∀ j i, ((P.coeff j).coeff i).natDegree ≤ m := by
  rw [← natDegree_zOut_le_iff] at h ⊢
  refine le_trans (natDegree_le_of_dvd (map_dvd (zOut F) hdvd) ?_) h
  intro h0
  exact hQ (zOut_injective (by simpa using h0))

/-- **`X`-degrees pass to factors** in `F[Z][X][Y]`. -/
theorem degX_of_dvd {P Q : F[X][X][X]} {m : ℕ} (hdvd : P ∣ Q) (hQ : Q ≠ 0)
    (h : ∀ j, (Q.coeff j).natDegree ≤ m) :
    ∀ j, (P.coeff j).natDegree ≤ m := by
  rw [← natDegree_swap_le_iff] at h ⊢
  refine le_trans (natDegree_le_of_dvd (map_dvd (swap (F[X])) hdvd) ?_) h
  simpa using hQ

/-- **`Y`-degrees pass to factors** in `F[Z][X][Y]`. -/
theorem degY_of_dvd {P Q : F[X][X][X]} {m : ℕ} (hdvd : P ∣ Q) (hQ : Q ≠ 0)
    (h : Q.natDegree ≤ m) : P.natDegree ≤ m :=
  le_trans (natDegree_le_of_dvd hdvd hQ) h

end ThreeVar

end JBAgreement
