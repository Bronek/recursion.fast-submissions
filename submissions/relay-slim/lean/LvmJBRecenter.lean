-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBRecenter.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBClearedJet

/-!
# Recentering: from the interpolant's coordinates to the jet's

The Guruswami–Sudan interpolant and its factors live in `F[Z][X][Y]`.  The jet
machinery lives in `(F[Z][T])[U][Y]`: coefficients in `A = F[Z][T]` (the free initial
root `T` adjoined), recentered at the slice `U = X - x₀`.  This file is the bridge.

* `recenter x₀` — the ring homomorphism performing `X ↦ U + x₀` and embedding `F[Z]`
  into `F[Z][T]`; it factors as a shift inside `F[Z][X]` followed by the constant
  embedding (`innerRecenter_eq`), which is what makes its size bounds one-liners.
* `fiberAt x₀` — the fiber map `W ↦ W(x₀, T, Z) ∈ F[Z][T]`, a coefficientwise
  evaluation, so its degree and height bounds are immediate.
* `chi z x₀` — the specialisation `F[Z][X] → F` at `(Z, X) = (z, x₀)`.

The commutation lemmas (`jetConst_recenter`, `xi_recenter`, `spec_fiberAt`,
`eval_eval_map_eq`, `eval_recenter_spec`) say that the structural constants of the
recentered branch are the fibers of the original one and that all evaluation routes to
`F` agree; each is an instance of "two ring homomorphisms agree on generators".

`ringHom_resultant_eq_zero_of_common_root` generalises the §2 specialisation lemma to
an arbitrary coefficient homomorphism.  Instantiated at `chi z x₀` it is the
discriminant argument: at a good slice `x₀`, only `O(deg·height)` many `z` can make the
branch and its `Y`-derivative share a root.
-/

namespace JBAgreement

open Polynomial

variable {F : Type*} [Field F]

/-! ### Two-level homomorphism extensionality -/

/-- Two ring homomorphisms out of `R[X][Y]` agreeing on constants and on the two
variables agree. -/
theorem ringHom_ext₂ {R S : Type*} [CommSemiring R] [Semiring S] {f g : R[X][X] →+* S}
    (hC : ∀ a : R, f (C (C a)) = g (C (C a)))
    (hX : f (C X) = g (C X)) (hY : f X = g X) : f = g := by
  refine ringHom_ext ?_ hY
  intro q
  have hcomp : f.comp (C : R[X] →+* R[X][X]) = g.comp (C : R[X] →+* R[X][X]) :=
    ringHom_ext hC hX
  exact RingHom.congr_fun hcomp q

/-! ### The recentering homomorphisms -/

/-- The recentering shift inside `F[Z][X]`: `X ↦ X + x₀`. -/
noncomputable def shiftZ (x₀ : F) : F[X][X] →+* F[X][X] :=
  eval₂RingHom (C : F[X] →+* F[X][X]) (X + C (C x₀))

/-- The inner recentering `F[Z][X] → (F[Z][T])[U]`: constants via `C ∘ C`, and
`X ↦ U + x₀`. -/
noncomputable def innerRecenter (x₀ : F) : F[X][X] →+* (F[X][X])[X] :=
  eval₂RingHom ((C : F[X][X] →+* (F[X][X])[X]).comp (C : F[X] →+* F[X][X]))
    (X + C (C (C x₀)))

/-- Recentering `F[Z][X][Y] → ((F[Z][T])[U])[Y]`: apply `innerRecenter` to every
`Y`-coefficient. -/
noncomputable def recenter (x₀ : F) : (F[X][X])[X] →+* ((F[X][X])[X])[X] :=
  mapRingHom (innerRecenter x₀)

/-- The fiber map `W ↦ W(x₀, T, Z)`: evaluate every `Y`-coefficient at `X = x₀`,
leaving a polynomial in `T` (the old `Y`) over `F[Z]`. -/
noncomputable def fiberAt (x₀ : F) : (F[X][X])[X] →+* (F[X])[X] :=
  mapRingHom (evalRingHom (C x₀))

/-- The point specialisation `F[Z][X] → F` at `Z = z`, `X = x₀`. -/
noncomputable def chi (z x₀ : F) : F[X][X] →+* F :=
  (evalRingHom z).comp (evalRingHom (C x₀))

@[simp] lemma fiberAt_coeff (x₀ : F) (W : (F[X][X])[X]) (j : ℕ) :
    (fiberAt x₀ W).coeff j = (W.coeff j).eval (C x₀) := by
  simp [fiberAt, coeff_map]

lemma chi_apply (z x₀ : F) (c : F[X][X]) : chi z x₀ c = (c.eval (C x₀)).eval z := rfl

/-- The inner recentering is the shift followed by the constant embedding into
`F[Z][T]`-coefficients. -/
theorem innerRecenter_eq (x₀ : F) :
    innerRecenter x₀
      = (mapRingHom (C : F[X] →+* F[X][X])).comp (shiftZ x₀) := by
  refine ringHom_ext ?_ ?_
  · intro a
    simp [innerRecenter, shiftZ]
  · simp [innerRecenter, shiftZ]

/-! ### Commutation with the structural constants -/

/-- The obstruction constant of the recentered branch is the fiber. -/
theorem jetConst_recenter (x₀ : F) (W : (F[X][X])[X]) :
    jetConst (recenter x₀ W) (X : F[X][X]) = fiberAt x₀ W := by
  have hhom :
      ((evalRingHom (X : F[X][X])).comp
        ((mapRingHom (evalRingHom (0 : F[X][X]))).comp (recenter x₀)))
      = fiberAt x₀ := by
    refine ringHom_ext₂ ?_ ?_ ?_
    · intro a
      simp [recenter, innerRecenter, fiberAt]
    · simp [recenter, innerRecenter, fiberAt]
    · simp [recenter, innerRecenter, fiberAt]
  have := RingHom.congr_fun hhom W
  simpa [jetConst] using this

/-- The simple-root value of the recentered branch is the fiber of the `Y`-derivative
(a Hasse derivative, so valid in every characteristic). -/
theorem xi_recenter (x₀ : F) (W : (F[X][X])[X]) :
    xi (recenter x₀ W) (X : F[X][X]) = fiberAt x₀ (hasseDeriv 1 W) := by
  have hcomm : hasseDeriv 1 (recenter x₀ W) = recenter x₀ (hasseDeriv 1 W) := by
    simp [recenter]
  rw [xi, hcomm]
  exact jetConst_recenter x₀ (hasseDeriv 1 W)

/-- Specialising the fiber is the two-variable point evaluation. -/
theorem spec_fiberAt (z x₀ t : F) (W : (F[X][X])[X]) :
    spec z t (fiberAt x₀ W) = eval₂ (chi z x₀) t W := by
  rw [spec_apply, fiberAt]
  rw [coe_mapRingHom, eval₂_map]
  rfl

/-- The two evaluation routes agree: substitute `Y := π` then evaluate at `x₀`, or
specialise `(Z, X) ↦ (z, x₀)` and evaluate `Y` at `π(x₀)`. -/
theorem eval_eval_map_eq (z x₀ : F) (W : (F[X][X])[X]) (π : F[X]) :
    ((W.map (mapRingHom (evalRingHom z))).eval π).eval x₀
      = eval₂ (chi z x₀) (π.eval x₀) W := by
  have h2 : (W.map (mapRingHom (evalRingHom z))).eval π
      = eval₂ (mapRingHom (evalRingHom z)) π W := by
    rw [eval_map]
  rw [h2]
  have h3 := hom_eval₂ W (mapRingHom (evalRingHom z)) (evalRingHom x₀) π
  have h4 : (evalRingHom x₀) (eval₂ (mapRingHom (evalRingHom z)) π W)
      = eval₂ ((evalRingHom x₀).comp (mapRingHom (evalRingHom z))) (π.eval x₀) W := by
    simpa using h3
  rw [show ((eval₂ (mapRingHom (evalRingHom z)) π W).eval x₀)
      = (evalRingHom x₀) (eval₂ (mapRingHom (evalRingHom z)) π W) from rfl, h4]
  congr 1
  refine ringHom_ext₂ ?_ ?_ ?_ <;> simp [chi]

/-- **Transport of roots to the recentered branch.**  If `π` is a `Y`-root of the
`z`-specialised `W`, then the shifted `π ∘ (X + x₀)` is a `Y`-root of the
`(z,t)`-specialised recentered branch — for every `t`, because the recentered branch
does not involve `T`. -/
theorem eval_recenter_spec (z x₀ t : F) (W : (F[X][X])[X]) (π : F[X])
    (hW : (W.map (mapRingHom (evalRingHom z))).eval π = 0) :
    ((recenter x₀ W).map (mapRingHom (spec z t))).eval (π.comp (X + C x₀)) = 0 := by
  set τ : F[X] →+* F[X] := eval₂RingHom (C : F →+* F[X]) (X + C x₀) with hτ
  have hinner : (mapRingHom (spec z t)).comp (innerRecenter x₀)
      = τ.comp (mapRingHom (evalRingHom z)) := by
    refine ringHom_ext₂ ?_ ?_ ?_
    · intro a
      simp [innerRecenter, spec, hτ]
    · simp [innerRecenter, spec, hτ]
    · simp [innerRecenter, spec, hτ]
  have hmap : (recenter x₀ W).map (mapRingHom (spec z t))
      = (W.map (mapRingHom (evalRingHom z))).map τ := by
    rw [recenter, coe_mapRingHom, Polynomial.map_map, Polynomial.map_map]
    congr 1
  have hπ : π.comp (X + C x₀) = τ π := by
    rw [hτ, coe_eval₂RingHom, comp]
  rw [hmap, hπ]
  set V := W.map (mapRingHom (evalRingHom z)) with hV
  have hev : (V.map τ).eval (τ π) = τ (V.eval π) := by
    rw [eval_map, eval₂_hom]
  rw [hev, hW, map_zero]

/-! ### Sizes of the recentered branch -/

/-- The shift preserves `Z`-heights. -/
theorem isHeightLE_shiftZ (x₀ : F) {c : F[X][X]} {d : ℕ} (hc : IsHeightLE c d) :
    IsHeightLE (shiftZ x₀ c) d := by
  rw [shiftZ, coe_eval₂RingHom, eval₂_eq_sum_range]
  refine IsHeightLE.sum _ _ fun m _ => ?_
  have h1 : IsHeightLE (C (c.coeff m) : F[X][X]) d := by
    intro i
    rw [coeff_C]
    split_ifs with h
    · exact hc m
    · simp
  have h2 : IsHeightLE (((X : F[X][X]) + C (C x₀)) ^ m) 0 := by
    have hbase : IsHeightLE ((X : F[X][X]) + C (C x₀)) 0 := by
      intro i
      rw [coeff_add, coeff_X, coeff_C]
      split_ifs <;> simp
    simpa using hbase.pow m
  simpa using h1.mul h2

/-- The `Y`-`U`-coefficients of the recentered branch: constants in `T`, of the same
`Z`-height. -/
theorem recenter_coeff_coeff (x₀ : F) (W : (F[X][X])[X]) (j i : ℕ) :
    ((recenter x₀ W).coeff j).coeff i
      = C ((shiftZ x₀ (W.coeff j)).coeff i) := by
  rw [recenter, coe_mapRingHom, coeff_map, innerRecenter_eq]
  rw [RingHom.comp_apply, coe_mapRingHom, coeff_map]

/-- Branch input: the recentered branch has `T`-degree-zero coefficients. -/
theorem recenter_coeff_natDegree (x₀ : F) (W : (F[X][X])[X]) (j i : ℕ) :
    (((recenter x₀ W).coeff j).coeff i).natDegree ≤ 0 := by
  rw [recenter_coeff_coeff]
  simp

/-- Branch input: the recentered branch inherits `Z`-heights. -/
theorem recenter_coeff_isHeightLE (x₀ : F) (W : (F[X][X])[X]) {dZ : ℕ}
    (hW : ∀ j, IsHeightLE (W.coeff j) dZ) (j i : ℕ) :
    IsHeightLE (((recenter x₀ W).coeff j).coeff i) dZ := by
  rw [recenter_coeff_coeff]
  intro l
  rw [coeff_C]
  split_ifs with h
  · exact isHeightLE_shiftZ x₀ (hW j) i
  · simp

/-- Branch input: the recentered branch has the same `Y`-degree bound. -/
theorem recenter_natDegree_le (x₀ : F) (W : (F[X][X])[X]) {d : ℕ}
    (hW : W.natDegree ≤ d) : (recenter x₀ W).natDegree ≤ d :=
  le_trans (natDegree_map_le) hW

/-! ### Sizes and nonvanishing of the fiber -/

/-- Evaluating at a scalar point does not raise the `Z`-degree. -/
theorem natDegree_eval_C_le {r : F[X][X]} {d : ℕ} (hr : IsHeightLE r d) (x₀ : F) :
    (r.eval (C x₀)).natDegree ≤ d := by
  rw [eval_eq_sum_range]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (natDegree_mul_le) ?_
  have h2 : ((C x₀ : F[X]) ^ i).natDegree = 0 := by
    simp [natDegree_pow]
  have h3 := hr i
  omega

/-- The fiber inherits the `T`-degree bound from the `Y`-degree. -/
theorem fiberAt_natDegree_le (x₀ : F) (W : (F[X][X])[X]) {d : ℕ}
    (hW : W.natDegree ≤ d) : (fiberAt x₀ W).natDegree ≤ d :=
  le_trans (natDegree_map_le) hW

/-- The fiber inherits `Z`-heights. -/
theorem fiberAt_isHeightLE (x₀ : F) (W : (F[X][X])[X]) {dZ : ℕ}
    (hW : ∀ j, IsHeightLE (W.coeff j) dZ) : IsHeightLE (fiberAt x₀ W) dZ := by
  intro j
  rw [fiberAt_coeff]
  exact natDegree_eval_C_le (hW j) x₀

/-- **The fiber of an irreducible branch is nonzero.**  If it vanished, the constant
`X - x₀` would divide the branch, contradicting irreducibility in `Y`-degree `≥ 1`. -/
theorem fiberAt_ne_zero (x₀ : F) {W : (F[X][X])[X]} (hirr : Irreducible W)
    (hdeg : 1 ≤ W.natDegree) : fiberAt x₀ W ≠ 0 := by
  intro h0
  -- All `Y`-coefficients vanish at `x₀`, so `X - x₀` divides them all.
  have hdvd : (C ((X : F[X][X]) - C (C x₀)) : (F[X][X])[X]) ∣ W := by
    rw [C_dvd_iff_dvd_coeff]
    intro j
    have hj : (W.coeff j).eval (C x₀) = 0 := by
      have := congrArg (fun p => Polynomial.coeff p j) h0
      simpa [fiberAt_coeff] using this
    exact (dvd_iff_isRoot (p := W.coeff j)).mpr hj
  obtain ⟨e, he⟩ := hdvd
  rcases hirr.isUnit_or_isUnit he with hu | hu
  · -- `X - x₀` is not a unit: it has positive `X`-degree.
    have : ((X : F[X][X]) - C (C x₀)).natDegree = 1 := natDegree_X_sub_C (C x₀)
    have := natDegree_eq_zero_of_isUnit (isUnit_C.mp hu)
    omega
  · -- The cofactor is a unit, so `W` has `Y`-degree 0.
    have hW0 : W ≠ 0 := hirr.ne_zero
    have he0 : e ≠ 0 := by rintro rfl; simp at he; exact hW0 he
    have hC0 : (C ((X : F[X][X]) - C (C x₀)) : (F[X][X])[X]) ≠ 0 := by
      rw [Ne, C_eq_zero]
      exact X_sub_C_ne_zero (C x₀)
    have hdegW : W.natDegree = 0 := by
      rw [he, natDegree_mul hC0 he0]
      rw [natDegree_C, natDegree_eq_zero_of_isUnit hu]
    omega

/-! ### The generalised specialisation lemma for resultants -/

/-- **Common roots kill the resultant, under any coefficient homomorphism.**
Generalises `eval_resultant_eq_zero_of_common_root` from `evalRingHom z` to an
arbitrary `χ : A →+* F`; the proof is the same Bezout evaluation. -/
theorem ringHom_resultant_eq_zero_of_common_root {A B : Type*} [CommRing A]
    [CommRing B] (χ : A →+* B) (H g : A[X]) {m n : ℕ}
    (hH : H.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0) (t : B)
    (hHt : eval₂ χ t H = 0) (hgt : eval₂ χ t g = 0) :
    χ (resultant H g m n) = 0 := by
  obtain ⟨u, v, -, -, hbez⟩ := exists_mul_add_mul_eq_C_resultant H g hH hg hmn
  have hmap := congrArg (eval₂ χ t) hbez
  rw [eval₂_add, eval₂_mul, eval₂_mul, hHt, hgt, zero_mul, zero_mul, add_zero,
    eval₂_C] at hmap
  exact hmap.symm

end JBAgreement
