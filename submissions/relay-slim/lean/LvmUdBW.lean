-- WP-6 (UD). Ported from flock-recursive `FRProximityFold.lean` sections `G6_FRProximityBW` and
-- `G6_FRProximityLine` (branch kk/base `c52529eb`): `mul_mem_degreeLT`, `poly_eq_zero_of_vanish`,
-- `bw_unique`, `polyOf`, `colPoly`, `rowPoly`, `bwRes`, `bwMap`, `bw_exists`, `bw_E_ne`,
-- `bw_few_zero_cols`, `line_eq_root`, `mca_ud_line_cover`. Changes: positions are any finite type
-- `ι` with an embedding `domain : ι ↪ F` (FR: `Fin n` and an injective `x`); the line is
-- `u₀ + z u₁` (FR: `u₀ + z (u₁ − u₀)`); the threshold is an agreement count `A` (FR: `n − e`).
import LvmRS
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.ComputeDegree

/-!
# Correlated agreement on lines in the unique-decoding range (Berlekamp–Welch with a variable)

Generic over a field `F`, a finite position type `ι` (`n = |ι|`), `domain : ι ↪ F`, the code
`C = RS[F, domain, k]` and an error bound `e` with `2e + k ≤ n` (`2e < d = n − k + 1`).

For words `u₀ u₁ : ι → F`, `lineBad C e u₀ u₁` is the set of `z` for which `u₀ + z u₁` agrees with
a codeword `w` on at least `n − e` positions but **no** pair `v₀ v₁ ∈ C` has joint agreement with
`(u₀, u₁)` exactly equal to that agreement set. **`lineBad_cover`**: that set is covered by a
finite set of at most `lineMca n k e = k e + n` elements. No threshold on the number of close `z`
is needed; the bound holds in every field.

The proof (Berlekamp–Welch with a variable `Z`, solved by counting rather than by a rank argument
over `F(Z)`; FR's argument):

1. **Interpolation** (`bw_exists`). With `a := n − k − e ≥ e`, there are coefficient arrays
   `E` (`X`-degree `≤ a`, `Z`-degree `≤ e`) and `N` (`X`-degree `< n − e`, `Z`-degree `≤ e + 1`),
   not both zero, with `N(x_j, Z) = E(x_j, Z) · (u₀_j + Z u₁_j)` in `F[Z]` for every `j`:
   `(a+1)(e+1) + (n−e)(e+2)` unknowns against `n (e+2)` linear equations.
2. `E ≠ 0` (else `N` vanishes at `n` points with `X`-degree `< n`), so `E(x_j, Z) = 0` for at
   most `a` positions (`bw_few_zero_cols`); pick `k` positions `J` with `E(x_j, Z) ≠ 0`, and let
   `v₀, v₁ ∈ C` interpolate `u₀, u₁` on `J`.
3. For `z` off the `≤ k e` roots of the `E(x_j, Z)`, `j ∈ J`, and `u₀ + z u₁` close to `w = P(x)`:
   `bw_unique` gives `N(X, z) = E(X, z) P`, so `u₀ + z u₁ = P` on `J`, so `w = v₀ + z v₁`.
4. Off the joint agreement set of `(u₀, u₁)` with `(v₀, v₁)`, `u₀ + z u₁ − (v₀ + z v₁)` is a
   nonzero affine function of `z` at each position: at most `n` further values of `z` add an
   agreement. For every other close `z` the agreement set is exactly the joint one.
-/

namespace LeanVM.Protocol.Whir.Ud

open Polynomial Finset

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-! ## Degree facts and Berlekamp–Welch uniqueness -/

/-- `deg p ≤ a`, `deg q < b` give `deg (p q) < a + b`. -/
theorem mul_mem_degreeLT {a b : ℕ} {p q : F[X]} (hp : p ∈ degreeLT F (a + 1))
    (hq : q ∈ degreeLT F b) : p * q ∈ degreeLT F (a + b) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hq0 : q = 0
  · simp [hq0]
  have h1 := (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp)
  have h2 := (natDegree_lt_iff_degree_lt hq0).2 (mem_degreeLT.1 hq)
  rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt (mul_ne_zero hp0 hq0), natDegree_mul hp0 hq0]
  omega

omit [Fintype ι] in
/-- A polynomial of degree `< m` vanishing at `m` of the points `domain j` is zero. -/
theorem poly_eq_zero_of_vanish (domain : ι ↪ F) {m : ℕ} {p : F[X]}
    (hp : p ∈ degreeLT F m) (S : Finset ι) (hS : m ≤ S.card)
    (h : ∀ j ∈ S, p.eval (domain j) = 0) : p = 0 := by
  have hk : ((m : ℕ) : WithBot ℕ) ≤ (S.card : WithBot ℕ) := by exact_mod_cast hS
  exact Polynomial.eq_of_degrees_lt_of_eval_index_eq S (domain.injective.injOn)
    ((mem_degreeLT.1 hp).trans_le hk) (by simp) fun j hj ↦ by simp [h j hj]

omit [Fintype ι] in
/-- **Berlekamp–Welch uniqueness** (FR `bw_unique`): if `N(x_j) = E(x_j) · u_j` at every
position, `deg E ≤ a`, `deg N < a + k`, `deg P < k`, and `u_j = P(x_j)` on a set `S` of `a + k`
positions, then `N = E · P`. -/
theorem bw_unique (domain : ι ↪ F) {a k : ℕ} {E N P : F[X]}
    (hE : E ∈ degreeLT F (a + 1)) (hN : N ∈ degreeLT F (a + k)) (hP : P ∈ degreeLT F k)
    (u : ι → F) (hEN : ∀ j, N.eval (domain j) = E.eval (domain j) * u j) (S : Finset ι)
    (hS : a + k ≤ S.card) (hagree : ∀ j ∈ S, u j = P.eval (domain j)) : N = E * P := by
  rw [← sub_eq_zero]
  refine poly_eq_zero_of_vanish domain (sub_mem hN (mul_mem_degreeLT hE hP)) S hS fun j hj ↦ ?_
  rw [eval_sub, eval_mul, hEN, hagree j hj, sub_self]

/-! ## Coefficient arrays as polynomials -/

/-- The polynomial `Σ_{a<m} d_a X^a`. -/
noncomputable def polyOf {m : ℕ} (d : Fin m → F) : F[X] := ∑ a : Fin m, C (d a) * X ^ (a : ℕ)

omit [Fintype ι] in
theorem polyOf_mem {m : ℕ} (d : Fin m → F) : polyOf d ∈ degreeLT F m :=
  mem_degreeLT.2 (degree_sum_fin_lt d)

omit [Fintype ι] in
theorem eval_polyOf {m : ℕ} (d : Fin m → F) (y : F) :
    (polyOf d).eval y = ∑ a, d a * y ^ (a : ℕ) := by
  simp [polyOf, eval_finsetSum]

omit [Fintype ι] in
theorem coeff_polyOf {m : ℕ} (d : Fin m → F) (a : Fin m) : (polyOf d).coeff a = d a := by
  simp [polyOf, finsetSum_coeff, coeff_X_pow, Fin.val_inj]

omit [Fintype ι] in
theorem polyOf_add {m : ℕ} (d d' : Fin m → F) : polyOf (d + d') = polyOf d + polyOf d' := by
  simp [polyOf, add_mul, sum_add_distrib]

omit [Fintype ι] in
theorem polyOf_smul {m : ℕ} (c : F) (d : Fin m → F) : polyOf (c • d) = C c * polyOf d := by
  simp [polyOf, mul_sum, mul_assoc]

/-- `B(y, Z) = Σ_a y^a B_a(Z)` for the coefficient array `B a b` of `X^a Z^b`. -/
noncomputable def colPoly {m T : ℕ} (B : Fin m → Fin T → F) (y : F) : F[X] :=
  ∑ a : Fin m, C (y ^ (a : ℕ)) * polyOf (B a)

/-- `B(X, z)`. -/
noncomputable def rowPoly {m T : ℕ} (B : Fin m → Fin T → F) (z : F) : F[X] :=
  polyOf fun a ↦ (polyOf (B a)).eval z

omit [Fintype ι] in
theorem eval_colPoly {m T : ℕ} (B : Fin m → Fin T → F) (y z : F) :
    (colPoly B y).eval z = (rowPoly B z).eval y := by
  simp [colPoly, rowPoly, eval_polyOf, eval_finsetSum, mul_comm]

omit [Fintype ι] in
theorem coeff_colPoly {m T : ℕ} (B : Fin m → Fin T → F) (y : F) (t : Fin T) :
    (colPoly B y).coeff t = (polyOf fun a ↦ B a t).eval y := by
  simp only [colPoly, finsetSum_coeff, coeff_C_mul, coeff_polyOf, eval_polyOf]
  exact sum_congr rfl fun a _ ↦ mul_comm _ _

omit [Fintype ι] in
theorem colPoly_mem {m T : ℕ} (B : Fin m → Fin T → F) (y : F) : colPoly B y ∈ degreeLT F T :=
  sum_mem fun a _ ↦ by rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (polyOf_mem _)

omit [Fintype ι] in
theorem colPoly_add {m T : ℕ} (B B' : Fin m → Fin T → F) (y : F) :
    colPoly (B + B') y = colPoly B y + colPoly B' y := by
  simp [colPoly, polyOf_add, mul_add, sum_add_distrib]

omit [Fintype ι] in
theorem colPoly_smul {m T : ℕ} (c : F) (B : Fin m → Fin T → F) (y : F) :
    colPoly (c • B) y = C c * colPoly B y := by
  simp only [colPoly, Pi.smul_apply, polyOf_smul, mul_sum]
  exact sum_congr rfl fun _ _ ↦ by ring

omit [Fintype ι] in
theorem colPoly_zero {m T : ℕ} (y : F) : colPoly (0 : Fin m → Fin T → F) y = 0 := by
  simpa using colPoly_smul (0 : F) (0 : Fin m → Fin T → F) y

/-! ## The Berlekamp–Welch system with a variable `Z` -/

/-- The residual `N(x_j, Z) − E(x_j, Z) (u₀_j + Z u₁_j)` at position `j`. -/
noncomputable def bwRes {m m' T T' : ℕ} (domain : ι ↪ F) (u₀ u₁ : ι → F)
    (E : Fin m → Fin T → F) (N : Fin m' → Fin T' → F) (j : ι) : F[X] :=
  colPoly N (domain j) - colPoly E (domain j) * (C (u₀ j) + X * C (u₁ j))

/-- The residuals' first `T + 1` coefficients, an `F`-linear map of `(E, N)`. -/
noncomputable def bwMap (domain : ι ↪ F) (u₀ u₁ : ι → F) (m m' T : ℕ) :
    ((Fin m → Fin T → F) × (Fin m' → Fin (T + 1) → F)) →ₗ[F] (ι → Fin (T + 1) → F) where
  toFun p j t := (bwRes domain u₀ u₁ p.1 p.2 j).coeff t
  map_add' p q := by
    funext j t
    simp only [bwRes, Prod.fst_add, Prod.snd_add, colPoly_add, Pi.add_apply]
    rw [← coeff_add]; exact congrArg (coeff · t) (by ring)
  map_smul' c p := by
    funext j t
    simp only [bwRes, Prod.smul_fst, Prod.smul_snd, colPoly_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← coeff_C_mul]; exact congrArg (coeff · t) (by ring)

omit [Fintype ι] in
theorem bwRes_mem {m m' T : ℕ} (domain : ι ↪ F) (u₀ u₁ : ι → F) (E : Fin m → Fin T → F)
    (N : Fin m' → Fin (T + 1) → F) (j : ι) : bwRes domain u₀ u₁ E N j ∈ degreeLT F (T + 1) := by
  refine sub_mem (colPoly_mem N _) ?_
  rw [mul_comm, Nat.add_comm T 1]
  refine mul_mem_degreeLT ?_ (colPoly_mem E _)
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
  compute_degree!

/-- **Step 1** (`bw_exists`): with `2e + k ≤ n` the system has a nonzero solution with
`X`-degrees `≤ n − k − e`, `< n − e` and `Z`-degrees `≤ e`, `≤ e + 1`. -/
theorem bw_exists (domain : ι ↪ F) (u₀ u₁ : ι → F) {k e : ℕ}
    (h : 2 * e + k ≤ Fintype.card ι) :
    ∃ (E : Fin (Fintype.card ι - k - e + 1) → Fin (e + 1) → F)
      (N : Fin (Fintype.card ι - e) → Fin (e + 2) → F),
      (E, N) ≠ 0 ∧ ∀ j, bwRes domain u₀ u₁ E N j = 0 := by
  set n := Fintype.card ι with hn
  have hdim : Module.finrank F (ι → Fin (e + 1 + 1) → F) <
      Module.finrank F ((Fin (n - k - e + 1) → Fin (e + 1) → F) ×
        (Fin (n - e) → Fin (e + 1 + 1) → F)) := by
    simp only [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_self,
      Fintype.card_fin, mul_one, sum_const, card_univ, smul_eq_mul, ← hn]
    obtain ⟨a, ha⟩ : ∃ a, n - k - e = e + a := ⟨n - k - e - e, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, n = e + b := ⟨n - e, by omega⟩
    rw [ha, hb, Nat.add_sub_cancel_left]
    ring_nf
    omega
  obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1
    (LinearMap.ker_ne_bot_of_finrank_lt (f := bwMap domain u₀ u₁ _ _ _) hdim)
  refine ⟨p.1, p.2, hp0, fun j ↦ ?_⟩
  have hres := bwRes_mem domain u₀ u₁ p.1 p.2 j
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hres
  ext t
  rw [coeff_zero]
  by_cases ht : t < e + 2
  · exact congrFun (congrFun (LinearMap.mem_ker.1 hp) j) ⟨t, ht⟩
  · exact hres t (by omega)

/-- **Step 2a**: a solution with `E = 0` and `m' ≤ n` is zero. -/
theorem bw_E_ne (domain : ι ↪ F) {u₀ u₁ : ι → F} {m m' T T' : ℕ}
    (hm' : m' ≤ Fintype.card ι) {E : Fin m → Fin T → F} {N : Fin m' → Fin T' → F}
    (hne : (E, N) ≠ 0) (hres : ∀ j, bwRes domain u₀ u₁ E N j = 0) : E ≠ 0 := by
  rintro rfl
  apply hne
  ext a t
  · rfl
  have hj : ∀ j, (polyOf fun a ↦ N a t).eval (domain j) = 0 := fun j ↦ by
    have := congrArg (fun p ↦ p.coeff t) (hres j)
    simpa [bwRes, colPoly_zero, coeff_colPoly] using this
  have h0 := poly_eq_zero_of_vanish domain (polyOf_mem _) univ (by simpa using hm')
    fun j _ ↦ hj j
  simpa [coeff_polyOf] using congrArg (fun p ↦ p.coeff a) h0

omit [Fintype ι] in
/-- **Step 2b** (`bw_few_zero_cols`): for `E ≠ 0` of `X`-degree `< m`, `E(x_j, Z) = 0` at fewer
than `m` positions. -/
theorem bw_few_zero_cols (domain : ι ↪ F) {m T : ℕ} {E : Fin m → Fin T → F} (hE : E ≠ 0)
    (S : Finset ι) (hS : ∀ j ∈ S, colPoly E (domain j) = 0) : S.card + 1 ≤ m := by
  classical
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hE
  obtain ⟨b, hb⟩ := Function.ne_iff.1 ha
  set p := polyOf fun a ↦ E a b
  have hp0 : p ≠ 0 := fun h0 ↦ hb (by simpa [p, coeff_polyOf] using congrArg (coeff · a) h0)
  have hsub : (S.image domain).val ⊆ p.roots := by
    intro y hy
    simp only [Finset.mem_val, mem_image] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [mem_roots hp0, IsRoot, ← coeff_colPoly, hS j hj, coeff_zero]
  have h1 := card_le_degree_of_subset_roots hsub
  rw [card_image_of_injective _ domain.injective] at h1
  have := (natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 (polyOf_mem fun a ↦ E a b))
  omega

/-! ## The bad set of a line -/

variable [DecidableEq F]

/-- The positions where two single words agree. -/
def wAgree (u w : ι → F) : Finset ι := univ.filter fun j ↦ u j = w j

/-- The positions where `u₀ = v₀` and `u₁ = v₁` (the joint agreement of two pairs of words). -/
def wAgree₂ (u₀ u₁ v₀ v₁ : ι → F) : Finset ι := univ.filter fun j ↦ u₀ j = v₀ j ∧ u₁ j = v₁ j

omit [Field F] in
@[simp] theorem mem_wAgree {u w : ι → F} {j : ι} : j ∈ wAgree u w ↔ u j = w j := by
  simp [wAgree]

omit [Field F] in
@[simp] theorem mem_wAgree₂ {u₀ u₁ v₀ v₁ : ι → F} {j : ι} :
    j ∈ wAgree₂ u₀ u₁ v₀ v₁ ↔ u₀ j = v₀ j ∧ u₁ j = v₁ j := by
  simp [wAgree₂]

/-- The **bad set** of the line `u₀ + z u₁` (FR `lineBad`, direction form): the `z` for which
`u₀ + z u₁` agrees with a codeword `w` on at least `n − e` positions, but no pair of codewords has
joint agreement with `(u₀, u₁)` equal to that agreement set. -/
def lineBad (C : Submodule F (ι → F)) (e : ℕ) (u₀ u₁ : ι → F) : Set F :=
  {z | ∃ w ∈ C, Fintype.card ι - e ≤ (wAgree (u₀ + z • u₁) w).card ∧
    ¬ ∃ v₀ ∈ C, ∃ v₁ ∈ C, wAgree₂ u₀ u₁ v₀ v₁ = wAgree (u₀ + z • u₁) w}

/-- The count the proof gives: `k e + n`. -/
def lineMca (n k e : ℕ) : ℕ := k * e + n

omit [Fintype ι] [DecidableEq F] in
/-- At a position where `(u₀, u₁) ≠ (v₀, v₁)`, `u₀ + z u₁ = v₀ + z v₁` holds only at
`z = (v₀ − u₀) / (u₁ − v₁)`. -/
theorem line_eq_root {a₀ a₁ b₀ b₁ z : F} (hne : ¬ (a₀ = b₀ ∧ a₁ = b₁))
    (h : a₀ + z * a₁ = b₀ + z * b₁) : z = (b₀ - a₀) / (a₁ - b₁) := by
  by_cases hc : a₁ - b₁ = 0
  · exfalso; apply hne
    have h1 : a₁ = b₁ := sub_eq_zero.mp hc
    exact ⟨by rw [h1] at h; linear_combination h, h1⟩
  · field_simp
    linear_combination h

/-- **The line cover** (FR `mca_ud_line_cover`, direction form): for any field `F`, any
`domain : ι ↪ F` and `2e + k ≤ n`, the bad set of every line is contained in a finite set of at
most `k e + n` elements. -/
theorem lineBad_cover [DecidableEq ι] (domain : ι ↪ F) {k e : ℕ}
    (h : 2 * e + k ≤ Fintype.card ι) (u₀ u₁ : ι → F) :
    ∃ B : Finset F, B.card ≤ lineMca (Fintype.card ι) k e ∧
      lineBad (rsCode domain k) e u₀ u₁ ⊆ B := by
  set n := Fintype.card ι with hn
  -- step 1: the interpolating pair
  obtain ⟨E, N, hne, hres⟩ := bw_exists domain u₀ u₁ h
  have hE := bw_E_ne domain (by omega) hne hres
  -- step 2: `k` positions where `E(x_j, Z) ≠ 0`, and the interpolated line
  have hfew := bw_few_zero_cols domain hE (univ.filter fun j ↦ colPoly E (domain j) = 0)
    fun j hj ↦ (mem_filter.1 hj).2
  obtain ⟨J, hJA, hJ⟩ : ∃ J ⊆ univ.filter (fun j ↦ ¬ colPoly E (domain j) = 0), J.card = k := by
    apply exists_subset_card_eq
    have := card_filter_add_card_filter_not (s := (univ : Finset ι))
      fun j ↦ colPoly E (domain j) = 0
    rw [card_univ] at this
    omega
  obtain ⟨v₀, hv₀, hv₀J⟩ := exists_mem_rsCode_eqOn domain J hJ.le u₀
  obtain ⟨v₁, hv₁, hv₁J⟩ := exists_mem_rsCode_eqOn domain J hJ.le u₁
  -- the cover
  let S₁ := J.biUnion fun j ↦ (colPoly E (domain j)).roots.toFinset
  let S₂ := univ.image fun j ↦ (v₀ j - u₀ j) / (u₁ j - v₁ j)
  refine ⟨S₁ ∪ S₂, ?_, ?_⟩
  · have h1 : S₁.card ≤ k * e := by
      refine (card_biUnion_le).trans ((sum_le_card_nsmul _ _ e fun j hj ↦ ?_).trans
        (by rw [hJ, smul_eq_mul]))
      have := (natDegree_lt_iff_degree_lt (mem_filter.1 (hJA hj)).2).2
        (mem_degreeLT.1 (colPoly_mem E (domain j)))
      exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (by omega))
    have h2 : S₂.card ≤ n := card_image_le.trans (by simp [hn])
    exact (card_union_le _ _).trans (by unfold lineMca; omega)
  rintro z ⟨w, hw, hcl, hnot⟩
  by_contra hzB
  obtain ⟨hz1, hz2⟩ := not_or.1 (mt mem_union.2 hzB)
  apply hnot
  refine ⟨v₀, hv₀, v₁, hv₁, ?_⟩
  set uz := u₀ + z • u₁
  have hVz : v₀ + z • v₁ ∈ rsCode domain k := add_mem hv₀ (Submodule.smul_mem _ _ hv₁)
  -- step 3: `w` is the line's codeword at `z`
  have hwV : w = v₀ + z • v₁ := by
    obtain ⟨P, hP, hPw⟩ := mem_rsCode_iff_eval.1 hw
    have hspec : ∀ j, (rowPoly N z).eval (domain j) = (rowPoly E z).eval (domain j) * uz j :=
      fun j ↦ by
        have := congrArg (eval z) (hres j)
        simp only [bwRes, eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_zero,
          eval_colPoly, sub_eq_zero] at this
        simpa [uz, smul_eq_mul, mul_comm z] using this
    have hNE := bw_unique domain (a := n - k - e) (k := k) (polyOf_mem _)
      (by rw [show n - k - e + k = n - e by omega]; exact polyOf_mem _) (mem_degreeLT.2 hP) uz
      hspec (wAgree uz w) (by omega) fun j hj ↦ by rw [hPw]; exact mem_wAgree.1 hj
    refine eq_of_mem_code_of_agreeOn domain hw hVz J hJ.ge fun j hj ↦ ?_
    have hEz : (rowPoly E z).eval (domain j) ≠ 0 := fun h0 ↦ hz1 (mem_biUnion.2 ⟨j, hj,
      Multiset.mem_toFinset.2 ((mem_roots (mem_filter.1 (hJA hj)).2).2 (by rwa [IsRoot.def,
        eval_colPoly]))⟩)
    have h1 := hspec j
    rw [hNE, eval_mul] at h1
    rw [← hPw j, show P.eval (domain j) = uz j from mul_left_cancel₀ hEz h1]
    simp [uz, hv₀J j hj, hv₁J j hj]
  -- step 4: the agreement set is the joint one
  rw [hwV]
  ext j
  simp only [mem_wAgree₂, mem_wAgree, uz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h0, h1⟩; rw [h0, h1]
  · intro hj
    by_contra hnj
    exact hz2 (mem_image.2 ⟨j, mem_univ _, (line_eq_root hnj hj).symm⟩)

end LeanVM.Protocol.Whir.Ud
