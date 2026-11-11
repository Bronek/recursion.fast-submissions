-- New for lvm (WP-8): the non-cyclic shift kernel and its closed form (BLUEPRINT §4.1, §7.2 `linkSpec`).
-- The low-bit recursion of the shift's extension is adapted from flock-recursive `FRShift.lean`
-- (`shiftMle`, `shift_mle`, `shiftPair`), restated on leanVM's `eqAt` and lists.
import LvmKeccakMultilinear
import LvmEqLemmas

/-!
# The shift kernel

The chain link `in_{i+1} = Pad43(Y_i)` holds for the rows `i ≤ N − 2` (`N = 2^n`), and the `KS`
sponge link reads the previous row. Both are reduced by a sumcheck over the row `k` whose kernels
are, on the cube (characteristic two, `|ρ| = n`):

* `shiftK ρ k = [1 ≤ k] · eq(ρ, k − 1)`: the **non-cyclic** shift (no wrap from row `N − 1` to row
  `0`: in characteristic two the cyclic and non-cyclic kernels differ by `eq(ρ, 1^n)·eq(0, k)`);
* `maskK ρ k = [k ≤ N − 2] · eq(ρ, k)`: the equality kernel with the last row masked.

Their multilinear extensions at a point `y` have closed forms the verifier computes in `O(n)`:

* **`sum_shiftK`**: `Σ_k eq(y, k)·shiftK ρ k = shiftEvalE ρ y`, where `shiftEvalE` is V_S's
  `shiftEval` (`LvmDecideV0`) over `E`: `Σ_j [Π_{t<j} x_t(1 + y_t)]·(1 + x_j) y_j·Π_{u>j}(1 + x_u + y_u)`
  (the carry of `i + 1` stops at bit `j`);
* **`sum_maskK`**: `Σ_k eq(y, k)·maskK ρ k = eqEval ρ y + Π ρ · Π y` (V_S's `eqMasked`);
* `sum_maskK_one`: `Σ_k maskK ρ k = 1 + Π ρ` (the shift sumcheck's target factor).

The route is FRShift's recursion `S_{n+1}(x, y) = (1 + x₀) y₀ eq(x', y') + x₀ (1 + y₀) S_n(x', y')`
(`shiftRec`, `shiftRec_eq`), then the closed form unrolled (`shiftEvalE_eq_shiftRec`).
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Complete Finset

/-! ## Kernels -/

/-- The non-cyclic shift kernel on the cube: `[1 ≤ k] eq(ρ, k − 1)`. -/
def shiftK (ρ : List E) (k : ℕ) : E := if 1 ≤ k then eqAt ρ (k - 1) else 0

/-- The equality kernel with the last row masked: `[k + 1 < 2^|ρ|] eq(ρ, k)`. -/
def maskK (ρ : List E) (k : ℕ) : E := if k + 1 < 2 ^ ρ.length then eqAt ρ k else 0

/-- V_S's `shiftEval` (`LvmDecideV0`) over `E`: the shift's extension in `O(n)`. -/
def shiftEvalE (x y : List E) : E :=
  let n := x.length
  sumE ((List.range n).map fun j =>
    prodE ((List.range j).map fun t => x.getD t 0 * (1 + y.getD t 0)) *
      ((1 + x.getD j 0) * y.getD j 0) *
      prodE ((List.range (n - j - 1)).map fun u =>
        1 + x.getD (j + 1 + u) 0 + y.getD (j + 1 + u) 0))

/-- V_S's `eqMasked` over `E`: `eq(x, y) + eq(x, 1^n) eq(1^n, y)`. -/
def eqMaskedE (x y : List E) : E := eqEval x y + prodE x * prodE y

/-- FRShift's low-bit recursion of the shift's extension. -/
def shiftRec : List E → List E → E
  | x :: xs, y :: ys => (1 + x) * y * eqEval xs ys + x * (1 + y) * shiftRec xs ys
  | _, _ => 0

/-! ## Sums of products of equality weights -/

theorem eqAt_even (r : E) (rs : List E) (w : ℕ) : eqAt (r :: rs) (2 * w) = (1 + r) * eqAt rs w := by
  rw [eqAt_cons, if_neg (by omega), show 2 * w / 2 = w by omega]

theorem eqAt_odd (r : E) (rs : List E) (w : ℕ) : eqAt (r :: rs) (2 * w + 1) = r * eqAt rs w := by
  rw [eqAt_cons, if_pos (by omega), show (2 * w + 1) / 2 = w by omega]

/-- **The equality weights pair to `eqEval`.** -/
theorem sum_eqAt_mul_eqAt : ∀ (x y : List E), x.length = y.length →
    ∑ w ∈ range (2 ^ x.length), eqAt x w * eqAt y w = eqEval x y
  | [], [], _ => by simp [eqEval]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    simp only [List.length_cons, add_left_inj] at h
    rw [List.length_cons, sum_cube_succ, eqEval_cons, ← sum_eqAt_mul_eqAt x y h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [eqAt_even, eqAt_even, eqAt_odd, eqAt_odd]
    linear_combination (a * b * (eqAt x w * eqAt y w)) * CharTwo.two_eq_zero (R := E)

/-- The weight of the last row is the product of the coordinates. -/
theorem eqAt_last : ∀ x : List E, eqAt x (2 ^ x.length - 1) = prodE x
  | [] => by simp [prodE]
  | a :: x => by
    have h : 2 ^ (a :: x).length - 1 = 2 * (2 ^ x.length - 1) + 1 := by
      rw [List.length_cons, pow_succ]; have := Nat.one_le_two_pow (n := x.length); omega
    rw [h, eqAt_odd, eqAt_last x, prodE_eq_prod', prodE_eq_prod', List.prod_cons]
where
  prodE_eq_prod' (l : List E) : prodE l = l.prod := by unfold prodE; rw [List.prod_eq_foldl]

theorem prodE_cons (a : E) (l : List E) : prodE (a :: l) = a * prodE l := by
  rw [eqAt_last.prodE_eq_prod', eqAt_last.prodE_eq_prod', List.prod_cons]

/-- **The shift's recursion** is the shift sum. -/
theorem shiftRec_eq : ∀ (x y : List E), x.length = y.length →
    shiftRec x y = ∑ i ∈ range (2 ^ x.length),
      if i + 1 < 2 ^ x.length then eqAt x i * eqAt y (i + 1) else 0
  | [], [], _ => by simp [shiftRec]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    simp only [List.length_cons, add_left_inj] at h
    rw [shiftRec, shiftRec_eq x y h, ← sum_eqAt_mul_eqAt x y h, Finset.mul_sum, Finset.mul_sum,
      List.length_cons, sum_cube_succ, Finset.sum_add_distrib]
    have hp : 0 < 2 ^ x.length := Nat.two_pow_pos _
    congr 1
    · refine Finset.sum_congr rfl fun w hw ↦ ?_
      have hw' := Finset.mem_range.1 hw
      rw [if_pos (by rw [pow_succ]; omega), eqAt_even, eqAt_odd]
      ring
    · refine Finset.sum_congr rfl fun w hw ↦ ?_
      have hw' := Finset.mem_range.1 hw
      by_cases hl : w + 1 < 2 ^ x.length
      · rw [if_pos hl, if_pos (show 2 * w + 1 + 1 < 2 ^ (x.length + 1) by rw [pow_succ]; omega),
          eqAt_odd, show 2 * w + 1 + 1 = 2 * (w + 1) by ring, eqAt_even]
        ring
      · rw [if_neg hl, if_neg (show ¬ 2 * w + 1 + 1 < 2 ^ (x.length + 1) by rw [pow_succ]; omega),
          mul_zero]

theorem list_sum_map_range (f : ℕ → E) : ∀ n, ((List.range n).map f).sum = ∑ j ∈ range n, f j
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_map_range f n,
      Finset.sum_range_succ]
    simp

theorem list_prod_map_range (f : ℕ → E) : ∀ n, ((List.range n).map f).prod = ∏ j ∈ range n, f j
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, list_prod_map_range f n,
      Finset.prod_range_succ]
    simp

/-- `eqEval` as a product over the coordinates. -/
theorem eqEval_eq_prod_range : ∀ (x y : List E), x.length = y.length →
    eqEval x y = ∏ u ∈ range x.length, (1 + x.getD u 0 + y.getD u 0)
  | [], [], _ => by simp [eqEval]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    simp only [List.length_cons, add_left_inj] at h
    rw [eqEval_cons, eqEval_eq_prod_range x y h, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- V_S's closed form as a finite sum. -/
theorem shiftEvalE_eq_sum (x y : List E) :
    shiftEvalE x y = ∑ j ∈ range x.length,
      (∏ t ∈ range j, x.getD t 0 * (1 + y.getD t 0)) * ((1 + x.getD j 0) * y.getD j 0) *
        ∏ u ∈ range (x.length - j - 1), (1 + x.getD (j + 1 + u) 0 + y.getD (j + 1 + u) 0) := by
  simp only [shiftEvalE, sumE_eq_sum, eqAt_last.prodE_eq_prod', list_sum_map_range,
    list_prod_map_range]

/-- The closed form peels its first coordinate as FRShift's recursion. -/
theorem shiftEvalE_cons (a b : E) (x y : List E) (h : x.length = y.length) :
    shiftEvalE (a :: x) (b :: y) = (1 + a) * b * eqEval x y + a * (1 + b) * shiftEvalE x y := by
  rw [shiftEvalE_eq_sum, shiftEvalE_eq_sum, eqEval_eq_prod_range x y h, List.length_cons,
    Finset.sum_range_succ', Finset.mul_sum]
  have h0 : (∏ t ∈ range 0, (a :: x).getD t 0 * (1 + (b :: y).getD t 0)) *
      ((1 + (a :: x).getD 0 0) * (b :: y).getD 0 0) *
      ∏ u ∈ range (x.length + 1 - 0 - 1), (1 + (a :: x).getD (0 + 1 + u) 0 + (b :: y).getD (0 + 1 + u) 0) =
      (1 + a) * b * ∏ u ∈ range x.length, (1 + x.getD u 0 + y.getD u 0) := by
    rw [Finset.prod_range_zero, one_mul, show x.length + 1 - 0 - 1 = x.length by omega]
    refine congrArg _ (Finset.prod_congr rfl fun u _ ↦ ?_)
    rw [show 0 + 1 + u = u + 1 by omega]
    rfl
  have h1 : ∀ j ∈ range x.length,
      (∏ t ∈ range (j + 1), (a :: x).getD t 0 * (1 + (b :: y).getD t 0)) *
        ((1 + (a :: x).getD (j + 1) 0) * (b :: y).getD (j + 1) 0) *
        ∏ u ∈ range (x.length + 1 - (j + 1) - 1),
          (1 + (a :: x).getD (j + 1 + 1 + u) 0 + (b :: y).getD (j + 1 + 1 + u) 0) =
      a * (1 + b) * ((∏ t ∈ range j, x.getD t 0 * (1 + y.getD t 0)) *
        ((1 + x.getD j 0) * y.getD j 0) *
        ∏ u ∈ range (x.length - j - 1), (1 + x.getD (j + 1 + u) 0 + y.getD (j + 1 + u) 0)) := by
    intro j _
    rw [Finset.prod_range_succ', show x.length + 1 - (j + 1) - 1 = x.length - j - 1 by omega]
    have e : ∀ u, (1 + (a :: x).getD (j + 1 + 1 + u) 0 + (b :: y).getD (j + 1 + 1 + u) 0) =
        (1 + x.getD (j + 1 + u) 0 + y.getD (j + 1 + u) 0) := fun u ↦ by
      rw [show j + 1 + 1 + u = (j + 1 + u) + 1 by omega]; rfl
    simp only [e]
    change (∏ t ∈ range j, x.getD t 0 * (1 + y.getD t 0)) * (a * (1 + b)) *
      ((1 + x.getD j 0) * y.getD j 0) * _ = _
    ring
  rw [Finset.sum_congr rfl h1, h0, add_comm]

theorem shiftEvalE_nil (y : List E) : shiftEvalE [] y = 0 := by simp [shiftEvalE, sumE]

/-- **The closed form is FRShift's recursion.** -/
theorem shiftEvalE_eq_shiftRec : ∀ (x y : List E), x.length = y.length →
    shiftEvalE x y = shiftRec x y
  | [], [], _ => by simp [shiftEvalE_nil, shiftRec]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    simp only [List.length_cons, add_left_inj] at h
    rw [shiftEvalE_cons a b x y h, shiftRec, shiftEvalE_eq_shiftRec x y h]

/-! ## The kernels' extensions -/

/-- **The shift kernel's extension** at `y` is V_S's closed form. -/
theorem sum_shiftK (ρ y : List E) (h : ρ.length = y.length) :
    ∑ k ∈ range (2 ^ ρ.length), eqAt y k * shiftK ρ k = shiftEvalE ρ y := by
  rw [shiftEvalE_eq_shiftRec ρ y h, shiftRec_eq ρ y h]
  have hp : 0 < 2 ^ ρ.length := Nat.two_pow_pos _
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ ρ.length = M + 1 := ⟨2 ^ ρ.length - 1, by omega⟩
  rw [hM, Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [shiftK, Nat.le_add_left, ite_true, Nat.add_sub_cancel, show ¬ (1 ≤ 0) by omega,
    ite_false, mul_zero, add_zero, show ¬ (M + 1 < M + 1) by omega]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [if_pos (by have := Finset.mem_range.1 hi; omega)]
  ring

/-- **The masked kernel's extension** at `y` is V_S's `eqMasked`. -/
theorem sum_maskK (ρ y : List E) (h : ρ.length = y.length) :
    ∑ k ∈ range (2 ^ ρ.length), eqAt y k * maskK ρ k = eqMaskedE ρ y := by
  have hp : 0 < 2 ^ ρ.length := Nat.two_pow_pos _
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ ρ.length = M + 1 := ⟨2 ^ ρ.length - 1, by omega⟩
  have hfull := sum_eqAt_mul_eqAt ρ y h
  have hl := eqAt_last ρ
  have hly := eqAt_last y
  rw [← h] at hly
  rw [hM] at hfull hl hly ⊢
  rw [Finset.sum_range_succ] at hfull ⊢
  simp only [Nat.add_sub_cancel] at hl hly
  rw [eqMaskedE, ← hfull, hl, hly]
  simp only [maskK, hM, show ¬ (M + 1 < M + 1) by omega, ite_false, mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun i hi ↦ by
    rw [if_pos (by have := Finset.mem_range.1 hi; omega), mul_comm]]
  linear_combination (-(prodE ρ * prodE y)) * CharTwo.two_eq_zero (R := E)

/-- The masked kernel sums to `1 + Π ρ` (the shift sumcheck's target factor). -/
theorem sum_maskK_one (ρ : List E) :
    ∑ k ∈ range (2 ^ ρ.length), maskK ρ k = 1 + prodE ρ := by
  have hp : 0 < 2 ^ ρ.length := Nat.two_pow_pos _
  have hs := sum_eqAt ρ
  have hl := eqAt_last ρ
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ ρ.length = M + 1 := ⟨2 ^ ρ.length - 1, by omega⟩
  rw [hM] at hs hl ⊢
  rw [Finset.sum_range_succ] at hs ⊢
  simp only [Nat.add_sub_cancel] at hl
  simp only [maskK, hM, show ¬ (M + 1 < M + 1) by omega, ite_false, add_zero]
  rw [Finset.sum_congr rfl fun i hi ↦ if_pos (by have := Finset.mem_range.1 hi; omega)]
  rw [hl] at hs
  linear_combination hs + (-(prodE ρ)) * CharTwo.two_eq_zero (R := E)

end Lvm.KG
