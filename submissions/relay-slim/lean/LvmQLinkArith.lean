import LvmDecideV0
import LvmQSumcheck

/-!
# QA1 links: closed forms of the `CH` and `KS` link checks of `M3.ofParts` (the links of the former `M3.v0`) (WP-11b QA1)

`F`'s link functions (`LvmDecideV0`: `chShiftTarget0`, `chSc2Target0`, `chLink0`, `ksLink0`, WP-15a's
links, reviewed correct by WP-8) read `eq` tables as arrays (`eqKernelA`) and the shift kernel as
an `O(n²)` sum (`shiftEval`); `ksLink0`'s `contShift` sums over ≈ 14 k rows of two `2^15` tables.
The circuit evaluates the same values in `O(log)` rows; this module proves the forms equal:

* `eqKernel_getD`, `eqKernelA_eq`: `eqKernel a` at `z` is WP-10's `eqW a z` (first coordinate the
  low bit); `eqKernelA a = (eqKernel a).toArray`.
* `padConst_eq`, `chShiftTarget0_eq`: `C(1 + eq(ρ, 1ⁿ))` from six `eq` entries.
* `shiftEval_cons`: the shift kernel's low-bit recursion `S(x₀x, y₀y) = (1+x₀)y₀·eq(x,y) + x₀(1+y₀)·S(x,y)`
  (FR `FRShift.shiftPair`'s recursion, rf-k flock-recursive `FRShift.lean@8bff272b`; proved here for
  `F`'s index form directly).
* `chLink_sum_eq`: `Σ_q W̃(μ, q)·yS_q = α·Σ_{q<56} eq(ζ, q+8)·yS_q + β·Σ_{q<8} eq(ζ, q)·yS_{q+56}`,
  `α = Σ_m eq(μ,m)eq(λ,m)`, `β = Σ_m eq(μ,m)eq(λ,m+1)`.
* `contShift_eq`: `contShift` = `pre(B−1) + pre(K+30) + pre(K−1)` with `K = 2^r + 400`,
  `pre(H) = Σ_{k<H} eq(ρ', k)·eq(ρ, k+1)` in closed form by a low-bit recursion with three values
  per level (`preCF`, **`preCF_eq`**).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-! ## `eq` tables -/

/-- One doubling of `eqKernel`. -/
def eqStep (out : List FE) (r : FE) : List FE := out.map (· * (1 + r)) ++ out.map (· * r)

theorem eqKernel_foldl (a : List FE) : eqKernel a = a.foldl eqStep [1] := rfl

theorem sub_eq_add' (a b : FE) : a - b = a + b := CharTwo.sub_eq_add a b

theorem eqStep_length (out : List FE) (r : FE) : (eqStep out r).length = 2 * out.length := by
  simp [eqStep]; omega

theorem eqStep_getD (out : List FE) (r : FE) {w : Nat} (hw : w < 2 * out.length) :
    (eqStep out r).getD w 0 =
      if w < out.length then out.getD w 0 * (1 + r) else out.getD (w - out.length) 0 * r := by
  unfold eqStep
  split
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rename_i h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_map, List.getElem?_map]
    rw [List.getD_eq_getElem?_getD]
    cases out[w - out.length]? <;> simp

theorem foldl_eqStep_length : ∀ (a acc : List FE), (a.foldl eqStep acc).length = acc.length * 2 ^ a.length
  | [], acc => by simp
  | r :: rs, acc => by
    rw [List.foldl_cons, foldl_eqStep_length rs, eqStep_length, List.length_cons, pow_succ]; ring

theorem foldl_eqStep_getD : ∀ (a acc : List FE) (z : Nat), z < acc.length * 2 ^ a.length →
    (a.foldl eqStep acc).getD z 0 = acc.getD (z % acc.length) 0 * eqW a (z / acc.length)
  | [], acc, z, hz => by
    simp only [List.foldl_nil, List.length_nil, pow_zero, Nat.mul_one] at hz ⊢
    rw [Nat.mod_eq_of_lt hz]; simp [eqW]
  | r :: rs, acc, z, hz => by
    have hN : 0 < acc.length := by
      rcases Nat.eq_zero_or_pos acc.length with h | h
      · rw [h] at hz; simp at hz
      · exact h
    rw [List.foldl_cons, foldl_eqStep_getD rs (eqStep acc r) z
      (by rw [eqStep_length]; simp [pow_succ] at hz ⊢; nlinarith), eqStep_length]
    have hw : z % (2 * acc.length) < 2 * acc.length := Nat.mod_lt _ (by omega)
    rw [eqStep_getD acc r hw, eqW]
    have hdiv : z / (2 * acc.length) = z / acc.length / 2 := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [hdiv]
    have key : z % (2 * acc.length) = z % acc.length + acc.length * (z / acc.length % 2) := by
      rw [Nat.mul_comm 2 acc.length, Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one (z / acc.length) with h0 | h1
    · rw [key, h0, Nat.mul_zero, Nat.add_zero, if_pos (Nat.mod_lt _ hN), if_neg (by omega)]
      rw [sub_eq_add']; ring
    · rw [key, h1, Nat.mul_one, if_neg (by omega), if_pos rfl, Nat.add_sub_cancel]
      ring

/-- **`eqKernel a` at `z` is `eq(a, z)`** (`eqW`, first coordinate the low bit). -/
theorem eqKernel_getD (a : List FE) {z : Nat} (hz : z < 2 ^ a.length) :
    (eqKernel a).getD z 0 = eqW a z := by
  rw [eqKernel_foldl, foldl_eqStep_getD a [1] z (by simpa using hz)]
  simp [Nat.mod_one]

theorem eqKernel_length_lk (a : List FE) : (eqKernel a).length = 2 ^ a.length := by
  rw [eqKernel_foldl, foldl_eqStep_length]; simp

theorem eqKernelA_foldl : ∀ (a acc : List FE),
    a.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) acc.toArray =
      (a.foldl eqStep acc).toArray
  | [], acc => rfl
  | r :: rs, acc => by
    rw [List.foldl_cons, List.foldl_cons, ← eqKernelA_foldl rs]
    congr 1
    simp [eqStep]

theorem eqKernelA_eq (a : List FE) : eqKernelA a = (eqKernel a).toArray :=
  eqKernelA_foldl a [1]

theorem arr_getD (l : List FE) (i : Nat) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- An `eqKernelA` entry. -/
theorem eqKernelA_getD (a : List FE) {z : Nat} (hz : z < 2 ^ a.length) :
    (eqKernelA a).getD z 0 = eqW a z := by
  rw [eqKernelA_eq, arr_getD, eqKernel_getD a hz]

/-! ## List sums and products as `Finset` sums -/

theorem list_sum_range (f : Nat → FE) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]
    simp

theorem list_prod_range (f : Nat → FE) : ∀ n, ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, list_prod_range f n, Finset.prod_range_succ]
    simp

theorem foldl_mul (a : FE) (l : List FE) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, mul_assoc]

theorem prodE_eq_prod (l : List FE) : prodE l = l.prod := by
  rw [prodE, foldl_mul, one_mul]

theorem sumE_range_lk (f : Nat → FE) (n : Nat) : sumE ((List.range n).map f) = ∑ i ∈ Finset.range n, f i := by
  rw [sumE_eq_sum, list_sum_range]

theorem prodE_range (f : Nat → FE) (n : Nat) : prodE ((List.range n).map f) = ∏ i ∈ Finset.range n, f i := by
  rw [prodE_eq_prod, list_prod_range]

/-- `dot` of two lists of length `n`. -/
theorem dot_range : ∀ (l r : List FE), l.length = r.length →
    dot l r = ∑ i ∈ Finset.range l.length, l.getD i 0 * r.getD i 0
  | [], [], _ => by simp [dot]
  | a :: l, b :: r, h => by
    have ih := dot_range l r (by simpa using h)
    unfold dot at ih ⊢
    rw [List.zipWith_cons_cons, List.foldl_cons, foldl_add] at *
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← ih]; ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- `eqEval` of two points of length `n`: `Π (1 + x_i + y_i)`. -/
theorem eqEval_cons (x0 y0 : FE) (x y : List FE) : eqEval (x0 :: x) (y0 :: y) = (1 + x0 + y0) * eqEval x y := by
  unfold eqEval
  rw [List.zipWith_cons_cons, List.foldl_cons, foldl_mul, foldl_mul]
  ring

theorem eqEval_nil (y : List FE) : eqEval [] y = 1 := by simp [eqEval]

/-! ## The `CH` link -/

theorem omegaCH_getD (lam zeta : List FE) {l p : Nat} (hl : l < 2 ^ lam.length) (hp : p < 2 ^ zeta.length) :
    ((omegaCH lam zeta).getD l #[]).getD p 0 = eqW lam l * eqW zeta p := by
  unfold omegaCH
  rw [eqKernelA_eq, eqKernelA_eq]
  have hl' : l < (eqKernel lam).length := by rw [eqKernel_length_lk]; exact hl
  have hp' : p < (eqKernel zeta).length := by rw [eqKernel_length_lk]; exact hp
  simp [Array.getD_eq_getD_getElem?, hl', hp']
  rw [← List.getD_eq_getElem _ 0 hl', ← List.getD_eq_getElem _ 0 hp', eqKernel_getD _ hl, eqKernel_getD _ hp]

/-- `Pad43`'s constant bits: `0x43` in byte 0 (bits 0, 1, 6 of lane 0), `0x01` in byte 33 (bit 8 of
lane 4). -/
theorem padConst_eq (lam zeta : List FE) (hl : lam.length = 3) (hz : zeta.length = 6) :
    padConst (omegaCH lam zeta) =
      eqW lam 0 * (eqW zeta 0 + eqW zeta 1 + eqW zeta 6) + eqW lam 4 * eqW zeta 8 := by
  have h : ∀ l p, l < 8 → p < 64 → ((omegaCH lam zeta).getD l #[]).getD p 0 = eqW lam l * eqW zeta p :=
    fun l p hl8 hp64 => omegaCH_getD lam zeta (by rw [hl]; omega) (by rw [hz]; omega)
  have e : padConst (omegaCH lam zeta) =
      0 + ((omegaCH lam zeta).getD 0 #[]).getD 0 0 + ((omegaCH lam zeta).getD 0 #[]).getD 1 0 +
        ((omegaCH lam zeta).getD 0 #[]).getD 6 0 + ((omegaCH lam zeta).getD 4 #[]).getD 8 0 := rfl
  rw [e, h 0 0 (by omega) (by omega), h 0 1 (by omega) (by omega), h 0 6 (by omega) (by omega),
    h 4 8 (by omega) (by omega)]
  ring

/-- **The `CH` shift sumcheck's claim** in closed form. -/
theorem chShiftTarget0_eq (p : Params) (chal : List FE) (hc : chal.length = p.logN + 9) :
    chShiftTarget0 p chal =
      (eqW ((chal.drop p.logN).take 3) 0 * (eqW (chal.drop (p.logN + 3)) 0 + eqW (chal.drop (p.logN + 3)) 1 +
        eqW (chal.drop (p.logN + 3)) 6) + eqW ((chal.drop p.logN).take 3) 4 * eqW (chal.drop (p.logN + 3)) 8) *
      (1 + (chal.take p.logN).prod) := by
  unfold chShiftTarget0 chSplit eqOnes
  simp only []
  rw [padConst_eq _ _ (by simp; omega) (by simp; omega), prodE_eq_prod]

/-- The two-round sumcheck's claim: `f₁ + S(ρ, ρ')·Σ_p eq(ζ, p)·inS_p`. -/
theorem chSc2Target0_eq (p : Params) (chal : List FE) (shift : List FE × FE) (inS : List FE)
    (hc : chal.length = p.logN + 9) (hi : inS.length = 64) :
    chSc2Target0 p chal shift inS = shift.2 + shiftEval (chal.take p.logN) shift.1 *
      ∑ q ∈ Finset.range 64, eqW (chal.drop (p.logN + 3)) q * inS.getD q 0 := by
  unfold chSc2Target0 chSplit
  simp only []
  have hz : (chal.drop (p.logN + 3)).length = 6 := by simp; omega
  rw [dot_range _ _ (by rw [eqKernel_length_lk, hz, hi]; rfl), eqKernel_length_lk, hz, show (2 : Nat) ^ 6 = 64 from rfl]
  congr 2
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [eqKernel_getD _ (by rw [hz]; exact Finset.mem_range.mp hq)]

theorem eqEval_range : ∀ (x y : List FE), x.length = y.length →
    eqEval x y = ∏ u ∈ Finset.range x.length, (1 + x.getD u 0 + y.getD u 0)
  | [], [], _ => by simp [eqEval_nil]
  | x0 :: x, y0 :: y, h => by
    rw [eqEval_cons, eqEval_range x y (by simpa using h), List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- **The shift kernel's low-bit recursion** (FR `FRShift.shiftPair`, rf-k flock-recursive
`FRShift.lean@8bff272b`): the carry of `k + 1` stops at bit `0` (`(1 + x₀)y₀·eq`) or passes it
(`x₀(1 + y₀)·S`). -/
theorem shiftEval_cons (x0 y0 : FE) (x y : List FE) (h : x.length = y.length) :
    shiftEval (x0 :: x) (y0 :: y) = (1 + x0) * y0 * eqEval x y + x0 * (1 + y0) * shiftEval x y := by
  unfold shiftEval
  simp only [List.length_cons, sumE_range_lk, prodE_range]
  rw [Finset.sum_range_succ', eqEval_range x y h, Finset.mul_sum, add_comm]
  congr 1
  · simp only [Finset.range_zero, Finset.prod_empty, one_mul, List.getD_cons_zero,
      Nat.add_sub_cancel, Nat.sub_zero]
    congr 1
    refine Finset.prod_congr rfl fun u _ => ?_
    rw [show 0 + 1 + u = u + 1 by omega, List.getD_cons_succ, List.getD_cons_succ]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [show x.length + 1 - (j + 1) - 1 = x.length - j - 1 by omega]
    have h2 : ∀ u, j + 1 + 1 + u = (j + 1 + u) + 1 := fun u => by omega
    simp only [h2, List.getD_cons_succ]
    ring

theorem shiftEval_nil (y : List FE) : shiftEval [] y = 0 := by simp [shiftEval, sumE]

/-- **The `CH` link's sum** `Σ_q W̃(μ, q)·yS_q`, regrouped by the two halves of `Pad43`'s shift. -/
theorem chLink_sum_eq (lam zeta mu yS : List FE) (hl : lam.length = 3) (hz : zeta.length = 6)
    (hm : mu.length = 2) :
    sumE ((List.range 64).map fun q => sumE ((List.range 4).map fun m =>
        (eqKernel mu).getD m 0 * padWeight (omegaCH lam zeta) m q) * yS.getD q 0) =
      (∑ m ∈ Finset.range 4, eqW mu m * eqW lam m) * ∑ q ∈ Finset.range 56, eqW zeta (q + 8) * yS.getD q 0 +
      (∑ m ∈ Finset.range 4, eqW mu m * eqW lam (m + 1)) * ∑ q ∈ Finset.range 8, eqW zeta q * yS.getD (q + 56) 0 := by
  have hom : ∀ l p, l < 8 → p < 64 → ((omegaCH lam zeta).getD l #[]).getD p 0 = eqW lam l * eqW zeta p :=
    fun l p hl8 hp64 => omegaCH_getD lam zeta (by rw [hl]; omega) (by rw [hz]; omega)
  have hmu : ∀ m, m < 4 → (eqKernel mu).getD m 0 = eqW mu m :=
    fun m hm4 => eqKernel_getD mu (by rw [hm]; omega)
  simp only [sumE_range_lk]
  rw [show 64 = 56 + 8 from rfl, Finset.sum_range_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_range.mp hq
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm' => ?_
    have hm4 := Finset.mem_range.mp hm'
    rw [hmu m hm4, padWeight, if_pos (by omega), hom m (q + 8) (by omega) (by omega)]
    ring
  · refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_range.mp hq
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm' => ?_
    have hm4 := Finset.mem_range.mp hm'
    rw [hmu m hm4, padWeight, if_neg (by omega), show 56 + q - 56 = q by omega,
      hom (m + 1) q (by omega) (by omega), show 56 + q = q + 56 by omega]
    ring

/-! ## The `KS` link: interval shift sums in closed form -/

theorem sum_range_two_mul' (g : Nat → FE) : ∀ N : Nat,
    ∑ x ∈ Finset.range (2 * N), g x = ∑ x ∈ Finset.range N, (g (2 * x) + g (2 * x + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul' g N, Finset.sum_range_succ]
    ring

theorem eqW_even' (r : FE) (rs : List FE) (x : Nat) : eqW (r :: rs) (2 * x) = (1 + r) * eqW rs x := by
  simp only [eqW]; rw [if_neg (by omega), show 2 * x / 2 = x by omega, sub_eq_add']

theorem eqW_odd' (r : FE) (rs : List FE) (x : Nat) : eqW (r :: rs) (2 * x + 1) = r * eqW rs x := by
  simp only [eqW]; rw [if_pos (by omega), show (2 * x + 1) / 2 = x by omega]

/-- `pre(H) = Σ_{k<H} eq(y, k)·eq(x, k + 1)`. -/
def preSum (x y : List FE) (H : Nat) : FE := ∑ k ∈ Finset.range H, eqW y k * eqW x (k + 1)

/-- `E(H) = Σ_{k<H} eq(y, k)·eq(x, k)`. -/
def eSum (x y : List FE) (H : Nat) : FE := ∑ k ∈ Finset.range H, eqW y k * eqW x k

/-- One level of `preCF`: from the values one bit up to these, `h` the bound's bit here. -/
def preStep (x0 y0 : FE) (h : Bool) (r : FE × FE × FE) : FE × FE × FE :=
  let E1 := if h then r.2.1 + r.2.2 else r.2.1
  ((1 + y0) * x0 * E1 + y0 * (1 + x0) * r.1,
   (1 + y0) * (1 + x0) * E1 + y0 * x0 * r.2.1,
   (if h then y0 * x0 else (1 + y0) * (1 + x0)) * r.2.2)

/-- **The closed form** of `(pre(H), E(H), eq(y,H)·eq(x,H))`: a low-bit recursion, three values per
level, `H`'s bits static (`O(n)` rows). -/
def preCF : List FE → List FE → Nat → FE × FE × FE
  | x0 :: x, y0 :: y, H => preStep x0 y0 (H % 2 = 1) (preCF x y (H / 2))
  | _, _, H => ((H : FE), (H : FE), 1)

theorem sum_range_parity (f : Nat → FE) (H : Nat) :
    ∑ k ∈ Finset.range H, f k = ∑ k ∈ Finset.range (H / 2 + H % 2), f (2 * k) + ∑ k ∈ Finset.range (H / 2), f (2 * k + 1) := by
  rcases Nat.mod_two_eq_zero_or_one H with h0 | h1
  · have hH : H = 2 * (H / 2) := by omega
    rw [h0, Nat.add_zero]
    conv_lhs => rw [hH]
    rw [sum_range_two_mul', Finset.sum_add_distrib]
  · have hH : H = 2 * (H / 2) + 1 := by omega
    rw [h1]
    conv_lhs => rw [hH]
    rw [Finset.sum_range_succ, sum_range_two_mul', Finset.sum_add_distrib, Finset.sum_range_succ]
    ring

theorem preSum_cons (x0 y0 : FE) (x y : List FE) (H : Nat) :
    preSum (x0 :: x) (y0 :: y) H =
      (1 + y0) * x0 * eSum x y (H / 2 + H % 2) + y0 * (1 + x0) * preSum x y (H / 2) := by
  unfold preSum eSum
  rw [sum_range_parity (fun k => eqW (y0 :: y) k * eqW (x0 :: x) (k + 1)) H, Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) (Finset.sum_congr rfl fun k _ => ?_)
  · rw [eqW_even', eqW_odd']; ring
  · rw [eqW_odd', show 2 * k + 1 + 1 = 2 * (k + 1) by ring, eqW_even']; ring

theorem eSum_cons (x0 y0 : FE) (x y : List FE) (H : Nat) :
    eSum (x0 :: x) (y0 :: y) H =
      (1 + y0) * (1 + x0) * eSum x y (H / 2 + H % 2) + y0 * x0 * eSum x y (H / 2) := by
  unfold eSum
  rw [sum_range_parity (fun k => eqW (y0 :: y) k * eqW (x0 :: x) k) H, Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => ?_) (Finset.sum_congr rfl fun k _ => ?_)
  · rw [eqW_even', eqW_even']; ring
  · rw [eqW_odd', eqW_odd']; ring

theorem pt_cons (x0 y0 : FE) (x y : List FE) (H : Nat) :
    eqW (y0 :: y) H * eqW (x0 :: x) H =
      (if H % 2 = 1 then y0 * x0 else (1 + y0) * (1 + x0)) * (eqW y (H / 2) * eqW x (H / 2)) := by
  simp only [eqW]
  split <;> (try simp only [sub_eq_add']) <;> ring

theorem eSum_succ_bit (x y : List FE) (H : Nat) :
    (if H % 2 = 1 then eSum x y (H / 2) + eqW y (H / 2) * eqW x (H / 2) else eSum x y (H / 2)) =
      eSum x y (H / 2 + H % 2) := by
  rcases Nat.mod_two_eq_zero_or_one H with h0 | h1
  · rw [h0]; simp
  · rw [h1, if_pos rfl, eSum, eSum, Finset.sum_range_succ]

theorem preCF_eq : ∀ (x y : List FE) (H : Nat), x.length = y.length →
    preCF x y H = (preSum x y H, eSum x y H, eqW y H * eqW x H)
  | [], [], H, _ => by simp [preCF, preSum, eSum, eqW]
  | x0 :: x, y0 :: y, H, h => by
    have ih := preCF_eq x y (H / 2) (by simpa using h)
    rw [show preCF (x0 :: x) (y0 :: y) H = preStep x0 y0 (H % 2 = 1) (preCF x y (H / 2)) from rfl, ih,
      preSum_cons, eSum_cons, pt_cons, ← eSum_succ_bit]
    unfold preStep
    by_cases hb : H % 2 = 1 <;> simp [hb]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem foldl_add_map (g : Nat → FE) : ∀ (l : List Nat) (a : FE),
    l.foldl (fun acc i => acc + g i) a = a + (l.map g).sum
  | [], a => by simp
  | i :: l, a => by rw [List.foldl_cons, foldl_add_map g l, List.map_cons, List.sum_cons]; ring

/-- **`contShift` in closed form**: the trace's continuation rows `[1, B)` and the WOTS leaf's rows
`[K + 1, K + 32)` (`K = 2^r + 399`), each an interval of the shift sum. -/
theorem contShift_eq (p : Params) (rho rho' : List FE) (h1 : rho.length = p.ksLog)
    (h2 : rho'.length = p.ksLog) (hB : 1 ≤ spongeBlocks p) (hB2 : spongeBlocks p ≤ 2 ^ p.ksLog)
    (hK : 2 ^ p.recRowsLog + 431 ≤ 2 ^ p.ksLog) :
    contShift p rho rho' = preSum rho rho' (spongeBlocks p - 1) +
      preSum rho rho' (2 ^ p.recRowsLog + 399 + 31) + preSum rho rho' (2 ^ p.recRowsLog + 399) := by
  have hg : ∀ i, 1 ≤ i → i < 2 ^ p.ksLog → (eqKernelA rho).getD i 0 * (eqKernelA rho').getD (i - 1) 0 =
      eqW rho' (i - 1) * eqW rho (i - 1 + 1) := by
    intro i hi1 hi2
    rw [eqKernelA_getD _ (by rw [h1]; exact hi2), eqKernelA_getD _ (by rw [h2]; omega),
      Nat.sub_add_cancel hi1]; ring
  have hc : contShift p rho rho' =
      ((contRows p).map fun i => (eqKernelA rho).getD i 0 * (eqKernelA rho').getD (i - 1) 0).sum := by
    unfold contShift; rw [foldl_add_map, zero_add]
  rw [hc, contRows, List.map_append, List.sum_append]
  generalize hR : 2 ^ p.recRowsLog = R at *
  have hA : (((List.range (spongeBlocks p - 1)).map (· + 1)).map fun i =>
      (eqKernelA rho).getD i 0 * (eqKernelA rho').getD (i - 1) 0).sum = preSum rho rho' (spongeBlocks p - 1) := by
    rw [List.map_map, list_sum_range, preSum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    simp only [Function.comp_def]
    rw [hg (k + 1) (by omega) (by omega), Nat.add_sub_cancel]
  have hS : (((List.range 31).map (R + 399 + 1 + ·)).map fun i =>
      (eqKernelA rho).getD i 0 * (eqKernelA rho').getD (i - 1) 0).sum =
      ∑ k ∈ Finset.range 31, eqW rho' (R + 399 + k) * eqW rho (R + 399 + k + 1) := by
    rw [List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    simp only [Function.comp_def]
    rw [hg _ (by omega) (by omega), show R + 399 + 1 + k - 1 = R + 399 + k by omega]
  have hP : preSum rho rho' (R + 399 + 31) = preSum rho rho' (R + 399) +
      ∑ k ∈ Finset.range 31, eqW rho' (R + 399 + k) * eqW rho (R + 399 + k + 1) := by
    unfold preSum; rw [Finset.sum_range_add]
  have h22 := CharTwo.add_self_eq_zero (preSum rho rho' (R + 399))
  rw [hA, hS, hP]
  linear_combination -h22

end Lvm.Q1
