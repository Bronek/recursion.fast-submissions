import LvmQBuildLemmas
import LvmSelfEval
import LvmDecideWhir

/-!
# QA2 gadgets: shared base (row equations of placed blocks, running sums, `F`'s loops as sums)

WP-11b-QA2 writes `Q_arith` for the WHIR, ring-switching, bus and table finals as LoopIR blocks
(`LvmLoopIR`) and proves each block's cells equal to `F`'s function (`LvmDecide*`) on the same data.
This module holds what every gadget uses:

* `prefix_cells`: a one-row (or `w`-row) accumulator block whose result at index `x` adds `f x` to its
  result at `x − 1` holds prefix sums; `prefix_diff`: in characteristic 2 the sum over a window is the
  sum of two prefix cells (no zero prologue is needed: the offset cancels).
* `forSum`, `foldRow0_eq`, `foldRowE_eq`: `F`'s `for` loops as `Finset` sums.
* Stream convention: `K` input cell `p` is lane `p` of `Σ` (`lane sig p = kAt sig (8p)`, WP-10 §4);
  `F`'s `feAt sig (8p)` is the `loadE` of lanes `p, p+1, p+2` (`loadE_eq`).

Reuse (RULES "Reuse first"): the list/sum identities follow leanerVM
`LeanerVM/Protocol/ToCompPoly/FinLoop.lean` (`foldl_add_eq_add_sum`), restated on `Lvm.FE`. Gadgets are
written with QL's builder (`LvmQBuild*`).
-/

set_option autoImplicit false

namespace Lvm.Loop

open Program

/-! ## `F`'s loops as sums -/

-- adapted from leanerVM LeanerVM/Protocol/ToCompPoly/FinLoop.lean (foldl_add_eq_add_sum), on Lvm.FE
theorem foldl_add_sum (g : Nat → FE) : ∀ (l : List Nat) (a : FE),
    l.foldl (fun acc k => acc + g k) a = a + (l.map g).sum
  | [], a => by simp
  | k :: l, a => by rw [List.foldl_cons, foldl_add_sum g l]; simp [add_assoc]

theorem sum_map_range (g : Nat → FE) : ∀ w, ((List.range w).map g).sum = ∑ k ∈ Finset.range w, g k
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range g n, Finset.sum_range_succ]
    simp

/-- An accumulating `for` loop over `[0:w]` is the sum. -/
theorem forSum (w : Nat) (g : Nat → FE) :
    (Id.run do
      let mut acc : FE := 0
      for k in [0:w] do
        acc := acc + g k
      return acc) = ∑ k ∈ Finset.range w, g k := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  simp [foldl_add_sum, List.range'_eq_map_range, ← sum_map_range]
  rfl

/-- `F`'s level-0 row fold as a sum (`LvmDecideWhir.foldRow0`). -/
theorem foldRow0_eq (sig : ByteArray) (eq : Array FE) (o w : Nat) :
    foldRow0 sig eq o w =
      ∑ k ∈ Finset.range w, FE.ofK (kAt sig (o + 8 * (w - 1 - k))) * eq.getD k 0 := by
  rw [foldRow0, ← forSum]; simp [FE.smulBase_eq_mul]

/-- `F`'s later-level row fold as a sum (`LvmDecideWhir.foldRowE`). -/
theorem foldRowE_eq (sig : ByteArray) (eq : Array FE) (o w : Nat) :
    foldRowE sig eq o w = ∑ k ∈ Finset.range w, feAt sig (o + 24 * k) * eq.getD k 0 := by
  rw [foldRowE, ← forSum]

/-! ## The stream as input cells -/

/-- Lane `p` of the stream `Σ` (WP-10 §4: input `K` cell `p` is lane `p`). -/
def lane (sig : ByteArray) (p : Nat) : FK := kAt sig (8 * p)

theorem loadE_eq (a b c : FK) :
    FE.ofK a + FE.y * FE.ofK b + FE.y * FE.y * FE.ofK c = ⟨a, b, c⟩ := by
  apply FE.ext_limb
  intro l hl
  interval_cases l <;> simp [limb, mul_c₀, mul_c₁, mul_c₂, FE.y, FE.ofK]

/-- `F`'s scalar at byte `8p` is the `loadE` of lanes `p, p + 1, p + 2`. -/
theorem feAt_lanes (sig : ByteArray) (p : Nat) :
    feAt sig (8 * p) = FE.ofK (lane sig p) + FE.y * FE.ofK (lane sig (p + 1)) +
      FE.y * FE.y * FE.ofK (lane sig (p + 2)) := by
  rw [loadE_eq]; simp only [feAt, lane]; congr 2


theorem Mem.rd_E (M : Mem) (n : Nat) : M.rd .E n = M.e n := rfl
theorem Mem.rd_K (M : Mem) (n : Nat) : M.rd .K n = FE.ofK (M.k n) := rfl

/-! ## Running sums -/

/-- **Prefix sums.** If the cells `c + w·x` (`x < n`) satisfy `cell(x) = f x + cell(x − 1)`, with
`cell(−1) = c − w`, then `cell(c − w + w·m) = cell(c − w) + Σ_{i<m} f i` for `m ≤ n`. -/
theorem prefix_cells (E : Nat → FE) (c w n : Nat) (hw : w ≤ c) (f : Nat → FE)
    (hstep : ∀ x < n, E (c + w * x) = f x + E (c - w + w * x)) :
    ∀ m ≤ n, E (c - w + w * m) = E (c - w) + ∑ i ∈ Finset.range m, f i := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, show c - w + w * (m + 1) = c + w * m by rw [Nat.mul_succ]; omega,
      hstep m (by omega), ih (by omega)]
    ring

/-- **Window sums** in characteristic 2: the sum of two prefix cells is the sum over the window. -/
theorem prefix_diff (a : FE) (f : Nat → FE) (m k : Nat) :
    (a + ∑ i ∈ Finset.range (m + k), f i) + (a + ∑ i ∈ Finset.range m, f i) =
      ∑ i ∈ Finset.range k, f (m + i) := by
  rw [Finset.sum_range_add]
  have h2 : ∀ x : FE, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  linear_combination h2 a + h2 (∑ i ∈ Finset.range m, f i)

/-- Two-dimensional loop index of `[l, a]`. -/
theorem unflat_la {l a k q : Nat} (hk : k < 2 ^ l) (hq : q < 2 ^ a) :
    unflat [l, a] (k + 2 ^ l * q) = [k, q] := unflat_two hk hq

theorem lt_size_la {l a k q : Nat} (hk : k < 2 ^ l) (hq : q < 2 ^ a) :
    k + 2 ^ l * q < 2 ^ (l + a) := by
  rw [pow_add]
  calc k + 2 ^ l * q < 2 ^ l * (q + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ 2 ^ l * 2 ^ a := Nat.mul_le_mul_left _ hq

namespace Build

theorem loop_adv (dims : List Nat) (tpl : List LRow) (p : Ptr) :
    p.adv (loop dims tpl p).2 = ⟨p.k + ltw .K tpl * 2 ^ dims.sum, p.e + ltw .E tpl * 2 ^ dims.sum⟩ := by
  have := mkLoop_tw p dims tpl
  simp only [loop_apply, Ptr.adv, segsW, List.map, Seg.w, this, Block.size, Block.lsize, List.sum_cons,
    List.sum_nil, add_zero]
  simp [mkLoop]

end Build

end Lvm.Loop
