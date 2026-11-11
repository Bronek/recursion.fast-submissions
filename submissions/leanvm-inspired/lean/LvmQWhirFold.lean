import LvmQWhirBase

/-!
# QA2: WHIR row folds (`foldRow0`, `foldRowE`) as builder gadgets

The hot loop of `Q_arith` (BLUEPRINT §4.6): per opened position `q`, the fold of its row
`Σ_k eq(α, k) · row_q[k]` (`LvmDecideWhir.foldRow0`, `foldRowE`). Per chunk of `2^a` positions:
one loop of dims `[l, a]` (word `k` fastest) with **one template row**, a running sum over all
`(q, k)`: `acc(k + 2^l q) = row_q[k] · e[k] + acc(previous)` (`Opd.prev`; at iteration 0 it reads
whatever cell precedes the loop); then a loop of dims `[a]` taking differences of prefix cells
(`prefix_diff`: characteristic 2, so no zero prologue is needed). Cost per position: level 0,
`2^l` `E·K` rows (14 words) + one `lin` (12); later levels `2^l` × (`loadE` 10 + `E·E` 16) + one
`lin`. Two pieces per chunk.

* `rowFold0 l a lb S er`: word `k` of position `q` is the `K` cell `lb + k + S·q` (a stream lane);
  `e[k]` is the `E` cell `er + k`, the **reversed** `eq` table (`eq(α, 2^l − 1 − k)`): `foldRow0`
  pairs `eq[k]` with word `2^l − 1 − k`, and strides are non-negative.
* `rowFoldE l a lb S er`: scalar `k` of position `q` is lanes `lb + 3k + S·q + (0, 1, 2)` (a
  `loadE` row); `e[k]` the `eq` table in natural order.

Theorems: `rowFold0_spec`, `rowFoldE_spec` (fold cells = sums of cells) and **`rowFold0_eq`,
`rowFoldE_eq`** (= `F`'s `foldRow0`/`foldRowE` on the stream: Q_arith_eq for the row folds).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-- Level-0 row folds of `2^a` positions with `2^l` words each; the fold cells. -/
def rowFold0 (l a lb S er : Nat) : BM (Nat → Cell) := do
  let p ← getPtr
  let _ ← loop [l, a] [⟨.muladd, .E, [.abs ⟨.K, lb, [1, S]⟩, .abs ⟨.E, er, [1, 0]⟩, .prev 0]⟩]
  let d ← loop [a] [⟨.lin 1 0, .E,
    [.abs ⟨.E, p.e - 1 + 1 * 2 ^ l, [1 * 2 ^ l]⟩, .abs ⟨.E, p.e - 1, [1 * 2 ^ l]⟩]⟩]
  pure fun q => d.cell 0 q

/-- Later-level row folds of `2^a` positions with `2^l` `E` scalars each; the fold cells. -/
def rowFoldE (l a lb S er : Nat) : BM (Nat → Cell) := do
  let p ← getPtr
  let _ ← loop [l, a]
    [⟨.loadE, .E, [.abs ⟨.K, lb, [3, S]⟩, .abs ⟨.K, lb + 1, [3, S]⟩, .abs ⟨.K, lb + 2, [3, S]⟩]⟩,
     ⟨.muladd, .E, [.cur 0, .abs ⟨.E, er, [1, 0]⟩, .prev 1]⟩]
  let d ← loop [a] [⟨.lin 1 0, .E,
    [.abs ⟨.E, p.e - 1 + 2 * 2 ^ l, [2 * 2 ^ l]⟩, .abs ⟨.E, p.e - 1, [2 * 2 ^ l]⟩]⟩]
  pure fun q => d.cell 0 q

theorem unflat_lt {l a x : Nat} (hx : x < 2 ^ (l + a)) :
    unflat [l, a] x = [x % 2 ^ l, x / 2 ^ l] := by
  have : x / 2 ^ l < 2 ^ a := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm]; exact hx
  simp [unflat, Nat.mod_eq_of_lt this]

theorem split_la {l q i : Nat} (hi : i < 2 ^ l) :
    (2 ^ l * q + i) % 2 ^ l = i ∧ (2 ^ l * q + i) / 2 ^ l = q := by
  constructor
  · rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi
  · rw [Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hi, Nat.add_zero]

theorem flat_split {l x : Nat} : x = x % 2 ^ l + 2 ^ l * (x / 2 ^ l) := by
  have := Nat.div_add_mod x (2 ^ l); omega

variable {c : Ctx} {M : Mem}

/-- The difference loop: from a prefix law on the cells `p₀ + w·m`, its cell `q` is the window
sum. -/
theorem diff_spec {p : Ptr} {l a w p₀ : Nat} (f : Nat → FE)
    (h : SegsHold c M p (loop [a] [⟨.lin 1 0, .E,
      [.abs ⟨.E, p₀ + w * 2 ^ l, [w * 2 ^ l]⟩, .abs ⟨.E, p₀, [w * 2 ^ l]⟩]⟩] p).2)
    (hpre : ∀ m ≤ 2 ^ (l + a), M.e (p₀ + w * m) = M.e p₀ + ∑ i ∈ Finset.range m, f i)
    {q : Nat} (hq : q < 2 ^ a) :
    ((loop [a] [⟨.lin 1 0, .E,
      [.abs ⟨.E, p₀ + w * 2 ^ l, [w * 2 ^ l]⟩, .abs ⟨.E, p₀, [w * 2 ^ l]⟩]⟩] p).1.cell 0 q).val M =
      ∑ i ∈ Finset.range (2 ^ l), f (2 ^ l * q + i) := by
  have hr := loop_rel h (jf := q) (t := 0) (by simpa using hq) (by simp)
  simp only [LRel, List.getD_cons_zero, LoopOut.arg, List.getD_cons_succ, loop_apply,
    Opd.val_abs, Mem.rd_E, Addr.at, dot, unflat, Nat.mod_eq_of_lt hq] at hr
  have hq1 : 2 ^ l * (q + 1) ≤ 2 ^ (l + a) := by rw [pow_add]; exact Nat.mul_le_mul_left _ hq
  rw [loop_apply, hr, show p₀ + w * 2 ^ l + (w * 2 ^ l * q + 0) = p₀ + w * (2 ^ l * q + 2 ^ l) by ring,
    show p₀ + (w * 2 ^ l * q + 0) = p₀ + w * (2 ^ l * q) by ring,
    hpre _ (by rw [← Nat.mul_succ]; exact hq1),
    hpre _ (le_trans (Nat.mul_le_mul_left _ (by omega)) hq1), ofK_one, ofK_zero, one_mul, add_zero]
  exact prefix_diff _ _ _ _

theorem rowFold0_step {p : Ptr} {l a lb S er : Nat} {x : Nat}
    (h : SegsHold c M p (loop [l, a]
      [⟨.muladd, .E, [.abs ⟨.K, lb, [1, S]⟩, .abs ⟨.E, er, [1, 0]⟩, .prev 0]⟩] p).2)
    (hx : x < 2 ^ (l + a)) :
    M.e (p.e + 1 * x) = FE.ofK (M.k (lb + x % 2 ^ l + S * (x / 2 ^ l))) * M.e (er + x % 2 ^ l) +
      M.e (p.e - 1 + 1 * x) := by
  have hx' : x < 2 ^ [l, a].sum := by simpa using hx
  have hr := loop_rel h (jf := x) (t := 0) hx' (by simp)
  simp only [LRel, List.getD_cons_zero, LoopOut.arg, List.getD_cons_succ, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at hr
  rw [Opd.val_prev M _ hx'] at hr
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, unflat_lt hx] at hr
  simp only [Mem.rd_E, Mem.rd_K, Nat.one_mul] at hr ⊢
  rw [hr, ← Nat.add_assoc]

theorem rowFoldE_step {p : Ptr} {l a lb S er : Nat} {x : Nat}
    (h : SegsHold c M p (loop [l, a]
      [⟨.loadE, .E, [.abs ⟨.K, lb, [3, S]⟩, .abs ⟨.K, lb + 1, [3, S]⟩, .abs ⟨.K, lb + 2, [3, S]⟩]⟩,
       ⟨.muladd, .E, [.cur 0, .abs ⟨.E, er, [1, 0]⟩, .prev 1]⟩] p).2)
    (hx : x < 2 ^ (l + a)) :
    M.e (p.e + 1 + 2 * x) =
      (⟨M.k (lb + 3 * (x % 2 ^ l) + S * (x / 2 ^ l)), M.k (lb + 1 + 3 * (x % 2 ^ l) + S * (x / 2 ^ l)),
        M.k (lb + 2 + 3 * (x % 2 ^ l) + S * (x / 2 ^ l))⟩ : FE) * M.e (er + x % 2 ^ l) +
      M.e (p.e + 1 - 2 + 2 * x) := by
  have hx' : x < 2 ^ [l, a].sum := by simpa using hx
  have hl := loop_rel h (jf := x) (t := 0) hx' (by simp)
  have hr := loop_rel h (jf := x) (t := 1) hx' (by simp)
  simp only [LRel, List.getD_cons_zero, LoopOut.arg, List.getD_cons_succ, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at hl hr
  rw [Opd.val_prev M _ hx', Opd.val_cur M _ hx'] at hr
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, unflat_lt hx,
    LoopOut.cell_val] at hl hr
  simp only [Mem.rd_E, Mem.rd_K] at hl hr ⊢
  rw [loadE_eq] at hl
  have e := flat_split (l := l) (x := x)
  rw [hr, hl, show p.e - 1 + 2 * x = p.e + 1 - 2 + 2 * x by omega]
  congr 3 <;> ring_nf

/-- **Level-0 row folds**: fold cell `q` is `Σ_k word_q[k] · e[k]`. -/
theorem rowFold0_spec {p : Ptr} {l a lb S er : Nat} (h : SegsHold c M p (rowFold0 l a lb S er p).2)
    (hp : 1 ≤ p.e) {q : Nat} (hq : q < 2 ^ a) :
    ((rowFold0 l a lb S er p).1 q).val M =
      ∑ k ∈ Finset.range (2 ^ l), FE.ofK (M.k (lb + k + S * q)) * M.e (er + k) := by
  simp only [rowFold0, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil,
    Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  let f : Nat → FE := fun x =>
    FE.ofK (M.k (lb + x % 2 ^ l + S * (x / 2 ^ l))) * M.e (er + x % 2 ^ l)
  have hpre := prefix_cells M.e p.e 1 (2 ^ (l + a)) hp f fun x hx => rowFold0_step h.1 hx
  rw [diff_spec f h.2 hpre hq]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hm, hdv⟩ := split_la (q := q) (Finset.mem_range.mp hi)
  simp only [f, hm, hdv]

/-- **Later-level row folds**: fold cell `q` is `Σ_k row_q[k] · e[k]`, `row_q[k]` the `E` scalar
in lanes `lb + 3k + S·q + (0, 1, 2)`. -/
theorem rowFoldE_spec {p : Ptr} {l a lb S er : Nat} (h : SegsHold c M p (rowFoldE l a lb S er p).2)
    (hp : 1 ≤ p.e) {q : Nat} (hq : q < 2 ^ a) :
    ((rowFoldE l a lb S er p).1 q).val M =
      ∑ k ∈ Finset.range (2 ^ l), (⟨M.k (lb + 3 * k + S * q), M.k (lb + 1 + 3 * k + S * q),
        M.k (lb + 2 + 3 * k + S * q)⟩ : FE) * M.e (er + k) := by
  simp only [rowFoldE, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil,
    Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  let f : Nat → FE := fun x =>
    (⟨M.k (lb + 3 * (x % 2 ^ l) + S * (x / 2 ^ l)), M.k (lb + 1 + 3 * (x % 2 ^ l) + S * (x / 2 ^ l)),
      M.k (lb + 2 + 3 * (x % 2 ^ l) + S * (x / 2 ^ l))⟩ : FE) * M.e (er + x % 2 ^ l)
  have hpre := prefix_cells M.e (p.e + 1) 2 (2 ^ (l + a)) (by omega) f
    fun x hx => rowFoldE_step h.1 hx
  rw [show p.e + 1 - 2 = p.e - 1 by omega] at hpre
  rw [diff_spec f h.2 hpre hq]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨hm, hdv⟩ := split_la (q := q) (Finset.mem_range.mp hi)
  simp only [f, hm, hdv]

/-! ## Equivalence with `F` -/

/-- **Q_arith_eq, level-0 row fold.** If the `K` cells hold the stream's lanes and `e[k]` the
reversed `eq` table, fold cell `q` is `F`'s `foldRow0` of the row at byte `8 (lb + S q)`. -/
theorem rowFold0_eq {p : Ptr} {l a lb S er : Nat} (h : SegsHold c M p (rowFold0 l a lb S er p).2)
    (hp : 1 ≤ p.e) (sig : ByteArray) (eq : Array FE) {q : Nat} (hq : q < 2 ^ a)
    (hS : ∀ k < 2 ^ l, M.k (lb + k + S * q) = lane sig (lb + k + S * q))
    (he : ∀ k < 2 ^ l, M.e (er + k) = eq.getD (2 ^ l - 1 - k) 0) :
    ((rowFold0 l a lb S er p).1 q).val M = foldRow0 sig eq (8 * (lb + S * q)) (2 ^ l) := by
  rw [rowFold0_spec h hp hq, foldRow0_eq]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [hS k hk', he k hk', lane]
  have : 2 ^ l - 1 - (2 ^ l - 1 - k) = k := by omega
  -- `rw`, not `congr 1`: its `rfl` attempt on `kAt` unfolds the lane reads (15 s)
  rw [this, show 8 * (lb + k + S * q) = 8 * (lb + S * q) + 8 * k by ring]

/-- **Q_arith_eq, later-level row fold**: `F`'s `foldRowE` of the row at byte `8 (lb + S q)`. -/
theorem rowFoldE_eq {p : Ptr} {l a lb S er : Nat} (h : SegsHold c M p (rowFoldE l a lb S er p).2)
    (hp : 1 ≤ p.e) (sig : ByteArray) (eq : Array FE) {q : Nat} (hq : q < 2 ^ a)
    (hS : ∀ k < 2 ^ l, ∀ c < 3, M.k (lb + c + 3 * k + S * q) = lane sig (lb + c + 3 * k + S * q))
    (he : ∀ k < 2 ^ l, M.e (er + k) = eq.getD k 0) :
    ((rowFoldE l a lb S er p).1 q).val M = foldRowE sig eq (8 * (lb + S * q)) (2 ^ l) := by
  rw [rowFoldE_spec h hp hq, foldRowE_eq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have h0 := hS k hk' 0 (by omega)
  have h1' := hS k hk' 1 (by omega)
  have h2 := hS k hk' 2 (by omega)
  simp only [Nat.add_zero] at h0
  have key : (⟨lane sig (lb + 3 * k + S * q), lane sig (lb + 1 + 3 * k + S * q),
      lane sig (lb + 2 + 3 * k + S * q)⟩ : FE) = feAt sig (8 * (lb + S * q) + 24 * k) := by
    have e0 : 8 * (lb + 3 * k + S * q) = 8 * (lb + S * q) + 24 * k := by ring
    have e1 : 8 * (lb + 1 + 3 * k + S * q) = 8 * (lb + S * q) + 24 * k + 8 := by ring
    have e2 : 8 * (lb + 2 + 3 * k + S * q) = 8 * (lb + S * q) + 24 * k + 16 := by ring
    simp only [lane, feAt]
    rw [e0, e1, e2]
  rw [h0, h1', h2, he k hk', key]

end Lvm.Loop.Build
