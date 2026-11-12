import LvmQWhirFold

/-!
# QA2: `eq` tables, powers and dot products (WHIR fold kernel, batching `λ`, stacked batching)

* **`eqTab`**: the `eq` table of a point by levels (WP-10's `eqLevel` written with the builder):
  each level prepends one coordinate `ρ`, a loop of dims `[k]` with two rows
  `T'[2x] = T[x]·(1+ρ)`, `T'[2x+1] = T[x]·ρ`. Processing the coordinates `n−1, …, 0` from the
  table `[1]` gives `F`'s `eqKernelA` (`eqKernelA_getD`: entry `x` is `eqW pt x`); with `rev` the
  two factors swap and the table is reversed (`eqW_compl`), which the level-0 row fold reads.
  Cost: `2^(n+1) − 2` `E·E` rows + `n` `lin` rows.
* **`pows`**: `1, λ, …, λ^(2^a)` (`F`'s `powers`, for the query weights and the stacked scales):
  a copy of `1`, then a loop with the running product.
* **`dotG`**: `Σ_{i<n} x_i · y_i` (`n ≤ 2^a`: the loop runs `2^a` terms, the difference row stops at
  `n`, so non-power-of-two counts are exact) at affine cells (`F`'s `dot`: the enforced sum
  `Σ_q λ^q fold_q`, the stacked target and basis): a running `muladd` and one difference row.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-! ## `eqKernelA` is `eqW` -/

theorem eqW_append : ∀ (a b : List FE) (x : Nat),
    eqW (a ++ b) x = eqW a (x % 2 ^ a.length) * eqW b (x / 2 ^ a.length)
  | [], b, x => by simp [eqW]
  | r :: a, b, x => by
    simp only [List.cons_append, eqW, List.length_cons]
    rw [eqW_append a b (x / 2)]
    have h1 : x % 2 ^ (a.length + 1) % 2 = x % 2 := by
      rw [pow_succ', Nat.mod_mul_right_mod]
    have h2 : x % 2 ^ (a.length + 1) / 2 = x / 2 % 2 ^ a.length := by
      rw [pow_succ', Nat.mod_mul_right_div_self]
    have h3 : x / 2 / 2 ^ a.length = x / 2 ^ (a.length + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    simp only [h1, h2, h3]; ring

theorem eqKernelA_toList (pt : List FE) : (eqKernelA pt).toList = eqKernel pt := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton l r ih =>
    simp only [eqKernelA, eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [Array.toList_append, Array.toList_map, Array.toList_map, ih]

theorem eqKernel_length (pt : List FE) : (eqKernel pt).length = 2 ^ pt.length := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton l r ih =>
    simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [List.length_append, List.length_map, List.length_map, ih]; simp [pow_succ]; ring

theorem eqKernel_get? (pt : List FE) : ∀ x < 2 ^ pt.length, (eqKernel pt)[x]? = some (eqW pt x) := by
  induction pt using List.reverseRecOn with
  | nil => intro x hx; simp at hx; subst hx; simp [eqKernel, eqW]
  | append_singleton l r ih =>
    intro x hx
    have hs := eqKernel_length l
    have hT : eqKernel (l ++ [r]) = (eqKernel l).map (· * (1 + r)) ++ (eqKernel l).map (· * r) := by
      simp [eqKernel, List.foldl_append]
    rw [hT, eqW_append]
    simp only [List.length_append, List.length_singleton] at hx
    by_cases hlt : x < 2 ^ l.length
    · rw [List.getElem?_append_left (by simp [hs, hlt]), List.getElem?_map, ih x hlt]
      simp [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, eqW]
      left; rw [sub_eq_add_neg, CharTwo.neg_eq]
    · have hge : 2 ^ l.length ≤ x := by omega
      have hlt2 : x - 2 ^ l.length < 2 ^ l.length := by rw [pow_succ] at hx; omega
      rw [List.getElem?_append_right (by simp [hs, hge]), List.getElem?_map, List.length_map, hs,
        ih _ hlt2]
      have hmod : x % 2 ^ l.length = x - 2 ^ l.length := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2]
      have hdiv : x / 2 ^ l.length = 1 := by
        apply Nat.div_eq_of_lt_le <;> [rw [pow_succ] at hx; skip] <;> omega
      simp [hmod, hdiv, eqW, mul_comm]

/-- **`F`'s `eq` table**: entry `x` of `eqKernelA pt` is `eqW pt x` (first coordinate lowest). -/
theorem eqKernelA_getD (pt : List FE) (x : Nat) (hx : x < 2 ^ pt.length) :
    (eqKernelA pt).getD x 0 = eqW pt x := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, eqKernelA_toList, eqKernel_get? pt x hx]
  rfl

/-- The reversed table is the table of the complemented point (`1 − r = 1 + r`). -/
theorem eqW_compl : ∀ (pt : List FE) (x : Nat), x < 2 ^ pt.length →
    eqW (pt.map (1 + ·)) x = eqW pt (2 ^ pt.length - 1 - x)
  | [], x, hx => by simp [eqW]
  | r :: pt, x, hx => by
    simp only [List.map_cons, eqW, List.length_cons] at hx ⊢
    have hx2 : x / 2 < 2 ^ pt.length := by rw [pow_succ] at hx; omega
    rw [eqW_compl pt (x / 2) hx2]
    have hy : (2 ^ (pt.length + 1) - 1 - x) / 2 = 2 ^ pt.length - 1 - x / 2 := by
      rw [pow_succ] at hx ⊢; omega
    have hpar : (2 ^ (pt.length + 1) - 1 - x) % 2 = 1 ↔ ¬ (x % 2 = 1) := by
      rw [pow_succ] at hx ⊢; omega
    rw [hy]
    by_cases h : x % 2 = 1
    · rw [if_pos h, if_neg (by rw [hpar]; exact not_not.mpr h)]
      congr 1
    · rw [if_neg h, if_pos (hpar.mpr h)]
      congr 1; rw [sub_eq_add_neg, CharTwo.neg_eq, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-! ## The `eq` table gadget -/

/-- The coordinate a level prepends: `α_i`, or `1 + α_i` for the reversed table. -/
def eqCoord (rev : Bool) (α : FE) : FE := if rev then 1 + α else α

/-- The levels of an `eq` table: prepend the coordinates `is` (in order) to the table at `tb`
(`2^k` cells); the base of the final table. `al i` holds `α_i`; `z` an `E` zero cell. -/
def eqTabGo (al : Nat → Cell) (z : Cell) (rev : Bool) : List Nat → Nat → Nat → BM Nat
  | [], tb, _ => pure tb
  | i :: is, tb, k => do
    let o ← lin .E 0 1 (al i) (al i)
    let p ← getPtr
    let _ ← loop [k] [⟨.muladd, .E, [.abs ⟨.E, tb, [1]⟩, (if rev then al i else o).opd, z.opd]⟩,
      ⟨.muladd, .E, [.abs ⟨.E, tb, [1]⟩, (if rev then o else al i).opd, z.opd]⟩]
    eqTabGo al z rev is p.e (k + 1)

variable {c : Ctx} {M : Mem}

/-- With at least one coordinate to prepend, `eqTabGo` leaves the `E` pointer immediately
after its final table of `2^(k + is.length)` cells. -/
theorem eqTabGo_end (al : Nat → Cell) (z : Cell) (rev : Bool) :
    ∀ (is : List Nat) (tb k : Nat) (p : Ptr), is ≠ [] →
      (p.adv (eqTabGo al z rev is tb k p).2).e =
        (eqTabGo al z rev is tb k p).1 + 2 ^ (k + is.length)
  | [], _, _, _, hn => (hn rfl).elim
  | i :: is, tb, k, p, _ => by
    simp only [eqTabGo, bind_apply, getPtr, List.nil_append, Ptr.adv_nil,
      Ptr.adv_append]
    cases is with
    | nil =>
      simp only [eqTabGo, pure_apply, Ptr.adv_nil, List.length_cons, List.length_nil,
        Nat.zero_add]
      rw [loop_adv]
      simp [ltw, LRow.w, Row.w, Row.writes, pow_succ]
      omega
    | cons j js =>
      rw [eqTabGo_end al z rev (j :: js) _ (k + 1) _ (by simp)]
      simp only [List.length_cons]
      congr 2
      omega

theorem eqTabGo_spec (al : Nat → Cell) (z : Cell) (rev : Bool) (hz : z.val M = 0)
    (hal : ∀ i, (al i).ty = .E) :
    ∀ (is : List Nat) (tb k : Nat) (pt : List FE) (p : Ptr), pt.length = k →
      SegsHold c M p (eqTabGo al z rev is tb k p).2 →
      (∀ x < 2 ^ k, M.e (tb + x) = eqW pt x) →
      ∀ x < 2 ^ (k + is.length), M.e ((eqTabGo al z rev is tb k p).1 + x) =
        eqW ((is.map fun i => eqCoord rev ((al i).val M)).reverse ++ pt) x
  | [], tb, k, pt, p, _, _, hT => by simpa [eqTabGo, pure_apply] using hT
  | i :: is, tb, k, pt, p, hk, h, hT => by
    simp only [eqTabGo, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil,
      Ptr.adv_nil] at h ⊢
    rw [segsHold_append] at h
    have ho := lin_spec h.1
    set p₁ := p.adv (lin Ty.E 0 1 (al i) (al i) p).2 with hp₁
    rw [segsHold_append] at h
    have hT' : ∀ x < 2 ^ (k + 1), M.e (p₁.e + x) = eqW (eqCoord rev ((al i).val M) :: pt) x := by
      intro x hx
      have hx2 : x / 2 < 2 ^ [k].sum := by simp; rw [pow_succ] at hx; omega
      have hu : unflat [k] (x / 2) = [x / 2] := by simp [unflat, Nat.mod_eq_of_lt (by simpa using hx2)]
      have r0 := loop_rel h.2.1 (jf := x / 2) (t := 0) hx2 (by simp)
      have r1 := loop_rel h.2.1 (jf := x / 2) (t := 1) hx2 (by simp)
      have hTx := hT (x / 2) (by simpa using hx2)
      have hov : (lin Ty.E 0 1 (al i) (al i) p).1.val M = 1 + (al i).val M := by
        rw [ho, ofK_zero, ofK_one, zero_mul, add_zero, add_comm]
      cases rev <;>
      · simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
          LoopOut.cell_val, Opd.val_abs, Cell.opd, if_true, if_false, Bool.false_eq_true] at r0 r1
        simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E,
          Cell.addr] at r0 r1
        have hzv : M.rd z.ty z.n = 0 := hz
        have hav : M.rd (al i).ty (al i).n = (al i).val M := rfl
        have hov' : M.rd (lin Ty.E 0 1 (al i) (al i) p).1.ty (lin Ty.E 0 1 (al i) (al i) p).1.n =
            1 + (al i).val M := hov
        rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
        · have ex : x = 2 * (x / 2) := by omega
          rw [ex, r0, hTx, hzv, add_zero, eqW_even]
          simp only [eqCoord, hav, hov', Bool.false_eq_true, if_true, if_false, sub_eq_add_neg,
            CharTwo.neg_eq]
          first | ring1 |
            linear_combination (-(eqW pt (x / 2))) * (CharTwo.two_eq_zero (R := FE))
        · have ex : x = 2 * (x / 2) + 1 := by omega
          rw [ex, show p₁.e + (2 * (x / 2) + 1) = p₁.e + 1 + 2 * (x / 2) by ring, r1, hTx, hzv,
            add_zero, eqW_odd]
          simp only [eqCoord, hav, hov', Bool.false_eq_true, if_true, if_false, sub_eq_add_neg,
            CharTwo.neg_eq]
          ring
    have ih := eqTabGo_spec al z rev hz hal is p₁.e (k + 1) (eqCoord rev ((al i).val M) :: pt)
      (p₁.adv (loop [k] _ p₁).2) (by simp [hk]) h.2.2 hT'
    intro x hx
    rw [List.length_cons, show k + (is.length + 1) = k + 1 + is.length by ring] at hx
    rw [ih x hx]
    simp

/-- **The `eq` table of `n` coordinates** `α_i = (al i).val` (`rev`: of `1 + α_i`), from an `E`
cell `one` holding `1`; the base cell of the `2^n` entries. -/
def eqTab (al : Nat → Cell) (z one : Cell) (rev : Bool) (n : Nat) : BM Nat :=
  eqTabGo al z rev (List.range n).reverse one.n 0

/-- For a positive number of coordinates, `eqTab` leaves the `E` pointer immediately after
the returned table of `2^n` cells. -/
theorem eqTab_end (al : Nat → Cell) (z one : Cell) (rev : Bool) {n : Nat}
    (hn : 0 < n) (p : Ptr) :
    (p.adv (eqTab al z one rev n p).2).e = (eqTab al z one rev n p).1 + 2 ^ n := by
  simpa [eqTab] using eqTabGo_end al z rev (List.range n).reverse one.n 0 p (by
    intro he
    have := congrArg List.length he
    simp at this
    omega)

theorem eqTab_spec (al : Nat → Cell) (z one : Cell) (rev : Bool) (n : Nat) {p : Ptr}
    (h : SegsHold c M p (eqTab al z one rev n p).2) (hz : z.val M = 0) (hal : ∀ i, (al i).ty = .E)
    (hone : M.e one.n = 1) :
    ∀ x < 2 ^ n, M.e ((eqTab al z one rev n p).1 + x) =
      eqW ((List.range n).map fun i => eqCoord rev ((al i).val M)) x := by
  intro x hx
  have := eqTabGo_spec al z rev hz hal (List.range n).reverse one.n 0 [] p rfl h
    (fun y hy => by simp at hy; subst hy; simpa [eqW] using hone) x (by simpa using hx)
  rw [eqTab, this]
  simp [List.map_reverse]

/-- **Q_arith_eq, `eq` tables**: the table is `F`'s `eqKernelA αs`, entry by entry; reversed with
`rev` (the level-0 row fold's `e[k] = eq[2^l − 1 − k]`). -/
theorem eqTab_eq (al : Nat → Cell) (z one : Cell) (rev : Bool) {p : Ptr} (αs : List FE)
    (h : SegsHold c M p (eqTab al z one rev αs.length p).2) (hz : z.val M = 0)
    (hal : ∀ i, (al i).ty = .E) (hone : M.e one.n = 1)
    (hv : ∀ i < αs.length, (al i).val M = αs.getD i 0) :
    ∀ x < 2 ^ αs.length, M.e ((eqTab al z one rev αs.length p).1 + x) =
      (eqKernelA αs).getD (if rev then 2 ^ αs.length - 1 - x else x) 0 := by
  intro x hx
  rw [eqTab_spec al z one rev αs.length h hz hal hone x hx]
  have hm : (List.range αs.length).map (fun i => eqCoord rev ((al i).val M)) =
      αs.map (eqCoord rev) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hv i (by simpa using h1), List.getD_eq_getElem _ _ (by simpa using h1)]
  rw [hm]
  cases rev
  · have e : eqCoord false = fun a => a := funext fun _ => rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [e, List.map_id', eqKernelA_getD αs x hx]
  · have e : eqCoord true = fun a => 1 + a := funext fun _ => rfl
    simp only [↓reduceIte]
    rw [e, eqW_compl αs x hx, eqKernelA_getD αs _ (by omega)]

/-! ## Powers and dot products -/

/-- **`1, λ, …, λ^(2^a)`** at consecutive `E` cells from the returned one (`one` holds `1`). -/
def pows (a : Nat) (lam one z : Cell) : BM Nat := do
  let o ← copy one
  let _ ← loop [a] [⟨.muladd, .E, [.prev 0, lam.opd, z.opd]⟩]
  pure o.n

theorem pows_spec {a : Nat} {lam one z : Cell} {p : Ptr} (h : SegsHold c M p (pows a lam one z p).2)
    (hz : z.val M = 0) (hone : one.val M = 1) (hE : one.ty = .E) :
    ∀ i ≤ 2 ^ a, M.e ((pows a lam one z p).1 + i) = lam.val M ^ i := by
  simp only [pows, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append] at h
  have hc := lin_spec h.1
  have hp1 : (p.adv (copy one p).2).e = p.e + 1 := by
    simp [copy, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes, hE]
  have hcn : (copy one p).1.n = p.e := by simp [copy, lin, rowRes, hE, Ptr.at]
  have h0 : M.e p.e = 1 := by
    have : (copy one p).1.val M = M.e p.e := by simp [copy, lin, rowRes, hE, Ptr.at, Cell.val, Mem.rd_E]
    rw [← this]; simp only [copy] at hc ⊢; rw [hc, hone, ofK_zero]; ring
  rw [hcn]
  intro i hi
  induction i with
  | zero => simpa using h0
  | succ i ih =>
    have hjf : i < 2 ^ [a].sum := by simpa using hi
    have r := loop_rel h.2 (jf := i) (t := 0) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Cell.opd, Opd.val_abs] at r
    rw [Opd.val_prev M _ hjf] at r
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, Mem.rd_E, hp1,
      Cell.addr] at r
    have hzv : M.rd z.ty z.n = 0 := hz
    rw [show p.e + (i + 1) = p.e + 1 + i by ring, r, hzv, add_zero, ih (by omega), pow_succ]
    rfl

/-- `F`'s `powers`: entry `i` is `base^i`. -/
theorem powers_getD (b : FE) : ∀ (n i : Nat), i < n → (powers b n).getD i 0 = b ^ i := by
  have key : ∀ (acc : FE) (n i : Nat), i < n → (powersFrom acc b n).getD i 0 = acc * b ^ i := by
    intro acc n
    induction n generalizing acc with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      cases i with
      | zero => simp [powersFrom]
      | succ i => simp only [powersFrom, List.getD_cons_succ]; rw [ih _ i (by omega)]; ring
  intro n i hi
  rw [powers, key 1 n i hi, one_mul]

/-- **`Σ_i x_i · y_i`** over `2^a` terms, `x_i`, `y_i` at the `E` cells `xb + xs·i`, `yb + ys·i`. -/
def dotG (a n xb xs yb ys : Nat) : BM Cell := do
  let p ← getPtr
  let s ← loop [a] [⟨.muladd, .E, [.abs ⟨.E, xb, [xs]⟩, .abs ⟨.E, yb, [ys]⟩, .prev 0]⟩]
  add (s.cell 0 (n - 1)) (ec (p.e - 1))

theorem dotG_spec {p : Ptr} {a n xb xs yb ys : Nat} (h : SegsHold c M p (dotG a n xb xs yb ys p).2)
    (hp : 1 ≤ p.e) (hn : 1 ≤ n) (hna : n ≤ 2 ^ a) :
    (dotG a n xb xs yb ys p).1.val M =
      ∑ i ∈ Finset.range n, M.e (xb + xs * i) * M.e (yb + ys * i) := by
  simp only [dotG, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  have hs := lin_spec h.2
  simp only [add] at hs ⊢
  rw [hs]
  have hstep : ∀ x < 2 ^ a, M.e (p.e + 1 * x) =
      M.e (xb + xs * x) * M.e (yb + ys * x) + M.e (p.e - 1 + 1 * x) := by
    intro x hx
    have hjf : x < 2 ^ [a].sum := by simpa using hx
    have hu : unflat [a] x = [x] := by simp [unflat, Nat.mod_eq_of_lt hx]
    have r := loop_rel h.1 (jf := x) (t := 0) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Opd.val_abs] at r
    rw [Opd.val_prev M _ hjf] at r
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E] at r
    simp only [Nat.one_mul]
    rw [r]
  have hpre := prefix_cells M.e p.e 1 (2 ^ a) hp _ hstep
  have hl := hpre n hna
  simp only [Nat.one_mul] at hl
  have hc : (LoopOut.cell ⟨p, [a], [⟨.muladd, .E, [.abs ⟨.E, xb, [xs]⟩, .abs ⟨.E, yb, [ys]⟩,
      .prev 0]⟩]⟩ 0 (n - 1)).val M = M.e (p.e - 1 + n) := by
    simp [LoopOut.cell_val, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Mem.rd_E]
    congr 1; omega
  simp only [loop_apply] at hc ⊢
  rw [hc, hl, ofK_one, ofK_zero, one_mul, add_zero, Cell.val_E, add_right_comm,
    CharTwo.add_self_eq_zero, zero_add]

/-- `F`'s `dot` on lists of one length is the sum of the products. -/
theorem foldl_add_id : ∀ (l : List FE) (a : FE), l.foldl (fun x1 x2 => x1 + x2) a = a + l.sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_id l]; simp [add_assoc]

theorem dot_eq_sum : ∀ (l r : List FE), l.length = r.length →
    Lvm.dot l r = ∑ i ∈ Finset.range l.length, l.getD i 0 * r.getD i 0
  | [], [], _ => by simp [Lvm.dot]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l, y :: r, h => by
    have ih := dot_eq_sum l r (by simpa using h)
    simp only [Lvm.dot, foldl_add_id, zero_add] at ih ⊢
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

end Lvm.Loop.Build
