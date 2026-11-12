import LvmQWhirWeight

/-!
# QA2: column-claim weights at the WHIR terminal point (`eqEval`)

The stacked opening's basis (`LvmDecideWhir.verifyStackedOpening`, `evaluateBasis`) is
`Σ_c s^c · W_c(x)`, and a column claim's weight is `eqAbove · eqEval z (x.take n)`
(`LvmDecideBase.BlockClaim.point`, `onStack`), both products of `eqEval`'s factors
`1 + l_i + r_i`. **`eqEvalG cs lb rb acc`**: `acc · Π_{i < Σ 2^c} (1 + l_i + r_i)` with `l_i`, `r_i`
the `E` cells `lb + i`, `rb + i`; one loop with a prologue per chunk `2^c` of coordinates (a `lin`
and a `muladd` per coordinate, 28 words). `eqEvalG_eq`: with `acc = 1` it is `F`'s `eqEval`.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-- The template of one chunk from coordinate `i₀`. -/
def eeTpl (lb rb i₀ : Nat) (z : Cell) : List LRow :=
  [⟨.lin 1 1, .E, [.abs ⟨.E, lb + i₀, [1]⟩, .abs ⟨.E, rb + i₀, [1]⟩]⟩,
   ⟨.muladd, .E, [.prev 1, .cur 0, z.opd]⟩]

/-- **`acc · Π_i (1 + l_i + r_i)`** over the chunks `cs` of coordinates from `i₀`. -/
def eqEvalG (lb rb : Nat) (z : Cell) : List Nat → Nat → Cell → BM Cell
  | [], _, acc => pure acc
  | cc :: cs, i₀, acc => do
    let o ← loopP [cc] (eeTpl lb rb i₀ z) fun _ => acc
    eqEvalG lb rb z cs (i₀ + 2 ^ cc) (o.cell 1 (2 ^ cc - 1))

variable {c : Ctx} {M : Mem}

theorem eeChunk_spec {cc lb rb i₀ : Nat} {z acc : Cell} {p : Ptr}
    (h : SegsHold c M p (loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).2) (hz : z.val M = 0) :
    ∀ x < 2 ^ cc, ((loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).1.cell 1 x).val M =
      acc.val M * ∏ i ∈ Finset.range (x + 1), (1 + M.e (lb + i₀ + i) + M.e (rb + i₀ + i)) := by
  have hzv : M.rd z.ty z.n = 0 := hz
  have rows : ∀ x < 2 ^ cc,
      ((loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).1.cell 1 x).val M =
        (Opd.prev 1).val M (loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).1 x *
          (1 + M.e (lb + i₀ + x) + M.e (rb + i₀ + x)) := by
    intro x hx
    have hjf : x < 2 ^ [cc].sum := by simpa using hx
    have hu : unflat [cc] x = [x] := by simp [unflat, Nat.mod_eq_of_lt hx]
    have r0 := loopP_rel h (jf := x) (t := 0) hjf (by simp [eeTpl])
    have r1 := loopP_rel h (jf := x) (t := 1) hjf (by simp [eeTpl])
    generalize ho : (loopP [cc] (eeTpl lb rb i₀ z) (fun _ => acc) p).1 = o at r0 r1 ⊢
    have htpl : o.tpl = eeTpl lb rb i₀ z := by rw [← ho]; rfl
    have hdims : o.dims = [cc] := by rw [← ho]; rfl
    unfold LRel at r0 r1
    simp only [LoopOut.arg, htpl, eeTpl, List.getD_cons_zero, List.getD_cons_succ] at r0 r1
    rw [Opd.val_cur M _ (by rw [hdims]; simpa using hjf)] at r1
    rw [r1, r0]
    simp only [Opd.val_abs, Cell.opd, Cell.addr, Addr.at, hdims, hu, dot, Mem.rd_E, ofK_one, one_mul,
      Nat.add_zero]
    rw [hzv, add_zero]
    ring
  intro x hx
  induction x with
  | zero =>
    rw [rows 0 hx, loopP_prev_zero h (t := 1) (by simp [eeTpl]) (by simp [eeTpl])]
    simp
  | succ x ih =>
    rw [rows (x + 1) hx, loopP_prev_succ M _ _ _ p (by simpa using hx), ih (by omega),
      Finset.prod_range_succ _ (x + 1)]
    ring

theorem eqEvalG_spec (lb rb : Nat) (z : Cell) (hz : z.val M = 0) :
    ∀ (cs : List Nat) (i₀ : Nat) (acc : Cell) (p : Ptr),
      SegsHold c M p (eqEvalG lb rb z cs i₀ acc p).2 →
      (eqEvalG lb rb z cs i₀ acc p).1.val M =
        acc.val M * ∏ i ∈ Finset.range (csum cs), (1 + M.e (lb + i₀ + i) + M.e (rb + i₀ + i))
  | [], _, acc, _, _ => by simp [eqEvalG, pure_apply, csum]
  | cc :: cs, i₀, acc, p, h => by
    simp only [eqEvalG, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [eqEvalG_spec lb rb z hz cs _ _ _ h.2, eeChunk_spec h.1 hz _ (by have := Nat.two_pow_pos cc; omega),
      show 2 ^ cc - 1 + 1 = 2 ^ cc by have := Nat.two_pow_pos cc; omega, csum_cons,
      Finset.prod_range_add, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show lb + (i₀ + 2 ^ cc) + i = lb + i₀ + (2 ^ cc + i) by ring,
      show rb + (i₀ + 2 ^ cc) + i = rb + i₀ + (2 ^ cc + i) by ring]

/-- `F`'s `eqEval` as a product. -/
theorem eqEval_prod : ∀ (l r : List FE), l.length = r.length →
    eqEval l r = ∏ i ∈ Finset.range l.length, (1 + l.getD i 0 + r.getD i 0)
  | [], [], _ => by simp [eqEval]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: l, y :: r, h => by
    have ih := eqEval_prod l r (by simpa using h)
    have key : ∀ (L : List FE) (a : FE), L.foldl (· * ·) a = a * L.foldl (· * ·) 1 := by
      intro L; induction L with
      | nil => simp
      | cons b L ihL => intro a; simp only [List.foldl_cons]; rw [ihL (a * b), ihL (1 * b)]; ring
    simp only [eqEval, List.zipWith_cons_cons, List.foldl_cons, one_mul] at ih ⊢
    rw [key, ih, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- **Q_arith_eq, `eqEval`**: from a cell holding `1`, the gadget is `F`'s `eqEval l r`. -/
theorem eqEvalG_eq {lb rb : Nat} {z one : Cell} {cs : List Nat} {p : Ptr} (l r : List FE)
    (h : SegsHold c M p (eqEvalG lb rb z cs 0 one p).2) (hz : z.val M = 0) (hone : one.val M = 1)
    (hl : l.length = csum cs) (hr : r.length = csum cs)
    (hlc : ∀ i < csum cs, M.e (lb + i) = l.getD i 0) (hrc : ∀ i < csum cs, M.e (rb + i) = r.getD i 0) :
    (eqEvalG lb rb z cs 0 one p).1.val M = eqEval l r := by
  rw [eqEvalG_spec lb rb z hz cs 0 one p h, hone, one_mul, eqEval_prod l r (hl.trans hr.symm), hl]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Nat.add_zero, Nat.add_zero, hlc i (Finset.mem_range.mp hi), hrc i (Finset.mem_range.mp hi)]

end Lvm.Loop.Build
