import LvmQWhirBatch

/-!
# QA2: the WHIR terminal: `multilinearEval` of the residual, and the terminal check

`F`'s final level (`LvmDecideWhir.whirLevels`, `[]` case): `terminal = weight · multilinearEval
residual tailFolds`, `require (terminal == target)`.

* **`mleFold n tb ts rp`**: the residual (`2^n` `E` cells at `tb + ts·v`) folded by the points
  `rp 0 … rp (n−1)` (`F`'s `foldPairs`, one level per coordinate): per pair a `lin` (`a + b`) and a
  `muladd` (`r·(a + b) + a = a(1+r) + br`), 28 words per pair; the levels are loops of dims
  `[n − j − 1]`. `mleFold_spec`: the result is `multilinearEval residual point`.
* **`terminalCheck weight mle target gate`**: `t = weight · mle + target`, `assert0 t gate`:
  with the gate on, the assertion holds iff `weight · mle = target` (`F`'s `terminal == target`).

Cost (P20): C_rec 2^13 residual: 8,191 pairs (229 k words) + its loads; C_main 2^8: 255 pairs.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-! ## The F side -/

/-- One fold of `multilinearEval` as an index function. -/
theorem foldPairs_getD (r : FE) : ∀ (L : List FE) (x : Nat), 2 * x + 1 < L.length →
    (foldPairs r L).getD x 0 = L.getD (2 * x) 0 * (1 + r) + L.getD (2 * x + 1) 0 * r
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: rest, 0, _ => by simp [foldPairs]
  | a :: b :: rest, x + 1, h => by
    simp only [foldPairs, List.getD_cons_succ]
    rw [foldPairs_getD r rest x (by simp at h; omega)]
    congr 2 <;> congr 1 <;> ring

theorem foldPairs_length (r : FE) : ∀ (L : List FE), (foldPairs r L).length = L.length / 2
  | [] => rfl
  | [_] => by simp [foldPairs]
  | a :: b :: rest => by
    simp only [foldPairs, List.length_cons, foldPairs_length r rest]; omega

/-- The residual after `j` folds. -/
def resAfter (res pt : List FE) (j : Nat) : List FE := (pt.take j).foldl (fun cur r => foldPairs r cur) res

theorem resAfter_succ (res pt : List FE) (j : Nat) (hj : j < pt.length) :
    resAfter res pt (j + 1) = foldPairs (pt.getD j 0) (resAfter res pt j) := by
  simp only [resAfter]
  rw [List.take_succ, List.foldl_append, List.getElem?_eq_getElem hj]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem resAfter_length (res pt : List FE) (n : Nat) (hres : res.length = 2 ^ n) :
    ∀ j ≤ n, j ≤ pt.length → (resAfter res pt j).length = 2 ^ (n - j) := by
  intro j hj hjp
  induction j with
  | zero => simpa [resAfter] using hres
  | succ j ih =>
    rw [resAfter_succ _ _ _ (by omega), foldPairs_length, ih (by omega) (by omega)]
    rw [show n - j = (n - (j + 1)) + 1 by omega, pow_succ]; simp

theorem multilinearEval_eq (res pt : List FE) (n : Nat) (hres : res.length = 2 ^ n)
    (hpt : pt.length = n) : multilinearEval res pt = (resAfter res pt n).getD 0 0 := by
  simp only [multilinearEval, resAfter]
  rw [← hpt, List.take_length]
  cases h : List.foldl (fun cur r => foldPairs r cur) res pt with
  | nil => rfl
  | cons a l => rfl

/-! ## The circuit -/

/-- The fold levels `j, j+1, …, n−1` from the table at `tb` (stride `ts`, `2^(n−j)` entries). -/
def mleLevels (rp : Nat → Cell) (n : Nat) : (j tb ts : Nat) → (fuel : Nat) → BM Cell
  | _, tb, _, 0 => pure (ec tb)
  | j, tb, ts, fuel + 1 => do
    let p ← getPtr
    let _ ← loop [n - j - 1] [⟨.lin 1 0, .E, [.abs ⟨.E, tb, [2 * ts]⟩, .abs ⟨.E, tb + ts, [2 * ts]⟩]⟩,
      ⟨.muladd, .E, [(rp j).opd, .cur 0, .abs ⟨.E, tb, [2 * ts]⟩]⟩]
    mleLevels rp n (j + 1) (p.e + 1) 2 fuel

/-- **The residual's multilinear evaluation**: load the `2^n` scalars (lanes `lb + 3v + (0,1,2)`),
then fold them by `rp 0, …, rp (n−1)`; the result cell. -/
def mleFold (n lb : Nat) (rp : Nat → Cell) : BM Cell := do
  let p ← getPtr
  let _ ← loop [n] [⟨.loadE, .E, [.abs ⟨.K, lb, [3]⟩, .abs ⟨.K, lb + 1, [3]⟩, .abs ⟨.K, lb + 2, [3]⟩]⟩]
  mleLevels rp n 0 p.e 1 n

variable {c : Ctx} {M : Mem}

theorem mleLevels_spec (rp : Nat → Cell) (n : Nat) (res pt : List FE) (hres : res.length = 2 ^ n)
    (hpt : pt.length = n) (hrp : ∀ j < n, (rp j).val M = pt.getD j 0) :
    ∀ (fuel j tb ts : Nat) (p : Ptr), j + fuel = n →
      SegsHold c M p (mleLevels rp n j tb ts fuel p).2 →
      (∀ x < 2 ^ (n - j), M.e (tb + ts * x) = (resAfter res pt j).getD x 0) →
      (mleLevels rp n j tb ts fuel p).1.val M = (resAfter res pt n).getD 0 0
  | 0, j, tb, ts, p, hj, _, hT => by
    simp only [mleLevels, pure_apply, Cell.val_E]
    have := hT 0 (Nat.two_pow_pos _)
    rw [Nat.add_zero] at hj; subst hj
    simpa using this
  | fuel + 1, j, tb, ts, p, hj, h, hT => by
    simp only [mleLevels, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
    rw [segsHold_append] at h
    apply mleLevels_spec rp n res pt hres hpt hrp fuel (j + 1) (p.e + 1) 2 _ (by omega) h.2
    intro x hx
    have hjf : x < 2 ^ [n - j - 1].sum := by
      simp; rwa [show n - (j + 1) = n - j - 1 by omega] at hx
    have hu : unflat [n - j - 1] x = [x] := by
      simp [unflat, Nat.mod_eq_of_lt (by simpa using hjf)]
    have r0 := loop_rel h.1 (jf := x) (t := 0) hjf (by simp)
    have r1 := loop_rel h.1 (jf := x) (t := 1) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Opd.val_abs, Cell.opd] at r0 r1
    rw [Opd.val_cur M _ hjf] at r1
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, Cell.addr,
      LoopOut.cell_val, ofK_one, ofK_zero] at r0 r1
    have hlen := resAfter_length res pt n hres j (by omega) (by omega)
    have hlt : 2 * x + 1 < (resAfter res pt j).length := by
      rw [hlen, show n - j = (n - (j + 1)) + 1 by omega, pow_succ]; omega
    rw [resAfter_succ res pt j (by omega), foldPairs_getD _ _ x hlt]
    have ha := hT (2 * x) (by rw [← hlen]; omega)
    have hb := hT (2 * x + 1) (by rw [← hlen]; omega)
    rw [r1, r0, ← hrp j (by omega)]
    rw [show tb + 2 * ts * x = tb + ts * (2 * x) by ring, show tb + ts + 2 * ts * x = tb + ts * (2 * x + 1) by
      ring, ha, hb]
    have hrv : M.rd (rp j).ty (rp j).n = (rp j).val M := rfl
    rw [hrv]
    ring

/-- **Q_arith_eq, residual evaluation**: the gadget's cell is `F`'s `multilinearEval res pt`, when
the stream lanes hold the residual's `2^n` scalars and `rp j` holds `pt[j]`. -/
theorem mleFold_eq {p : Ptr} {n lb : Nat} {rp : Nat → Cell} (h : SegsHold c M p (mleFold n lb rp p).2)
    (sig : ByteArray) (res pt : List FE) (hres : res.length = 2 ^ n) (hpt : pt.length = n)
    (hrp : ∀ j < n, (rp j).val M = pt.getD j 0)
    (hS : ∀ v < 2 ^ n, ∀ k < 3, M.k (lb + k + 3 * v) = lane sig (lb + k + 3 * v))
    (hv : ∀ v < 2 ^ n, feAt sig (8 * (lb + 3 * v)) = res.getD v 0) :
    (mleFold n lb rp p).1.val M = multilinearEval res pt := by
  simp only [mleFold, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  rw [multilinearEval_eq res pt n hres hpt]
  refine mleLevels_spec rp n res pt hres hpt hrp n 0 p.e 1 _ (by omega) h.2 ?_
  intro v hv'
  have hv2 : v < 2 ^ n := by simpa using hv'
  have hjf : v < 2 ^ [n].sum := by simpa using hv2
  have hu : unflat [n] v = [v] := by simp [unflat, Nat.mod_eq_of_lt hv2]
  have r0 := loop_rel h.1 (jf := v) (t := 0) hjf (by simp)
  simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
    LoopOut.cell_val, Opd.val_abs] at r0
  simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, hu, Mem.rd_E, Mem.rd_K] at r0
  rw [loadE_eq] at r0
  simp only [Nat.one_mul, resAfter, List.take_zero, List.foldl_nil]
  rw [r0, ← hv v hv2]
  have h0 := hS v hv2 0 (by omega)
  have h1 := hS v hv2 1 (by omega)
  have h2 := hS v hv2 2 (by omega)
  simp only [Nat.add_zero] at h0
  rw [show lb + 1 + 3 * v = lb + 1 + 3 * v from rfl, h0, h1, h2]
  simp only [lane, feAt]
  -- `rw`, not `congr 1`: its `rfl` attempt on `kAt` unfolds the lane reads (31 s)
  rw [show 8 * (lb + 1 + 3 * v) = 8 * (lb + 3 * v) + 8 by ring,
    show 8 * (lb + 2 + 3 * v) = 8 * (lb + 3 * v) + 16 by ring]

/-- **The terminal check**: `t = weight · mle + target`, asserted zero under the gate. -/
def terminalCheck (w m tgt gate : Cell) : BM Unit := do
  let t ← mulAdd .E w m tgt
  assert0 t gate

/-- **Q_arith_eq, terminal check**: with the gate on, the assertion holds iff `F`'s
`terminal == target` (`weight · mle = target`). -/
theorem terminalCheck_iff {p : Ptr} {w m tgt gate : Cell}
    (h : SegsHold c M p (terminalCheck w m tgt gate p).2) (hg : gate.val M = 1) :
    SegsAssert M p (terminalCheck w m tgt gate p).2 ↔ w.val M * m.val M = tgt.val M := by
  simp only [terminalCheck, bind_apply, List.nil_append] at h ⊢
  rw [segsHold_append] at h
  have ht := mulAdd_spec h.1
  rw [segsAssert_append]
  have hrow : SegsAssert M p (mulAdd Ty.E w m tgt p).2 := by
    simp [mulAdd, rowRes, SegsAssert, Program.RowAssert, rowInst]
  constructor
  · intro ha
    have := assert0_spec ha.2
    rw [hg, one_mul, ht] at this
    have h2 : w.val M * m.val M + tgt.val M + tgt.val M = tgt.val M := by rw [this, zero_add]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h2
    exact h2
  · intro he
    refine ⟨hrow, ?_⟩
    simp only [assert0, emit]
    rw [segsAssert_row]
    show M.arg _ 1 * M.arg _ 0 = 0
    rw [rowInst_arg, rowInst_arg]
    show gate.val M * (mulAdd Ty.E w m tgt p).1.val M = 0
    rw [hg, one_mul, ht, he, CharTwo.add_self_eq_zero]

end Lvm.Loop.Build
