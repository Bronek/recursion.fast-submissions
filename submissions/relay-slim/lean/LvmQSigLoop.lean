import LvmQBuildLemmas

/-!
# Q_sig: `K`-valued loop rows on QL's builder

New for lvm (WP-12), on QL's builder (`LvmQBuild*`, `loop_rel`, `loop_assert`, `Opd.val_cur`): the
relation of a `K` template row of a loop as an equation in `K` (`loopK_lin`, `loopK_mad`,
`loopK_as0`), with operand values `ov` (`ov_abs`, `ov_cur`). Template-row shorthands `lr`, `mr`,
`ar`; operands `oA` (fixed `K` cell), `oS` (`K` cell moving by a stride).
-/

set_option autoImplicit false

namespace Lvm.QSig

open Lvm Lvm.Loop Lvm.Loop.Build

/-- A fixed `K` operand. -/
abbrev oA (n : Nat) : Opd := .abs ⟨.K, n, []⟩

/-- A `K` operand moving by `s` per iteration of a one-dimensional loop. -/
abbrev oS (n s : Nat) : Opd := .abs ⟨.K, n, [s]⟩

/-- Template row `c = a + k·b + k'`. -/
abbrev lr (k k' : FK) (a b : Opd) : LRow := ⟨.lin k k', .K, [a, b]⟩

/-- Template row `c = a·b + d`. -/
abbrev mr (a b d : Opd) : LRow := ⟨.muladd, .K, [a, b, d]⟩

/-- Template row `gate · a = 0`. -/
abbrev ar (a gate : Opd) : LRow := ⟨.assert0, .K, [a, gate]⟩

/-- The `K` value of an operand at an iteration. -/
def ov (M : Mem) (o : LoopOut) (jf : Nat) (x : Opd) : FK :=
  M.k ((x.resolve o.p o.dims o.tpl).at (unflat o.dims jf))

/-- The resolved operand is a `K` cell. -/
def OpdK (o : LoopOut) (x : Opd) : Prop := (x.resolve o.p o.dims o.tpl).ty = .K

theorem opd_val_K {M : Mem} {o : LoopOut} {jf : Nat} {x : Opd} (h : OpdK o x) :
    x.val M o jf = FE.ofK (ov M o jf x) := by
  unfold Opd.val ov; rw [h]; rfl

theorem ov_abs (M : Mem) (o : LoopOut) (jf n : Nat) (s : List Nat) :
    ov M o jf (.abs ⟨.K, n, s⟩) = M.k (n + dot s (unflat o.dims jf)) := rfl

theorem ov_oA (M : Mem) (o : LoopOut) (jf n : Nat) : ov M o jf (oA n) = M.k n := by
  simp [ov, Opd.resolve, Addr.at, dot]

theorem ov_oS (M : Mem) (o : LoopOut) {d jf : Nat} (hd : o.dims = [d]) (hjf : jf < 2 ^ d)
    (n s : Nat) : ov M o jf (oS n s) = M.k (n + s * jf) := by
  simp [ov, Opd.resolve, Addr.at, dot, hd, Nat.mod_eq_of_lt hjf, unflat]

theorem ov_cur (M : Mem) (o : LoopOut) {jf : Nat} (hjf : jf < 2 ^ o.dims.sum) (t : Nat)
    (hK : (o.tpl.getD t default).ty = .K) : ov M o jf (.cur t) = M.k (o.cell t jf).n := by
  have := Opd.val_cur M o hjf t
  have hc : (o.cell t jf).ty = .K := hK
  have h2 : OpdK o (.cur t) := hK
  rw [opd_val_K h2, Cell.val, hc] at this
  exact ofK_inj this

theorem cell_K {M : Mem} {o : LoopOut} {t jf : Nat} (hK : (o.tpl.getD t default).ty = .K) :
    (o.cell t jf).val M = FE.ofK (M.k (o.cell t jf).n) := by
  simp only [Cell.val, LoopOut.cell, hK]; rfl

/-- **A `lin` row of a loop, in `K`.** -/
theorem loopK_lin {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr}
    (h : SegsHold c M p (loop dims tpl p).2) {jf t : Nat} (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {k k' : FK} {a b : Opd} (hr : tpl.getD t default = lr k k' a b)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b) :
    M.k ((loop dims tpl p).1.cell t jf).n =
      ov M (loop dims tpl p).1 jf a + k * ov M (loop dims tpl p).1 jf b + k' := by
  have hl := loop_rel h hjf ht
  have hK : ((loop dims tpl p).1.tpl.getD t default).ty = .K := by
    show (tpl.getD t default).ty = .K; rw [hr]
  unfold LRel LoopOut.arg at hl
  simp only [loop_apply] at hl hK ha hb ⊢
  rw [hr] at hl
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hl
  rw [cell_K (o := ⟨p, dims, tpl⟩) hK, opd_val_K ha, opd_val_K hb, ← ofK_mul, ← ofK_add,
    ← ofK_add] at hl
  exact ofK_inj hl

/-- **A `muladd` row of a loop, in `K`.** -/
theorem loopK_mad {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr}
    (h : SegsHold c M p (loop dims tpl p).2) {jf t : Nat} (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {a b d : Opd} (hr : tpl.getD t default = mr a b d)
    (ha : OpdK (loop dims tpl p).1 a) (hb : OpdK (loop dims tpl p).1 b)
    (hd : OpdK (loop dims tpl p).1 d) :
    M.k ((loop dims tpl p).1.cell t jf).n =
      ov M (loop dims tpl p).1 jf a * ov M (loop dims tpl p).1 jf b + ov M (loop dims tpl p).1 jf d := by
  have hl := loop_rel h hjf ht
  have hK : ((loop dims tpl p).1.tpl.getD t default).ty = .K := by
    show (tpl.getD t default).ty = .K; rw [hr]
  unfold LRel LoopOut.arg at hl
  simp only [loop_apply] at hl hK ha hb hd ⊢
  rw [hr] at hl
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hl
  rw [cell_K (o := ⟨p, dims, tpl⟩) hK, opd_val_K ha, opd_val_K hb, opd_val_K hd, ← ofK_mul,
    ← ofK_add] at hl
  exact ofK_inj hl

/-- **An `assert0` row of a loop, in `K`.** -/
theorem loopK_as0 {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr}
    (h : SegsAssert M p (loop dims tpl p).2) {jf t : Nat} (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) {a g : Opd} (hr : tpl.getD t default = ar a g)
    (ha : OpdK (loop dims tpl p).1 a) (hg : OpdK (loop dims tpl p).1 g) :
    ov M (loop dims tpl p).1 jf g * ov M (loop dims tpl p).1 jf a = 0 := by
  have hl := loop_assert h hjf ht
  unfold LAssert LoopOut.arg at hl
  simp only [loop_apply] at hl ha hg ⊢
  rw [hr] at hl
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hl
  rw [opd_val_K ha, opd_val_K hg, ← ofK_mul] at hl
  exact ofK_inj hl

end Lvm.QSig
