-- New for lvm (WP-11b-QL): the specifications of `LvmQBuild`'s primitives (no earlier formalisation
-- has WP-10's LoopIR; the `g`-power address lemma follows leanVM's exponent addressing, WP-0 flag 2).
import LvmQBuildSem

/-!
# Specifications of the builder's primitives

Every lemma has the shape `SegsHold c M p (g p).2 → fact about (g p).1 in M` (and `SegsAssert` for
assertions), so a gadget's proof is a chain of these through `hold_bind`/`assert_bind`.

* `K` embeds in `E`: `ofK_add`, `ofK_mul`, `ofK_inj`.
* Straight-line rows: `mulAdd_spec`, `lin_spec`, `loadE_spec`, `fixmul_spec`, `readd_spec` (with
  `GInj`: the computed address names exactly one cell), `assert0_spec`; on `K` cells
  (`kc`): `mulAddK_spec`, `linK_spec`, `addK_specK`, `assert0K_spec`, `assertEqK_spec`,
  `assertEqKK_spec`.
* Loops: `loop_rel` (row `t` at iteration `jf`: `LRel`, the operation on the resolved operand
  values `LoopOut.arg`), `loop_assert`, `Opd.val_abs`, `Opd.val_cur`, `Opd.val_prev`;
  `loopP_out`, `loopP_prev_zero` (the prologue's copies), `loopP_prev_succ`.
* Addresses from bits: `gpowBits_spec` (`g^(lo + s · Σ β_k 2^k)` from Boolean `K` cells).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-! ## `K` inside `E` -/

theorem ofK_add (a b : FK) : FE.ofK (a + b) = FE.ofK a + FE.ofK b := map_add FE.ofKRingHom a b
theorem ofK_mul (a b : FK) : FE.ofK (a * b) = FE.ofK a * FE.ofK b := map_mul FE.ofKRingHom a b
theorem ofK_inj {a b : FK} (h : FE.ofK a = FE.ofK b) : a = b := congrArg FE.c₀ h
theorem ofK_zero : FE.ofK 0 = 0 := rfl
theorem ofK_one : FE.ofK 1 = 1 := rfl

theorem FK.add_self (a : FK) : a + a = 0 := CharTwo.add_self_eq_zero a

/-! ## Straight-line rows -/

theorem dot_nil (s : List Nat) : dot s [] = 0 := by cases s <;> rfl

theorem rowInst_res (M : Mem) (p : Ptr) (r : Row) :
    M.res (rowInst p r) = M.rd r.ty (p.at r.ty) := by
  rcases r with ⟨op, τ, args⟩; cases τ <;> rfl

theorem rowInst_arg (M : Mem) (p : Ptr) (op : Op) (τ : Ty) (args : List Addr) (o : Nat) :
    M.arg (rowInst p ⟨op, τ, args⟩) o = M.rd (args.getD o default).ty (args.getD o default).base := by
  simp [Mem.arg, Inst.arg, rowInst, Addr.at, dot_nil]

theorem segsHold_row {c : Ctx} {M : Mem} {p : Ptr} {r : Row} :
    SegsHold c M p [.row r] ↔ RowRel c M (rowInst p r) := by simp [SegsHold]

theorem segsAssert_row {M : Mem} {p : Ptr} {r : Row} :
    SegsAssert M p [.row r] ↔ Program.RowAssert M (rowInst p r) := by simp [SegsAssert]

/-- The result of a row gadget is the cell at the pointer. -/
theorem rowRes_val (M : Mem) (τ : Ty) (r : Row) (p : Ptr) : (rowRes τ r p).1.val M = M.rd τ (p.at τ) := rfl

section
variable {c : Ctx} {M : Mem} {p : Ptr}

theorem mulAdd_spec {τ : Ty} {a b d : Cell} (h : SegsHold c M p (mulAdd τ a b d p).2) :
    (mulAdd τ a b d p).1.val M = a.val M * b.val M + d.val M := by
  have h1 : M.res (rowInst p ⟨.muladd, τ, [a.addr, b.addr, d.addr]⟩) =
      M.arg (rowInst p ⟨.muladd, τ, [a.addr, b.addr, d.addr]⟩) 0 *
        M.arg (rowInst p ⟨.muladd, τ, [a.addr, b.addr, d.addr]⟩) 1 +
      M.arg (rowInst p ⟨.muladd, τ, [a.addr, b.addr, d.addr]⟩) 2 := segsHold_row.mp h
  rw [rowInst_res, rowInst_arg, rowInst_arg, rowInst_arg] at h1
  exact h1

theorem lin_spec {τ : Ty} {k k' : FK} {a b : Cell} (h : SegsHold c M p (lin τ k k' a b p).2) :
    (lin τ k k' a b p).1.val M = a.val M + FE.ofK k * b.val M + FE.ofK k' := by
  have h1 : M.res (rowInst p ⟨.lin k k', τ, [a.addr, b.addr]⟩) =
      M.arg (rowInst p ⟨.lin k k', τ, [a.addr, b.addr]⟩) 0 +
        FE.ofK k * M.arg (rowInst p ⟨.lin k k', τ, [a.addr, b.addr]⟩) 1 + FE.ofK k' :=
    segsHold_row.mp h
  rw [rowInst_res, rowInst_arg, rowInst_arg] at h1
  exact h1

theorem loadE_spec {a₀ a₁ a₂ : Cell} (h : SegsHold c M p (loadE a₀ a₁ a₂ p).2) :
    (loadE a₀ a₁ a₂ p).1.val M = a₀.val M + FE.y * a₁.val M + FE.y * FE.y * a₂.val M := by
  have h1 : M.res (rowInst p ⟨.loadE, .E, [a₀.addr, a₁.addr, a₂.addr]⟩) =
      M.arg (rowInst p ⟨.loadE, .E, [a₀.addr, a₁.addr, a₂.addr]⟩) 0 +
        FE.y * M.arg (rowInst p ⟨.loadE, .E, [a₀.addr, a₁.addr, a₂.addr]⟩) 1 +
      FE.y * FE.y * M.arg (rowInst p ⟨.loadE, .E, [a₀.addr, a₁.addr, a₂.addr]⟩) 2 :=
    segsHold_row.mp h
  rw [rowInst_res, rowInst_arg, rowInst_arg, rowInst_arg] at h1
  exact h1

theorem fixmul_spec {τ : Ty} {a d : Cell} (h : SegsHold c M p (fixmul τ a d p).2) :
    (fixmul τ a d p).1.val M = FE.ofK (c.fm []) * a.val M + d.val M := by
  have h1 : M.res (rowInst p ⟨.fixmul, τ, [a.addr, d.addr]⟩) =
      FE.ofK (c.fm []) * M.arg (rowInst p ⟨.fixmul, τ, [a.addr, d.addr]⟩) 0 +
        M.arg (rowInst p ⟨.fixmul, τ, [a.addr, d.addr]⟩) 1 := segsHold_row.mp h
  rw [rowInst_res, rowInst_arg, rowInst_arg] at h1
  exact h1

/-- **A read at a computed address**: if the address cell holds `g^e₀` and `g`-powers are
injective below `N` (above the cell counts and `e₀`), the result is cell `e₀`. -/
theorem readd_spec {τ : Ty} {lo m : Nat} {α : Cell} {N e₀ : Nat}
    (h : SegsHold c M p (readd τ lo m α p).2) (hinj : GInj N) (hN : c.cells τ ≤ N)
    (hα : α.val M = FE.ofK (FK.x ^ e₀)) (he : e₀ < N) :
    (readd τ lo m α p).1.val M = M.rd τ e₀ := by
  have h1 : ∃ e < c.cells τ, FK.x ^ e = (M.arg (rowInst p ⟨.readd lo m, τ, [α.addr]⟩) 0).c₀ ∧
      M.res (rowInst p ⟨.readd lo m, τ, [α.addr]⟩) = M.rd τ e := segsHold_row.mp h
  obtain ⟨e, he', hx, hr⟩ := h1
  rw [rowInst_arg] at hx
  rw [rowInst_res] at hr
  have : e = e₀ := hinj e e₀ (by omega) he (by rw [hx]; exact congrArg FE.c₀ hα)
  subst this
  exact hr

theorem assert0_spec {a g : Cell} (h : SegsAssert M p (assert0 a g p).2) :
    g.val M * a.val M = 0 := by
  have h1 : M.arg (rowInst p ⟨.assert0, .K, [a.addr, g.addr]⟩) 1 *
      M.arg (rowInst p ⟨.assert0, .K, [a.addr, g.addr]⟩) 0 = 0 := segsAssert_row.mp h
  rw [rowInst_arg, rowInst_arg] at h1
  exact h1

/-! ### On `K` cells -/

theorem mulAddK_spec {a b d : Nat} (h : SegsHold c M p (mulAdd .K (kc a) (kc b) (kc d) p).2) :
    M.k p.k = M.k a * M.k b + M.k d := by
  have := mulAdd_spec h
  simp only [mulAdd, rowRes, Cell.val, Ptr.at, Mem.rd, kc] at this
  rw [← ofK_mul, ← ofK_add] at this
  exact ofK_inj this

theorem linK_spec {k k' : FK} {a b : Nat} (h : SegsHold c M p (lin .K k k' (kc a) (kc b) p).2) :
    M.k p.k = M.k a + k * M.k b + k' := by
  have := lin_spec h
  simp only [lin, rowRes, Cell.val, Ptr.at, Mem.rd, kc] at this
  rw [← ofK_mul, ← ofK_add, ← ofK_add] at this
  exact ofK_inj this

theorem assert0K_spec {a g : Nat} (h : SegsAssert M p (assert0 (kc a) (kc g) p).2) :
    M.k g * M.k a = 0 := by
  have := assert0_spec h
  simp only [Cell.val, Mem.rd, kc] at this
  rw [← ofK_mul] at this
  exact ofK_inj this

/-- `assertEq` on `K` cells: when the gate is `1`, the cells are equal. -/
theorem assertEqKK_spec {a b g : Nat} (h : SegsHold c M p (assertEq (kc a) (kc b) (kc g) p).2)
    (hA : SegsAssert M p (assertEq (kc a) (kc b) (kc g) p).2) (hg : M.k g = 1) : M.k a = M.k b := by
  rw [assertEq, hold_bind] at h
  rw [assertEq, assert_bind] at hA
  have h1 := linK_spec h.1
  have h2 := assert0K_spec (a := p.k) hA.2
  rw [hg, one_mul, h1, one_mul, add_zero] at h2
  have := congrArg (· + M.k b) h2
  simpa [add_assoc, FK.add_self] using this

/-- `assertEqK` on a `K` cell: when the gate is `1`, the cell is the constant. -/
theorem assertEqK_spec {a g : Nat} {k' : FK} (h : SegsHold c M p (assertEqK (kc a) k' (kc g) p).2)
    (hA : SegsAssert M p (assertEqK (kc a) k' (kc g) p).2) (hg : M.k g = 1) : M.k a = k' := by
  rw [assertEqK, hold_bind] at h
  rw [assertEqK, assert_bind] at hA
  have h1 := linK_spec h.1
  have h2 := assert0K_spec (a := p.k) hA.2
  rw [hg, one_mul, h1, zero_mul, add_zero] at h2
  have := congrArg (· + k') h2
  simpa [add_assoc, FK.add_self] using this

end

/-! ## Loops -/

theorem getD_map_default {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (hf : f default = default)
    (l : List α) (t : Nat) : (l.map f).getD t default = f (l.getD t default) := by
  induction l generalizing t with
  | nil => simp [hf]
  | cons x xs ih =>
    cases t with
    | zero => rfl
    | succ t => exact ih t

/-- A template row with its operands resolved. -/
def resRow (p : Ptr) (dims : List Nat) (tpl : List LRow) (r : LRow) : Row :=
  ⟨r.op, r.ty, r.args.map (Opd.resolve p dims tpl)⟩

theorem mkLoop_row (p : Ptr) (dims : List Nat) (tpl : List LRow) (t : Nat) :
    (mkLoop p dims tpl).tpl.getD t default = resRow p dims tpl (tpl.getD t default) :=
  getD_map_default (resRow p dims tpl) rfl tpl t

theorem resRow_w (p : Ptr) (dims : List Nat) (tpl : List LRow) (τ : Ty) (r : LRow) :
    (resRow p dims tpl r).w τ = r.w τ := rfl

theorem mkLoop_tw (p : Ptr) (dims : List Nat) (tpl : List LRow) (τ : Ty) :
    (mkLoop p dims tpl).tw τ = ltw τ tpl := by
  simp only [Block.tw, mkLoop, ltw, List.map_map]
  rfl

theorem mkLoop_rank (p : Ptr) (dims : List Nat) (tpl : List LRow) (τ : Ty) (t : Nat) :
    (mkLoop p dims tpl).rank τ t = lrank τ tpl t := by
  simp only [Block.rank, mkLoop, lrank, ← List.map_take, List.map_map]
  rfl

theorem instAt_clock (p : Ptr) (B : Block) (jf t : Nat) (τ : Ty) :
    (instAt p B jf t).clock τ = p.at τ + B.tw τ * jf + B.rank τ t := by
  cases τ <;> rfl

/-- The value of a template operand at flat iteration `jf` of the loop `o`. -/
def Opd.val (M : Mem) (o : LoopOut) (jf : Nat) (x : Opd) : FE :=
  M.rd (x.resolve o.p o.dims o.tpl).ty ((x.resolve o.p o.dims o.tpl).at (unflat o.dims jf))

/-- Operand `k` of template row `t` at flat iteration `jf`. -/
def LoopOut.arg (M : Mem) (o : LoopOut) (jf t k : Nat) : FE :=
  ((o.tpl.getD t default).args.getD k default).val M o jf

/-- **The relation of template row `t` at flat iteration `jf`** of the loop `o` (`RowRel` on the
resolved operands). -/
def LRel (c : Ctx) (M : Mem) (o : LoopOut) (jf t : Nat) : Prop :=
  match (o.tpl.getD t default).op with
  | .muladd => (o.cell t jf).val M = o.arg M jf t 0 * o.arg M jf t 1 + o.arg M jf t 2
  | .lin k k' => (o.cell t jf).val M = o.arg M jf t 0 + FE.ofK k * o.arg M jf t 1 + FE.ofK k'
  | .assert0 => True
  | .loadE => (o.cell t jf).val M = o.arg M jf t 0 + FE.y * o.arg M jf t 1 + FE.y * FE.y * o.arg M jf t 2
  | .fixmul => (o.cell t jf).val M = FE.ofK (c.fm (unflat o.dims jf)) * o.arg M jf t 0 + o.arg M jf t 1
  | .readd _ _ => ∃ e < c.cells (o.tpl.getD t default).ty,
      FK.x ^ e = (o.arg M jf t 0).c₀ ∧ (o.cell t jf).val M = M.rd (o.tpl.getD t default).ty e

/-- The assertion of template row `t` at flat iteration `jf`. -/
def LAssert (M : Mem) (o : LoopOut) (jf t : Nat) : Prop :=
  match (o.tpl.getD t default).op with
  | .assert0 => o.arg M jf t 1 * o.arg M jf t 0 = 0
  | _ => True

/-- The block a loop gadget emits. -/
def LoopOut.blk (o : LoopOut) : Block := mkLoop o.p o.dims o.tpl

theorem loop_apply (dims : List Nat) (tpl : List LRow) (p : Ptr) :
    loop dims tpl p = (⟨p, dims, tpl⟩, [.blk (mkLoop p dims tpl)]) := rfl

theorem instAt_loop_res (M : Mem) (o : LoopOut) (jf t : Nat) :
    M.res (instAt o.p o.blk jf t) = (o.cell t jf).val M := by
  simp only [Mem.res, instAt_clock]
  simp only [instAt, LoopOut.blk, mkLoop_row, resRow, mkLoop_tw, mkLoop_rank, LoopOut.cell,
    Cell.val]
  rw [Nat.add_right_comm]

theorem instAt_loop_arg (M : Mem) (o : LoopOut) (jf t k : Nat) :
    M.arg (instAt o.p o.blk jf t) k = o.arg M jf t k := by
  simp only [Mem.arg, Inst.arg, instAt, LoopOut.blk, mkLoop_row, resRow, LoopOut.arg, Opd.val]
  rw [getD_map_default (Opd.resolve o.p o.dims o.tpl) rfl]
  rfl

/-- **A loop row at an iteration** (`RowRel` of the instance). -/
theorem loop_rel_iff (c : Ctx) (M : Mem) (o : LoopOut) (jf t : Nat) :
    RowRel c M (instAt o.p o.blk jf t) ↔ LRel c M o jf t := by
  have hrow : (instAt o.p o.blk jf t).row = resRow o.p o.dims o.tpl (o.tpl.getD t default) :=
    mkLoop_row _ _ _ _
  have hj : (instAt o.p o.blk jf t).j = unflat o.dims jf := rfl
  unfold RowRel LRel
  rw [hrow]
  simp only [resRow, instAt_loop_res, instAt_loop_arg, hj]
  rfl

theorem loop_assert_iff (M : Mem) (o : LoopOut) (jf t : Nat) :
    Program.RowAssert M (instAt o.p o.blk jf t) ↔ LAssert M o jf t := by
  have hrow : (instAt o.p o.blk jf t).row = resRow o.p o.dims o.tpl (o.tpl.getD t default) :=
    mkLoop_row _ _ _ _
  unfold Program.RowAssert LAssert
  rw [hrow]
  simp only [resRow, instAt_loop_arg]
  exact Iff.rfl

/-- **The rows of a loop hold at every iteration.** -/
theorem loop_rel {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr}
    (h : SegsHold c M p (loop dims tpl p).2) {jf t : Nat} (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) : LRel c M (loop dims tpl p).1 jf t := by
  simp only [loop_apply, SegsHold] at h
  exact (loop_rel_iff c M ⟨p, dims, tpl⟩ jf t).mp (h.1 jf hjf t (by simpa [mkLoop] using ht))

theorem loop_assert {M : Mem} {dims : List Nat} {tpl : List LRow} {p : Ptr}
    (h : SegsAssert M p (loop dims tpl p).2) {jf t : Nat} (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) : LAssert M (loop dims tpl p).1 jf t := by
  simp only [loop_apply, SegsAssert] at h
  exact (loop_assert_iff M ⟨p, dims, tpl⟩ jf t).mp (h.1 jf hjf t (by simpa [mkLoop] using ht))

/-! ### A loop row of a known operation -/

section
variable {c : Ctx} {M : Mem} {o : LoopOut} {jf t : Nat}

theorem lrel_muladd {τ : Ty} {args : List Opd} (hr : o.tpl.getD t default = ⟨.muladd, τ, args⟩)
    (h : LRel c M o jf t) : (o.cell t jf).val M =
      (args.getD 0 default).val M o jf * (args.getD 1 default).val M o jf + (args.getD 2 default).val M o jf := by
  unfold LRel LoopOut.arg at h; rw [hr] at h; exact h

theorem lrel_lin {k k' : FK} {τ : Ty} {args : List Opd} (hr : o.tpl.getD t default = ⟨.lin k k', τ, args⟩)
    (h : LRel c M o jf t) : (o.cell t jf).val M =
      (args.getD 0 default).val M o jf + FE.ofK k * (args.getD 1 default).val M o jf + FE.ofK k' := by
  unfold LRel LoopOut.arg at h; rw [hr] at h; exact h

theorem lrel_readd {lo m : Nat} {τ : Ty} {args : List Opd} (hr : o.tpl.getD t default = ⟨.readd lo m, τ, args⟩)
    (h : LRel c M o jf t) : ∃ e < c.cells τ, FK.x ^ e = ((args.getD 0 default).val M o jf).c₀ ∧
      (o.cell t jf).val M = M.rd τ e := by
  unfold LRel LoopOut.arg at h; rw [hr] at h; exact h

theorem lassert_of {τ : Ty} {args : List Opd} (hr : o.tpl.getD t default = ⟨.assert0, τ, args⟩)
    (h : LAssert M o jf t) : (args.getD 1 default).val M o jf * (args.getD 0 default).val M o jf = 0 := by
  unfold LAssert LoopOut.arg at h; rw [hr] at h; exact h

end

theorem Opd.val_absK (M : Mem) (o : LoopOut) (jf : Nat) (base : Nat) (strides : List Nat) :
    (Opd.abs ⟨.K, base, strides⟩).val M o jf = FE.ofK (M.k (base + dot strides (unflat o.dims jf))) := rfl

theorem Cell.val_opd (M : Mem) (o : LoopOut) (jf : Nat) (x : Cell) :
    x.opd.val M o jf = x.val M := by
  simp only [Cell.opd, Opd.val, Opd.resolve, Cell.addr, Addr.at, Cell.val]
  rfl

/-! ### Operand values -/

theorem dot_scaled : ∀ (dims : List Nat) (w : Nat) (j : List Nat),
    dot (scaledStrides dims w) j = w * flat dims j
  | [], _, _ => by simp [scaledStrides, dot, flat]
  | d :: ds, w, [] => by simp [scaledStrides, dot, flat]
  | d :: ds, w, j :: js => by
    simp only [scaledStrides, dot, flat, dot_scaled ds]
    rw [Nat.mul_add, Nat.mul_assoc]

theorem Opd.val_abs (M : Mem) (o : LoopOut) (jf : Nat) (a : Addr) :
    (Opd.abs a).val M o jf = M.rd a.ty (a.at (unflat o.dims jf)) := rfl

theorem LoopOut.cell_val (M : Mem) (o : LoopOut) (t jf : Nat) :
    (o.cell t jf).val M = M.rd (o.tpl.getD t default).ty
      (o.p.at (o.tpl.getD t default).ty + lrank (o.tpl.getD t default).ty o.tpl t +
        ltw (o.tpl.getD t default).ty o.tpl * jf) := rfl

theorem Opd.val_cur (M : Mem) (o : LoopOut) {jf : Nat} (hjf : jf < 2 ^ o.dims.sum) (t : Nat) :
    (Opd.cur t).val M o jf = (o.cell t jf).val M := by
  simp only [Opd.val, Opd.resolve, curAddr, Addr.at, dot_scaled, flat_unflat_of_lt _ hjf,
    LoopOut.cell, Cell.val]

theorem Opd.val_prev (M : Mem) (o : LoopOut) {jf : Nat} (hjf : jf < 2 ^ o.dims.sum) (t : Nat) :
    (Opd.prev t).val M o jf = M.rd (o.tpl.getD t default).ty
      (o.p.at (o.tpl.getD t default).ty + lrank (o.tpl.getD t default).ty o.tpl t -
        ltw (o.tpl.getD t default).ty o.tpl + ltw (o.tpl.getD t default).ty o.tpl * jf) := by
  simp only [Opd.val, Opd.resolve, curAddr, Addr.at, dot_scaled, flat_unflat_of_lt _ hjf]

/-- `prev` at iteration `jf + 1` is the row's result at `jf` (when the loop's pointer is past one
iteration's cells, as after a prologue). -/
theorem Opd.val_prev_succ (M : Mem) (o : LoopOut) {jf : Nat} (hjf : jf + 1 < 2 ^ o.dims.sum) (t : Nat)
    (hp : ltw (o.tpl.getD t default).ty o.tpl ≤ o.p.at (o.tpl.getD t default).ty) :
    (Opd.prev t).val M o (jf + 1) = (o.cell t jf).val M := by
  rw [Opd.val_prev M o hjf, LoopOut.cell_val]
  congr 1
  rw [Nat.mul_succ]
  omega

/-! ### The prologue -/

theorem prologueRow_w (init : Nat → Cell) (t : Nat) (r : LRow) (τ : Ty) :
    segsW τ (prologueRow init t r) = r.w τ := by
  rcases r with ⟨op, ty, args⟩
  cases op <;> simp [prologueRow, segsW, Seg.w, LRow.w, Row.w, Row.writes]

theorem prologueSegs_w (init : Nat → Cell) (τ : Ty) : ∀ (t : Nat) (tpl : List LRow),
    segsW τ (prologueSegs init t tpl) = ltw τ tpl
  | _, [] => rfl
  | t, r :: rs => by
    simp only [prologueSegs, segsW_append, prologueSegs_w init τ (t + 1) rs, ltw, List.map_cons,
      List.sum_cons, prologueRow_w]

/-- The prologue's copies: writing row `t`'s cell of iteration `−1` holds `init t`. -/
theorem prologueSegs_spec {c : Ctx} {M : Mem} (init : Nat → Cell) : ∀ (p : Ptr) (t₀ : Nat)
    (tpl : List LRow), SegsHold c M p (prologueSegs init t₀ tpl) →
    ∀ t < tpl.length, (tpl.getD t default).op ≠ .assert0 →
      M.rd (tpl.getD t default).ty (p.at (tpl.getD t default).ty + lrank (tpl.getD t default).ty tpl t) =
        (init (t₀ + t)).val M
  | _, _, [], _, t, ht, _ => absurd ht (by simp)
  | p, t₀, r :: rs, h, t, ht, hop => by
    simp only [prologueSegs] at h
    rw [segsHold_append] at h
    rcases t with _ | t
    · simp only [List.getD_cons_zero, lrank, List.take_zero, List.map_nil, List.sum_nil,
        Nat.add_zero] at hop ⊢
      rcases r with ⟨op, ty, args⟩
      have h1 : SegsHold c M p [.row ⟨.lin 0 0, ty, [(init t₀).addr, (init t₀).addr]⟩] := by
        cases op <;> first | exact absurd rfl hop | exact h.1
      have h2 := lin_spec (c := c) (M := M) (p := p) (τ := ty) (k := 0) (k' := 0)
        (a := init t₀) (b := init t₀) h1
      simp only [lin, rowRes, Cell.val, ofK_zero, zero_mul, add_zero] at h2
      exact h2
    · have ih := prologueSegs_spec init _ (t₀ + 1) rs h.2 t (by simpa using ht) (by simpa using hop)
      simp only [List.getD_cons_succ] at ih ⊢
      rw [show t₀ + (t + 1) = t₀ + 1 + t by omega, ← ih]
      congr 1
      simp only [Ptr.adv, lrank, List.take_succ_cons, List.map_cons, List.sum_cons, prologueRow_w]
      generalize (rs.getD t default).ty = τ
      cases τ <;> simp only [Ptr.at] <;> omega

theorem loopP_apply (dims : List Nat) (tpl : List LRow) (init : Nat → Cell) (p : Ptr) :
    loopP dims tpl init p =
      (⟨p.adv (prologueSegs init 0 tpl), dims, tpl⟩,
        prologueSegs init 0 tpl ++ [.blk (mkLoop (p.adv (prologueSegs init 0 tpl)) dims tpl)]) := rfl

/-- The loop of `loopP` starts one iteration's cells after the prologue's start. -/
theorem loopP_ptr (dims : List Nat) (tpl : List LRow) (init : Nat → Cell) (p : Ptr) (τ : Ty) :
    (loopP dims tpl init p).1.p.at τ = p.at τ + ltw τ tpl := by
  rw [loopP_apply]; cases τ <;> simp [Ptr.at, Ptr.adv, prologueSegs_w]

/-- **`loopP`'s rows hold** at every iteration (its loop is `(loopP …).1`). -/
theorem loopP_rel {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow} {init : Nat → Cell}
    {p : Ptr} (h : SegsHold c M p (loopP dims tpl init p).2) {jf t : Nat} (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) : LRel c M (loopP dims tpl init p).1 jf t := by
  rw [loopP_apply, segsHold_append] at h
  have := loop_rel (c := c) (M := M) (dims := dims) (tpl := tpl) (p := p.adv (prologueSegs init 0 tpl))
    (by simpa [loop_apply] using h.2) hjf ht
  simpa [loop_apply, loopP_apply] using this

theorem loopP_assert {M : Mem} {dims : List Nat} {tpl : List LRow} {init : Nat → Cell}
    {p : Ptr} (h : SegsAssert M p (loopP dims tpl init p).2) {jf t : Nat} (hjf : jf < 2 ^ dims.sum)
    (ht : t < tpl.length) : LAssert M (loopP dims tpl init p).1 jf t := by
  rw [loopP_apply, segsAssert_append] at h
  have := loop_assert (M := M) (dims := dims) (tpl := tpl) (p := p.adv (prologueSegs init 0 tpl))
    (by simpa [loop_apply] using h.2) hjf ht
  simpa [loop_apply, loopP_apply] using this

/-- **`prev` at iteration `0` reads the prologue**: `init t`. -/
theorem loopP_prev_zero {c : Ctx} {M : Mem} {dims : List Nat} {tpl : List LRow}
    {init : Nat → Cell} {p : Ptr} (h : SegsHold c M p (loopP dims tpl init p).2) {t : Nat}
    (ht : t < tpl.length) (hop : (tpl.getD t default).op ≠ .assert0) :
    (Opd.prev t).val M (loopP dims tpl init p).1 0 = (init t).val M := by
  rw [loopP_apply, segsHold_append] at h
  have hs := prologueSegs_spec init p 0 tpl h.1 t ht hop
  rw [Nat.zero_add] at hs
  rw [Opd.val_prev M _ (Nat.two_pow_pos _), ← hs]
  have hp := loopP_ptr dims tpl init p (tpl.getD t default).ty
  simp only [loopP_apply] at hp ⊢
  rw [hp]
  congr 1
  omega

/-- `prev` at iteration `jf + 1` of `loopP` is the row's result at `jf`. -/
theorem loopP_prev_succ (M : Mem) (dims : List Nat) (tpl : List LRow) (init : Nat → Cell) (p : Ptr)
    {jf : Nat} (hjf : jf + 1 < 2 ^ dims.sum) (t : Nat) :
    (Opd.prev t).val M (loopP dims tpl init p).1 (jf + 1) = ((loopP dims tpl init p).1.cell t jf).val M :=
  Opd.val_prev_succ M _ hjf t (by rw [loopP_ptr]; exact Nat.le_add_left _ _)

/-! ## Addresses from bits -/

/-- The number whose bit `k` is `1` iff bit cell `k` holds `1`. -/
def bitsNat (M : Mem) : List Cell → Nat
  | [] => 0
  | β :: bs => (if M.k β.n = 1 then 1 else 0) + 2 * bitsNat M bs

/-- A Boolean `K` cell. -/
def IsBit (M : Mem) (β : Cell) : Prop := β.ty = .K ∧ (M.k β.n = 0 ∨ M.k β.n = 1)

theorem gpow_add (a b : Nat) : gpow (a + b) = gpow a * gpow b := pow_add FK.x a b

theorem gpow_zero : gpow 0 = 1 := pow_zero FK.x

/-- `(1 + β(G + 1))·A = G^β·A` for a bit `β` (characteristic 2). -/
theorem bit_select (A G b : FK) (hb : b = 0 ∨ b = 1) :
    b * (A + G * A + 0) + A = A * (if b = 1 then G else 1) := by
  rcases hb with rfl | rfl
  · simp [show (0 : FK) ≠ 1 from by decide]
  · simp only [one_mul, add_zero, ite_true]
    rw [add_comm A, add_assoc, FK.add_self, add_zero, mul_comm]

/-- One more bit: `u = (G + 1)·acc` at `p.k`, `acc' = β·u + acc` at `p.k + 1`. -/
theorem gpowBitsGo_cons (s k : Nat) (acc β : Cell) (bs : List Cell) (p : Ptr) :
    gpowBits.gpowBitsGo s k acc (β :: bs) p =
      ((gpowBits.gpowBitsGo s (k + 1) (kc (p.k + 1)) bs ⟨p.k + 1 + 1, p.e⟩).1,
        [.row ⟨.lin (gpow (s * 2 ^ k)) 0, .K, [acc.addr, acc.addr]⟩] ++
          ([.row ⟨.muladd, .K, [β.addr, (kc p.k).addr, acc.addr]⟩] ++
            (gpowBits.gpowBitsGo s (k + 1) (kc (p.k + 1)) bs ⟨p.k + 1 + 1, p.e⟩).2)) := rfl

theorem gpowBits_cons (lo s : Nat) (x β₀ : Cell) (bs : List Cell) (p : Ptr) :
    gpowBits lo s x (β₀ :: bs) p =
      ((gpowBits.gpowBitsGo s 1 (kc p.k) bs ⟨p.k + 1, p.e⟩).1,
        [.row ⟨.lin (gpow lo * (gpow s + 1) + 1) (gpow lo), .K, [β₀.addr, β₀.addr]⟩] ++
          (gpowBits.gpowBitsGo s 1 (kc p.k) bs ⟨p.k + 1, p.e⟩).2) := rfl

/-- A `K` row's segment: its relation at `p`, then the rest one `K` cell later. -/
theorem segsHold_consK {c : Ctx} {M : Mem} {p : Ptr} {op : Op} {args : List Addr} {δ : List Seg}
    (hop : op ≠ .assert0) :
    SegsHold c M p (.row ⟨op, .K, args⟩ :: δ) ↔
      RowRel c M (rowInst p ⟨op, .K, args⟩) ∧ SegsHold c M ⟨p.k + 1, p.e⟩ δ := by
  have : p.adv [.row ⟨op, .K, args⟩] = ⟨p.k + 1, p.e⟩ := by
    cases op <;> first | exact absurd rfl hop | simp [Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
  simp only [SegsHold, this]

theorem segsAssert_consK {M : Mem} {p : Ptr} {op : Op} {args : List Addr} {δ : List Seg}
    (hop : op ≠ .assert0) :
    SegsAssert M p (.row ⟨op, .K, args⟩ :: δ) ↔ SegsAssert M ⟨p.k + 1, p.e⟩ δ := by
  have : p.adv [.row ⟨op, .K, args⟩] = ⟨p.k + 1, p.e⟩ := by
    cases op <;> first | exact absurd rfl hop | simp [Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
  have h2 : Program.RowAssert M (rowInst p ⟨op, .K, args⟩) := by
    cases op <;> first | exact absurd rfl hop | trivial
  simp only [SegsAssert, this, h2, true_and]

theorem segsHold_consA {c : Ctx} {M : Mem} {p : Ptr} {τ : Ty} {args : List Addr} {δ : List Seg} :
    SegsHold c M p (.row ⟨.assert0, τ, args⟩ :: δ) ↔ SegsHold c M p δ := by
  have : p.adv [.row ⟨.assert0, τ, args⟩] = p := by simp [Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
  simp only [SegsHold, this]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

theorem segsAssert_consA {M : Mem} {p : Ptr} {τ : Ty} {args : List Addr} {δ : List Seg} :
    SegsAssert M p (.row ⟨.assert0, τ, args⟩ :: δ) ↔
      M.arg (rowInst p ⟨.assert0, τ, args⟩) 1 * M.arg (rowInst p ⟨.assert0, τ, args⟩) 0 = 0 ∧
        SegsAssert M p δ := by
  have : p.adv [.row ⟨.assert0, τ, args⟩] = p := by simp [Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
  simp only [SegsAssert, this]
  exact Iff.rfl

theorem gpowBitsGo_spec {c : Ctx} {M : Mem} (s : Nat) : ∀ (k na : Nat) (bs : List Cell)
    (p : Ptr), (∀ β ∈ bs, IsBit M β) →
    SegsHold c M p (gpowBits.gpowBitsGo s k (kc na) bs p).2 →
    (gpowBits.gpowBitsGo s k (kc na) bs p).1.ty = .K ∧
      M.k (gpowBits.gpowBitsGo s k (kc na) bs p).1.n = M.k na * gpow (s * 2 ^ k * bitsNat M bs)
  | k, na, [], p, _, _ => by
    refine ⟨rfl, ?_⟩
    show M.k na = M.k na * gpow (s * 2 ^ k * 0)
    rw [Nat.mul_zero, gpow_zero, mul_one]
  | k, na, β :: bs, p, hb, h => by
    obtain ⟨hβ, hβv⟩ := hb β (by simp)
    obtain ⟨nb, rfl⟩ : ∃ n, β = kc n := ⟨β.n, by cases β; simp_all [kc]⟩
    rw [gpowBitsGo_cons] at h ⊢
    simp only [List.cons_append, List.nil_append] at h
    rw [segsHold_consK (by intro h; cases h), segsHold_consK (by intro h; cases h)] at h
    obtain ⟨hu, hacc, hrest⟩ := h
    have hu' : M.k p.k = M.k na + gpow (s * 2 ^ k) * M.k na + 0 := by
      have := (segsHold_row (c := c) (M := M)).mpr hu
      exact linK_spec this
    have hacc' : M.k (p.k + 1) = M.k nb * M.k p.k + M.k na := by
      have := (segsHold_row (c := c) (M := M) (p := ⟨p.k + 1, p.e⟩)).mpr hacc
      exact mulAddK_spec (a := nb) (b := p.k) (d := na) this
    obtain ⟨ih1, ih2⟩ := gpowBitsGo_spec s (k + 1) (p.k + 1) bs _
      (fun β hβ => hb β (by simp [hβ])) hrest
    refine ⟨ih1, ?_⟩
    rw [ih2, hacc', hu', bit_select _ _ _ hβv]
    simp only [bitsNat, kc] at hβv ⊢
    rcases hβv with h0 | h1
    · simp only [h0, show (0 : FK) ≠ 1 from by decide, ite_false, mul_one, Nat.zero_add]
      congr 2; ring
    · simp only [h1, ite_true, mul_assoc, ← gpow_add]
      congr 2; ring

/-- **The address from bits**: with Boolean `K` bit cells (low first), the result is the `K` cell
`g^(lo + s · Σ_k β_k 2^k)` (`x`, a `K` cell, is read only when there is no bit). -/
theorem gpowBits_spec {c : Ctx} {M : Mem} {lo s : Nat} {x : Cell} {bs : List Cell} {p : Ptr}
    (hx : x.ty = .K) (hb : ∀ β ∈ bs, IsBit M β) (h : SegsHold c M p (gpowBits lo s x bs p).2) :
    (gpowBits lo s x bs p).1.ty = .K ∧
      M.k (gpowBits lo s x bs p).1.n = gpow (lo + s * bitsNat M bs) := by
  cases bs with
  | nil =>
    obtain ⟨nx, rfl⟩ : ∃ n, x = kc n := ⟨x.n, by cases x; simp_all [kc]⟩
    refine ⟨rfl, ?_⟩
    have := linK_spec (k := 1) (k' := gpow lo) (a := nx) (b := nx) h
    rw [one_mul, FK.add_self, zero_add] at this
    show M.k p.k = gpow (lo + s * 0)
    rw [Nat.mul_zero, Nat.add_zero]
    exact this
  | cons β₀ bs =>
    obtain ⟨hβ, hβv⟩ := hb β₀ (by simp)
    obtain ⟨nb, rfl⟩ : ∃ n, β₀ = kc n := ⟨β₀.n, by cases β₀; simp_all [kc]⟩
    rw [gpowBits_cons] at h ⊢
    simp only [List.cons_append, List.nil_append] at h
    rw [segsHold_consK (by intro h; cases h)] at h
    obtain ⟨ha, hrest⟩ := h
    have ha' : M.k p.k = M.k nb + (gpow lo * (gpow s + 1) + 1) * M.k nb + gpow lo := by
      have := (segsHold_row (c := c) (M := M)).mpr ha
      exact linK_spec this
    obtain ⟨g1, g2⟩ := gpowBitsGo_spec (c := c) (M := M) s 1 p.k bs _
      (fun β hβ => hb β (by simp [hβ])) hrest
    refine ⟨g1, ?_⟩
    rw [g2, ha']
    simp only [bitsNat, kc] at hβv ⊢
    rcases hβv with h0 | h1
    · simp only [h0, mul_zero, add_zero, zero_add, show (0 : FK) ≠ 1 from by decide, ite_false,
        Nat.zero_add, ← gpow_add]
      congr 1; ring
    · simp only [h1, ite_true, mul_one]
      have e : (1 : FK) + (gpow lo * (gpow s + 1) + 1) + gpow lo =
          gpow lo * gpow s + ((1 + 1) + (gpow lo + gpow lo)) := by ring
      rw [e, FK.add_self, FK.add_self, add_zero, add_zero, ← gpow_add, ← gpow_add]
      congr 1; ring

end Lvm.Loop.Build
