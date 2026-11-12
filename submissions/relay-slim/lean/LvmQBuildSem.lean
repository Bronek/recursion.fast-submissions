-- New for lvm (WP-11b-QL): the semantics of `LvmQBuild`'s gadgets. No earlier formalisation has a
-- program logic for WP-10's LoopIR; FR's `FRVIRCompileSound` (`compile_sound`) is the analogue for
-- its R1CS compiler and served as the model of the statement shape (rows hold ⇒ values are right).
import LvmQBuild
import LvmLoopInterp

/-!
# What a gadget's segments mean: a compositional program logic for LoopIR

`Program.RowDef` reads two things of the whole program: the glue matrix (`fixmul`) and the cell
counts (`readd`). `Ctx` abstracts them, so a gadget's rows can be stated **without the program**:

* `RowRel c M i`: instance `i`'s operation holds in memory `M` (`Program.RowDef` with `Q` replaced
  by `c`; `rowDef_iff`);
* `SegsHold c M p δ`: every row instance of the segments `δ`, placed at pointer `p`, holds;
  `SegsAssert M p δ`: every `assert0` of `δ` holds (`gate · a = 0`).

**Composition and frame.** `segsHold_append`: `δ₁ ++ δ₂` holds at `p` iff `δ₁` holds at `p` and
`δ₂` at `p.adv δ₁`; `hold_bind`/`assert_bind` restate it for `m >>= f`. A gadget's correctness is
stated as `SegsHold c M p (g p).2 → SegsAssert M p (g p).2 → Spec (g p).1 M`: it reads only its
own rows, whatever comes before or after it (the frame property), and it holds in any memory:
the committed one (`loopir_sound`'s `WitnessOf`) or the interpreter's.

**The bridge to programs.** `holds_iff`, `asserts_iff`: `Q.Holds M` (`Q.Asserts M`) iff every
block holds at its start pointer. `toProgram_holds`, `toProgram_asserts`: for `Q = toProgram nK nE
m`, `Q.Holds M ↔ SegsHold (ctxOf Q) M ⟨nK, nE⟩ (m ⟨nK, nE⟩).2`, and likewise `Asserts`.
`toProgram_interp`: with the program check, `inb` and `GInj`, the interpreter's memory holds every
segment, and `ok = true` iff every assertion holds in it. `segsOk_wf`: the one-pass check
`segsOk` implies `Q.wf` (for `decide` on concrete programs).

**Primitives.** `mulAdd_spec`, `lin_spec`, `loadE_spec`, `readd_spec`, `add_spec`, `addK_spec`,
`scale_spec`, `const_spec`, `copy_spec`, `assert0_spec`, `assertEq_spec`, `assertEqK_spec`;
`gpowBits_spec` (the address from bits); `loop_rel` (a loop row at an iteration, its operands
resolved), `prologue_spec`.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-! ## The context a row relation reads -/

/-- What `RowDef` reads of the program: the glue matrix and the cell counts. -/
structure Ctx where
  /-- The glue matrix (`fixmul`'s multiplier at a loop index). -/
  fm : List Nat → FK
  /-- The cell counts (`readd` finds its cell below them). -/
  cells : Ty → Nat

/-- The context of a program. -/
def ctxOf (Q : Program) : Ctx := ⟨Q.fixMat, Q.cells⟩

/-- **The relation of an instance** in context `c` (`Program.RowDef`). -/
def RowRel (c : Ctx) (M : Mem) (i : Inst) : Prop :=
  match i.row.op with
  | .muladd => M.res i = M.arg i 0 * M.arg i 1 + M.arg i 2
  | .lin k k' => M.res i = M.arg i 0 + FE.ofK k * M.arg i 1 + FE.ofK k'
  | .assert0 => True
  | .loadE => M.res i = M.arg i 0 + FE.y * M.arg i 1 + FE.y * FE.y * M.arg i 2
  | .fixmul => M.res i = FE.ofK (c.fm i.j) * M.arg i 0 + M.arg i 1
  | .readd _ _ => ∃ e < c.cells i.row.ty, FK.x ^ e = (M.arg i 0).c₀ ∧ M.res i = M.rd i.row.ty e

theorem rowDef_iff (Q : Program) (M : Mem) (i : Inst) : Q.RowDef M i ↔ RowRel (ctxOf Q) M i := by
  unfold Program.RowDef RowRel
  rcases i.row.op <;> exact Iff.rfl

/-- The value of a cell in a memory. -/
def Cell.val (M : Mem) (c : Cell) : FE := M.rd c.ty c.n

@[simp] theorem Cell.val_K (M : Mem) (n : Nat) : (kc n).val M = FE.ofK (M.k n) := rfl
@[simp] theorem Cell.val_E (M : Mem) (n : Nat) : (ec n).val M = M.e n := rfl

/-! ## Segments at a pointer -/

/-- The instance of block `B` at pointer `p`, flat index `jf`, template row `t` (the fields
`RowRel` does not read are `0`). -/
def instAt (p : Ptr) (B : Block) (jf t : Nat) : Inst :=
  ⟨0, 0, unflat B.dims jf, 0, B.tpl.getD t default, p.k + B.tw .K * jf + B.rank .K t,
    p.e + B.tw .E * jf + B.rank .E t⟩

/-- The instance of a straight-line row at pointer `p`. -/
def rowInst (p : Ptr) (r : Row) : Inst := ⟨0, 0, [], 0, r, p.k, p.e⟩

/-- Every instance of block `B` at `p` holds. -/
def BlockHolds (c : Ctx) (M : Mem) (p : Ptr) (B : Block) : Prop :=
  ∀ jf < B.size, ∀ t < B.tpl.length, RowRel c M (instAt p B jf t)

/-- Every assertion of block `B` at `p` holds. -/
def BlockAsserts (M : Mem) (p : Ptr) (B : Block) : Prop :=
  ∀ jf < B.size, ∀ t < B.tpl.length, Program.RowAssert M (instAt p B jf t)

/-- **The segments `δ` at `p` hold in `M`.** -/
def SegsHold (c : Ctx) (M : Mem) : Ptr → List Seg → Prop
  | _, [] => True
  | p, .row r :: δ => RowRel c M (rowInst p r) ∧ SegsHold c M (p.adv [.row r]) δ
  | p, .blk B :: δ => BlockHolds c M p B ∧ SegsHold c M (p.adv [.blk B]) δ

/-- **Every assertion of the segments `δ` at `p` holds in `M`.** -/
def SegsAssert (M : Mem) : Ptr → List Seg → Prop
  | _, [] => True
  | p, .row r :: δ => Program.RowAssert M (rowInst p r) ∧ SegsAssert M (p.adv [.row r]) δ
  | p, .blk B :: δ => BlockAsserts M p B ∧ SegsAssert M (p.adv [.blk B]) δ

theorem segsW_append (τ : Ty) (δ₁ δ₂ : List Seg) : segsW τ (δ₁ ++ δ₂) = segsW τ δ₁ + segsW τ δ₂ := by
  simp [segsW]

theorem segsW_cons (τ : Ty) (s : Seg) (δ : List Seg) : segsW τ (s :: δ) = s.w τ + segsW τ δ := by
  simp [segsW]

@[simp] theorem Ptr.adv_nil (p : Ptr) : p.adv [] = p := by simp [Ptr.adv, segsW]

theorem Ptr.adv_append (p : Ptr) (δ₁ δ₂ : List Seg) : p.adv (δ₁ ++ δ₂) = (p.adv δ₁).adv δ₂ := by
  simp only [Ptr.adv, segsW_append, Nat.add_assoc]

theorem Ptr.adv_cons (p : Ptr) (s : Seg) (δ : List Seg) : p.adv (s :: δ) = (p.adv [s]).adv δ := by
  rw [← Ptr.adv_append]; rfl

/-- **Composition (and frame)**: the segments of two gadgets hold iff each holds at its pointer. -/
theorem segsHold_append (c : Ctx) (M : Mem) : ∀ (p : Ptr) (δ₁ δ₂ : List Seg),
    SegsHold c M p (δ₁ ++ δ₂) ↔ SegsHold c M p δ₁ ∧ SegsHold c M (p.adv δ₁) δ₂
  | p, [], δ₂ => by simp [SegsHold]
  | p, .row r :: δ₁, δ₂ => by
    simp only [List.cons_append, SegsHold]
    rw [segsHold_append c M _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]
  | p, .blk B :: δ₁, δ₂ => by
    simp only [List.cons_append, SegsHold]
    rw [segsHold_append c M _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]

theorem segsAssert_append (M : Mem) : ∀ (p : Ptr) (δ₁ δ₂ : List Seg),
    SegsAssert M p (δ₁ ++ δ₂) ↔ SegsAssert M p δ₁ ∧ SegsAssert M (p.adv δ₁) δ₂
  | p, [], δ₂ => by simp [SegsAssert]
  | p, .row r :: δ₁, δ₂ => by
    simp only [List.cons_append, SegsAssert]
    rw [segsAssert_append M _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]
  | p, .blk B :: δ₁, δ₂ => by
    simp only [List.cons_append, SegsAssert]
    rw [segsAssert_append M _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]

/-! ## The monad -/

theorem bind_apply {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    (m >>= f) p = ((f (m p).1 (p.adv (m p).2)).1, (m p).2 ++ (f (m p).1 (p.adv (m p).2)).2) := rfl

theorem pure_apply {α : Type} (x : α) (p : Ptr) : (pure x : BM α) p = (x, []) := rfl

/-- **Sequencing**: `m >>= f` holds iff `m` holds and `f` (on `m`'s output) holds after it. -/
theorem hold_bind {α β : Type} (c : Ctx) (M : Mem) (m : BM α) (f : α → BM β) (p : Ptr) :
    SegsHold c M p ((m >>= f) p).2 ↔
      SegsHold c M p (m p).2 ∧ SegsHold c M (p.adv (m p).2) (f (m p).1 (p.adv (m p).2)).2 := by
  rw [bind_apply]; exact segsHold_append c M _ _ _

theorem assert_bind {α β : Type} (M : Mem) (m : BM α) (f : α → BM β) (p : Ptr) :
    SegsAssert M p ((m >>= f) p).2 ↔
      SegsAssert M p (m p).2 ∧ SegsAssert M (p.adv (m p).2) (f (m p).1 (p.adv (m p).2)).2 := by
  rw [bind_apply]; exact segsAssert_append M _ _ _

/-! ## Blocks of a program -/

/-- The pointer after the blocks `bs`. -/
def Ptr.advBs (p : Ptr) (bs : List Block) : Ptr :=
  ⟨p.k + (bs.map fun B => B.tw .K * B.size).sum, p.e + (bs.map fun B => B.tw .E * B.size).sum⟩

/-- Every block of `bs` holds at its pointer. -/
def BlocksHold (c : Ctx) (M : Mem) : Ptr → List Block → Prop
  | _, [] => True
  | p, B :: bs => BlockHolds c M p B ∧ BlocksHold c M (p.advBs [B]) bs

/-- Every assertion of every block of `bs`. -/
def BlocksAssert (M : Mem) : Ptr → List Block → Prop
  | _, [] => True
  | p, B :: bs => BlockAsserts M p B ∧ BlocksAssert M (p.advBs [B]) bs

theorem Ptr.advBs_cons (p : Ptr) (B : Block) (bs : List Block) :
    p.advBs (B :: bs) = (p.advBs [B]).advBs bs := by
  simp [Ptr.advBs, Nat.add_assoc]

theorem blocksHold_iff (c : Ctx) (M : Mem) : ∀ (p : Ptr) (bs : List Block),
    BlocksHold c M p bs ↔ ∀ b < bs.length, BlockHolds c M (p.advBs (bs.take b)) (bs.getD b default)
  | p, [] => by simp [BlocksHold]
  | p, B :: bs => by
    simp only [BlocksHold, blocksHold_iff c M _ bs, List.length_cons]
    constructor
    · rintro ⟨h0, h⟩ b hb
      rcases b with _ | b
      · simpa [Ptr.advBs] using h0
      · have := h b (by omega)
        simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this
    · intro h
      refine ⟨by simpa [Ptr.advBs] using h 0 (by omega), fun b hb => ?_⟩
      have := h (b + 1) (by omega)
      simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this

theorem blocksAssert_iff (M : Mem) : ∀ (p : Ptr) (bs : List Block),
    BlocksAssert M p bs ↔ ∀ b < bs.length, BlockAsserts M (p.advBs (bs.take b)) (bs.getD b default)
  | p, [] => by simp [BlocksAssert]
  | p, B :: bs => by
    simp only [BlocksAssert, blocksAssert_iff M _ bs, List.length_cons]
    constructor
    · rintro ⟨h0, h⟩ b hb
      rcases b with _ | b
      · simpa [Ptr.advBs] using h0
      · have := h b (by omega)
        simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this
    · intro h
      refine ⟨by simpa [Ptr.advBs] using h 0 (by omega), fun b hb => ?_⟩
      have := h (b + 1) (by omega)
      simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this

theorem start_ptr (Q : Program) (b : Nat) :
    (⟨Q.start .K b, Q.start .E b⟩ : Ptr) = (⟨Q.nInK, Q.nInE⟩ : Ptr).advBs (Q.blocks.take b) := rfl

/-- `RowRel` does not read an instance's block, flat index or template-row fields. -/
theorem rowRel_inst (c : Ctx) (M : Mem) (Q : Program) (b jf t : Nat) :
    RowRel c M (Q.inst b jf t) ↔
      RowRel c M (instAt ⟨Q.start .K b, Q.start .E b⟩ (Q.blk b) jf t) := Iff.rfl

theorem rowAssert_inst (M : Mem) (Q : Program) (b jf t : Nat) :
    Program.RowAssert M (Q.inst b jf t) ↔
      Program.RowAssert M (instAt ⟨Q.start .K b, Q.start .E b⟩ (Q.blk b) jf t) := Iff.rfl

/-- **`Holds` block by block**: every block holds at its start pointer. -/
theorem holds_iff (Q : Program) (M : Mem) :
    Q.Holds M ↔ BlocksHold (ctxOf Q) M ⟨Q.nInK, Q.nInE⟩ Q.blocks := by
  rw [blocksHold_iff]
  constructor
  · intro h b hb jf hjf t ht
    have hi := (Q.mem_insts (Q.inst b jf t)).mpr ⟨b, hb, jf, by simpa [Program.blk] using hjf, t,
      by simpa [Program.blk] using ht, rfl⟩
    have := (rowDef_iff Q M _).mp (h _ hi)
    simpa [rowRel_inst, start_ptr, Program.blk] using this
  · intro h i hi
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
    rw [rowDef_iff, rowRel_inst, start_ptr]
    exact h b hb jf (by simpa [Program.blk] using hjf) t (by simpa [Program.blk] using ht)

/-- **`Asserts` block by block.** -/
theorem asserts_iff (Q : Program) (M : Mem) :
    Q.Asserts M ↔ BlocksAssert M ⟨Q.nInK, Q.nInE⟩ Q.blocks := by
  rw [blocksAssert_iff]
  constructor
  · intro h b hb jf hjf t ht
    have hi := (Q.mem_insts (Q.inst b jf t)).mpr ⟨b, hb, jf, by simpa [Program.blk] using hjf, t,
      by simpa [Program.blk] using ht, rfl⟩
    simpa [rowAssert_inst, start_ptr, Program.blk] using h _ hi
  · intro h i hi
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
    rw [rowAssert_inst, start_ptr]
    exact h b hb jf (by simpa [Program.blk] using hjf) t (by simpa [Program.blk] using ht)

/-! ## Grouping segments into blocks -/

/-- A run of rows as a glue block (none when empty). -/
def glueB (rs : List Row) (bs : List Block) : List Block :=
  if rs.isEmpty then bs else ⟨[], rs⟩ :: bs

theorem group_eq (δ : List Seg) : group δ = glueB (groupAux δ).1 (groupAux δ).2 := rfl

theorem groupAux_blk (B : Block) (δ : List Seg) :
    groupAux (.blk B :: δ) = ([], B :: glueB (groupAux δ).1 (groupAux δ).2) := rfl

theorem groupAux_row (r : Row) (δ : List Seg) :
    groupAux (.row r :: δ) =
      if decide (glueCap ≤ (groupAux δ).1.length) then
        ([r], glueB (groupAux δ).1 (groupAux δ).2)
      else (r :: (groupAux δ).1, (groupAux δ).2) := rfl

theorem rank_glue_succ (r : Row) (rs : List Row) (τ : Ty) (t : Nat) :
    Block.rank ⟨[], r :: rs⟩ τ (t + 1) = r.w τ + Block.rank ⟨[], rs⟩ τ t := by
  simp [Block.rank, List.take_succ_cons]

theorem advBs_glue (p : Ptr) (rs : List Row) : p.advBs [⟨[], rs⟩] = p.adv (rs.map .row) := by
  simp only [Ptr.advBs, Ptr.adv, segsW, Block.tw, Block.size, Block.lsize, List.sum_nil, pow_zero,
    Nat.mul_one, List.map_cons, List.map_nil, List.sum_cons, Nat.add_zero, List.map_map]
  rfl

theorem instAt_glue_zero (p : Ptr) (r : Row) (rs : List Row) :
    instAt p ⟨[], r :: rs⟩ 0 0 = rowInst p r := by
  simp [instAt, rowInst, Block.rank, unflat]

theorem instAt_glue_succ (p : Ptr) (r : Row) (rs : List Row) (t : Nat) :
    instAt p ⟨[], r :: rs⟩ 0 (t + 1) = instAt (p.adv [.row r]) ⟨[], rs⟩ 0 t := by
  simp only [instAt, rank_glue_succ, Ptr.adv, segsW, Seg.w, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.mul_zero, List.getD_cons_succ, unflat]
  congr 1 <;> omega

/-- A glue block holds iff its rows, as straight-line segments, do. -/
theorem glue_iff (c : Ctx) (M : Mem) : ∀ (p : Ptr) (rs : List Row),
    BlockHolds c M p ⟨[], rs⟩ ↔ SegsHold c M p (rs.map .row)
  | p, [] => by simp [BlockHolds, SegsHold]
  | p, r :: rs => by
    have ih := glue_iff c M (p.adv [.row r]) rs
    simp only [List.map_cons, SegsHold, ← ih, BlockHolds, Block.size, Block.lsize, List.sum_nil,
      pow_zero, Nat.lt_one_iff, forall_eq, List.length_cons]
    constructor
    · intro h
      refine ⟨by simpa [instAt_glue_zero] using h 0 (by omega), fun t ht => ?_⟩
      have := h (t + 1) (by omega)
      rwa [instAt_glue_succ] at this
    · rintro ⟨h0, h⟩ t ht
      rcases t with _ | t
      · rw [instAt_glue_zero]; exact h0
      · rw [instAt_glue_succ]; exact h t (by omega)

theorem glueA_iff (M : Mem) : ∀ (p : Ptr) (rs : List Row),
    BlockAsserts M p ⟨[], rs⟩ ↔ SegsAssert M p (rs.map .row)
  | p, [] => by simp [BlockAsserts, SegsAssert]
  | p, r :: rs => by
    have ih := glueA_iff M (p.adv [.row r]) rs
    simp only [List.map_cons, SegsAssert, ← ih, BlockAsserts, Block.size, Block.lsize, List.sum_nil,
      pow_zero, Nat.lt_one_iff, forall_eq, List.length_cons]
    constructor
    · intro h
      refine ⟨by simpa [instAt_glue_zero] using h 0 (by omega), fun t ht => ?_⟩
      have := h (t + 1) (by omega)
      rwa [instAt_glue_succ] at this
    · rintro ⟨h0, h⟩ t ht
      rcases t with _ | t
      · rw [instAt_glue_zero]; exact h0
      · rw [instAt_glue_succ]; exact h t (by omega)

theorem blocksHold_glueB (c : Ctx) (M : Mem) (p : Ptr) (rs : List Row) (bs : List Block) :
    BlocksHold c M p (glueB rs bs) ↔
      SegsHold c M p (rs.map .row) ∧ BlocksHold c M (p.adv (rs.map .row)) bs := by
  unfold glueB
  rcases rs with _ | ⟨r, rs⟩
  · simp [SegsHold]
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, BlocksHold, glue_iff, advBs_glue]

theorem blocksAssert_glueB (M : Mem) (p : Ptr) (rs : List Row) (bs : List Block) :
    BlocksAssert M p (glueB rs bs) ↔
      SegsAssert M p (rs.map .row) ∧ BlocksAssert M (p.adv (rs.map .row)) bs := by
  unfold glueB
  rcases rs with _ | ⟨r, rs⟩
  · simp [SegsAssert]
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, BlocksAssert, glueA_iff, advBs_glue]

theorem advBs_blk (p : Ptr) (B : Block) : p.advBs [B] = p.adv [.blk B] := by
  simp [Ptr.advBs, Ptr.adv, segsW, Seg.w]

theorem groupAux_hold (c : Ctx) (M : Mem) : ∀ (p : Ptr) (δ : List Seg),
    SegsHold c M p δ ↔ SegsHold c M p ((groupAux δ).1.map .row) ∧
      BlocksHold c M (p.adv ((groupAux δ).1.map .row)) (groupAux δ).2
  | p, [] => by simp [SegsHold, BlocksHold, groupAux]
  | p, .row r :: δ => by
    rw [groupAux_row]
    split
    · simp only [SegsHold, List.map_cons, List.map_nil, and_true]
      rw [groupAux_hold c M _ δ, blocksHold_glueB]
    · simp only [SegsHold, List.map_cons]
      rw [groupAux_hold c M _ δ, Ptr.adv_cons p (.row r) ((groupAux δ).1.map .row), and_assoc]
  | p, .blk B :: δ => by
    rw [groupAux_blk]
    simp only [SegsHold, List.map_nil, Ptr.adv_nil, BlocksHold, true_and]
    rw [groupAux_hold c M _ δ, blocksHold_glueB, advBs_blk]

theorem groupAux_assert (M : Mem) : ∀ (p : Ptr) (δ : List Seg),
    SegsAssert M p δ ↔ SegsAssert M p ((groupAux δ).1.map .row) ∧
      BlocksAssert M (p.adv ((groupAux δ).1.map .row)) (groupAux δ).2
  | p, [] => by simp [SegsAssert, BlocksAssert, groupAux]
  | p, .row r :: δ => by
    rw [groupAux_row]
    split
    · simp only [SegsAssert, List.map_cons, List.map_nil, and_true]
      rw [groupAux_assert M _ δ, blocksAssert_glueB]
    · simp only [SegsAssert, List.map_cons]
      rw [groupAux_assert M _ δ, Ptr.adv_cons p (.row r) ((groupAux δ).1.map .row), and_assoc]
  | p, .blk B :: δ => by
    rw [groupAux_blk]
    simp only [SegsAssert, List.map_nil, Ptr.adv_nil, BlocksAssert, true_and]
    rw [groupAux_assert M _ δ, blocksAssert_glueB, advBs_blk]

/-- **Grouping keeps the meaning**: the blocks of `δ` hold iff its segments do. -/
theorem group_hold (c : Ctx) (M : Mem) (p : Ptr) (δ : List Seg) :
    BlocksHold c M p (group δ) ↔ SegsHold c M p δ := by
  rw [group_eq, blocksHold_glueB, groupAux_hold c M p δ]

theorem group_assert (M : Mem) (p : Ptr) (δ : List Seg) :
    BlocksAssert M p (group δ) ↔ SegsAssert M p δ := by
  rw [group_eq, blocksAssert_glueB, groupAux_assert M p δ]

/-! ## Programs from gadgets -/

/-- **The program of a gadget holds iff the gadget's segments do.** -/
theorem toProgram_holds {α : Type} (nK nE : Nat) (m : BM α) (M : Mem) :
    (toProgram nK nE m).Holds M ↔ SegsHold (ctxOf (toProgram nK nE m)) M ⟨nK, nE⟩ (m ⟨nK, nE⟩).2 := by
  rw [holds_iff]; exact group_hold _ M _ _

theorem toProgram_asserts {α : Type} (nK nE : Nat) (m : BM α) (M : Mem) :
    (toProgram nK nE m).Asserts M ↔ SegsAssert M ⟨nK, nE⟩ (m ⟨nK, nE⟩).2 := by
  rw [asserts_iff]; exact group_assert M _ _

/-- **The interpreter on a gadget's program**: with the program check, `inb` and `GInj`, its
memory holds every segment, and `ok` is "every assertion holds in it". -/
theorem interp_segs (Q : Program) (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (hinj : GInj (max (Q.cells .K) (Q.cells .E)))
    (hinb : (Q.interp inK inE).inb = true) :
    BlocksHold (ctxOf Q) (Q.interpMem inK inE) ⟨Q.nInK, Q.nInE⟩ Q.blocks ∧
      ((Q.interp inK inE).ok = true ↔ BlocksAssert (Q.interpMem inK inE) ⟨Q.nInK, Q.nInE⟩ Q.blocks) ∧
      Q.Inputs (Q.interpMem inK inE) inK inE := by
  obtain ⟨hH, hI⟩ := Q.interp_holds hwf inK inE hsz hinb
  obtain ⟨-, hok⟩ := Q.interp_unique hwf inK inE hsz _ hI hH hinj hinb
  exact ⟨(holds_iff Q _).mp hH, by rw [hok, asserts_iff], hI⟩

theorem toProgram_interp {α : Type} (nK nE : Nat) (m : BM α)
    (hwf : (toProgram nK nE m).wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = nK ∧ inE.size = nE)
    (hinj : GInj (max ((toProgram nK nE m).cells .K) ((toProgram nK nE m).cells .E)))
    (hinb : ((toProgram nK nE m).interp inK inE).inb = true) :
    SegsHold (ctxOf (toProgram nK nE m)) ((toProgram nK nE m).interpMem inK inE) ⟨nK, nE⟩
        (m ⟨nK, nE⟩).2 ∧
      (((toProgram nK nE m).interp inK inE).ok = true ↔
        SegsAssert ((toProgram nK nE m).interpMem inK inE) ⟨nK, nE⟩ (m ⟨nK, nE⟩).2) ∧
      (toProgram nK nE m).Inputs ((toProgram nK nE m).interpMem inK inE) inK inE := by
  obtain ⟨h1, h2, h3⟩ := interp_segs _ hwf inK inE hsz hinj hinb
  exact ⟨group_hold _ _ _ _ |>.mp h1, by rw [h2]; exact group_assert _ _ _, h3⟩

end Lvm.Loop.Build
