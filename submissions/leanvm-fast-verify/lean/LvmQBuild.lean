-- New for lvm (WP-11b-QL). Searched for a reusable builder: FR's `FRVIRCompile` (an R1CS compiler of
-- a register IR with linear-form slots) and FR's node layout modules target a different circuit
-- language; leanerVM has no LoopIR. Nothing fits WP-10's dense-allocation LoopIR, so this is new.
import LvmLoopIR

/-!
# A builder for LoopIR programs (`Lvm.Loop.Build`)

WP-10's LoopIR (`LvmLoopIR`) allocates results densely: the cells a row writes are fixed by the
rows before it. Writing a program by hand means tracking two allocation pointers (`K` and `E`
cells) across blocks. This module does the bookkeeping.

* **`BM α`**: a gadget. Given the allocation pointer `p : Ptr` (the next free `K` and `E` cells)
  it returns its outputs and the *segments* it emits, in order. The pointer after a gadget is
  *computed* from its segments (`Ptr.adv`), so it cannot drift: `bind` runs the continuation at
  `p.adv δ` where `δ` are the first gadget's segments.
* **Segments.** `Seg.row r`: one straight-line row (it goes into the current *glue* block, a block
  with no loop dimension); `Seg.blk B`: a loop block. `group` merges consecutive rows into one glue
  block; `toProgram` makes the `Program`.
* **Cells.** `Cell` = memory and exponent. Straight-line primitives return the cell they write:
  `mulAdd`, `lin`, `loadE`, `readd`, `fixmul`; `assert0 a gate` asserts `gate · a = 0`. Derived:
  `add`, `addK` (a constant), `scale`, `const`, `copy`, `assertEq`, `assertEqK`.
* **Loops** (`loop dims tpl`). A template row's operands are `Opd.abs a` (an affine address,
  WP-10's `Addr`), `Opd.cur t` (row `t`'s result in this iteration) or `Opd.prev t` (row `t`'s
  result in the previous iteration, flat order; at iteration 0 the *prologue*). `loopP dims tpl
  init` first emits the prologue: one copy row per writing template row, from `init t`, in the
  template's write order, so the loop's `prev` reads at iteration 0 land on it. `LoopOut.cell t jf`
  names row `t`'s result at flat iteration `jf`; `LoopOut.addr t` is its affine address for a
  later loop over the same dimensions.
* **Computed addresses** (`gpowBits lo s bits`): the `K` cell `g^(lo + s · Σ_k β_k 2^k)` from bit
  cells `β_k`, for `readd` (WP-10 design point 5): `2·|bits| − 1` rows.

The semantics (what a gadget's segments mean in a memory, composition and the bridge to
`Program.Holds`/`Asserts`/`interp`) is in `LvmQBuildSem`. Nothing here imports Mathlib.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-! ## Cells, pointers, segments -/

/-- A cell: its memory and its exponent (the bus address is `g^n`). -/
structure Cell where
  /-- The memory. -/
  ty : Ty
  /-- The exponent. -/
  n : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The fixed operand naming a cell. -/
def Cell.addr (c : Cell) : Addr := ⟨c.ty, c.n, []⟩

/-- A `K` cell. -/
abbrev kc (n : Nat) : Cell := ⟨.K, n⟩
/-- An `E` cell. -/
abbrev ec (n : Nat) : Cell := ⟨.E, n⟩

/-- The allocation pointer: the next free cell of each memory. -/
structure Ptr where
  /-- The next free `K` cell. -/
  k : Nat
  /-- The next free `E` cell. -/
  e : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The pointer of memory `τ`. -/
def Ptr.at (p : Ptr) : Ty → Nat
  | .K => p.k
  | .E => p.e

/-- What a gadget emits. -/
inductive Seg where
  /-- One straight-line row, appended to the current glue block. -/
  | row (r : Row)
  /-- A loop block. -/
  | blk (B : Block)
  deriving Repr

/-- The cells of memory `τ` a segment writes. -/
def Seg.w (τ : Ty) : Seg → Nat
  | .row r => r.w τ
  | .blk B => B.tw τ * B.size

/-- The cells of memory `τ` the segments write. -/
def segsW (τ : Ty) (δ : List Seg) : Nat := (δ.map (Seg.w τ)).sum

/-- The pointer after the segments `δ`. -/
def Ptr.adv (p : Ptr) (δ : List Seg) : Ptr := ⟨p.k + segsW .K δ, p.e + segsW .E δ⟩

/-! ## The builder monad -/

/-- **A gadget**: from the allocation pointer, its outputs and the segments it emits. -/
def BM (α : Type) : Type := Ptr → α × List Seg

/-- Run `m`, then `f` on its output at the advanced pointer; the segments are concatenated. -/
@[inline] def BM.bind {α β : Type} (m : BM α) (f : α → BM β) : BM β := fun p =>
  let r := m p
  let r' := f r.1 (p.adv r.2)
  (r'.1, r.2 ++ r'.2)

instance : Monad BM where
  pure x := fun _ => (x, [])
  bind := BM.bind

/-- The current pointer. -/
def getPtr : BM Ptr := fun p => (p, [])

/-- Emit a row with no result. -/
def emit (r : Row) : BM Unit := fun _ => ((), [.row r])

/-- Emit a row writing memory `τ`; its result is the cell at the pointer. -/
def rowRes (τ : Ty) (r : Row) : BM Cell := fun p => (⟨τ, p.at τ⟩, [.row r])

/-- Emit a loop block as it is. -/
def emitBlk (B : Block) : BM Unit := fun _ => ((), [.blk B])

/-- Run a list of gadgets in order, collecting their outputs. -/
def seqAll {α : Type} : List (BM α) → BM (List α)
  | [] => pure []
  | m :: ms => do
    let x ← m
    let xs ← seqAll ms
    pure (x :: xs)

/-- `f 0, …, f (n − 1)` in order. -/
def forN {α : Type} (n : Nat) (f : Nat → BM α) : BM (List α) := seqAll ((List.range n).map f)

/-! ## Straight-line primitives (WP-10's operations) -/

/-- The memory of a result computed from operands of memories `a`, `b`: `E` if either is. -/
def jn : Ty → Ty → Ty
  | .K, .K => .K
  | _, _ => .E

/-- `c = a·b + d` in memory `τ` (`K` rows need `K` operands). -/
def mulAdd (τ : Ty) (a b d : Cell) : BM Cell := rowRes τ ⟨.muladd, τ, [a.addr, b.addr, d.addr]⟩

/-- `c = a + k·b + k'` in memory `τ`. -/
def lin (τ : Ty) (k k' : FK) (a b : Cell) : BM Cell := rowRes τ ⟨.lin k k', τ, [a.addr, b.addr]⟩

/-- Assert `gate · a = 0` (`gate` a `K` cell, normally the node flag). -/
def assert0 (a gate : Cell) : BM Unit := emit ⟨.assert0, .K, [a.addr, gate.addr]⟩

/-- `c = a₀ + y·a₁ + y²·a₂` (an `E` cell from three `K` cells). -/
def loadE (a₀ a₁ a₂ : Cell) : BM Cell := rowRes .E ⟨.loadE, .E, [a₀.addr, a₁.addr, a₂.addr]⟩

/-- `c = mem_τ[α]`: the cell of memory `τ` whose address `g^e` is the value of the `K` cell `α`,
searched in `[lo, lo + 2^m)` by the interpreter. -/
def readd (τ : Ty) (lo m : Nat) (α : Cell) : BM Cell := rowRes τ ⟨.readd lo m, τ, [α.addr]⟩

/-- `c = F·a + d`, `F` the glue matrix at the (empty) loop index. -/
def fixmul (τ : Ty) (a d : Cell) : BM Cell := rowRes τ ⟨.fixmul, τ, [a.addr, d.addr]⟩

/-- `a·b + d`, the result's memory the join of the operands'. -/
def mad (a b d : Cell) : BM Cell := mulAdd (jn (jn a.ty b.ty) d.ty) a b d

/-- `a + b`. -/
def add (a b : Cell) : BM Cell := lin (jn a.ty b.ty) 1 0 a b

/-- `a + k'` for a constant `k'`. -/
def addK (a : Cell) (k' : FK) : BM Cell := lin a.ty 0 k' a a

/-- `k · a` for a constant `k` (`a + (k + 1)·a`, characteristic 2). -/
def scale (k : FK) (a : Cell) : BM Cell := lin a.ty (k + 1) 0 a a

/-- The constant `k'` in memory `τ`, from any cell `x` of a memory `τ` may read (`x + x + k'`). -/
def const (τ : Ty) (k' : FK) (x : Cell) : BM Cell := lin τ 1 k' x x

/-- A copy of `a` (`a + 0·a + 0`). -/
def copy (a : Cell) : BM Cell := lin a.ty 0 0 a a

/-- Assert `gate · (a + b) = 0`: `a = b` when the gate is on. -/
def assertEq (a b gate : Cell) : BM Unit := do
  let d ← add a b
  assert0 d gate

/-- Assert `gate · (a + k') = 0`: `a = k'` when the gate is on. -/
def assertEqK (a : Cell) (k' : FK) (gate : Cell) : BM Unit := do
  let d ← addK a k'
  assert0 d gate

/-! ## Computed addresses from bits (for `readd`) -/

/-- `g^e` as a `K` constant. -/
def gpow (e : Nat) : FK := FK.x ^ e

/-- The address `g^(lo + s · Σ_k β_k 2^k)` from bit cells `β_0, β_1, …` (low first; each `0` or
`1`). One `lin` for the first bit (`g^lo + β₀·g^lo(g^s + 1)`), then per bit `u = (g^(s 2^k) + 1)·acc`
and `acc' = β_k·u + acc`. With no bits: the constant `g^lo` from `x`. -/
def gpowBits (lo s : Nat) (x : Cell) : List Cell → BM Cell
  | [] => const .K (gpow lo) x
  | β₀ :: bs => do
    -- lin c = a + k·b + k' with a = b = β₀: (1 + k)·β₀ + k'
    let a₀ ← lin .K (gpow lo * (gpow s + 1) + 1) (gpow lo) β₀ β₀
    gpowBitsGo s 1 a₀ bs
where
  /-- The remaining bits, bit `k` weighing `2^k`. -/
  gpowBitsGo (s k : Nat) (acc : Cell) : List Cell → BM Cell
    | [] => pure acc
    | β :: bs => do
      let u ← lin .K (gpow (s * 2 ^ k)) 0 acc acc
      let acc' ← mulAdd .K β u acc
      gpowBitsGo s (k + 1) acc' bs

/-! ## Loops -/

/-- A template operand. -/
inductive Opd where
  /-- An affine address (WP-10's `Addr`: base and per-dimension strides). -/
  | abs (a : Addr)
  /-- Template row `t`'s result in this iteration (`t` before the reading row). -/
  | cur (t : Nat)
  /-- Template row `t`'s result in the previous iteration (flat order; the prologue at 0). -/
  | prev (t : Nat)
  deriving Repr, Inhabited

/-- A cell as a loop-invariant operand. -/
def Cell.opd (c : Cell) : Opd := .abs c.addr

/-- A template row with symbolic operands. -/
structure LRow where
  /-- The operation. -/
  op : Op
  /-- The result memory. -/
  ty : Ty
  /-- The operands. -/
  args : List Opd
  deriving Repr

instance : Inhabited LRow := ⟨⟨.assert0, .K, []⟩⟩

/-- The row's write of memory `τ` (as `Row.w`). -/
def LRow.w (τ : Ty) (r : LRow) : Nat := Row.w τ ⟨r.op, r.ty, []⟩

/-- Template rows writing memory `τ`. -/
def ltw (τ : Ty) (tpl : List LRow) : Nat := (tpl.map (LRow.w τ)).sum

/-- Template rows before row `t` writing memory `τ`. -/
def lrank (τ : Ty) (tpl : List LRow) (t : Nat) : Nat := ((tpl.take t).map (LRow.w τ)).sum

/-- The strides of a flat index scaled by `w`: `w`, `w·2^D₀`, `w·2^(D₀+D₁)`, … -/
def scaledStrides : List Nat → Nat → List Nat
  | [], _ => []
  | d :: ds, w => w :: scaledStrides ds (w * 2 ^ d)

/-- The address of template row `t`'s results in a loop at `p` (`cur t`). -/
def curAddr (p : Ptr) (dims : List Nat) (tpl : List LRow) (t : Nat) : Addr :=
  let τ := (tpl.getD t default).ty
  ⟨τ, p.at τ + lrank τ tpl t, scaledStrides dims (ltw τ tpl)⟩

/-- An operand resolved for a loop at `p`. -/
def Opd.resolve (p : Ptr) (dims : List Nat) (tpl : List LRow) : Opd → Addr
  | .abs a => a
  | .cur t => curAddr p dims tpl t
  | .prev t =>
    let a := curAddr p dims tpl t
    { a with base := a.base - ltw a.ty tpl }

/-- The loop block at `p`. -/
def mkLoop (p : Ptr) (dims : List Nat) (tpl : List LRow) : Block :=
  ⟨dims, tpl.map fun r => ⟨r.op, r.ty, r.args.map (Opd.resolve p dims tpl)⟩⟩

/-- A loop's results: row `t`'s at flat iteration `jf` is `cell t jf`. -/
structure LoopOut where
  /-- The pointer at the loop's first cell. -/
  p : Ptr
  /-- The loop dimensions. -/
  dims : List Nat
  /-- The template. -/
  tpl : List LRow

/-- Row `t`'s result at flat iteration `jf`. -/
def LoopOut.cell (o : LoopOut) (t jf : Nat) : Cell :=
  let τ := (o.tpl.getD t default).ty
  ⟨τ, o.p.at τ + lrank τ o.tpl t + ltw τ o.tpl * jf⟩

/-- Row `t`'s results as an affine operand (for a later loop over the same dimensions). -/
def LoopOut.addr (o : LoopOut) (t : Nat) : Addr := curAddr o.p o.dims o.tpl t

/-- **A loop block** of dimensions `dims` (log sizes, dimension 0 fastest). -/
def loop (dims : List Nat) (tpl : List LRow) : BM LoopOut := fun p =>
  (⟨p, dims, tpl⟩, [.blk (mkLoop p dims tpl)])

/-- The prologue's row for template row `t`: a copy of `init t` in its memory (none for `assert0`). -/
def prologueRow (init : Nat → Cell) (t : Nat) (r : LRow) : List Seg :=
  match r.op with
  | .assert0 => []
  | _ => [.row ⟨.lin 0 0, r.ty, [(init t).addr, (init t).addr]⟩]

/-- The prologue's rows from template row `t` on. -/
def prologueSegs (init : Nat → Cell) : Nat → List LRow → List Seg
  | _, [] => []
  | t, r :: rs => prologueRow init t r ++ prologueSegs init (t + 1) rs

/-- The prologue of a loop: per writing template row `t` (in order), a copy of `init t` in row
`t`'s memory: the cells the loop's `prev` operands read at iteration `0`. -/
def prologue (tpl : List LRow) (init : Nat → Cell) : BM Unit := fun _ => ((), prologueSegs init 0 tpl)

/-- **A loop with carried values**: the prologue (`init t` for row `t`'s iteration `−1`), then the
loop. -/
def loopP (dims : List Nat) (tpl : List LRow) (init : Nat → Cell) : BM LoopOut := do
  prologue tpl init
  loop dims tpl

/-! ## Programs -/

/-- The longest glue run kept in one block (A23: no self-evaluation, so glue runs are no longer split
by row shape as A20 required; a run is split only past `2^16` rows). -/
def glueCap : Nat := 2 ^ 16

/-- Merge consecutive rows into glue blocks: the rows before the first loop block, and the blocks
(a run longer than `glueCap` rows starts a new glue block). -/
def groupAux : List Seg → List Row × List Block
  | [] => ([], [])
  | .row r :: δ =>
    let g := groupAux δ
    if decide (glueCap ≤ g.1.length) then
      ([r], if g.1.isEmpty then g.2 else ⟨[], g.1⟩ :: g.2)
    else (r :: g.1, g.2)
  | .blk B :: δ => let g := groupAux δ; ([], B :: (if g.1.isEmpty then g.2 else ⟨[], g.1⟩ :: g.2))

/-- **The blocks of the segments**: runs of rows become glue blocks (`dims = []`), split past
`glueCap` rows. -/
def group (δ : List Seg) : List Block :=
  let g := groupAux δ
  if g.1.isEmpty then g.2 else ⟨[], g.1⟩ :: g.2

/-- **The program of a gadget** run from the input counts: its blocks, and as glue (the blocks the
`fixmul` rows self-evaluate) every block without loop dimension. -/
def toProgram {α : Type} (nInK nInE : Nat) (m : BM α) : Program :=
  let bs := group (m ⟨nInK, nInE⟩).2
  ⟨nInK, nInE, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

/-! ## A fast program check -/

/-- WP-10's `Program.rowOk` for a row whose cells defined before it are `cl τ`, in a block of
dimensions `dims` writing `tw τ` cells per iteration. -/
def rowOkC (cl : Ty → Nat) (dims : List Nat) (tw : Ty → Nat) (r : Row) : Bool :=
  r.typeOk &&
  r.args.all (fun a => decide (a.base + maxExcess a.strides dims (tw a.ty) < cl a.ty)) &&
  match r.op with
  | .readd lo m => decide (lo + 2 ^ m ≤ cl r.ty)
  | _ => true

/-- Every row of a block at `p`. -/
def blockOkAt (p : Ptr) (B : Block) : Bool :=
  (List.range B.tpl.length).all fun t =>
    rowOkC (fun τ => p.at τ + B.rank τ t) B.dims B.tw (B.tpl.getD t default)

/-- **The program check, in one pass** over the segments with the running pointer
(`segsOk_wf`: it implies `Program.wf`). -/
def segsOk : Ptr → List Seg → Bool
  | _, [] => true
  | p, .row r :: δ => rowOkC p.at [] (fun _ => 0) r && segsOk (p.adv [.row r]) δ
  | p, .blk B :: δ => blockOkAt p B && segsOk (p.adv [.blk B]) δ

end Lvm.Loop.Build
