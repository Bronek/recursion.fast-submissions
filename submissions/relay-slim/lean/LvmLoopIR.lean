import LvmFieldE

/-!
# LoopIR: the verifier arithmetic as loop tables (the language, its layout, its interpreter)

BLUEPRINT §4.5. A *program* is a list of *blocks*; a block is a list of loop dimensions (log sizes)
and a *template*, a list of rows executed once per loop index. A row is an operation with its
operand addresses. Every cell lives in one of two memories, `K` cells and `E` cells; a cell is
named by its exponent `e`, its bus address being `g^e` (`g = FK.x`, leanVM's generator).

* **Operands.** An operand is `⟨τ, base, strides⟩`: at loop index `j` it names the cell
  `base + Σ_d strides[d] * j_d` of memory `τ` (address `g^base · Π_d (g^{s_d})^{j_d}`: affine in
  the exponent).
* **Results are allocated densely.** The cells `[0, nIn τ)` of memory `τ` are the inputs (stream
  lanes, digests, bit fields: cells other tables define). Every other cell is the result of exactly
  one row instance: block `b`'s instance `(jf, t)` (flattened loop index `jf`, template row `t`)
  that writes memory `τ` writes cell `start τ b + tw τ * jf + rank τ t`, where `tw τ` counts the
  template rows writing `τ` and `rank τ t` those before `t`. So the program has one writer per cell
  by construction (the single-writer property), the result address is affine in the loop index,
  and the cells of memory `τ` defined before an instance are exactly `[0, clock τ)`.
* **Definition before use** is then `exponent < clock` for every read, which for an affine operand
  over a box is the closed check `base + Σ_d (s_d - w_d)·(2^{D_d} - 1) < start + rank`
  (`maxExcess`, `w_d = tw · 2^{D_0 + … + D_{d-1}}`): the program check `wf` costs
  `O(|tpl| · |dims|)` per block and is kernel-friendly (`Nat` arithmetic only).
* **Operations** (`c` the result; every operand is a read):
  - `muladd`: `c = a·b + d`;            - `lin k k'`: `c = a + k·b + k'` (`k, k' ∈ K` constants);
  - `assert0`: `gate·a = 0` (no result; `gate` is an operand, normally the node flag cell);
  - `loadE`: `c = a₀ + y·a₁ + y²·a₂` (`E` from three `K` cells);
  - `fixmul`: `c = F·a + d`, `F` the program's *glue matrix* at the loop index (`fixMat`):
    BLUEPRINT's self-evaluation rows (`LvmSelfEval`);
  - `readd lo m`: `c = mem[α]`, the cell whose address is the value `α` of the `K` operand: a read
    at a computed address (WP-0 flag 2: a cap node chosen by position bits). `lo, m` name the region
    `[lo, lo + 2^m)` the interpreter searches; the table does not use them.
  `K`-typed rows have `K` operands; `E`-typed rows may mix (`K` embeds into `E`).
* **The interpreter** `interp` runs the instances in order (blocks, then loop indices with dimension
  0 fastest, then template rows), pushing each result onto its memory: total and computable. It
  returns the cells, `ok` (every `assert0` holds) and `inb` (every `readd` found its cell in its
  region).
* **Tables** are not here: `LvmLoopTable` compiles a program to *pieces*, power-of-two tables of
  one row shape each (`pieces`, defined here because `fixmul` reads their fixed columns).

Nothing here imports Mathlib: the prover's witness generation and the native verifier's
fixed-column closed forms run this code.
-/

namespace Lvm.Loop

/-! ## Types, operands, rows -/

/-- The two memories: `K` cells and `E` cells. -/
inductive Ty where
  | K
  | E
  deriving DecidableEq, Repr, Inhabited

/-- How many `K` words a value of the type takes (columns per operand, coordinates per bus value). -/
def Ty.limbs : Ty → Nat
  | .K => 1
  | .E => 3

/-- Dot product of a stride list with a loop index; the shorter list decides (missing = 0). -/
def dot : List Nat → List Nat → Nat
  | s :: ss, j :: js => s * j + dot ss js
  | _, _ => 0

/-- An operand: cell `base + dot strides j` of memory `ty` at loop index `j`. -/
structure Addr where
  /-- The memory read. -/
  ty : Ty
  /-- The exponent at loop index `0`. -/
  base : Nat
  /-- The exponent's step along each loop dimension. -/
  strides : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- The cell an operand names at loop index `j`. -/
def Addr.at (a : Addr) (j : List Nat) : Nat := a.base + dot a.strides j

/-- An operand that does not move with the loop. -/
def Addr.fixed (ty : Ty) (base : Nat) : Addr := ⟨ty, base, []⟩

/-- The operations. Operand lists: `muladd [a, b, d]`, `lin [a, b]`, `assert0 [a, gate]`,
`loadE [a₀, a₁, a₂]`, `fixmul [a, d]`, `readd [α]`. -/
inductive Op where
  | muladd
  | lin (k k' : FK)
  | assert0
  | loadE
  | fixmul
  | readd (lo m : Nat)
  deriving DecidableEq, Repr

/-- A template row: an operation, the memory of its result, its operands. -/
structure Row where
  /-- The operation. -/
  op : Op
  /-- The memory the result is written to (ignored by `assert0`). -/
  ty : Ty
  /-- The operands. -/
  args : List Addr
  deriving DecidableEq, Repr

instance : Inhabited Row := ⟨⟨.assert0, .K, []⟩⟩

/-- The memory a row writes, if it writes. -/
def Row.writes (r : Row) : Option Ty :=
  match r.op with
  | .assert0 => none
  | _ => some r.ty

/-- Whether a row writes memory `τ` (as a number, for counting). -/
def Row.w (τ : Ty) (r : Row) : Nat := if r.writes = some τ then 1 else 0

/-- A block: loop dimensions (log sizes, dimension 0 the fastest) and a template. -/
structure Block where
  /-- The loop dimensions, each a log size. -/
  dims : List Nat
  /-- The template, executed once per loop index. -/
  tpl : List Row
  deriving DecidableEq, Repr

instance : Inhabited Block := ⟨⟨[], []⟩⟩

/-- A program: the input cell counts, the blocks, and the *glue* blocks (indices) whose fixed
columns `fixmul` rows read. -/
structure Program where
  /-- Input `K` cells `[0, nInK)`. -/
  nInK : Nat
  /-- Input `E` cells `[0, nInE)`. -/
  nInE : Nat
  /-- The blocks, in execution order. -/
  blocks : List Block
  /-- The blocks whose fixed columns form the glue matrix (`fixMat`). -/
  glue : List Nat
  deriving Repr

/-! ## Layout -/

namespace Block

variable (B : Block)

/-- `log₂` of the number of loop indices. -/
def lsize : Nat := B.dims.sum

/-- The number of loop indices. -/
def size : Nat := 2 ^ B.lsize

/-- Template rows writing memory `τ`: cells of `τ` written per loop index. -/
def tw (τ : Ty) : Nat := (B.tpl.map (Row.w τ)).sum

/-- Template rows before row `t` that write memory `τ`. -/
def rank (τ : Ty) (t : Nat) : Nat := ((B.tpl.take t).map (Row.w τ)).sum

end Block

/-- The loop index of flattened index `n` (dimension 0 the lowest digits). -/
def unflat : List Nat → Nat → List Nat
  | [], _ => []
  | d :: ds, n => n % 2 ^ d :: unflat ds (n / 2 ^ d)

/-- The flattened index of loop index `j`. -/
def flat : List Nat → List Nat → Nat
  | d :: ds, j :: js => j + 2 ^ d * flat ds js
  | _, _ => 0

namespace Program

variable (Q : Program)

/-- The input cell count of memory `τ`. -/
def nIn : Ty → Nat
  | .K => Q.nInK
  | .E => Q.nInE

/-- Block `b` (a default block past the end). -/
def blk (b : Nat) : Block := Q.blocks.getD b default

/-- The first cell of memory `τ` that block `b` writes. -/
def start (τ : Ty) (b : Nat) : Nat :=
  Q.nIn τ + ((Q.blocks.take b).map fun B => B.tw τ * B.size).sum

/-- The number of cells of memory `τ`: inputs and every result. -/
def cells (τ : Ty) : Nat := Q.start τ Q.blocks.length

end Program

/-! ## Instances -/

/-- A row instance: block, flattened and unflattened loop index, template row, the row, and the
clocks (cells of each memory defined before it). -/
structure Inst where
  /-- The block. -/
  blk : Nat
  /-- The flattened loop index. -/
  jf : Nat
  /-- The loop index. -/
  j : List Nat
  /-- The template row. -/
  t : Nat
  /-- The row. -/
  row : Row
  /-- `K` cells defined before this instance. -/
  ck : Nat
  /-- `E` cells defined before this instance. -/
  ce : Nat
  deriving Repr

/-- The clock of memory `τ`: the cells defined before the instance, and the cell it writes. -/
def Inst.clock (i : Inst) : Ty → Nat
  | .K => i.ck
  | .E => i.ce

/-- The instances of the template rows `rs` (the first being row `t`) at one loop index, from the
clocks `k`, `e`. -/
def tplInsts (b jf : Nat) (j : List Nat) : Nat → Nat → Nat → List Row → List Inst
  | _, _, _, [] => []
  | t, k, e, r :: rs => ⟨b, jf, j, t, r, k, e⟩ :: tplInsts b jf j (t + 1) (k + r.w .K) (e + r.w .E) rs

namespace Program

variable (Q : Program)

/-- The instances of block `b`, loop index by loop index. -/
def blockInsts (b : Nat) (B : Block) : List Inst :=
  (List.range B.size).flatMap fun jf =>
    tplInsts b jf (unflat B.dims jf) 0 (Q.start .K b + B.tw .K * jf) (Q.start .E b + B.tw .E * jf)
      B.tpl

/-- Every instance of the program, in execution order. -/
def insts : List Inst := (List.range Q.blocks.length).flatMap fun b => Q.blockInsts b (Q.blk b)

/-- The instance of block `b`, loop index `jf`, template row `t` (closed form). -/
def inst (b jf t : Nat) : Inst :=
  let B := Q.blk b
  ⟨b, jf, unflat B.dims jf, t, B.tpl.getD t default,
    Q.start .K b + B.tw .K * jf + B.rank .K t, Q.start .E b + B.tw .E * jf + B.rank .E t⟩

end Program

/-! ## Pieces: the power-of-two tables of one row shape -/

/-- The operation without its constants. -/
inductive Kind where
  | muladd
  | lin
  | assert0
  | loadE
  | fixmul
  | readd
  deriving DecidableEq, Repr, Inhabited

/-- The kind of an operation. -/
def Op.kind : Op → Kind
  | .muladd => .muladd
  | .lin .. => .lin
  | .assert0 => .assert0
  | .loadE => .loadE
  | .fixmul => .fixmul
  | .readd .. => .readd

/-- A row shape: what a table's columns and constraints depend on. -/
structure Shape where
  /-- The operation kind. -/
  kind : Kind
  /-- The result memory (`K` for `assert0`). -/
  ty : Ty
  /-- The operand memories. -/
  args : List Ty
  deriving DecidableEq, Repr, Inhabited

/-- The shape of a row. -/
def Row.shape (r : Row) : Shape :=
  ⟨r.op.kind, if r.op.kind = .assert0 then .K else r.ty, r.args.map (·.ty)⟩

/-- Whether rows of the shape write a result. -/
def Shape.writes (σ : Shape) : Bool := σ.kind != .assert0

/-- A fixed (verifier-known) column of a piece. -/
inductive FCol where
  /-- The address `g^c` of the result cell. -/
  | res
  /-- The address of operand `o` (every operand: its address is fixed; `readd`'s computed address
  is a committed column). -/
  | arg (o : Nat)
  /-- `lin`'s `k`. -/
  | k
  /-- `lin`'s `k'`. -/
  | k'
  /-- `fixmul`'s multiplier `F`. -/
  | F
  deriving DecidableEq, Repr, Inhabited

/-- The fixed columns of a shape, in order. -/
def Shape.fcols (σ : Shape) : List FCol :=
  (if σ.writes then [.res] else []) ++ (List.range σ.args.length).map .arg ++
    (if σ.kind = .lin then [.k, .k'] else []) ++ (if σ.kind = .fixmul then [.F] else [])

/-- A piece: `2^a` template rows `ts` of block `blk`, all of shape `shape`, times the block's loop
indices. Row `x` of the piece (height `2^(a + lsize)`) is loop index `x % size`, template row
`ts[x / size]`. -/
structure Piece where
  /-- The block. -/
  blk : Nat
  /-- The shape of its rows. -/
  shape : Shape
  /-- `log₂` of the number of template rows. -/
  a : Nat
  /-- The template rows, `2^a` of them. -/
  ts : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- The set bits of `n`, from bit `k` on, lowest first (`fuel` at least the bit length). -/
def bitsUp : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | f + 1, k, n => (if n % 2 = 1 then [k] else []) ++ bitsUp f (k + 1) (n / 2)

/-- The set bits of `n`, highest first: the sizes `2^a` of a cut of `n` rows into pieces. -/
def binParts (n : Nat) : List Nat := (bitsUp (n + 1) 0 n).reverse

/-- The distinct elements of a list, in order of first occurrence. -/
def nub {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (nub xs).filter (fun y => decide (y ≠ x))

/-- Cut `l` into consecutive chunks of sizes `2^a`, `a ∈ as`. -/
def chunks : List Nat → List Nat → List (Nat × List Nat)
  | [], _ => []
  | a :: as, l => (a, l.take (2 ^ a)) :: chunks as (l.drop (2 ^ a))

namespace Block

variable (B : Block)

/-- The template rows of shape `σ`. -/
def rowsOf (σ : Shape) : List Nat :=
  (List.range B.tpl.length).filter fun t => (B.tpl.getD t default).shape = σ

/-- The shapes of the template, each once, in order of first use. -/
def shapes : List Shape := nub (B.tpl.map Row.shape)

/-- The pieces of block `b`: per shape, the binary decomposition of its rows (no padding). -/
def pieces (b : Nat) : List Piece :=
  B.shapes.flatMap fun σ =>
    (chunks (binParts (B.rowsOf σ).length) (B.rowsOf σ)).map fun (a, ts) => ⟨b, σ, a, ts⟩

end Block

namespace Program

variable (Q : Program)

/-- Every piece of the program. -/
def pieces : List Piece := (List.range Q.blocks.length).flatMap fun b => (Q.blk b).pieces b

/-- `log₂` of the height of a piece. -/
def height (p : Piece) : Nat := p.a + (Q.blk p.blk).lsize

/-- The instance at row `x` of piece `p`. -/
def pinst (p : Piece) (x : Nat) : Inst :=
  let B := Q.blk p.blk
  Q.inst p.blk (x % B.size) (p.ts.getD (x / B.size) 0)

/-- A fixed column at row `x` of piece `p`, `fixmul`'s multiplier excepted (`0` there). -/
def fvalBasic (p : Piece) (c : FCol) (x : Nat) : FK :=
  let i := Q.pinst p x
  match c with
  | .res => FK.x ^ i.clock i.row.ty
  | .arg o => FK.x ^ ((i.row.args.getD o default).at i.j)
  | .k => match i.row.op with
    | .lin k _ => k
    | _ => 0
  | .k' => match i.row.op with
    | .lin _ k' => k'
    | _ => 0
  | .F => 0

/-- The columns of the glue matrix: every basic fixed column of every piece of a glue block. -/
def glueCols : List (Piece × FCol) :=
  (Q.pieces.filter fun p => Q.glue.contains p.blk).flatMap fun p =>
    (p.shape.fcols.filter (· != .F)).map fun c => (p, c)

/-- The glue matrix at loop index `j`: column `j₀`, row `j₁` (`0` outside). -/
def fixMat (j : List Nat) : FK :=
  match Q.glueCols[j.getD 0 0]? with
  | some (p, c) => if j.getD 1 0 < 2 ^ Q.height p then Q.fvalBasic p c (j.getD 1 0) else 0
  | none => 0

/-- A fixed column at row `x` of piece `p`. -/
def fval (p : Piece) (c : FCol) (x : Nat) : FK :=
  match c with
  | .F => Q.fixMat (Q.pinst p x).j
  | c => Q.fvalBasic p c x

end Program

/-! ## The program check -/

/-- The largest excess of `dot s j` over `w · flat D j` on the box `j_d < 2^{D_d}`. -/
def maxExcess : List Nat → List Nat → Nat → Nat
  | s :: ss, d :: ds, w => (s - w) * (2 ^ d - 1) + maxExcess ss ds (w * 2 ^ d)
  | _, _, _ => 0

/-- Operand count and memories of a row. -/
def Row.typeOk (r : Row) : Bool :=
  let ts := r.args.map (·.ty)
  match r.op with
  | .muladd => ts.length == 3 && (r.ty == .E || ts.all (· == .K))
  | .lin .. => ts.length == 2 && (r.ty == .E || ts.all (· == .K))
  | .assert0 => ts.length == 2
  | .loadE => ts == [.K, .K, .K] && r.ty == .E
  | .fixmul => ts.length == 2 && (r.ty == .E || ts.all (· == .K))
  | .readd .. => ts == [.K]

namespace Program

variable (Q : Program)

/-- Row `t` of block `b` reads only cells defined before it, at every loop index; a `readd`'s region
is defined before it. -/
def rowOk (b : Nat) (B : Block) (t : Nat) (r : Row) : Bool :=
  r.typeOk &&
  r.args.all (fun a => decide (a.base + maxExcess a.strides B.dims (B.tw a.ty) <
    Q.start a.ty b + B.rank a.ty t)) &&
  match r.op with
  | .readd lo m => decide (lo + 2 ^ m ≤ Q.start r.ty b + B.rank r.ty t)
  | _ => true

/-- The program check: every row of every block. -/
def wf : Bool :=
  (List.range Q.blocks.length).all fun b =>
    (List.range (Q.blk b).tpl.length).all fun t => Q.rowOk b (Q.blk b) t ((Q.blk b).tpl.getD t default)

end Program

/-! ## The interpreter -/

/-- The interpreter's state: the cells so far, and the two flags. -/
structure St where
  /-- The `K` cells defined so far. -/
  kc : Array FK
  /-- The `E` cells defined so far. -/
  ec : Array FE
  /-- Every `assert0` so far holds. -/
  ok : Bool
  /-- Every `readd` so far found its cell. -/
  inb : Bool

namespace St

/-- Cell `n` of memory `τ`, as an `E` value (`0` if undefined). -/
def rd (s : St) : Ty → Nat → FE
  | .K, n => FE.ofK (s.kc.getD n 0)
  | .E, n => s.ec.getD n 0

/-- Define the next cell of memory `τ` (a `K` cell keeps the constant coefficient). -/
def put (s : St) : Ty → FE → St
  | .K, v => { s with kc := s.kc.push v.c₀ }
  | .E, v => { s with ec := s.ec.push v }

end St

/-- The exponent `e ∈ [lo, lo + 2^m)` with `g^e = α`, if any. -/
def findExp (α : FK) (lo m : Nat) : Option Nat :=
  ((List.range (2 ^ m)).find? fun i => FK.x ^ (lo + i) == α).map (lo + ·)

namespace Program

variable (Q : Program)

/-- Run one instance. -/
def step (s : St) (i : Inst) : St :=
  let r := i.row
  let rd (o : Nat) : FE := s.rd (r.args.getD o default).ty ((r.args.getD o default).at i.j)
  match r.op with
  | .muladd => s.put r.ty (rd 0 * rd 1 + rd 2)
  | .lin k k' => s.put r.ty (rd 0 + FE.ofK k * rd 1 + FE.ofK k')
  | .assert0 => { s with ok := s.ok && decide (rd 1 * rd 0 = 0) }
  | .loadE => s.put r.ty (rd 0 + FE.y * rd 1 + FE.y * FE.y * rd 2)
  | .fixmul => s.put r.ty (FE.ofK (Q.fixMat i.j) * rd 0 + rd 1)
  | .readd lo m =>
    match findExp (rd 0).c₀ lo m with
    | some e => s.put r.ty (s.rd r.ty e)
    | none => { s.put r.ty 0 with inb := false }

/-- **The interpreter**: run every instance in order from the inputs. -/
def interp (inK : Array FK) (inE : Array FE) : St :=
  Q.insts.foldl Q.step ⟨inK, inE, true, true⟩

end Program

end Lvm.Loop
