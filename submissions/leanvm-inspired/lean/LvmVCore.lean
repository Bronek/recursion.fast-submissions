-- Ported from leanVM `formal/Statement/LeanVmVerifier.lean` (formal rev 40f877dc), the generic part
-- of Part 3 (the verifier), as `LvmVCore` for lvm (WP-2). Kept: verifier arithmetic, constants,
-- placements, forms, flushes (lines 402-708), the table and bus-layout structures (919-940,
-- 972-1056), and the generic phases: sumcheck rounds, the grand-product GKR and bus balance, the
-- table sumcheck, the WHIR opening, Keccak by GKR, ring switching (1126-1902). Cut (leanISA): the
-- instruction tables (710-918), `tables` and what reads it (942-970, 1057-1125), and the leanVM
-- verifier proper with its seed (1903-2089). See docs/lvm/stages/WP-2.md.
import LvmDsl
import LvmVParams

section

/-! # Part 3: the verifier -/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics

/-!
## Verifier arithmetic (`crates/verifier/src/field.rs`, `crates/verifier/src/multilinear.rs`)

A function that transcribes a Rust function has its name in `lowerCamelCase` and computes the same
value on the inputs the verifier gives it; the products and sums are taken in the Rust's order
where it is visible (`foldl` from `1` or `0`), although `E` is a field and neither the order nor
the grouping changes a value. The Rust's `E::new(n, 0, 0)` for an integer `n < 2^64` is
`eOfNat n`: the natural-number cast of `E` is the characteristic-two one (`(2 : E) = 0`) and is
never used for a wire integer. A `K` value that the Rust lifts into `E` (`E::from`,
`field.rs:161-165`) is `ofK`.

**Preconditions the Rust checks and the verifier always meets.** `multilinear_eval` rejects a
table not of `2^|point|` entries, and `eq_eval` and `dot` assert equal lengths. At every call site
of the verifier the lengths agree by construction (the table sizes are `2^k` for the `k`
coordinates the caller passes), so these functions are total here: an excess entry is ignored, as
`zip` ignores it.
-/

/-- The integer value of a `K` word (the Rust's `K.0`). -/
def kToNat (a : K) : ℕ := a.toBitVec.toNat

/-- The three limbs of `e` as one 192-bit integer, limb `0` lowest: the bits `sample_queries`
reads (`whir.rs:81`). -/
def eToNat (e : E) : ℕ :=
  kToNat (e.limb 0) + 2 ^ 64 * kToNat (e.limb 1) + 2 ^ 128 * kToNat (e.limb 2)

/-- `gpow(index) = GEN.pow(index)` (`layout.rs:114-116`): `Parameters.addressOfIndex index`, the
same power in `K`, in limb `0`. -/
def gpow (index : ℕ) : E := gen ^ index

/-- `E::sum(values)`: the sum from `ZERO`, left to right (`field.rs:121-123`). -/
def sumE (values : List E) : E := values.foldl (· + ·) 0

/-- The product from `ONE`, left to right, as the GKR step takes a child's
(`crates/verifier/src/bus.rs:35-37`). -/
def prodE (values : List E) : E := values.foldl (· * ·) 1

/-- `acc, acc·base, acc·base², …`, `count` terms. -/
def powersFrom (acc base : E) : ℕ → List E
  | 0 => []
  | count + 1 => acc :: powersFrom (acc * base) base count

/-- `powers(base, count)`: `1, base, base², …`, `count` terms (`field.rs:258-267`). -/
def powers (base : E) (count : ℕ) : List E := powersFrom 1 base count

/-- `eq_kernel(point)`: the `2^|point|` equality weights, the first coordinate the lowest bit
(`multilinear.rs:6-19`). -/
def eqKernel (point : List E) : List E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) [1]

/-- One fold of `multilinear_eval`: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairs (r : E) : List E → List E
  | a :: b :: rest => (a * (1 + r) + b * r) :: foldPairs r rest
  | _ => []

/-- `multilinear_eval(mle, point)`: the multilinear extension of the table at the point, the
first coordinate folding adjacent entries (`multilinear.rs:45-59`). A table of the wrong size,
which the Rust rejects, never reaches it (see the section note); `0` for an empty result. -/
def multilinearEval (mle point : List E) : E :=
  (point.foldl (fun cur r ↦ foldPairs r cur) mle).headD 0

/-- The bit length of a natural number, `0` at `0`. -/
def bitLength (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- `log2_ceil(value)`: the bit length of `value - 1`, saturating (`multilinear.rs:61-63`); `0`
at `value = 0`, the height of a table with no row. -/
def log2Ceil (value : ℕ) : ℕ := bitLength (value - 1)

/-- `log2_strict(value)`: the exponent of a power of two, `none` otherwise
(`multilinear.rs:65-68`). -/
def log2Strict (value : ℕ) : Option ℕ :=
  if 0 < value ∧ value &&& (value - 1) = 0 then some (bitLength value - 1) else none

/-- `eq_eval(left, right) = Π (1 + x + y)` (`multilinear.rs:70-77`). -/
def eqEval (left right : List E) : E :=
  (List.zipWith (fun x z ↦ 1 + x + z) left right).foldl (· * ·) 1

/-- `dot(left, right) = Σ x·y` (`multilinear.rs:79-86`). -/
def dot (left right : List E) : E :=
  (List.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `padding_weight(point, n)`: `pad_n(point)`, the multilinear extension of `[z ≥ n]` for
`n ≤ 2^|point|`, unrolled from the low bit (`multilinear.rs:88-96`; `doc/leanvm`, Lemma
`lem:suffix`). -/
def paddingWeight (point : List E) (n : ℕ) : E :=
  (1 + eOfNat ((n >>> point.length) % 2)) *
    point.zipIdx.foldl (fun pad (r, k) ↦
      let b := eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1

/-- `index_mle(point)`: the multilinear extension of `[1, g, g², …]` at an LSB-first point,
`Π (1 + r_i·(1 + g^(2^i)))` (`multilinear.rs:98-107`). -/
def indexMleFrom (generatorPower : E) : List E → E → E
  | [], acc => acc
  | r :: rs, acc => indexMleFrom (generatorPower ^ 2) rs (acc * (1 + r * (1 + generatorPower)))

/-- `index_mle(point)` (`multilinear.rs:98-107`). -/
def indexMle (point : List E) : E := indexMleFrom gen point 1

/-- `poly_eval(coefficients, point)`: Horner's rule over the coefficients, constant first
(`multilinear.rs:109-112`). -/
def polyEval (coefficients : List E) (point : E) : E :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-- `selector_point(selector, length)`: the low `length` bits of `selector` as `0/1` elements,
lowest first (`multilinear.rs:146-148`). -/
def selectorPoint (selector length : ℕ) : List E :=
  (List.range length).map fun bit ↦ eOfNat ((selector >>> bit) % 2)

/-! ## The verifier's layout

lvm (WP-2): the leanISA instruction tables (`tables`, `layout.rs:186-490`) and `build_layout` are not
ported; the bus balance and the table sumcheck take the table list as their first argument
(`accumulateSide`, `verifyBusBalance`, `tableSumcheck`), so that an instance other than leanISA's
supplies its own. -/

/-! ## The verifier's layout (leanVM's heading) (`multilinear.rs:114-148`, `layout.rs`, `bus.rs:53-93`) -/

/-! ### Constants (`layout.rs:12, 70-88, 130-132, 373-379`;
`crates/verifier/src/keccak.rs:18-20, 55-67`) -/

/-- `BUS_BITS`: the bus communicates tuples of `2^BUS_BITS` field elements (`layout.rs:12`). -/
def busBits : ℕ := 4

/-- `NUM_GLOBAL_COLUMNS`: the columns no instruction table owns, first in the global numbering
(`layout.rs:70-71`). -/
def globalColumnCount : ℕ := 6

/-- Global column `MEMORY_0` (`layout.rs:72`); then `MEMORY_1`, `MEMORY_2`,
`MEMORY_FINAL_COUNTERS`, `BYTECODE_FINAL_COUNTERS`. -/
def memory0 : ℕ := 0
def memory1 : ℕ := 1
def memory2 : ℕ := 2
def memoryFinalCounters : ℕ := 3
def bytecodeFinalCounters : ℕ := 4
/-- Global column `QKECCAK`, the Keccak reduction's committed column: per step, its input state's
lanes and the state after every `KECCAK_DEPTH` rounds but the last, a lane per slot, and in the
slots left over the `KECCAK` table's own first committed columns (`keccakSlot`; `layout.rs:77`). -/
def qkeccak : ℕ := 5

/-- `K_BITS`: a `K` word's bits (`layout.rs:79`). -/
def kBits : ℕ := 64

/-- `KECCAK_DEPTH`: the reduction commits a step's state every `12` rounds (`layout.rs:83`). -/
def keccakDepth : ℕ := 12

/-- `KeccakShape::segments`, `ROUNDS / depth` at `depth = KECCAK_DEPTH`, `ROUNDS = 24`
(`keccak.rs:56-58`). -/
def keccakSegments : ℕ := 24 / keccakDepth

/-- The bits of a segment index, `log2_ceil(shape.segments())` (`keccak.rs:247`). -/
def keccakSegmentBits : ℕ := log2Ceil keccakSegments

/-- `KeccakShape::slot_bits`, `log2_ceil(STATE_LANES * segments)`, `STATE_LANES = 25`
(`keccak.rs:64-67`): lane `l` of the state after `KECCAK_DEPTH · m` rounds is slot `25m + l`; the
`2^6 - 50` slots above the states carry `KECCAK` columns (`keccakSlot`). -/
def qkeccakSlotBits : ℕ := log2Ceil (25 * keccakSegments)

/-- `KECCAK_MIN_STEPS_LOG`: the reduction is sized for at least one block of `512` steps
(`layout.rs:84`). -/
def keccakMinStepsLog : ℕ := 9

/-- `BITS = 64 * STATE_LANES`: a state's bits (`keccak.rs:18`). -/
def keccakBits : ℕ := 1600

/-- `LOCAL_BITS`: a bit position is `z + 64 · lane`, in a cube of `2^11` (`keccak.rs:19`). -/
def keccakLocalBits : ℕ := 11

/-- `LANE_BITS`: the bits of a lane's index, `25 ≤ 2^5` (`keccak.rs:20`). -/
def keccakLaneBits : ℕ := 5

/-- The bus separators `SEP_STATE`, `SEP_MEM`, `SEP_BYTECODE` (`layout.rs:130-132`). -/
def sepState : E := 1
def sepMem : E := gen
def sepBytecode : E := gen ^ 2

/-- The opcodes' numbers `OP_XOR`, `OP_MUL`, `OP_SET`, `OP_DEREF`, `OP_JUMP`, `OP_KECCAK`
(`layout.rs:373-378`). -/
def opXor : ℕ := 0
def opMul : ℕ := 1
def opSet : ℕ := 2
def opDeref : ℕ := 3
def opJump : ℕ := 4
def opKeccak : ℕ := 5

/-! ### Placements (`Placement`, `multilinear.rs:114-148`) -/

/-- Where something sits in the stacked cube: a claim's point fills the low `variableCount`
coordinates, the bits of the selector `index` fixing the rest. -/
structure Placement where
  /-- The coordinates the claim's point fills. -/
  variableCount : ℕ
  /-- The selector whose bits fix the other coordinates. -/
  index : ℕ
  deriving Inhabited, DecidableEq

/-- `Placement::stack_point`: the point on the stacked cube (`multilinear.rs:122-125`). -/
def Placement.stackPoint (p : Placement) (point : List E) (stackLog : ℕ) : List E :=
  point ++ selectorPoint (p.index >>> p.variableCount) (stackLog - p.variableCount)

/-- `Placement::eq_above`: the equality weight of the coordinates above the window
(`multilinear.rs:127-131`). -/
def Placement.eqAbove (p : Placement) (point : List E) : E :=
  eqEval (selectorPoint (p.index >>> p.variableCount) (point.length - p.variableCount))
    (point.drop p.variableCount)

/-- `stack_offsets(sizes)`: blocks of `2^size` laid end to end, largest first, ties by index;
their offsets, and the log-size of the total (`multilinear.rs:134-144`). -/
def stackOffsets (sizes : List ℕ) : List ℕ × ℕ :=
  let size := fun i ↦ sizes.getD i 0
  let order := (List.range sizes.length).mergeSort fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))
  let placed := order.foldl (fun (acc : List ℕ × ℕ) i ↦
    (acc.1.set i acc.2, acc.2 + 2 ^ size i)) (List.replicate sizes.length 0, 0)
  (placed.1, log2Ceil placed.2)

/-! ### Forms (`Form`, `layout.rs:14-53, 118-128`) -/

/-- A polynomial of degree at most two in a table's columns: monomial (sorted column indices) to
coefficient, in insertion order (the Rust's `BTreeMap` orders them by monomial; a form's value does
not depend on the order). -/
structure Form where
  /-- The monomials, each with its coefficient. -/
  terms : List (List ℕ × E) := []
  deriving Inhabited

/-- Add `c` into the coefficient of `m`, appending the monomial if it is new (the
`entry(monomial).or_default() +=` of `Form::add_scaled`). -/
def addTerm : List (List ℕ × E) → List ℕ → E → List (List ℕ × E)
  | [], m, c => [(m, 0 + c)]
  | (m', c') :: rest, m, c =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: addTerm rest m c

/-- `Form::add_scaled`: add `weight · other`. -/
def Form.addScaled (f other : Form) (weight : E) : Form :=
  ⟨other.terms.foldl (fun acc t ↦ addTerm acc t.1 (weight * t.2)) f.terms⟩

/-- `Form + Form`. -/
def Form.add (f g : Form) : Form := f.addScaled g 1

/-- `Form::sum`: the empty sum is the zero polynomial. -/
def Form.sum (forms : List Form) : Form := forms.foldl Form.add {}

/-- `Form::evaluate`: `Σ c · Π column(i)` over the terms. -/
def Form.evaluate (f : Form) (column : ℕ → E) : E :=
  sumE (f.terms.map fun t ↦ t.1.foldl (fun acc i ↦ acc * column i) t.2)

/-- `constant(value)`. -/
def Form.const (value : E) : Form := ⟨[([], value)]⟩

/-- `col(index, exponent)`: `g^exponent · x_index`. -/
def Form.col (index : ℕ) (exponent : ℕ := 0) : Form := ⟨[([index], gpow exponent)]⟩

/-- `prod(a, b, exponent)`: `g^exponent · x_a · x_b`. -/
def Form.prod (a b : ℕ) (exponent : ℕ := 0) : Form := ⟨[([min a b, max a b], gpow exponent)]⟩

/-! ### Flushes (`Flushes`, `layout.rs:134-184`) -/

/-- A table's bus flushes: the tuples it pushes and pulls, in pairs. -/
structure Flushes where
  /-- The tuples pushed. -/
  push : List (List Form) := []
  /-- The tuples pulled, each paired with the push at its position. -/
  pull : List (List Form) := []
  deriving Inhabited

namespace Flushes

/-- `Flushes::pair`. -/
def pair (f : Flushes) (push pull : List Form) : Flushes := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes::state_derived`. -/
def stateDerived (f : Flushes) (pc fp : ℕ) (npc nfp : Form) : Flushes :=
  f.pair [Form.const sepState, npc, nfp] [Form.const sepState, Form.col pc, Form.col fp]

/-- `Flushes::state_step`. -/
def stateStep (f : Flushes) (pc fp : ℕ) : Flushes :=
  f.stateDerived pc fp (Form.col pc 1) (Form.col fp)

/-- `Flushes::counted`: a pull at `count` and a push at `counter`, the same otherwise. -/
def counted (f : Flushes) (pre : List Form) (counter : Form) (count : ℕ) (suffix : List Form) :
    Flushes :=
  f.pair (pre ++ [counter] ++ suffix) (pre ++ [Form.col count] ++ suffix)

/-- `Flushes::bytecode`. -/
def bytecode (f : Flushes) (pc count opcode : ℕ) (operands : List Form) : Flushes :=
  f.counted [Form.const sepBytecode, Form.col pc] (Form.col count 1) count
    (Form.const (gpow opcode) :: operands)

/-- `Flushes::memory`. -/
def memory (f : Flushes) (address : Form) (count : ℕ) (values : List Form) : Flushes :=
  f.counted [Form.const sepMem, address] (Form.col count 1) count values

/-- `Flushes::memory_if`: `memory` when the column `flag` is `1`. The push's counter is
`count·(1 + flag·(g + 1))`: `g·count` at `1`, and the pull's `count` at `0`, so the pair cancels
and touches no cell. -/
def memoryIf (f : Flushes) (flag : ℕ) (address : Form) (count : ℕ) (values : List Form) :
    Flushes :=
  f.counted [Form.const sepMem, address]
    (Form.sum [Form.col count, Form.prod flag count 1, Form.prod flag count]) count values

/-- `Flushes::memory_cols`: the columns, padded with zeros to three limbs. -/
def memoryCols (f : Flushes) (address : Form) (count : ℕ) (columns : List ℕ) : Flushes :=
  f.memory address count
    (columns.map (Form.col ·) ++ List.replicate (3 - columns.length) (Form.const 0))

end Flushes

/-- One instruction's table: its columns, its bus flushes, its constraints
(`layout.rs:186-207`). -/
structure Table where
  /-- Its opcode, also its index in `tables()`. -/
  opcode : ℕ
  /-- Its columns' names, in order. -/
  columns : List String
  /-- Its bus flushes. -/
  flushes : Flushes
  /-- Its constraints, as a function of a row's evaluations. -/
  constraints : List E → List E := fun _ ↦ []
  /-- The row a padding row holds (lvm: a field; leanVM's `Table::padding`, `layout.rs:448,
  455-460`, is a function of the leanISA tables, zero but for `KECCAK`'s output lanes). -/
  padding : List E := List.replicate columns.length 0
  deriving Inhabited

/-- `Table::width`. -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `Table::n_constraints`: the number of constraints, read off the zero row. -/
def Table.nConstraints (t : Table) : ℕ := (t.constraints (List.replicate t.width 0)).length

/-- `Table::count_columns`: the columns whose name starts with `cnt`. -/
def Table.countColumns (t : Table) : List ℕ :=
  (t.columns.zipIdx.filter fun (name, _) ↦ name.startsWith "cnt").map (·.2)

/-! ### The bus layout (`layout.rs:55-62`, `bus.rs:53-93`, `lib.rs:119-120`) -/

/-- One block of a bus side, owned by a table (`BusBlock`, `layout.rs:55-62`). -/
structure BusBlock where
  /-- The owner's log-height: the block spans `2 ^ logRows` rows. -/
  logRows : ℕ
  /-- The owner's row count: the first `rows` rows flush, the others are padding rows, whose
  leaves are `1`. -/
  rows : ℕ
  /-- The tuple flushed, over the owner's local columns. -/
  coordinates : List Form
  /-- The owner's opcode. -/
  owner : ℕ
  deriving Inhabited

/-- Where a side's blocks sit in the stacked leaf cube: its log-size, the framework blocks'
placements, and the table blocks', in the side's block order (`BusLayout`, `bus.rs:53-59`). -/
structure BusLayout where
  /-- The log-size of the stacked leaf cube. -/
  depth : ℕ
  /-- The framework blocks' placements. -/
  framework : List Placement
  /-- The table blocks' placements, in the side's block order. -/
  tables : List Placement

/-- `bus_layout(framework_log_rows, blocks)` (`bus.rs:61-79`). -/
def busLayout (frameworkLogRows : List ℕ) (blocks : List BusBlock) : BusLayout :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let (offsets, depth) := stackOffsets sizes
  let placements := List.zipWith (fun size offset ↦ ({ variableCount := size, index := offset } :
    Placement)) sizes offsets
  ⟨depth, placements.take frameworkLogRows.length, placements.drop frameworkLogRows.length⟩

/-- A column claim: the global column's multilinear extension at `point` (over the column's own
variables) is `value` (`ColumnClaim`, `bus.rs:81-85`). -/
structure ColumnClaim where
  /-- The global column. -/
  column : ℕ
  /-- The point, over the column's own variables. -/
  point : List E
  /-- The claimed value. -/
  value : E
  deriving Inhabited

/-- A claim on the stack: the weight it puts on the stack, and the value it claims for it
(`StackClaim`, `lib.rs:119-120`). -/
abbrev StackClaim : Type := (List E → E) × E

/-! ### `build_layout` (`layout.rs:90-103, 492-583`) -/

/-- The layout the verifier derives from the bytecode and the announced sizes. -/
structure Layout where
  /-- The memory's log-size, `κ`. -/
  logMemory : ℕ
  /-- The bytecode's log-size, in tuples of `2^BUS_BITS` words. -/
  logBytecode : ℕ
  /-- The bytecode's words. -/
  bytecode : List K
  /-- The push side's blocks. -/
  push : List BusBlock
  /-- The pull side's blocks. -/
  pull : List BusBlock
  /-- The count side's blocks. -/
  count : List BusBlock
  /-- Every global column's placement; `none` for a `KECCAK` output lane. -/
  placements : List (Option Placement)
  /-- The stack's log-size: the committed columns stacked in one cube. -/
  stackLog : ℕ
  /-- The tables' log-heights, each the least `h` with `rows ≤ 2 ^ h`, at least its floor. -/
  tableLogHeights : List ℕ

/-- The placement of a committed column (`layout.placements[column]`), which the verifier reads
of `MEMORY_0` and `QKECCAK`. -/
def Layout.placement (layout : Layout) (column : ℕ) : Placement :=
  (layout.placements.getD column none).getD default

/-- `ColumnClaim::on_stack` (`bus.rs:87-93`): the claim as an equality weight on the
stack; `none` for a column nothing commits (a `KECCAK` output lane), whose claim never reaches
the stack. -/
def ColumnClaim.onStack (c : ColumnClaim) (layout : Layout) : Option StackClaim :=
  (layout.placements.getD c.column none).map fun placement ↦
    (fun x ↦ eqEval (placement.stackPoint c.point layout.stackLog) x, c.value)


open LeanVM.Protocol.Compile

/-!
## Sumcheck rounds (`transcript.rs:188-233`)

A round polynomial of `count` coefficients is sent with one coefficient left out, which the
verifier derives from the running claim: in plain mode (`eq_factor = None`) `q(0) + q(1) = claim`
fixes `c1`; in equality mode (`eq_factor = r`) `(1 + r)·q(0) + r·q(1) = claim` fixes `c0`
(characteristic two).
-/

/-- Fail on `none`: a pure step that returns a `Result` in the Rust. -/
def liftOption {α : Type} : Option α → VerifierProgram α
  | none => VerifierProgram.fail
  | some a => VerifierProgram.ret a

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`: read a round polynomial of `count`
coefficients, deriving the one the claim fixes; its coefficients, constant first
(`transcript.rs:188-204`). -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → VerifierProgram (List E)
  | none => do
    let constant ← VerifierProgram.readScalar
    let tail ← VerifierProgram.readScalars (count - 2)
    return constant :: (claim + sumE tail) :: tail
  | some eqFactor => do
    let tail ← VerifierProgram.readScalars (count - 1)
    return (claim + eqFactor * sumE tail) :: tail

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry of `equalities`, each
reading its polynomial and sampling its challenge; the challenges in order, and the final claim
(`transcript.rs:219-233`). -/
def sumcheck (claim : E) (count : ℕ) : List (Option E) → VerifierProgram (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← VerifierProgram.sampleChallenge
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    return (challenge :: point, final)

/-!
## The bus phase (`bus.rs:14-213`)

The three GKR trees (push, pull, count) are batched, their roots read as `shared, count` (push and
pull share their root, which is the balance), the layers walked two at a time, one first when the
depth is odd. The leaf decomposition is pure (`accumulateSide`): every side's framework blocks are
evaluated outright, its table blocks accumulate into the owner's form for that side, and the
side's total is the GKR value less the framework and the padding.
-/

/-- The state of the GKR walk: the push, pull and count trees' values at `point`. -/
structure GkrState where
  /-- The push, pull and count trees' values. -/
  values : List E
  /-- The point they are at. -/
  point : List E

/-- One step of `step` levels of the GKR walk (`bus.rs:21-47`). -/
def gkrStep (step : ℕ) (state : GkrState) : VerifierProgram GkrState := do
  let combiner ← VerifierProgram.sampleChallenge
  let claim := polyEval state.values combiner
  let (x, claim) ← sumcheck claim (2 ^ step + 1) (state.point.map some)
  let child0 ← VerifierProgram.readScalars (2 ^ step)
  let child1 ← VerifierProgram.readScalars (2 ^ step)
  let child2 ← VerifierProgram.readScalars (2 ^ step)
  let children := [child0, child1, child2]
  let products := children.map prodE
  VerifierProgram.require (claim = polyEval products combiner)
  let y ← VerifierProgram.sampleChallenges step
  let values := children.map (multilinearEval · y)
  return ⟨values, y ++ x⟩

/-- The `while layer > 0` loop: one level when the remaining depth is odd, two otherwise. -/
def gkrLayers : ℕ → GkrState → VerifierProgram GkrState
  | 0, s => return s
  | 1, s => do
    let s ← gkrStep 1 s
    gkrLayers 0 s
  | n + 2, s =>
    if n % 2 = 1 then do
      let s ← gkrStep 1 s
      gkrLayers (n + 1) s
    else do
      let s ← gkrStep 2 s
      gkrLayers n s

/-- `verify_gkr_grand_products(depth)`: the count root, the GKR point, and the three trees'
values there (`bus.rs:14-51`). -/
def verifyGkrGrandProducts (depth : ℕ) : VerifierProgram (E × List E × List E) := do
  let shared ← VerifierProgram.readScalar
  let count ← VerifierProgram.readScalar
  let s ← gkrLayers depth ⟨[shared, shared, count], []⟩
  return (count, s.point, s.values)

/-- `BusResult` (`bus.rs:98-104`): the framework columns' claims, the GKR point (which the table
sumcheck reuses), each table's form per side (`forms[table][side]`), and the three sides' totals.
The Rust's `bytecode_point`, which only the summary of a walk reads, is left out. -/
structure BusResult where
  /-- The framework columns' claims. -/
  claims : List ColumnClaim
  /-- The GKR point. -/
  point : List E
  /-- Each table's form per side. -/
  forms : List (List Form)
  /-- The three sides' totals. -/
  totals : List E
  deriving Inhabited

/-- The three framework fingerprints of a side (`fingerprints`, `bus.rs:147-159`; the Rust
hoists `memory_index` and `bytecode_index`, `bus.rs:137-138`, pure values inlined here;
`bytecode_value` is the bytecode's value, from `bytecodeValue`). -/
def fingerprints (weights memory memoryLow bytecodeLow : List E) (bytecodeValue : E)
    (pc memoryCount bytecodeCount : E) : List E :=
  [dot (weights.take 3) [sepState, pc, gpow 0],
    dot (weights.take 6) ([sepMem, indexMle memoryLow, memoryCount] ++ memory),
    dot (weights.take 3) [sepBytecode, indexMle bytecodeLow, bytecodeCount] + bytecodeValue]

/-- One table block's form on a side: `side_beta` plus the block's fingerprint, one tuple slot at
a time (`bus.rs:192-195`). -/
def blockForm (block : BusBlock) (sideWeights : List E) (sideBeta : E) : Form :=
  block.coordinates.zipIdx.foldl
    (fun form (coordinate, slot) ↦ form.addScaled coordinate (sideWeights.getD slot 0))
    (Form.const sideBeta)

/-- One side of the leaf decomposition (`bus.rs:183-203`): the forms with the side's table
blocks added, and the side's total. A table's form is summed over its padding rows too, whose
leaves hold `1` instead: the difference, `padding_rows`, is public. -/
def accumulateSide (tables : List Table) (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sideLayout : BusLayout) (frameworkFingerprints sideWeights : List E) (sideBeta : E)
    (point : List E) (treeValue : E) : List (List Form) × E :=
  let frameworkSelectors := sideLayout.framework.map (·.eqAbove point)
  let tableSelectors := sideLayout.tables.map (·.eqAbove point)
  let known := dot frameworkSelectors (frameworkFingerprints.map (sideBeta + ·))
  let (forms, paddingRows) := (List.zip tableSelectors blocks).foldl
    (fun (forms, paddingRows) (selector, block) ↦
      let form := blockForm block sideWeights sideBeta
      let padding := (tables.getD block.owner default).padding
      (forms.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
        paddingRows + selector * paddingWeight (point.take block.logRows) block.rows *
          (form.evaluate (padding.getD · 0) + 1))) (forms, 0)
  let onesPadding := sumE (frameworkSelectors ++ tableSelectors) + 1
  (forms, treeValue + known + onesPadding + paddingRows)

/-- `verify_bus_balance(layout, transcript)` (`bus.rs:106-213`). **Where the verifier gets the
value of the fixed polynomial**, the stacked bytecode's multilinear extension at the bus point
(`bus.rs:139-145`), which the statement fixes and the proof does not: from `bytecodeValue`, which
the deployed verifier computes (`computedBytecodeValue`) and the verifier inside an aggregate takes
from a claim it hands on (`claimedBytecodeValue`). -/
def verifyBusBalance (tables : List Table) (bytecodeValue : List K → List E → VerifierProgram E) (layout : Layout) :
    VerifierProgram BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let alphas ← VerifierProgram.sampleChallenges busBits
  let weights := eqKernel alphas
  let beta ← VerifierProgram.sampleChallenge
  let (countRoot, point, treeValues) ← verifyGkrGrandProducts pushLayout.depth
  VerifierProgram.require (countRoot ≠ 0)
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← VerifierProgram.readScalars 3
  let memoryFinal ← VerifierProgram.readScalar
  let bytecodeFinal ← VerifierProgram.readScalar
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let bytecodeValue ← bytecodeValue layout.bytecode (bytecodeLow ++ alphas)
  let fp := fingerprints weights memory memoryLow bytecodeLow bytecodeValue
  let pcFinal := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide tables forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide tables forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide tables forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, point, forms3, [total0, total1, total2]⟩

/-!
## The table sumcheck (`bus.rs:215-259`)

One plain-mode sumcheck over `max` of the tables' log-heights, its challenges reversed the point;
the terminal claim is `Σ weight · (constraints + forms)`, and a table of log-height `h` has its
evaluations at the point's first `h` coordinates.
-/

/-- The tables' weights at the point (`bus.rs:231-237`): coordinate `v` contributes
`1 + equality_point[v] + r_v` to a table taller than `v`, and `r_v` to the others. -/
def tableWeights (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    List.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ ↦ 1)

/-- The per-table loops of `table_sumcheck` (`bus.rs:239-257`): read each table's row
evaluations, add its weighted terms to `final`, and collect its point and evaluations. The Rust
reads every table's evaluations before it sums the terms: the same reads, in the same order. -/
def tableTerms (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → ℕ → E → VerifierProgram (E × List (List E × List E))
  | [], _, final => return (final, [])
  | (table, height, forms, weight) :: rest, cursor, final => do
    let evaluations ← VerifierProgram.readScalars table.width
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let (final, rows) ← tableTerms constraintPowers formPowers point rest
      (cursor + table.nConstraints) final
    return (final, (point.take height, evaluations) :: rows)

/-- `table_sumcheck(tables, table_log_heights, bus_forms, constraint_powers, form_powers,
equality_point, target, transcript)` (`bus.rs:218-259`): each table's point and its columns'
evaluations there. -/
def tableSumcheck (tables : List Table) (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) : VerifierProgram
    (List (List E × List E)) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheck target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := List.zip tables (List.zip heights (List.zip busForms weights))
  let (final, evaluations) ← tableTerms constraintPowers formPowers point rows 0 0
  VerifierProgram.require (final = claim)
  return evaluations

/-!
## The WHIR opening (`whir.rs`, `lib.rs:122-139`)

**Commitments.** The Rust reads a Merkle root as two scalars (`Digest::from_halves` of
`next_scalars(2)`, `whir.rs:177-178`) and opens it a level later with
`transcript.merkle(current_root, block_length, &queries, leaf_words)` (`whir.rs:196`). The
language's `commit height width` fixes the matrix shape when the root is read, so the shape is
computed from the ladder there:

* the stack's root (commitment `0`, read by `verify_execution` before the bus phase, `commitStack`)
  is opened at level `0`: `2^(log_n − folds[0] + rate_0)` leaves of `2^folds[0]` words;
* the root read at level `ℓ` (commitment `ℓ + 1`) is opened at level `ℓ + 1`:
  `2^(message_log_ℓ − folds[ℓ+1] + rate_{ℓ+1})` leaves of `3 · 2^folds[ℓ+1]` words.

Level `ℓ` therefore opens commitment `ℓ` (`VerifierProgram.queryOpenings ℓ`). The rows come back as
raw words; the level-0 reversal and the regrouping of deeper rows into `E` (`ext_row`) are the
program's.

`derive_config` is `LeanVM.Parameters.Whir.ladder`. `induced_weight` requires
`point.len() == message_log` (`whir.rs:112`); every glued claim is evaluated at
`point[fold_start..]`, the fold challenges from `fold_start` on and then the tail's, of length
`log_n − fold_start = message_log`, so the check always holds and is not repeated. The error after
the level loop (`WhirNoTerminalLevel`, `whir.rs:264`) is `VerifierProgram.fail` on an empty ladder,
which `derive_config` never returns.
-/

/-- The loop of `sample_queries`: each sample yields up to `192 / depth` positions of `depth`
bits, low bits first (`whir.rs:79-88`). -/
def sampleQueriesAux (depth : ℕ) : ℕ → ℕ → VerifierProgram (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← VerifierProgram.sampleChallenge)
      let n := min (192 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← sampleQueriesAux depth fuel (remaining - n)
      return chunk ++ rest

/-- `sample_queries(transcript, 2^depth, count)` (`whir.rs:75-90`), from the block's log-length
`depth` (the Rust recovers it from the length by `log2_strict`, which cannot fail).
`count` rounds of fuel suffice: each yields `min(192 / depth, remaining) ≥ 1` positions, as
`depth ≤ 64`. -/
def sampleQueries (depth count : ℕ) : VerifierProgram (List ℕ) := sampleQueriesAux depth count count

/-- `ext_row(words)`: a deeper level's leaf words regrouped into the `E` values they encode,
three per lane (`whir.rs:65-73`). A trailing incomplete lane, which the leaf width rules out, is
padded with zeros here and dropped by the Rust. -/
def extRow : List K → List E
  | c0 :: c1 :: c2 :: rest => E.ofLimbs c0 c1 c2 :: extRow rest
  | [c0, c1] => [E.ofLimbs c0 c1 0]
  | [c0] => [E.ofLimbs c0 0 0]
  | [] => []

/-- The level's enforced sum, `Σ_q w_q · ⟨row_q, eq(folds, ·)⟩` (`row_values` and `enforced`,
`whir.rs:197-211`). -/
def enforcedSum (rows : List (List E)) (folds queryWeights : List E) : E :=
  let laneWeights := eqKernel folds
  (List.zip queryWeights rows).foldl (fun total (w, row) ↦ total + w * dot row laneWeights) 0

/-- The layers of `subspace_roots`: square-and-shift the layer by the last root, pop the next
root (`whir.rs:96-102`). -/
def subspaceRootsAux : ℕ → E → List E → List E
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value ^ 2 + last * value with
    | [] => []
    | root :: rest => root :: subspaceRootsAux n root rest

/-- `subspace_roots(log_n)`: `1`, then the `log_n` subspace polynomial values (`whir.rs:92-104`;
in `K` there, embedded in `E` here). -/
def subspaceRoots (logN : ℕ) : List E :=
  1 :: subspaceRootsAux logN 1 ((List.range logN).map fun i ↦ eOfNat (2 ^ (i + 1)))

/-- `induced_weight(message_log, queries, query_weights, point)`: the level's batched query
claims as one weight at `point`, `Σ_q w_q Π_k (1 + p_k (1 + Ŵ_k(x_q)))` (`whir.rs:106-126`;
`K::inv` maps zero to zero). -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights point : List E) : E :=
  let roots := subspaceRoots messageLog
  let inverses := roots.map fun value ↦ if value = 0 then 0 else value⁻¹
  (List.zip queryWeights queries).foldl (fun total (weight, query) ↦
    let product := point.zipIdx.foldl (fun (acc : E × E) (challenge, coordinate) ↦
      (acc.1 * (1 + challenge * (1 + acc.2 * inverses.getD coordinate 0)),
        acc.2 ^ 2 + roots.getD coordinate 0 * acc.2)) (weight, eOfNat query)
    total + product.1) 0

/-- `GluedClaim`: a claim folded into the running sumcheck, and the weight it owes back
(`whir.rs:130-139`). -/
structure GluedClaim where
  /-- The power of the level's `λ` it was glued with. -/
  scalar : E
  /-- How many fold challenges preceded the level. -/
  foldStart : ℕ
  /-- Its weight at the terminal point, restricted to the level's message coordinates. -/
  weightAt : List E → E

/-! ### The level loop (`whir.rs:158-264`) -/

/-- The running state of `verify_whir`: `running_quad`, every fold challenge so far, and the glued
claims so far (`running_target` is the final level's tail rounds', `tailRounds`). -/
structure WhirState where
  /-- `running_quad`: the running sumcheck's quadratic. -/
  runningQuad : List E
  /-- Every fold challenge so far. -/
  folds : List E
  /-- The glued claims so far. -/
  glued : List GluedClaim

/-- A level's fold rounds: sample, fold the running claim, read the next quadratic
(`whir.rs:159-165`). Returns the state and the level's own challenges. -/
def foldRounds : ℕ → WhirState → List E → VerifierProgram (WhirState × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← VerifierProgram.sampleChallenge
    let quad ← sumcheckRoundPoly 3 (polyEval s.runningQuad challenge) none
    foldRounds n { s with runningQuad := quad, folds := s.folds ++ [challenge] } (levelFolds ++
        [challenge])

/-- The final level's tail rounds: sample, fold, and read the next quadratic unless it is the
last round (`whir.rs:237-246`). The tail challenges and the final running claim. With no round
the Rust compares against `ZERO` and this fails; the ladder never leaves the final level fewer than
two variables. -/
def tailRounds : ℕ → List E → VerifierProgram (List E × E)
  | 0, _ => VerifierProgram.fail
  | n + 1, quad => do
    let challenge ← VerifierProgram.sampleChallenge
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRounds n quad
      return (challenge :: rest, target)

/-- Glue a level's pending claims, each an intro message and a weight, into the running sumcheck
with powers of `λ`, the running claim keeping `λ⁰` (`whir.rs:221-232`). -/
def glue (lam : E) (state : WhirState) (pending : List (List E × (List E → E))) : WhirState :=
  (pending.foldl (fun (acc : WhirState × E) (intro, weightAt) ↦
    let scalar := acc.2 * lam
    let state := acc.1
    ({ state with
        runningQuad := List.zipWith (fun q i ↦ q + scalar * i) state.runningQuad intro,
        glued := state.glued ++ [⟨scalar, state.folds.length, weightAt⟩] }, scalar)) (state, 1)).1

/-- The shape of the commitment a level opens: `2^(message_log + rate)` leaves of `width`
words, the message log being the one after the level's folds. -/
def levelShape (messageLogBefore : ℕ) (level : Whir.Level) (width : ℕ) : ℕ × ℕ :=
  (messageLogBefore - level.fold + level.logInvRate, width)

/-- One level of `verify_whir` and every level after it (`whir.rs:158-262`). `index` is
the level's index, which is also the index of the commitment it opens; `laneFolds` is
`config.folds[0]`. -/
def whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → VerifierProgram Unit
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRounds level.fold s []
    let messageLog := logN - s.folds.length
    -- The level's claims: the residual on the final level; otherwise the next commitment and
    -- its out-of-domain claim.
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← VerifierProgram.readScalars (2 ^ messageLog)
        pure (residual, ([] : List (List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        VerifierProgram.readCommitment height width
        let oodPoint ← VerifierProgram.sampleChallenges messageLog
        let oodValue ← VerifierProgram.readScalar
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(intro, fun x ↦ eqEval oodPoint x)])
    VerifierProgram.grindProofOfWork Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← VerifierProgram.sampleChallenge
    let queryWeights := powers lam queries.length
    let words ← VerifierProgram.queryOpenings index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++ [(intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRounds messageLog s.runningQuad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      VerifierProgram.require (terminal = target)
    | _ :: _ => whirLevels logN laneFolds evaluateBasis (index + 1) rest s

/-- `verify_whir(transcript, log_n, log_inv_rate, target, root, evaluate_basis)`, the root being
commitment `0` (`whir.rs:141-265`). -/
def verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : VerifierProgram
    Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevels logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config ⟨quad, [], []⟩

/-- Read the stack's root (`verify_execution`, step 2, `lib.rs:235-237`): commitment `0`, the
shape level `0` opens it at. -/
def commitStack (logN logInvRate : ℕ) : VerifierProgram Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  match config with
  | [] => VerifierProgram.fail
  | level :: _ =>
    let (height, width) := levelShape logN level (2 ^ level.fold)
    VerifierProgram.readCommitment height width

/-- `verify_stacked_opening(transcript, root, stack_log, log_inv_rate, claims)`: batch the claims
with powers of one challenge into one WHIR opening (`lib.rs:122-139`). -/
def verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) : VerifierProgram
    Unit := do
  let scales := powers (← VerifierProgram.sampleChallenge) claims.length
  verifyWhir stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-!
## Keccak, by GKR over its rounds (`keccak.rs`)

The protocol is `doc/leanvm/body/c-keccak-gkr.tex`; `KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI`
(`crates/verifier/src/hash.rs:11-49`) are `keccakRC`, `keccakRho`, `keccakPi` of `Keccak.lean`.
A claim is a weighted sum of the bits of one state per segment, the weight of bit `j` of instance
`i` of pack `y` (sixteen consecutive steps) in segment `m` being
`eq(point, (y, m)) · weights[j] · mu[i]`; each layer turns a claim on the states after a round into
one on the states before it.

**Representation.**

* The Rust tabulates the embedding, `RMFE_EMBED` and `RMFE_PROJECT` (`keccak.rs:22-46`); it is
  derived here (`rmfe`), from integer polynomials over `GF(2)` as natural numbers, bit `i` the
  coefficient of `x^i`. Their loops are bounded by fuel: `carryless a b` by `b` (each step halves
  `b`), `carrylessDivmod a f` by the bit length of `a` plus one (each step lowers the bit length of
  the remainder when `f ≠ 0`; `f = 0` is never passed).
* A factor's inverse is the first `g` in `1 .. 2^degree - 1` that inverts the cofactor modulo the
  factor, by `List.find?`, `0` if none (every factor of `rmfeFactors` is irreducible, so one is
  found).
* The weight array `g` of `linear_transpose` is an array here, set where the Rust sets it.
-/

/-! ### Constants (`keccak.rs:14-17`) -/

/-- `EMBED_BITS`: a pack's bits embed in a polynomial of `24` coefficients (`keccak.rs:16`). -/
def embedBits : ℕ := 24

/-- `PRODUCT_BITS = 2 · EMBED_BITS − 1`: the product of two embeddings has `47` coefficients
(`keccak.rs:17`). -/
def productBits : ℕ := 2 * embedBits - 1

/-- The moduli the embedding is glued from, with the bits each holds. -/
def rmfeFactors : List (ℕ × ℕ) :=
  [(0b10, 1), (0b11, 1), (0b1011, 2), (0b1101, 2), (0b100101, 3), (0b101001, 3), (0b101111, 3)]

/-! ### The embedding (`RMFE_EMBED`, `RMFE_PROJECT`, `keccak.rs:22-46`) -/

/-- The loop of `carryless`: while `b ≠ 0`, add `a` if `b`'s low bit is set, then shift. -/
def carrylessAux : (fuel a b out : ℕ) → ℕ
  | 0, _, _, out => out
  | fuel + 1, a, b, out =>
    if b = 0 then out
    else carrylessAux fuel (a <<< 1) (b >>> 1) (if b % 2 = 1 then out ^^^ a else out)

/-- `carryless a b`: the product of two binary polynomials. -/
def carryless (a b : ℕ) : ℕ := carrylessAux b a b 0

/-- The loop of `carrylessDivmod`: while the remainder is nonzero and no shorter than `f`,
subtract `f` shifted under its leading bit. -/
def carrylessDivmodAux : (fuel f quotient a : ℕ) → ℕ × ℕ
  | 0, _, quotient, a => (quotient, a)
  | fuel + 1, f, quotient, a =>
    if a ≠ 0 ∧ bitLength f ≤ bitLength a then
      let shift := bitLength a - bitLength f
      carrylessDivmodAux fuel f (quotient ||| (1 <<< shift)) (a ^^^ (f <<< shift))
    else (quotient, a)

/-- `carrylessDivmod a f`: the quotient and remainder of binary polynomials. -/
def carrylessDivmod (a f : ℕ) : ℕ × ℕ := carrylessDivmodAux (bitLength a + 1) f 0 a

/-- The parity of the set bits. -/
def bitParity (n : ℕ) : ℕ := ((List.range (bitLength n)).countP fun i ↦ n.testBit i) % 2

/-- The product of the moduli, by `carryless`. -/
def rmfeModulus : ℕ :=
  match rmfeFactors.map Prod.fst with
  | [] => 0
  | f :: fs => fs.foldl carryless f

/-- One factor's share of `rmfe`: its bits' embeddings (the residues,
lifted through the Chinese remainder theorem), and per bit the projection's mask, the product
coefficients whose parity is the bit. -/
def rmfeFactor (modulus f bits : ℕ) : List ℕ × List ℕ :=
  let cofactor := (carrylessDivmod modulus f).1
  let degree := bitLength f - 1
  let inverse := (((List.range (2 ^ degree)).drop 1).find? fun g ↦
    (carrylessDivmod (carryless (carrylessDivmod cofactor f).2 g) f).2 = 1).getD 0
  let lift := (carrylessDivmod (carryless cofactor inverse) modulus).2
  -- A residue is the polynomial taking the bits as its values at 0, 1 and infinity.
  let residues : List ℕ := if bits = 1 then [1] else if bits = 2 then [0b11, 0b10]
    else [0b011, 0b010, 0b110]
  let embed := residues.map fun r ↦ (carrylessDivmod (carryless lift r) modulus).2
  let masks := (List.range productBits).foldl (fun masks c ↦
    let g := (carrylessDivmod (1 <<< c) f).2
    let atZero := g % 2
    let atOne := bitParity g
    let values : List ℕ := if bits = 1 then [if f = 0b10 then atZero else atOne]
      else if bits = 2 then [atZero, atOne] else [atZero, atOne, g >>> 4]
    List.zipWith (fun mask value ↦ mask ||| (value <<< c)) masks values)
    (List.replicate bits 0)
  (embed, masks)

/-- The embedding (`keccak.rs:22-24`): sixteen bits embed in a binary polynomial of degree at
most `23`, and a product of two embeddings projects to the AND of what they embed. Each unit
vector's embedding, and per bit of the projection the product coefficients it is the parity of;
the last bit rides the leading coefficient, which the residues do not see. -/
def rmfe : List ℕ × List ℕ :=
  let (embed, project) := rmfeFactors.foldl (fun (acc : List ℕ × List ℕ) (f, bits) ↦
    let (e, p) := rmfeFactor rmfeModulus f bits
    (acc.1 ++ e, acc.2 ++ p)) ([], [])
  (embed ++ [rmfeModulus], project ++ [1 <<< (productBits - 1)])

/-- `RMFE_EMBED` (`keccak.rs:25-28`). -/
def rmfeEmbed : List ℕ := rmfe.1

/-- `RMFE_PROJECT` (`keccak.rs:29-46`). -/
def rmfeProject : List ℕ := rmfe.2

/-! ### Claims and the round's linear map (`keccak.rs:70-113`) -/

/-- `Claim` (`keccak.rs:70-75`): a claim's value, the weight of each instance of a pack, its point
(a pack index, then a segment index), and the weight of each bit position. -/
structure KeccakClaim where
  /-- The claimed value. -/
  value : E
  /-- The weight of each instance of a pack. -/
  mu : List E
  /-- Its point: a pack index, then a segment index. -/
  point : List E
  /-- The weight of each bit position. -/
  weights : List E
  deriving Inhabited

/-- `along(j, k)`: the position `k` columns along from `j`, in the same row and slice
(`keccak.rs:77-81`). -/
def keccakAlong (j k : ℕ) : ℕ :=
  let lane := j / 64
  let z := j % 64
  64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z

/-- `linear_transpose(w)` (`keccak.rs:83-101`): the transpose of θ, ρ, π on weight
vectors, `⟨w, L(a)⟩ = ⟨Lᵀ(w), a⟩`. `g` is the weight each position of θ's output carries. -/
def keccakLinearTranspose (w : List E) : List E :=
  let w := w.toArray
  let g : Array E := (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0)
  let columns : Array E := ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
    sumE ((List.range 5).map fun y ↦ g.getD (64 * (x + 5 * y) + z) 0)).toArray
  (List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
    g.getD (64 * lane + z) 0 + columns.getD (64 * ((lane % 5 + 1) % 5) + z) 0 +
      columns.getD (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0

/-- `instance_weights(s)` (`keccak.rs:103-113`): the instance weights of a claim made
at the polynomial point `s`, each unit vector's embedding at `s`. -/
def keccakInstanceWeights (s : E) : List E :=
  let sPowers := powers s embedBits
  rmfeEmbed.map fun e ↦
    sumE ((List.range embedBits).filterMap fun b ↦
      if e.testBit b then some (sPowers.getD b 0) else none)

/-! ### A layer (`keccak.rs:115-196`) -/

/-- Step 3 of a layer, the pack and the segment (`keccak.rs:152-161`): an equality-mode round
per coordinate of the claim's point, the value scaled by `1 + r + challenge`. The new value, the
product of the scales, and the challenges. -/
def keccakPackRounds : List E → E → E → VerifierProgram (E × E × List E)
  | [], value, scale => return (value, scale, [])
  | r :: rs, value, scale => do
    let message ← sumcheckRoundPoly 3 value (some r)
    let challenge ← VerifierProgram.sampleChallenge
    let (value, scale, point) ← keccakPackRounds rs
      ((1 + r + challenge) * polyEval message challenge) (scale * (1 + r + challenge))
    return (value, scale, challenge :: point)

/-- `verify_layer(transcript, shape, step, claim)` (`keccak.rs:115-196`): a claim on the states
`step` layers below the committed outputs becomes one on the states a layer further down. The Rust
splits `eq(local, j)`, `j = 64 · lane + z`, into `eq_z[z] · eq_lane[lane]` (`keccak.rs:166-189`);
here it is the one kernel `eqKernel localPoint`, the same values. -/
def verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) : VerifierProgram KeccakClaim := do
  let packBits := logSteps - 4
  -- 1] The product polynomial: the claim's weighted sum of the packs' unprojected chi.
  let product ← VerifierProgram.readScalars productBits
  let projected := sumE ((List.range productBits).map fun c ↦
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0)
  -- iota flips known positions of lane 0 in every instance.
  let segments := eqKernel (claim.point.drop packBits)
  let iota := sumE ((List.range keccakSegments).map fun segment ↦
    let constant := keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((List.range 64).filterMap fun z ↦
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))
  VerifierProgram.require (projected + iota * sumE claim.mu = claim.value)
  -- 2] At a random point a pack is one field element, and the polynomial's value a sumcheck
  -- claim.
  let s ← VerifierProgram.sampleChallenge
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  -- 3] The pack and the segment.
  let (value, scale, point) ← keccakPackRounds claim.point (polyEval product s) 1
  -- 4] The bit position: `Σ_j w[j] (κ T[j] + (κ + T[j + 1]) T[j + 2])`.
  let (localPoint, value) ← sumcheck value 4 (List.replicate keccakLocalBits none)
  let t ← VerifierProgram.readScalars 3
  let eq := eqKernel localPoint
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  VerifierProgram.require
    (scale * dot (eq.take keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) = value)
  -- 5] `t[k] = Σ_j eq[j] T[j + k]`: one claim on the state before chi, then on the round's
  -- input through the linear map.
  let beta ← VerifierProgram.sampleChallenge
  let weights := (List.range keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)
  return ⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose weights⟩

/-- The layers, `step` from `0` to `KECCAK_DEPTH - 1` (`keccak.rs:264-267`). -/
def keccakLayers (logSteps : ℕ) : List ℕ → KeccakClaim → VerifierProgram KeccakClaim
  | [], claim => return claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayer logSteps step claim
    keccakLayers logSteps steps claim

/-! ### Opening `q_keccak` (`keccak.rs:198-294`) -/

/-- The weights of `open` (`keccak.rs:208-221`): the weight a claim puts on each
`(slot, z)`, its position weights on the slots of the states it speaks of, scaled by the segment;
`first` is the state segment `0` claims, and only the first `count` segments' states are committed.
The slots above the states (`qkeccakSlots …`), which carry `KECCAK` columns, weigh nothing. -/
def keccakSlotWeights (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) : List (List E) :=
  let segments := eqKernel (claim.point.drop (logSteps - 4))
  let weights := claim.weights.toArray
  let rows : Array (Array E) := (List.range count).foldl (fun rows segment ↦
    (List.range keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (segments.getD segment 0 * weights.getD j 0)) rows)
    (Array.replicate (2 ^ qkeccakSlotBits) (Array.replicate 64 0))
  rows.toList.map Array.toList

/-- `open(transcript, shape, claim, first, count, value)` (`keccak.rs:198-223`): a sumcheck over
the slot; the point it ends on, the weight the claim puts on each slice there, and what is left to
match. The sumcheck draws nothing from the weights, so computing them after it, as the pin does,
or before is the same. The Rust sums each slot's row scaled by `eq(slot, ·)` (`eq_kernel(&slot)`);
here the table of rows is folded by the slot's challenges, the same values. -/
def keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    VerifierProgram (List E × List E × E) := do
  let (slot, value) ← sumcheck value 3 (List.replicate qkeccakSlotBits none)
  let rows := slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) (keccakSlotWeights logSteps claim first count)
  return (slot, rows.headD [], value)

/-- The first claim of `verify_keccak` (`keccak.rs:247-263`), on every segment's output at
`instance` and the segment `segment`: the last segment's output is the permutation's, claimed by
the table's lanes `output`, the others' `committed`; the lanes are combined as words at
`lanePoint`, bit `z` of a word weighing `x^z`. -/
def keccakFirstClaim (inst segment lanePoint output : List E) (committed : E) : KeccakClaim :=
  let lanes := eqKernel lanePoint
  let weights := (List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))
  let last := (eqKernel segment).getD (keccakSegments - 1) 0 * dot (lanes.take 25) output
  ⟨committed + last, eqKernel (inst.take 4), inst.drop 4 ++ segment, weights⟩

/-- `verify_keccak(transcript, shape, instance, output)` (`keccak.rs:225-294`): the reduction, a
random claim on every segment's output at `instance`, `KECCAK_DEPTH` layers down to the committed
inputs. The last segment's output is the permutation's, claimed by the table's lanes `output` at
`instance`; the others are committed. It leaves openings of `q_keccak`: the committed outputs as
words at one point (column claims), and the column's 64 slices at another (the point and the
slices, for ring switching). The Rust first checks the shape (`keccak.rs:243-246`), which the
`KECCAK` table's point and lanes always meet, its log-height at least `keccakMinStepsLog`. -/
def verifyKeccak (logSteps : ℕ) (inst output : List E) : VerifierProgram
    (List ColumnClaim × List E × List E) := do
  let packBits := logSteps - 4
  let rLow := inst.take 4
  let segment ← VerifierProgram.sampleChallenges keccakSegmentBits
  let lanePoint ← VerifierProgram.sampleChallenges keccakLaneBits
  let committed ← if 1 < keccakSegments then VerifierProgram.readScalar else pure 0
  let first := keccakFirstClaim inst segment lanePoint output committed
  let claim ← keccakLayers logSteps (List.range keccakDepth) first
  -- The committed outputs, whose instance weights are an eq already: slice 0 holds the slot's
  -- weight, the others `x^z` times it.
  let outputs ← if 1 < keccakSegments then do
      let (slot, weights, value) ← keccakOpen logSteps first 1 (keccakSegments - 1) committed
      let word ← VerifierProgram.readScalar
      VerifierProgram.require (weights.headD 0 * word = value)
      pure [(⟨qkeccak, rLow ++ inst.drop 4 ++ slot, word⟩ : ColumnClaim)]
    else pure []
  -- The inputs: the instances of a pack first, then the slot.
  let (low, value) ← sumcheck claim.value 3 (List.replicate 4 none)
  let (slot, weights, value) ← keccakOpen logSteps claim 0 keccakSegments value
  let slices ← VerifierProgram.readScalars kBits
  VerifierProgram.require (multilinearEval claim.mu low * dot weights slices = value)
  return (outputs, low ++ claim.point.take packBits ++ slot, slices)

/-!
## Ring switching (`crates/verifier/src/ring_switch.rs`)

The 64 claims `s[i] = z(i, point)` on `q_keccak`'s bit slices become one dense claim
`Σ_u W(u) q_keccak(u) = target` on the committed column.
-/

/-- `RING_MAP_SHIFTS` (`ring_switch.rs:9`; `COMPOSITION_SHIFTS`,
`crates/pcs/src/ring_switch.rs:82`): the Frobenius shifts of the six stages composing `Φ`, one
challenge each. -/
def ringMapShifts : List ℕ := [32, 16, 8, 4, 2, 1]

/-- `ring_map(value, challenges)`: `a ↦ a + f_p · a^(2^shift)`, stage by stage
(`ring_switch.rs:11-17`). -/
def phiMap (value : E) (challenges : List E) : E :=
  (List.zip challenges ringMapShifts).foldl
    (fun value (challenge, shift) ↦ value + challenge * value ^ (2 ^ shift)) value

/-- `ring_weight(r, r_prime, coefficients)`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`
(`ring_switch.rs:19-34`). -/
def ringWeight (r rPrime coefficients : List E) : E :=
  (coefficients.foldl (fun (acc : E × List E) c ↦
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
    (acc.1 + product, acc.2.map (· ^ 2))) (0, r)).1

/-- The Frobenius coefficients of the drawn map, `Φ(a) = Σ_{k < 64} c_k a^(2^k)`
(`ring_switch.rs:42-50`). -/
def ringCoefficients (challenges : List E) : List E :=
  (List.range kBits).map fun k ↦
    ((List.zip challenges ringMapShifts).filter fun (_, s) ↦ k &&& s ≠ 0).foldl
      (fun acc (f, s) ↦ acc * f ^ (2 ^ (k % s))) 1

/-- `ring_switch(point, s, transcript)` (`ring_switch.rs:36-54`): draw the map, and return the
target `Σ_i g^i Φ(s_i)` and the weight `W(u) = Φ(eq(point, u))` as a function of the opening
point. -/
def ringSwitch (point s : List E) : VerifierProgram (E × (List E → E)) := do
  let challenges ← VerifierProgram.sampleChallenges ringMapShifts.length
  let coefficients := ringCoefficients challenges
  let target := polyEval (s.map (phiMap · challenges)) gen
  return (target, fun rPrime ↦ ringWeight point rPrime coefficients)

open LeanVM.Semantics LeanVM.Protocol.KeccakHash



/-! ## From `LeanVM.Facts.Verifier`

Ported from leanVM `formal/lean_vm/LeanVM/Facts/Verifier.lean` (lines 36-63): the selector-point
facts, `yE`, `packBits`, `pack`. Its `KECCAK` slot facts (leanISA layout), `seed` and `verify` (the
deployed duplex verifier) are not ported. -/


/-- Dropping the low `v` coordinates of a selector point leaves the selector point of the
selector shifted by `v`. -/
theorem selectorPoint_drop (selector length v : ℕ) :
    (selectorPoint selector length).drop v = selectorPoint (selector >>> v) (length - v) := by
  apply List.ext_getElem (by simp [selectorPoint])
  intro i _ _
  simp [selectorPoint, Nat.shiftRight_add]

/-- `stack_point` as the point, then the selector point's coordinates above the window. -/
theorem Placement.stackPoint_eq_drop (p : Placement) (point : List E) (stackLog : ℕ) :
    p.stackPoint point stackLog =
      point ++ (selectorPoint p.index stackLog).drop p.variableCount := by
  rw [selectorPoint_drop, Placement.stackPoint]


/-- `E(0, 1)`, the tower generator `y` with `y^3 = y + 1`. -/
def yE : E := E.ofLimbs 0 1 0

/-- `PACK_BITS` (`crates/verifier/src/keccak.rs:14`): a pack is `2 ^ PACK_BITS` consecutive
steps. -/
def packBits : ℕ := 4

/-- The steps of a pack, `2 ^ PACK_BITS = 16`. -/
def pack : ℕ := 16

theorem pack_eq : pack = 2 ^ packBits := rfl

end LeanVM.Protocol.Verifier

end
