import LvmFieldE
import LvmParams

/-!
# The decision `F`: verifier arithmetic and the stream reader

Two parts.

**Verifier arithmetic** (ported from leanVM `formal/Statement/LeanVmVerifier.lean`, Part 3,
"Verifier arithmetic", `:427-516`, itself a transcription of `crates/verifier/src/field.rs` and
`multilinear.rs`): the same functions with the same names, over `Lvm.FE` (= `E`, WP-1) instead of
leanVM's `E`. leanVM's `ofK` is `FE.ofK`, its `eOfNat n` (the Rust's `E::new(n, 0, 0)`, `n < 2^64`)
is `eOfNat`, its generator `gen = x` is `gen`. leanVM's helper tests
(`lean_vm/tests/LeanVMTests/Protocol/Verifier/Helpers.lean`, values of the Rust verifier at its
pin) are replayed on this port by the compiled test in `logs/` (WP-11a report).

**The stream reader** (`DM`). `F` reads the stream `Σ = tagTrace ‖ traceBytes tr` (LvmDriver) in
schedule order through a cursor: `ent` is the byte offset of the next trace entry, `msg` the
message bytes of that entry (an FS query) read so far. An FS entry is
`enc64 |q| (8) ‖ st (32) ‖ msg ‖ answer (32)`, a leaf entry `enc64 |q| ‖ row ‖ answer`, a node
entry 104 B. `readE` takes the next 24 message bytes; `sampleE` takes the answer that follows
the message (lanes 0–2 as an `E` element) and moves to the next entry; `positionsR` takes `⌈t/8⌉`
answers' bit fields (after `grindPreR`, `powCheckR`: a level's proof of
work, PI-GRIND); `openingR` returns the rows' offsets and skips the paths. The cursor never
reads a length lane: every offset is fixed by `F`'s own sequence of reads, which is the
schedule's (`LvmSchedule`). Checks do not stop the reading: `require` clears a flag, so `F`'s
reading is the same on every stream (a static shape, as the circuit's).
-/

set_option autoImplicit false

namespace Lvm

/-! ## Verifier arithmetic (`LeanVmVerifier.lean:427-516`) -/

/-- The generator `x` of `K^×` in `E` (leanVM `gen`, `layout.rs:114`). -/
def gen : FE := FE.ofK FK.x

/-- `E::new(n, 0, 0)`: the integer `n < 2^64` as the `K` word with those bits, in `E`. -/
def eOfNat (n : Nat) : FE := FE.ofK ⟨n.toUInt64⟩

/-- The integer value of a `K` word (`K.0`). -/
def kToNat (a : FK) : Nat := a.val.toNat

/-- The three limbs of `e` as one 192-bit integer, limb `0` lowest (`whir.rs:81`). -/
def eToNat (e : FE) : Nat := kToNat e.c₀ + 2 ^ 64 * kToNat e.c₁ + 2 ^ 128 * kToNat e.c₂

/-- `gpow(index) = GEN.pow(index)` (`layout.rs:114-116`). -/
def gpow (index : Nat) : FE := gen ^ index

/-- `E::sum(values)` (`field.rs:121-123`). -/
def sumE (values : List FE) : FE := values.foldl (· + ·) 0

/-- The product from `ONE`, left to right (`bus.rs:35-37`). -/
def prodE (values : List FE) : FE := values.foldl (· * ·) 1

/-- `acc, acc·base, acc·base², …`, `count` terms. -/
def powersFrom (acc base : FE) : Nat → List FE
  | 0 => []
  | count + 1 => acc :: powersFrom (acc * base) base count

/-- `powers(base, count)` (`field.rs:258-267`). -/
def powers (base : FE) (count : Nat) : List FE := powersFrom 1 base count

/-- `eq_kernel(point)`: the `2^|point|` equality weights, the first coordinate the lowest bit
(`multilinear.rs:6-19`). -/
def eqKernel (point : List FE) : List FE :=
  point.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) [1]

/-- `eq_kernel` as an array (the same values; for the hot loops). -/
def eqKernelA (point : List FE) : Array FE :=
  point.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) #[1]

/-- One fold of `multilinear_eval`: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairs (r : FE) : List FE → List FE
  | a :: b :: rest => (a * (1 + r) + b * r) :: foldPairs r rest
  | _ => []

/-- `multilinear_eval(mle, point)` (`multilinear.rs:45-59`); `0` for an empty result. -/
def multilinearEval (mle point : List FE) : FE :=
  (point.foldl (fun cur r => foldPairs r cur) mle).headD 0

/-- The bit length of a natural number, `0` at `0`. -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- `log2_ceil(value)` (`multilinear.rs:61-63`). -/
def log2Ceil (value : Nat) : Nat := bitLength (value - 1)

/-- `eq_eval(left, right) = Π (1 + x + y)` (`multilinear.rs:70-77`). -/
def eqEval (left right : List FE) : FE :=
  (List.zipWith (fun x z => 1 + x + z) left right).foldl (· * ·) 1

/-- `dot(left, right) = Σ x·y` (`multilinear.rs:79-86`). -/
def dot (left right : List FE) : FE :=
  (List.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `padding_weight(point, n)`: the multilinear extension of `[z ≥ n]` (`multilinear.rs:88-96`). -/
def paddingWeight (point : List FE) (n : Nat) : FE :=
  (1 + eOfNat ((n >>> point.length) % 2)) *
    point.zipIdx.foldl (fun pad (r, k) =>
      let b := eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) 1

/-- `index_mle(point)`: `Π (1 + r_i·(1 + g^(2^i)))` (`multilinear.rs:98-107`). -/
def indexMleFrom (generatorPower : FE) : List FE → FE → FE
  | [], acc => acc
  | r :: rs, acc => indexMleFrom (generatorPower ^ 2) rs (acc * (1 + r * (1 + generatorPower)))

/-- `index_mle(point)` (`multilinear.rs:98-107`). -/
def indexMle (point : List FE) : FE := indexMleFrom gen point 1

/-- `poly_eval(coefficients, point)`: Horner, constant first (`multilinear.rs:109-112`). -/
def polyEval (coefficients : List FE) (point : FE) : FE :=
  coefficients.foldr (fun c acc => acc * point + c) 0

/-- `selector_point(selector, length)`: the low `length` bits of `selector` as `0/1`
(`multilinear.rs:146-148`). -/
def selectorPoint (selector length : Nat) : List FE :=
  (List.range length).map fun bit => eOfNat ((selector >>> bit) % 2)

/-! ## Placements and stacked claims (`LeanVmVerifier.lean:587-616, 1005-1053`) -/

/-- Where a block sits in a commitment's cube: a claim's point fills the low `variableCount`
coordinates, the bits of `index` fix the rest (`Placement`, `multilinear.rs:114-148`). -/
structure Placement where
  /-- The coordinates the block's own point fills. -/
  variableCount : Nat
  /-- The selector whose bits fix the other coordinates. -/
  index : Nat
  deriving Inhabited, DecidableEq, Repr

/-- `Placement::stack_point` (`multilinear.rs:122-125`). -/
def Placement.stackPoint (p : Placement) (point : List FE) (stackLog : Nat) : List FE :=
  point ++ selectorPoint (p.index >>> p.variableCount) (stackLog - p.variableCount)

/-- `Placement::eq_above` (`multilinear.rs:127-131`). -/
def Placement.eqAbove (p : Placement) (point : List FE) : FE :=
  eqEval (selectorPoint (p.index >>> p.variableCount) (point.length - p.variableCount))
    (point.drop p.variableCount)

/-- A claim on the stack: its weight on the stack's cube and its value (`StackClaim`,
`lib.rs:119-120`). -/
abbrev StackClaim : Type := (List FE → FE) × FE

/-- A claim on a block of a commitment: `Σ_u W(u)·f(index + u) = value` over the block's
`variableCount` variables. A column claim at a point `z` has `W = eq(z, ·)`. -/
structure BlockClaim where
  /-- The block. -/
  block : Placement
  /-- The weight over the block's own variables. -/
  weight : List FE → FE
  /-- The claimed value. -/
  value : FE

/-- A column claim: the block's multilinear extension at `z` is `v`. -/
def BlockClaim.point (block : Placement) (z : List FE) (v : FE) : BlockClaim :=
  ⟨block, eqEval z, v⟩

/-- The claim on the stack (leanVM `ColumnClaim.onStack`, `ringSwitchClaim`): the block's weight
times the selector of the coordinates above it. -/
def BlockClaim.onStack (c : BlockClaim) : StackClaim :=
  (fun x => c.block.eqAbove x * c.weight (x.take c.block.variableCount), c.value)

/-! ## Polynomial forms (`Form`, `LeanVmVerifier.lean:618-656`) -/

/-- A polynomial of degree at most two in a table's columns: monomials with coefficients. -/
structure Form where
  /-- The monomials (sorted column indices), each with its coefficient. -/
  terms : List (List Nat × FE) := []
  deriving Inhabited

/-- Add `c` into the coefficient of `m`. -/
def addTerm : List (List Nat × FE) → List Nat → FE → List (List Nat × FE)
  | [], m, c => [(m, 0 + c)]
  | (m', c') :: rest, m, c => if m' = m then (m', c' + c) :: rest else (m', c') :: addTerm rest m c

/-- `Form::add_scaled`: add `weight · other`. -/
def Form.addScaled (f other : Form) (weight : FE) : Form :=
  ⟨other.terms.foldl (fun acc t => addTerm acc t.1 (weight * t.2)) f.terms⟩

/-- `Form::evaluate`: `Σ c · Π column(i)`. -/
def Form.value (f : Form) (column : Nat → FE) : FE :=
  sumE (f.terms.map fun t => t.1.foldl (fun acc i => acc * column i) t.2)

/-- `constant(value)`. -/
def Form.const (value : FE) : Form := ⟨[([], value)]⟩

/-- `col(index, exponent)`: `g^exponent · x_index`. -/
def Form.col (index : Nat) (exponent : Nat := 0) : Form := ⟨[([index], gpow exponent)]⟩

/-! ## The stream reader -/

/-- The reader's cursor. -/
structure RS where
  /-- The byte offset of the next trace entry in `Σ`. -/
  ent : Nat
  /-- The message bytes of the next entry read so far. -/
  msg : Nat
  /-- Every check so far held. -/
  ok : Bool
  deriving Inhabited, Repr

/-- The reader monad: the stream, and the cursor. -/
abbrev DM := ReaderT ByteArray (StateM RS)

/-- The little-endian lane at byte `o` (`get!`: 0 beyond the end; `Σ`'s length is fixed). -/
def laneAt (b : ByteArray) (o : Nat) : UInt64 :=
  let g (i : Nat) : UInt64 := (b.get! (o + i)).toUInt64 <<< (8 * i).toUInt64
  g 0 ||| g 1 ||| g 2 ||| g 3 ||| g 4 ||| g 5 ||| g 6 ||| g 7

/-- The `K` word at byte `o`. -/
@[inline] def kAt (b : ByteArray) (o : Nat) : FK := ⟨laneAt b o⟩

/-- The `E` scalar at byte `o`: three lanes `c₀ ‖ c₁ ‖ c₂` (BLUEPRINT §2.1). -/
@[inline] def feAt (b : ByteArray) (o : Nat) : FE := ⟨kAt b o, kAt b (o + 8), kAt b (o + 16)⟩

/-- The cursor after `q₀` and the seed: the first schedule entry, at byte
`1 + (8 + 7 + 32) + (8 + seedLen + 32)` (5,736 for the 5,624-byte header). -/
def RS.start : RS := ⟨1 + 47 + (8 + (32 + headerBytes - 8) + 32), 0, true⟩

/-- The byte offset in `Σ` of header byte `j ≥ 8` (in the seed query, after `a₀`). -/
def headerAt (j : Nat) : Nat := 1 + 47 + 8 + 32 + (j - 8)

namespace DM

/-- Record a check. The condition comes first, so it is computed even after an earlier check
failed: `F`'s work is the same on every stream (no short cut through `&&`). -/
@[inline] def require (c : Bool) : DM Unit := modify fun s => { s with ok := c && s.ok }

/-- The next prover scalar. -/
@[inline] def readE : DM FE := fun b s => (feAt b (s.ent + 40 + s.msg), { s with msg := s.msg + 24 })

/-- The next `n` prover scalars. -/
def readEs : Nat → DM (List FE)
  | 0 => pure []
  | n + 1 => do
    let x ← readE
    let xs ← readEs n
    pure (x :: xs)

/-- Skip `n` message bytes (a cap: the driver checks the openings against it). -/
@[inline] def skip (n : Nat) : DM Unit := modify fun s => { s with msg := s.msg + n }

/-- The answer of the next FS entry, which follows its message; move to the entry after it. -/
@[inline] def answerAt : DM Nat := fun _ s => (s.ent + 40 + s.msg, { s with ent := s.ent + 72 + s.msg, msg := 0 })

/-- One challenge: the next FS answer's lanes 0–2 as an `E` element. -/
@[inline] def sampleE : DM FE := do
  let o ← answerAt
  let b ← read
  pure (feAt b o)

/-- `n` challenges. -/
def samples : Nat → DM (List FE)
  | 0 => pure []
  | n + 1 => do
    let x ← sampleE
    let xs ← samples n
    pure (x :: xs)

/-- The positions of an oracle: `⌈t/8⌉` answers, 8 bit fields of `height` bits each, low first
(BLUEPRINT §2.2; leanVM `sample_queries` draws `192 / depth` per sample instead). -/
def positionsAux (h : Nat) : (n rem : Nat) → DM (List Nat)
  | 0, _ => pure []
  | n + 1, rem => do
    let x ← sampleE
    let bits := eToNat x
    let cnt := min positionsPerAnswer rem
    let ps := (List.range cnt).map fun j => (bits >>> (j * h)) % 2 ^ h
    let rest ← positionsAux h n (rem - cnt)
    pure (ps ++ rest)

/-- The positions of the oracle of level `L`. -/
def positionsR (L : Level) : DM (List Nat) :=
  positionsAux L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) L.t

/-- The proof of work holds on the challenge `c`: its top `g` bits (of `192`) are zero, i.e.
`eToNat c < 2^(192 − g)` (LvmWhirProg `powOK`; for `g ≤ 64`, lane 2 `< 2^(64 − g)`). -/
def powOKR (g : Nat) (c : FE) : Bool := decide (eToNat c < 2 ^ (192 - g))

/-- Before a level's proof of work (PI-GRIND; LvmWhirProg `grindPre`): the separating challenge
(it absorbs the cap or the final; its value is unused) and the nonce. Nothing at `g = 0`. -/
def grindPreR (g : Nat) : DM Unit :=
  if g = 0 then pure () else do
    let _ ← sampleE
    let _ ← readE
    pure ()

/-- A level's proof of work (PI-GRIND; LvmWhirProg `powCheck`): the PoW challenge (it absorbs the
nonce), its top `g` bits zero. Nothing at `g = 0`. -/
def powCheckR (g : Nat) : DM Unit :=
  if g = 0 then pure () else do
    let c ← sampleE
    require (powOKR g c)

/-- The openings of the oracle of level `L` at `t` positions: the offsets in `Σ` of the rows
(each leaf entry's query), the node entries skipped. No message may be pending. -/
def openingAux (L : Level) : Nat → DM (List Nat)
  | 0 => pure []
  | n + 1 => do
    let o ← fun _ s => (s.ent + 8, { s with ent := s.ent + 40 + L.row + 104 * L.path })
    let rest ← openingAux L n
    pure (o :: rest)

/-- The rows of the oracle of level `L`. -/
def openingR (L : Level) : DM (List Nat) := do
  modify fun s => { s with ok := s.ok && s.msg == 0 }
  openingAux L L.t

end DM

/-- Run a reader on a stream from the start; its value and whether every check held. -/
def DM.runOn {α : Type} (m : DM α) (sig : ByteArray) : α × RS := (m sig).run RS.start

end Lvm
