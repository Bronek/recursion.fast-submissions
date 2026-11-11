-- New for lvm (WP-11b-QL); the pattern is FR's A.5 `reassemble`
-- (rf-k/submissions/flock-recursive/lean/FRFormat.lean@8bff272b: a walk over the item sequence that
-- puts every absorbed message, opened row and sibling half back into the proof), re-cut for lvm's
-- driver: no fields, the body is the concatenation of the entries' contributions in trace order.
import LvmDriver

/-!
# The trace plan, `reassemble`, and what Q_link asserts (BLUEPRINT §2.2, §4.6)

The driver (`LvmDriver.drive`) asks a fixed sequence of queries. **The plan** (`plan p`) describes
the trace entry by entry, statically (no trace, no oracle): its class, its query length, and what
links it to earlier entries. It is computed by a walk over the schedule (`planItem`) that mirrors
`driveItems` item for item:

* `q0`: the 7 bytes `"lvm/1\0\0"`;
* `fs st`: a Fiat–Shamir query (the seed too): it starts with the answer of entry `st` (the
  current state; the seed's is `q₀`'s answer `a₀`), the rest is the message;
* `leaf`: an opened row;
* `node pe h j lvl cap`: the node query at level `lvl` of position `j` of an oracle whose positions
  come from the answers of entries `pe, pe + 1, …` (`h` bits each, 8 per answer, low first:
  `posVal`); the current node is its left half iff bit `lvl` of the position is `0`; on the last
  level `cap = some (ce, co, path)`: the answer must be the cap node `pos >> path`, the 32 bytes
  at `co + 32 · (pos >> path)` of entry `ce`'s query (the FS query that absorbed the cap).

`planItems` also accumulates a static flag `ok` (`PlanOk`): every opening finds its cap, follows
its own positions with nothing pending, has a path and a cap large enough for `pos >> path`, and
a leaf row within `queryCap`; the schedule ends with nothing pending. `decide` checks it per
parameter set.

* **`Good tr i e`**: entry `i` of `tr` has the plan's length and link (what Q_link asserts on the
  stream; `LinkOk p tr`: every entry is `Good`, and `tr` has the plan's length).
* **`contrib tr i e`**: the proof bytes entry `i` carries: an FS query its message (`q[32..]`), a
  leaf query the row, a node query the sibling (the right half iff the left half is the previous
  answer: the *compare rule*, equal to the position bit's choice on every `Good` entry).
* **`reassemble p tr`** = `'S' ‖ 0^7 ‖` the contributions in trace order (BLUEPRINT §2.2). The seed's
  contribution is the header from byte 8, so π's first 8 bytes are the only ones in no query
  (`parseOk` fixes them: `'S'`, zero padding).
-/

set_option autoImplicit false

namespace Lvm.Replay

open RecursionFast Lvm

/-! ## Bytes and entries -/

/-- The bytes of a byte array, as a list. -/
def bl (b : ByteArray) : List UInt8 := b.data.toList

/-- The empty entry (past the end of a trace). -/
def dflt : ByteArray × Digest := (ByteArray.empty, zeroDigest)

/-- Entry `i`'s query. -/
def qOf (tr : Trace) (i : Nat) : ByteArray := (tr.getD i dflt).1

/-- Entry `i`'s answer. -/
def aOf (tr : Trace) (i : Nat) : Digest := (tr.getD i dflt).2

/-- Position `j` of an oracle whose positions answers start at entry `pe`, `h` bits per position,
8 per answer, low first (the driver's `posLoop`). -/
def posVal (tr : Trace) (pe h j : Nat) : Nat := (answerBits (aOf tr (pe + j / 8)) >>> (j % 8 * h)) % 2 ^ h

/-! ## The plan -/

/-- What an entry is and what links it to earlier entries. -/
inductive EK where
  /-- The first query. -/
  | q0
  /-- A Fiat–Shamir query (or the seed) starting with entry `st`'s answer. -/
  | fs (st : Nat)
  /-- An opened row. -/
  | leaf
  /-- A node query (level `lvl`, position `j`, positions from entry `pe` on, `h` bits); on the last
  level the cap: entry, byte offset of the cap in its query, path length. -/
  | node (pe h j lvl : Nat) (cap : Option (Nat × Nat × Nat))
  deriving DecidableEq, Repr, Inhabited

/-- A planned entry: what it is, its query length. -/
structure PE where
  /-- What the entry is. -/
  k : EK
  /-- Its query's length in bytes. -/
  len : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The walk's state (mirrors the driver's `DSt`, with entry indices instead of values). -/
structure WS where
  /-- The next entry. -/
  i : Nat
  /-- Message bytes read since the last FS query. -/
  pend : Nat
  /-- The entry whose answer is the FS state. -/
  st : Nat
  /-- Caps read but not yet absorbed (newest first): ref, offset in the pending bytes, bytes. -/
  pcaps : List (Ref × Nat × Nat)
  /-- Absorbed caps (newest first): ref, entry, byte offset in its query, bytes. -/
  caps : List (Ref × Nat × Nat × Nat)
  /-- The first positions entry of the current oracle. -/
  pe : Nat
  /-- The oracle of the last positions item. -/
  posRef : Option Ref
  /-- Every static condition held so far. -/
  ok : Bool
  deriving Repr

/-- An FS query at entry `i` absorbs the pending caps. -/
def WS.settle (w : WS) : WS :=
  { w with caps := w.pcaps.map (fun c => (c.1, w.i, 32 + c.2.1, c.2.2)) ++ w.caps, pcaps := [] }

/-- The entries of an opening of level `L` at positions entries `pe`, cap `(ce, co)`. -/
def openPlan (L : Level) (pe ce co : Nat) : List PE :=
  (List.range L.t).flatMap fun j => ⟨.leaf, L.row⟩ :: (List.range L.path).map fun lvl =>
    ⟨.node pe L.height j lvl (if lvl + 1 = L.path then some (ce, co, L.path) else none), 64⟩

/-- **One item of the walk**: the entries it plans and the next state (`driveItems`, item for
item). -/
def planItem (p : Params) (w : WS) : Item → List PE × WS
  | .read m => ([], { w with pend := w.pend + eBytes * m })
  | .cap c r => ([], { w with pcaps := (r, w.pend, nodeBytes * 2 ^ c) :: w.pcaps,
                              pend := w.pend + nodeBytes * 2 ^ c })
  | .sample => ([⟨.fs w.st, 32 + w.pend⟩], { w.settle with i := w.i + 1, pend := 0, st := w.i })
  | .positions r =>
    let n := (p.level r).nPosQ
    ((List.range n).map (fun k => if k = 0 then ⟨.fs w.st, 32 + w.pend⟩ else ⟨.fs (w.i + k - 1), 32⟩),
      { w.settle with i := w.i + n, pend := 0, st := w.i + n - 1, pe := w.i, posRef := some r,
                      ok := w.ok && decide (1 ≤ n) })
  | .opening r =>
    let L := p.level r
    match w.caps.find? (·.1 == r) with
    | none => ([], { w with ok := false })
    | some (_, ce, co, nb) =>
      (openPlan L w.pe ce co,
        { w with i := w.i + L.t * (1 + L.path),
                 ok := w.ok && w.pend == 0 && w.pcaps.isEmpty && w.posRef == some r &&
                   decide (1 ≤ L.path) && decide (L.path ≤ L.height) &&
                   decide (nodeBytes * 2 ^ (L.height - L.path) ≤ nb) && decide (L.row ≤ queryCap) &&
                   decide (positionsPerAnswer * (L.nPosQ - 1) < L.t) && decide (L.t ≤ positionsPerAnswer * L.nPosQ) })

/-- The walk over a list of items. -/
def planItems (p : Params) : WS → List Item → List PE × WS
  | w, [] => ([], w)
  | w, it :: its =>
    let a := planItem p w it
    let b := planItems p a.2 its
    (a.1 ++ b.1, b.2)

/-- The walk's start: entry 2 (after `q₀` and the seed), state = the seed's answer. -/
def w0 : WS := ⟨2, 0, 1, [], [], 0, none, true⟩

/-- The walk over the schedule. -/
def planAll (p : Params) : List PE × WS := planItems p w0 (schedule p)

/-- **The plan**: `q₀`, the seed, then the schedule's entries. -/
def plan (p : Params) : List PE := ⟨.q0, 7⟩ :: ⟨.fs 0, seedLen⟩ :: (planAll p).1

/-- **The static conditions** of the plan (decided per parameter set). -/
def PlanOk (p : Params) : Prop :=
  (planAll p).2.ok = true ∧ (planAll p).2.pend = 0 ∧ (planAll p).2.pcaps = []

instance (p : Params) : Decidable (PlanOk p) := by unfold PlanOk; infer_instance

/-! ## What Q_link asserts, and what an entry carries -/

/-- **Entry `i` of `tr` meets its plan**: its query has the planned length, and its link. -/
def Good (tr : Trace) (i : Nat) (e : PE) : Prop :=
  (qOf tr i).size = e.len ∧
  match e.k with
  | .q0 => qOf tr i = q0Query
  | .fs st => (bl (qOf tr i)).take 32 = (aOf tr st).toList
  | .leaf => True
  | .node pe h j lvl cap =>
    (if (posVal tr pe h j >>> lvl) % 2 = 0 then (bl (qOf tr i)).take 32 else (bl (qOf tr i)).drop 32) =
        (aOf tr (i - 1)).toList ∧
      match cap with
      | none => True
      | some (ce, co, path) =>
        aOf tr i = Vector.ofFn fun x => (qOf tr ce).get! (co + nodeBytes * (posVal tr pe h j >>> path) + x.val)

/-- **The trace is a trace of the schedule** (BLUEPRINT §4.6, Q_link): the plan's length, and every
entry meets its plan. -/
def LinkOk (p : Params) (tr : Trace) : Prop :=
  tr.length = (plan p).length ∧ ∀ i < tr.length, Good tr i ((plan p).getD i default)

/-- **The proof bytes entry `i` carries**: an FS query its message, a leaf its row, a node query the
sibling: the right half if the left half is the previous answer (the current node), else the left
half. This *compare rule* (WP-13a's, so that the extractor needs no position bits) picks the half the
position bit does on every trace that meets its plan (`Good`): when both halves are the current
node they are equal. -/
def contrib (tr : Trace) (i : Nat) (e : PE) : List UInt8 :=
  match e.k with
  | .q0 => []
  | .fs _ => (bl (qOf tr i)).drop 32
  | .leaf => bl (qOf tr i)
  | .node .. =>
    if (bl (qOf tr i)).take 32 = (aOf tr (i - 1)).toList then (bl (qOf tr i)).drop 32 else (bl (qOf tr i)).take 32

/-- The contributions of the entries `i, i + 1, …` of the plan `P`. -/
def bodyFrom (tr : Trace) (P : List PE) (i : Nat) : List UInt8 :=
  (List.range' i (P.length - i)).flatMap fun k => contrib tr k (P.getD k default)

/-- The bytes of `π` before its body: `'S'` and seven zero bytes. -/
def hdr8 : List UInt8 := [0x53, 0, 0, 0, 0, 0, 0, 0]

/-- **`reassemble p tr`**: the proof the trace carries (BLUEPRINT §2.2): `'S' ‖ 0^7 ‖` every entry's
contribution in order. -/
def reassemble (p : Params) (tr : Trace) : ByteArray := ⟨(hdr8 ++ bodyFrom tr (plan p) 0).toArray⟩

end Lvm.Replay
