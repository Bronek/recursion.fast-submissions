-- New for lvm (WP-11b-QL): the Q_link program (BLUEPRINT §4.6), written with LvmQBuild.
import LvmQLinkPlan
import LvmQLinkGadgets

/-!
# Q_link: the stream is a trace of the schedule

Inputs (`Layout`): the stream lane `j` is the `K` cell `sb + j`; the node flag `fg`; the static
lane-check table **QLT** (`qt`, three cells per entry: `g^e₁`, `g^e₂`, `v`); the position bits
(`bb`, per opening a region of `H` cells per position, positions padded to their chunks); the
positions' BITS fields (`fl`: per position its low and its high field, A20).

Program (`qlink`), few loop blocks (A20: piece count binds):
0. the **position cells** (`posLoop`, A20): position `g` (all openings' positions in order) is the sum
   of its two BITS fields, `x_g = lo_g + hi_g` (`hi_g = 0` unless the position crosses a lane), the
   `K` cells `pt.k + g` that `Q_arith` reads (`eOfNat q`);
1. a **step array** (`stepArr`): `2^K` copies of the flag, then `2^K` zeros; a chunk of `r` real
   positions out of `2^a` is gated by `Z[2^K − r + j]`;
2. **the QLT loop** (`qltLoop`) over the table (`qltData`): lanes 0 and 1 (the constants), every
   FS entry (its length lane, and its first four lanes against its state entry's answer), and the
   last sponge block's padding lanes (WP-8's `PadOk`);
3. per opening, per position chunk: **cap loops** (the leaf's length lane; the last answer of the
   path against the cap node read at the address the cap bits give) and, per level chunk, **node
   loops** (the node's length lane; the previous answer in the half the position bit selects).

The soundness theorem is `LvmQLinkSound.qlink_sound`.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-! ## The sponge padding (WP-8's `PadOk`, `padAt`, `nBlk`, verbatim, `rate = 136`) -/

/-- The number of Keccak-256 blocks of an `L`-byte message. -/
def nBlk (L : Nat) : Nat := L / 136 + 1

/-- The padding byte at offset `p` of a padded `L`-byte message (WP-8's `padAt`). -/
def padAt (L p : Nat) : UInt8 :=
  if p = L then (if L % 136 = 136 - 1 then 0x81 else 0x01)
  else if p % 136 = 136 - 1 then 0x80 else 0

/-- **The padding bytes of the stream are pinned** (WP-8's `PadOk` on the stream's bytes). -/
def PadOkB (B : List UInt8) (L : Nat) : Prop := ∀ q, L ≤ q → q < 136 * nBlk L → B.getD q 0 = padAt L q

/-- Lane `q` of the padding, as a number. -/
def padLane (L q : Nat) : Nat := ofLE ((List.range 8).map fun b => padAt L (8 * q + b))

/-! ## Layout and static data -/

/-- Where Q_link's inputs are. -/
structure Layout where
  /-- Stream lane `j` is the `K` cell `sb + j`. -/
  sb : Nat
  /-- The node flag cell. -/
  fg : Nat
  /-- The QLT table: entry `k` at cells `qt + 3k + {0, 1, 2}`. -/
  qt : Nat
  /-- The position bits: per opening, `H` cells per (padded) position. -/
  bb : Nat
  /-- `readd` region: the stream cells `[sb, sb + 2^m)`. -/
  m : Nat
  /-- The step array has `2^K` flags then `2^K` zeros. -/
  K : Nat
  /-- The QLT loop has `2^aQ` iterations. -/
  aQ : Nat
  /-- The positions' BITS fields: position `g`'s low field at `fl + g`, its high field at
  `fl + 2^pa + g`. -/
  fl : Nat
  /-- The positions loop has `2^pa` iterations. -/
  pa : Nat
  deriving Repr, Inhabited

/-- The positions chunks: the largest power of two, then the rest padded to a power of two. -/
def pchunks (t : Nat) : List (Nat × Nat) :=
  if t = 2 ^ t.log2 then [(0, t.log2)] else [(0, t.log2), (2 ^ t.log2, (t - 2 ^ t.log2 - 1).log2 + 1)]

/-- The positions an opening's bit region holds (its chunks, padded). -/
def padT (t : Nat) : Nat := ((pchunks t).map fun c => 2 ^ c.2).sum

/-- The QLT entries `(e₁, e₂, v)`: lanes 0, 1; every FS entry; the padding lanes. -/
def qltEntries (p : Params) (lay : Layout) : List (Nat × Nat × Nat) :=
  [(lay.sb, lay.sb + 1, lane0C), (lay.sb + 1, lay.sb + 2, lane1C)] ++
  ((plan p).zipIdx.filterMap fun x => match x.1.k with
    | .fs st => some (lay.sb + eLane p x.2, lay.sb + ansLane p st, x.1.len)
    | _ => none) ++
  ((List.range (17 * nBlk (hashedLen p) - hashedLen p / 8)).map fun k =>
    let q := hashedLen p / 8 + k
    (lay.sb + q, lay.sb + q + 1, padLane (hashedLen p) q))

/-- The QLT entries padded to `2^aQ` with copies of the first. -/
def qltPadded (p : Params) (lay : Layout) : List (Nat × Nat × Nat) :=
  qltEntries p lay ++ List.replicate (2 ^ lay.aQ - (qltEntries p lay).length) (lay.sb, lay.sb + 1, lane0C)

/-- The table cells of entries: per entry `g^e₁, g^e₂, v`. -/
def tblOf : List (Nat × Nat × Nat) → List FK
  | [] => []
  | e :: l => Build.gpow e.1 :: Build.gpow e.2.1 :: kOf e.2.2 :: tblOf l

/-- **The QLT input cells**: per entry `g^e₁, g^e₂, v`. -/
def qltData (p : Params) (lay : Layout) : List FK := tblOf (qltPadded p lay)

/-! ## The program -/

/-- The step array: `2^K` copies of the gate cell, then `2^K` zeros; returns its first cell. -/
def stepArr (K : Nat) (g : Cell) : BM Nat := do
  let pt ← getPtr
  let _ ← loop [K] [⟨.lin 0 0, .K, [g.opd, g.opd]⟩]
  let _ ← loop [K] [⟨.lin 1 0, .K, [g.opd, g.opd]⟩]
  pure pt.k

/-- The real positions of chunk `(s, a)` of an opening of `t` positions. -/
def realCount (t s a : Nat) : Nat := min (2 ^ a) (t - s)

/-- The loops of one opening (`zo` the step array, `bo` the opening's bit region). -/
def openLoops (p : Params) (lay : Layout) (zo bo : Nat) (o : OpenInfo) : BM Unit := do
  let L := o.L
  let ℓO := eLane p o.i0
  let Sj := posStride L
  let capL := eLane p o.ce + 1 + o.co / 8
  let _ ← seqAll ((pchunks L.t).map fun c => do
    let gz := zo + 2 ^ lay.K - realCount L.t c.1 c.2
    capLoop [c.2] (lay.sb + ℓO + Sj * c.1) L.row (lay.sb + ℓO + Sj * c.1 + slotOff L L.path + 9)
      (lay.sb + capL) lay.sb lay.m [Sj] (bo + L.height * c.1 + L.path) [L.height] (L.height - L.path) gz [1]
    let _ ← seqAll ((chunks L.path).map fun d =>
      nodeLoop [d.2, c.2] (lay.sb + ℓO + Sj * c.1 + slotOff L (d.1 + 1))
        (lay.sb + ℓO + Sj * c.1 + slotOff L (d.1 + 1) + 1) (lay.sb + ℓO + Sj * c.1 + slotOff L (d.1 + 1) + 5)
        (lay.sb + ℓO + Sj * c.1 + slotOff L (d.1 + 1) - 4) [13, Sj]
        (bo + L.height * c.1 + d.1) [1, L.height] gz [0, 1])
    pure ())
  pure ()

/-- **The position cells** (A20): `2^a` rows `x_g = lo_g + hi_g`, the low fields from `lo`, the high
fields from `hi`. -/
def posLoop (a lo hi : Nat) : BM LoopOut :=
  loop [a] [⟨.lin 1 0, .K, [.abs ⟨.K, lo, [1]⟩, .abs ⟨.K, hi, [1]⟩]⟩]

/-- The index of position `j` of opening `k` among all positions (openings in order). -/
def posIdx (p : Params) (k j : Nat) : Nat := (((opens p).take k).map fun o => o.L.t).sum + j

/-- The bit region of opening `k` (the openings before it, padded). -/
def bitBase (p : Params) (lay : Layout) (k : Nat) : Nat :=
  lay.bb + (((opens p).take k).map fun o => padT o.L.t * o.L.height).sum

/-- Q_link after the position cells. -/
def qlinkCore (p : Params) (lay : Layout) : BM Unit := do
  let zo ← stepArr lay.K (kc lay.fg)
  qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg)
  let _ ← seqAll ((List.range (opens p).length).map fun k =>
    openLoops p lay zo (bitBase p lay k) ((opens p).getD k default))
  pure ()

/-- **Q_link**: the position cells (at the start pointer's `K` cells), then the checks. -/
def qlink (p : Params) (lay : Layout) : BM Unit := do
  let _ ← posLoop lay.pa lay.fl (lay.fl + 2 ^ lay.pa)
  qlinkCore p lay

end Lvm.QLink
