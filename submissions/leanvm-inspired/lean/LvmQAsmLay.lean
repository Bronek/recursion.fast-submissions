-- New for lvm (WP-16a): the input map of the assembled node program (BLUEPRINT A19) and Q_link's
-- position `BITS` classes (WP-11b-QL §2, A20).
import LvmQLinkMain
import LvmSigBits

/-!
# The input map and the position `BITS` classes

The node program's `K` input cells, in order (every region an input array, the arrays tiling
`[0, nK)`, WP-9b's `inOkB`):

| region | cells | array |
|---|---|---|
| stream `Σ` (lane `j` at `j`) | `17·2^rl` | 17-bundle, stride 17, aliased on `C_rec` columns 0–16 |
| `σ'` (`I.sg`) | `2^10` | aliased on `C_rec` column 17 |
| `KS` messages above `R` (`I.xs`) | `17·2^9` | 17-bundle, aliased on `KS`'s `X` columns |
| `KS` digests above `R` (`I.ys`) | `4·2^9` | 4-bundle, aliased on `KS`'s `Y` lanes 0–3 |
| trace digest (`I.md`) | `4` | 4-bundle `τ = 0`, `KS` row `B − 1` |
| `PUB` (`pb`) | `2^10` | public: the header's 615 lanes (`b, vk, c_L, s, n, h, σ_leaf`) |
| `QLT` (`qt`) | `2^aQT` | public: Q_link's static table `qltData` |
| `BITS` outputs (`ob`) | `2^bo` | written: Q_sig's regions, the position bits, fields and spares, `s'`'s bits, the PoW fields, the lane classes' spares (`nsB … spEnd`) |

`Q_sig`'s flag, `vk`, `c_L`, `σ_leaf` are `PUB` lanes `0`, `1`, `5`, `18`; Q_link's flag is `PUB`
lane `0`. The position classes (`posSpecs`; lvm2 EV-DIET B: one class per answer lane, shared by all
openings): an opening's row per positions answer and lane `l` writes the bits of the lane that belong to
positions (`bit`, into Q_link's bit region, the form of `LvmQLinkBits.PosBits`; every padded position of
Q_link's bit region, `nRows`) and the fields of the positions that start or end in the lane (`fld`, A20:
`lo` at `fl + g`, `hi` at `fl + 2^pa + g`; positions past `t` write two spare cells, bits past the padded
region spare cells, `spOf`): its `laneOuts`. Lane `l`'s class has the rows of every opening that uses the
lane (in `opens` order) and the union of their outputs (`lnOuts`); a row's output that is not one of its
opening's goes to a spare cell of its own (`posOc`, the region `nsB` after the PoW fields).
-/

set_option autoImplicit false

namespace Lvm.QAsm

open Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.Bits Lvm.BitsTab

/-- The configuration of a parameter set's node program. -/
structure QCfg where
  /-- The parameter record. -/
  p : Params
  /-- `log₂` of `C_rec`'s rows (`R = 2^rl`). -/
  rl : Nat
  /-- The child's chain-length bound `n' ≤ 2^ln` (`logN`). -/
  ln : Nat
  /-- Q_link's QLT loop (`2^aQ` entries), step array (`2^K`), `readd` region (`2^m`), positions (`2^pa`). -/
  aQ : Nat
  K : Nat
  m : Nat
  pa : Nat
  /-- The QLT array's log-height (`3·2^aQ ≤ 2^aQT`). -/
  aQT : Nat
  /-- The BITS output region's log-size. -/
  bo : Nat

/-- `P20`'s node program. -/
def cfg20 : QCfg := ⟨P20, 14, 20, 11, 8, 18, 10, 13, 15⟩

/-- `P8`'s node program (the test parameter set; `readd` region 2^17 lanes: the stream passes 2^16). -/
def cfg8 : QCfg := ⟨P8, 13, 9, 11, 5, 17, 8, 13, 16⟩

section Regions

variable (C : QCfg)

/-- The stream's cells. -/
def nStream : Nat := 17 * 2 ^ C.rl
/-- `σ'`. -/
def sgB : Nat := nStream C
/-- The `KS` messages above `R`. -/
def xsB : Nat := sgB C + 2 ^ 10
/-- The `KS` digests above `R`. -/
def ysB : Nat := xsB C + 17 * 2 ^ 9
/-- The trace digest. -/
def mdB : Nat := ysB C + 4 * 2 ^ 9
/-- `PUB`. -/
def pbB : Nat := mdB C + 4
/-- `QLT`. -/
def qtB : Nat := pbB C + 2 ^ 10
/-- The `BITS` outputs. -/
def obB : Nat := qtB C + 2 ^ C.aQT
/-- The `K` input cells. -/
def nK : Nat := obB C + 2 ^ C.bo

/-! Q_sig's output regions (sizes as `SigRegLt`), then the position bits, fields and spares (then `s'`'s
bits `bsB`, the PoW fields `pwB` and the lane classes' spares `nsB`, below). -/
def biB : Nat := obB C
def bdB : Nat := biB C + 18
def bcB : Nat := bdB C + 256
def bxB : Nat := bcB C + 10
def beB : Nat := bxB C + 3192
def bpB : Nat := beB C + 1064
def bhB : Nat := bpB C + 256
def bclB : Nat := bhB C + 8
def blsB : Nat := bclB C + 8
def bnB : Nat := blsB C + 8
/-- The position bits (Q_link's `bb`). -/
def bbB : Nat := bnB C + C.ln + 5
/-- The position bit region's size (every opening's padded positions, `H` bits each). -/
def bbN : Nat := ((opens C.p).map fun o => padT o.L.t * o.L.height).sum
/-- The position fields (Q_link's `fl`). -/
def flB : Nat := bbB C + bbN C
/-- The spare cells (fields of the positions past `t` in an opening's last answer). -/
def spB : Nat := flB C + 2 * 2 ^ C.pa

/-- **Q_link's layout** in the node program. -/
def lay : Layout := ⟨0, pbB C, qtB C, bbB C, C.m, C.K, C.aQ, flB C, C.pa⟩

/-- **Q_sig's input cells** in the node program. -/
def sigIn : SigIn where
  flag := pbB C
  vk := pbB C + 1
  cL := pbB C + 5
  sl := pbB C + 18
  hd := 11
  sg := sgB C
  md := mdB C
  ys := ysB C
  yc := ysB C + 4 * 430
  yls := ysB C + 4 * 447
  yns := ysB C + 4 * 448
  bi := biB C
  bd := bdB C
  bc := bcB C
  bx := bxB C
  be := beB C
  bp := bpB C
  bn := bnB C
  bh := bhB C
  bcl := bclB C
  bls := blsB C
  xs := xsB C
  ln := C.ln

end Regions

/-! ## The position classes -/

/-- An opening's positions answers. -/
def nAns (o : OpenInfo) : Nat := (o.L.t + 7) / 8

/-- The rows of an opening's position classes: every padded position (Q_link's bit region holds
`padT t` positions; the padded chunks' loops read their bits too, INB), 8 per row. Rows past `nAns`
read the stream lanes after the positions answers (any word: their bits are bits). -/
def nRows (o : OpenInfo) : Nat := (padT o.L.t + 7) / 8

/-- The fields of position `i < 8` of an answer (`s = i·H`): `(lane, z, m, d)` of `lo` and of `hi`. -/
def fields (H i : Nat) : (Nat × Nat × Nat × Nat) × (Nat × Nat × Nat × Nat) :=
  let s := i * H
  let m₁ := if s / 64 = (s + H - 1) / 64 then H - 1 else 64 - s % 64
  ((s / 64, s % 64, m₁, 0), ((s + m₁) / 64, (s + m₁) % 64, H - m₁, m₁))

/-- The field outputs of lane `l`'s row: the fields of the positions with a part in the lane (`lo`
before `hi`, positions in order), tagged `(out, kind, i)`, kind `1` field `lo` of position `i`, `2` its
`hi`. -/
def laneFlds (H l : Nat) : List (BOut × Nat × Nat) :=
  (List.range 8).flatMap fun i =>
    let f := fields H i
    (if f.1.1 = l then [(.fld f.1.2.1 f.1.2.2.1 f.1.2.2.2, 1, i)] else []) ++
    (if f.2.1 = l then [(.fld f.2.2.1 f.2.2.2.1 f.2.2.2.2, 2, i)] else [])

/-- The outputs of lane `l`'s row: the bits `n ∈ [64 l, min (64 l + 64) (8 H))`, then the fields
(`laneFlds`). Each output is tagged: `(out, kind, n or i)` with kind `0` bit `n`, `1` field `lo` of
position `i`, `2` its `hi`. -/
def laneOuts (H l : Nat) : List (BOut × Nat × Nat) :=
  ((List.range 64).filter (fun z => 64 * l + z < 8 * H)).map (fun z => (.bit z, 0, 64 * l + z)) ++
    laneFlds H l

/-- The number of bit outputs of lane `l`'s row (`laneOuts`' first outputs). -/
def laneBits (H l : Nat) : Nat := min 64 (8 * H - 64 * l)

/-- The lanes an opening's position bits occupy (`8 H ≤ 192`: lanes `0..2`). -/
def nLanes (H : Nat) : Nat := (8 * H + 63) / 64

/-- An opening's spare cells: two fields per row position past `t`, the bits of the row positions past
`padT t`. -/
def spOf (o : OpenInfo) : Nat := 2 * (8 * nRows o - o.L.t) + o.L.height * (8 * nRows o - padT o.L.t)

/-- The spare cells before opening `k`. -/
def spBefore (p : Params) (k : Nat) : Nat := (((opens p).take k).map spOf).sum

/-- The cell of output `(kind, v)` of answer `x` of opening `k` (`o` its info). -/
def posCell (C : QCfg) (k : Nat) (o : OpenInfo) (x : Nat) : BOut × Nat × Nat → Nat
  | (_, 0, n) =>
    let j := 8 * x + n / o.L.height
    if j < padT o.L.t then bitBase C.p (lay C) k + o.L.height * j + n % o.L.height
    else spB C + spBefore C.p k + 2 * (8 * nRows o - o.L.t) + o.L.height * (j - padT o.L.t) + n % o.L.height
  | (_, kind, i) =>
    let j := 8 * x + i
    if j < o.L.t then flB C + (if kind = 1 then 0 else 2 ^ C.pa) + posIdx C.p k j
    else spB C + spBefore C.p k + 2 * (j - o.L.t) + (kind - 1)

/-- `⌈log₂ n⌉`. -/
def clog2 (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

/-- The bit outputs of the child's chain start `s'` (lvm2 S2: the wiring target's `⟨ω, Pad43(s')⟩`):
256 cells after the spares, bit `z` of lane `l` at `bsB + 64 l + z`. -/
def bsB (C : QCfg) : Nat := spB C + spBefore C.p (opens C.p).length

/-- **The `s'` bit class** (lvm2 S2; replaces v1's byte shifts, which served only the deleted `CH`
start claims): 4 rows, row `l` reads the stream lane `hd + 9 + l` (the child's header lane `s_l`),
outputs its 64 bits (`.bit z`). -/
def sSpec (C : QCfg) (pl : Nat → Bool × Nat) : BSpec :=
  ⟨2, 4, (List.range 64).map BOut.bit, true, fun x => (sigIn C).hd + 9 + x, fun j x => bsB C + 64 * x + j, pl⟩

/-- The PoW fields (PI-GRIND): one `K` cell per opening after `s'`'s 256 bits. -/
def pwB (C : QCfg) : Nat := bsB C + 256

/-- **The PoW class** (PI-GRIND; T-Q step B): one row per opening `x` (`opens`: `C_rec`'s level, then
`C_main`'s), reading lane 2 of its PoW challenge's answer (the entry before its first positions entry) and
writing the field of its low `64 − g` bits at `pwB + x`: the circuit asserts that the lane equals it, so the
lane is below `2^(64−g)`. -/
def powSpec (C : QCfg) (pl : Nat → Bool × Nat) : BSpec :=
  ⟨clog2 (opens C.p).length, (opens C.p).length, [BOut.fld 0 (64 - C.p.grind) 0], true,
    fun x => ansLane C.p (((opens C.p).getD x default).pe - 1) + 2, fun _ x => pwB C + x, pl⟩

/-! ## The lane classes (lvm2 EV-DIET B)

Lane `l`'s class: the rows of every opening whose positions use lane `l` (`lnOps`, in `opens` order;
`nRows o` rows each), the outputs `lnOuts` (bits `0 … nb − 1`, `nb` the most bits any of them has in the
lane, then every field output of theirs once). Output `j` of a row of opening `k` goes to `posCell` of the
opening's output with the same word function (`laneOuts` has no two outputs with one word function), else
to the row's spare cell `sb + j − laneBits` (`posOc`): a row of `o` has `|lnOuts| − laneBits` spare cells
from `sb`, the openings' rows one after the other from `spBase l` (`posRowsAux`), the classes one after
the other from `nsB` (after the PoW fields). -/

/-- The openings whose positions use lane `l`, with their index (in `opens` order). -/
def lnOps (p : Params) (l : Nat) : List (Nat × OpenInfo) :=
  ((List.range (opens p).length).map fun k => (k, (opens p).getD k default)).filter
    fun ko => decide (l < nLanes ko.2.L.height)

/-- The number of lane classes: the most lanes an opening uses. -/
def nPosCls (C : QCfg) : Nat := ((opens C.p).map fun o => nLanes o.L.height).foldl max 0

/-- `u` appended unless present. -/
def addNew (a : List BOut) (u : BOut) : List BOut := if u ∈ a then a else a ++ [u]

/-- The bit outputs of lane `l`'s class: the most bits any of its openings has in the lane. -/
def lnBits (p : Params) (l : Nat) : Nat := ((lnOps p l).map fun ko => laneBits ko.2.L.height l).foldl max 0

/-- **Lane `l`'s class outputs**: `bit 0 … bit (lnBits − 1)`, then the field outputs of its openings,
each once, in order of first appearance. -/
def lnOuts (p : Params) (l : Nat) : List BOut :=
  (List.range (lnBits p l)).map BOut.bit ++
    (lnOps p l).foldl (fun a ko => (laneFlds ko.2.L.height l).foldl (fun a e => addNew a e.1) a) []

/-- The rows of a lane class from spare cell `b` on (`u` the class's outputs): per opening `(k, o)` of
`ops`, its rows `(k, o, x, sb)`, `x < nRows o`, `sb` the row's first spare cell (`u − laneBits` per row). -/
def posRowsAux (u l : Nat) : Nat → List (Nat × OpenInfo) → List (Nat × OpenInfo × Nat × Nat)
  | _, [] => []
  | b, (k, o) :: r =>
    (List.range (nRows o)).map (fun x => (k, o, x, b + x * (u - laneBits o.L.height l))) ++
      posRowsAux u l (b + nRows o * (u - laneBits o.L.height l)) r

/-- The spare cells of a lane class's rows (`posRowsAux`). -/
def spTot (u l : Nat) (ops : List (Nat × OpenInfo)) : Nat :=
  (ops.map fun ko => nRows ko.2 * (u - laneBits ko.2.L.height l)).sum

/-- The lane classes' spare cells: after the PoW fields. -/
def nsB (C : QCfg) : Nat := pwB C + (opens C.p).length

/-- Where lane class `l`'s spare cells start. -/
def spBase (C : QCfg) : Nat → Nat
  | 0 => nsB C
  | l + 1 => spBase C l + spTot (lnOuts C.p l).length l (lnOps C.p l)

/-- **Lane class `l`'s rows** `(k, o, x, sb)`. -/
def posRows (C : QCfg) (l : Nat) : List (Nat × OpenInfo × Nat × Nat) :=
  posRowsAux (lnOuts C.p l).length l (spBase C l) (lnOps C.p l)

/-- **Output `j`'s cell at a class row** `r = (k, o, x, sb)` of lane `l` (`U` the class's outputs): the
`posCell` of the opening's output with `U[j]`'s word function, else the spare cell `sb + j − laneBits`. -/
def posOc (C : QCfg) (l : Nat) (U : List BOut) (r : Nat × OpenInfo × Nat × Nat) (j : Nat) : Nat :=
  match (laneOuts r.2.1.L.height l).find? (fun e => e.1 == U.getD j (.bit 0)) with
  | some e => posCell C r.1 r.2.1 r.2.2.1 e
  | none => r.2.2.2 + (j - laneBits r.2.1.L.height l)

/-- **Lane class `l`**: row `y` is the class row `r = posRows[y]`, reading the opening's answer lane
`ansLane (pe + x) + l`, writing `lnOuts` to `posOc`; placed by `bpl l`. -/
def posSpec (C : QCfg) (bpl : Nat → Nat → Bool × Nat) (l : Nat) : BSpec :=
  let U := lnOuts C.p l
  let R := posRows C l
  ⟨clog2 R.length, R.length, U, true, fun y => ansLane C.p ((R.getD y default).2.1.pe + (R.getD y default).2.2.1) + l,
    fun j y => posOc C l U (R.getD y default) j, bpl l⟩

/-- **The position classes**: one per lane `l < nPosCls` (`posSpec`). -/
def posSpecs (C : QCfg) (bpl : Nat → Nat → Bool × Nat) : List BSpec :=
  (List.range (nPosCls C)).map (posSpec C bpl)

section
variable (C : QCfg) (bpl : Nat → Nat → Bool × Nat) (l : Nat)
theorem posSpec_τ : (posSpec C bpl l).τ = clog2 (posRows C l).length := rfl
theorem posSpec_n : (posSpec C bpl l).n = (posRows C l).length := rfl
theorem posSpec_outs : (posSpec C bpl l).outs = lnOuts C.p l := rfl
theorem posSpec_rd : (posSpec C bpl l).rd = true := rfl
theorem posSpec_wc (y : Nat) : (posSpec C bpl l).wc y =
    ansLane C.p (((posRows C l).getD y default).2.1.pe + ((posRows C l).getD y default).2.2.1) + l := rfl
theorem posSpec_oc (j y : Nat) : (posSpec C bpl l).oc j y = posOc C l (lnOuts C.p l) ((posRows C l).getD y default) j := by
  dsimp only [posSpec]
theorem posSpec_pl : (posSpec C bpl l).pl = bpl l := rfl
end

/-- The end of the lane classes' spare cells. -/
def spEnd (C : QCfg) : Nat := spBase C (nPosCls C)

end Lvm.QAsm
