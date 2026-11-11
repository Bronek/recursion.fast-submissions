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
| `BITS` outputs (`ob`) | `2^bo` | written: Q_sig's regions, the position bits, the position fields |

`Q_sig`'s flag, `vk`, `c_L`, `σ_leaf` are `PUB` lanes `0`, `1`, `5`, `18`; Q_link's flag is `PUB`
lane `0`. The position classes (`posSpecs`): per opening `k` and answer lane `l`, one `BITS` row per
positions answer: the bits of the lane that belong to positions (`bit`, into Q_link's bit region,
the form of `LvmQLinkBits.PosBits`; every padded position of Q_link's bit region, `nRows`) and the fields
of the positions that start or end in the lane (`fld`, A20: `lo` at `fl + g`, `hi` at `fl + 2^pa + g`;
positions past `t` write two spare cells, bits past the padded region spare cells, `spOf`).
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
def cfg8 : QCfg := ⟨P8, 12, 9, 10, 5, 17, 8, 12, 16⟩

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

/-! Q_sig's output regions (sizes as `SigRegLt`), then the position bits, fields and spares. -/
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

/-- The outputs of lane `l`'s row: the bits `n ∈ [64 l, min (64 l + 64) (8 H))`, then the fields of
the positions with a part in the lane (`lo` before `hi`, positions in order). Each output is tagged:
`(out, kind, n or i)` with kind `0` bit `n`, `1` field `lo` of position `i`, `2` its `hi`. -/
def laneOuts (H l : Nat) : List (BOut × Nat × Nat) :=
  ((List.range 64).filter (fun z => 64 * l + z < 8 * H)).map (fun z => (.bit z, 0, 64 * l + z)) ++
  (List.range 8).flatMap fun i =>
    let f := fields H i
    (if f.1.1 = l then [(.fld f.1.2.1 f.1.2.2.1 f.1.2.2.2, 1, i)] else []) ++
    (if f.2.1 = l then [(.fld f.2.2.1 f.2.2.2.1 f.2.2.2.2, 2, i)] else [])

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

/-- **The position classes**: per opening `k` and lane `l < nLanes H`, one row per answer. Class
`c` (in this order) is placed by `bpl c`. -/
def posSpecs (C : QCfg) (bpl : Nat → Nat → Bool × Nat) : List BSpec :=
  let cls := (List.range (opens C.p).length).flatMap fun k =>
    let o := (opens C.p).getD k default
    (List.range (nLanes o.L.height)).map fun l => (k, o, l)
  cls.zipIdx.map fun ((k, o, l), c) =>
    let outs := laneOuts o.L.height l
    ⟨clog2 (nRows o), nRows o, outs.map (·.1), true, fun x => ansLane C.p (o.pe + x) + l,
      fun j x => posCell C k o x (outs.getD j (.bit 0, 0, 0)), bpl c⟩

/-- The number of position classes. -/
def nPosCls (C : QCfg) : Nat :=
  ((List.range (opens C.p).length).map fun k => nLanes ((opens C.p).getD k default).L.height).sum

/-- The byte-shift outputs of the child's chain start `s'` (HAR's boundary claim `Pad43(s')`): 8 cells after
the spares, `shl 8` of lane `l` at `bsB + 2l`, `shr 56` at `bsB + 2l + 1`. -/
def bsB (C : QCfg) : Nat := spB C + spBefore C.p (opens C.p).length

/-- **The `s'` byte-shift class**: 4 rows, row `l` reads the stream lane `hd + 9 + l` (the child's header
lane `s_l`), outputs `shl 8`, `shr 56` (as Q_sig's `h'`/`c_L'` rows of WP-12b's class 4). -/
def sSpec (C : QCfg) (pl : Nat → Bool × Nat) : BSpec :=
  ⟨2, 4, [.shl 8, .shr 56], true, fun x => (sigIn C).hd + 9 + x, fun j x => bsB C + 2 * x + j, pl⟩

end Lvm.QAsm
