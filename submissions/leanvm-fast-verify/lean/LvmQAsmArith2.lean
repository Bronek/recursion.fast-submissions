-- New for lvm (HAR): the rest of Q_arith (`qarithRest`): phases 2–3 (bus, table sumcheck), the ring
-- switches and the claims, phases 8–9 (the stacked WHIR openings of `C_rec` and `C_main`).
import LvmQAsmArith2P47
import LvmQAsmHarBase
import LvmQAsmData20
import LvmQAsmData8
import LvmQAsmArith2Bus
import LvmQAsmArith2ClaimLink
import LvmQAsmArith2WhirP
import LvmQAsmArith2Tab
import LvmQAccSound
import LvmQAsmHarClaims

/-!
# Q_arith after phases 4–7 (`qarithRest`)

`LvmQAsmProg.qarith C = phases47 C >>= qarithRest C` (BLUEPRINT A19, A23). Phase families (owners
in `docs/lvm/stages/HAR.md`): bus/tables (`LvmQAsmArith2Bus*`, `LvmQAsmArith2Tab*`), rings and claims
(`LvmQAsmArith2Ring*`, `LvmQAsmArith2Claim*`), stacked WHIR (`LvmQAsmArith2Whir*`). `Q_acc` (phase
3b, A23) is AC-Q's.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.M3 Lvm.QAcc Lvm.QLink

/-- The placement record of a configuration (`P20`: `data20`, else `data8`). -/
def dataOf (C : QCfg) : QData := if C.rl = 14 then data20 else data8

/-- A placeholder cache: the circuit reads only the tables' shapes (`tabs_shape`). -/
def G0 : PG := cacheG (toProgram 0 0 (pure ()))

/-- `arrs` with empty public values (`PUB`, `QLT`): the same shapes (`arrsS_shape`), built without
`qltData` (4.5 s at `P20`). -/
def arrsS (C : QCfg) (D : QData) : List InArr :=
  let R := 2 ^ C.rl
  (List.range 17).map (fun l => ⟨.K, C.rl, l, 17, [(true, l * R)], fin D l, none⟩) ++
  [⟨.K, 10, sgB C, 1, [(true, 17 * R)], fin D 17, none⟩] ++
  (List.range 17).map (fun l => ⟨.K, 9, xsB C + l, 17, [(false, xOff C + l * R)], fin D (18 + l), none⟩) ++
  (List.range 4).map (fun l => ⟨.K, 9, ysB C + l, 4, [(false, ksY C l + R)], fin D (35 + l), none⟩) ++
  (List.range 4).map (fun l =>
    ⟨.K, 0, mdB C + l, 4, [(false, ksY C l + (spongeBlocks C.p - 1))], fin D (39 + l), none⟩) ++
  [pubArr 10 (pbB C) 1 (false, 0) (fin D 43) [],
   pubArr C.aQT (qtB C) 1 (false, 0) (fin D 44) [],
   ⟨.K, C.bo, obB C, 1, [(false, D.aval)], fin D 45, none⟩]

/-- The tables with empty public values and the placeholder cache (`tabs`' shapes). -/
def tabsS (C : QCfg) (D : QData) : List Tab := lvmTabsC G0 (plOf D) D.groups (arrsS C D) (aux C D)

/-- **The sumcheck tables' shapes** of the record `D` (the table phase is built from them;
`shapesOf_eq`: those of `tabs C G D pub`, any `G`, `pub`). -/
def shapesOf (C : QCfg) (D : QData) : List TShape :=
  (sumcheckTabs (tabsS C D)).map Tab.shape

/-- `fixCols`' (table, column) indices, on shapes (`fixColsR_idx`). -/
def fixIdx (S : List TShape) (pubTab : Nat) : List (Nat × Nat) :=
  S.zipIdx.flatMap fun x => x.1.cols.zipIdx.filterMap fun ci => match ci.1 with
    | some _ => none
    | none => if x.2 == pubTab && ci.2 == 0 then none else some (x.2, ci.2)

/-- `Q_acc`'s inputs from the table gadget's output (BLUEPRINT §12.5; AC-Q's `AccIn`), on the sumcheck
tables' shapes `S` (`shapesOf C D`). -/
def accInOf (C : QCfg) (S : List TShape) (tab : List (List Cell × List Cell)) (z : Cell) : AccIn where
  L := tabEnd S C.p.tableRounds (tabPos C.p) / 8
  dk := C.p.accLog
  la := C.p.accLog / 2
  τp := 10
  pb := pbB C
  rc := tablePointC tab
  ppt := (tab.getD C.p.pubTab default).1
  pv := (tab.getD C.p.pubTab default).2.getD 0 z
  fx := (fixIdx S C.p.pubTab).map fun ji => (tab.getD ji.1 default).2.getD ji.2 z

/-! ## Padding the record-dependent rows

The record `D` (groups, placements) is computed from the program, and the table phase is built from
`D`: per row shape the groups are the binary decomposition of the shape's total rows, so a few rows more
or less of a shape change the groups and the iteration `D ↦ mkData (QT C D)` need not settle. `withPad`
pads the rows `m` emits, per shape, to a rounded total (`roundUp6`, at most ≈ 3 % more) with dummy rows
of the shape that read only zero cells. -/

/-- Add `k` rows of shape `σ` to per-shape counts (shapes in order of first use). -/
def addCnt (σ : Shape) (k : Nat) : List (Shape × Nat) → List (Shape × Nat)
  | [] => [(σ, k)]
  | (σ', n) :: l => if σ' = σ then (σ', n + k) :: l else (σ', n) :: addCnt σ k l

/-- **Rows per shape** of segments: a straight-line row is one row, a loop block's template row
`2^lsize` rows. -/
def rowsByShape (δ : List Seg) : List (Shape × Nat) :=
  δ.foldl (fun acc s => match s with
    | .row r => addCnt r.shape 1 acc
    | .blk B => B.tpl.foldl (fun acc r => addCnt r.shape (2 ^ B.lsize) acc) acc) []

/-- `n` rounded up to a multiple of `2^e`, `e = log₂ n − 5` (`0` below 64). -/
def roundUp6 (n : Nat) : Nat :=
  let g := 2 ^ (n.log2 - 5)
  (n + g - 1) / g * g

/-- A dummy row of shape `σ` reading the zero cells `zK`, `zE` (none for `fixmul`, `readd`). -/
def padRow (zK zE : Cell) (σ : Shape) : Option Row :=
  let args := σ.args.map fun t => match t with
    | .K => zK.addr
    | .E => zE.addr
  match σ.kind with
  | .muladd => some ⟨.muladd, σ.ty, args⟩
  | .lin => some ⟨.lin 0 0, σ.ty, args⟩
  | .assert0 => some ⟨.assert0, .K, args⟩
  | .loadE => some ⟨.loadE, σ.ty, args⟩
  | _ => none

/-- The padding rows of per-shape counts `cs`. -/
def padSegs (zK zE : Cell) (cs : List (Shape × Nat)) : List Seg :=
  cs.flatMap fun x => match padRow zK zE x.1 with
    | some r => List.replicate (roundUp6 x.2 - x.2) (.row r)
    | none => []

/-- **`m`, then its rows padded per shape** (`roundUp6`) with dummy rows on the zero cells. -/
def withPad {α : Type} (zK zE : Cell) (m : BM α) : BM α := fun p =>
  let r := m p
  (r.1, r.2 ++ padSegs zK zE (rowsByShape r.2))

/-- The position cells of opening `k` (`C_rec` 0, `C_main`'s levels 1…): Q_link's `pt.k + posIdx p k j`. -/
def posBase (C : QCfg) (k : Nat) : Nat := nK C + posIdx C.p k 0

/-- **The rest of Q_arith built from a placement record `D`** (the assembler iterates
`D ↦ mkData (QT C D)` to a fixed point): phase 2, phase 3, `Q_acc`, the ring switches and claims,
phases 8–9, padded per row shape (`withPad`: the assembler's iteration settles). The table shapes `S`
are built once. -/
def qarithT (C : QCfg) (D : QData) (o : P47Out) : BM Unit := do
  let g := kc (pbB C)
  let p := C.p
  let S := shapesOf C D
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let zK ← const .K 0 (kc 0)
  let chB : Placement := ⟨p.logN + slotLog, (layout0 p).ch⟩
  let ksB : Placement := ⟨p.ksLog + slotLog, (layout0 p).ks⟩
  withPad zK z do
    -- phases 2–3 (HAR-BT), 3b (AC-Q)
    let bus ← busG p z one g (busPos p)
    let tab ← tabG S p.tableRounds (tabPos p) z one g bus
    qacc (accInOf C S tab z)
    -- ring switches and claims of phases 4–7 (HAR-RC)
    let rgC ← ringGkr (p.logN - 4) (aLane p 2) z.n
    let chF ← chFixedG p.logN 52 chB z.n one.n (bsB C) ((sigIn C).bn + 2) o.r o.v
    let clC ← chLinkG p.logN (aLane p 3) z.n one.n chB 52
    let rgK ← ringGkr (p.ksLog - 4) (aLane p 6) z.n
    let clK ← ksLinkG p (aLane p 7) z.n one.n
    -- phases 8–9 (HAR-WH)
    let cs := claimsC (tabClaims S tab z) (kClaimsC chB o.ko rgC ++ chF) (kClaimsC ksB o.kko rgK) clC
      (ksOutC p o.rk o.vk z.n one.n) clK
    openG (cfgRec p (posBase C)) (cfgMain p (posBase C)) cs z one g

/-- **The rest of Q_arith** on the configuration's own record. -/
def qarithRest (C : QCfg) (o : P47Out) : BM Unit := qarithT C (dataOf C) o

end Lvm.Har
