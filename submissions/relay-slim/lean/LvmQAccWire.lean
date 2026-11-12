-- New for lvm (AC-Q): Q_acc in the node program with its table inputs loaded from the child's stream
-- (until HAR-BT's table gadget supplies the table point and evaluation cells, `AccIn.rc/ppt/pv/fx`).
import LvmQAcc
import LvmQAsmTabs
import LvmQAsmArith2P47
import LvmDecideM3Real

/-!
# Wiring Q_acc (`qaccW C D`)

The positions come from the schedule and the placement record `D` (the tables' shapes):
* the table phase starts at position `phaseByte p .tables` (lane `tl`): `ξ`'s entry, then `tableRounds`
  rounds of 144 bytes; challenge `j` at lane `tl + 23 + 18 j`; the table point is the challenges
  reversed (`tableSumcheck`);
* the evaluations item at position lane `e0 = tl + 9 + 18 R` (value `k` at lane `e0 + 5 + 3k`); table `j`'s
  first column is evaluation `evOff ts j` (`ts` the sumcheck tables, widths in order);
* phase 3b starts at `8 (e0 + 3 W)` (`W = tableEvals`), and ends at phase 4's start (`8 z0 + 24`).
`fixPos`: the flat positions of `fixColsR ts pubTab`; `PUB`'s value column is column 0 of table `pubTab`.
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.M3

/-- A cache for shape-only uses of `tabs` (the column kinds do not depend on the closed forms). -/
def g0 : PG := cacheG (toProgram 0 0 (pure () : BM Unit))

/-- The sumcheck tables of the node program's record `D` (shapes only). -/
def shTabs (C : QCfg) (D : QData) : List Tab := sumcheckTabs (tabs C g0 D default)

/-- The flat index of table `j`'s first evaluation. -/
def evOff (ts : List Tab) (j : Nat) : Nat := ((ts.take j).map (·.w)).sum

/-- `fixCols`' flat positions in the evaluations item. -/
def fixPos (ts : List Tab) (pubTab : Nat) : List Nat :=
  (fixColsR ts pubTab).map fun c => evOff ts c.tab + c.col

/-- The lane of the table phase's start. -/
def tlOf (p : Params) : Nat := Har.phaseByte p .tables / 8

/-- The lane of the evaluations item's position. -/
def e0Of (p : Params) : Nat := tlOf p + 9 + 18 * p.tableRounds

/-- **Q_acc wired with stream loads**: the table point (reversed challenges), `fixCols`' and `PUB`'s
evaluations as cells, then `qacc`. -/
def qaccW (C : QCfg) (D : QData) : BM Unit := do
  let p := C.p
  let R := p.tableRounds
  let ts := shTabs C D
  let fx := fixPos ts p.pubTab
  let rb ← ldEsB ((List.range R).map fun i => tlOf p + 23 + 18 * (R - 1 - i))
  let fb ← ldEsB (fx.map fun q => e0Of p + 5 + 3 * q)
  let pv ← ldE (e0Of p + 5 + 3 * evOff ts p.pubTab)
  qacc ⟨e0Of p + 3 * p.tableEvals, p.accLog, p.accLog / 2, 10, pbB C,
    (List.range R).map (fun i => ec (rb + i)), (List.range 10).map (fun i => ec (rb + i)), pv,
    (List.range fx.length).map fun k => ec (fb + k)⟩

end Lvm.QAcc
