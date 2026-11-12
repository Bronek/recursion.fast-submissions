-- New for lvm (WP-16a): the node program `Q = Q_link ++ Q_sig ++ Q_arith` (BLUEPRINT A19) and its
-- lvm tables (WP-9's `lvmTabs`, INT-2's `lvmTabsC`) from a placement record.
import LvmQAsmTabs
import LvmQKeccakGkr
import LvmQLinkArithKS
import LvmQAsmArith2

/-!
# The node program

* `qarith C`: Q_arith, the child's `decideF` (`Lvm.Har.phases47` then `Lvm.Har.qarithRest`, decideProg's order).
* **`Q C = toProgram (nK C) 0 (qlink; qsig; qarith)`** (`LvmNodeSoundCirc.qprog`'s order).
* Its tables, arrays and placement record: `LvmQAsmTabs`.
-/

set_option autoImplicit false

namespace Lvm.QAsm

open Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.SigBits

/-! ## Q_arith (WP-16a: the phases wired so far, in `decideProg`'s order) -/

/-- The byte offset of phase `ph`'s first trace entry (`phaseFirst`; `0` if the phase has none). -/
def phaseByte (p : Params) (ph : Phase) : Nat :=
  ((phaseFirst p).find? (·.1 == ph)).elim 0 (·.2.2)

/-- The reader's positions (`ent + msg`, `decideProg`'s reading) at the steps the circuit wires:
`CH`'s point (after the table phase's one pending scalar: A23's phase 3b ends with the zero scalar, the
evaluations went into `κ`'s query), its 25 lanes, its GKR, the `CH`
link; the same for `KS` (no pending scalars), the `KS` link. A value at position `P` is at byte
`P + 40` (`readE`, `answerAt`), lane `(P + 40)/8`. -/
def arithPos (p : Params) : List Nat :=
  let tp := phaseByte p .tape + 24
  let ks := phaseByte p .ks
  [tp, tp + 72 * p.logN, tp + 72 * p.logN + 24 * lanes, phaseByte p .wire,
   ks, ks + 72 * p.ksLog, ks + 72 * p.ksLog + 24 * lanes, phaseByte p .ksLink]

/-- The lane of position `k` of `arithPos`. -/
def aLane (p : Params) (k : Nat) : Nat := ((arithPos p).getD k 0 + 40) / 8

/-- `2^D` `E` cells loaded from the stream lanes `a + st·i` (three lanes each, `feAt`). -/
def loadEs (D a st : Nat) : BM LoopOut :=
  loop [D] [⟨.loadE, .E, [.abs ⟨.K, a, [st]⟩, .abs ⟨.K, a + 1, [st]⟩, .abs ⟨.K, a + 2, [st]⟩]⟩]

/-- **Q_arith** (WP-16a's phases 4–7, `Lvm.Har.phases47`; HAR's phases 2–3, rings, claims and
openings, `Lvm.Har.qarithRest`). -/
def qarith (C : QCfg) : BM Unit := Lvm.Har.phases47 C >>= Lvm.Har.qarithRest C

/-- The node program's segments: Q_link, Q_sig, Q_arith. -/
def qprogC (C : QCfg) : BM Unit := do
  qlink C.p (lay C)
  let _ ← qsig (sigIn C)
  qarith C

/-- **The node program.** -/
def Q (C : QCfg) : Program := toProgram (nK C) 0 (qprogC C)

/-- The node program's segments with Q_arith built from the record `D` (HAR; the assembler's
fixed-point iteration). -/
def qprogT (C : QCfg) (D : QData) : BM Unit := do
  qlink C.p (lay C)
  let _ ← qsig (sigIn C)
  Lvm.Har.phases47 C >>= Lvm.Har.qarithT C D

/-- **The node program on the record `D`**; `Q C = QT C (dataOf C)`. -/
def QT (C : QCfg) (D : QData) : Program := toProgram (nK C) 0 (qprogT C D)

theorem Q_eq_QT (C : QCfg) : Q C = QT C (Lvm.Har.dataOf C) := rfl

end Lvm.QAsm
