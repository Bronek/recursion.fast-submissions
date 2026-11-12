-- New for lvm (HAR): WP-16a's phases 4–7 of Q_arith with their output cells exposed for the claims of
-- phases 8–9 (`P47Out`). lvm2 S2 (T-Q): phases 4–5 are the tape (`tapeGadget`) and the wire
-- (`wireGadget`, the borrow chain for `m`'s bits); phases 6–7 (`KS`) are v1's.
import LvmQAsmLay
import LvmQWire
import LvmQAsmBorrow
import LvmQLinkArithKS

/-!
# Q_arith, phases 4–7 (`phases47`, lvm2 S2)

* **phase 4, the tape** (T-V's `dTape`): `r` (`logN` challenges) and the 25 output scalars loaded from
  the stream, then `tapeGadget (logN − 5)` from the first lane challenge;
* **phase 5, the wire** (`dRange; dWire`): the bits of `m = n' − 1` by the borrow chain on Q_sig's bits of
  `n'` (`dRange` needs no rows: Q_sig's `ChildOk` bounds `n'`), then `wireGadget (logN − 5)` from the wire's
  first message (`tapeEnd`), its input claim the tape's carried cells, `s'`'s bits the `sSpec` class at
  `bsB`;
* **phases 6–7, `KS`**: as v1 (`gkrGadget (ksLog − 4)`, `ksLinkGadget`).

The reader's positions are `arithPos` (A23: the message pending before the tape's first sample is phase
3b's one zero scalar, 24 bytes).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm

/-- The byte offset of phase `ph`'s first trace entry (`phaseFirst`; `0` if the phase has none). -/
def phaseByte (p : Params) (ph : Phase) : Nat :=
  ((phaseFirst p).find? (·.1 == ph)).elim 0 (·.2.2)

/-- The reader's positions (`ent + msg`) at the steps phases 4–7 wire: the tape's `r`, its 25 scalars, its
first lane challenge, the wire's first message; `KS`'s point, lanes, GKR; the `KS` link. A value at
position `P` is at byte `P + 40`, lane `(P + 40)/8`. -/
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

/-- The cells of `s'`'s 256 bits (`sSpec`'s outputs, bit `z` of lane `l` at `bsB + 64 l + z`). -/
def sbCells (C : QCfg) : List Cell := (List.range 256).map fun q => kc (bsB C + q)

/-- The cells phases 4–7 hand on. -/
structure P47Out where
  /-- The tape's instance point (`logN` cells) and its 25 output scalars. -/
  r : List Cell
  v : List Cell
  /-- The tape's input claim. -/
  tape : Lvm.Q1.TapeOut
  /-- `m = n' − 1`'s `logN` bits (the borrow chain). -/
  mb : List Cell
  /-- The wire's outputs. -/
  wire : Lvm.Q1.WireOut
  /-- `KS`'s instance point (`ksLog` cells), lanes, GKR output. -/
  rk : List Cell
  vk : List Cell
  kko : Lvm.Q1.GkrOut

/-- **Phases 4–7** (every assertion gated by the node flag). -/
def phases47 (C : QCfg) : BM P47Out := do
  let g := kc (pbB C)
  let p := C.p
  let r ← loadEs (clog2 p.logN) (aLane p 0) 9
  let v ← loadEs 5 (aLane p 1) 3
  let tp ← Lvm.Q1.tapeGadget (p.logN - 5) (aLane p 2) (fun i => r.cell 0 i) (fun l => v.cell 0 l) g
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let mb ← borrow ((sigIn C).bn + 2) one.n p.logN
  let wo ← Lvm.Q1.wireGadget (p.logN - 5) (aLane p 3) tp.cv mb (sbCells C) g z.n
  let rk ← loadEs (clog2 p.ksLog) (aLane p 4) 9
  let vk ← loadEs 5 (aLane p 5) 3
  let kko ← Lvm.Q1.gkrGadget (p.ksLog - 4) (aLane p 6) (fun i => rk.cell 0 i) (fun l => vk.cell 0 l) g
  Lvm.Q1.ksLinkGadget p (clog2 p.ksLog) (aLane p 7) g
  pure ⟨(List.range p.logN).map (r.cell 0), (List.range 25).map (v.cell 0), tp, mb, wo,
    (List.range p.ksLog).map (rk.cell 0), (List.range 25).map (vk.cell 0), kko⟩

end Lvm.Har
