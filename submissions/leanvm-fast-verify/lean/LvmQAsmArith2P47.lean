-- New for lvm (HAR): WP-16a's phases 4–7 of Q_arith (`LvmQAsmProg.qarith`, moved here unchanged) with
-- their output cells exposed for the claims of phases 8–9 (`P47Out`).
import LvmQAsmLay
import LvmQKeccakGkr
import LvmQLinkArithKS

/-!
# Q_arith, phases 4–7 (`phases47`)

The same segments as WP-16a's `qarith` (CH point + 25 lanes loaded from the stream, QA1's
`gkrGadget`, the CH link; the same for `KS`; reader positions `arithPos`), returning the cells the
later phases read: the instance points and lanes (`r`, `v`, `rk`, `vk`) and the two GKRs' outputs.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm

/-- The byte offset of phase `ph`'s first trace entry (`phaseFirst`; `0` if the phase has none). -/
def phaseByte (p : Params) (ph : Phase) : Nat :=
  ((phaseFirst p).find? (·.1 == ph)).elim 0 (·.2.2)

/-- The reader's positions (`ent + msg`) at the steps phases 4–7 wire (WP-16a's `arithPos`; A23: the
message pending before `CH`'s first sample is phase 3b's one zero scalar, 24 bytes). -/
def arithPos (p : Params) : List Nat :=
  let ch := phaseByte p .ch + 24
  let ks := phaseByte p .ks
  [ch, ch + 72 * p.logN, ch + 72 * p.logN + 24 * lanes, phaseByte p .chLink,
   ks, ks + 72 * p.ksLog, ks + 72 * p.ksLog + 24 * lanes, phaseByte p .ksLink]

/-- The lane of position `k` of `arithPos`. -/
def aLane (p : Params) (k : Nat) : Nat := ((arithPos p).getD k 0 + 40) / 8

/-- `2^D` `E` cells loaded from the stream lanes `a + st·i` (three lanes each, `feAt`). -/
def loadEs (D a st : Nat) : BM LoopOut :=
  loop [D] [⟨.loadE, .E, [.abs ⟨.K, a, [st]⟩, .abs ⟨.K, a + 1, [st]⟩, .abs ⟨.K, a + 2, [st]⟩]⟩]

/-- The cells phases 4–7 hand on. -/
structure P47Out where
  /-- `CH`'s instance point (`logN` cells) and its 25 lanes. -/
  r : List Cell
  v : List Cell
  /-- `CH`'s Keccak GKR output. -/
  ko : Lvm.Q1.GkrOut
  /-- `KS`'s instance point (`ksLog` cells), lanes, GKR output. -/
  rk : List Cell
  vk : List Cell
  kko : Lvm.Q1.GkrOut

/-- **Phases 4–7** (WP-16a's `qarith`, every assertion gated by the node flag). -/
def phases47 (C : QCfg) : BM P47Out := do
  let g := kc (pbB C)
  let p := C.p
  let r ← loadEs (clog2 p.logN) (aLane p 0) 9
  let v ← loadEs 5 (aLane p 1) 3
  let ko ← Lvm.Q1.gkrGadget (p.logN - 4) (aLane p 2) (fun i => r.cell 0 i) (fun l => v.cell 0 l) g
  Lvm.Q1.chLinkGadget p.logN (clog2 p.logN) (aLane p 3) g
  let rk ← loadEs (clog2 p.ksLog) (aLane p 4) 9
  let vk ← loadEs 5 (aLane p 5) 3
  let kko ← Lvm.Q1.gkrGadget (p.ksLog - 4) (aLane p 6) (fun i => rk.cell 0 i) (fun l => vk.cell 0 l) g
  Lvm.Q1.ksLinkGadget p (clog2 p.ksLog) (aLane p 7) g
  pure ⟨(List.range p.logN).map (r.cell 0), (List.range 25).map (v.cell 0), ko,
    (List.range p.ksLog).map (rk.cell 0), (List.range 25).map (vk.cell 0), kko⟩

end Lvm.Har
