-- New for lvm (HAR): `F`'s decision program cut into its phases (`decideProg` = `decideProgH`, by
-- `rfl`), the cursor convention the Q_arith phase lemmas are stated in, and the stream binding of
-- the node program's input cells to `Σ`.
import LvmDecide

/-!
# `decideProg` by phases

`decideProgH p m vk c` is `decideProg p m vk c` (`decideProg_eq`, definitional) written as a
sequence of phase programs, each of which a Q_arith gadget family replays:

| phase | program | reads |
|---|---|---|
| 2 bus | `busPh p` | `α`, `β`, the grand-product GKR, `count ≠ 0`, the leaf-decomposition scalars |
| 3 tables | `tabPh p m pub bus point` | `ξ`, the table sumcheck and the evaluations |
| 3b accumulator | `accFold p m pub evals` (AC-V, A23) | `pubCheck`, `κ`, `h`, `t`, the zero scalar (Q_acc: AC-Q) |
| 4 tape (lvm2 S2) | `tapePh p` | `r`, the 25 scalars, the tape GKR (T-V's `dTape`) |
| 5 wire | `wirePh p pub claim` | A1's range of `n` (`dRange`), the wiring (T-V's `dWire`) |
| 6 KS | `ksPh p` | as `chPh` on `2^ksLog` instances |
| 7 KS link | `ksLinkPh p m rk pub` | the link |
| 8–9 openings | `openPh p claims` | `C_rec`'s, then `C_main`'s stacked WHIR opening |

**Cursor convention.** Every read of `F` but `openingR` depends only on `pos s = s.ent + s.msg`:
`readE` reads the scalar at byte `pos + 40` and adds 24; `sampleE` reads the answer at byte
`pos + 40` and sets `ent := pos + 72`, `msg := 0`. A value at byte `8 q` is stream lane `q`
(`Streamed M Σ T`: `M.k q = kAt Σ (8 q)`, QA1's binding). Phase lemmas take the start as
`s.ent + s.msg = P` and state the position after.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm DM

/-- The reader's position (`ent + msg`). -/
def pos (s : RS) : Nat := s.ent + s.msg

/-- **Phase 2**: the bus challenges, the grand-product GKR, `count ≠ 0`, the leaf-decomposition
scalars. -/
def busPh (p : Params) : DM (List FE × FE × FE × List FE × List FE × List FE) := do
  let alphas ← samples busBits
  let beta ← sampleE
  let (countRoot, point, values) ← verifyGkrGrandProducts p.busDepth
  require (countRoot != 0)
  let leafdec ← readEs p.leafdecReads
  pure (alphas, beta, countRoot, point, values, leafdec)

/-- **Phase 3**: `ξ`, its powers, the table sumcheck; the evaluations (A23: then `accFold`, phase 3b). -/
def tabPh (p : Params) (m : M3) (pub : Pub) (bus : BusOut) (point : List FE) :
    DM (List (List FE × List FE)) := do
  let xi ← sampleE
  let tables := m.tables pub
  let nC := (tables.map (·.nConstraints)).sum
  let xiPowers := powers xi (nC + 3)
  let formPowers := xiPowers.drop nC
  tableSumcheck p.tableRounds tables bus.forms (xiPowers.take nC) formPowers
    point (dot formPowers bus.totals)

/-- **Phase 4** (lvm2 S2): the tape (T1–T2, T-V's `dTape`). -/
def tapePh (p : Params) : DM TapeRes := dTape p.logN

/-- **Phase 5** (lvm2 S2): A1's range of `n` (`dRange`), then the wire (T3–T4, `dWire`). -/
def wirePh (p : Params) (pub : Pub) (claim : KeccakClaim) : DM WireOut := do
  dRange p pub
  dWire p pub claim

/-- **Phase 6**: `KS`'s instance point, lanes, GKR, ring switch. -/
def ksPh (p : Params) : DM (List FE × List FE × KeccakOut × (FE × (List FE → FE))) := do
  let rk ← samples p.ksLog
  let vks ← readEs lanes
  let kko ← verifyKeccak p.ksLog rk vks
  let kring ← ringSwitch kko.slicePoint kko.slices
  pure (rk, vks, kko, kring)

/-- **Phase 7**: the `KS` link. -/
def ksLinkPh (p : Params) (m : M3) (rk : List FE) (pub : Pub) : DM (Bool × List (Com × BlockClaim)) := do
  let kchal ← samples (p.ksLog + laneBits)
  let kshift ← sumcheck (m.ksShiftTarget kchal) 3 (List.replicate p.ksLog none)
  let kvals ← readEs 4
  pure (m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩)

/-- The claims of phase 8 (`decideProg`'s list). -/
def claimsOf (p : Params) (m : M3) (pub : Pub) (bus : BusOut) (evals : List (List FE × List FE))
    (tp : TapeRes) (wo : WireOut) (rk vks : List FE) (kko : KeccakOut) (kring : FE × (List FE → FE))
    (kLinkClaims : List (Com × BlockClaim)) : List (Com × BlockClaim) :=
  bus.claims ++ m.tableClaims pub evals ++
    (tapeClaims p tp wo pub ++ keccakClaims m.ksBlock kko kring).map (.main, ·) ++
    m.ksOutputClaims rk vks ++ kLinkClaims

/-- **Phases 8–9**: the two stacked openings. -/
def openPh (p : Params) (claims : List (Com × BlockClaim)) : DM Unit := do
  let on (com : Com) := (claims.filter (·.1 == com)).map (·.2.onStack)
  verifyStackedOpening p.recLevels p.nuRec (on .crec) false p.grind
  verifyStackedOpening p.mainLevels p.nuMain (on .main) false p.grind

/-- **`decideProg` by phases.** -/
def decideProgH (p : Params) (m : M3) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)
  let (alphas, beta, countRoot, point, values, leafdec) ← busPh p
  let bus := m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
  require bus.ok
  let evals ← tabPh p m pub bus point
  let accOut ← accFold p m pub evals
  let tp ← tapePh p
  let wo ← wirePh p pub tp.claim
  let (rk, vks, kko, kring) ← ksPh p
  let (okK, kLinkClaims) ← ksLinkPh p m rk pub
  require okK
  openPh p (claimsOf p m pub bus evals tp wo rk vks kko kring kLinkClaims)
  pure accOut

set_option maxHeartbeats 4000000 in
theorem decideProg_eq (p : Params) (m : M3) (vk c : Vector UInt8 32) :
    decideProg p m vk c = decideProgH p m vk c := by
  funext sig s
  simp only [decideProg, decideProgH, busPh, tabPh, tapePh, wirePh, ksPh, ksLinkPh, openPh, claimsOf,
    bind_assoc, pure_bind]

end Lvm.Har
