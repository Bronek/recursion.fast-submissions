-- New for lvm (WP-14a): the concrete middle phases of `P_S` (LvmCertS `PSWith`), V_S's phases 2–7
-- (`LvmDecide.decideProg`) as a program of the verifier language, built from WP-9b's
-- `lbusTableCheckProg` and WP-8's `kgSpec` program, with the claim assembly of `decideProg`'s phase
-- 8 transcribed over `E`.
import LvmM3Mid
import LvmKeccakCallerPhases
import LvmKeccakCallerTape
import LvmVerifierS
import LvmAccSpecT

/-!
# The middle phases `midS` of `P_S`

`midS tabs x` (agreed with WP-14): from the statement bytes `x` (the header from byte 8),

1. the public values `pubX x` (V_S's `pubOf` on the header's key copy, the header's statement and
   the header bytes), the sumcheck tables `T = sumcheckTabs (tabs pub)`;
2. phases 2–3b: WP-9b's `lvmBusTableProg` (bus, table sumcheck), returning the tables' column
   claims, then (A23) phase 3b, AC-S's `accProgV` (V_S's `accFold` read over `E`: `PUB`'s check,
   `κ`, `h`, `t`, the zero scalar, and the folded claim `Φ̃(line(t)) = h(t)`, which V_S checks only
   after the run, `AccOk` in `decideF`): `busTabAccProg = Acc.lbusTableAccProg P20` (so `midS` is
   AC-S's `midSA` by `rfl`);
3. phases 4–7 (lvm2 S2): `kgProgS s n`, the tape caller `tapeProg 20 2 0 s n`, then WP-8's `KS`
   caller and `KS` link at `Pk = 11`, `r = 14`, `rows = contRows P20`;
4. the claims (`assembleS`): `decideProg`'s claim list over `E` (`BClaim` is V_S's `BlockClaim`
   with the verifier language's `Placement`), filtered by commitment and put on the stack, `C_rec`'s
   first.

Everything `decideProg` computes from the header (`Pub`) stays native (`FK` lanes, sent to `E` by
`kE`); everything read or sampled is the program's.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol.Compile
open Lvm.KG

/-- The verifier language's placements and stack claims. -/
abbrev VPlacement : Type := LeanVM.Protocol.Verifier.Placement
/-- A claim on the stack: weight and value. -/
abbrev VStackClaim : Type := LeanVM.Protocol.Verifier.StackClaim

/-! ## Public values from the statement -/

/-- The statement's bytes where V_S's stream holds them: header byte `j ≥ 8` at `headerAt j`. -/
def sigOfX (x : List UInt8) : ByteArray := ⟨(List.replicate (headerAt 8) 0 ++ x).toArray⟩

/-- The header fields of the statement bytes (WP-14's `hdrOf`). -/
def hdX (x : List UInt8) : Header := Header.ofProof ⟨(List.replicate 8 0 ++ x).toArray⟩

/-- **The public values of the statement**: V_S's `pubOf` on the header's key copy, the header's
statement and the header bytes. -/
def pubX (x : List UInt8) : Pub := pubOf (hdX x).vk (hdX x).stmt (sigOfX x)

/-! ## Block claims over `E` -/

/-- V_S's `BlockClaim` over `E`. -/
structure BClaim where
  /-- The block. -/
  block : VPlacement
  /-- The weight over the block's own variables. -/
  weight : List E → E
  /-- The claimed value. -/
  value : E

open LeanVM.Protocol.Verifier in
/-- A column claim on a block at `z`. -/
def BClaim.point (block : VPlacement) (z : List E) (v : E) : BClaim := ⟨block, LeanVM.Protocol.Verifier.eqEval z, v⟩

open LeanVM.Protocol.Verifier in
/-- The claim on the stack. -/
def BClaim.onStack (c : BClaim) : VStackClaim :=
  (fun x => c.block.eqAbove x * c.weight (x.take c.block.variableCount), c.value)

open LeanVM.Protocol.Verifier in
/-- `selectorPoint` over `E`. -/
abbrev selE (s n : ℕ) : List E := LeanVM.Protocol.Verifier.selectorPoint s n

open LeanVM.Protocol.Verifier in
/-- V_S's `sumClaim` over `E`. -/
def sumClaimE (nu : ℕ) (parts : List (E × VPlacement × List E)) (value : E) : BClaim :=
  ⟨⟨nu, 0⟩, fun x => LeanVM.Protocol.Verifier.sumE (parts.map fun (c, blk, z) =>
    c * blk.eqAbove x * LeanVM.Protocol.Verifier.eqEval z (x.take blk.variableCount)), value⟩

/-! ## The P20 layout (V_S's `M3.ofParts P20`, `layout0 P20`; lvm2 FRZ-0) -/

/-- v1's `CH` block (dead at lvm2 S2; kept for v1's `CH` link lemmas). -/
def chBlk : VPlacement := ⟨20 + slotLog, 0⟩
/-- `D`'s block (lvm2 S2: `dBlock P20`, 4 lanes of `2^20` rows at word 0). -/
def dBlkE : VPlacement := ⟨20 + 2, CMain.dOff20⟩
/-- `KS`'s block. -/
def ksBlk : VPlacement := ⟨15 + slotLog, CMain.ksOff20⟩
/-- `KS`'s `Y` lanes 14–24. -/
def ksY2Off : ℕ := CMain.ksY2Off20
/-- The `X` message columns. -/
def xOff : ℕ := CMain.xOff20
/-- `C_main`'s variables at `P20` (lvm2 S2: `2^24` words). -/
def nuMainE : ℕ := CMain.nu20

/-! ## The claims of phases 2–7 over `E` -/

open LeanVM.Protocol.Verifier in
/-- The tables' committed column claims (V_S's `tableClaimsR`) from the table phase's column
claims: each claim on a committed column of table `j`, on its commitment's block. -/
def tableClaimsE (T : List M3.Tab) (cl : List ColumnClaim) : List (Com × BClaim) :=
  cl.filterMap fun c => (M3.colLoc T c.column).bind fun ji =>
    match T[ji.1]?.bind fun t => t.cols[ji.2]? with
    | some (.com rec off) => some (if rec then .crec else .main,
        BClaim.point ⟨(T[ji.1]?.map (·.τ)).getD 0, off⟩ c.point c.value)
    | _ => none

/-- The output of WP-8's caller program (`callerProg`). -/
abbrev CallerOut : Type :=
  List E × List E × (List LeanVM.Protocol.Verifier.ColumnClaim × List E × List E) × (E × (List E → E))

/-- A Keccak table's claims (V_S's `keccakClaims`): the committed-output word and the ring switch. -/
def keccakClaimsE (blk : VPlacement) (co : CallerOut) : List BClaim :=
  co.2.2.1.1.map (fun c => BClaim.point blk c.point c.value) ++ [⟨blk, co.2.2.2.2, co.2.2.2.1⟩]

/-- `CH`'s output lanes 0–3 on `Y` and the boundary claims (V_S's `chFixedClaims`). -/
def chFixedClaimsE (r v : List E) (pub : Pub) : List BClaim :=
  ((List.range 4).map fun l => BClaim.point chBlk (r ++ selE (Lvm.chYSlotV1 + l) slotLog) (v.getD l 0)) ++
  ((pad43 pub.s).zipIdx.map fun (w, l) =>
    BClaim.point chBlk (selE 0 20 ++ selE l slotLog) (M3.kE w)) ++
  (pub.h.zipIdx.map fun (w, l) =>
    BClaim.point chBlk (selE (pub.n - 1) 20 ++ selE (Lvm.chYSlotV1 + l) slotLog) (M3.kE w))

/-- The `CH` link's claims (V_S's `chLink0` claims): the two ring switches, the 17 constant lanes. -/
def chLinkClaimsE (lo : ChLinkOut) : List (Com × BClaim) :=
  let rho' := lo.shift.1
  let consts := (List.range 17).map fun j =>
    BClaim.point chBlk (rho' ++ selE (8 + j) slotLog)
      (M3.kE (if 8 + j = 16 then ⟨(0x80 : UInt64) <<< 56⟩ else 0))
  ([(⟨chBlk, lo.ringIn.2, lo.ringIn.1⟩ : BClaim), ⟨chBlk, lo.ringY.2, lo.ringY.1⟩] ++ consts).map
    (.main, ·)

/-- `KS`'s `Y` lane `l` (V_S's `ksYPart`). -/
def ksYPartE (l : ℕ) (pt : List E) : VPlacement × List E :=
  if l < 14 then (ksBlk, pt ++ selE (50 + l) slotLog)
  else (⟨15, ksY2Off + (l - 14) * 2 ^ 15⟩, pt)

/-- The openings of `KS`'s 25 output lanes (V_S's `ksOutputClaims0`). -/
def ksOutputClaimsE (rk v : List E) : List (Com × BClaim) :=
  (List.range 25).map fun l =>
    let bz := ksYPartE l rk
    (.main, BClaim.point bz.1 bz.2 (v.getD l 0))

open LeanVM.Protocol.Verifier in
/-- The `KS` link's claims (V_S's `ksLink0` claims). -/
def ksLinkClaimsE (kchal : List E) (kshift : List E × E) (vals : List E) : List (Com × BClaim) :=
  let om := LeanVM.Protocol.Verifier.eqKernel (kchal.drop 15)
  let rho' := kshift.1
  let lo := rho'.take 14
  let yC := sumClaimE nuMainE ((List.range 25).map fun l =>
    let bz := ksYPartE l rho'
    (om.getD l 0, bz.1, bz.2)) (vals.getD 0 0)
  let inC := sumClaimE nuMainE ((List.range 25).map fun l =>
    (om.getD l 0, ksBlk, rho' ++ selE l slotLog)) (vals.getD 1 0)
  let mC := sumClaimE 19 ((List.range 17).map fun l =>
    (om.getD l 0, (⟨14, l * 2 ^ 14⟩ : VPlacement), lo)) (vals.getD 2 0)
  let xC := sumClaimE nuMainE ((List.range 17).map fun l =>
    (om.getD l 0, (⟨14, xOff + l * 2 ^ 14⟩ : VPlacement), lo)) (vals.getD 3 0)
  [(.main, yC), (.main, inC), (.crec, mC), (.main, xC)]

/-- **The tape's claims** (V_S's `tapeClaims P20`, lvm2 S2): `D̃_l(r) = a_l` (`l < 4`), the ring claim on
`C_main`, the boundary claims `D̃_l(bits(n − 1)) = h_l`. -/
def tapeClaimsE (tp : TapeOutE) (pub : Pub) : List BClaim :=
  ((List.range 4).map fun l => BClaim.point dBlkE (tp.1 ++ selE l 2) (tp.2.1.getD l 0)) ++
  [⟨⟨nuMainE, 0⟩, tp.2.2.2.d.ring.2, tp.2.2.2.d.ring.1⟩] ++
  (pub.h.zipIdx.map fun (w, l) =>
    BClaim.point dBlkE (selE (pub.n - 1) 20 ++ selE l 2) (M3.kE w))

/-! ## The program -/

/-- **V_S phases 4–7** (lvm2 S2): the tape caller (`tapeProg 20 2 0 s n`: `D` is block 0 of the four
`2^22`-word blocks of `C_main`), then WP-8's `KS` caller and `KS` link at `P20` (`ksLog = 11 + 4`). -/
def kgProgS (s : RecursionFast.Digest) (n : ℕ) :=
  tapeProg 20 2 0 s n >>= fun tp ↦
    (callerProg (11 + 4) >>= fun co ↦ ksLinkProg (11 + 4) 14 (contRows P20) >>= fun lo ↦
      VerifierProgram.ret (co, lo)) >>= fun kso ↦ VerifierProgram.ret (tp, kso)

/-- What `kgProgS` returns. -/
abbrev KgOut : Type :=
  TapeOutE × (CallerOut × (List E × (List E × E) × List E))

/-- **The claims of phases 2–7** (V_S's claim list of phase 8: tables, the tape's claims, `KS`'s
Keccak claims, `KS`'s output lanes, the `KS` link), put on the stack per commitment:
`(C_rec, C_main)`. -/
def assembleS (T : List M3.Tab) (pub : Pub) (cl : List LeanVM.Protocol.Verifier.ColumnClaim)
    (kg : KgOut) : List VStackClaim × List VStackClaim :=
  let ks := kg.2.1
  let claims : List (Com × BClaim) :=
    tableClaimsE T cl ++
      (tapeClaimsE kg.1 pub ++ keccakClaimsE ksBlk ks).map (.main, ·) ++
      ksOutputClaimsE ks.1 ks.2.1 ++
      ksLinkClaimsE kg.2.2.1 kg.2.2.2.1 kg.2.2.2.2
  let on (com : Com) := (claims.filter (·.1 == com)).map (·.2.onStack)
  (on .crec, on .main)

/-! ## Phase 3b over `E` (A23, BLUEPRINT §12.4) -/

/-- **V_S phases 2–3b**: WP-9b's bus phase and table sumcheck, then phase 3b (AC-S's
`lbusTableAccProg`: `accProgV`, V_S's `accFold` read through `FE.toExt3`); the tables' column
claims. -/
def busTabAccProg (tabs : Pub → List M3.Tab) (pub : Pub) :
    VerifierProgram (List LeanVM.Protocol.Verifier.ColumnClaim) :=
  Lvm.Acc.lbusTableAccProg P20 tabs pub P20.busDepth

/-- **The middle phases of `P_S`** (V_S phases 2–7 with A23's phase 3b, then the claims for the
openings). -/
def midS (tabs : Pub → List M3.Tab) (x : List UInt8) :
    VerifierProgram (List VStackClaim × List VStackClaim) :=
  let pub := pubX x
  let T := M3.sumcheckTabs (tabs pub)
  busTabAccProg tabs pub >>= fun cl ↦
    kgProgS (hdX x).s pub.n >>= fun kg ↦ VerifierProgram.ret (assembleS T pub cl kg)

end Lvm.VEq
