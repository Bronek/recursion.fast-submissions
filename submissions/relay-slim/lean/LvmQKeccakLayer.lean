import LvmQKeccakParts2
import LvmQKeccakConst
import LvmQEqKeccakAlg3

/-!
# QA1: one Keccak GKR layer as a loop template (`layerTB`)

The template of one layer of `F`'s `verifyKeccakLayer` on a table of `2^(P+4)` instances (`CH`:
`P = 16`, `KS`: `P = 11`). The claim is carried from the previous iteration through `C = 57 + P`
copy rows at the template's end (`cb` is the first): `value, μ[16], κ, point[P+1], B[25], a[6],
flip[7]`; the weights are `Lᵀ(eq(a) ⊗ B)` (or the first claim's `lanes ⊗ x^z` when the layer's
`first` constant is `1`). Per-layer constants (`K` cells, 16 per layer from `cst`): the RC bits at
`2^i − 1` of both segments (`14`), `first`, the gate. Stream: the layer's first product scalar is
lane `q`; a layer is `366 + 15(P+1)` lanes.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- The layer's configuration. -/
structure LCfg where
  /-- Pack rounds minus one (`logSteps − 4`). -/
  P : Nat
  /-- The lane of the first product scalar at layer `0`. -/
  q : Nat
  /-- The first constant cell. -/
  cst : Nat
  /-- The first carried copy row. -/
  cb : Nat

/-- Lanes per layer. -/
def LCfg.str (c : LCfg) : Nat := 366 + 15 * (c.P + 1)

/-- Carried rows. -/
def LCfg.C (c : LCfg) : Nat := 57 + c.P

/-- A carried input (the previous iteration's copy `j`). -/
def LCfg.pv (c : LCfg) (j : Nat) : Src := .prev (c.cb + j)

/-- A constant `K` cell of the layer. -/
def LCfg.k (c : LCfg) (j : Nat) : Src := .ext ⟨.K, c.cst + j, [16]⟩

/-- A copy row. -/
def gCopy (a : Src) : TB Src := gLin 0 0 a a

/-- **The layer.** -/
def layerTB (c : LCfg) : TB Unit :=
  let str := [c.str]
  let value := c.pv 0
  let mu := (List.range 16).map fun i => c.pv (1 + i)
  let kappa := c.pv 17
  let point := (List.range (c.P + 1)).map fun i => c.pv (18 + i)
  let B := (List.range 25).map fun l => c.pv (19 + c.P + l)
  let a := (List.range 6).map fun i => c.pv (44 + c.P + i)
  let flips := (List.range 7).map fun i => c.pv (50 + c.P + i)
  let q := c.q
  gZero (.ext ⟨.K, q, str⟩) >>= fun z => gOne z >>= fun one =>
  mapTB (fun k => gLoad (q + 3 * k) str) (List.range productBits) >>= fun prod =>
  gLoad (q + 141) str >>= fun s =>
  gProj z rmfeProject mu prod >>= fun proj =>
  gOne (point.getD c.P default) >>= fun seg0 =>
  gDot z ((List.range 7).map fun i => (c.k i, flips.getD i default)) >>= fun in0 =>
  gDot z ((List.range 7).map fun i => (c.k (7 + i), flips.getD i default)) >>= fun in1 =>
  gDot z [(seg0, in0), (point.getD c.P default, in1)] >>= fun iota =>
  gMul iota kappa proj >>= fun e1 => gAdd e1 value >>= fun e1' => gAssert e1' (c.k 15) >>= fun _ =>
  gInst z one s rmfeEmbed >>= fun mk =>
  gHorner s (prod.getD 46 default) ((List.range 46).reverse.map fun k => prod.getD k default) >>= fun v0 =>
  gPackRounds z str (q + 150) point v0 one >>= fun pk =>
  gLocalRounds str 11 (q + 150 + 15 * (c.P + 1)) pk.1 >>= fun lc =>
  let q3 := q + 348 + 15 * (c.P + 1)
  mapTB (fun k => gLoad (q3 + 3 * k) str) (List.range 3) >>= fun t =>
  gLoad (q3 + 9) str >>= fun beta =>
  gEqTab z [one] (lc.2.take 3) >>= fun tbLo => gEqTab z [one] ((lc.2.drop 3).take 3) >>= fun tbHi =>
  gEqTab z [one] (a.take 3) >>= fun taLo => gEqTab z [one] (a.drop 3) >>= fun taHi =>
  gEqTab z [one] (lc.2.drop 6) >>= fun eL =>
  mapTB (gLowTab z taLo tbLo 0) (List.range 8) >>= fun L0 =>
  mapTB (gLowTab z taLo tbLo 1) (List.range 8) >>= fun L1 =>
  mapTB (gHighTab z taHi tbHi) (List.range 8) >>= fun H =>
  mapTB (gShift z L0 L1 H) (List.range 64) >>= fun sh =>
  gSumMap z 25 (fun l => gLaneForm z B (fun r => sh.getD r default) l >>= fun lf =>
    gMul (eL.getD l default) lf z) >>= fun Wk =>
  gSumMap z 25 (fun l => gMul (eL.getD l default) (B.getD l default) z) >>= fun dfB =>
  gIndex z 0 one (lc.2.take 6) >>= fun idx => gMul dfB idx z >>= fun Wf =>
  gAdd Wf Wk >>= fun d => gMul (c.k 14) d Wk >>= fun W =>
  gMul mk.2 (t.getD 0 default) z >>= fun kt0 => gAdd mk.2 (t.getD 1 default) >>= fun k1 =>
  gMul k1 (t.getD 2 default) kt0 >>= fun m => gMul pk.2.1 W z >>= fun sw => gMul sw m lc.1 >>= fun e2 =>
  gAssert e2 (c.k 15) >>= fun _ =>
  gMul beta (t.getD 2 default) (t.getD 1 default) >>= fun tt => gMul beta tt (t.getD 0 default) >>= fun v' =>
  gLaneW eL beta >>= fun B' =>
  gEqTab z [one] (lc.2.take 6) >>= fun A' =>
  mapTB (gFlip z B' A') (List.range 7) >>= fun fl =>
  mapTB gCopy ([v'] ++ mk.1 ++ [mk.2] ++ pk.2.2 ++ B' ++ lc.2.take 6 ++ fl) >>= fun _ => pure ()

end Lvm.Q1
