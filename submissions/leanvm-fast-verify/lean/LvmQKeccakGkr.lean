import LvmQKeccakLayer

/-!
# QA1: the whole Keccak GKR verifier as a LoopIR gadget (`gkrGadget`)

`F`'s `verifyKeccak logSteps inst output` (`LvmDecideKeccak`) on a table of `2^(P+4)` instances,
as QL builder blocks (`BM`). The stream lane of the first FS answer (the segment challenge) is
`qs`; every later read is at a fixed lane offset from it (`gkrEnd` is the lane after the GKR).

1. **Constants** (`cstIns`, 256 `K` rows from the node flag `b`): per layer iteration `jf < 16`
   and `j < 16`, `K` cell `p.k + 16·jf + j` holds the RC bit at `2^j − 1` of
   `keccakRC[12 − jf − 1]` (`j < 7`), of `keccakRC[24 − jf − 1]` (`7 ≤ j < 14`), `first = [jf = 0]`
   (`j = 14`) and the gate `b·[jf < 12]` (`j = 15`); zero for the dummy iterations `jf ≥ 12`.
2. **First claim** (`preTB`): `lanes = eq` table of the five lane challenges,
   `last = eq(seg, 1)·Σ_{l<25} lanes_l·output_l`, value `committed + last`, `μ = eq` table of
   `inst[0..4)`, `κ = 1` (`Σ μ`), point `inst[4..) ++ [seg]`, `B = lanes[0..25)`, `a = 0`,
   `flip_i = lanes_0·x^(2^i − 1)`; then the `C = 57 + P` carried values as copy rows (`cpIns`), the
   cells the layer loop's `prev` reads at iteration `0`.
3. **The layers**: `loop [4]` of the layer template (`layerTB`, 12 layers + 4 dummies gated off).
   The template is built once at the origin (`lay0 P`: lanes from `0`, constants from `0`) and
   relocated (`relocI`): `K` operands of stride `16` move by the constants' cell, the others (the
   stream lanes) by the layers' first lane `qs + 57`. The carried claim of iteration `jf + 1` is
   the copy rows of `jf`.
4. **Openings**: the committed open (`scGadget` 6 rounds from `committed`), the instance sumcheck
   (4 rounds from the last claim's value), the input open (6 rounds); then (`fin1TB`) the 64
   slices (loaded twice, for the rotation block), the `eq` tables of the two slot points and of the
   last claim's `a`, the committed word and its gated check; (`rotIns`, `loop [6]`) the 64 rotated
   sums `R(s) = Σ_z slice_z·eq(a, (z + s) mod 64)` (iteration `i` gives `s = −i mod 64`); (`fin2TB`)
   `Σ_l (eq(slot, l)(1 + x) + eq(slot, 25 + l)x)·laneForm B R l`, `multilinearEval μ low` and the
   gated input check.

The correctness theorem is `gkr_spec` (`LvmQEqKeccakGkr`). New code; the reading of `F` it
replays is `LvmQEqKeccakRead`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Operands across blocks -/

/-- A cell as a fixed operand. -/
def gkS (c : Cell) : Src := .ext c.addr

/-- A result of a straight block `o` (`loop []`) as an operand of a later block. -/
def Src.gkOut (o : LoopOut) : Src → Src
  | .loc n => .ext (o.cell n 0).addr
  | s => s

/-- A result of a straight block `o` as a cell. -/
def Src.gkCell (o : LoopOut) : Src → Cell
  | .loc n => o.cell n 0
  | .ext a => ⟨a.ty, a.base⟩
  | .prev _ => default

/-! ## The relocated layer template -/

/-- Relocate an operand: stride-`16` `K` operands (the constants) by `cst`, other strided ones
(the stream lanes) by `q`. -/
def relocS (q cst : Nat) : Src → Src
  | .ext ⟨τ, b, [s]⟩ => if s = 16 then .ext ⟨τ, cst + b, [s]⟩ else .ext ⟨τ, q + b, [s]⟩
  | x => x

/-- Relocate an instruction's operands. -/
def relocI (q cst : Nat) (i : Ins) : Ins := ⟨i.op, i.ty, i.args.map (relocS q cst)⟩

/-- The first carried copy row of the layer template. -/
def cbOf (P : Nat) : Nat := (layerTB ⟨P, 0, 0, 0⟩ 0).2.length - (57 + P)

/-- The layer at the origin. -/
def lay0 (P : Nat) : LCfg := ⟨P, 0, 0, cbOf P⟩

/-- The layer template at the origin. -/
def layIns (P : Nat) : List Ins := (layerTB (lay0 P) 0).2

/-- The layer template, its lanes from `q`, its constants from `cst`. -/
def layTpl (P q cst : Nat) : List LRow := tplOf ((layIns P).map (relocI q cst))

/-- The structural facts of the layer template the proof reads (decided for each `P`): its length
is `cb + C`, every assertion is gated by constant `15`, and the last `C` rows write consecutive
`E` cells. -/
def layOk (P : Nat) : Bool :=
  (layIns P).length == cbOf P + (57 + P) &&
  (layIns P).all (fun i => i.op != .assert0 || i.args.getD 1 default == (lay0 P).k 15) &&
  ((layIns P).drop (cbOf P)).all fun i => i.ty == .E && i.op != .assert0

/-! ## The constants -/

/-- Bit `2^i − 1` of a round constant, in `K`. -/
def rcK (rc : UInt64) (i : Nat) : FK := if rc.toNat.testBit (iotaPos i) then 1 else 0

/-- Constant `j < 15` of layer iteration `jf`. -/
def cstK (jf j : Nat) : FK :=
  if 12 ≤ jf then 0
  else if j < 7 then rcK (keccakRC.getD (gkrDepth * 1 - jf - 1) 0) j
  else if j < 14 then rcK (keccakRC.getD (gkrDepth * 2 - jf - 1) 0) (j - 7)
  else if jf = 0 then 1 else 0

/-- Row `t = 16·jf + j` of the constants: `b + b + k'` (a constant), or the gate `b·[jf < 12]`. -/
def cstI (b : Src) (t : Nat) : Ins :=
  if t % 16 = 15 then ⟨.lin (if t / 16 < 12 then 0 else 1) 0, .K, [b, b]⟩
  else ⟨.lin 1 (cstK (t / 16) (t % 16)), .K, [b, b]⟩

/-- The constants block. -/
def cstIns (b : Src) : List Ins := (List.range 256).map (cstI b)

/-! ## The first claim -/

/-- What the first-claim block exports. -/
structure PreOut where
  /-- The committed scalar. -/
  com : Src
  /-- The segment challenge. -/
  seg : Src
  /-- The `eq` table of the lane challenges. -/
  lanes : List Src
  /-- The carried claim (`C` values). -/
  carried : List Src

/-- **The first claim** (`keccakFirstClaim`). -/
def preTB (P qs : Nat) (inst out : Nat → Src) (b : Src) : TB PreOut :=
  gZero b >>= fun z => gOne z >>= fun one =>
  gLoad qs [] >>= fun seg =>
  mapTB (fun k => gLoad (qs + 9 * (k + 1)) []) (List.range 5) >>= fun lp =>
  gLoad (qs + 54) [] >>= fun com =>
  gEqTab z [one] lp >>= fun lanes =>
  gDot z ((List.range 25).map fun l => (lanes.getD l default, out l)) >>= fun dt =>
  gMul seg dt com >>= fun v0 =>
  gEqTab z [one] ((List.range 4).map inst) >>= fun mu =>
  mapTB (fun i => gScale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) >>= fun fl =>
  pure ⟨com, seg, lanes, [v0] ++ mu ++ [one] ++ (List.range P).map (fun i => inst (4 + i)) ++ [seg] ++
    lanes.take 25 ++ List.replicate 6 z ++ fl⟩

/-- Copy rows of the carried values. -/
def cpIns (l : List Src) : List Ins := l.map fun a => linI 0 0 a a

/-! ## The openings -/

/-- What the first opening block exports. -/
structure Fin1Out where
  /-- A zero. -/
  z : Src
  /-- A one. -/
  one : Src
  /-- The committed word. -/
  word : Src
  /-- The slices, twice. -/
  sl : List Src
  /-- The `eq` table of the input open's slot point. -/
  e3 : List Src
  /-- The `eq` table of the last claim's slice challenges `a`. -/
  ea : List Src

/-- The slices (twice), the `eq` tables, the committed word and its check
`b·(Σ_l eq(slot, 25 + l)·(1 + seg)·lanes_l·word + value) = 0`. -/
def fin1TB (qO : Nat) (b : Src) (slot1 slot3 aF : List Src) (seg val1 : Src) (lanes : List Src) : TB Fin1Out :=
  mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) >>= fun sl =>
  gZero b >>= fun z => gOne z >>= fun one =>
  gLoad (qO + 90) [] >>= fun word =>
  gEqTab z [one] slot1 >>= fun e1 =>
  gDot z ((List.range 25).map fun l => (e1.getD (25 + l) default, lanes.getD l default)) >>= fun wc =>
  gOne seg >>= fun f =>
  gMul wc f z >>= fun w =>
  gMul w word val1 >>= fun t =>
  gAssert t b >>= fun _ =>
  gEqTab z [one] slot3 >>= fun e3 =>
  gEqTab z [one] aF >>= fun ea =>
  pure ⟨z, one, word, sl, e3, ea⟩

/-- The rotated sums: iteration `i`, row `w`: `Σ_{w' ≤ w} eq(a, w')·slice2[w' + i]` (`sb` the
first slice cell). -/
def rotIns (ea : List Src) (sb : Nat) (z : Src) : List Ins :=
  (List.range 64).map fun w =>
    mulI (ea.getD w default) (.ext ⟨.E, sb + w, [1]⟩) (if w = 0 then z else .loc (w - 1))

/-- `foldPairs` (one coordinate of `multilinearEval`), `r1 = 1 + r`. -/
def gFoldPairs (z r1 r : Src) : List Src → TB (List Src)
  | a :: b :: rest => gMul b r z >>= fun t => gMul a r1 t >>= fun x =>
      gFoldPairs z r1 r rest >>= fun xs => pure (x :: xs)
  | _ => pure []

/-- `multilinearEval mle point`. -/
def gMle (z : Src) : List Src → List Src → TB Src
  | cur, [] => pure (cur.headD z)
  | cur, r :: rs => gOne r >>= fun r1 => gFoldPairs z r1 r cur >>= fun nxt => gMle z nxt rs

/-- The input check `b·(multilinearEval μ low · Σ_l W_l·laneForm B R l + value) = 0`. -/
def fin2TB (b z : Src) (B : List Src) (R : Nat → Src) (e3 : List Src) (x : Src) (mu low : List Src)
    (val3 : Src) : TB Unit :=
  gOne x >>= fun x1 =>
  gSumMap z 25 (fun l => gLaneForm z B R l >>= fun lf => gMul (e3.getD l default) x1 z >>= fun u =>
    gMul (e3.getD (25 + l) default) x u >>= fun u' => gMul u' lf z) >>= fun tot =>
  gMle z mu low >>= fun mle =>
  gMul mle tot val3 >>= fun t => gAssert t b

/-! ## The gadget -/

/-- The gadget's outputs (`F`'s `KeccakOut` as cells). -/
structure GkrOut where
  /-- The committed-output word claim's point. -/
  wordPoint : List Cell
  /-- Its value. -/
  word : Cell
  /-- The slice point. -/
  slicePoint : List Cell
  /-- The slices. -/
  slices : List Cell

/-- The values of the outputs. -/
def GkrOut.vals (o : GkrOut) (M : Mem) : KeccakOut :=
  ⟨o.wordPoint.map (Cell.val M), o.word.val M, o.slicePoint.map (Cell.val M), o.slices.map (Cell.val M)⟩

/-- The lane of the committed open's first message. -/
def gkrQO (P qs : Nat) : Nat := qs + 57 + 12 * (lay0 P).str

/-- The lane after the GKR. -/
def gkrEnd (P qs : Nat) : Nat := gkrQO P qs + 435

/-- **`F`'s `verifyKeccak (P + 4) inst output`**, its first FS answer at lane `qs`, the caller's
instance point and output lanes in cells `inst i` (`i < P + 4`), `out l` (`l < 25`), the node flag
`b` gating every check. -/
def gkrGadget (P qs : Nat) (inst out : Nat → Cell) (b : Cell) : BM GkrOut :=
  getPtr >>= fun p =>
  loop [] (tplOf (cstIns (gkS b))) >>= fun _ =>
  loop [] (tplOf (preTB P qs (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0).2) >>= fun pre =>
  let F := (preTB P qs (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0).1
  loop [] (tplOf (cpIns (F.carried.map (Src.gkOut pre)))) >>= fun _ =>
  loop [4] (layTpl P (qs + 57) p.k) >>= fun lay =>
  let cb := cbOf P
  let qO := gkrQO P qs
  scGadget 3 2 qO .plain (F.com.gkCell pre) >>= fun sc1 =>
  scGadget 2 2 (qO + 93) .plain (lay.cell cb 11) >>= fun sc2 =>
  scGadget 3 2 (qO + 153) .plain (sc2.cell 5 3) >>= fun sc3 =>
  let G := fin1TB qO (gkS b) ((List.range 6).map fun i => gkS (sc1.cell 2 i))
    ((List.range 6).map fun i => gkS (sc3.cell 2 i)) ((List.range 6).map fun i => gkS (lay.cell (cb + 44 + P + i) 11))
    (F.seg.gkOut pre) (gkS (sc1.cell 5 5)) (F.lanes.map (Src.gkOut pre))
  loop [] (tplOf (G 0).2) >>= fun f1 =>
  loop [6] (tplOf (rotIns ((G 0).1.ea.map (Src.gkOut f1)) f1.p.e ((G 0).1.z.gkOut f1))) >>= fun rot =>
  loop [] (tplOf (fin2TB (gkS b) ((G 0).1.z.gkOut f1)
    ((List.range 25).map fun l => gkS (lay.cell (cb + 19 + P + l) 11))
    (fun s => gkS (rot.cell 63 ((64 - s) % 64))) ((G 0).1.e3.map (Src.gkOut f1))
    (gkS (lay.cell (cb + 18 + P) 11)) ((List.range 16).map fun i => gkS (lay.cell (cb + 1 + i) 11))
    ((List.range 4).map fun i => gkS (sc2.cell 2 i)) (gkS (sc3.cell 5 5)) 0).2) >>= fun _ =>
  pure ⟨(List.range (P + 4)).map inst ++ (List.range 6).map (fun i => sc1.cell 2 i),
    (G 0).1.word.gkCell f1,
    (List.range 4).map (fun i => sc2.cell 2 i) ++ (List.range P).map (fun i => lay.cell (cb + 18 + i) 11) ++
      (List.range 6).map (fun i => sc3.cell 2 i),
    (List.range 64).map fun k => ((G 0).1.sl.getD k default).gkCell f1⟩

/-! ## The layer template's structure, per shape

The kernel decides `layOk P` on the RMFE literals (`projLit`, `embedLit`): `layOk_eq_lit` rewrites
it, for every `P`, into `layOkT (layerTBT projLit embedLit) P`, where `layerTBT` is `layerTB` with
the two tables as parameters (`layerTB_eq_tbl`, by `rfl`) and `layOkT T` is `layOk` with `T` in
place of `layerTB` (`layOk_eq_T`, by `rfl`). The decided statement is then the evaluated form
itself, and the main theorem's cast is a rewrite of `layOk P` alone. -/

/-- `layerTB` with the RMFE tables `pr` (`rmfeProject`), `em` (`rmfeEmbed`) as parameters. -/
def layerTBT (pr em : List Nat) (c : LCfg) : TB Unit :=
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
  gProj z pr mu prod >>= fun proj =>
  gOne (point.getD c.P default) >>= fun seg0 =>
  gDot z ((List.range 7).map fun i => (c.k i, flips.getD i default)) >>= fun in0 =>
  gDot z ((List.range 7).map fun i => (c.k (7 + i), flips.getD i default)) >>= fun in1 =>
  gDot z [(seg0, in0), (point.getD c.P default, in1)] >>= fun iota =>
  gMul iota kappa proj >>= fun e1 => gAdd e1 value >>= fun e1' => gAssert e1' (c.k 15) >>= fun _ =>
  gInst z one s em >>= fun mk =>
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

theorem layerTB_eq_tbl : layerTB = layerTBT rmfeProject rmfeEmbed := rfl

/-- `cbOf` for the template builder `T`. -/
def cbOfT (T : LCfg → TB Unit) (P : Nat) : Nat := (T ⟨P, 0, 0, 0⟩ 0).2.length - (57 + P)

/-- `lay0` for the template builder `T`. -/
def lay0T (T : LCfg → TB Unit) (P : Nat) : LCfg := ⟨P, 0, 0, cbOfT T P⟩

/-- `layIns` for the template builder `T`. -/
def layInsT (T : LCfg → TB Unit) (P : Nat) : List Ins := (T (lay0T T P) 0).2

/-- `layOk` for the template builder `T`. -/
def layOkT (T : LCfg → TB Unit) (P : Nat) : Bool :=
  (layInsT T P).length == cbOfT T P + (57 + P) &&
  (layInsT T P).all (fun i => i.op != .assert0 || i.args.getD 1 default == (lay0T T P).k 15) &&
  ((layInsT T P).drop (cbOfT T P)).all fun i => i.ty == .E && i.op != .assert0

theorem layOk_eq_T (P : Nat) : layOk P = layOkT layerTB P := rfl

theorem layOk_eq_lit (P : Nat) : layOk P = layOkT (layerTBT projLit embedLit) P := by
  rw [layOk_eq_T, layerTB_eq_tbl, rmfeProject_eq, rmfeEmbed_eq]

theorem layOk_16 : layOk 16 = true := by rw [layOk_eq_lit]; decide +kernel

theorem layOk_11 : layOk 11 = true := by rw [layOk_eq_lit]; decide +kernel

theorem layOk_9 : layOk 9 = true := by rw [layOk_eq_lit]; decide +kernel

theorem layOk_5 : layOk 5 = true := by rw [layOk_eq_lit]; decide +kernel

end Lvm.Q1
