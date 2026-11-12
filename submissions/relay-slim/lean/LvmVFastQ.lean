-- New for lvm (V-PERF): the node program and Q_link's static table built in linear time.
import LvmQAsmProg
import LvmQAsmArith2P47

/-!
# The node program and `qltData`, built once in linear time

A compiled Lean program evaluates every closed constant of its import closure at start-up, so
`M3.Q20 = QAsm.Q cfg20` is built at every badge start (≈ 4.6 s): `mkLoop` resolves each operand
`cur t` with `lrank τ tpl t` and `ltw τ tpl`, list scans of the template (QA1's Keccak layer:
2,395 rows, ≈ 2 s per GKR gadget); `qltData` calls `eLane`/`ansLane`, which rescan the plan, per
FS entry (≈ 4.7 s per table build). Here the scans become prefix sums (`psums`) read from arrays:

* `mkLoopF`, `loopF` (`loopF_eq : loopF = loop`); `gkrGadgetF` (QA1's `gkrGadget` with `loopF`;
  `gkrGadgetF_eq`), `toProgramF` (the glue run's length carried; `toProgramF_eq`), `qarithF`, `qprogF`,
  **`QF C`** with **`QF_eq : QF C = QAsm.Q C`**; `QTF C D` (`QTF_eq : QTF C D = QAsm.QT C D`, the assembler's);
* `eLaneF`, `ansLaneF` on the plan's offsets (`eLaneF_eq`, `ansLaneF_eq`), **`qltDataF`** with
  **`qltDataF_eq : qltDataF p lay = qltData p lay`**.
-/

set_option autoImplicit false

namespace Lvm.VF

open Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QAsm Lvm.M3 Lvm.Q1

theorem toArray_getD {α : Type} (l : List α) (i : Nat) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-! ## `mkLoop` with prefix sums -/

/-- A template's ranks (`psums` of the widths), widths and rows as arrays. -/
structure TC where
  /-- `lrank .K tpl t` for `t ≤ |tpl|`. -/
  rK : Array Nat
  /-- `lrank .E tpl t` for `t ≤ |tpl|`. -/
  rE : Array Nat
  /-- `ltw .K tpl`. -/
  wK : Nat
  /-- `ltw .E tpl`. -/
  wE : Nat
  /-- The rows. -/
  rows : Array LRow

/-- The arrays of a template. -/
def tcOf (tpl : List LRow) : TC :=
  ⟨(psums (tpl.map (LRow.w .K)) 0).toArray, (psums (tpl.map (LRow.w .E)) 0).toArray,
    ltw .K tpl, ltw .E tpl, tpl.toArray⟩

/-- `lrank τ tpl t` from prefix sums `R` (the scan past the end). -/
def rankA (R : Array Nat) (τ : Ty) (tpl : List LRow) (t : Nat) : Nat :=
  if t < R.size then R.getD t 0 else lrank τ tpl t

theorem rankA_eq (τ : Ty) (tpl : List LRow) (t : Nat) :
    rankA (psums (tpl.map (LRow.w τ)) 0).toArray τ tpl t = lrank τ tpl t := by
  unfold rankA
  by_cases h : t < (psums (tpl.map (LRow.w τ)) 0).toArray.size
  · rw [if_pos h]
    simp only [List.size_toArray, length_psums, List.length_map] at h
    rw [toArray_getD, psums_getD _ _ _ (by simp only [List.length_map]; omega), lrank, List.map_take]
    simp
  · rw [if_neg h]

/-- The rank of memory `τ`. -/
def TC.rank (c : TC) (tpl : List LRow) : Ty → Nat → Nat
  | .K, t => rankA c.rK .K tpl t
  | .E, t => rankA c.rE .E tpl t

/-- The width of memory `τ`. -/
def TC.tw (c : TC) : Ty → Nat
  | .K => c.wK
  | .E => c.wE

theorem tcOf_rank (tpl : List LRow) (τ : Ty) (t : Nat) : (tcOf tpl).rank tpl τ t = lrank τ tpl t := by
  cases τ <;> exact rankA_eq _ _ _

theorem tcOf_tw (tpl : List LRow) (τ : Ty) : (tcOf tpl).tw τ = ltw τ tpl := by
  cases τ <;> rfl

/-- `curAddr` on the arrays. -/
def curAddrF (c : TC) (p : Ptr) (dims : List Nat) (tpl : List LRow) (t : Nat) : Addr :=
  let τ := (c.rows.getD t default).ty
  ⟨τ, p.at τ + c.rank tpl τ t, Build.scaledStrides dims (c.tw τ)⟩

theorem curAddrF_eq (p : Ptr) (dims : List Nat) (tpl : List LRow) (t : Nat) :
    curAddrF (tcOf tpl) p dims tpl t = curAddr p dims tpl t := by
  unfold curAddrF curAddr
  simp only [tcOf_rank, tcOf_tw]
  rw [show (tcOf tpl).rows = tpl.toArray from rfl, toArray_getD]

/-- `Opd.resolve` on the arrays. -/
def resolveF (c : TC) (p : Ptr) (dims : List Nat) (tpl : List LRow) : Opd → Addr
  | .abs a => a
  | .cur t => curAddrF c p dims tpl t
  | .prev t =>
    let a := curAddrF c p dims tpl t
    { a with base := a.base - c.tw a.ty }

theorem resolveF_eq (p : Ptr) (dims : List Nat) (tpl : List LRow) :
    resolveF (tcOf tpl) p dims tpl = Opd.resolve p dims tpl := by
  funext o
  cases o with
  | abs a => rfl
  | cur t => exact curAddrF_eq p dims tpl t
  | prev t => simp only [resolveF, Opd.resolve, curAddrF_eq, tcOf_tw]

/-- `mkLoop` with the template's arrays built once. -/
def mkLoopF (p : Ptr) (dims : List Nat) (tpl : List LRow) : Block :=
  let c := tcOf tpl
  ⟨dims, tpl.map fun r => ⟨r.op, r.ty, r.args.map (resolveF c p dims tpl)⟩⟩

theorem mkLoopF_eq (p : Ptr) (dims : List Nat) (tpl : List LRow) : mkLoopF p dims tpl = mkLoop p dims tpl := by
  unfold mkLoopF mkLoop
  dsimp only
  rw [resolveF_eq]

/-- `loop` with `mkLoopF`. -/
def loopF (dims : List Nat) (tpl : List LRow) : BM LoopOut := fun p =>
  (⟨p, dims, tpl⟩, [.blk (mkLoopF p dims tpl)])

theorem loopF_eq : loopF = loop := by
  funext dims tpl p
  unfold loopF loop
  rw [mkLoopF_eq]

/-! ## `toProgram` with the glue run's length carried -/

/-- `groupAux` with the current glue run's length (`groupAux` recomputes it per row: quadratic in the
run, ≈ 1.5 s on Q_arith's table and opening glue). -/
def groupAuxN : List Seg → List Row × Nat × List Block
  | [] => ([], 0, [])
  | .row r :: δ =>
    let g := groupAuxN δ
    if decide (glueCap ≤ g.2.1) then
      ([r], 1, if g.1.isEmpty then g.2.2 else ⟨[], g.1⟩ :: g.2.2)
    else (r :: g.1, g.2.1 + 1, g.2.2)
  | .blk B :: δ =>
    let g := groupAuxN δ
    ([], 0, B :: (if g.1.isEmpty then g.2.2 else ⟨[], g.1⟩ :: g.2.2))

theorem groupAuxN_eq : ∀ δ : List Seg,
    groupAuxN δ = ((groupAux δ).1, (groupAux δ).1.length, (groupAux δ).2)
  | [] => rfl
  | .row r :: δ => by
    simp only [groupAuxN, groupAux, groupAuxN_eq δ]
    split_ifs <;> simp
  | .blk B :: δ => by
    simp only [groupAuxN, groupAux, groupAuxN_eq δ]
    simp

/-- `group` on `groupAuxN`. -/
def groupF (δ : List Seg) : List Block :=
  let g := groupAuxN δ
  if g.1.isEmpty then g.2.2 else ⟨[], g.1⟩ :: g.2.2

theorem groupF_eq : groupF = group := by
  funext δ
  unfold groupF group
  rw [groupAuxN_eq]

/-- `toProgram` with `groupF`. -/
def toProgramF {α : Type} (nInK nInE : Nat) (m : BM α) : Program :=
  let bs := groupF (m ⟨nInK, nInE⟩).2
  ⟨nInK, nInE, bs, (List.range bs.length).filter fun b => (bs.getD b default).dims.isEmpty⟩

theorem toProgramF_eq : @toProgramF = @toProgram := by
  funext α nInK nInE m
  unfold toProgramF toProgram
  rw [groupF_eq]

/-! ## The node program -/

/-- QA1's `gkrGadget` with `loopF` (its text otherwise). -/
def gkrGadgetF (P qs : Nat) (inst out : Nat → Cell) (b : Cell) : BM GkrOut :=
  getPtr >>= fun p =>
  loopF [] (tplOf (cstIns (gkS b))) >>= fun _ =>
  loopF [] (tplOf (preTB P qs (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0).2) >>= fun pre =>
  let F := (preTB P qs (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0).1
  loopF [] (tplOf (cpIns (F.carried.map (Src.gkOut pre)))) >>= fun _ =>
  loopF [4] (layTpl P (qs + 57) p.k) >>= fun lay =>
  let cb := cbOf P
  let qO := gkrQO P qs
  scGadget 3 2 qO .plain (F.com.gkCell pre) >>= fun sc1 =>
  scGadget 2 2 (qO + 93) .plain (lay.cell cb 11) >>= fun sc2 =>
  scGadget 3 2 (qO + 153) .plain (sc2.cell 5 3) >>= fun sc3 =>
  let G := fin1TB qO (gkS b) ((List.range 6).map fun i => gkS (sc1.cell 2 i))
    ((List.range 6).map fun i => gkS (sc3.cell 2 i)) ((List.range 6).map fun i => gkS (lay.cell (cb + 44 + P + i) 11))
    (F.seg.gkOut pre) (gkS (sc1.cell 5 5)) (F.lanes.map (Src.gkOut pre))
  loopF [] (tplOf (G 0).2) >>= fun f1 =>
  loopF [6] (tplOf (rotIns ((G 0).1.ea.map (Src.gkOut f1)) f1.p.e ((G 0).1.z.gkOut f1))) >>= fun rot =>
  loopF [] (tplOf (fin2TB (gkS b) ((G 0).1.z.gkOut f1)
    ((List.range 25).map fun l => gkS (lay.cell (cb + 19 + P + l) 11))
    (fun s => gkS (rot.cell 63 ((64 - s) % 64))) ((G 0).1.e3.map (Src.gkOut f1))
    (gkS (lay.cell (cb + 18 + P) 11)) ((List.range 16).map fun i => gkS (lay.cell (cb + 1 + i) 11))
    ((List.range 4).map fun i => gkS (sc2.cell 2 i)) (gkS (sc3.cell 5 5)) 0).2) >>= fun _ =>
  pure ⟨(List.range (P + 4)).map inst ++ (List.range 6).map (fun i => sc1.cell 2 i),
    (G 0).1.word.gkCell f1,
    (List.range 4).map (fun i => sc2.cell 2 i) ++ (List.range P).map (fun i => lay.cell (cb + 18 + i) 11) ++
      (List.range 6).map (fun i => sc3.cell 2 i),
    (List.range 64).map fun k => ((G 0).1.sl.getD k default).gkCell f1⟩

theorem gkrGadgetF_eq : gkrGadgetF = gkrGadget := by
  funext P qs inst out b
  unfold gkrGadgetF
  rw [loopF_eq]
  rfl

/-- `tapeGadget` with `loopF` (the 24 layers' template: two `mkLoop`s over QA1's layer rows). -/
def tapeGadgetF (P qs : Nat) (inst out : Nat → Cell) (b : Cell) : BM TapeOut :=
  getPtr >>= fun p =>
  loopF [] (tplOf (cstInsT (gkS b))) >>= fun _ =>
  loopF [] (tplOf (preTBT P qs (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0).2) >>= fun pre =>
  let F := (preTBT P qs (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0).1
  loopF [] (tplOf (cpIns (F.carried.map (Src.gkOut pre)))) >>= fun _ =>
  loopF [4] (layTpl P (tapeQ qs) p.k) >>= fun _ =>
  loopF [3] (layTpl P (tapeQ qs + 16 * (lay0 P).str) (p.k + 16 * 16)) >>= fun lay =>
  pure ⟨fun j => lay.cell (cbOf P + j) 7⟩

theorem tapeGadgetF_eq : tapeGadgetF = tapeGadget := by
  funext P qs inst out b
  unfold tapeGadgetF
  rw [loopF_eq]
  rfl

/-- `Lvm.Har.phases47` with `tapeGadgetF`, `gkrGadgetF`. -/
def phases47F (C : QCfg) : BM Lvm.Har.P47Out := do
  let g := kc (pbB C)
  let p := C.p
  let r ← Lvm.Har.loadEs (clog2 p.logN) (Lvm.Har.aLane p 0) 9
  let v ← Lvm.Har.loadEs 5 (Lvm.Har.aLane p 1) 3
  let tp ← tapeGadgetF (p.logN - 5) (Lvm.Har.aLane p 2) (fun i => r.cell 0 i) (fun l => v.cell 0 l) g
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let mb ← Lvm.Har.borrow ((sigIn C).bn + 2) one.n p.logN
  let wo ← Lvm.Q1.wireGadget (p.logN - 5) (Lvm.Har.aLane p 3) tp.cv mb (Lvm.Har.sbCells C) g z.n
  let rk ← Lvm.Har.loadEs (clog2 p.ksLog) (Lvm.Har.aLane p 4) 9
  let vk ← Lvm.Har.loadEs 5 (Lvm.Har.aLane p 5) 3
  let kko ← gkrGadgetF (p.ksLog - 4) (Lvm.Har.aLane p 6) (fun i => rk.cell 0 i) (fun l => vk.cell 0 l) g
  Lvm.Q1.ksLinkGadget p (clog2 p.ksLog) (Lvm.Har.aLane p 7) g
  pure ⟨(List.range p.logN).map (r.cell 0), (List.range 25).map (v.cell 0), tp, mb, wo,
    (List.range p.ksLog).map (rk.cell 0), (List.range 25).map (vk.cell 0), kko⟩

/-- `QAsm.qarith` with `gkrGadgetF` (HAR mirrors every change of `qarith` here). -/
def qarithF (C : QCfg) : BM Unit := phases47F C >>= Lvm.Har.qarithRest C

/-- `QAsm.qprogC` with `qarithF`. -/
def qprogF (C : QCfg) : BM Unit := do
  qlink C.p (lay C)
  let _ ← Lvm.QSig.qsig (sigIn C)
  qarithF C

/-- **The node program, built in linear time.** -/
def QF (C : QCfg) : Program := toProgramF (nK C) 0 (qprogF C)

/-- **It is the node program.** -/
theorem QF_eq (C : QCfg) : QF C = QAsm.Q C := by
  unfold QF QAsm.Q qprogF qprogC qarithF qarith phases47F Lvm.Har.phases47
  rw [tapeGadgetF_eq, gkrGadgetF_eq, toProgramF_eq]

/-- `QAsm.qprogT` with `phases47F` (the assembler's fixed-point iteration). -/
def qprogTF (C : QCfg) (D : QData) : BM Unit := do
  qlink C.p (lay C)
  let _ ← Lvm.QSig.qsig (sigIn C)
  phases47F C >>= Lvm.Har.qarithT C D

/-- **The node program on the record `D`, built in linear time.** -/
def QTF (C : QCfg) (D : QData) : Program := toProgramF (nK C) 0 (qprogTF C D)

theorem QTF_eq (C : QCfg) (D : QData) : QTF C D = QAsm.QT C D := by
  unfold QTF QAsm.QT qprogTF QAsm.qprogT phases47F Lvm.Har.phases47
  rw [tapeGadgetF_eq, gkrGadgetF_eq, toProgramF_eq]

/-! ## The pieces and the program cache in linear time -/

/-- `Block.pieces` with the template as an array (`rowsOf` indexes the template list per row:
quadratic in a glue block's length, ≈ 8 s on the node program). -/
def blockPiecesF (B : Block) (b : Nat) : List Piece :=
  let A := B.tpl.toArray
  B.shapes.flatMap fun σ =>
    let rs := (List.range B.tpl.length).filter fun t => (A.getD t default).shape = σ
    (chunks (binParts rs.length) rs).map fun (a, ts) => ⟨b, σ, a, ts⟩

theorem blockPiecesF_eq (B : Block) (b : Nat) : blockPiecesF B b = B.pieces b := by
  unfold blockPiecesF Block.pieces Block.rowsOf
  simp only [toArray_getD]

/-- **`Program.pieces`**, blocks and templates as arrays. -/
def piecesF (Q : Program) : List Piece :=
  let bs := Q.blocks.toArray
  (List.range Q.blocks.length).flatMap fun b => blockPiecesF (bs.getD b default) b

theorem piecesF_eq (Q : Program) : piecesF Q = Q.pieces := by
  unfold piecesF Program.pieces Program.blk
  simp only [toArray_getD, blockPiecesF_eq]

/-- `cache` on the pieces `ps` (`cacheP Q Q.pieces = cache Q`). -/
def cacheP (Q : Program) (ps : List Piece) : PC :=
  let sK := psums (Q.blocks.map fun B => B.tw .K * B.size) Q.nInK
  let sE := psums (Q.blocks.map fun B => B.tw .E * B.size) Q.nInE
  ⟨Q, ((Q.blocks.zip (sK.zip sE)).map fun (B, k, e) => mkBC B k e).toArray,
    (ps.map fun p => (p, p.ts.toArray)).toArray,
    (ps.filter fun p => Q.glue.contains p.blk).flatMap fun p =>
      (p.shape.fcols.filter (· != .F)).map fun c => (p, c)⟩

theorem cacheP_eq (Q : Program) : cacheP Q Q.pieces = cache Q := rfl

/-- `BC.rank` with the template's length read off the array (`BC.rank` takes the list's length per
call: quadratic over a glue block's coefficients, ≈ 5.6 s at `P20`). -/
def rankF (bc : BC) (τ : Ty) (t : Nat) : Nat :=
  if t ≤ bc.tpl.size then (match τ with | .K => bc.rK | .E => bc.rE).getD t 0 else bc.B.rank τ t

/-- `colAffineF` with `rankF`. -/
def colAffineFF (bc : BC) (c : FCol) (t : Nat) : Nat × List Nat :=
  let r := bc.tpl.getD t default
  match c with
  | .res => (bc.start r.ty + rankF bc r.ty t, Loop.scaledStrides bc.B.dims (bc.tw r.ty))
  | .arg o => ((r.args.getD o default).base, (r.args.getD o default).strides)
  | _ => (0, [])

/-- `coefS` with `colAffineFF`. -/
def coefSF (bc : BC) (ts : Array Nat) (c : FCol) (i : Nat) : FE :=
  match c with
  | .res | .arg _ => FE.ofK (FK.x ^ (colAffineFF bc c (ts.getD i 0)).1)
  | .k | .k' => FE.ofK (kOf c (bc.tpl.getD (ts.getD i 0) default).op)
  | .F => 0

/-- `mkPE` with `coefSF`. -/
def mkPEF (bc : BC) (p : Piece) : M3.PE :=
  let ts := p.ts.toArray
  ⟨p, ts, (p.shape.fcols.filter (· != .F)).map fun c => (c, Array.ofFn (n := 2 ^ p.a) fun i => coefSF bc ts c i.val)⟩

theorem mkPEF_eq (bc : BC) (h : bc.tpl.size = bc.B.tpl.length) (p : Piece) : mkPEF bc p = mkPE bc p := by
  have hr : ∀ τ t, rankF bc τ t = bc.rank τ t := fun τ t => by
    unfold rankF BC.rank; rw [h]; cases τ <;> rfl
  have hc : ∀ c t, colAffineFF bc c t = colAffineF bc c t := fun c t => by
    unfold colAffineFF colAffineF; cases c <;> simp only [hr]
  have hs : ∀ ts c i, coefSF bc ts c i = coefS bc ts c i := fun ts c i => by
    unfold coefSF coefS; cases c <;> simp only [hc]
  unfold mkPEF mkPE
  simp only [hs]

theorem cache_bc_size (Q : Program) (b : Nat) : ((cache Q).bc b).tpl.size = ((cache Q).bc b).B.tpl.length := by
  rw [cache_bc]; simp [mkBC]

/-- **`cacheG`**: the pieces computed once (`cacheG` builds them three times), the coefficients with
`mkPEF`, one entry per glue piece. -/
def cacheGF (Q : Program) : PG :=
  let ps := piecesF Q
  let C := cacheP Q ps
  ⟨C, (ps.map fun p => mkPEF (C.bc p.blk) p).toArray,
    (ps.filter fun p => Q.glue.contains p.blk).flatMap fun p =>
      let pe := mkPEF (C.bc p.blk) p
      (p.shape.fcols.filter (· != .F)).map fun c => (pe, c)⟩

theorem cacheGF_eq (Q : Program) : cacheGF Q = cacheG Q := by
  unfold cacheGF cacheG
  simp only [piecesF_eq, cacheP_eq, Program.glueCols, List.map_flatMap, List.map_map,
    mkPEF_eq _ (cache_bc_size Q _)]
  rfl

/-! ## `qltData` with shared offsets -/

/-- The plan's entry offsets `bOff p i` for `i ≤ |plan|`. -/
def offs (p : Params) : Array Nat := (psums ((lens p).map (40 + ·)) 1).toArray

/-- `eLane` from the offsets (the scan past the end). -/
def eLaneF (O : Array Nat) (p : Params) (i : Nat) : Nat :=
  if i < O.size then O.getD i 0 / 8 else eLane p i

theorem eLaneF_eq (p : Params) : eLaneF (offs p) p = eLane p := by
  funext i
  unfold eLaneF offs
  by_cases h : i < (psums ((lens p).map (40 + ·)) 1).toArray.size
  · rw [if_pos h]
    simp only [List.size_toArray, length_psums, List.length_map] at h
    rw [toArray_getD, psums_getD _ _ _ (by simp only [List.length_map]; omega), eLane, bOff, slenS,
      List.map_take]
  · rw [if_neg h]

theorem eLaneF_eq' (p : Params) (i : Nat) : eLaneF (offs p) p i = eLane p i := by rw [eLaneF_eq]

/-- `ansLane` from the offsets and the plan as an array. -/
def ansLaneF (O : Array Nat) (PA : Array Replay.PE) (p : Params) (i : Nat) : Nat :=
  if i = 0 then 2 else eLaneF O p i + 1 + (PA.getD i default).len / 8

theorem ansLaneF_eq (p : Params) : ansLaneF (offs p) (plan p).toArray p = ansLane p := by
  funext i
  unfold ansLaneF ansLane
  rw [eLaneF_eq, toArray_getD]

theorem ansLaneF_eq' (p : Params) (i : Nat) : ansLaneF (offs p) (plan p).toArray p i = ansLane p i := by
  rw [ansLaneF_eq]

/-- `qltEntries` on the shared offsets. -/
def qltEntriesF (p : Params) (lay : Layout) : List (Nat × Nat × Nat) :=
  let O := offs p
  let PA := (plan p).toArray
  [(lay.sb, lay.sb + 1, lane0C), (lay.sb + 1, lay.sb + 2, lane1C)] ++
  ((plan p).zipIdx.filterMap fun x => match x.1.k with
    | .fs st => some (lay.sb + eLaneF O p x.2, lay.sb + ansLaneF O PA p st, x.1.len)
    | _ => none) ++
  ((List.range (17 * nBlk (hashedLen p) - hashedLen p / 8)).map fun k =>
    let q := hashedLen p / 8 + k
    (lay.sb + q, lay.sb + q + 1, padLane (hashedLen p) q))

theorem qltEntriesF_eq (p : Params) (lay : Layout) : qltEntriesF p lay = qltEntries p lay := by
  unfold qltEntriesF qltEntries
  simp only [ansLaneF_eq', eLaneF_eq']
  rfl

/-- **`qltData`, built once.** -/
def qltDataF (p : Params) (lay : Layout) : List FK :=
  let E := qltEntriesF p lay
  tblOf (E ++ List.replicate (2 ^ lay.aQ - E.length) (lay.sb, lay.sb + 1, lane0C))

theorem qltDataF_eq (p : Params) (lay : Layout) : qltDataF p lay = qltData p lay := by
  unfold qltDataF qltData qltPadded
  rw [qltEntriesF_eq]

end Lvm.VF
