-- New for lvm (WP-16a2, FIN-DEC): the static facts of HAR's `harith_core` and FIN-BV's `PosOk`/`SBits`
-- that are decided on the frozen `P20` record: `KS`'s glue template at `P20` (`okE_P20`, adapted from QA1's
-- `okE_P8`, LvmQLinkArithP8), the numeric fields of `HarStatic` in one decision (`harNum20`), and FIN-BV's
-- `PosLanes` (one answer per opening, on the extractor's blocks: `lens_P20`, LvmXOutSeg) with
-- `bsB cfg20 + 8 ≤ nK cfg20`.
import LvmQAsmHarMain
import LvmQAsmHarLink20
import LvmFinBVPos
import LvmXOutSeg
import LvmNodeSoundTr

/-!
# The decided static facts at `P20`

* **`okE_P20`**: `SLok` of `KS`'s glue block E at `ksLog = 15`, `recRowsLog = 14`,
  `spongeBlocks P20 - 1 = 14708` (as `okE_P8`: the check reads only the template's shape), decided
  through the one-pass check `SLokF` (`SLok_of_F`).
* **`HarNum C T P4 … P8`**: the fields of `HarStatic` that are numbers of `C.p` (positions of
  phases 4–7, lane bounds, sizes); **`harStatic_of`** builds `HarStatic` from it, the layer checks,
  the glue checks, the shape facts and the WHIR layouts (generic in the configuration).
  **`harNum20`**: `HarNum` at `cfg20`, the stream's lanes and the phases' first positions (one
  decision on `P20`'s numbers; `streamLanes`, `spongeBlocks` from `sizes_P20`).
* **`posLanes_of`**: FIN-BV's `PosLanes` from `PosLanesR` (each opening's first answer and its run of
  32-byte queries: consecutive answers lie 9 lanes apart, `ansLane_run`); **`posLanesR_of_K`**:
  `PosLanesR` at `P20` from `PosLanesK`, the same facts on the extractor's 1,215 blocks (`lens_P20`;
  a block's entries and lanes are closed forms, `ansLane_blk`, `lens_run_blk`), so the decision never
  evaluates the 11,832-entry plan (6.5 s of kernel against 20 s on the plan);
  **`posLanesR20`**, **`posLanesM20`**, **`hbs20`** (one decision).

Kernel (dev VM): `okE_P20` 1.2 s (16 s with `SLok`'s quadratic lookups), `harNum20` 1.1 s,
`posLanesB20` 6.5 s; WP-16b: about half of that through `posLanesKB` (each level's block walked to once,
`blkWalk`, instead of two prefix sums, a `drop` and a lookup).
-/

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.Har Lvm.Replay Lvm.QLink
open Lvm.QAsm (QCfg QData cfg20 data20 nK bsB clog2 nAns pbB)
open Lvm.X (Blk blocks lensB lanesOf lanes_eq lensB_opn)

/-! ## `KS`'s glue block at `P20` (`SLokF`, `SLok_of_F`: `LvmQAsmHarLink20`) -/

/-- **`SLok` of `KS`'s block E at `P20`** (`ksLog = 15`, `recRowsLog = 14`, `14709` sponge blocks). -/
theorem okE_P20 (Q : ℕ) (gate : Cell) (sh : LoopOut) :
    SLok (ksGlueE 15 Q (ksQV 15 Q) 14708 (2 ^ 14 + 399 + 31) (2 ^ 14 + 399) (rho'C sh 15) (sh.cell 2 14)
      (sh.cell 5 (15 - 1)) gate) = true := by
  rw [← SLok_shape]
  simp only [ksGlueE, List.map_append]
  rw [loadsAt_shape, loadsAt_shape (q := ksQV 15 Q), preRecIns_shape, preRecIns_shape (n := 13 * 15 + 6),
    preRecIns_shape (n := 25 * 15 + 6), mulChainIns_shape]
  simp only [List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI,
    shape_linI, shape_addI, shape_loc, rho'C, preP, shape_ins_mk, shape_getD_mapCellSrc]
  apply SLok_of_F
  decide +kernel

/-! ## `HarStatic`'s numbers -/

/-- **The fields of `HarStatic` that are numbers of `C.p`** (phases 4–7's positions `P47Pos`, the lane
bounds, sizes, the table phase's position, the start of phases 8–9). -/
def HarNum (C : QCfg) (T P4 P5 P6 P7 P8 : ℕ) : Prop :=
  (P4 + 40 = 8 * aLane C.p 0 ∧ kV C.p.logN P4 + 40 = 8 * aLane C.p 1 ∧
    kG C.p.logN P4 = 8 * aLane C.p 2 - 40 ∧
    8 * gkrEnd (C.p.logN - 4) (aLane C.p 2) - 40 + 72 * ringStages = P5 ∧ P5 + 40 = 8 * aLane C.p 3 ∧
    chP6 C.p P5 = P6 ∧ P6 + 40 = 8 * aLane C.p 4 ∧ kV C.p.ksLog P6 + 40 = 8 * aLane C.p 5 ∧
    kG C.p.ksLog P6 = 8 * aLane C.p 6 - 40 ∧
    8 * gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 40 + 72 * ringStages = P7 ∧ P7 + 40 = 8 * aLane C.p 7 ∧
    ksP2 C.p P7 + 96 = P8) ∧
  4 ≤ C.p.logN ∧ 4 ≤ C.p.ksLog ∧ C.p.recRowsLog < C.p.ksLog ∧ 5 ≤ aLane C.p 2 ∧ 5 ≤ aLane C.p 6 ∧
  gkrEnd (C.p.logN - 4) (aLane C.p 2) + 48 ≤ T ∧ gkrEnd (C.p.ksLog - 4) (aLane C.p 6) + 48 ≤ T ∧
  aLane C.p 0 + 9 * C.p.logN + 2 < T ∧ aLane C.p 1 + 3 * 25 + 2 < T ∧
  aLane C.p 4 + 9 * C.p.ksLog + 2 < T ∧ aLane C.p 5 + 3 * 25 + 2 < T ∧
  C.p.logN ≤ 2 ^ clog2 C.p.logN ∧ C.p.ksLog ≤ 2 ^ clog2 C.p.ksLog ∧
  chQC C.p.logN (aLane C.p 3) + 240 ≤ T ∧ ksQV C.p.ksLog (aLane C.p 7) + 3 * 4 + 3 ≤ T ∧
  aLane C.p 7 + 9 * (C.p.ksLog + laneBits) + 15 * C.p.ksLog + 12 ≤ T ∧
  1 ≤ spongeBlocks C.p ∧ spongeBlocks C.p ≤ 2 ^ C.p.ksLog ∧ 2 ^ C.p.recRowsLog + 431 ≤ 2 ^ C.p.ksLog ∧
  C.p.leafdecReads = 1 ∧ busPos C.p % 8 = 0 ∧ busEnd C.p (busPos C.p) + 40 ≤ 8 * T ∧
  tabPos C.p % 8 = 0 ∧ 10 ≤ C.p.tableRounds ∧ C.p.tableRounds ≤ accVars ∧ 1 ≤ C.p.accLog ∧
  11 + pubLanes ≤ T ∧ 29 ≤ T ∧ C.p.logN ≤ 64 ∧ P8 = 8 * openU C.p

/-- **`HarStatic` from its numbers**, the layer checks, the glue checks, the table shapes' facts and the
WHIR layouts (any configuration, record, stream lanes and positions; phase 3b's `accZ0` written out). -/
theorem harStatic_of {C : QCfg} {D : QData} {T P4 P5 P6 P7 P8 : ℕ} (hN : HarNum C T P4 P5 P6 P7 P8)
    (hlay : layOk (C.p.logN - 4) = true) (hlayk : layOk (C.p.ksLog - 4) = true)
    (okA : SLok (chGlueA C.p.logN (aLane C.p 3)) = true)
    (okB : ∀ oA sh : LoopOut, SLok (chGlueB (chQB C.p.logN (aLane C.p 3)) (rhoC oA C.p.logN)
      (rho'C sh C.p.logN) (eZC oA C.p.logN) (sh.cell 5 (C.p.logN - 1))) = true)
    (okC : ∀ oA sh sc2 oB : LoopOut, SLok (chGlueC (chQC C.p.logN (aLane C.p 3)) [sc2.cell 2 0, sc2.cell 2 1]
      (eLC oA C.p.logN) (eZC oA C.p.logN) (rho'C sh C.p.logN) (oA.cell (2 * C.p.logN + 163) 0)
      (oB.cell (8 * C.p.logN + 123) 0) (sc2.cell 5 1) (kc (pbB C))) = true)
    (okE : ∀ sh : LoopOut, SLok (ksGlueE C.p.ksLog (aLane C.p 7) (ksQV C.p.ksLog (aLane C.p 7))
      (spongeBlocks C.p - 1) (2 ^ C.p.recRowsLog + 399 + 31) (2 ^ C.p.recRowsLog + 399) (rho'C sh C.p.ksLog)
      (sh.cell 2 C.p.recRowsLog) (sh.cell 5 (C.p.ksLog - 1)) (kc (pbB C))) = true)
    (htT : tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) + 40 ≤ 8 * T)
    (hpubT : C.p.pubTab < (shapesOf C D).length)
    (hpubτ : ((shapesOf C D).map (·.τ)).getD C.p.pubTab 0 = 10)
    (hRmax : ∃ s ∈ shapesOf C D, C.p.tableRounds ≤ s.τ)
    (hnf : (fixIdx (shapesOf C D) C.p.pubTab).length ≤ 2 ^ C.p.accLog)
    (hzL : tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) / 8 + 9 * C.p.accLog + 3 * (accVars + 1) + 9 +
      5 + 2 < T)
    (hP4 : 8 * (tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) / 8 + 9 * C.p.accLog + 3 * (accVars + 1) +
      9) + 24 = P4)
    (hlr : LayOk (cfgRec C.p (posBase C)) T = true) (hlm : LayOk (cfgMain C.p (posBase C)) T = true) :
    HarStatic C D T P4 P5 P6 P7 P8 := by
  obtain ⟨⟨ch0, ch1, ch2, ch5, l5, l6, ks0, ks1, ks2, ks7, l7, l8⟩, hn, hk, hr, hq, hqk, hTg, hTgk, hTr, hTv,
    hTrk, hTvk, hD, hDk, hTl, hTlk, hTlk', hB, hB2, hK, hld, hbP, hbT, htP, h10, hRacc, hdk1, hH, hT29, hlog,
    hP8⟩ := hN
  exact ⟨⟨ch0, ch1, ch2, ch5, l5, l6, ks0, ks1, ks2, ks7, l7, l8⟩, hn, hk, hr, hlay, hlayk, hq, hqk, hTg, hTgk,
    hTr, hTv, hTrk, hTvk, hD, hDk, hTl, hTlk, hTlk', okA, okB, okC, hB, hB2, hK, okE, hld, hbP, hbT, htP, htT,
    hpubT, hpubτ, h10, hRmax, hRacc, hdk1, hnf, hzL, hH, hP4, hT29, hlog, hlr, hlm, hP8⟩

set_option maxRecDepth 200000 in
/-- **`HarStatic`'s numbers at `P20`** (`T` the stream's lanes, `P4 … P8` the first positions of phases
4–8). -/
theorem harNum20 : HarNum cfg20 (streamLanes P20) (Har.phaseByte P20 .ch + 24) (Har.phaseByte P20 .chLink)
    (Har.phaseByte P20 .ks) (Har.phaseByte P20 .ksLink) (8 * openU P20) := by
  unfold HarNum
  rw [cfg20_p, sizes_P20.2.2.2.2.2.2.1, sizes_P20.2.2.2.2.2.2.2.2]
  decide +kernel

/-! ## FIN-BV's `PosLanes` -/

/-- A run of 32-byte queries in the plan (entries `e … e + n − 1`). -/
theorem lens_run {p : Params} {e n : ℕ} (hr : ((lens p).drop e).take n = List.replicate n 32) {y : ℕ}
    (hy : y < n) : e + y < (plan p).length ∧ ((plan p).getD (e + y) default).len = 32 := by
  have hl : (((lens p).drop e).take n).length = n := by rw [hr, List.length_replicate]
  simp only [List.length_take, List.length_drop, lens_length] at hl
  refine ⟨by omega, ?_⟩
  rw [← lens_getD]
  have h1 : (((lens p).drop e).take n).getD y 0 = 32 := by
    rw [hr, List.getD_eq_getElem _ _ (by simpa using hy), List.getElem_replicate]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hy, List.getElem?_drop] at h1
  rw [List.getD_eq_getElem?_getD]
  exact h1

/-- **Consecutive positions answers lie 9 lanes apart** when the entries after the first carry 32-byte
queries (`ansLane (i + 1) = ansLane i + 5 + len (i + 1) / 8`, QL's `eLane_succ`). -/
theorem ansLane_run {p : Params} (hS : streamOkL (plan p) = true) {e n : ℕ} (he : 1 ≤ e)
    (hr : ((lens p).drop (e + 1)).take n = List.replicate n 32) :
    ∀ x ≤ n, ansLane p (e + x) = ansLane p e + 9 * x
  | 0, _ => rfl
  | x + 1, hx => by
    have ih := ansLane_run hS he hr x (by omega)
    obtain ⟨h0, l1⟩ := lens_run hr (y := x) (by omega)
    have hs := eLane_succ hS (i := e + x) (by omega) (by omega)
    have a0 : ansLane p (e + x) = eLane p (e + x) + 1 + ((plan p).getD (e + x) default).len / 8 := by
      simp only [ansLane, ite_eq_right (show e + x ≠ 0 by omega)]
    have a1 : ansLane p (e + (x + 1)) = eLane p (e + x + 1) + 1 + 32 / 8 := by
      rw [← Nat.add_assoc, ← l1, show e + 1 + x = e + x + 1 by omega]
      simp only [ansLane, ite_eq_right (show e + x + 1 ≠ 0 by omega)]
    omega

/-- **`PosLanes` with one answer per opening**: level `i` is opening `k0 + i` (height at most 64), the
opening's entries after its first positions entry carry 32-byte queries, and its first answer is at the
level's positions lane. -/
def PosLanesR (p : Params) (Ls : List Level) (V k0 : ℕ) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens p).length ∧ ((opens p).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧ 1 ≤ ((opens p).getD (k0 + i) default).pe ∧
    ((lens p).drop (((opens p).getD (k0 + i) default).pe + 1)).take
        (nAns ((opens p).getD (k0 + i) default) - 1) =
      List.replicate (nAns ((opens p).getD (k0 + i) default) - 1) 32 ∧
    8 * (posLanes Ls V).getD i 0 + 40 = 8 * ansLane p ((opens p).getD (k0 + i) default).pe

theorem posLanes_of {p : Params} (hS : streamOkL (plan p) = true) {Ls : List Level} {V k0 : ℕ}
    (h : PosLanesR p Ls V k0) : PosLanes p Ls V k0 := by
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h i hi
  refine ⟨h1, h2, h3, fun x hx => ?_⟩
  rw [ansLane_run hS h4 h5 x (by omega)]
  omega

/-! ### The plan's lengths through the extractor's blocks

The plan's entries after `q₀` are the extractor's blocks' queries (`lens_P20`, `lensL`); a block's
entries and lanes are numbers of the block (`bCnt`, `Blk.lanes`), so an opening's first answer lane
is a sum over the blocks before it (`ansLane_blk`) and its run of 32-byte queries a run of blocks
(`lens_run_blk`): the decision walks 1,215 blocks instead of 11,832 plan entries. -/

/-- A block's entries. -/
def bCnt : Blk → ℕ
  | .one _ _ => 1
  | .opn t _ path => t * (path + 1)

theorem length_lensB (b : Blk) : (lensB b).length = bCnt b := by
  cases b with
  | one c len => rfl
  | opn t row path =>
    rw [lensB_opn]; simp [bCnt, List.length_flatten, List.map_replicate, List.sum_replicate]

theorem length_flatMap_lensB (bs : List Blk) : (bs.flatMap lensB).length = (bs.map bCnt).sum := by
  rw [List.length_flatMap]
  exact congrArg List.sum (List.map_congr_left fun b _ => length_lensB b)

theorem lanesOf_flatMap : ∀ bs : List Blk, lanesOf (bs.flatMap lensB) = (bs.map Blk.lanes).sum
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, List.map_cons, List.sum_cons, ← lanesOf_flatMap bs, lanes_eq]
    simp only [lanesOf, List.map_append, List.sum_append]

theorem slenS_lanesOf : ∀ {l : List ℕ}, (∀ x ∈ l, x % 8 = 0) → slenS l = 8 * lanesOf l
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a (List.mem_cons_self ..)
    have ih := slenS_lanesOf (l := l) fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [slenS, lanesOf, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem lens_blocks : lens P20 = 7 :: (blocks P20).flatMap lensB := Lvm.NS.lens_P20

theorem mod8_blocks {x : ℕ} (hx : x ∈ (blocks P20).flatMap lensB) : x % 8 = 0 := by
  have h := List.all_eq_true.mp Lvm.X.lensL_facts.2 x hx
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- The answer lane of the entry that starts block `j` (a single query), from the blocks before it. -/
def blkAns (bs : List Blk) (j : ℕ) : Option ℕ :=
  match bs[j]? with
  | some (.one _ len) => some (6 + ((bs.take j).map Blk.lanes).sum + 1 + len / 8)
  | _ => none

theorem blkAns_some {bs : List Blk} {j A : ℕ} (h : blkAns bs j = some A) :
    ∃ c len, bs[j]? = some (.one c len) ∧ A = 6 + ((bs.take j).map Blk.lanes).sum + 1 + len / 8 := by
  unfold blkAns at h
  split at h
  · rename_i c len hj
    exact ⟨c, len, hj, (Option.some.inj h).symm⟩
  · cases h

/-- The plan's lengths around block `j` (a single query of `len` bytes). -/
theorem lens_split {j : ℕ} {c : QClass} {len : ℕ} (hj : (blocks P20)[j]? = some (.one c len)) :
    lens P20 =
      7 :: (((blocks P20).take j).flatMap lensB ++ len :: ((blocks P20).drop (j + 1)).flatMap lensB) := by
  have hl : j < (blocks P20).length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have hd : (blocks P20).drop j = .one c len :: (blocks P20).drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hl]
    rw [List.getElem?_eq_getElem hl, Option.some.injEq] at hj
    rw [hj]
  have e : (blocks P20).flatMap lensB =
      ((blocks P20).take j).flatMap lensB ++ ((blocks P20).drop j).flatMap lensB := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [lens_blocks, e, hd, List.flatMap_cons]
  rfl

theorem drop_mid {α : Type} (a : α) (pre : List α) (x : α) (R : List α) :
    (a :: (pre ++ x :: R)).drop (1 + pre.length + 1) = R := by
  have e : a :: (pre ++ x :: R) = (a :: pre ++ [x]) ++ R := by simp
  rw [e, show 1 + pre.length + 1 = (a :: pre ++ [x]).length by simp; omega, List.drop_left]

/-- **The answer lane of a block's first entry** from the blocks before it. -/
theorem ansLane_blk {j A : ℕ} (h : blkAns (blocks P20) j = some A) :
    ansLane P20 (1 + (((blocks P20).take j).map bCnt).sum) = A := by
  obtain ⟨c, len, hj, rfl⟩ := blkAns_some h
  have hs := lens_split hj
  set pre := ((blocks P20).take j).flatMap lensB with hpre
  have hpl : pre.length = (((blocks P20).take j).map bCnt).sum := length_flatMap_lensB _
  have h8 : ∀ x ∈ pre, x % 8 = 0 := fun x hx => mod8_blocks (by
    rw [hpre] at hx
    obtain ⟨b, hb, hx⟩ := List.mem_flatMap.mp hx
    exact List.mem_flatMap.mpr ⟨b, List.mem_of_mem_take hb, hx⟩)
  have hL : ((plan P20).getD (1 + pre.length) default).len = len := by
    rw [← lens_getD, hs, Nat.add_comm 1, List.getD_cons_succ, List.getD_append_right _ _ _ _ le_rfl,
      Nat.sub_self, List.getD_cons_zero]
  have hT : (lens P20).take (1 + pre.length) = 7 :: pre := by
    rw [hs, Nat.add_comm 1, List.take_succ_cons, List.take_left' rfl]
  rw [← hpl]
  simp only [ansLane, ite_eq_right (show 1 + pre.length ≠ 0 by omega), eLane, bOff, hT, hL]
  rw [show slenS (7 :: pre) = 47 + slenS pre from rfl, slenS_lanesOf h8, hpre, lanesOf_flatMap]
  omega

theorem flatMap_rep32 :
    ∀ n : ℕ, (List.replicate n (Blk.one .fs 32)).flatMap lensB = List.replicate n 32
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, List.flatMap_cons, flatMap_rep32 n]; rfl

/-- **The run after a block's first entry**: `n` single 32-byte queries. -/
theorem lens_run_blk {j n : ℕ} {c : QClass} {len : ℕ} (hj : (blocks P20)[j]? = some (.one c len))
    (hr : ((blocks P20).drop (j + 1)).take n = List.replicate n (.one .fs 32)) :
    ((lens P20).drop (1 + (((blocks P20).take j).map bCnt).sum + 1)).take n = List.replicate n 32 := by
  rw [lens_split hj, ← length_flatMap_lensB, drop_mid, ← List.take_append_drop n ((blocks P20).drop (j + 1)),
    hr, List.flatMap_append, flatMap_rep32, List.take_left' (by simp)]

/-- **`PosLanesR` at `P20` through the extractor's blocks** (`js`: the block of each opening's first
positions entry). -/
def PosLanesK (Ls : List Level) (V k0 : ℕ) (js : List ℕ) : Prop :=
  ∀ i < Ls.length, k0 + i < (opens P20).length ∧ ((opens P20).getD (k0 + i) default).L = Ls.getD i default ∧
    (Ls.getD i default).height ≤ 64 ∧
    1 + (((blocks P20).take (js.getD i 0)).map bCnt).sum = ((opens P20).getD (k0 + i) default).pe ∧
    ((blocks P20).drop (js.getD i 0 + 1)).take (nAns ((opens P20).getD (k0 + i) default) - 1) =
      List.replicate (nAns ((opens P20).getD (k0 + i) default) - 1) (.one .fs 32) ∧
    blkAns (blocks P20) (js.getD i 0) = some ((posLanes Ls V).getD i 0 + 5)

theorem posLanesR_of_K {Ls : List Level} {V k0 : ℕ} {js : List ℕ} (h : PosLanesK Ls V k0 js) :
    PosLanesR P20 Ls V k0 := by
  intro i hi
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h i hi
  obtain ⟨c, len, hj, -⟩ := blkAns_some h6
  refine ⟨h1, h2, h3, by omega, ?_, ?_⟩
  · rw [← h4]; exact lens_run_blk hj h5
  · rw [← h4, ansLane_blk h6]; omega

/-- Walk `j` blocks: the entries and the lanes before block `j`, and the blocks from `j`. -/
def blkWalk : List Blk → ℕ → ℕ → ℕ → ℕ × ℕ × List Blk
  | bs, 0, c, l => (c, l, bs)
  | [], _ + 1, c, l => (c, l, [])
  | b :: bs, j + 1, c, l => blkWalk bs j (c + bCnt b) (l + b.lanes)

theorem blkWalk_eq : ∀ (bs : List Blk) (j c l : ℕ),
    blkWalk bs j c l = (c + ((bs.take j).map bCnt).sum, l + ((bs.take j).map Blk.lanes).sum, bs.drop j)
  | bs, 0, c, l => by simp [blkWalk]
  | [], _ + 1, c, l => by simp [blkWalk]
  | b :: bs, j + 1, c, l => by
    rw [blkWalk, blkWalk_eq bs j]
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.drop_succ_cons, Prod.mk.injEq,
      and_true]
    exact ⟨by omega, by omega⟩

/-- `blkAns` from the walk: the block at `j` is a single query, its answer lane is `A`. -/
def blkAnsW (pre : ℕ) (rest : List Blk) (A : ℕ) : Bool :=
  match rest with
  | .one _ len :: _ => 6 + pre + 1 + len / 8 == A
  | _ => false

theorem blkAns_of_W {bs : List Blk} {j A : ℕ}
    (h : blkAnsW ((bs.take j).map Blk.lanes).sum (bs.drop j) A = true) : blkAns bs j = some A := by
  unfold blkAns
  rw [← List.head?_drop]
  unfold blkAnsW at h
  split at h
  · rename_i c len r heq
    rw [heq]
    simp only [List.head?_cons, beq_iff_eq] at h ⊢
    rw [h]
  · cases h

/-- **`PosLanesK` as one Boolean**: each level's first positions block walked to once (`blkWalk`). -/
def posLanesKB (Ls : List Level) (V k0 : ℕ) (js : List ℕ) : Bool :=
  (List.range Ls.length).all fun i =>
    let o := (opens P20).getD (k0 + i) default
    let w := blkWalk (blocks P20) (js.getD i 0) 0 0
    decide (k0 + i < (opens P20).length) && decide (o.L = Ls.getD i default) &&
    decide ((Ls.getD i default).height ≤ 64) && decide (1 + w.1 = o.pe) &&
    decide ((w.2.2.drop 1).take (nAns o - 1) = List.replicate (nAns o - 1) (.one .fs 32)) &&
    blkAnsW w.2.1 w.2.2 ((posLanes Ls V).getD i 0 + 5)

theorem posLanesK_of_B {Ls : List Level} {V k0 : ℕ} {js : List ℕ} (h : posLanesKB Ls V k0 js = true) :
    PosLanesK Ls V k0 js := by
  intro i hi
  unfold posLanesKB at h
  have hi' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, blkWalk_eq, Nat.zero_add, List.drop_drop] at hi'
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hi'
  exact ⟨h1, h2, h3, h4, h5, blkAns_of_W h6⟩

set_option maxRecDepth 200000 in
/-- The positions lanes of both openings (the blocks of their first positions entries: 1040; 1086, 1131,
1161, 1187), and the `s'` byte shifts' cells below `nK cfg20` (one decision, `posLanesKB`). -/
theorem posLanesB20 : PosLanesK P20.recLevels (openU P20 + 15) 0 [1040] ∧
    PosLanesK P20.mainLevels (stackEndL P20.recLevels (openU P20 + 15) + 15) 1 [1086, 1131, 1161, 1187] ∧
    bsB cfg20 + 8 ≤ nK cfg20 := by
  have h : (posLanesKB P20.recLevels (openU P20 + 15) 0 [1040] &&
      posLanesKB P20.mainLevels (stackEndL P20.recLevels (openU P20 + 15) + 15) 1 [1086, 1131, 1161, 1187] &&
      decide (bsB cfg20 + 8 ≤ nK cfg20)) = true := by decide +kernel
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨posLanesK_of_B h.1.1, posLanesK_of_B h.1.2, h.2⟩

/-- **FIN-BV's `PosLanes` for `C_rec`** (`posOkR20`'s `hPL`). -/
theorem posLanesR20 : PosLanes P20 P20.recLevels (openU P20 + 15) 0 :=
  posLanes_of Lvm.QAsm.hS20.1 (posLanesR_of_K posLanesB20.1)

/-- **FIN-BV's `PosLanes` for `C_main`** (`posOkM20`'s `hPL`). -/
theorem posLanesM20 : PosLanes P20 P20.mainLevels (stackEndL P20.recLevels (openU P20 + 15) + 15) 1 :=
  posLanes_of Lvm.QAsm.hS20.1 (posLanesR_of_K posLanesB20.2.1)

/-- **FIN-BV's `hbs`** (`sBits20`): the `s'` byte shifts' output cells are input cells. -/
theorem hbs20 : bsB cfg20 + 8 ≤ nK cfg20 := posLanesB20.2.2

end Lvm.Fin
