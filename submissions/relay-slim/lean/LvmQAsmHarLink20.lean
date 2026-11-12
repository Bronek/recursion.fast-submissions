-- New for lvm (HAR; WP-16b: the checks through WP-16a2's one-pass `SLokF`, moved here from `LvmFinDec`):
-- QA1's link soundness at `P20` (`logN = 20`, `ksLog = 15`, `recRowsLog = 14`):
-- the template checks (`SLok`) decided as for `P8` (QA1's `LvmQLinkArithP8`), the KS template
-- (`okE`) after the re-freeze.
import LvmQLinkArithP8

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1

/-! ## `SLok` in one pass (WP-16a2, moved here from `LvmFinDec` for the `P20` glue checks)

`SLok` looks every operand's row up from the template's head (quadratic: 16 s of kernel at the
600-row block E); `SLokF` walks the template once and looks the assertions up in a short list. -/

/-- The positions of a template's assertions. -/
def assertPos (ins : List Ins) : List ℕ :=
  (ins.zipIdx.filter fun x => !(x.1.op != .assert0)).map Prod.snd

/-- **`SLok` in one pass**: the reads of earlier results look the assertions up in `assertPos`. -/
def SLokF (ins : List Ins) : Bool :=
  ins.zipIdx.all fun x => (match x.1.op with
    | .muladd | .lin .. | .loadE | .assert0 => true
    | _ => false) &&
    x.1.args.all fun s => match s with
      | .loc k' => decide (k' < x.2) && !((assertPos ins).contains k')
      | .prev k' => decide (k' < ins.length) && !((assertPos ins).contains k')
      | .ext _ => true

/-- A row is no assertion iff its position is not in `assertPos`. -/
theorem bne_assert {ins : List Ins} {k : ℕ} (hk : k < ins.length) :
    ((ins.getD k default).op != .assert0) = !((assertPos ins).contains k) := by
  rw [List.getD_eq_getElem _ _ hk]
  cases hc : (assertPos ins).contains k
  · have hn : ¬ k ∈ assertPos ins := by simpa using hc
    simp only [Bool.not_false]
    by_contra hb
    apply hn
    simp only [assertPos, List.mem_map, List.mem_filter]
    exact ⟨(ins[k], k), ⟨List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]), by simpa using hb⟩, rfl⟩
  · have hm : k ∈ assertPos ins := by simpa using hc
    simp only [assertPos, List.mem_map, List.mem_filter] at hm
    obtain ⟨⟨i, k'⟩, ⟨hz, hb⟩, rfl⟩ := hm
    have := List.mem_zipIdx_iff_getElem?.mp hz
    simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at this
    rw [← this] at hb
    simpa using hb

/-- **`SLokF` decides `SLok`** (one direction suffices). -/
theorem SLok_of_F {ins : List Ins} (h : SLokF ins = true) : SLok ins = true := by
  unfold SLok
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  unfold SLokF at h
  rw [List.all_eq_true] at h
  have hx := h (ins[k], k) (List.mem_zipIdx_iff_getElem?.mpr (by simp [hk]))
  rw [List.getD_eq_getElem _ _ hk]
  unfold Ins.locOk
  simp only [Bool.and_eq_true, List.all_eq_true] at hx ⊢
  refine ⟨hx.1, fun s hs => ?_⟩
  have hs' := hx.2 s hs
  cases s with
  | loc k' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs' ⊢
    refine ⟨hs'.1, ?_⟩
    rw [bne_assert (by omega)]
    exact hs'.2
  | prev k' =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hs' ⊢
    refine ⟨hs'.1, ?_⟩
    rw [bne_assert hs'.1]
    exact hs'.2
  | ext a => rfl

end Lvm.Fin

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

theorem okA_P20 (Q : Nat) : SLok (chGlueA 20 Q) = true := by
  rw [← SLok_shape]
  simp only [chGlueA, List.map_append]
  rw [loadsAt_shape]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

theorem okB_P20 (Q : Nat) (oA sh : LoopOut) :
    SLok (chGlueB (chQB 20 Q) (rhoC oA 20) (rho'C sh 20) (eZC oA 20) (sh.cell 5 (20 - 1))) = true := by
  rw [← SLok_shape]
  simp only [chGlueB, List.map_append]
  rw [loadsAt_shape, dotIns_shape, shiftRecIns_shape]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI, shape_linI, shape_addI, shape_loc, shape_shape, shape_getD_cellSrc, rhoC, rho'C, eZC, eLC, preP, List.length_map, List.length_range, shape_ins_mk, shape_getD_mapCellSrc, eMus_any]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

theorem okC_P20 (Q : Nat) (gate : Cell) (oA sh sc2 oB : LoopOut) :
    SLok (chGlueC (chQC 20 Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA 20) (eZC oA 20) (rho'C sh 20)
      (oA.cell (2 * 20 + 163) 0) (oB.cell (8 * 20 + 123) 0) (sc2.cell 5 1) gate) = true := by
  rw [← SLok_shape]
  simp only [chGlueC, List.map_append]
  rw [loadsAt_shape, eqTabGo_shape, dotIns_shape, dotIns_shape (n := 78), dotIns_shape (n := 82),
    dotIns_shape (n := 138), mulChainIns_shape]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI, shape_linI, shape_addI, shape_loc, shape_shape, shape_getD_cellSrc, rhoC, rho'C, eZC, eLC, preP, List.length_map, List.length_range, shape_ins_mk, shape_getD_mapCellSrc, eMus_any]
  apply Lvm.Fin.SLok_of_F
  decide +kernel

-- `okE` at `P20` depends on the sponge-block count literally (`preRecIns` walks its bits): decided after the
-- re-freeze, as `okE_P8`.

end Lvm.Q1
