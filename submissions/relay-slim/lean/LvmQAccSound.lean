-- New for lvm (AC-Q): Q_acc's soundness as a replay of phase 3b (`accFold`), HAR's `Replays` form,
-- and the bridges from M3.real's `fixSent`/`pubCheck`/`tablePoint` to the table gadget's cells.
import LvmQAccFacts
import LvmQAsmHarBase
import LvmQBusBase

/-!
# `qacc_sound`

**`qacc_sound`** (BLUEPRINT §12.5, §12.6 node level; HAR's `Replays` unfolded): where Q_acc's rows
and assertions hold with the gate on and the child's stream bound, `accFold` (phase 3b) run from
position `8 L` with `ok` keeps `ok` (its four checks: `pubCheck`, `h₀ = acc_in'.y`, `Σh = y_own`, the
zero scalar), ends at `8 z0 + 24` (phase 4's start), and its value is the current proof's `acc_in`
(`accC M pb`, its `PUB` cells). With `decideProg` that is `accOutOf Σ' = accIn x` and the child's
`pubCheck`. Hypotheses on `m` (`hfs`, `hpc`, `htp`) say that the evaluations `F` read are the table
gadget's cells; for `M3.real` they follow from `evals = evV M evc` (`fixSentR_evV`, `pubCheckR_evV`,
`tablePoint_evV`).
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1 DM

variable {M : Mem}

/-! ## `dot` with the `eq` table -/

theorem dot_le : ∀ (l r : List FE), r.length ≤ l.length →
    Lvm.dot l r = ∑ i ∈ Finset.range r.length, l.getD i 0 * r.getD i 0
  | _, [], _ => by simp [Lvm.dot]
  | [], _ :: _, h => by simp at h
  | x :: l, y :: r, h => by
    have ih := dot_le l r (by simpa using h)
    simp only [Lvm.dot, foldl_add_id, zero_add] at ih ⊢
    simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; ring

theorem dot_eqKernel (κ r : List FE) (h : r.length ≤ 2 ^ κ.length) :
    Lvm.dot (eqKernel κ) r = ∑ k ∈ Finset.range r.length, eqW κ k * r.getD k 0 := by
  rw [dot_le _ _ (by rw [eqKernel_length]; exact h)]
  apply Finset.sum_congr rfl; intro k hk; rw [Finset.mem_range] at hk
  rw [List.getD_eq_getElem?_getD, eqKernel_get? κ k (by omega)]; rfl

theorem sumE_eq (l : List FE) : sumE l = l.sum := by
  rw [sumE, foldl_add_id, zero_add]

/-! ## The soundness of Q_acc -/

set_option maxHeartbeats 1000000 in
/-- **Q_acc replays phase 3b** (HAR's `Replays c M Σ (accFold P m pub evals) (qacc A) p (8 L)
(8 z0 + 24) (fun a _ => a = accC M pb)`, unfolded; `pub = pubOf vk c Σ` is the child's). -/
theorem qacc_sound {c : Ctx} {sig : ByteArray} {T : Nat} {A : AccIn} {p : Ptr}
    (P : Params) (m : M3) (vk cc : Vector UInt8 32) (evals : List (List FE × List FE))
    (hS : Streamed M sig T) (hT : A.zL + 2 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k A.pb = 1)
    (hpp : ∀ i, (A.pp i).ty = .E) (hτp : pubLanes ≤ 2 ^ A.τp) (hla : A.la ≤ A.dk)
    (hnf : A.fx.length ≤ 2 ^ A.dk) (hRD : A.rc.length + A.dk = accVars)
    (hdk : P.accLog = A.dk) (hdk1 : 1 ≤ A.dk)
    (hvk : ∀ i < 4, M.k (A.pb + 1 + i) = (digestLanes vk).getD i 0) (hppl : A.ppt.length = A.τp)
    (hfs : m.fixSent (pubOf vk cc sig) evals = A.fx.map (Cell.val M))
    (hpc : m.pubCheck (pubOf vk cc sig) evals =
      (A.pv.val M == M3.pubEval (pubOf vk cc sig).hdrLanes (A.ppt.map (Cell.val M))))
    (htp : tablePoint evals = A.rc.map (Cell.val M)) :
    Ok c M (qacc A) p → ∀ s : RS, s.ent + s.msg = 8 * A.L → s.ok = true →
      (accFold P m (pubOf vk cc sig) evals sig s).2.ok = true ∧
      (accFold P m (pubOf vk cc sig) evals sig s).2.ent +
        (accFold P m (pubOf vk cc sig) evals sig s).2.msg = 8 * A.z0 + 24 ∧
      (accFold P m (pubOf vk cc sig) evals sig s).1 = accC M A.pb := by
  intro h s hs hok
  have F := qacc_facts hS hT hH hg hpp hτp hla hnf hRD h
  have hD : accVars = 28 := rfl
  rw [accFold_run P m _ evals sig s (by omega)]
  simp only [hs, hdk, phH, phZ]
  -- positions as lanes
  have pk : ∀ i, 8 * A.L + 40 + 72 * i = 8 * A.kap i := by intro i; simp only [AccIn.kap]; ring
  have phv : ∀ j, 8 * A.L + 72 * A.dk + 40 + 24 * j = 8 * A.hL j := by
    intro j; simp only [AccIn.hL, AccIn.h0]; ring
  have ptv : 8 * A.L + 72 * A.dk + 24 * (accVars + 1) + 40 = 8 * A.tL := by
    simp only [AccIn.tL, AccIn.h0]; ring
  have pzv : 8 * A.L + 72 * A.dk + 24 * (accVars + 1) + 72 + 40 = 8 * A.zL := by
    simp only [AccIn.zL, AccIn.z0, AccIn.h0]; ring
  have hkap : samplesAt (feAt sig) (8 * A.L) A.dk =
      (List.range A.dk).map fun i => feAt sig (8 * A.kap i) := by
    simp only [samplesAt]; apply List.map_congr_left; intro i _; rw [pk]
  have hhs : scalarsAt (feAt sig) (8 * A.L + 72 * A.dk + 40) (accVars + 1) =
      (List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j) := by
    simp only [scalarsAt]; apply List.map_congr_left; intro j _; rw [phv]
  have hacc : ∀ i, headerAt (offAcc + eBytes * i) = 8 * accLane i := by
    intro i; simp only [headerAt, offAcc, eBytes, sigBytes, accLane]; omega
  have hy : (pubOf vk cc sig).accIn.y = feAt sig (8 * accLane accVars) := by
    show feAt sig (headerAt (offAcc + eBytes * accVars)) = _; rw [hacc]
  have hpt : (pubOf vk cc sig).accIn.pt = (List.range accVars).map fun i => feAt sig (8 * accLane i) := by
    show (List.range accVars).map (fun i => feAt sig (headerAt (offAcc + eBytes * i))) = _
    simp only [hacc]
  rw [hkap, hhs, ptv, pzv, hfs, hpc, htp]
  refine ⟨?_, by simp only [AccIn.z0, AccIn.h0]; ring, ?_⟩
  · -- the four checks
    have c2 : sumE ((List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j)) =
        Lvm.dot (eqKernel ((List.range A.dk).map fun i => feAt sig (8 * A.kap i))) (A.fx.map (Cell.val M)) := by
      rw [sumE_eq, F.sum, dot_eqKernel _ _ (by simp only [List.length_map, List.length_range]; exact hnf)]
      simp only [List.length_map]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
        Option.map_some, Option.getD_some]
    have c3 : ((List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j)).headD 0 =
        (pubOf vk cc sig).accIn.y := by
      rw [hy, ← F.h0, List.range_succ_eq_map, List.map_cons, List.headD_cons]
    have c4 : A.pv.val M = M3.pubEval (pubOf vk cc sig).hdrLanes (A.ppt.map (Cell.val M)) := by
      rw [F.pub, pubEval_child hS hH cc (vkc := A.pb + 1) (fun i hi => by rw [hvk i hi]) _ (by
        simpa [hppl] using hτp)]
      have : A.ppt.map (Cell.val M) = (List.range A.τp).map fun i => (A.pp i).val M := by
        apply List.ext_getElem (by simp [hppl])
        intro i h1 h2
        simp [AccIn.pp, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
      rw [this]
    rw [c2, c3, c4, F.zero]
    simp [hok, QB.FE.beq_iff]
  · -- the folded claim
    show _ = Acc.mk (accC M A.pb).pt (accC M A.pb).y
    refine congrArg₂ Acc.mk ?_ F.y
    rw [hpt]
    apply List.ext_getElem
    · simp [accLine, accC, List.length_zipWith, hRD]
    intro i h1 h2
    have hi : i < accVars := by simpa [accC] using h2
    have := F.line i hi
    rw [List.getD_eq_getElem _ _ h2] at this
    rw [← this]
    simp only [accLine, List.getElem_zipWith, List.getElem_map, List.getElem_range]
    congr 2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [List.length_append, hRD]; omega),
      Option.getD_some]

/-- **Q_acc in HAR's `Replays` form** (phase 3b from `8 L` to phase 4's start `8 z0 + 24`; the value is
the current proof's `acc_in`, `accC M pb`). -/
theorem qacc_replays {c : Ctx} {sig : ByteArray} {T : Nat} {A : AccIn} {p : Ptr}
    (P : Params) (m : M3) (vk cc : Vector UInt8 32) (evals : List (List FE × List FE))
    (hS : Streamed M sig T) (hT : A.zL + 2 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k A.pb = 1)
    (hpp : ∀ i, (A.pp i).ty = .E) (hτp : pubLanes ≤ 2 ^ A.τp) (hla : A.la ≤ A.dk)
    (hnf : A.fx.length ≤ 2 ^ A.dk) (hRD : A.rc.length + A.dk = accVars)
    (hdk : P.accLog = A.dk) (hdk1 : 1 ≤ A.dk)
    (hvk : ∀ i < 4, M.k (A.pb + 1 + i) = (digestLanes vk).getD i 0) (hppl : A.ppt.length = A.τp)
    (hfs : m.fixSent (pubOf vk cc sig) evals = A.fx.map (Cell.val M))
    (hpc : m.pubCheck (pubOf vk cc sig) evals =
      (A.pv.val M == M3.pubEval (pubOf vk cc sig).hdrLanes (A.ppt.map (Cell.val M))))
    (htp : tablePoint evals = A.rc.map (Cell.val M)) :
    Har.Replays c M sig (accFold P m (pubOf vk cc sig) evals) (qacc A) p (8 * A.L) (8 * A.z0 + 24)
      (fun a _ => a = accC M A.pb) := fun h s hs hok =>
  qacc_sound P m vk cc evals hS hT hH hg hpp hτp hla hnf hRD hdk hdk1 hvk hppl hfs hpc htp h s hs hok

/-! ## M3.real's evaluations as the table gadget's cells -/

/-- The values of the table gadget's cells (`tabPh`'s result shape). -/
def evV (M : Mem) (evc : List (List Cell × List Cell)) : List (List FE × List FE) :=
  evc.map fun e => (e.1.map (Cell.val M), e.2.map (Cell.val M))

/-- `tablePoint` on cells. -/
def tablePointC (evc : List (List Cell × List Cell)) : List Cell :=
  evc.foldl (fun r e => if r.length < e.1.length then e.1 else r) []

theorem tablePoint_evV (evc : List (List Cell × List Cell)) :
    tablePoint (evV M evc) = (tablePointC evc).map (Cell.val M) := by
  have key : ∀ (l : List (List Cell × List Cell)) (r : List Cell),
      (evV M l).foldl (fun r e => if r.length < e.1.length then e.1 else r) (r.map (Cell.val M)) =
        (l.foldl (fun r e => if r.length < e.1.length then e.1 else r) r).map (Cell.val M) := by
    intro l
    induction l with
    | nil => intro r; rfl
    | cons e l ih =>
      intro r
      simp only [evV, List.map_cons, List.foldl_cons, List.length_map] at ih ⊢
      split_ifs with h
      · exact ih e.1
      · exact ih r
  exact key evc []

/-- `fixCols`' evaluation cells (`zc` a cell holding `0`, for columns past a table's end). -/
def fixCellsR (tabs : List M3.Tab) (pubTab : Nat) (evc : List (List Cell × List Cell)) (zc : Cell) :
    List Cell :=
  (M3.fixColsR tabs pubTab).map fun c => (evc.getD c.tab default).2.getD c.col zc

theorem getD_evV (evc : List (List Cell × List Cell)) (j : Nat) :
    (evV M evc).getD j default = ((evc.getD j default).1.map (Cell.val M), (evc.getD j default).2.map (Cell.val M)) := by
  simp only [evV, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases evc[j]? <;> rfl

theorem getD_vals (l : List Cell) (zc : Cell) (hz : zc.val M = 0) (i : Nat) :
    (l.map (Cell.val M)).getD i 0 = (l.getD i zc).val M := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hz]

theorem fixSentR_evV (tabs : List M3.Tab) (pubTab : Nat) (evc : List (List Cell × List Cell)) {zc : Cell}
    (hz : zc.val M = 0) :
    M3.fixSentR tabs pubTab (evV M evc) = (fixCellsR tabs pubTab evc zc).map (Cell.val M) := by
  simp only [M3.fixSentR, fixCellsR, List.map_map]
  apply List.map_congr_left; intro x _
  simp only [Function.comp_apply, getD_evV, getD_vals _ zc hz]

theorem pubCheckR_evV (pubTab : Nat) (pub : Pub) (evc : List (List Cell × List Cell)) {zc : Cell}
    (hz : zc.val M = 0) :
    M3.pubCheckR pubTab pub (evV M evc) = (((evc.getD pubTab default).2.getD 0 zc).val M ==
      M3.pubEval pub.hdrLanes ((evc.getD pubTab default).1.map (Cell.val M))) := by
  simp only [M3.pubCheckR, getD_evV, getD_vals _ zc hz]

end Lvm.QAcc
