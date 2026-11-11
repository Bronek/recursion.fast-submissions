-- New for lvm (AC-Q): the proof of Q_acc's facts (`qacc_facts`).
import LvmQAcc

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

-- adapted from LvmQSigParts.ok_bind' (WP-12)
theorem okBind {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Ok c M (m >>= f) p) : Ok c M m p ∧ Ok c M (f (m p).1) (p.adv (m p).2) := by
  obtain ⟨h1, h2⟩ := h
  rw [hold_bind] at h1; rw [assert_bind] at h2
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

theorem okBindE {c : Ctx} {M : Mem} {α β : Type} {m : BM α} {f : α → BM β} {p : Ptr}
    (h : Ok c M (m >>= f) p) : ∃ x q, (m p).1 = x ∧ p.adv (m p).2 = q ∧ Ok c M m p ∧ Ok c M (f x) q :=
  ⟨_, _, rfl, rfl, okBind h⟩

theorem adv_e_le (p : Ptr) (δ : List Seg) : p.e ≤ (p.adv δ).e := by
  simp only [Ptr.adv]; exact Nat.le_add_right _ _

theorem kc_val_one {M : Mem} {n : Nat} (h : M.k n = 1) : (kc n).val M = 1 := by
  show FE.ofK (M.k n) = 1; rw [h]; rfl

theorem sum_map_range' (f : Nat → FE) (n : Nat) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := sum_map_range f n

-- `horner`'s recursion on the concrete coefficient list must not be unfolded by unification.
attribute [local irreducible] horner macChain linePts in
set_option maxHeartbeats 1000000 in
/-- **Q_acc's facts**: where its rows and assertions hold with the gate on (`M.k pb = 1`) and the
child's stream bound (`Streamed`, lanes below `T`), the six equations of `AccFacts`. -/
theorem qacc_facts {c : Ctx} {M : Mem} {sig : ByteArray} {T : Nat} {A : AccIn} {p : Ptr}
    (hS : Streamed M sig T) (hT : A.zL + 2 < T) (hH : 11 + pubLanes ≤ T) (hg : M.k A.pb = 1)
    (hpp : ∀ i, (A.pp i).ty = .E) (hτp : pubLanes ≤ 2 ^ A.τp) (hla : A.la ≤ A.dk)
    (hnf : A.fx.length ≤ 2 ^ A.dk) (hRD : A.rc.length + A.dk = accVars)
    (h : Ok c M (qacc A) p) : AccFacts A M sig := by
  have hD : accVars = 28 := rfl
  have hPL : pubLanes = 702 := rfl
  have hgv : (kc A.pb).val M = 1 := kc_val_one hg
  unfold qacc at h
  -- constants
  obtain ⟨zo, p1, evo1, epo1, o1, h⟩ := okBindE h
  obtain ⟨hz1, hz2, hz0, hone⟩ := consts_spec o1.1
  have hp1 : 1 ≤ (p.adv (consts A.pb p).2).e := by
    have := adv_e_le p (consts A.pb p).2
    have : (p.adv (consts A.pb p).2).e = p.e + 2 := by
      simp [consts, const, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes, bind_apply, pure_apply]
    omega
  have hzv : (consts A.pb p).1.1.val M = 0 := by rw [hz1]; exact hz0
  have hzE : (consts A.pb p).1.1.ty = .E := by rw [hz1]
  have hov : M.e (consts A.pb p).1.2.n = 1 := by rw [hz2]; exact hone
  have hov' : (consts A.pb p).1.2.val M = 1 := by rw [hz2]; exact hone
  -- κ'
  rw [evo1] at hzv hzE hov hov'
  rw [epo1] at hp1
  obtain ⟨kb, p2, evo2, epo2, o2, h⟩ := okBindE h
  have hk := ldEsB_spec hS (qs := (List.range A.dk).map A.kap)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [AccIn.kap, AccIn.zL, AccIn.z0, AccIn.h0] at hT ⊢; omega) o2.1
  have hp2 := le_trans hp1 (adv_e_le p1 (ldEsB ((List.range A.dk).map A.kap) p1).2)
  -- (4) PUB
  rw [evo2] at hk
  rw [epo2] at hp2
  obtain ⟨sP, p3, evo3, epo3, o3, h⟩ := okBindE h
  have hsP := qpub_spec hzv hpp hov hτp o3.1
  rw [evo3] at hsP
  obtain ⟨_vo4, p4, evo4, epo4, o4, h⟩ := okBindE h
  have e4 := assertEqE_spec o4 hgv
  -- (1) y'
  obtain ⟨y, p5, evo5, epo5, o5, h⟩ := okBindE h
  have hy := qyown_spec hla hnf hzv hov o5.1
  -- h', acc_in'
  rw [evo5] at hy
  obtain ⟨hb, p6, evo6, epo6, o6, h⟩ := okBindE h
  have hh := ldEsB_spec hS (qs := (List.range (accVars + 1)).map A.hL)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [AccIn.hL, AccIn.zL, AccIn.z0, AccIn.h0] at hT ⊢; omega) o6.1
  rw [evo6] at hh
  obtain ⟨ab, p7, evo7, epo7, o7, h⟩ := okBindE h
  have ha := ldEsB_spec hS (qs := (List.range (accVars + 1)).map accLane)
    (by intro q hq; simp only [List.mem_map, List.mem_range] at hq; obtain ⟨i, hi, rfl⟩ := hq
        simp only [accLane]; omega) o7.1
  rw [evo7] at ha
  obtain ⟨_vo8, p8, evo8, epo8, o8, h⟩ := okBindE h
  have e8 := assertEqE_spec o8 hgv
  obtain ⟨sh, p9, evo9, epo9, o9, h⟩ := okBindE h
  have hsh := macChain_spec _ _ _ o9.1
  rw [evo9] at hsh
  obtain ⟨_vo10, p10, evo10, epo10, o10, h⟩ := okBindE h
  have e10 := assertEqE_spec o10 hgv
  -- t', h'(t'), the line
  obtain ⟨t, p11, evo11, epo11, o11, h⟩ := okBindE h
  have ht := ldE_feAt hS (q := A.tL) (by simp only [AccIn.tL, AccIn.zL, AccIn.z0] at hT ⊢; omega) o11.1
  rw [evo11] at ht
  obtain ⟨hv, p12, evo12, epo12, o12, h⟩ := okBindE h
  have hhv := horner_spec (c := c) (M := M) t zo.1 hzv ((List.range (accVars + 1)).map fun j => ec (hb + j)) p11 o12.1
  rw [evo12] at hhv
  obtain ⟨pts, p13, evo13, epo13, o13, h⟩ := okBindE h
  have hpt := linePts_spec (c := c) (M := M) t ((List.range accVars).map fun i => (ec (ab + i), A.bC kb i)) p12 o13.1
  -- the current acc_in
  rw [evo13] at hpt
  obtain ⟨pc, p14, evo14, epo14, o14, h⟩ := okBindE h
  have hpc := ldEsB_val (c := c) (M := M) (qs := (List.range (accVars + 1)).map fun j => A.pb + 615 + 3 * j) (p := p13) o14.1
  rw [evo14] at hpc
  obtain ⟨_vo15, p15, evo15, epo15, o15, h⟩ := okBindE h
  have e15 := assertEqs_spec (c := c) (M := M) hgv ((List.range accVars).map fun i => (pts.getD i default, ec (pc + i))) p14 o15
  obtain ⟨_vo16, p16, evo16, epo16, o16, h⟩ := okBindE h
  have e16 := assertEqE_spec o16 hgv
  obtain ⟨zz, _qo17, evo17, epo17, o17, h⟩ := okBindE h
  have hz := ldE_feAt hS (q := A.zL) (by omega) o17.1
  rw [evo17] at hz
  have e17 := assert0_spec h.2
  rw [hgv, one_mul] at e17
  -- the facts
  have hkv : (List.range A.dk).map (fun i => M.e (kb + i)) =
      (List.range A.dk).map fun i => feAt sig (8 * A.kap i) := by
    apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    rw [hk i (by simpa using hi)]; simp [List.getD_eq_getElem?_getD, hi]
  have hhv' : ∀ j < accVars + 1, M.e (hb + j) = feAt sig (8 * A.hL j) := by
    intro j hj; rw [hh j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, hj]
  have hav : ∀ j < accVars + 1, M.e (ab + j) = feAt sig (8 * accLane j) := by
    intro j hj; rw [ha j (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, hj]
  have hHl : (List.range (accVars + 1)).map (fun j => feAt sig (8 * A.hL j)) =
      ((List.range (accVars + 1)).map fun j => ec (hb + j)).map (Cell.val M) := by
    rw [List.map_map]; apply List.map_congr_left; intro j hj; rw [List.mem_range] at hj
    simp [hhv' j hj]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e4, hsP]
  · rw [← hhv' 0 (by omega), ← hav accVars (by omega)]; exact e8
  · have hsum : sh.val M = ∑ j ∈ Finset.range (accVars + 1), feAt sig (8 * A.hL j) := by
      rw [hsh, hzv, zero_add, List.map_map, sum_map_range']
      apply Finset.sum_congr rfl; intro j hj; rw [Finset.mem_range] at hj
      simp [hov', hhv' j hj]
    have hyv : y.val M = ∑ k ∈ Finset.range A.fx.length,
        eqW ((List.range A.dk).map fun i => feAt sig (8 * A.kap i)) k * (A.fx.getD k default).val M := by
      rw [hy, ← hkv]
      apply Finset.sum_congr rfl; intro k hk'
      rw [Finset.mem_range] at hk'
      rw [List.getD_eq_getElem _ _ hk', List.getD_eq_getElem _ _ hk']
    rw [sum_map_range', ← hsum, e10, hyv]
  · intro i hi
    have hpi := hpt.2 i (by simpa using hi)
    rw [List.getD_eq_getElem ((List.range accVars).map fun i => (ec (ab + i), A.bC kb i)) _ (by simpa using hi),
      List.getElem_map, List.getElem_range] at hpi
    have hq := e15 ((pts.getD i default, ec (pc + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simp only at hq
    have hpci : M.e (pc + i) = ⟨M.k (A.pb + 615 + 3 * i), M.k (A.pb + 615 + 3 * i + 1),
        M.k (A.pb + 615 + 3 * i + 2)⟩ := by
      rw [hpc i (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_range (by omega : i < accVars + 1)]
    have hb : (A.bC kb i).val M = (A.rc.map (Cell.val M) ++
        (List.range A.dk).map fun j => feAt sig (8 * A.kap j)).getD i 0 := by
      simp only [AccIn.bC]
      by_cases hir : i < A.rc.length
      · have hir' : i < (A.rc.map (Cell.val M)).length := by simpa using hir
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hir, List.getElem?_append_left hir',
          List.getElem?_map, List.getElem?_eq_getElem hir, Option.map_some, Option.getD_some]
      · have hik : i - A.rc.length < A.dk := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
        simp only [List.length_map, List.getElem?_map, List.getElem?_range hik, Option.map_some,
          Option.getD_some]
        rw [Cell.val_E, hk (i - A.rc.length) (by simpa using hik)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_range hik]
    rw [hq, Cell.val_E, hpci, Cell.val_E, hav i (by omega), ht, hb] at hpi
    rw [← hpi]
    simp [accC, List.getD_eq_getElem?_getD, List.getElem?_range hi]
  · rw [hHl, ← ht, ← hhv, e16, Cell.val_E, hpc accVars (by simp)]
    simp [accC, List.getD_eq_getElem?_getD]
  · rw [← hz]; exact e17

end Lvm.QAcc
