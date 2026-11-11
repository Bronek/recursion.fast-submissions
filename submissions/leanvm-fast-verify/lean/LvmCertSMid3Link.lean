-- WP-16b (CERT). New for lvm (O6 link, the two links): the `CH` link's and the `KS` link's
-- assembled claims (`chLinkClaimsE`, `ksLinkClaimsE`) holding on the commitments give WP-8's
-- `ChLinkClaims` and `KsLinkClaims` with WP-14c's accessors.
import LvmCertSMid3Blk

/-!
# The links' claims

* **`chLinkClaims_of`**: the two ring claims and the 17 constant lanes at `ρ'`;
* **`ksLinkClaims_of`**: the four combined claims `yC`, `inC`, `mC` (on `C_rec`), `xC`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-! ## Helpers -/

/-- Equality weights at a cube point: the indicator of the index. -/
theorem lk_eqAt_boolPoint {m z w : ℕ} (hz : z < 2 ^ m) (hw : w < 2 ^ m) :
    eqAt (boolPoint m z) w = if w = z then 1 else 0 := by
  have e := eqEval_boolPoint_eqAt (boolPoint m z) w
  rw [length_boolPoint] at e
  rw [← e, Complete.eqEval_boolPoint_boolPoint m z w hz hw]
  by_cases hwz : w = z
  · simp [hwz]
  · simp [hwz, Ne.symm hwz]

/-- A sum weighted by `eq(a ‖ sel(t), ·)` over `h + 6` coordinates is slot `t`'s. -/
theorem lk_sum_sel {h t : ℕ} {a : List E} (ha : a.length = h) (ht : t < 2 ^ 6) (F : ℕ → E) :
    ∑ n ∈ range (2 ^ (h + 6)), eqAt (a ++ selE t 6) n * F n =
      ∑ x ∈ range (2 ^ h), eqAt a x * F (x + 2 ^ h * t) := by
  have hs : (selE t 6).length = 6 := by simp [selE, selectorPoint_eq_boolPoint]
  have e := col_split (s := selE t 6) ha F
  rw [hs] at e
  rw [e, Finset.sum_eq_single t]
  · simp only [selE, selectorPoint_eq_boolPoint]
    rw [lk_eqAt_boolPoint ht ht, ite_eq_left rfl, one_mul]
  · intro o ho hne
    simp only [selE, selectorPoint_eq_boolPoint]
    rw [lk_eqAt_boolPoint ht (Finset.mem_range.1 ho), ite_eq_right hne, zero_mul]
  · intro hn
    exact absurd (Finset.mem_range.2 ht) hn

/-- A list sum over `range k` is the `Finset` sum. -/
theorem lk_sum_map_range (g : ℕ → E) :
    ∀ k, ((List.range k).map g).sum = ∑ l ∈ range k, g l
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, lk_sum_map_range g k,
      Finset.sum_range_succ]
    simp

/-- A placed point weight paired with the stack is the block's extension at the point. -/
theorem lk_sum_placed {μ : ℕ} (blk : VPlacement) (z : List E) (hz : z.length = blk.variableCount)
    (hal : 2 ^ blk.variableCount ∣ blk.index) (hfit : blk.index + 2 ^ blk.variableCount ≤ 2 ^ μ)
    (q : Column μ) :
    ∑ x : Fin (2 ^ μ), blk.eqAbove (boolPoint μ x) *
        LeanVM.Protocol.Verifier.eqEval z ((boolPoint μ x).take blk.variableCount) *
        ofK (q.values.getD x 0) =
      ∑ n ∈ range (2 ^ blk.variableCount), eqAt z n * ofK (q.values.getD (blk.index + n) 0) := by
  obtain ⟨v, off⟩ := blk
  simp only at hz hal hfit ⊢
  rw [sum_block hal hfit]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  subst hz
  rw [eqEval_boolPoint_eqAt]

/-- **A `sumClaimE` claim on its commitment** is the combination of its parts' block extensions. -/
theorem lk_holds_sumClaim {μ k : ℕ} (F : ℕ → E × VPlacement × List E) (val : E) (q : Column μ)
    (hF : ∀ l < k, (F l).2.2.length = (F l).2.1.variableCount ∧
      2 ^ (F l).2.1.variableCount ∣ (F l).2.1.index ∧
      (F l).2.1.index + 2 ^ (F l).2.1.variableCount ≤ 2 ^ μ)
    (h : StackClaim.Holds μ (sumClaimE μ ((List.range k).map F) val).onStack q) :
    ∑ l ∈ range k, (F l).1 * ∑ n ∈ range (2 ^ (F l).2.1.variableCount),
      eqAt (F l).2.2 n * ofK (q.values.getD ((F l).2.1.index + n) 0) = val := by
  have h' : ∑ x : Fin (2 ^ μ), (sumClaimE μ ((List.range k).map F) val).onStack.1 (boolPoint μ x) *
      ofK (q.values.getD x 0) = val := h
  have key : ∀ x : Fin (2 ^ μ),
      (sumClaimE μ ((List.range k).map F) val).onStack.1 (boolPoint μ x) * ofK (q.values.getD x 0) =
        ∑ l ∈ range k, (F l).1 * ((F l).2.1.eqAbove (boolPoint μ x) *
          LeanVM.Protocol.Verifier.eqEval (F l).2.2
            ((boolPoint μ x).take (F l).2.1.variableCount) * ofK (q.values.getD x 0)) := by
    intro x
    have h1 : ({ variableCount := μ, index := 0 } : VPlacement).eqAbove (boolPoint μ x) = 1 := by
      rw [eqAbove_boolPoint (by simp) x.isLt, Nat.div_eq_of_lt x.isLt, Nat.zero_div, ite_eq_left rfl]
    have h2 : (boolPoint μ x).take μ = boolPoint μ x := List.take_of_length_le (by simp)
    show ({ variableCount := μ, index := 0 } : VPlacement).eqAbove (boolPoint μ x) *
        LeanVM.Protocol.Verifier.sumE (((List.range k).map F).map fun (c, blk, z) =>
          c * blk.eqAbove ((boolPoint μ x).take μ) *
            LeanVM.Protocol.Verifier.eqEval z (((boolPoint μ x).take μ).take blk.variableCount)) *
        ofK (q.values.getD x 0) = _
    rw [h1, h2, one_mul, LeanVM.Protocol.Verifier.sumE, foldl_add_eq, zero_add, List.map_map,
      lk_sum_map_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Function.comp_apply]
    generalize F l = p
    obtain ⟨c, blk, z⟩ := p
    dsimp only
    ring
  rw [← h', Finset.sum_congr rfl fun x _ ↦ key x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  obtain ⟨hz, hal, hfit⟩ := hF l (Finset.mem_range.1 hl)
  rw [← Finset.mul_sum, lk_sum_placed _ _ hz hal hfit]


/-! ## The links -/

/-- A ring claim on `CH`'s block is the ring claim on `C_main`'s first `2^26` words. -/
theorem lk_ringCol {qm : Column 26} (ring : E × (List E → E))
    (h : StackClaim.Holds 26 (BClaim.onStack ⟨chBlk, ring.2, ring.1⟩) qm) :
    Lvm.KG.RingColTrue 20 (colM qm) ring := by
  rw [holds_onStack _ (dvd_zero _) (by simp [chBlk, slotLog])] at h
  simp only [chBlk, zero_add] at h
  exact h.symm

/-- **The `CH` link's claims.** -/
theorem chLinkClaims_of (lo : Lvm.KG.ChLinkOut) (hρ : lo.shift.1.length = 20) {qm : Column 26}
    {qr : Column 19} (h : ∀ e ∈ chLinkClaimsE lo, HoldsC qm qr e) :
    Lvm.KG.ChLinkClaims 20 (colM qm) lo := by
  refine ⟨lk_ringCol _ (h (.main, ⟨chBlk, lo.ringIn.2, lo.ringIn.1⟩) (List.mem_map.mpr
      ⟨_, List.mem_append_left _ (List.mem_cons_self ..), rfl⟩)),
    lk_ringCol _ (h (.main, ⟨chBlk, lo.ringY.2, lo.ringY.1⟩) (List.mem_map.mpr
      ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl⟩)), ?_⟩
  intro t ht8 ht25
  have hj : t - 8 < 17 := by omega
  have hc := h (.main, BClaim.point chBlk (lo.shift.1 ++ selE (8 + (t - 8)) slotLog)
      (M3.kE (if 8 + (t - 8) = 16 then ⟨(0x80 : UInt64) <<< 56⟩ else 0)))
    (List.mem_map.mpr ⟨_, List.mem_append_right _
      (List.mem_map.mpr ⟨t - 8, List.mem_range.mpr hj, rfl⟩), rfl⟩)
  have hc' := (holds_point (μ := 26) (v := 20 + 6) (off := 0) (dvd_zero _) (by norm_num) _
    (by simp [hρ, selE, selectorPoint_eq_boolPoint, slotLog]) _ qm).mp hc
  rw [show 8 + (t - 8) = t by omega, show slotLog = 6 from rfl] at hc'
  simp only [zero_add] at hc'
  rw [lk_sum_sel hρ (by omega)] at hc'
  unfold LeanVM.Protocol.KeccakGkr.stepMle
  refine hc'.trans ?_
  unfold Lvm.KG.padConstLane
  split_ifs <;> rfl


/-- **The `KS` link's claims.** -/
theorem ksLinkClaims_of (kchal : List E) (kshift : List E × E) (vals : List E)
    (h1 : kchal.length = 20) (h2 : kshift.1.length = 15) {qm : Column 26} {qr : Column 19}
    (h : ∀ e ∈ ksLinkClaimsE kchal kshift vals, HoldsC qm qr e) :
    Lvm.KG.KsLinkClaims 15 14 (ksCol qm) (Lvm.KG.ksYRow 15 ksY2 (colM qm) (ksCol qm)) (msgM qr)
      (msgX qm) (kchal, kshift, vals) := by
  have hlam : (kchal.drop 15).length = 5 := by simp [h1]
  have hom : ∀ l < 25, (LeanVM.Protocol.Verifier.eqKernel (kchal.drop 15)).getD l 0 =
      eqAt (kchal.drop 15) l := fun l hl ↦ by
    rw [eqKernel_getD, hlam, ite_eq_left (by omega)]
  have hlo : (kshift.1.take 14).length = 14 := by simp [h2]
  have hy := h _ (List.mem_cons_self ..)
  have hi := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hm := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hx := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := lk_holds_sumClaim (μ := 26) (k := 25) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 15)).getD l 0, (ksYPartE l kshift.1).1,
        (ksYPartE l kshift.1).2)) (vals.getD 0 0) qm ?_ hy
    · dsimp only at e ⊢
      rw [← e]
      refine Finset.sum_congr rfl fun l hl ↦ ?_
      have hl' := Finset.mem_range.1 hl
      rw [hom l hl']
      refine congrArg (eqAt (kchal.drop 15) l * ·) ?_
      unfold LeanVM.Protocol.KeccakGkr.stepMle
      by_cases hl14 : l < 14
      · simp only [ksYPartE, hl14, ↓reduceIte]
        rw [show slotLog = 6 from rfl, lk_sum_sel h2 (by omega)]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [Lvm.KG.ksYRow, Lvm.KG.ksY, hl14, ↓reduceIte, ksCol, Lvm.NS.wd]
      · simp only [ksYPartE, hl14, ↓reduceIte]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp only [Lvm.KG.ksYRow, Lvm.KG.ksY, hl14, ↓reduceIte, colM, Lvm.NS.wd, ksY2Off, ksY2]
    · intro l hl
      dsimp only
      by_cases hl14 : l < 14
      · simp only [ksYPartE, hl14, ↓reduceIte]
        exact ⟨by simp [h2, selE, selectorPoint_eq_boolPoint, slotLog], ⟨25, by norm_num [slotLog]⟩,
          by norm_num [slotLog]⟩
      · simp only [ksYPartE, hl14, ↓reduceIte]
        exact ⟨h2, ⟨56 * 2 ^ 5 + (l - 14), by rw [ksY2Off]; ring⟩, by rw [ksY2Off]; norm_num; omega⟩
  · have e := lk_holds_sumClaim (μ := 26) (k := 25) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 15)).getD l 0,
        ({ variableCount := 15 + slotLog, index := 50 * 2 ^ 20 } : VPlacement),
        kshift.1 ++ selE l slotLog)) (vals.getD 1 0) qm
      (fun l hl ↦ by
        dsimp only
        exact ⟨by simp [h2, selE, selectorPoint_eq_boolPoint, slotLog], ⟨25, by norm_num [slotLog]⟩,
          by norm_num [slotLog]⟩) hi
    dsimp only at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l hl']
    refine congrArg (eqAt (kchal.drop 15) l * ·) ?_
    unfold LeanVM.Protocol.KeccakGkr.stepMle
    rw [show slotLog = 6 from rfl, lk_sum_sel h2 (by omega)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [ksCol, Lvm.NS.wd]
  · have e := lk_holds_sumClaim (μ := 19) (k := 17) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 15)).getD l 0,
        ({ variableCount := 14, index := l * 2 ^ 14 } : VPlacement), kshift.1.take 14))
      (vals.getD 2 0) qr
      (fun l hl ↦ ⟨hlo, ⟨l, by ring⟩, by
        have : l * 2 ^ 14 + 2 ^ 14 ≤ 17 * 2 ^ 14 := by nlinarith
        calc _ ≤ 17 * 2 ^ 14 := this
          _ ≤ 2 ^ 19 := by norm_num⟩) hm
    dsimp only at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l (by omega)]
    unfold LeanVM.Protocol.KeccakGkr.stepMle
    refine congrArg (eqAt (kchal.drop 15) l * ·) (Finset.sum_congr rfl fun x _ ↦ ?_)
    simp only [msgM, Lvm.NS.wd]
  · have e := lk_holds_sumClaim (μ := 26) (k := 17) (fun l ↦
      ((LeanVM.Protocol.Verifier.eqKernel (kchal.drop 15)).getD l 0,
        ({ variableCount := 14, index := xOff + l * 2 ^ 14 } : VPlacement), kshift.1.take 14))
      (vals.getD 3 0) qm
      (fun l hl ↦ ⟨hlo, ⟨56 * 2 ^ 6 + 2 ^ 5 + l, by rw [xOff]; ring⟩, by
        have : l * 2 ^ 14 + 2 ^ 14 ≤ 17 * 2 ^ 14 := by nlinarith
        rw [add_assoc]
        calc _ ≤ xOff + 17 * 2 ^ 14 := Nat.add_le_add_left this _
          _ ≤ 2 ^ 26 := by rw [xOff]; norm_num⟩) hx
    dsimp only at e ⊢
    rw [← e]
    refine Finset.sum_congr rfl fun l hl ↦ ?_
    have hl' := Finset.mem_range.1 hl
    rw [hom l (by omega)]
    unfold LeanVM.Protocol.KeccakGkr.stepMle
    have hidx : xOff + l * 2 ^ 14 = ksY2 + 2 ^ 19 + l * 2 ^ 14 := by simp only [xOff, ksY2]
    refine congrArg (eqAt (kchal.drop 15) l * ·) (Finset.sum_congr rfl fun x _ ↦ ?_)
    simp only [msgX, Lvm.NS.wd, hidx]

end Lvm.ASM
