-- WP-13b: the decoder's correctness from WP-7's extraction facts (`LvmWhirDoom.ud_extract_rec20_l0`); new.
import LvmXDecLv
import LvmWhirDoom

/-!
# The decoder returns the unique candidate's message

WP-7's `ud_extract_rec20_l0`: for a committed word `W` of `C_rec` (`μ = 19`, `R = 2`, threshold
`udThr 13 2`), the fold challenges `α ∈ E^6` and the final residual `f`, if neither the commitment
nor the residual is doomed, there is exactly one candidate `q` (a `K`-valued stack whose lane-wise
encoding agrees with `W` on `≥ thr` columns), it is good, `f = foldMsg α q`, and off the luck
event the agreement set of the folded word with `Enc(f)` is the word's agreement set with `q`.

**`decodeRec_of_ud`**: then, off the luck event for that `q`, the pure decoder on the word's leaf
words (`wdOf W`), the challenges (`alphaN α`) and the residual's coefficients (`fNr f`) returns
`q`'s `2^19` words. The leaves are assumed to have 64 words (`wordOf`'s rows are well shaped).

The bridges: `eqW_eq_eqA` (the fold weights), `laneRows_eq` (lane `u` is leaf word `63 − ⟨u⟩`),
`encRows_eq` (`q`'s lane encoding is `cwRec` of its words), `foldAll_laneRows_eq` (the fold is
`foldAt`), `enc_fN` (`Enc(f)` is `enc0 (fNr f)`), `fN_foldMsg` (the residual is the fold of `q`'s
words).
-/

namespace Lvm.X

open Finset Lvm.Nb CompPoly.Extension BF64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd

/-! ## The decoder's inputs from WP-7's objects -/

/-- The decoder's word: leaf word `t` at position `q` of the committed word (`0` past the leaf). -/
def wdOf (W : Compile.Word) (q t : ℕ) : BF64 := (W q).getD t 0

/-- The fold challenges, `ℕ`-indexed. -/
def alphaN (α : Fin laneBits → E) (i : ℕ) : Ext3 := if h : i < 6 then α ⟨i, h⟩ else 0

/-- The residual's coefficients, `ℕ`-indexed (`v ↦ f(bits v)`). -/
def fNr (f : (Fin (19 - laneBits) → Bool) → E) (v : ℕ) : Ext3 :=
  if h : v < 2 ^ 13 then f ((bitsEquiv 13).symm ⟨v, h⟩) else 0

/-- A stack's `2^19` words. -/
def msgOf (q : Column 19) (i : ℕ) : BF64 := q.values.getD i 0

/-! ## The bridges -/

theorem bitsEquiv_symm_bitsToNat {κ : ℕ} (u : Fin κ → Bool) :
    (bitsEquiv κ).symm ⟨bitsToNat u, bitsToNat_lt u⟩ = u := by
  apply (bitsEquiv κ).injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (bitsEquiv_val u).symm

theorem cube_sum64 {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ u : Fin laneBits → Bool, F (bitsToNat u) = ∑ l ∈ range 64, F l := sum_cube 6 F

theorem lt15 {n : ℕ} (x : Fin (2 ^ (19 - laneBits + 2))) (h : n = x) : n < 2 ^ 15 :=
  h ▸ x.isLt.trans_le (by norm_num)

/-- **The fold weights**: `eqW α u = eq(α, ⟨u⟩)`. -/
theorem eqW_eq_eqA (α : Fin laneBits → E) (u : Fin laneBits → Bool) :
    eqW α u = eqA (alphaN α) (bitsToNat u) := by
  rw [eqW, eqA, eqBits, bitSel, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [testBit_bitsToNat u i]
  simp [alphaN, i.isLt]

theorem getD_reverse64 {L : List BF64} (hL : L.length = 64) {l : ℕ} (hl : l < 64) :
    L.reverse.getD l 0 = L.getD (63 - l) 0 := by
  rw [List.getD_eq_getElem _ _ (by simp [hL]; omega), List.getD_eq_getElem _ _ (by omega),
    List.getElem_reverse]
  congr 1; omega

/-- **Lane `u` is leaf word `63 − ⟨u⟩`.** -/
theorem laneRows_eq (W : Compile.Word) (hW : ∀ v < 2 ^ 15, (W v).length = 64)
    (u : Fin laneBits → Bool) (x : Fin (2 ^ (19 - laneBits + 2))) :
    laneRows 19 2 W u x = ofK (rowW (wdOf W) (bitsToNat u) x) := by
  rw [laneRows, laneWord, laneOf, bitsEquiv_val, rowW, wdOf, ofK_eq,
    getD_reverse64 (hW x (lt15 x rfl)) (bitsToNat_lt u)]

/-- **`q`'s lane encoding is `cwRec` of its words.** -/
theorem encRows_eq (q : Column 19) (u : Fin laneBits → Bool) (x : Fin (2 ^ (19 - laneBits + 2))) :
    encRows 19 2 q u x = ofK (cwRec (msgOf q) (bitsToNat u) x) := by
  have hx : (x : ℕ) < 2 ^ 15 := lt15 x rfl
  rw [encRows, enc_apply, cwRec, Lvm.X.ofK, map_sum,
    ← sum_cube 13 (fun v => algebraMap BF64 Ext3 (msgOf q (bitsToNat u * 2 ^ 13 + v) * nbAt v x))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [blockOf, bitsEquiv_val, map_mul, nbAt_eq_novelAt ((bitsToNat_lt y).trans (by norm_num)),
    ← Lvm.X.ofK, ← Lvm.X.ofK, ofK_eq, ofK_eq, msgOf]
  have e : bitsToNat y + 2 ^ (19 - laneBits) * bitsToNat u = bitsToNat u * 2 ^ 13 + bitsToNat y := by
    rw [show (2 : ℕ) ^ (19 - laneBits) = 2 ^ 13 from rfl]; ring
  rw [e]

/-- **The fold of the lanes is `foldAt`.** -/
theorem foldAll_laneRows_eq (W : Compile.Word) (hW : ∀ v < 2 ^ 15, (W v).length = 64)
    (α : Fin laneBits → E) (r : Fin 0 → Bool) (x : Fin (2 ^ (19 - laneBits + 2))) :
    foldAll α (laneRows 19 2 W) r x = foldAt (alphaN α) (wdOf W) x := by
  rw [foldAll_eq_sum, foldAt, ← cube_sum64 (fun l => eqA (alphaN α) l * ofK (rowW (wdOf W) l x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [laneRows_eq W hW, eqW_eq_eqA]

/-- **`Enc(f)` is `Enc₀` of the coefficients.** -/
theorem enc_fN (f : (Fin (19 - laneBits) → Bool) → E) (x : Fin (2 ^ (19 - laneBits + 2))) :
    enc (19 - laneBits) 2 f x = enc0 (fNr f) x := by
  rw [enc_apply, enc0, ← sum_cube 13 (fun v => fNr f v * ofK (nbAt v x))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [nbAt_eq_novelAt ((bitsToNat_lt u).trans (by norm_num)), ofK_eq]
  unfold fNr
  split
  · rename_i h
    congr 1
    exact congrArg f (bitsEquiv_symm_bitsToNat u).symm
  · rename_i h
    exact absurd (bitsToNat_lt u) h

/-- **The residual is the fold of `q`'s words.** -/
theorem fN_foldMsg (α : Fin laneBits → E) (q : Column 19) {v : ℕ} (hv : v < 2 ^ 13) :
    fNr (foldMsg α q) v = ∑ l ∈ range 64, eqA (alphaN α) l * ofK (msgOf q (l * 2 ^ 13 + v)) := by
  rw [fNr, dif_pos hv, foldMsg, Finset.sum_apply]
  rw [← cube_sum64 (fun l => eqA (alphaN α) l * ofK (msgOf q (l * 2 ^ 13 + v)))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, eqW_eq_eqA, blockOf, bitsEquiv_val, msgOf, ofK_eq]
  have h : bitsToNat ((bitsEquiv 13).symm ⟨v, hv⟩) = v := by
    rw [← bitsEquiv_val, Equiv.apply_symm_apply]
  have e : bitsToNat ((bitsEquiv 13).symm ⟨v, hv⟩) + 2 ^ (19 - laneBits) * bitsToNat u =
      bitsToNat u * 2 ^ 13 + v := by
    rw [h, show (2 : ℕ) ^ (19 - laneBits) = 2 ^ 13 from rfl]; ring
  rw [e]

/-! ## The theorem -/

/-- **The decoder returns the unique candidate's message** (BLUEPRINT §6.2, from WP-7's
`ud_extract_rec20_l0`): not doomed after the commitment and after the residual, and not lucky. -/
theorem decodeRec_of_ud (Good : Column 19 → Prop) (W : Compile.Word) (α : Fin laneBits → E)
    (f : (Fin (19 - laneBits) → Bool) → E) (hW : ∀ v < 2 ^ 15, (W v).length = 64)
    (hC : ¬ CommitDoomUd 19 2 (udThr 13 2) Good W)
    (hF : ¬ FinalDoomUd 19 2 (udThr 13 2) (by norm_num) W α f) :
    ∃ q ∈ Candidates 19 2 (udThr 13 2) W, Good q ∧
      (∀ q' ∈ Candidates 19 2 (udThr 13 2) W, q' = q) ∧
      (¬ FoldAllLuck α (laneRows 19 2 W) (encRows 19 2 q) →
        decodeRec (wdOf W) (alphaN α) (fNr f) = some ((List.range (2 ^ 19)).map (msgOf q))) := by
  obtain ⟨q, hq, hG, huniq, hf, hcard, hluck⟩ := ud_extract_rec20_l0 Good W α f hC hF
  refine ⟨q, hq, hG, huniq, fun hL => ?_⟩
  have hfx : ∀ x : Fin (2 ^ (19 - laneBits + 2)),
      x ∈ agreeSet (laneRows 19 2 W) (encRows 19 2 q) ↔
        ∀ l < 64, rowW (wdOf W) l x = cwRec (msgOf q) l x := by
    intro x
    rw [mem_agreeSet]
    constructor
    · intro h l hl
      have := h ((bitsEquiv laneBits).symm ⟨l, hl⟩)
      rw [laneRows_eq W hW, encRows_eq] at this
      have hb : bitsToNat ((bitsEquiv laneBits).symm ⟨l, hl⟩) = l := by
        rw [← bitsEquiv_val, Equiv.apply_symm_apply]
      rw [hb] at this
      exact (algebraMap BF64 Ext3).injective this
    · intro h u
      rw [laneRows_eq W hW, encRows_eq, h _ (bitsToNat_lt u)]
  refine decodeRec_correct_ud (wdOf W) (alphaN α) (fNr f) (msgOf q) ?_ ?_ ?_
  · -- closeness: the agreement set maps into `closeSet`
    refine hcard.trans (le_of_le_of_eq (Finset.card_le_card_of_injOn (fun x => (x : ℕ)) ?_
      (fun a _ b _ h => Fin.ext h)) rfl)
    intro x hx
    have hx' := (hfx x).1 hx
    simp only [Finset.coe_filter, closeSet, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨lt15 x rfl, hx'⟩
  · intro v hv
    rw [hf]; exact fN_foldMsg α q hv
  · intro x hx hfold l hl
    have hmem : (⟨x, hx.trans_le (by norm_num)⟩ : Fin (2 ^ (19 - laneBits + 2))) ∈
        agreeSet (foldAll α (laneRows 19 2 W)) (fun _ ↦ enc (19 - laneBits) 2 f) := by
      rw [mem_agreeSet]
      intro r
      rw [foldAll_laneRows_eq W hW, enc_fN]
      exact hfold
    rw [hluck hL] at hmem
    exact (hfx _).1 hmem l hl

/-- `decodeRec_of_ud` for a well-shaped word (`wordOf`'s rows have `64` words, `wellShaped_wordOf`). -/
theorem decodeRec_of_ud_ws (Good : Column 19 → Prop) (W : Compile.Word) (α : Fin laneBits → E)
    (f : (Fin (19 - laneBits) → Bool) → E) (hW : WellShaped 64 W)
    (hC : ¬ CommitDoomUd 19 2 (udThr 13 2) Good W)
    (hF : ¬ FinalDoomUd 19 2 (udThr 13 2) (by norm_num) W α f) :
    ∃ q ∈ Candidates 19 2 (udThr 13 2) W, Good q ∧
      (∀ q' ∈ Candidates 19 2 (udThr 13 2) W, q' = q) ∧
      (¬ FoldAllLuck α (laneRows 19 2 W) (encRows 19 2 q) →
        decodeRec (wdOf W) (alphaN α) (fNr f) = some ((List.range (2 ^ 19)).map (msgOf q))) :=
  decodeRec_of_ud Good W α f (fun v _ => hW v) hC hF

end Lvm.X
