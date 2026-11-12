-- New for lvm2 (T-Q): v1's ring-switch gadget (`ringG`, HAR-RC's, from `LvmQAsmArith2Ring`) and
-- its cell spec, moved below the assembly modules so that the S2 wire gadget (`LvmQWire`) can use
-- it without the v1 phase cut. Unchanged text; `vs` moved here from `LvmQAsmHarBase`.
import LvmQRingTarget
import LvmQSumcheckCore

/-!
# The ring-switch gadget (`ringG`)

* `loadAt qs`: one `loadE` row per stream lane `q`; `loadAt_e`, `loadAt_vs`: the cells are
  `feAt Σ (8 q)`.
* **`ringG q lb z`**: the six challenges from lanes `q + 9 i`, QA2's `coeffs` and `ringTargetG`
  over the slices at lanes `lb + 3 k`; outputs `RingOut` = the 64 coefficient cells and the target.
* **`ringG_spec`**: the coefficients are `ringCoefficients (chsAt Σ q)`, the target is
  `polyEval ((slAt Σ lb).map (phiMap · chs)) gen`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM

/-- The values of a list of cells. -/
def vs (M : Mem) (l : List Cell) : List FE := l.map (Cell.val M)

/-! ## Loading stream scalars -/

/-- One `loadE` row per lane `q`: the stream's `E` scalar at lanes `q, q + 1, q + 2`. -/
def loadAt : List Nat → BM (List Cell)
  | [] => pure []
  | q :: qs => do
    let c ← loadE (kc q) (kc (q + 1)) (kc (q + 2))
    let cs ← loadAt qs
    pure (c :: cs)

variable {c : Ctx} {M : Mem}

theorem loadE_out (a₀ a₁ a₂ : Cell) (p : Ptr) : (loadE a₀ a₁ a₂ p).1 = ec p.e := rfl

theorem loadE_adv (a₀ a₁ a₂ : Cell) (p : Ptr) : p.adv (loadE a₀ a₁ a₂ p).2 = ⟨p.k, p.e + 1⟩ := by
  simp [loadE, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]

theorem loadAt_adv : ∀ (qs : List Nat) (p : Ptr), p.adv (loadAt qs p).2 = ⟨p.k, p.e + qs.length⟩
  | [], p => by simp [loadAt, pure_apply]
  | q :: qs, p => by
    simp only [loadAt]
    rw [bind_adv_eq (loadE_out _ _ _ _) (loadE_adv _ _ _ _), bind_apply, Ptr.adv_append,
      loadAt_adv qs]
    simp only [pure_apply, Ptr.adv_nil, List.length_cons, Ptr.mk.injEq, true_and]
    omega

theorem loadAt_out : ∀ (qs : List Nat) (p : Ptr),
    (loadAt qs p).1 = (List.range qs.length).map fun i => ec (p.e + i)
  | [], p => rfl
  | q :: qs, p => by
    simp only [loadAt]
    rw [bind_fst_eq (loadE_out _ _ _ _) (loadE_adv _ _ _ _), bind_apply, loadAt_out qs]
    simp only [pure_apply, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1
    omega

theorem loadAt_e {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) :
    ∀ (qs : List Nat) (p : Ptr), (∀ q ∈ qs, q + 2 < T) → SegsHold c M p (loadAt qs p).2 →
      ∀ i < qs.length, M.e (p.e + i) = feAt sig (8 * qs.getD i 0)
  | [], _, _, _, i, hi => absurd hi (by simp)
  | q :: qs, p, hq, h, i, hi => by
    simp only [loadAt] at h
    rw [hold_bind_eq (loadE_out _ _ _ _) (loadE_adv _ _ _ _), hold_bind] at h
    obtain ⟨h1, h2, -⟩ := h
    cases i with
    | zero =>
      have e := loadE_spec h1
      simp only [loadE_out, Cell.val_E, Cell.val_K] at e
      rw [Nat.add_zero, e, load_feAt hS (hq q (by simp))]
      rfl
    | succ i =>
      have e := loadAt_e hS qs _ (fun q' hq' => hq q' (by simp [hq'])) h2 i
        (by simpa using hi)
      rw [show p.e + (i + 1) = p.e + 1 + i by omega, e]
      rfl

/-- The values of `loadAt`'s cells. -/
theorem loadAt_vs {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (qs : List Nat) (p : Ptr)
    (hq : ∀ q ∈ qs, q + 2 < T) (h : SegsHold c M p (loadAt qs p).2) :
    vs M (loadAt qs p).1 = qs.map fun q => feAt sig (8 * q) := by
  rw [loadAt_out]
  refine List.ext_getElem (by simp [vs]) fun i h1 h2 => ?_
  simp only [vs, List.length_map, List.length_range] at h1
  simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
  rw [loadAt_e hS qs p hq h i h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  rfl

/-! ## The ring-switch gadget -/

/-- The lanes of a ring switch's six challenges (`sampleE` answers from the reader at `8 q − 40`). -/
def ringLanes (q : Nat) : List Nat := (List.range ringStages).map fun i => q + 9 * i

/-- The six challenges at lanes `q + 9 i`. -/
def chsAt (sig : ByteArray) (q : Nat) : List FE :=
  (List.range ringStages).map fun i => feAt sig (8 * (q + 9 * i))

/-- The 64 slices at lanes `lb + 3 k`. -/
def slAt (sig : ByteArray) (lb : Nat) : List FE :=
  (List.range kBits).map fun k => feAt sig (8 * (lb + 3 * k))

/-- A ring switch's output cells. -/
structure RingOut where
  /-- The 64 Frobenius coefficients `c_k` (`ringCoefficients`). -/
  cs : List Cell
  /-- The target `Σ_i g^i Φ(s_i)`. -/
  target : Cell

/-- **A ring switch**: the challenges from lanes `q + 9 i`, the slices from lanes `lb + 3 k`, `z` an
`E` zero cell. -/
def ringG (q lb z : Nat) : BM RingOut := do
  let p ← getPtr
  let _ ← loadAt (ringLanes q)
  let cb ← coeffs p.e z
  let t ← ringTargetG lb p.e z
  pure ⟨(List.range kBits).map fun k => ec (cb + k), ec t⟩

theorem ringG_out (q lb z : Nat) (p : Ptr) :
    (ringG q lb z p).1 = ⟨(List.range kBits).map fun k => ec (p.e + 6 + 67 + k), ec (p.e + 6 + 131 + 4545)⟩ := by
  simp only [ringG]
  rw [bind_fst_eq (getPtr_out _) (getPtr_adv _), bind_fst_eq rfl (loadAt_adv _ _),
    bind_fst_eq (coeffs_out _ _ _) (coeffs_adv _ _ _), bind_fst_eq (ringTargetG_out _ _ _ _)
      (ringTargetG_adv _ _ _ _)]
  simp [pure_apply, ringLanes, ringStages]

/-- **The ring-switch gadget's cells.** -/
theorem ringG_spec {sig : ByteArray} {T q lb z : Nat} {p : Ptr} (hS : Streamed M sig T)
    (hq : q + 48 ≤ T) (hlb : lb + 192 ≤ T) (hz : M.e z = 0) (h : SegsHold c M p (ringG q lb z p).2) :
    vs M (ringG q lb z p).1.cs = ringCoefficients (chsAt sig q) ∧
      (ringG q lb z p).1.target.val M = polyEval ((slAt sig lb).map (phiMap · (chsAt sig q))) gen := by
  simp only [ringG] at h
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq rfl (loadAt_adv _ _)] at h
  obtain ⟨hL, h⟩ := h
  rw [hold_bind_eq (coeffs_out _ _ _) (coeffs_adv _ _ _)] at h
  obtain ⟨hC, h⟩ := h
  rw [hold_bind] at h
  obtain ⟨hT, -⟩ := h
  have hlen : (ringLanes q).length = 6 := by simp [ringLanes, ringStages]
  simp only [hlen] at hC hT
  have hcl : (chsAt sig q).length = 6 := by simp [chsAt, ringStages]
  have hch : ∀ i < 6, M.e (p.e + i) = (chsAt sig q).getD i 0 := by
    intro i hi
    rw [loadAt_e hS (ringLanes q) p (fun q' hq' => by
      simp only [ringLanes, ringStages, List.mem_map, List.mem_range] at hq'
      obtain ⟨j, hj, rfl⟩ := hq'; omega) hL i (by rw [hlen]; exact hi)]
    simp [ringLanes, chsAt, ringStages, List.getD_eq_getElem?_getD, List.getElem?_range hi]
  have hco := coeffs_eq hcl hch hz hC
  have hsl : (slAt sig lb).length = 64 := by simp [slAt, kBits]
  have hs : ∀ i < 64, (⟨M.k (lb + 3 * i), M.k (lb + 1 + 3 * i), M.k (lb + 2 + 3 * i)⟩ : FE) =
      (slAt sig lb).getD i 0 := by
    intro i hi
    rw [hS _ (by omega), hS _ (by omega), hS _ (by omega)]
    simp only [slAt, kBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some, feAt]
    congr 2 <;> omega
  have hta := ringTarget_eq hcl hch hz hsl hs hT
  rw [ringG_out]
  refine ⟨?_, ?_⟩
  · refine List.ext_getElem (by simp [vs, kBits, ringCoefficients]) fun k h1 h2 => ?_
    simp only [vs, List.length_map, List.length_range, kBits] at h1
    simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
    rw [hco k h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  · rw [← hta, ringTargetG_out]
    rfl

end Lvm.Har
