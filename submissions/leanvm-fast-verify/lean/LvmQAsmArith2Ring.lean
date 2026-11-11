-- New for lvm (HAR-RC): Q_arith's four ring switches (`CH` and `KS` after their Keccak GKRs, the two
-- raw switches of the `CH` link) as one gadget `ringG` reading its six challenges and 64 slices from
-- the stream, on QA2's `coeffs` (`coeffs_eq`) and `ringTargetG` (`ringTarget_eq`); reading lemmas
-- against `F` (`ringSwitch`, `ringRaw`, HAR's `ringAt`). Searched for reuse: QA2 `LvmQRing*` (used),
-- HAR `LvmQAsmHar47` (`ringAt`, `ringSwitch_run`, used), QA1 `LvmQLinkArithRead` (`ringOf`,
-- `ringRaw_run`, used), `LvmQEqKeccakGkr` (`vk_facts`, used for the slices' lanes).
import LvmQAsmHar47
import LvmQRingTarget

/-!
# Q_arith: the ring switches

* `loadAt qs`: one `loadE` row per stream lane `q` (the `E` scalar of lanes `q, q + 1, q + 2`), the
  cells consecutive from the pointer (`loadAt_out`); `loadAt_e`, `loadAt_vs`: the cells are
  `feAt Σ (8 q)`.
* **`ringG q lb z`**: the six challenges from lanes `q + 9 i` (`sampleE` answers: the reader at
  `8 q − 40`), QA2's `coeffs` (131 rows) and `ringTargetG` over the slices at lanes `lb + 3 k`
  (4,546 rows); outputs `RingOut` = the 64 coefficient cells and the target cell.
* **`ringG_spec`**: the coefficients are `ringCoefficients (chsAt Σ q)`, the target is
  `polyEval ((slAt Σ lb).map (phiMap · chs)) gen`; `ringG_ringAt`: HAR's `ringAt` from `8 q − 40` is
  `(target, ringWeight pt · cs)`.
* **`ringSwitch_replays`**, **`ringRaw_replays`**: `Replays` of `F`'s `ringSwitch pt (slAt Σ lb)` and
  `ringRaw (slAt Σ lb)` from position `8 q − 40` to `8 q + 392`.
* `vkSpec_slices`: the slices `F`'s Keccak GKR returns are `slAt Σ (gkrEnd P qs − 192)` (the ring
  switch after a GKR reads them back from there: `ringGkr`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 DM

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

/-! ## Against `F` -/

theorem samplesAt_ring (sig : ByteArray) {q : Nat} (hq : 5 ≤ q) :
    samplesAt (feAt sig) (8 * q - 40) ringStages = chsAt sig q := by
  simp only [samplesAt, chsAt]
  refine List.map_congr_left fun i _ => ?_
  congr 1; omega

/-- **HAR's `ringAt` is the gadget's claim**: target and weight closure. -/
theorem ringG_ringAt {sig : ByteArray} {T q lb z : Nat} {p : Ptr} (pt : List FE) (hq5 : 5 ≤ q)
    (hS : Streamed M sig T) (hq : q + 48 ≤ T) (hlb : lb + 192 ≤ T) (hz : M.e z = 0)
    (h : SegsHold c M p (ringG q lb z p).2) :
    (ringAt (feAt sig) (8 * q - 40) pt (slAt sig lb)).1 = (ringG q lb z p).1.target.val M ∧
      (ringAt (feAt sig) (8 * q - 40) pt (slAt sig lb)).2 =
        fun x => ringWeight pt x (vs M (ringG q lb z p).1.cs) := by
  obtain ⟨h1, h2⟩ := ringG_spec hS hq hlb hz h
  simp only [ringAt, samplesAt_ring sig hq5, h1, h2]
  exact ⟨trivial, trivial⟩

/-- The relation of a ring switch's result to the gadget's cells. -/
def RingRel (M : Mem) (pt : List FE) (res : FE × (List FE → FE)) (o : RingOut) : Prop :=
  res.1 = o.target.val M ∧ res.2 = fun x => ringWeight pt x (vs M o.cs)

/-- **`F`'s `ringSwitch` (after a Keccak GKR) replayed by `ringG`.** -/
theorem ringSwitch_replays {sig : ByteArray} {T q lb z : Nat} {p : Ptr} (pt : List FE) (hq5 : 5 ≤ q)
    (hS : Streamed M sig T) (hq : q + 48 ≤ T) (hlb : lb + 192 ≤ T) (hz : M.e z = 0) :
    Replays c M sig (ringSwitch pt (slAt sig lb)) (ringG q lb z) p (8 * q - 40) (8 * q + 392)
      (RingRel M pt) := by
  intro hOk s hs hok
  rw [ringSwitch_run, hs]
  exact ⟨hok, by simp [pos, ringStages]; omega, ringG_ringAt pt hq5 hS hq hlb hz hOk.1⟩

/-- **`F`'s `ringRaw` (the `CH` link's switches) replayed by `ringG`.** -/
theorem ringRaw_replays {sig : ByteArray} {T q lb z : Nat} {p : Ptr} (hq5 : 5 ≤ q)
    (hS : Streamed M sig T) (hq : q + 48 ≤ T) (hlb : lb + 192 ≤ T) (hz : M.e z = 0) :
    Replays c M sig (ringRaw (slAt sig lb)) (ringG q lb z) p (8 * q - 40) (8 * q + 392)
      (fun res o => res.1 = o.target.val M ∧ res.2 = vs M o.cs) := by
  intro hOk s hs hok
  obtain ⟨h1, h2⟩ := ringG_spec hS hq hlb hz hOk.1
  rw [ringRaw_run]
  simp only [pos] at hs
  rw [hs, samplesAt_ring sig hq5]
  exact ⟨hok, by simp [pos, ringStages]; omega, h2.symm, h1.symm⟩

/-! ## After a Keccak GKR -/

/-- **The slices of `F`'s Keccak GKR** (first FS answer at lane `qs`) are the stream scalars at
lanes `gkrEnd P qs − 192 + 3 k`. -/
theorem vkSpec_slices (v : Nat → FE) {ls qs : Nat} (hls : 4 ≤ ls) (hq : 5 ≤ qs) (instV outV : List FE)
    (hinst : instV.length = ls) (ok : Bool) :
    (vkSpec v ls instV outV (8 * qs - 40) ok).1.slices =
      (List.range kBits).map fun k => v (8 * (gkrEnd (ls - 4) qs - 192 + 3 * k)) := by
  obtain ⟨h1, -, -⟩ := vk_facts v (ls - 4) qs instV outV ok hq (by omega)
  rw [show ls - 4 + 4 = ls by omega] at h1
  rw [h1]
  simp only [vkSl, kBits]
  refine List.map_congr_left fun k _ => congrArg v ?_
  simp only [gkrEnd]
  omega

/-- The ring switch after a Keccak GKR whose first FS answer is at lane `qs` (`P = ls − 4`). -/
def ringGkr (P qs z : Nat) : BM RingOut := ringG (gkrEnd P qs) (gkrEnd P qs - 192) z

/-- **The ring switch after a Keccak GKR** (HAR's `chPh_run`/`ksPh_run` form): with `F`'s GKR read
from `8 qs − 40` (`K = vkSpec …`, ending at `8 · gkrEnd − 40`), `ringAt` at the GKR's end on its
slices is the gadget's claim. -/
theorem ringGkr_ringAt {sig : ByteArray} {T ls qs z : Nat} {p : Ptr} (hls : 4 ≤ ls) (hq : 5 ≤ qs)
    (instV outV : List FE) (hinst : instV.length = ls) (ok : Bool) (hS : Streamed M sig T)
    (hT : gkrEnd (ls - 4) qs + 48 ≤ T) (hz : M.e z = 0) (h : SegsHold c M p (ringGkr (ls - 4) qs z p).2) :
    RingRel M (vkSpec (feAt sig) ls instV outV (8 * qs - 40) ok).1.slicePoint
      (ringAt (feAt sig) (8 * gkrEnd (ls - 4) qs - 40) (vkSpec (feAt sig) ls instV outV (8 * qs - 40) ok).1.slicePoint
        (vkSpec (feAt sig) ls instV outV (8 * qs - 40) ok).1.slices) (ringGkr (ls - 4) qs z p).1 := by
  have hE : 192 ≤ gkrEnd (ls - 4) qs := by simp only [gkrEnd, gkrQO]; omega
  rw [vkSpec_slices (feAt sig) hls hq instV outV hinst ok]
  exact ringG_ringAt _ (by simp only [gkrEnd, gkrQO]; omega) hS hT (by omega) hz h

/-- **The slices of QA1's GKR gadget** are the stream scalars at lanes `gkrEnd P qs − 192 + 3 k` (from
`gkr_spec`: the gadget's outputs are `F`'s `KeccakOut`). -/
theorem gkrGadget_slices {sig : ByteArray} {T P qs : Nat} {inst out : Nat → Cell} {b : Cell} {p : Ptr}
    (hP : Lvm.Q1.layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T) (hT : gkrEnd P qs ≤ T)
    (h : SegsHold c M p (gkrGadget P qs inst out b p).2) :
    ((gkrGadget P qs inst out b p).1.vals M).slices = slAt sig (gkrEnd P qs - 192) := by
  have g1 := (gkr_spec hP hq hS hT h ⟨8 * qs - 40, 0, true⟩ (by simp)).1
  rw [← g1, verifyKeccak_run sig _ _ _ _ (8 * qs - 40) (by simp),
    vkSpec_slices (feAt sig) (by omega) hq _ _ (by simp) true, Nat.add_sub_cancel]
  rfl

/-- **The ring switch after a Keccak GKR**, for any `KeccakOut` `K` whose slices are the stream's
(`gkrGadget_slices`, `vkSpec_slices`): HAR's `ringAt` at the GKR's end is the gadget's claim. -/
theorem ringGkr_rel {sig : ByteArray} {T P qs z : Nat} {p : Ptr} (K : KeccakOut) (hq : 5 ≤ qs)
    (hK : K.slices = slAt sig (gkrEnd P qs - 192)) (hS : Streamed M sig T) (hT : gkrEnd P qs + 48 ≤ T)
    (hz : M.e z = 0) (h : SegsHold c M p (ringGkr P qs z p).2) :
    RingRel M K.slicePoint (ringAt (feAt sig) (8 * gkrEnd P qs - 40) K.slicePoint K.slices)
      (ringGkr P qs z p).1 := by
  have hE : 192 ≤ gkrEnd P qs := by simp only [gkrEnd, gkrQO]; omega
  rw [hK]
  exact ringG_ringAt _ (by simp only [gkrEnd, gkrQO]; omega) hS hT (by omega) hz h

end Lvm.Har
