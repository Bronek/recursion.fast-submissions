-- New for lvm (HAR-RC): Q_arith's four ring switches (`CH` and `KS` after their Keccak GKRs, the two
-- raw switches of the `CH` link) as one gadget `ringG` reading its six challenges and 64 slices from
-- the stream, on QA2's `coeffs` (`coeffs_eq`) and `ringTargetG` (`ringTarget_eq`); reading lemmas
-- against `F` (`ringSwitch`, `ringRaw`, HAR's `ringAt`). Searched for reuse: QA2 `LvmQRing*` (used),
-- HAR `LvmQAsmHar47` (`ringAt`, `ringSwitch_run`, used), QA1 `LvmQLinkArithRead` (`ringOf`,
-- `ringRaw_run`, used), `LvmQEqKeccakGkr` (`vk_facts`, used for the slices' lanes).
import LvmQAsmHar47
import LvmQRingG

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

variable {c : Ctx} {M : Mem}

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
