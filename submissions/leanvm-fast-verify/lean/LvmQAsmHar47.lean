-- New for lvm (HAR): `F`'s phases 4–7 (`chPh`, `chLinkPh`, `ksPh`, `ksLinkPh`) as functions of the
-- reader position, and the loads of `phases47` as stream values (composition of WP-16a's wiring with
-- QA1's `gkr_spec`, `chLink_sound`, `ksLink_sound`).
import LvmQAsmArith2P47
import LvmQAsmHarBase
import LvmQEqKeccakGkr
import LvmQBusBase

/-!
# Phases 4–7: the reading

* `ringSwitch_run`: a ring switch reads 6 challenges and moves the position by `72·6`.
* `chPh_run`, `ksPh_run`: the instance point, the lanes, the Keccak GKR (`verifyKeccak_run`), the
  ring switch, from any position.
* `chLinkPh_run`, `ksLinkPh_run`: QA1's `chLinkPhase_run`/`ksLinkPhase_run` without the `require`
  (which `decideProgH` does after the phase).
* `loadEs_val`: a `loadEs` cell is the stream's scalar (`phases47`'s points and lanes).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-! ## The reading -/

/-- The value of a ring switch at the challenges read at `P` (`ringSwitch`'s result). -/
def ringAt (v : Nat → FE) (P : Nat) (point s : List FE) : FE × (List FE → FE) :=
  let chs := samplesAt v P ringStages
  (polyEval (s.map (phiMap · chs)) gen, fun rPrime => ringWeight point rPrime (ringCoefficients chs))

theorem ringSwitch_run (sig : ByteArray) (point s : List FE) (st : RS) :
    ringSwitch point s sig st = (ringAt (feAt sig) (pos st) point s, ⟨pos st + 72 * ringStages, 0, st.ok⟩) := by
  rw [show ringSwitch point s = (samples ringStages >>= fun challenges =>
    pure (polyEval (s.map (phiMap · challenges)) gen,
      fun rPrime => ringWeight point rPrime (ringCoefficients challenges))) from rfl,
    bind_run, samples_run sig ringStages st (by decide), pure_run]
  rfl

/-- The positions of phase 4 (or 6) from its start `P` with `ls` instance coordinates: the lanes, the GKR. -/
def kV (ls P : Nat) : Nat := P + 72 * ls
def kG (ls P : Nat) : Nat := kV ls P + 24 * lanes

/-- **Phase 4 (and 6) from position `P`**: the point and lanes read at `P`, the GKR's `vkSpec`, the ring
switch at the GKR's end. -/
theorem kPh_run (sig : ByteArray) (ls : Nat) (hls : 1 ≤ ls) (s : RS) :
    (do let r ← samples ls; let v ← readEs lanes; let ko ← verifyKeccak ls r v
        let ring ← ringSwitch ko.slicePoint ko.slices; pure (r, v, ko, ring) : DM _) sig s =
      let r := samplesAt (feAt sig) (pos s) ls
      let v := scalarsAt (feAt sig) (kV ls (pos s) + 40) lanes
      let K := vkSpec (feAt sig) ls r v (kG ls (pos s)) s.ok
      ((r, v, K.1, ringAt (feAt sig) (K.2.2 + 24 * kBits) K.1.slicePoint K.1.slices),
        ⟨K.2.2 + 24 * kBits + 72 * ringStages, 0, K.2.1⟩) := by
  rw [bind_run, samples_run sig ls s hls]
  dsimp only
  rw [bind_run, readEs_run]
  dsimp only
  rw [bind_run, verifyKeccak_run sig ls _ _ _ (kG ls (pos s)) (by simp [kG, kV, pos])]
  dsimp only
  rw [bind_run, ringSwitch_run, pure_run]
  simp only [pos, samplesAt, kV, Nat.add_zero]

theorem chPh_run (p : Params) (hn : 1 ≤ p.logN) (sig : ByteArray) (s : RS) :
    chPh p sig s =
      let r := samplesAt (feAt sig) (pos s) p.logN
      let v := scalarsAt (feAt sig) (kV p.logN (pos s) + 40) lanes
      let K := vkSpec (feAt sig) p.logN r v (kG p.logN (pos s)) s.ok
      ((r, v, K.1, ringAt (feAt sig) (K.2.2 + 24 * kBits) K.1.slicePoint K.1.slices),
        ⟨K.2.2 + 24 * kBits + 72 * ringStages, 0, K.2.1⟩) :=
  kPh_run sig p.logN hn s

theorem ksPh_run (p : Params) (hn : 1 ≤ p.ksLog) (sig : ByteArray) (s : RS) :
    ksPh p sig s =
      let r := samplesAt (feAt sig) (pos s) p.ksLog
      let v := scalarsAt (feAt sig) (kV p.ksLog (pos s) + 40) lanes
      let K := vkSpec (feAt sig) p.ksLog r v (kG p.ksLog (pos s)) s.ok
      ((r, v, K.1, ringAt (feAt sig) (K.2.2 + 24 * kBits) K.1.slicePoint K.1.slices),
        ⟨K.2.2 + 24 * kBits + 72 * ringStages, 0, K.2.1⟩) :=
  kPh_run sig p.ksLog hn s

/-- **Phase 5 from position `P`** (QA1's reading; the link's check is `decideProgH`'s `require`). -/
theorem chLinkPh_run (p : Params) (m : M3) (r w : List FE) (pub : Pub) (sig : ByteArray) (s : RS)
    (hn : 1 ≤ p.logN) :
    chLinkPh p m r w pub sig s =
      (m.chLink (chLinkView p m (feAt sig) (pos s) r w pub), ⟨chP6 p (pos s), 0, s.ok⟩) := by
  unfold chLinkPh
  rw [bind_run, samples_run sig _ s (by omega)]
  dsimp only
  rw [bind_run, sumcheck_run sig 3 (by omega)]
  dsimp only
  rw [bind_run, readEs_run]
  dsimp only
  rw [bind_run, ringRaw_run]
  dsimp only
  rw [bind_run, sumcheck_run sig 3 (by omega)]
  dsimp only
  rw [bind_run, readEs_run]
  dsimp only
  rw [bind_run, ringRaw_run]
  dsimp only
  rw [bind_run, samples_run sig _ _ (by decide)]
  dsimp only
  rw [scState_replicate_lk _ _ hn, show ([none, none] : List (Option FE)) = List.replicate 2 none from rfl,
    scState_replicate_lk _ _ (by decide)]
  simp only [Nat.add_zero, Nat.zero_add]
  rw [show (List.replicate 2 none : List (Option FE)) = [none, none] from rfl]
  unfold pos
  generalize s.ent + s.msg = P
  rw [pure_run]
  rfl

theorem ksLinkPh_run (p : Params) (m : M3) (rk : List FE) (pub : Pub) (sig : ByteArray) (s : RS)
    (hn : 1 ≤ p.ksLog) :
    ksLinkPh p m rk pub sig s =
      (m.ksLink (ksLinkView p m (feAt sig) (pos s) rk pub), ⟨ksP2 p (pos s), 96, s.ok⟩) := by
  unfold ksLinkPh
  rw [bind_run, samples_run sig _ s (by simp [laneBits])]
  dsimp only
  rw [bind_run, sumcheck_run sig 3 (by omega)]
  dsimp only
  rw [bind_run, readEs_run]
  dsimp only
  rw [scState_replicate_lk _ _ hn]
  simp only [Nat.add_zero, Nat.zero_add]
  unfold pos
  generalize s.ent + s.msg = P
  rw [pure_run]
  rfl

/-! ## The loads of `phases47` -/

/-- **A `loadEs` cell is the stream's scalar** at lane `a + st·i`. -/
theorem loadEs_val {c : Ctx} {M : Mem} {p : Ptr} {D a st : Nat} {sig : ByteArray} {T : Nat}
    (h : SegsHold c M p (loadEs D a st p).2) (hS : Streamed M sig T) {i : Nat} (hi : i < 2 ^ D)
    (hT : a + st * i + 2 < T) :
    ((loadEs D a st p).1.cell 0 i).val M = feAt sig (8 * (a + st * i)) := by
  have hA : QB.AllE [QB.ldRow a st] := by simp [QB.AllE, QB.ldRow]
  have hrel := loop_rel h (jf := i) (t := 0) (by simpa using hi) (by simp)
  have e := QB.ldRow_val (d := D) (p := p) hA hi (by simp) (by rfl) hrel
  rw [show loadEs D a st = loop [D] [QB.ldRow a st] from rfl, QB.cell1 hA (by simp)]
  rw [e]
  apply QB.kE_lanes
  intro j hj
  rw [hS _ (by omega)]; rfl

/-! ## A Keccak block of `phases47`: the loads and the GKR -/

/-- **The point/lane loads and the GKR of a Keccak block** (`CH`: `ls = logN`; `KS`: `ls = ksLog`): with
the reader at `P` (`8·a0 = P + 40`, the lanes at `a1`, the GKR at `a2`), the cells are `F`'s point,
lanes and `KeccakOut`, and with the gate on the GKR's checks hold. -/
theorem kblock_sound {c : Ctx} {M : Mem} {sig : ByteArray} {T ls a0 a1 a2 : Nat} {g : Cell}
    {p0 p1 p2 : Ptr} (hls : 4 ≤ ls) (hlay : layOk (ls - 4) = true) (hq : 5 ≤ a2)
    (hS : Streamed M sig T) (hT : gkrEnd (ls - 4) a2 ≤ T) (hTr : a0 + 9 * ls + 2 < T)
    (hTv : a1 + 3 * 25 + 2 < T) (hD : ls ≤ 2 ^ clog2 ls)
    (hr : SegsHold c M p0 (loadEs (clog2 ls) a0 9 p0).2)
    (hv : SegsHold c M p1 (loadEs 5 a1 3 p1).2)
    (hk : SegsHold c M p2 (Lvm.Q1.gkrGadget (ls - 4) a2 (fun i => (loadEs (clog2 ls) a0 9 p0).1.cell 0 i)
      (fun l => (loadEs 5 a1 3 p1).1.cell 0 l) g p2).2)
    (hkA : SegsAssert M p2 (Lvm.Q1.gkrGadget (ls - 4) a2 (fun i => (loadEs (clog2 ls) a0 9 p0).1.cell 0 i)
      (fun l => (loadEs 5 a1 3 p1).1.cell 0 l) g p2).2) (hg : g.val M = 1)
    (P : Nat) (h0 : P + 40 = 8 * a0) (h1 : kV ls P + 40 = 8 * a1) (h2 : kG ls P = 8 * a2 - 40) (ok : Bool) :
    samplesAt (feAt sig) P ls = (List.range ls).map (fun i => ((loadEs (clog2 ls) a0 9 p0).1.cell 0 i).val M) ∧
    scalarsAt (feAt sig) (kV ls P + 40) lanes = (List.range 25).map (fun l => ((loadEs 5 a1 3 p1).1.cell 0 l).val M) ∧
    (vkSpec (feAt sig) ls (samplesAt (feAt sig) P ls) (scalarsAt (feAt sig) (kV ls P + 40) lanes) (kG ls P) ok).1 =
      (Lvm.Q1.gkrGadget (ls - 4) a2 (fun i => (loadEs (clog2 ls) a0 9 p0).1.cell 0 i)
        (fun l => (loadEs 5 a1 3 p1).1.cell 0 l) g p2).1.vals M ∧
    (vkSpec (feAt sig) ls (samplesAt (feAt sig) P ls) (scalarsAt (feAt sig) (kV ls P + 40) lanes) (kG ls P) ok).2.2 +
      24 * kBits = 8 * gkrEnd (ls - 4) a2 - 40 ∧
    (ok = true → (vkSpec (feAt sig) ls (samplesAt (feAt sig) P ls) (scalarsAt (feAt sig) (kV ls P + 40) lanes)
      (kG ls P) ok).2.1 = true) := by
  have eR : samplesAt (feAt sig) P ls = (List.range ls).map (fun i => ((loadEs (clog2 ls) a0 9 p0).1.cell 0 i).val M) := by
    unfold samplesAt
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [loadEs_val hr hS (by omega) (by omega)]
    congr 1; omega
  have eV : scalarsAt (feAt sig) (kV ls P + 40) lanes = (List.range 25).map (fun l => ((loadEs 5 a1 3 p1).1.cell 0 l).val M) := by
    unfold scalarsAt lanes
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [loadEs_val hv hS (by norm_num; omega) (by omega)]
    congr 1; omega
  have hls' : ls - 4 + 4 = ls := by omega
  obtain ⟨g1, g2, g3⟩ := gkr_spec (c := c) (M := M) (p := p2) hlay hq hS hT hk ⟨kG ls P, 0, ok⟩ (by simp [h2])
  rw [verifyKeccak_run sig _ _ _ _ (kG ls P) (by simp)] at g1 g2 g3
  simp only [hls'] at g1 g2 g3
  refine ⟨eR, eV, ?_, ?_, fun hok => ?_⟩
  · rw [eR, eV]; simpa [lanes] using g1
  · rw [eR, eV]; simpa [lanes] using g2
  · rw [eR, eV]; simpa [lanes, hok] using (g3 hg).mpr ⟨hok, hkA⟩

end Lvm.Har
