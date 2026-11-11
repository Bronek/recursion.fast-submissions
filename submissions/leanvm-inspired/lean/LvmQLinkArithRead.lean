import LvmQLinkArith
import LvmDecide

/-!
# QA1 links: what `F` reads in the link phases (phases 5 and 7 of `decideProg`)

`chLinkPhase`, `ksLinkPhase` are the two link phases of `decideProg` (`LvmDecide`, lines "5] CH link",
"7] KS link"), verbatim, as `DM` programs. **`chLinkPhase_run`**, **`ksLinkPhase_run`**: on any reader
state `s`, at position `P = s.ent + s.msg`, the phase reads the view `feAt Σ` at fixed offsets from `P`
(`chLinkView`, `ksLinkView`: every sample, sumcheck and scalar of the phase), adds exactly the link's
check to `ok`, and moves the position by a constant (`chLinkLen`, `ksLinkLen`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm DM

theorem samples_succ (n : Nat) :
    samples (n + 1) = (sampleE >>= fun x => samples n >>= fun xs => pure (x :: xs)) := rfl

theorem samples_val (sig : ByteArray) : ∀ (n : Nat) (s : RS),
    (samples n sig s).1 = (List.range n).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i)
  | 0, s => rfl
  | n + 1, s => by
    have e : (samples (n + 1) sig s).1 = feAt sig (s.ent + 40 + s.msg) ::
        (samples n sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩).1 := rfl
    rw [e, samples_val sig n, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Function.comp_def]
    rw [show s.ent + 40 + s.msg = s.ent + s.msg + 40 + 72 * 0 by omega]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [show s.ent + 72 + s.msg + 0 + 40 + 72 * i = s.ent + s.msg + 40 + 72 * (i + 1) by omega]

/-- One step of `samples`, evaluated (the kernel unfolds the left side once; `samples_st` rewrites
with it instead of comparing two `samples` terms by `rfl`). -/
theorem samples_succ_run (sig : ByteArray) (n : Nat) (s : RS) : samples (n + 1) sig s =
    (feAt sig (s.ent + 40 + s.msg) :: (samples n sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩).1,
      (samples n sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩).2) := rfl

theorem samples_st (sig : ByteArray) : ∀ (n : Nat) (s : RS), 1 ≤ n →
    (samples n sig s).2 = ⟨s.ent + s.msg + 72 * n, 0, s.ok⟩
  | 0, _, h => by omega
  | 1, s, _ => by
    show (⟨s.ent + 72 + s.msg, 0, s.ok⟩ : RS) = _
    rw [show s.ent + 72 + s.msg = s.ent + s.msg + 72 * 1 by omega]
  | n + 2, s, _ => by
    have e : (samples (n + 2) sig s).2 = (samples (n + 1) sig ⟨s.ent + 72 + s.msg, 0, s.ok⟩).2 := by
      rw [samples_succ_run]
    rw [e, samples_st sig (n + 1) _ (by omega)]
    simp only []
    rw [show s.ent + 72 + s.msg + 0 + 72 * (n + 1) = s.ent + s.msg + 72 * (n + 2) by omega]

/-- `n` challenges from position `P`: the answers at `P + 40 + 72i`. -/
theorem samples_run (sig : ByteArray) (n : Nat) (s : RS) (hn : 1 ≤ n) :
    samples n sig s = ((List.range n).map fun i => feAt sig (s.ent + s.msg + 40 + 72 * i),
      ⟨s.ent + s.msg + 72 * n, 0, s.ok⟩) := by
  rw [← samples_val, ← samples_st sig n s hn]
  rfl

theorem scState_replicate_lk (c : Nat) (st : RS) {n : Nat} (hn : 1 ≤ n) :
    scState c st (List.replicate n none) = ⟨st.ent + st.msg + n * roundLen c, 0, st.ok⟩ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [scState, List.replicate_succ]

theorem require_run_lk (c : Bool) (sig : ByteArray) (s : RS) :
    require c sig s = ((), { s with ok := c && s.ok }) := rfl

/-! ## Phase 5: the `CH` link -/

/-- **Phase 5 of `decideProg`** (`LvmDecide.lean`, "5] CH link"), verbatim. -/
def chLinkPhase (p : Params) (m : M3) (r v : List FE) (pub : Pub) : DM (Bool × List (Com × BlockClaim)) := do
  let chal ← samples (p.logN + 3 + 6)
  let shift ← sumcheck (m.chShiftTarget chal) 3 (List.replicate p.logN none)
  let inS ← readEs kBits
  let ringIn ← ringRaw inS
  let sc2 ← sumcheck (m.chSc2Target chal shift inS) 3 [none, none]
  let yS ← readEs kBits
  let ringY ← ringRaw yS
  let constLanes ← samples laneBits
  let (okL, linkClaims) := m.chLink ⟨chal, shift, inS, ringIn, sc2, yS, ringY, constLanes, r, v, pub⟩
  require okL
  pure (okL, linkClaims)

/-- The positions of phase 5 from its start `P`: the shift sumcheck, the `in` slices, the second
sumcheck, the `Y` slices, the constant lanes, the end. -/
def chP1 (p : Params) (P : Nat) : Nat := P + 72 * (p.logN + 3 + 6)
def chP2 (p : Params) (P : Nat) : Nat := chP1 p P + p.logN * roundLen 3
def chP3 (p : Params) (P : Nat) : Nat := chP2 p P + 24 * kBits + 72 * ringStages
def chP4 (p : Params) (P : Nat) : Nat := chP3 p P + 2 * roundLen 3
def chP5 (p : Params) (P : Nat) : Nat := chP4 p P + 24 * kBits + 72 * ringStages
def chP6 (p : Params) (P : Nat) : Nat := chP5 p P + 72 * laneBits

/-- A ring switch's value from its six challenges (`ringRaw`). -/
def ringOf (s chs : List FE) : FE × List FE := (polyEval (s.map (phiMap · chs)) gen, ringCoefficients chs)

/-- `n` challenges at `P + 40 + 72i` of the view. -/
def samplesAt (v : Nat → FE) (P n : Nat) : List FE := (List.range n).map fun i => v (P + 40 + 72 * i)

/-- **What phase 5 reads**, from the view `v` and the phase's start `P`. -/
def chLinkView (p : Params) (m : M3) (v : Nat → FE) (P : Nat) (r w : List FE) (pub : Pub) : ChLinkIn :=
  let chal := samplesAt v P (p.logN + 3 + 6)
  let shift := scSpec v 3 (chP1 p P) (m.chShiftTarget chal) (List.replicate p.logN none)
  let inS := scalarsAt v (chP2 p P + 40) kBits
  let ringIn := ringOf inS (samplesAt v (chP2 p P + 24 * kBits) ringStages)
  let sc2 := scSpec v 3 (chP3 p P) (m.chSc2Target chal shift inS) [none, none]
  let yS := scalarsAt v (chP4 p P + 40) kBits
  let ringY := ringOf yS (samplesAt v (chP4 p P + 24 * kBits) ringStages)
  ⟨chal, shift, inS, ringIn, sc2, yS, ringY, samplesAt v (chP5 p P) laneBits, r, w, pub⟩

theorem ringRaw_run (sig : ByteArray) (s : List FE) (st : RS) :
    ringRaw s sig st = (ringOf s (samplesAt (feAt sig) (st.ent + st.msg) ringStages),
      ⟨st.ent + st.msg + 72 * ringStages, 0, st.ok⟩) := by
  rw [show ringRaw s = (samples ringStages >>= fun challenges =>
    pure (polyEval (s.map (phiMap · challenges)) gen, ringCoefficients challenges)) from rfl,
    bind_run, samples_run sig ringStages st (by decide), pure_run]
  rfl

/-- **Phase 5 reads `chLinkView` and adds the link's check.** -/
theorem chLinkPhase_run (p : Params) (m : M3) (r w : List FE) (pub : Pub) (sig : ByteArray) (s : RS)
    (hn : 1 ≤ p.logN) :
    chLinkPhase p m r w pub sig s =
      ((m.chLink (chLinkView p m (feAt sig) (s.ent + s.msg) r w pub)),
        ⟨chP6 p (s.ent + s.msg), 0, (m.chLink (chLinkView p m (feAt sig) (s.ent + s.msg) r w pub)).1 && s.ok⟩) := by
  unfold chLinkPhase
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
  generalize s.ent + s.msg = P
  rw [bind_run, require_run_lk, pure_run]
  rfl

/-! ## Phase 7: the `KS` link -/

/-- **Phase 7 of `decideProg`** (`LvmDecide.lean`, "7] KS link"), verbatim. -/
def ksLinkPhase (p : Params) (m : M3) (rk : List FE) (pub : Pub) : DM (Bool × List (Com × BlockClaim)) := do
  let kchal ← samples (p.ksLog + laneBits)
  let kshift ← sumcheck (m.ksShiftTarget kchal) 3 (List.replicate p.ksLog none)
  let kvals ← readEs 4
  let (okK, kLinkClaims) := m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩
  require okK
  pure (okK, kLinkClaims)

/-- The positions of phase 7: the shift sumcheck, the four scalars. -/
def ksP1 (p : Params) (P : Nat) : Nat := P + 72 * (p.ksLog + laneBits)
def ksP2 (p : Params) (P : Nat) : Nat := ksP1 p P + p.ksLog * roundLen 3

/-- **What phase 7 reads.** -/
def ksLinkView (p : Params) (m : M3) (v : Nat → FE) (P : Nat) (rk : List FE) (pub : Pub) : KsLinkIn :=
  let kchal := samplesAt v P (p.ksLog + laneBits)
  ⟨kchal, scSpec v 3 (ksP1 p P) (m.ksShiftTarget kchal) (List.replicate p.ksLog none),
    scalarsAt v (ksP2 p P + 40) 4, rk, pub⟩

/-- **Phase 7 reads `ksLinkView` and adds the link's check**; the four scalars stay pending (96
message bytes) for the next FS query. -/
theorem ksLinkPhase_run (p : Params) (m : M3) (rk : List FE) (pub : Pub) (sig : ByteArray) (s : RS)
    (hn : 1 ≤ p.ksLog) :
    ksLinkPhase p m rk pub sig s =
      ((m.ksLink (ksLinkView p m (feAt sig) (s.ent + s.msg) rk pub)),
        ⟨ksP2 p (s.ent + s.msg), 96, (m.ksLink (ksLinkView p m (feAt sig) (s.ent + s.msg) rk pub)).1 && s.ok⟩) := by
  unfold ksLinkPhase
  rw [bind_run, samples_run sig _ s (by simp [laneBits])]
  dsimp only
  rw [bind_run, sumcheck_run sig 3 (by omega)]
  dsimp only
  rw [bind_run, readEs_run]
  dsimp only
  rw [scState_replicate_lk _ _ hn]
  simp only [Nat.add_zero, Nat.zero_add]
  generalize s.ent + s.msg = P
  rw [bind_run, require_run_lk, pure_run]
  rfl

end Lvm.Q1
