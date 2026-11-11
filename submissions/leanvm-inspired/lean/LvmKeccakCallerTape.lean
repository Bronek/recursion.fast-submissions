-- New for lvm2 (WP T-V, stage S2): the tape caller (lvm2 BLUEPRINT2 §1.2 T1–T5, §2.2, §5): V_S's
-- tape and wire phases as one program of the verifier language, and their specification from the
-- chain part of `TapeRel` (T-W's `ChainTapeRel.out`) to the claims on `C_main`.
import LvmWireSpec

/-!
# The tape caller (S2)

V_S's phases 4–5 at stage S2 (`LvmDecideTape.dTape`, `dWire`), over `E`:

```
r ← w challenges;  v ← 25 scalars;  claim ← tapeGkr w r v;  wo ← wireChProg w sb dsel s n claim
```

* T1: `r` is a zero test of the four digest lanes against the permutation's output on the virtual
  inputs (`chainIn`); the 25 scalars are `a_l = Z̃_l(r)` (lanes `l ≥ 4` free, BLUEPRINT2 §1.5).
  The table is `tapeDelta` (`w + 2` variables, the two lane bits not sampled):
  `zeroOn_tapeDelta_iff` (it vanishes iff `TapeOut`), `tapeDelta_zeroOn` (the output claims and
  `TiedD` at `r` make its extension vanish there).
* T2: T-G's `tapeGkr` (`tapeGkrSpec`: doom of the 25 output claims to doom of the input claim).
* T3–T4: T-W's `wireChProg` (`wireChSpec`), glued by `doomed_inClaim_of_tape`.
* The claims left for the openings: the four tied lanes `D̃_l(r) = a_l` (`TiedD`), the ring claim on
  `C_main`; T5's boundary claims `D̃_l(bits(n − 1)) = h_l` are placed by V_S directly.

**`tapeSpec`**: from doom of "`D` is the permutation's output on `chainIn` at every row" (T-W's
`ChainTapeRel.out`) and `R`, to doom of the ring claim, the tied lanes' claims and `R`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open Lvm.KSponge Lvm.WK Finset
open scoped ENNReal

/-- What the tape caller returns: `r`, the 25 scalars, the input claim, the wiring phase's output. -/
abbrev TapeOutE : Type := List E × List E × KeccakClaim × WireChOut

/-- **The tape caller** (V_S phases 4–5 at S2, `w = logN` row variables; `sb`, `dsel` place `D`'s
block in `C_main`, T-W's `dOf`). -/
def tapeProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) : VerifierProgram TapeOutE :=
  VerifierProgram.sampleChallenges w >>= fun r ↦
  VerifierProgram.readScalars 25 >>= fun v ↦
  tapeGkr w r v >>= fun claim ↦
  VerifierProgram.require (1 ≤ n ∧ n ≤ 2 ^ w) >>= fun _ ↦
  wireChProg w sb dsel s n claim >>= fun wo ↦
  VerifierProgram.ret (r, v, claim, wo)

/-- `D`'s lane `l < 4` of row `x` is the permutation's output lane on the virtual input (T-W's
`ChainTapeRel.out`, BLUEPRINT2 §1.1 `TapeRel` (a)). -/
def TapeOut (w : ℕ) (s : RecursionFast.Digest) (n : ℕ) (D : ℕ → ℕ → K) : Prop :=
  ∀ x < 2 ^ w, ∀ l < 4, D x l = laneWord (keccakF1600 (chainIn s n D x)) l

/-- T1's tied claims: `D̃_l(r) = a_l` for the four digest lanes. -/
def TiedD (w : ℕ) (D : ℕ → ℕ → K) (r v : List E) : Prop :=
  ∀ l < 4, stepMle w r (fun x ↦ D x l) = v.getD l 0

/-! ## T1's zero test -/

/-- **T1's zero-test table** on `w + 2` variables: entry `x + 2^w·l` (`x < 2^w`) is, for `l < 4`,
the mismatch of `D`'s lane `l` at row `x` and lane `l` of the permutation's output on the virtual
input `chainIn s n D x`; `0` for `l ≥ 4`. The `w` samples `r` bind the row variables; the two lane
variables stay free (one zero test per lane). -/
def tapeDelta (w : ℕ) (s : RecursionFast.Digest) (n : ℕ) (D : ℕ → ℕ → K) (v : ℕ) : E :=
  if v / 2 ^ w < 4 then
    ofK (D (v % 2 ^ w) (v / 2 ^ w)) +
      ofK (laneWord (keccakF1600 (chainIn s n D (v % 2 ^ w))) (v / 2 ^ w))
  else 0

/-- **The table vanishes exactly when `TapeOut` holds.** -/
theorem zeroOn_tapeDelta_iff (w : ℕ) (s : RecursionFast.Digest) (n : ℕ) (D : ℕ → ℕ → K) :
    ZeroOn (tapeDelta w s n D) [] (w + 2) ↔ TapeOut w s n D := by
  rw [zeroOn_nil]
  have hp := Nat.two_pow_pos w
  constructor
  · intro hz x hx l hl
    have := hz (x + 2 ^ w * l) (by rw [pow_add]; nlinarith)
    have e1 : (x + 2 ^ w * l) / 2 ^ w = l := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx, zero_add]
    have e2 : (x + 2 ^ w * l) % 2 ^ w = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    simp only [tapeDelta, e1, e2, hl, ite_true] at this
    exact Lvm.KG.ofK_injective (add_eq_zero_iff_E.1 this)
  · intro ho v _
    unfold tapeDelta
    split_ifs with hl
    · rw [← ho _ (Nat.mod_lt _ hp) _ hl]
      exact CharTwo.add_self_eq_zero _
    · rfl

/-- **The table's extension vanishes at `r`** when the `25` output claims of the GKR and the tied
lanes' claims hold there (`v_l` is both `Z̃_l(r)` and `D̃_l(r)`). -/
theorem tapeDelta_zeroOn {w : ℕ} (s : RecursionFast.Digest) (n : ℕ) (D : ℕ → ℕ → K)
    {r v : List E} (hr : r.length = w)
    (hout : ∀ l < 25, stepMle w r (fun x ↦ laneWord (keccakF1600 (chainIn s n D x)) l) =
      v.getD l 0)
    (htied : TiedD w D r v) : ZeroOn (tapeDelta w s n D) r (w + 2) := by
  intro t ht
  rw [hr, show w + 2 - w = 2 by omega] at ht
  have ht4 : t < 4 := lt_of_lt_of_eq ht (by norm_num)
  unfold foldT
  rw [hr]
  have hp := Nat.two_pow_pos w
  have e : ∀ x ∈ range (2 ^ w), tapeDelta w s n D (x + 2 ^ w * t) =
      ofK (D x t) + ofK (laneWord (keccakF1600 (chainIn s n D x)) t) := by
    intro x hx
    have hx' := Finset.mem_range.1 hx
    have e1 : (x + 2 ^ w * t) / 2 ^ w = t := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx', zero_add]
    have e2 : (x + 2 ^ w * t) % 2 ^ w = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx']
    simp only [tapeDelta, e1, e2, ht4, ite_true]
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [e x hx]]
  have h3 := htied t ht4
  have h4 := hout t (by omega)
  simp only [stepMle] at h3 h4
  simp only [mul_add, Finset.sum_add_distrib, h3, h4]
  exact CharTwo.add_self_eq_zero _

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ}

/-- The postcondition of the tape caller. -/
def TapePost (w h sb dsel : ℕ) (colM : β → ℕ → K) (R : β → Prop) (out : TapeOutE)
    (hist : List Ev) : Prop :=
  out.1.length = w ∧ out.2.1.length = 25 ∧ out.2.2.2.sc.1.length = w ∧
    out.2.2.2.d.sl.1.length = 2 ∧
    Doomed C (fun q ↦ RingColTrue h (colM q) out.2.2.2.d.ring ∧
      TiedD w (dOf w dsel (colM q)) out.1 out.2.1 ∧ R q) hist

/-- **The tape caller** (V_S phases 4–5 at S2, `w = P + 5` row variables), round by round: from
doom of "`D` is the permutation's output on the virtual chain inputs at every row (`TapeOut`), and
`R`" to doom of "the ring claim on `C_main`, the tied lanes' claims `D̃_l(r) = v_l`, and `R`".
Groups: the `w` zero-test samples at `L₀/|E|` each (the lead), the GKR's (largest `L₀·46/|E|`),
A1's range of `n` checked by a `require` (no transcript change, so no hypothesis on `n`), the
wiring and slot rounds' `L₀·2/|E|`, ring switching's six at `L₀/|E|` with the follower's
lead `T`. -/
noncomputable def tapeSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) {P sb dsel h : ℕ}
    (hw : P + 5 + 2 + sb = h + 6) (hsel : dsel < 2 ^ sb) (s : RecursionFast.Digest) {n : ℕ}
    (colM : β → ℕ → K) (R : β → Prop) {εmax T : ℝ≥0∞}
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax)
    (hrT : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T ≤ εmax) :
    Spec (tapeProg (P + 5) sb dsel s n)
      (Doomed C (fun q ↦ TapeOut (P + 5) s n (dOf (P + 5) dsel (colM q)) ∧ R q))
      (TapePost (C := C) (P + 5) h sb dsel colM R) εmax
      (((P + 5 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  have h5 : (L₀ : ℝ≥0∞) * errE 5 ≤ εmax := le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  have h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax := by
    rw [add_zero]; exact le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  ((zeroSpec (T := 0) hst hcard (fun q ↦ tapeDelta (P + 5) s n (dOf (P + 5) dsel (colM q))) R
      (n := P + 5 + 2) (m := P + 5) (by omega)).mono
    (fun hist (hd : Doomed C (fun q ↦ TapeOut (P + 5) s n (dOf (P + 5) dsel (colM q)) ∧ R q)
        hist) ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦ ⟨(zeroOn_tapeDelta_iff _ s n _).1 hz, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r ↦
  if hr : r.length = P + 5 then
    ((doomReadN (T := (L₀ : ℝ≥0∞) * errE 5) hst
        (fun q ↦ ZeroOn (tapeDelta (P + 5) s n (dOf (P + 5) dsel (colM q))) r (P + 5 + 2) ∧ R q)
        h5 24).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun v ↦
    if hv : v.length = 25 then
      ((tapeGkrSpec (T := 0) hst hcard
          (fun q ↦ TiedD (P + 5) (dOf (P + 5) dsel (colM q)) r v ∧ R q)
          (fun q ↦ chainIn s n (dOf (P + 5) dsel (colM q))) P hr hv h46 h2).mono
        (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hout, htied, hR⟩ ↦
          ⟨tapeDelta_zeroOn s n _ hr hout htied, hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun claim ↦
      if hc : claim.point.length + 4 = P + 5 then
        (Spec.require (T := 0) (c := 1 ≤ n ∧ n ≤ 2 ^ (P + 5))
          (Post := fun _ hist ↦ (1 ≤ n ∧ n ≤ 2 ^ (P + 5)) ∧ (ClaimShape P claim ∧
            Doomed C (fun q ↦ ClaimTrue (tapeStates P (chainIn s n (dOf (P + 5) dsel (colM q))) 24) P
              claim ∧ (TiedD (P + 5) (dOf (P + 5) dsel (colM q)) r v ∧ R q)) hist))
          (fun _ hp hcond ↦ ⟨hcond, hp⟩)).bind' fun _ ↦
        if hb : 1 ≤ n ∧ n ≤ 2 ^ (P + 5) then
          ((wireChSpec (T := T) hst hcard hw hsel s hb.1 hb.2 claim hc colM
              (fun q ↦ TiedD (P + 5) (dOf (P + 5) dsel (colM q)) r v ∧ R q) h2 hrT).mono
            (fun _ hd ↦ doomed_inClaim_of_tape _ claim _ hd.2.2)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun wo ↦
          (Spec.ret (r, v, claim, wo)).mono (fun _ hd ↦ ⟨hr, hv, hd.1, hd.2.1, hd.2.2⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hb hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ (hd : ClaimShape P claim ∧ _) ↦ hc (by
          obtain ⟨-, h1, -⟩ := hd.1; omega)) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hv hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hr hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.KG
