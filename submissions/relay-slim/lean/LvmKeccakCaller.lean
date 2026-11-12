-- New for lvm (WP-8): the Keccak GKR with caller claims (BLUEPRINT §4.1–4.2, §11 A6), on WP-2's port
-- of leanVM's `gkrSpec` (`LvmKeccakGkr`).
import LvmKeccakCallerRing

/-!
# The Keccak phase with the caller's output claims

V_S's phases 4 (`CH`) and 6 (`KS`) run, on a 64-slot block `qk` of `2^h` steps:

```
r ← h challenges;  v ← 25 scalars (all output lanes, bound before any lane challenge, A6);
res ← verifyKeccak h r v;  ring ← ringSwitch res.slicePoint res.slices
```

leanVM's `OutputClaim` is one value per lane at one instance point (`keccak_gkr/src/lib.rs:124-133`);
leanVM's `gkrSpec` starts from doom of "the lane claims against the committed middle state hold
at `inst`, and the middle state agrees with twelve rounds of the input at `inst`" (`midAgree`),
and leaves the region's validity at every step to the phase that draws `inst`. Here that phase
is the `r` samples themselves: they are a **zero test** of 64 tables over the steps (`callDelta`):
the 25 middle-state mismatches `midDelta`, and for each tied lane `l < nt` the mismatch between the
caller's column `Y l` and lane `l` of the permutation's output. So:

* Pre: doom of `RegionValid ∧ OutRel ∧ R` (the middle state is twelve rounds of the input at every
  step, and `Y l x = keccakF(in_x)[l]` for every tied lane and step);
* Post: doom of `RingColTrue (the switched slices) ∧ colTrue (the committed-output word) ∧
  TiedTrue (Ỹ_l(r) = v_l for the tied lanes) ∧ R`.

Groups: the `h` samples at `L₀/|E|` each (lead), the GKR's (largest `L₀·46/|E|`), ring
switching's six at `L₀/|E|`. Instances: `CH` ties lanes `0 … 3` to slots `52 … 55` (`chY`), `KS`
ties all 25 (`nt = 25`; V_S's `ksOutputClaims0` layout is the caller's choice of `Y`).
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal

/-! ## The program -/

/-- **The Keccak phase with caller claims** (V_S phases 4 and 6). -/
def callerProg (h : ℕ) :
    VerifierProgram (List E × List E × (List ColumnClaim × List E × List E) × (E × (List E → E))) :=
  VerifierProgram.sampleChallenges h >>= fun r ↦
  VerifierProgram.readScalars 25 >>= fun v ↦
  verifyKeccak h r v >>= fun res ↦
  ringSwitch res.2.1 res.2.2 >>= fun ring ↦
  VerifierProgram.ret (r, v, res, ring)

/-! ## The relation and the claims -/

variable (h nt : ℕ) (col : ℕ → K) (Y : ℕ → ℕ → K)

/-- The caller's tied lanes `l < nt` are the permutation's output lanes at every step. -/
def OutRel : Prop := ∀ l < nt, ∀ x < 2 ^ h, Y l x = laneWord (keccakF1600 (inState h col 0 x)) l

/-- The tied lanes' claims at the instance point `r`: `Ỹ_l(r) = v_l`. -/
def TiedTrue (r v : List E) : Prop := ∀ l < nt, stepMle h r (Y l) = v.getD l 0

/-- The zero-test table of the `r` samples: table `t < 25` the middle-state mismatch, table
`25 + l` (`l < nt`) the tied lane's mismatch, index `x + 2^h·t`. -/
def callDelta (w : ℕ) : E :=
  if w / 2 ^ h < 25 then midDelta h col (w / 2 ^ h) (w % 2 ^ h)
  else if w / 2 ^ h < 25 + nt then
    ofK (Y (w / 2 ^ h - 25) (w % 2 ^ h)) +
      ofK (laneWord (roundsFrom 12 12 (inState h col 1 (w % 2 ^ h))) (w / 2 ^ h - 25))
  else 0

theorem laneWord_inState (m x l : ℕ) (hl : l < 25) :
    laneWord (inState h col m x) l = col (x + 2 ^ h * (25 * m + l)) := by
  rw [laneWord, lane_inState h col m x hl]
  rfl

/-- **The table vanishes** on a valid region with true tied lanes. -/
theorem callDelta_zero (hv : RegionValid h col) (ho : OutRel h nt col Y) :
    ZeroOn (callDelta h nt col Y) [] (h + 6) := by
  rw [zeroOn_nil]
  intro w hw
  have hx : w % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos h)
  have hv' := hv _ hx
  unfold callDelta
  split_ifs with h1 h2
  · rw [midDelta, ← hv', laneWord_inState h col 1 _ _ h1, Nat.mul_one]
    exact CharTwo.add_self_eq_zero _
  · rw [ho _ (by omega) _ hx, keccakF_eq, ← hv']
    exact CharTwo.add_self_eq_zero _
  · rfl

theorem lane_ofLane' (w : UInt64) : K.lane (K.ofLane w) = w := rfl

theorem ofK_injective : Function.Injective (ofK : K → E) := (algebraMap K E).injective

/-- **Conversely, a vanishing table** is a valid region with true tied lanes (the start of the
zero test is the relation itself). -/
theorem valid_of_callDelta_zero (hnt : nt ≤ 25) (hz : ZeroOn (callDelta h nt col Y) [] (h + 6)) :
    RegionValid h col ∧ OutRel h nt col Y := by
  rw [zeroOn_nil] at hz
  have hp := Nat.two_pow_pos h
  have at_ : ∀ x < 2 ^ h, ∀ t < 64, callDelta h nt col Y (x + 2 ^ h * t) = 0 := fun x hx t ht ↦
    hz _ (by rw [pow_add]; nlinarith)
  have e1 : ∀ x < 2 ^ h, ∀ t, (x + 2 ^ h * t) / 2 ^ h = t := fun x hx t ↦ by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx, zero_add]
  have e2 : ∀ x < 2 ^ h, ∀ t, (x + 2 ^ h * t) % 2 ^ h = x := fun x hx t ↦ by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have hmid : ∀ x < 2 ^ h, ∀ t < 25,
      laneWord (roundsFrom 0 12 (inState h col 0 x)) t = col (x + 2 ^ h * (25 + t)) := by
    intro x hx t ht
    have := at_ x hx t (by omega)
    simp only [callDelta, e1 x hx, e2 x hx, ht, ite_true, midDelta] at this
    exact ofK_injective (add_eq_zero_iff_E.1 this)
  have hv : RegionValid h col := by
    intro x hx
    refine Vector.ext fun l hl ↦ ?_
    rw [← LeanVM.Protocol.KeccakGkr.lane_eq _ hl, ← LeanVM.Protocol.KeccakGkr.lane_eq _ hl,
      lane_inState h col 1 x hl, Nat.mul_one, ← hmid x hx l hl, laneWord, lane_ofLane']
  refine ⟨hv, fun l hl x hx ↦ ?_⟩
  have := at_ x hx (25 + l) (by omega)
  simp only [callDelta, e1 x hx, e2 x hx, show ¬ 25 + l < 25 by omega, ite_false,
    show 25 + l < 25 + nt by omega, ite_true, Nat.add_sub_cancel_left] at this
  rw [ofK_injective (add_eq_zero_iff_E.1 this), keccakF_eq, hv x hx]

/-- **The table's extension vanishes at `r`** when the GKR's starting claims and the tied lanes'
claims hold there. -/
theorem callDelta_zeroOn {r v : List E} (hr : r.length = h) (hnt : nt ≤ 25)
    (hout : outClaimsTrueMid h col r v) (hmid : midAgree h col r)
    (htied : TiedTrue h nt Y r v) : ZeroOn (callDelta h nt col Y) r (h + 6) := by
  intro t ht
  rw [hr, show h + 6 - h = 6 by omega] at ht
  unfold foldT
  rw [hr]
  have e : ∀ w ∈ range (2 ^ h), callDelta h nt col Y (w + 2 ^ h * t) =
      if t < 25 then midDelta h col t w
      else if t < 25 + nt then
        ofK (Y (t - 25) w) + ofK (laneWord (roundsFrom 12 12 (inState h col 1 w)) (t - 25))
      else 0 := by
    intro w hw
    have hw' := Finset.mem_range.1 hw
    have hp := Nat.two_pow_pos h
    have e1 : (w + 2 ^ h * t) / 2 ^ h = t := by
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hw', zero_add]
    have e2 : (w + 2 ^ h * t) % 2 ^ h = w := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw']
    simp only [callDelta, e1, e2]
  rw [Finset.sum_congr rfl fun w hw ↦ by rw [e w hw]]
  split_ifs with h1 h2
  · have := hmid t h1
    simp only [stepMle] at this
    simp only [midDelta, mul_add, Finset.sum_add_distrib, this]
    exact CharTwo.add_self_eq_zero _
  · have h3 := htied (t - 25) (by omega)
    have h4 := hout (t - 25) (by omega)
    simp only [stepMle] at h3 h4
    simp only [mul_add, Finset.sum_add_distrib, h3, h4]
    exact CharTwo.add_self_eq_zero _
  · simp

/-! ## The specification -/

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ}

/-- The postcondition of the phase. -/
def CallerPost (P nt : ℕ) (qk : β → ℕ → K) (Y : β → ℕ → ℕ → K) (R : β → Prop)
    (out : List E × List E × (List ColumnClaim × List E × List E) × (E × (List E → E)))
    (hist : List Ev) : Prop :=
  out.1.length = P + 4 ∧ out.2.1.length = 25 ∧
    Doomed C (fun q ↦ RingColTrue (P + 4) (qk q) out.2.2.2 ∧
      (∀ c ∈ out.2.2.1.1, colTrue (P + 4) (qk q) c) ∧ TiedTrue (P + 4) nt (Y q) out.1 out.2.1 ∧
      R q) hist

/-- **The Keccak phase with caller claims**, round by round: from doom of "the region is valid,
the tied lanes are the permutation's output, and `R`" to doom of "the switched slice claim, the
committed-output word claim, the tied lanes' claims at `r`, and `R`". Lead `h·L₀/|E|`. -/
noncomputable def callerSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (P nt : ℕ)
    (hnt : nt ≤ 25) (qk : β → ℕ → K) (Y : β → ℕ → ℕ → K) (R : β → Prop) {εmax T : ℝ≥0∞}
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax)
    (hring : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T ≤ εmax) :
    Spec (callerProg (P + 4))
      (Doomed C (fun q ↦ RegionValid (P + 4) (qk q) ∧ OutRel (P + 4) nt (qk q) (Y q) ∧ R q))
      (CallerPost (C := C) P nt qk Y R) εmax (((P + 4 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  have h6 : (L₀ : ℝ≥0∞) * errE 6 ≤ εmax := le_trans (by gcongr; exact errE_mono (by norm_num)) h46
  ((zeroSpec (T := 0) hst hcard (fun q ↦ callDelta (P + 4) nt (qk q) (Y q)) R
      (n := P + 4 + 6) (m := P + 4) (by omega)).mono
    (fun hist (hd : Doomed C (fun q ↦ RegionValid (P + 4) (qk q) ∧
        OutRel (P + 4) nt (qk q) (Y q) ∧ R q) hist) ↦ Doomed.mono hd fun q ⟨hz, hR⟩ ↦
      ⟨(valid_of_callDelta_zero (P + 4) nt (qk q) (Y q) hnt hz).1,
        (valid_of_callDelta_zero (P + 4) nt (qk q) (Y q) hnt hz).2, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r ↦
  if hr : r.length = P + 4 then
    ((doomReadN (T := (L₀ : ℝ≥0∞) * errE 6) hst
        (fun q ↦ ZeroOn (callDelta (P + 4) nt (qk q) (Y q)) r (P + 4 + 6) ∧ R q) h6 24).mono
      (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun v ↦
    if hv : v.length = 25 then
      ((specWithRet (gkrSpec (T := (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T) hst hcard
          (fun q ↦ TiedTrue (P + 4) nt (Y q) r v ∧ R q) qk P hr hv hring h46)
          (retOK_verifyKeccak_point (P + 4) r v (by omega) hr)).mono
        (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hout, hmid, htied, hR⟩ ↦
          ⟨callDelta_zeroOn (P + 4) nt (qk q) (Y q) hr hnt hout hmid htied, hR⟩)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun res ↦
      if hres : res.2.1.length = P + 4 + 6 ∧ res.2.2.length = 64 then
        ((ringColSpec (T := T) hst hcard (P + 4) qk
            (fun q ↦ (∀ c ∈ res.1, colTrue (P + 4) (qk q) c) ∧ TiedTrue (P + 4) nt (Y q) r v ∧ R q)
            res.2.1 res.2.2 hres).mono
          (fun _ (hd : (res.2.1.length = r.length + 6 ∧ res.2.2.length = 64) ∧ _) ↦
            Doomed.mono hd.2 fun q ⟨hsl, hcol, htied, hR⟩ ↦ ⟨hcol, hsl, htied, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ring ↦
        (Spec.ret (r, v, res, ring)).mono (fun _ hd ↦ ⟨hr, hv, hd⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl
      else Spec.dead.mono (fun _ (hd : (res.2.1.length = r.length + 6 ∧ res.2.2.length = 64) ∧ _) ↦
        hres ⟨by rw [hd.1.1, hr], hd.1.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hv hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hr hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## The two instances -/

/-- `CH`'s output lanes `0 … 3` at slots `ys + l` of its block (`ys = 52` in `M3.v0`). -/
def chY (hN ys : ℕ) (col : ℕ → K) (l x : ℕ) : K := col (x + 2 ^ hN * (ys + l))

/-- `KS`'s output lanes in `M3.v0`'s layout: lanes `0 … 13` at slots `50 … 63` of its block, lanes
`14 … 24` in `C_main` at `y2 + (l − 14)·2^hk`. -/
def ksY (hk y2 : ℕ) (main : ℕ → K) (ks : ℕ → K) (l x : ℕ) : K :=
  if l < 14 then ks (x + 2 ^ hk * (50 + l)) else main (y2 + (l - 14) * 2 ^ hk + x)

end Lvm.KG
