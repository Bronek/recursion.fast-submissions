-- New for lvm (WP-8): the CH link as a doom specification (BLUEPRINT §4.1, §7.2 `linkSpec`). The
-- sumcheck with a riding zero test (`sumcheckZSpec`) is leanVM's `sumcheckSpec` (`LvmKeccakRounds`)
-- with the zero test of `zeroOn_escape` carried along the rounds.
import LvmChainTableLinkMath

/-!
# The `CH` link

`chLinkProg` is V_S's phase 5 (`LvmDecide`, with `M3.v0`'s `chShiftTarget0`, `chSc2Target0`,
`chLink0`) on leanVM's DSL, read for read and sample for sample:

```
chal ← h + 9 challenges (ρ, λ, ζ);  shift ← h plain rounds of degree 2 on chShiftTarget;
inS ← 64 scalars;  ringIn ← ringSwitch (ρ', λ, 0, 0, 0) inS;
sc2 ← 2 plain rounds on chSc2Target;  yS ← 64 scalars;  ringY ← ringSwitch (ρ', μ, sel(ys/4)) yS;
5 challenges (unused);  require sc2.2 = Eq'(ρ, ρ')·Σ_q W̃(μ, q)·yS_q
```

**`chLinkSpec`**: from doom of `LinkBits ∧ ConstLanes ∧ R` (the link `in_{x+1} = Pad43(Y_x)` on every
row but the last, A9) to doom of the two ring claims (`RingColTrue`), the 17 constant-lane claims
at `ρ'` (`ConstClaims`) and `R`. Groups: `ρλζ`, `(h + 9)·L₀/|E|` (lead); each shift round
`L₀·2/|E|`, the constant lanes' zero test riding on the same challenges; each ring switch
`6·L₀/|E|`; each `Y`-lane round `L₀·2/|E|`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete Finset
open scoped ENNReal

/-! ## The program -/

/-- What the `CH` link returns. -/
structure ChLinkOut where
  /-- `ρ ‖ λ ‖ ζ`. -/
  chal : List E
  /-- The shift sumcheck's point `ρ'` and final claim. -/
  shift : List E × E
  /-- The 64 `in` slices at `(ρ', λ, 0, 0, 0)`. -/
  inS : List E
  /-- Their ring switch. -/
  ringIn : E × (List E → E)
  /-- The `Y`-lane sumcheck's point `μ` and final claim. -/
  sc2 : List E × E
  /-- The 64 `Y` slices at `(ρ', μ, sel(ys / 4))`. -/
  yS : List E
  /-- Their ring switch. -/
  ringY : E × (List E → E)

/-- **The `CH` link** (V_S phase 5, `M3.v0`). -/
def chLinkProg (h ys : ℕ) : VerifierProgram ChLinkOut :=
  VerifierProgram.sampleChallenges (h + 9) >>= fun chal ↦
  sumcheck (chShiftTargetE h chal) 3 (List.replicate h none) >>= fun shift ↦
  VerifierProgram.readScalars 64 >>= fun inS ↦
  ringSwitch (chInPt h chal shift) inS >>= fun ringIn ↦
  sumcheck (chSc2TargetE h chal shift inS) 3 (List.replicate 2 none) >>= fun sc2 ↦
  VerifierProgram.readScalars 64 >>= fun yS ↦
  ringSwitch (chYPt ys shift sc2) yS >>= fun ringY ↦
  VerifierProgram.sampleChallenges 5 >>= fun _ ↦
  VerifierProgram.require (sc2.2 = eqMaskedE (chRho h chal) shift.1 *
    ∑ q ∈ range 64, wtE (chLam h chal) (chZeta h chal) sc2.1 q * yS.getD q 0) >>= fun _ ↦
  VerifierProgram.ret ⟨chal, shift, inS, ringIn, sc2, yS, ringY⟩

/-- Characteristic two moves a summand across. -/
theorem char2_move {a b c : E} (h : a + b = c) : a = b + c := by
  linear_combination h - b * CharTwo.two_eq_zero (R := E)

/-! ## A sumcheck with a riding zero test -/

variable {β : Type} {C : List Ev → Set β}

/-- The escape of a round's challenge when a zero test rides on it. -/
theorem zplain_escape {F : β → List E → E} {d N : ℕ} (hF : PlainFamily F d N) (hd : 1 ≤ d)
    (κ : β → ℕ → E) (nZ : ℕ) (R : β → Prop) {acc msg : List E} (hacc : acc.length < N)
    (haccZ : acc.length < nZ) (hdm : msg.length - 1 ≤ d) (q : β)
    (hq : ¬ ((∀ x, polyEval msg x = F q (acc ++ [x])) ∧ ZeroOn (κ q) acc nZ ∧ R q)) :
    avgE (fun c ↦ indE (polyEval msg c = F q (acc ++ [c]) ∧ ZeroOn (κ q) (acc ++ [c]) nZ ∧ R q)) ≤
      errE d := by
  by_cases hR : R q
  swap
  · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2.2).trans
      ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  by_cases hZ : ZeroOn (κ q) acc nZ
  · have hm : ¬ ((∀ x, polyEval msg x = F q (acc ++ [x])) ∧ True) := fun h ↦ hq ⟨h.1, hZ, hR⟩
    exact (avgE_mono fun c ↦ indE_mono fun hc ↦ ⟨hc.1, trivial⟩).trans
      (plain_escape hF (fun _ ↦ True) hacc hdm q hm)
  · exact (avgE_mono fun c ↦ indE_mono fun hc ↦ hc.2.1).trans
      ((zeroOn_escape (κ q) haccZ hZ).trans (errE_mono hd))

variable [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- **Plain sumcheck rounds with a riding zero test** (leanVM's `sumcheckSpec` with
`ZeroOn (κ q) acc nZ` carried): from doom of `claim = F q acc ∧ ZeroOn κ acc ∧ R` to doom of
`final = F q (acc ++ point) ∧ ZeroOn κ (acc ++ point) ∧ R`; each challenge at `L₀·d/|E|`. -/
noncomputable def sumcheckZSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (R : β → Prop) (κ : β → ℕ → E) (nZ : ℕ) {F : β → List E → E} {d N : ℕ}
    (hF : PlainFamily F d N) (hd1 : 1 ≤ d) {count : ℕ} (hc : 2 ≤ count) (hcd : count - 1 ≤ d)
    (hT : T ≤ εmax) (he : (L₀ : ℝ≥0∞) * errE d + T ≤ εmax) :
    (n : ℕ) → (acc : List E) → (claim : E) → acc.length + n ≤ N → acc.length + n ≤ nZ →
      Spec (sumcheck claim count (List.replicate n none))
        (Doomed C (fun q ↦ claim = F q acc ∧ ZeroOn (κ q) acc nZ ∧ R q))
        (fun res h ↦ res.1.length = n ∧
          Doomed C (fun q ↦ res.2 = F q (acc ++ res.1) ∧ ZeroOn (κ q) (acc ++ res.1) nZ ∧ R q) h)
        εmax T T
  | 0, acc, claim, _, _ =>
    (Spec.ret (Post := fun (res : List E × E) h ↦ res.1.length = 0 ∧
        Doomed C (fun q ↦ res.2 = F q (acc ++ res.1) ∧ ZeroOn (κ q) (acc ++ res.1) nZ ∧ R q) h)
        ([], claim)).mono
      (fun _ h ↦ ⟨rfl, by simpa using h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | n + 1, acc, claim, hN, hZ => by
    refine ((roundSpec (T := (L₀ : ℝ≥0∞) * errE d + T) hst _ he count hc claim none).mono
      (fun _ h ↦ h) (fun msg h (hm : msg.length = count ∧ _ ∧ _) ↦ hm) le_rfl zero_le
      le_rfl).bind' fun msg ↦ ?_
    by_cases hm : msg.length = count
    · refine ((doomSample (εmax := εmax) (T := T) hst hcard
        (fun q ↦ (∀ x, polyEval msg x = F q (acc ++ [x])) ∧ ZeroOn (κ q) acc nZ ∧ R q)
        (fun c q ↦ polyEval msg c = F q (acc ++ [c]) ∧ ZeroOn (κ q) (acc ++ [c]) nZ ∧ R q) (errE d)
        (fun q hq ↦ zplain_escape hF hd1 κ nZ R (by omega) (by omega) (by omega) q hq)).mono
          (fun h (hh : msg.length = count ∧
              RoundSplit none claim (polyEval msg 0) (polyEval msg 1) ∧
              Doomed C (fun q ↦ claim = F q acc ∧ ZeroOn (κ q) acc nZ ∧ R q) h) ↦
            Doomed.mono hh.2.2 fun q ⟨hall, hZq, hR⟩ ↦ ⟨by
              have hs := hh.2.1
              rw [RoundSplit, hall, hall] at hs
              rw [← hs]
              exact (hF q acc (by omega)).2.symm, hZq, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun c ↦ ?_
      · refine (sumcheckZSpec hst hcard R κ nZ hF hd1 hc hcd hT he n (acc ++ [c]) (polyEval msg c)
          (by simp; omega) (by simp; omega)).bind' fun res ↦ ?_
        exact (Spec.ret (c :: res.1, res.2)).mono
          (fun _ h ↦ ⟨by simp [h.1], by simpa using h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    · exact Spec.dead.mono (fun _ h ↦ hm h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- Challenges nobody uses keep doom; the lead is the follower's. -/
noncomputable def samplesKeep (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (A : β → Prop)
    (n : ℕ) : Spec (VerifierProgram.sampleChallenges n) (Doomed C A) (fun _ h ↦ Doomed C A h)
      εmax T T :=
  (doomSampleN hst hcard (fun _ q ↦ A q) (fun _ ↦ 0)
      (fun _ q hq ↦ avgE_le_of_le fun _ ↦ (indE_of_not hq).le) n []).mono (fun _ h ↦ h)
    (fun _ _ h ↦ h.2) le_rfl (by simp) le_rfl

/-! ## The specification -/

/-- The postcondition of the `CH` link. -/
def ChLinkPost (h : ℕ) (col : β → ℕ → K) (R : β → Prop) (out : ChLinkOut) (hist : List Ev) :
    Prop :=
  out.shift.1.length = h ∧ Doomed C (fun q ↦ RingColTrue h (col q) out.ringIn ∧
    RingColTrue h (col q) out.ringY ∧ ConstClaims h (col q) out.shift.1 ∧ R q) hist

/-- **The `CH` link**, round by round: from doom of the link (`LinkBits`, `ConstLanes`) and `R` to
doom of the two ring-switched slice claims, the 17 constant-lane claims at `ρ'`, and `R`. -/
noncomputable def chLinkSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (h ys : ℕ)
    (hys : ys % 4 = 0) (hys' : ys / 4 < 16) (col : β → ℕ → K) (R : β → Prop)
    (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hr0 : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + 0 ≤ εmax)
    (hrT : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T ≤ εmax) :
    Spec (chLinkProg h ys)
      (Doomed C (fun q ↦ LinkBits h ys (col q) ∧ ConstLanes h (col q) ∧ R q))
      (ChLinkPost (C := C) h col R) εmax (((h + 9 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  ((zeroSpec (T := 0) hst hcard (fun q ↦ linkDelta h ys (col q))
      (fun q ↦ ZeroOn (constDelta h (col q)) [] (h + 5) ∧ R q) (n := h + 9) (m := h + 9)
      le_rfl).mono
    (fun hist (hd : Doomed C (fun q ↦ LinkBits h ys (col q) ∧ ConstLanes h (col q) ∧ R q) hist) ↦
      Doomed.mono hd fun q ⟨hz, hk, hR⟩ ↦
        ⟨linkBits_of_zero h ys (col q) hz, const_of_zero h (col q) hk, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun chal ↦
  if hc : chal.length = h + 9 then
    ((sumcheckZSpec (T := 0) hst hcard R (fun q ↦ constDelta h (col q)) (h + 5)
        (Fsh_plain h ys (chLam h chal) (chZeta h chal) col (chRho h chal)) (by norm_num)
        (count := 3) (by norm_num) (by norm_num) zero_le h2 h [] (chShiftTargetE h chal)
        (by simp) (by simp)).mono
      (fun _ (hd : chal.length = h + 9 ∧ Doomed C (fun q ↦ ZeroOn (linkDelta h ys (col q)) chal
          (h + 9) ∧ (ZeroOn (constDelta h (col q)) [] (h + 5) ∧ R q)) _) ↦
        Doomed.mono hd.2 fun q ⟨hcl, hk, hR⟩ ↦ ⟨zero_of_shiftClaim h ys (col q) hc hcl, hk, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun shift ↦
    if hs : shift.1.length = h then
      ((doomReadN (T := (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + 0) hst
          (fun q ↦ shift.2 = Fsh h ys (col q) (chLam h chal) (chZeta h chal) (chRho h chal)
            ([] ++ shift.1) ∧ ZeroOn (constDelta h (col q)) ([] ++ shift.1) (h + 5) ∧ R q)
          hr0 63).mono (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun inS ↦
      if hi : inS.length = 64 then
        ((ringColSpec (T := 0) hst hcard h col
            (fun q ↦ chSc2TargetE h chal shift inS =
                G2 h ys (col q) (chLam h chal) (chZeta h chal) (chRho h chal) shift.1 [] ∧
              ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧ R q)
            (chInPt h chal shift) inS ⟨by simp [chInPt, chLam, hs, hc], hi⟩).mono
          (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hsl, h2c, hk, hR⟩ ↦ ⟨by
              have hr : (chRho h chal).length = h := by simp [chRho, hc]
              have hl : (chLam h chal).length = 3 := by simp [chLam, hc]
              rw [List.nil_append, Fsh_end h ys (col q) _ _ hr hs hl]
              rw [chSc2TargetE, G2_nil] at h2c
              have hin : ∑ p ∈ range 64, eqAt (chZeta h chal) p * inS.getD p 0 =
                  ∑ p ∈ range 64, eqAt (chZeta h chal) p *
                    sliceExt h (col q) (shift.1 ++ chLam h chal ++ [0, 0, 0]) p :=
                Finset.sum_congr rfl fun p hp ↦ by rw [hsl.2.2 p (Finset.mem_range.1 hp)]; rfl
              rw [hin] at h2c
              exact char2_move h2c, by simpa using hk, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ringIn ↦
        ((sumcheckSpec (T := 0) hst hcard
            (fun q ↦ RingColTrue h (col q) ringIn ∧ ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧
              R q)
            (G2_plain h ys (chLam h chal) (chZeta h chal) col (chRho h chal) shift.1)
            (count := 3) (by norm_num) (by norm_num) zero_le h2 2 [] (chSc2TargetE h chal shift inS)
            (by simp)).mono
          (fun _ hd ↦ Doomed.mono hd fun q ⟨hc2, hRc, hk, hR⟩ ↦ ⟨hRc, hc2, hk, hR⟩)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun sc2 ↦
        if hm : sc2.1.length = 2 then
          ((doomReadN (T := (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T) hst
              (fun q ↦ sc2.2 = G2 h ys (col q) (chLam h chal) (chZeta h chal) (chRho h chal)
                shift.1 ([] ++ sc2.1) ∧ (RingColTrue h (col q) ringIn ∧
                  ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧ R q)) hrT 63).mono
            (fun _ hd ↦ hd.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun yS ↦
          if hy : yS.length = 64 then
            ((ringColSpec (T := T) hst hcard h col
                (fun q ↦ (sc2.2 = eqMaskedE (chRho h chal) shift.1 *
                    ∑ q ∈ range 64, wtE (chLam h chal) (chZeta h chal) sc2.1 q * yS.getD q 0) ∧
                  (RingColTrue h (col q) ringIn ∧
                    ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧ R q))
                (chYPt ys shift sc2) yS
                ⟨by simp [chYPt, hs, hm, selectorPoint], hy⟩).mono
              (fun _ hd ↦ Doomed.mono hd.2 fun q ⟨hsl, hcheck, hrest⟩ ↦ ⟨by
                  rw [List.nil_append, G2_end h ys (col q) _ _ _ _ hm, hcheck]
                  refine congrArg _ (Finset.sum_congr rfl fun qq hqq ↦ ?_)
                  rw [hsl.2.2 qq (Finset.mem_range.1 hqq)]
                  exact congrArg _ (sliceExt_y h ys (col q) hs hm hys hys' qq), hrest⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun ringY ↦
            (samplesKeep (T := T) hst hcard
              (fun q ↦ RingColTrue h (col q) ringY ∧
                ((sc2.2 = eqMaskedE (chRho h chal) shift.1 *
                    ∑ q ∈ range 64, wtE (chLam h chal) (chZeta h chal) sc2.1 q * yS.getD q 0) ∧
                  (RingColTrue h (col q) ringIn ∧
                    ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧ R q))) 5).bind' fun _ ↦
            (Spec.require (Post := fun _ hist ↦ Doomed C (fun q ↦ RingColTrue h (col q) ringY ∧
                RingColTrue h (col q) ringIn ∧ ZeroOn (constDelta h (col q)) shift.1 (h + 5) ∧
                  R q) hist)
              (fun _ hd hcond ↦ Doomed.mono hd fun q ⟨hy', hin, hk, hR⟩ ↦
                ⟨hy', hcond, hin, hk, hR⟩)).bind' fun _ ↦
            (Spec.ret (⟨chal, shift, inS, ringIn, sc2, yS, ringY⟩ : ChLinkOut)).mono
              (fun _ hd ↦ ⟨hs, Doomed.mono hd fun q ⟨hin, hy', hcc, hR⟩ ↦
                ⟨hy', hin, constZero_of_claims h (col q) hs hcc, hR⟩⟩)
              (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
          else Spec.dead.mono (fun _ hd ↦ hy hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hm hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ hi hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ hd ↦ hs hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hc hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.KG
