-- new for lvm (AC-S, BLUEPRINT §12 A23): phase 3b, the accumulator fold, on the wire. Reuses WP-8's
-- zero test `Lvm.KG.zeroSpec` (`LvmKeccakCallerRing`, leanVM's `zt_escape`), WP-2's `readNSuccSpec`,
-- `Spec.sampleE`/`readE`/`require`, the Schwartz-Zippel bound `sz_escape` (`LvmKeccakRounds`) and
-- WP-14's `Spec.orStable` (`LvmCertSFrame`).
import LvmKeccakCallerRing
import LvmFrontBusSpec
import LvmFrontBusGkr
import LvmCertSFrame

/-!
# Phase 3b: folding the incoming accumulator with the proof's own fixed claims

BLUEPRINT §12.4: after the table sumcheck, the verifier samples `κ ∈ E^dk`, reads the `D + 1`
coefficients `h₀ … h_D` of a line polynomial, samples `t`, reads one scalar that must be zero, and
checks `h(0) = acc_in.y`, `h(1) = y_own(κ)` and `AccOk (line(t), h(t))`, where
`line(t) = a + t·(a + b)` (characteristic two) runs from `a = acc_in.pt` to `b = r ++ κ`.

Generic in the evaluator `Φ` (the fixed multilinear polynomial) and in `y_own`, `b`:

* `line`, `hEval` (Horner), `hPoly`; **`lineDeg_mle`**: the restriction of any multilinear
  extension to a line is a polynomial of degree at most the number of variables;
* `accProg`: the phase on the wire;
* `AccHyp`: what the instance must give (`Φ ∘ line` of degree `≤ D`, the endpoints, and
  `y_own(κ) − Φ(b(κ)) = Σ_w eq(κ, w)·δ_w` for the claims' errors `δ`); `AccGood`: the pass check
  holds, `Φ(a) = y_in` (`AccOk acc_in`) and every `δ_w` is zero;
* **`accBadSpec`**: outside `AccGood` the phase never returns in doom; escape `1/|E|` per `κ_j`
  (the `dk` samples are one group, charged `dk/|E|` as the lead), `D/|E|` at `t` (§12.6's table);
* **`accSpecG`**: from `¬AccGood ∨ M` to `M` for any predicate `M` the phase keeps
  (`Spec.orStable`); the instance takes `M` = the committed claims' doom;
* **`accProg_complete`** (non-vacuity): under `AccGood` the honest coefficients pass for every `t`.
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval Polynomial Finset
open scoped ENNReal

/-! ## The line and the line polynomial -/

/-- The line through `a` (at `t = 0`) and `b` (at `t = 1`): `a_i + t·(a_i + b_i)`
(characteristic two, BLUEPRINT §12.4 step 4). -/
def line (a b : List E) (t : E) : List E := List.zipWith (fun x y ↦ x + t * (x + y)) a b

theorem length_line (a b : List E) (t : E) : (line a b t).length = min a.length b.length := by
  simp [line]

theorem line_zero : ∀ (a b : List E), a.length = b.length → line a b 0 = a
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    have ih := line_zero a b (by simpa using h)
    simp only [line, List.zipWith_cons_cons, zero_mul, add_zero] at ih ⊢
    rw [ih]

theorem line_one : ∀ (a b : List E), a.length = b.length → line a b 1 = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    have ih := line_one a b (by simpa using h)
    simp only [line, List.zipWith_cons_cons, one_mul] at ih ⊢
    rw [ih, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- `h(t) = Σ_j h_j t^j` (Horner; `h₀` the constant coefficient). -/
def hEval (hs : List E) (t : E) : E := hs.foldr (fun c acc ↦ c + t * acc) 0

theorem hEval_zero (hs : List E) : hEval hs 0 = hs.headD 0 := by
  cases hs <;> simp [hEval]

theorem hEval_one : ∀ hs : List E, hEval hs 1 = hs.sum
  | [] => rfl
  | c :: hs => by simp [hEval, ← hEval_one hs]

theorem hEval_cons (c : E) (hs : List E) (t : E) : hEval (c :: hs) t = c + t * hEval hs t := rfl

/-- Horner over a run of indices is the power sum. -/
theorem hEval_range' (f : ℕ → E) (t : E) : ∀ (m k : ℕ),
    hEval ((List.range' k m).map f) t * t ^ k = ∑ i ∈ Finset.Ico k (k + m), f i * t ^ i
  | 0, k => by simp [hEval]
  | m + 1, k => by
    rw [List.range'_succ, List.map_cons, hEval_cons,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : k < k + (m + 1)),
      show k + (m + 1) = k + 1 + m by omega, ← hEval_range' f t m (k + 1), pow_succ]
    ring

/-- The polynomial of a coefficient list. -/
noncomputable def hPoly (hs : List E) : E[X] := hs.foldr (fun c acc ↦ C c + X * acc) 0

theorem eval_hPoly (hs : List E) (t : E) : (hPoly hs).eval t = hEval hs t := by
  induction hs with
  | nil => simp [hPoly, hEval]
  | cons c hs ih =>
    simp only [hPoly, List.foldr_cons, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X] at ih ⊢
    rw [ih]; rfl

theorem natDegree_hPoly : ∀ (hs : List E) (n : ℕ), hs.length ≤ n + 1 → (hPoly hs).natDegree ≤ n
  | [], _, _ => by simp [hPoly]
  | c :: hs, n, h => by
    simp only [hPoly, List.foldr_cons]
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    rcases hs with _ | ⟨c', hs'⟩
    · simp
    · have hn : 1 ≤ n := by simp at h; omega
      refine (natDegree_mul_le).trans ?_
      have := natDegree_hPoly (c' :: hs') (n - 1) (by simp at h ⊢; omega)
      have hX : (X : E[X]).natDegree ≤ 1 := natDegree_X_le
      simp only [hPoly] at this
      omega

/-! ## The restriction of a multilinear extension to a line -/

/-- `eq(line(t), w)` as a polynomial in `t`. -/
noncomputable def eqPoly : List E → List E → ℕ → E[X]
  | x :: a, y :: b, w =>
    (if w % 2 = 1 then C x + X * C (x + y) else 1 + (C x + X * C (x + y))) * eqPoly a b (w / 2)
  | _, _, _ => 1

theorem eval_eqPoly : ∀ (a b : List E) (w : ℕ) (t : E), (eqPoly a b w).eval t = eqAt (line a b t) w
  | [], _, _, _ => by simp [eqPoly, line]
  | _ :: _, [], _, _ => by simp [eqPoly, line]
  | x :: a, y :: b, w, t => by
    simp only [eqPoly, line, List.zipWith_cons_cons, eval_mul, eqAt_cons]
    rw [← line, ← eval_eqPoly a b (w / 2) t]
    split_ifs <;> simp

theorem natDegree_eqPoly : ∀ (a b : List E) (w : ℕ), (eqPoly a b w).natDegree ≤ a.length
  | [], _, _ => by simp [eqPoly]
  | _ :: _, [], _ => by simp [eqPoly]
  | x :: a, y :: b, w => by
    simp only [eqPoly, List.length_cons]
    have ha := natDegree_eqPoly a b (w / 2)
    have hl : (C x + X * C (x + y) : E[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) ((natDegree_mul_le).trans (by
        have := natDegree_X_le (R := E); simp only [natDegree_C]; omega)))
    split_ifs
    · exact (natDegree_mul_le).trans (by omega)
    · refine (natDegree_mul_le).trans ?_
      have : (1 + (C x + X * C (x + y)) : E[X]).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le (by simp) hl)
      omega

/-- **The degree bound of the line restriction**: on the line from `a` to `b`, the extension of a
column of `2^D` cells is a polynomial of degree at most `D` in `t`. -/
theorem lineDeg_mle {D : ℕ} (q : Column D) (a b : List E) (ha : a.length = D) (hb : b.length = D) :
    ∃ g : E[X], g.natDegree ≤ D ∧
      ∀ t, g.eval t = eval₂Mle q.values (algebraMap K E) (vecOf D (line a b t)) := by
  refine ⟨∑ x ∈ range (2 ^ D), C (ofK (q.values.getD x 0)) * eqPoly a b x, ?_, fun t ↦ ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun x _ ↦ (natDegree_C_mul_le _ _).trans ?_
    exact ha ▸ natDegree_eqPoly a b x
  · have hl : (line a b t).length = D := by rw [length_line, ha, hb, min_self]
    rw [← sum_eqEval_mul, toList_vecOf _ hl, eval_finset_sum,
      Fin.sum_univ_eq_sum_range (fun x ↦ Verifier.eqEval (line a b t) (EndToEnd.boolPoint D x) *
        ofK (q.values.getD x 0))]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have he := eqEval_boolPoint_eqAt (line a b t) x
    rw [hl] at he
    rw [eval_mul, eval_C, eval_eqPoly, he, mul_comm]

/-! ## The phase -/

/-- **Phase 3b on the wire** (BLUEPRINT §12.3–§12.4): `κ` (`dk` samples), the line polynomial's
`D + 1` coefficients, `t`, the zero scalar; then the checks: `ok` (the fixed columns outside `Φ`,
i.e. `PUB`), `h(0) = y_in`, `h(1) = y_own(κ)`, the zero scalar, and `AccOk accOut`:
`Φ(line(a, b(κ), t)) = h(t)`. -/
def accProg (dk D : ℕ) (ok : Bool) (yIn : E) (a : List E) (yOwn : List E → E)
    (bOf : List E → List E) (Φ : List E → E) : VerifierProgram Unit :=
  (VerifierProgram.sampleChallenges dk).bind fun κ ↦
    (VerifierProgram.readScalars (D + 1)).bind fun hs ↦
      VerifierProgram.sampleChallenge.bind fun t ↦
        VerifierProgram.readScalar.bind fun z ↦
          VerifierProgram.require (ok = true ∧ hEval hs 0 = yIn ∧ hEval hs 1 = yOwn κ ∧ z = 0 ∧
            Φ (line a (bOf κ) t) = hEval hs t)

/-- **What the instance gives**: `Φ` on the line from `a` to `b(κ)` has degree at most `D`; the
line's endpoints are `a` and `b(κ)`; `y_own(κ) − Φ(b(κ))` is the multilinear extension in `κ` of
the claims' errors `δ` (BLUEPRINT §12.6: `Σ_k eq(κ, k)(v_fix[k] − F̃_k(r))`). -/
structure AccHyp (dk D : ℕ) (a : List E) (yOwn : List E → E) (bOf : List E → List E)
    (Φ : List E → E) (δ : ℕ → E) : Prop where
  line_deg : ∀ κ : List E, κ.length = dk →
    ∃ g : E[X], g.natDegree ≤ D ∧ ∀ t, g.eval t = Φ (line a (bOf κ) t)
  at0 : ∀ κ : List E, κ.length = dk → line a (bOf κ) 0 = a
  at1 : ∀ κ : List E, κ.length = dk → line a (bOf κ) 1 = bOf κ
  fold : ∀ κ : List E, κ.length = dk → yOwn κ - Φ (bOf κ) = ∑ w ∈ range (2 ^ dk), eqAt κ w * δ w

/-- **Nothing to fold away**: the pass check holds, the incoming claim is true (`AccOk acc_in`),
and every fixed claim is (`δ = 0`). -/
def AccGood (dk : ℕ) (ok : Bool) (yIn : E) (a : List E) (Φ : List E → E) (δ : ℕ → E) : Prop :=
  ok = true ∧ Φ a = yIn ∧ ∀ w < 2 ^ dk, δ w = 0

/-! ## Outside `AccGood`: the phase never returns in doom -/

section Bad

variable {dk D : ℕ} {ok : Bool} {yIn : E} {a : List E} {yOwn : List E → E}
  {bOf : List E → List E} {Φ : List E → E} {δ : ℕ → E} {εmax T : ℝ≥0∞}

/-- The one candidate of a history-free doom. -/
abbrev unitC : List Ev → Set Unit := fun _ ↦ Set.univ

theorem stable_unitC : Stable unitC := fun _ _ _ ↦ rfl

theorem ncard_unitC (h : List Ev) : (unitC h).ncard ≤ 1 := by simp [unitC]

theorem doomed_unitC {A : Unit → Prop} {h : List Ev} : Doomed unitC A h ↔ ¬ A () := by
  constructor
  · intro hd ha; exact hd () (Set.mem_univ _) ha
  · intro hn q _ hq; exact hn hq

/-- The doom after `t`: the checks cannot all pass at `t`. -/
def DoomT (ok : Bool) (yIn : E) (a : List E) (yOwn : List E → E) (bOf : List E → List E)
    (Φ : List E → E) (κ hs : List E) (t : E) : Prop :=
  ¬ (ok = true ∧ hEval hs 0 = yIn ∧ hEval hs 1 = yOwn κ ∧ hEval hs t = Φ (line a (bOf κ) t))

open Classical in
/-- The escape at `t`: a wrong line polynomial agrees with `Φ ∘ line` at `D` points at most. -/
theorem escape_t (H : AccHyp dk D a yOwn bOf Φ δ) {κ hs : List E} (hκ : κ.length = dk)
    (hhs : hs.length = D + 1) (hd : ¬ (ZeroOn δ κ dk ∧ (ok = true ∧ Φ a = yIn))) :
    (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c ↦
      ¬ DoomT ok yIn a yOwn bOf Φ κ hs c).card : ℝ≥0∞) ≤ errE D := by
  classical
  rw [card_filter_eq_avgE]
  by_cases hp : ok = true ∧ hEval hs 0 = yIn ∧ hEval hs 1 = yOwn κ
  · obtain ⟨g, hg, hgv⟩ := H.line_deg κ hκ
    have hne : hPoly hs ≠ g := by
      intro he
      have e0 := hgv 0
      have e1 := hgv 1
      rw [← he, eval_hPoly, H.at0 κ hκ] at e0
      rw [← he, eval_hPoly, H.at1 κ hκ] at e1
      refine hd ⟨(zeroOn_full δ hκ).mpr ?_, hp.1, by rw [← e0, hp.2.1]⟩
      rw [← H.fold κ hκ, ← e1, hp.2.2, sub_self]
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans
      (sz_escape hne (natDegree_hPoly hs D (by omega)) hg)
    rw [eval_hPoly, hgv]
    exact (not_not.mp hc).2.2.2
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ ?_).trans
      ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
    have hc' := not_not.mp hc
    exact hp ⟨hc'.1, hc'.2.1, hc'.2.2.1⟩

open Classical in
/-- **Outside `AccGood` the phase never returns in doom**: each `κ_j` escapes with `1/|E|` (WP-8's
zero test; the `dk` samples are one group, so the lead is `dk/|E|`), `t` with `D/|E|` (a wrong line
polynomial), the reads keep doom, and the checks reject. -/
noncomputable def accBadSpec (H : AccHyp dk D a yOwn bOf Φ δ) (hD : errE D ≤ εmax)
    (hT : T ≤ εmax) :
    Spec (accProg dk D ok yIn a yOwn bOf Φ) (fun _ ↦ ¬ AccGood dk ok yIn a Φ δ)
      (fun _ _ ↦ False) εmax (dk * errE 1) T :=
  let R : Unit → Prop := fun _ ↦ ok = true ∧ Φ a = yIn
  ((Lvm.KG.zeroSpec (C := unitC) (L₀ := 1) (εmax := εmax) (T := 0) stable_unitC ncard_unitC
      (fun _ ↦ δ) R (n := dk) (m := dk) le_rfl).bind fun κ ↦
    (readNSuccSpec (εmax := εmax) (T := errE D + 0)
        (fun hist ↦ κ.length = dk ∧ Doomed unitC (fun q ↦ ZeroOn δ κ dk ∧ R q) hist)
        (fun _ _ h ↦ h) (by rwa [add_zero]) D).bind fun hs ↦
      (Spec.sampleE (εmax := εmax) (T := 0) (errE D)
          (Pre := fun hist ↦ hs.length = D + 1 ∧
            (κ.length = dk ∧ Doomed unitC (fun q ↦ ZeroOn δ κ dk ∧ R q) hist))
          (Post := fun t _ ↦ DoomT ok yIn a yOwn bOf Φ κ hs t)
          (fun _ ⟨hhs, hκ, hd⟩ ↦ escape_t H hκ hhs (doomed_unitC.mp hd))).bind fun t ↦
        (Spec.readE (εmax := εmax) (T := T) (Post := fun _ _ ↦ DoomT ok yIn a yOwn bOf Φ κ hs t)
            (fun _ _ h ↦ h) hT).bind fun z ↦
          Spec.require (Pre := fun _ ↦ DoomT ok yIn a yOwn bOf Φ κ hs t) (Post := fun _ _ ↦ False)
            fun _ (hd : DoomT ok yIn a yOwn bOf Φ κ hs t)
              (hc : ok = true ∧ hEval hs 0 = yIn ∧ hEval hs 1 = yOwn κ ∧ z = 0 ∧
                Φ (line a (bOf κ) t) = hEval hs t) ↦
            hd ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.2.symm⟩).mono
    (fun _ hg ↦ by
      rw [doomed_unitC]
      rintro ⟨hz, hok, hΦ⟩
      exact hg ⟨hok, hΦ, (zeroOn_nil δ dk).mp hz⟩)
    (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

end Bad

/-! ## The phase: outside `AccGood` rejected, inside it the follower's doom carried -/

section Spec

variable {dk D : ℕ} {ok : Bool} {yIn : E} {a : List E} {yOwn : List E → E}
  {bOf : List E → List E} {Φ : List E → E} {δ : ℕ → E} {εmax T : ℝ≥0∞}

/-- **The phase's specification** (BLUEPRINT §12.6 `accSpec`, generic): from `¬AccGood ∨ M` to
`M`, for a predicate `M` of the history the phase keeps (the committed claims' doom). Escape
`1/|E|` per `κ_j`, `D/|E|` at `t`; lead the larger of `dk/|E|` and the follower's. -/
noncomputable def accSpecG (H : AccHyp dk D a yOwn bOf Φ δ) (M : List Ev → Prop)
    (hM : ∀ h₀ l, (accProg dk D ok yIn a yOwn bOf Φ).Reach h₀ l → M h₀ → M (h₀ ++ l))
    (hD : errE D ≤ εmax) (hT : T ≤ εmax) :
    Spec (accProg dk D ok yIn a yOwn bOf Φ) (fun h ↦ ¬ AccGood dk ok yIn a Φ δ ∨ M h)
      (fun _ h ↦ M h) εmax (max (dk * errE 1) T) T :=
  (accBadSpec H hD hT).orStable hM hT

/-- **Completeness (non-vacuity)**: under `AccGood`, the honest coefficients (those of `Φ ∘ line`)
pass every check of the phase, for every `κ` and `t`, with the zero scalar `0`. -/
theorem accProg_complete (H : AccHyp dk D a yOwn bOf Φ δ) (hg : AccGood dk ok yIn a Φ δ)
    (κ : List E) (hκ : κ.length = dk) :
    ∃ hs : List E, hs.length = D + 1 ∧ ∀ t : E,
      ok = true ∧ hEval hs 0 = yIn ∧ hEval hs 1 = yOwn κ ∧ (0 : E) = 0 ∧
        Φ (line a (bOf κ) t) = hEval hs t := by
  obtain ⟨g, hgd, hgv⟩ := H.line_deg κ hκ
  have hev : ∀ t, hEval ((List.range (D + 1)).map g.coeff) t = g.eval t := fun t ↦ by
    have key := hEval_range' g.coeff t (D + 1) 0
    rw [pow_zero, mul_one, zero_add, ← List.range_eq_range', ← Finset.range_eq_Ico] at key
    rw [key, eval_eq_sum_range' (n := D + 1) (by omega)]
  refine ⟨(List.range (D + 1)).map g.coeff, by simp, fun t ↦ ⟨hg.1, ?_, ?_, rfl, ?_⟩⟩
  · rw [hev, hgv, H.at0 κ hκ, hg.2.1]
  · rw [hev, hgv, H.at1 κ hκ, ← sub_eq_zero, ← neg_sub, H.fold κ hκ, neg_eq_zero]
    exact Finset.sum_eq_zero fun w hw ↦ by rw [hg.2.2 w (Finset.mem_range.mp hw), mul_zero]
  · rw [hev, hgv]

end Spec

end Lvm.Acc
