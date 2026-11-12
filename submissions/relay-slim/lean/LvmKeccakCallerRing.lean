-- New for lvm (WP-8): ring switching on a block column with a carried predicate, and a zero test over
-- challenges. Adapted from leanVM `EndToEnd/Front/RingSwitch.lean` as ported by WP-2 (`LvmRingSwitch`:
-- `RingAlive`, `ring_escape`, `ring_start`, `ring_end`, `ringSpecOf`), with the leanISA stack and
-- `ColumnClaimsHold` replaced by a column accessor and an arbitrary carried predicate `R`.
import LvmRingFidelity
import LvmKeccakRounds
import LvmKeccakBridge

/-!
# Generic tools for the `CH`/`KS` phases

* `specWithRet`: a specification's postcondition strengthened by a fact every return satisfies
  (`RetOK`), e.g. the lengths `verifyKeccak` returns.
* `RingColTrue h col (target, W)`: the ring-switched claim on a `2^(h+6)`-word block column,
  `target = Σ_n W(n)·col(n)` (the claim V_S places as `⟨blk, ring.2, ring.1⟩`); **`ringCol_iff`**: it
  holds iff `Σ_i x^i Φ(s_i − ẑ_i(pt)) = 0` (leanVM's `ringClaim_holds_iff` on a block).
* **`ringColSpec`**: `ringSwitch pt sv` from doom of `slicesTrue ∧ R` to doom of `RingColTrue ∧ R`,
  six challenges at `L₀/|E|` each (leanVM's `ringSpecOf` with `R` for the column claims).
* `ZeroAlive`, **`zero_escape`**: a multilinear zero test with a carried predicate, `1/|E|` per
  coordinate (leanVM's `zt_escape`, any number of coordinates).
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Sound
open LeanVM.Protocol.Ring Finset
open scoped ENNReal

/-! ## Returns -/

/-- A specification whose postcondition also states a fact of every return. -/
def specWithRet {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {εmax L T : ℝ≥0∞} (S : Spec p Pre Post εmax L T) {Q : α → Prop}
    (hQ : RetOK Q p) : Spec p Pre (fun a h ↦ Q a ∧ Post a h) εmax L T :=
  { S with post := fun hl ha hD ↦ ⟨hQ _ _ ha, S.post hl ha hD⟩ }

/-! ## The ring claim on a block column -/

/-- **The ring-switched claim on a block column** of `2^(h+6)` words. -/
def RingColTrue (h : ℕ) (col : ℕ → K) (ring : E × (List E → E)) : Prop :=
  ring.1 = ∑ n ∈ range (2 ^ (h + 6)), ring.2 (boolPoint (h + 6) n) * ofK (col n)

/-- The program's ring weight paired with a block column packs the slices' staged maps. -/
theorem pair_ringCol (h : ℕ) (col : ℕ → K) {pt ch : List E} (hpt : pt.length = h + 6)
    (hch : ch.length = 6) :
    ∑ n ∈ range (2 ^ (h + 6)), ringWeight pt (boolPoint (h + 6) n) (ringCoefficients ch) * ofK (col n) =
      ∑ i : Fin 64, ringW i * phiMap (sliceExt h col pt i) ch := by
  simp only [ringWeight_eq_sum, length_ringCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ k ∈ range 64, ∑ n ∈ range (2 ^ (h + 6)),
      (ringCoefficients ch).getD k 0 * eqEval (pt.map (· ^ 2 ^ k)) (boolPoint (h + 6) n) *
        ofK (col n) =
      (ringCoefficients ch).getD k 0 * ∑ i : Fin 64, ringW i * sliceExt h col pt i ^ 2 ^ k := by
    intro k _
    rw [← colExt_frob, colExt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have hl : (pt.map (· ^ 2 ^ k)).length = h + 6 := by rw [List.length_map, hpt]
    rw [← hl, eqEval_boolPoint_eqAt]
    ring
  rw [Finset.sum_congr rfl e]
  simp only [phiMap_eq_sum hch, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

/-- **The ring claim on a block holds iff the errors' twisted sum vanishes.** -/
theorem ringCol_iff (h : ℕ) (col : ℕ → K) {pt sv ch : List E} (hpt : pt.length = h + 6)
    (hsv : sv.length = 64) (hch : ch.length = 6) :
    RingColTrue h col (polyEval (sv.map (phiMap · ch)) gen,
        fun rPrime ↦ ringWeight pt rPrime (ringCoefficients ch)) ↔
      ∑ i : Fin 64, ringW i * phiMap (ringErr h col pt sv i) ch = 0 := by
  unfold RingColTrue
  simp only
  rw [pair_ringCol h col hpt hch, ringTarget_eq_sum sv ch hsv]
  simp only [ringErr, phiMap_sub, mul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]

/-! ## Ring switching with a carried predicate -/

variable {β : Type} {C : List Ev → Set β}

/-- Alive after the coefficients `acc`: `R`, and every `π_k`, `k < 2^(6 - |acc|)`, of the
slices' errors under the stages of `acc` vanishes. -/
def RingAliveC (h : ℕ) (col : β → ℕ → K) (R : β → Prop) (pt sv acc : List E) (q : β) : Prop :=
  R q ∧ ∀ k < 2 ^ (6 - acc.length),
    frobPair Finset.univ ringW (fun i ↦ frobMap (stagesOf acc) (ringErr h (col q) pt sv i)) k = 0

/-- A coefficient's escape (leanVM's `ring_escape`). -/
theorem ringC_escape (h : ℕ) (col : β → ℕ → K) (R : β → Prop) (pt sv acc : List E) (q : β)
    (hq : ¬ RingAliveC h col R pt sv acc q) :
    avgE (fun c ↦ indE (RingAliveC h col R pt sv (acc ++ [c]) q)) ≤ errE 1 := by
  classical
  have hzero : avgE (fun _ : E ↦ indE False) ≤ errE 1 :=
    (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le
  by_cases hG : R q
  swap
  · exact (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ hG hc.1).trans hzero
  let b : Fin 64 → E := fun i ↦ frobMap (stagesOf acc) (ringErr h (col q) pt sv i)
  rcases Nat.lt_or_ge acc.length 6 with hlen | hlen
  · let M := 2 ^ (5 - acc.length)
    have h2M : 2 * M = 2 ^ (6 - acc.length) := by
      simp only [M, ← pow_succ']
      congr 1
      omega
    have hex : ∃ k < 2 * M, frobPair Finset.univ ringW b k ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_and, not_not] at hall
      exact hq ⟨hG, fun k hk ↦ hall k (by rw [h2M]; exact hk)⟩
    have hcard := card_stage_zero_le_one Finset.univ ringW b M hex
    calc avgE (fun c ↦ indE (RingAliveC h col R pt sv (acc ++ [c]) q))
        ≤ avgE (fun c ↦ indE (∀ k < M,
            frobPair Finset.univ ringW (fun i ↦ b i + c * b i ^ 2 ^ M) k = 0)) :=
          avgE_mono fun c ↦ indE_mono fun hc k hk ↦ by
            have h' := hc.2 k (by
              rw [List.length_append, List.length_singleton]
              simp only [M] at hk
              rwa [show 6 - (acc.length + 1) = 5 - acc.length by omega])
            rw [stagesOf_snoc acc c hlen] at h'
            simp only [frobMap_append] at h'
            exact h'
      _ = (Fintype.card E : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun c : E ↦ ∀ k < M,
            frobPair Finset.univ ringW (fun i ↦ b i + c * b i ^ 2 ^ M) k = 0).card : ℝ≥0∞) :=
          (card_filter_eq_avgE _).symm
      _ ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
          exact_mod_cast hcard
      _ = errE 1 := by rw [mul_one, errE, Nat.cast_one, one_mul]
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ hq ⟨hG, fun k hk ↦ ?_⟩).trans hzero
    have h' := hc.2 k (by
      rw [List.length_append, List.length_singleton]
      rwa [show 6 - (acc.length + 1) = 6 - acc.length by omega])
    rwa [stagesOf_snoc_of_le acc c hlen] at h'

variable [Finite β] {L₀ : ℕ}

/-- Ring switching draws the six coefficients and returns the target and the weight. -/
theorem ringSwitch_eq' (point sv : List E) :
    ringSwitch point sv = VerifierProgram.sampleChallenges 6 >>= fun ch ↦
      VerifierProgram.ret (polyEval (sv.map (phiMap · ch)) gen,
        fun rPrime ↦ ringWeight point rPrime (ringCoefficients ch)) := rfl

/-- **Ring switching on a block column**, carrying `R`: from doom of `slicesTrue ∧ R` to doom of
`RingColTrue ∧ R`; lead `6·L₀/|E|` plus the follower's. -/
noncomputable def ringColSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (h : ℕ)
    (col : β → ℕ → K) (R : β → Prop) {εmax T : ℝ≥0∞} (pt sv : List E)
    (hl : pt.length = h + 6 ∧ sv.length = 64) :
    Spec (ringSwitch pt sv) (Doomed C (fun q ↦ slicesTrue h (col q) pt sv ∧ R q))
      (fun r hist ↦ Doomed C (fun q ↦ RingColTrue h (col q) r ∧ R q) hist) εmax
      ((∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T) T :=
  Spec.congr (ringSwitch_eq' pt sv).symm <|
    ((doomSampleN hst hcard (fun acc q ↦ RingAliveC h col R pt sv acc q) (fun _ ↦ errE 1)
        (fun acc q hq ↦ ringC_escape h col R pt sv acc q hq) 6 []).mono
        (fun _ hd q hq ⟨hR, hπ⟩ ↦ hd q hq ⟨by
          refine ⟨hl.1, hl.2, fun i hi ↦ ?_⟩
          have hδ := ringSwitch_injective (fun i ↦ ringErr h (col q) pt sv i)
            (fun k hk ↦ hπ k (by simpa using hk)) ⟨i, hi⟩
          exact sub_eq_zero.mp hδ, hR⟩)
        (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun ch ↦
      (Spec.ret _).mono (fun _ hd ↦ by
          intro q hq ⟨hclaim, hR⟩
          refine hd.2 q hq ?_
          have h6 : ch.length = 6 := by simpa using hd.1
          refine ⟨hR, fun k hk ↦ ?_⟩
          rw [List.nil_append, h6, Nat.sub_self, pow_zero, Nat.lt_one_iff] at hk
          subst hk
          have := (ringCol_iff h (col q) hl.1 hl.2 h6).mp hclaim
          simpa only [List.nil_append, frobPair, pow_zero, pow_one, phiMap_eq_frobMap] using this)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## A zero test with a carried predicate -/

/-- The escape bound of the `i`-th of `n` zero-test coordinates (`1` past them). -/
noncomputable def zE (n i : ℕ) : ℝ≥0∞ := if i < n then errE 1 else 1

omit [Finite β] in
/-- **A zero-test coordinate's escape**, carrying `R` (leanVM's `zt_escape`, `n` coordinates). -/
theorem zero_escape (δ : β → ℕ → E) (R : β → Prop) (n : ℕ) (acc : List E) (q : β)
    (hq : ¬ (ZeroOn (δ q) acc n ∧ R q)) :
    avgE (fun c ↦ indE (ZeroOn (δ q) (acc ++ [c]) n ∧ R q)) ≤ zE n acc.length := by
  unfold zE
  split_ifs with hn
  · by_cases hR : R q
    · exact (avgE_mono fun c ↦ indE_mono fun hc ↦ hc.1).trans
        (zeroOn_escape (δ q) hn fun h ↦ hq ⟨h, hR⟩)
    · exact (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hR h.2).trans
        ((avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le)
  · exact avgE_indE_le_one _

theorem sum_zE {n m : ℕ} (hm : m ≤ n) (L₀ : ℕ) :
    ∑ i ∈ range m, (L₀ : ℝ≥0∞) * zE n (0 + i) = m * (L₀ * errE 1) := by
  rw [Finset.sum_congr rfl fun i hi ↦ by
    rw [zE, if_pos (by have := Finset.mem_range.1 hi; omega)]]
  simp

/-- **`m ≤ n` zero-test coordinates**, carrying `R`: from doom of `ZeroOn δ [] n ∧ R` to doom of
`ZeroOn δ pt n ∧ R` at the `m` challenges `pt`; lead `m·L₀/|E|` plus the follower's. -/
noncomputable def zeroSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (δ : β → ℕ → E)
    (R : β → Prop) {n m : ℕ} (hm : m ≤ n) {εmax T : ℝ≥0∞} :
    Spec (VerifierProgram.sampleChallenges m) (Doomed C (fun q ↦ ZeroOn (δ q) [] n ∧ R q))
      (fun pt hist ↦ pt.length = m ∧ Doomed C (fun q ↦ ZeroOn (δ q) pt n ∧ R q) hist) εmax
      (m * (L₀ * errE 1) + T) T :=
  (doomSampleN hst hcard (fun acc q ↦ ZeroOn (δ q) acc n ∧ R q) (zE n)
      (fun acc q hq ↦ zero_escape δ R n acc q hq) m []).mono (fun _ h ↦ h)
    (fun _ _ h ↦ by simpa using h) le_rfl (by rw [List.length_nil, sum_zE hm]) le_rfl

end Lvm.KG
