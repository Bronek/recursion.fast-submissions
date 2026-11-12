-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Escape.lean` (formal rev 40f877dc) as `LvmWhirEscape`
-- for lvm (WP-7). Changed for the unique-decoding regime: the out-of-domain separation (`oodVal`, `OodSep`,
-- `card_oodSep_bad_le` and its helpers) and the three-term glue are cut with the step; `QueryGood`/`exists_agreeSet`
-- become `QueryGoodUd`/`exists_agreeSet_ud`, whose one candidate comes from the list bound (`card ≤ 1`) instead of
-- the out-of-domain answer; new: `mem_iList_of_close`, `FinViol` (the final level's doom after the residual) and
-- `exists_agreeSet_finViol`. The batching sums, `viol_of_close` and the final level's step are leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.Escape

  The escape counts of a WHIR level interface in the unique-decoding regime: the query positions
  catch the one candidate of the next oracle's list unless they all land in an agreement set of
  fewer than `A` columns; and the level's batching challenge `λ` keeps every list member violating
  the glued claim except at `t·L` values (`t` on the final level, no list).
-/


import LvmWhirLanes
import LvmWhirCounting

/-!
# Escapes at the level interface

Annex B of the leanVM specification (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "Query
message" and "Batching challenge", for lvm's order of messages (`whirLevelsUd`): commitment of the
next oracle `O'`, the query positions, `λ`, the openings, the query intro polynomial. The level's
claims are glued with powers of `λ`: the running claim with `λ⁰`, the `t` consistency claims with
`λ^(1+q)`. On the final level the residual `f` is sent instead of `O'`. There is no out-of-domain
step: in the unique-decoding regime the next list has at most one member (`listMax = 1`).

* `QueryGoodUd`: after positions `qs`, every member `V` of the next list violates the running
  claim or the consistency claim at some queried column. `exists_agreeSet_ud`: under the doom
  before the positions and a list of at most one member, there is a set `A` of at most `thr − 1`
  columns such that positions breaking `QueryGoodUd` all lie in `A`: the one candidate `V*`
  either is close to the folded word, then it violates the running claim by the doom, or agrees
  with it on fewer than `thr` columns.
* `card_glue_bad_le_final`: a nonzero discrepancy polynomial of degree `t` in `λ` has at most `t`
  roots (the glue of a mid level and of the final level alike).
* The final level: `exists_agreeSet_final`, and `FinViol P C Φ σ G` (the residual `G` violates the
  running claim, or its encoding is not in the list of the folded word `C`), which the doom of every
  member implies (`finViol_of_viol`) and which suffices for the query step
  (`exists_agreeSet_finViol`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset CompPoly
  CMlPolynomialEval

section

/-! ## Batching sums -/

/-- The batched sum with `powers λ`: `Σ_q λ^q f(q)`. -/
theorem sum_zip_powersFrom (lam acc : E) (qs : List ℕ) (f : ℕ → E) :
    (((powersFrom acc lam qs.length).zip qs).map fun wq ↦ wq.1 * f wq.2).sum =
      ∑ k : Fin qs.length, acc * lam ^ (k : ℕ) * f qs[k] := by
  induction qs generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.length_cons, powersFrom, List.zip_cons_cons, List.map_cons, List.sum_cons, ih,
      Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
    refine congrArg (_ + ·) (Finset.sum_congr rfl fun k _ ↦ ?_)
    simp only [pow_succ]
    ring_nf
    rfl

theorem sum_zip_powers (lam : E) (qs : List ℕ) (f : ℕ → E) :
    (((powers lam qs.length).zip qs).map fun wq ↦ wq.1 * f wq.2).sum =
      ∑ k : Fin qs.length, lam ^ (k : ℕ) * f qs[k] := by
  rw [powers, sum_zip_powersFrom]
  simp

/-- `powers λ t` has `t` entries. -/
theorem length_powers (lam : E) (t : ℕ) : (powers lam t).length = t := by
  rw [powers]
  suffices h : ∀ acc, (powersFrom acc lam t).length = t from h 1
  induction t with
  | zero => intro; rfl
  | succ t ih => intro acc; simp [powersFrom, ih]

/-! ## Query positions -/

/-- An entry of a word at an integer position (`0` outside). -/
def wordAt {n : ℕ} (C : Fin n → E) (q : ℕ) : E := if h : q < n then C ⟨q, h⟩ else 0

/-- After positions `qs`, every member of the list of `Q'` violates the running claim `(Φ, σ)` or
the consistency claim at a queried column of the folded word `C`. -/
def QueryGoodUd (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (qs : List ℕ) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) ≠ σ ∨
    ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (decode P' V)) q ≠ wordAt C q

/-- A message whose encoding agrees with the folded word on `thr` columns is in its list. -/
theorem mem_iList_of_close (P : LevelCode) (C : Fin P.n → E) (G : (Fin P.κ → Bool) → E)
    (hclose : P.thr ≤ (univ.filter fun x ↦ enc P.κ P.R G x = C x).card) :
    (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∈ iList P.code P.thr fun _ ↦ C := by
  rw [mem_iList]
  refine ⟨fun _ ↦ ?_, _, hclose, fun _ x hx ↦ ((Finset.mem_filter.mp hx).2).symm⟩
  show _ ∈ rsCode (domain P.κ P.R P.h64) (2 ^ P.κ)
  rw [← range_enc P.h64]; exact LinearMap.mem_range_self _ _

/-- A message whose encoding agrees with the folded word on `thr` columns is caught by the
running claim. -/
theorem viol_of_close (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E)
    (hclose : P.thr ≤ (univ.filter fun x ↦ enc P.κ P.R G x = C x).card) :
    ∑ x, Φ (bitsL x) * G x ≠ σ := by
  have hmem : (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∈ iList P.code P.thr fun _ ↦ C := by
    rw [mem_iList]
    refine ⟨fun _ ↦ ?_, _, hclose, fun _ x hx ↦ ((Finset.mem_filter.mp hx).2).symm⟩
    show _ ∈ rsCode (domain P.κ P.R P.h64) (2 ^ P.κ)
    rw [← range_enc P.h64]; exact LinearMap.mem_range_self _ _
  have := hviol _ hmem
  rwa [decode_enc P (fun _ ↦ G), claimSum_zero] at this

/-- **The query step** (unique decoding). Under the doom before the positions (every member of the
list of the folded word `C` violates `(Φ, σ)`) and a list of `Q'` with at most one member, the
positions breaking `QueryGoodUd` all lie in a set of at most `thr − 1` columns. -/
theorem exists_agreeSet_ud (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hone : (iList P'.code P'.thr Q').card ≤ 1) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodUd P P' hκ Q' C Φ σ qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ
  · obtain ⟨V₀, hV₀, hclaim⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact viol_of_close P C Φ σ hviol G (Nat.lt_succ_iff.mp (not_le.mp hlt))
        (by rw [sum_joinMsg]; exact hclaim)
    · intro hlt
      simp only [QueryGoodUd, not_forall, not_or, not_not, exists_prop, not_exists,
        not_and] at hqs
      obtain ⟨V, hV, -, hall⟩ := hqs
      have hVV : V = V₀ := Finset.card_le_one.mp hone _ hV _ hV₀
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV
    exact Or.inl fun h ↦ hex ⟨V, hV, h⟩

/-! ## The batching challenge -/

/-- **The final batching step.** If the residual violates the running claim or a consistency
claim, the glued claim with powers `1, λ, …, λ^t` holds at at most `t` values `λ`. -/
theorem card_glue_bad_le_final {t : ℕ} (a σ : E) (e c : Fin t → E)
    (h : a ≠ σ ∨ ∃ k, e k ≠ c k) :
    (univ.filter fun lam : E ↦ a + lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k =
        σ + lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k).card ≤ t := by
  let d : Fin (t + 1) → E := Fin.cons (a - σ) fun k ↦ e k - c k
  have hd : ∃ k, d k ≠ 0 := by
    rcases h with h | ⟨k, hk⟩
    · exact ⟨0, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨k.succ, by simpa [d, sub_eq_zero] using hk⟩
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans (card_powerBatch_eq_zero_le d hd)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
  have hs : ∑ k : Fin t, (e k - c k) * lam ^ ((k : ℕ) + 1) =
      lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k - lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [d, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, hs]
  linear_combination hlam

/-! ## The final level's query step -/

/-- After positions `qs` on the final level, the residual `G` violates the running claim or the
consistency claim at a queried column. -/
def QueryGoodFinal (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (qs : List ℕ) : Prop :=
  ∑ x, Φ (bitsL x) * G x ≠ σ ∨ ∃ q ∈ qs, encAt P.κ P.R G q ≠ wordAt C q

/-- **The final query step.** Positions breaking `QueryGoodFinal` lie in a set of at most
`thr − 1` columns. -/
theorem exists_agreeSet_final (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodFinal P C Φ σ G qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hc : ∑ x, Φ (bitsL x) * G x = σ
  · refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact viol_of_close P C Φ σ hviol G (Nat.lt_succ_iff.mp (not_le.mp hlt)) hc
    · simp only [QueryGoodFinal, not_or, not_not, not_exists, not_and] at hqs
      intro hlt
      have h := hqs.2 q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd (Or.inl hc) hqs⟩

/-- **The final level's doom after the residual** `G`: `G` violates the running claim, or its
encoding is not in the list of the folded word `C`. -/
def FinViol (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) : Prop :=
  ∑ x, Φ (bitsL x) * G x ≠ σ ∨
    (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∉ iList P.code P.thr fun _ ↦ C

/-- The doom of every member of the list implies the residual's. -/
theorem finViol_of_viol (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ) (G : (Fin P.κ → Bool) → E) :
    FinViol P C Φ σ G := by
  by_cases hc : ∑ x, Φ (bitsL x) * G x = σ
  · refine Or.inr fun hmem ↦ ?_
    have := hviol _ hmem
    rw [decode_enc P (fun _ ↦ G), claimSum_zero] at this
    exact this hc
  · exact Or.inl hc

/-- **The final query step from the residual's doom.** Positions breaking `QueryGoodFinal` lie in
a set of at most `thr − 1` columns. -/
theorem exists_agreeSet_finViol (P : LevelCode) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (hD : FinViol P C Φ σ G) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodFinal P C Φ σ G qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hc : ∑ x, Φ (bitsL x) * G x = σ
  · have hfar : (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G) ∉ iList P.code P.thr fun _ ↦ C :=
      hD.resolve_left (not_not.mpr hc)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact hfar (mem_iList_of_close P C G (Nat.lt_succ_iff.mp (not_le.mp hlt)))
    · simp only [QueryGoodFinal, not_or, not_not, not_exists, not_and] at hqs
      intro hlt
      have h := hqs.2 q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd (Or.inl hc) hqs⟩

end
end LeanVM.Protocol.Whir.Sound
