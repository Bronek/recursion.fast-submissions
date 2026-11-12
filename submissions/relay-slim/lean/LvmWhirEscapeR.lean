-- New for lvm2 (WP JB-L, J2): the escapes at the level interface with an out-of-domain step for the relativised doom
-- (`ViolR`, `LvmWhirPathR`). Twins of `QueryGood`, `exists_agreeSet`, `card_lambda_bad_le`, `escRet_queryFrag_le`
-- (`LvmWhirEscapeJ`, ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Escape.lean`, formal rev 0b850750)
-- and `escRet_queryFragG_le` (`LvmWhirMidJ`): only the tracked members of the lists are counted; same bounds.
/-
  LeanVM.Protocol.Whir.Sound.EscapeR

  The escapes of a WHIR level interface with an out-of-domain step, relativised to the members
  that are on no path of the good set `Gd`.
-/

import LvmWhirPathR
import LvmWhirMidJ

/-!
# Escapes at the level interface, relativised

The doom on the folded word `C` is `ViolR P Gd fs (fun _ ↦ C) Φ σ`: every **tracked** member of
`C`'s list (on no path of `Gd` after the fold challenges `fs`) violates the running claim.

* `QueryGoodR`: after positions `qs`, every tracked member `V` of the next list violates the running
  claim, or the out-of-domain claim, or the consistency claim at some queried column.
* `exists_agreeSet_R`: under the relativised doom and `OodSep`, the positions breaking `QueryGoodR`
  lie in a set of at most `thr − 1` columns. The one tracked member `V*` consistent with the running
  claim and the out-of-domain answer has a joined message whose encoding agrees with `C` on fewer
  than `thr` columns: otherwise that encoding is a member of `C`'s list, tracked
  (`pathAt_joinMsg_iff`), so it violates the running claim by the doom.
* `card_lambda_bad_le_R`: under `QueryGoodR`, at most `(t + 1)·listMax'` values `λ` break `ViolR`
  for the glued claim.
* `escRet_queryFrag_le_R`, `escRet_queryFragG_le_R`: the query group escapes the glued claim's
  relativised doom with probability at most `eQuery P P' t` (`2^-g · eQuery P P' t` with the proof
  of work).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-- After positions `qs`, every tracked member of the list of `Q'` violates the running claim
`(Φ, σ)`, the out-of-domain claim `(eq_eval(z, ·), y)`, or the consistency claim at a queried
column of the folded word `C`. -/
def QueryGoodR (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ) {μ : ℕ} (Gd : Set (Column μ))
    (fs : List E) (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', Tracked Gd fs (decode P' V) →
    claimSum Φ (decode P' V) ≠ σ ∨ oodVal z (decode P' V) ≠ y ∨
      ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (decode P' V)) q ≠ wordAt C q

/-- **The query step, relativised.** Under the relativised doom before the positions (every tracked
member of the list of the folded word `C` violates `(Φ, σ)`, and the out-of-domain values separate
the list of `Q'`), the positions breaking `QueryGoodR` all lie in a set of at most `thr − 1`
columns. -/
theorem exists_agreeSet_R (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ) {μ : ℕ}
    (Gd : Set (Column μ)) (fs : List E)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : ViolR P Gd fs (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGoodR P P' hκ Gd fs Q' C Φ σ z y qs → ∀ q ∈ qs, ∀ h : q < P.n,
        (⟨q, h⟩ : Fin P.n) ∈ A := by
  classical
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', Tracked Gd fs (decode P' V) ∧
      claimSum Φ (decode P' V) = σ ∧ oodVal z (decode P' V) = y
  · obtain ⟨V₀, hV₀, htr, hclaim, hood⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      have hclose : P.thr ≤ (univ.filter fun x ↦ enc P.κ P.R G x = C x).card :=
        Nat.lt_succ_iff.mp (not_le.mp hlt)
      have htrG : Tracked Gd fs (decode P (fun _ : Fin 0 → Bool ↦ enc P.κ P.R G)) := by
        rw [decode_enc P (fun _ ↦ G)]
        exact fun q hq hp ↦ htr q hq ((pathAt_joinMsg_iff hκ q fs _).mp hp)
      have h := hviol _ (mem_iList_of_close P C G hclose) htrG
      rw [decode_enc P (fun _ ↦ G), claimSum_zero] at h
      exact h (by rw [sum_joinMsg]; exact hclaim)
    · intro hlt
      simp only [QueryGoodR, not_forall, not_or, not_not, exists_prop, not_exists, not_and] at hqs
      obtain ⟨V, hV, -, hc, ho, hall⟩ := hqs
      have hVV : V = V₀ := by
        by_contra hne
        exact hsep V hV V₀ hV₀ hne (ho.trans hood.symm)
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV htr
    by_contra h
    simp only [not_or, not_not] at h
    exact hex ⟨V, hV, htr, h.1, h.2.1⟩

open Classical in
/-- **The batching step of a level with a next commitment, relativised.** -/
theorem card_lambda_bad_le_R (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) {μ : ℕ}
    (Gd : Set (Column μ)) (fs : List E)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n)
    (hgood : QueryGoodR P P' hκ Gd fs Q' C Φ σ z y qs) :
    (univ.filter fun lam : E ↦ ¬ ViolR P' Gd fs Q'
        (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])).card ≤
      (qs.length + 1) * P'.listMax := by
  set L := iList P'.code P'.thr Q'
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans
    ((card_filter_exists_le L (fun V lam ↦ Tracked Gd fs (decode P' V) ∧
        claimSum Φ (decode P' V) + lam * oodVal z (decode P' V) + lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R (joinMsg hκ (decode P' V)) qs[k] =
        σ + lam * y + lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])
      (N := qs.length + 1) fun V hV ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ViolR, not_forall, not_not,
      exists_prop] at hlam ⊢
    obtain ⟨V, hV, htr, heq⟩ := hlam
    refine ⟨V, hV, htr, ?_⟩
    rw [claimSum_glue2, claimSum_inducedWeight P hκ qs hqs lam] at heq
    rw [oodVal]
    simpa only [one_mul] using heq
  · by_cases htr : Tracked Gd fs (decode P' V)
    · refine (Finset.card_le_card fun lam hlam ↦ ?_).trans (card_glue_bad_le
        (claimSum Φ (decode P' V)) σ (oodVal z (decode P' V)) y
        (fun k : Fin qs.length ↦ encAt P.κ P.R (joinMsg hκ (decode P' V)) qs[k])
        (fun k : Fin qs.length ↦ wordAt C qs[k]) ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact hlam.2
      · rcases hgood V hV htr with h | h | ⟨q, hq, hne⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
          exact Or.inr (Or.inr ⟨⟨k, hk⟩, hne⟩)
    · simp [htr]
  · rw [mul_comm]
    exact Nat.mul_le_mul_left _ (P'.card_iList_le Q')

open Classical in
/-- **The query group of a level with a next commitment, relativised.** -/
theorem escRet_queryFrag_le_R (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    {μ : ℕ} (Gd : Set (Column μ)) (fs : List E)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : ViolR P Gd fs (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ViolR P' Gd fs Q' (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQuery P P' t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet_R P P' hκ Gd fs Q' C Φ σ z y hviol hsep
  refine (retExp_queryFrag_le per (P.κ + P.R) t c hper hpd h₀ hW _
    (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A)
    ((((t + 1) * P'.listMax : ℕ) : ENNReal) / Fintype.card E) ?_).trans ?_
  · intro qs hr hlen
    by_cases hall : ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A
    · have : allIn (fun q ↦ ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A) qs = 1 := by
        unfold allIn
        split_ifs with h
        · rfl
        · exact absurd hall h
      rw [this]
      exact (avg_le_one _ fun _ ↦ by split_ifs <;> simp).trans le_self_add
    · have hgood : QueryGoodR P P' hκ Gd fs Q' C Φ σ z y qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le_R P P' hκ Gd fs Q' C Φ σ z y qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦ ¬ ViolR P' Gd fs Q'
          (fun r ↦ Φ r + 1 * lam * eqEval z r +
            1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
          (σ + 1 * lam * y + 1 * lam * lam *
            ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])) fun lam hlam ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
        exact fun hv ↦ hlam (hJ qs lam hr hlen hv)
      rw [← hlen]
      exact_mod_cast hsub.trans hcard
  · rw [card_filter_mem, eQuery]
    exact add_le_add (pow_frac_le P A hA t) le_rfl

open Classical in
/-- **The query group of a level with a next commitment and an OOD sample, with the proof of
work, relativised.** -/
theorem escRet_queryFragG_le_R (g : ℕ) (hg : g ≤ 192) (P P' : LevelCode) {ℓ' : ℕ}
    (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ) (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    {μ : ℕ} (Gd : Set (Column μ)) (fs : List E)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : ViolR P Gd fs (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ViolR P' Gd fs Q' (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFragG g per (P.κ + P.R) t c) ≤
      (2 : ENNReal)⁻¹ ^ g * eQuery P P' t := by
  refine escRet_powCheck_le g hg _ h₀ _ _ fun h hh ↦ ?_
  rw [← hh] at hW
  refine escRet_queryFrag_le_R P P' hκ per t c hper hpd h hW Gd fs Q' C Φ σ z y hviol hsep
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

end
end LeanVM.Protocol.Whir.Sound
