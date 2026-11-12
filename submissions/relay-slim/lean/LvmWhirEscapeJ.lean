-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/{Escape,Interface,Defs,GroupEscape}.lean` (formal rev
-- 0b850750) as `LvmWhirEscapeJ` for lvm2 (WP JB-L): the out-of-domain path our unique-decoding port cut (`QueryGood`,
-- `exists_agreeSet`, `card_glue_bad_le`, `claimSum_glue2`, `card_lambda_bad_le`, `eOod`, `eQuery`,
-- `escRet_sampleN_le`, `escRet_queryFrag_le`), restored against `LvmWhirEscape`/`LvmWhirInterface`/`LvmWhirDefs`/
-- `LvmWhirGroupEscape`. Changed: `escRet_queryFrag_le` takes lvm's `queryFrag per (κ + R) t c` (positions `per` per
-- challenge, commitment index `c`, side conditions `1 ≤ per`, `per·(κ + R) ≤ 192`) as `escRet_queryFrag_le_ud` does;
-- no proof-of-work discount. Statements and proofs are otherwise leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.EscapeJ

  The escapes of a WHIR level interface with an out-of-domain step, for a list of the next oracle
  with up to `listMax'` members: the out-of-domain point separates the list except with
  probability `C(L', 2)·κ/|E|`; the query positions catch the one candidate consistent with the
  out-of-domain answer except with probability `((A − 1)/n)^t`; and `λ` keeps every member
  violating the glued claim except at `(t + 1)·L'` values.
-/

import LvmWhirOod
import LvmWhirGroupEscape

/-!
# Escapes at the level interface with an out-of-domain step

Annex B of the leanVM specification (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "OOD
challenge", "Query message" and "Batching challenge", for the deployed order of messages
(`verify_whir`, `crates/verifier/src/whir.rs:167-232` at `40f877dc`): commitment of the next
oracle `O'`, the out-of-domain point `z` and answer `y` with its intro polynomial, the query
positions, `λ`, the openings, the query intro polynomial. The level's claims are glued with powers
of `λ`: the running claim with `λ⁰`, the out-of-domain claim with `λ`, the `t` consistency claims
with `λ^(2+q)`.

* `QueryGood`: after positions `qs`, every member `V` of the next list violates the running claim,
  or the out-of-domain claim, or the consistency claim at some queried column. `exists_agreeSet`:
  under the doom before the positions and `OodSep` (`LvmWhirOod`), there is a set `A` of at most
  `thr − 1` columns such that positions breaking `QueryGood` all lie in `A`.
* `card_glue_bad_le`: a nonzero discrepancy polynomial of degree `t + 1` in `λ` has at most
  `t + 1` roots; `card_lambda_bad_le`: under `QueryGood`, at most `(t + 1)·listMax'` values `λ`
  break `Viol` for the glued claim (`claimSum_glue2`).
* `eOod P' κ = C(L', 2)·κ/|E|` and `eQuery P P' t = ((A − 1)/n)^t + (t + 1)·L'/|E|`.
* `escRet_sampleN_le`: the out-of-domain group (`sampleChallenges κ`) escapes `OodSep` with
  probability at most `eOod P' κ` (`card_oodSep_bad_le`, `retExp_sampleN`).
* `escRet_queryFrag_le`: the query group escapes the glued claim's doom with probability at most
  `eQuery P P' t` (`exists_agreeSet`, `retExp_queryFrag_le`, `card_lambda_bad_le`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## The query step -/

/-- After positions `qs`, every member of the list of `Q'` violates the running claim `(Φ, σ)`,
the out-of-domain claim `(eq_eval(z, ·), y)`, or the consistency claim at a queried column of the
folded word `C`. -/
def QueryGood (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) : Prop :=
  ∀ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) ≠ σ ∨ oodVal z (decode P' V) ≠ y ∨
    ∃ q ∈ qs, encAt P.κ P.R (joinMsg hκ (decode P' V)) q ≠ wordAt C q

/-- **The query step.** Under the doom before the positions (every member of the list of the
folded word `C` violates `(Φ, σ)`, and the out-of-domain values separate the list of `Q'`), the
positions breaking `QueryGood` all lie in a set of at most `thr − 1` columns. -/
theorem exists_agreeSet (P P' : LevelCode) {m : ℕ} (hκ : P.κ = m + P'.κ)
    (Q' : (Fin m → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) :
    ∃ A : Finset (Fin P.n), A.card + 1 ≤ P.thr ∧ ∀ qs : List ℕ,
      ¬ QueryGood P P' hκ Q' C Φ σ z y qs → ∀ q ∈ qs, ∀ h : q < P.n, (⟨q, h⟩ : Fin P.n) ∈ A := by
  by_cases hex : ∃ V ∈ iList P'.code P'.thr Q', claimSum Φ (decode P' V) = σ ∧
      oodVal z (decode P' V) = y
  · obtain ⟨V₀, hV₀, hclaim, hood⟩ := hex
    set G := joinMsg hκ (decode P' V₀)
    refine ⟨univ.filter fun x ↦ enc P.κ P.R G x = C x, ?_, fun qs hqs q hq ↦ ?_⟩
    · by_contra hlt
      exact viol_of_close P C Φ σ hviol G (Nat.lt_succ_iff.mp (not_le.mp hlt))
        (by rw [sum_joinMsg]; exact hclaim)
    · intro hlt
      simp only [QueryGood, not_forall, not_or, not_not, exists_prop, not_exists, not_and] at hqs
      obtain ⟨V, hV, hc, ho, hall⟩ := hqs
      have hVV : V = V₀ := by
        by_contra hne
        exact hsep V hV V₀ hV₀ hne (ho.trans hood.symm)
      subst hVV
      have h := hall q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simpa [encAt, wordAt, LevelCode.n, hlt] using h⟩
  · refine ⟨∅, by simpa using Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.two_pow_pos _)
      P.two_pow_le_thr), fun qs hqs ↦ absurd ?_ hqs⟩
    intro V hV
    by_contra h
    simp only [not_or, not_not] at h
    exact hex ⟨V, hV, h.1, h.2.1⟩

/-! ## The batching challenge -/

/-- **The batching step.** If a member violates one of the running, out-of-domain and `t`
consistency claims, the glued claim with powers `1, λ, λ^2, …, λ^(t+1)` holds at at most `t + 1`
values `λ`. -/
theorem card_glue_bad_le {t : ℕ} (a σ b y : E) (e c : Fin t → E)
    (h : a ≠ σ ∨ b ≠ y ∨ ∃ k, e k ≠ c k) :
    (univ.filter fun lam : E ↦ a + lam * b + lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k =
        σ + lam * y + lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k).card ≤ t + 1 := by
  let d : Fin (t + 2) → E := Fin.cons (a - σ) (Fin.cons (b - y) fun k ↦ e k - c k)
  have hd : ∃ k, d k ≠ 0 := by
    rcases h with h | h | ⟨k, hk⟩
    · exact ⟨0, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨1, by simpa [d, sub_eq_zero] using h⟩
    · exact ⟨k.succ.succ, by simpa [d, sub_eq_zero] using hk⟩
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans (card_powerBatch_eq_zero_le d hd)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
  have hs : ∑ k : Fin t, (e k - c k) * lam ^ ((k : ℕ) + 1 + 1) =
      lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * e k -
        lam * lam * ∑ k : Fin t, lam ^ (k : ℕ) * c k := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [d, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, hs]
  linear_combination hlam

theorem claimSum_glue2 {m κ : ℕ} (Φ Ψ₁ Ψ₂ : List E → E) (a b : E)
    (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    claimSum (fun r ↦ Φ r + a * Ψ₁ r + b * Ψ₂ r) g =
      claimSum Φ g + a * claimSum Ψ₁ g + b * claimSum Ψ₂ g := by
  simp only [claimSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

open Classical in
/-- **The batching step of a level with a next commitment.** -/
theorem card_lambda_bad_le (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (qs : List ℕ) (hqs : ∀ q ∈ qs, q < P.n)
    (hgood : QueryGood P P' hκ Q' C Φ σ z y qs) :
    (univ.filter fun lam : E ↦ ¬ Viol P' Q'
        (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])).card ≤
      (qs.length + 1) * P'.listMax := by
  set L := iList P'.code P'.thr Q'
  refine (Finset.card_le_card fun lam hlam ↦ ?_).trans
    ((card_filter_exists_le L (fun V lam ↦
        claimSum Φ (decode P' V) + lam * oodVal z (decode P' V) + lam * lam *
          ∑ k : Fin qs.length, lam ^ (k : ℕ) * encAt P.κ P.R (joinMsg hκ (decode P' V)) qs[k] =
        σ + lam * y + lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k])
      (N := qs.length + 1) fun V hV ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Viol, not_forall, not_not,
      exists_prop] at hlam ⊢
    obtain ⟨V, hV, heq⟩ := hlam
    refine ⟨V, hV, ?_⟩
    rw [claimSum_glue2, claimSum_inducedWeight P hκ qs hqs lam] at heq
    rw [oodVal]
    simpa only [one_mul] using heq
  · refine card_glue_bad_le _ σ _ y _ _ ?_
    rcases hgood V hV with h | h | ⟨q, hq, hne⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
      exact Or.inr (Or.inr ⟨⟨k, hk⟩, hne⟩)
  · rw [mul_comm]
    exact Nat.mul_le_mul_left _ (P'.card_iList_le Q')

/-! ## Escape bounds -/

/-- The out-of-domain escape: `C(L', 2)·κ / |E|`. -/
noncomputable def eOod (P' : LevelCode) (κ : ℕ) : ENNReal :=
  ((P'.listMax.choose 2 * κ : ℕ) : ENNReal) / Fintype.card E

/-- The query group's escape: `((A − 1)/n)^t + (t + 1)·L' / |E|`. -/
noncomputable def eQuery (P P' : LevelCode) (t : ℕ) : ENNReal :=
  (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t + (((t + 1) * P'.listMax : ℕ) : ENNReal) / Fintype.card E

/-! ## The groups -/

open Classical in
/-- **The out-of-domain group.** -/
theorem escRet_sampleN_le (P' : LevelCode) {κ ℓ' : ℕ} (hκ : κ = ℓ' + P'.κ) (hκ1 : 1 ≤ κ)
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (J : List E → List (ℕ × ℕ × Word) → Prop)
    (h₀ : List Ev) (hJ : ∀ z : List E, z.length = κ → OodSep P' Q' z → J z (commits h₀)) :
    escRet (fun z h ↦ J z (commits h)) h₀ [] (sampleChallenges κ) ≤ eOod P' κ := by
  unfold escRet
  rw [retExp_commits (fun z cs ↦ if J z cs then 0 else 1), List.append_nil, retExp_sampleN]
  set N := (univ.filter fun v : Vector E κ ↦ ¬ OodSep P' Q' v.toList).card
  have hsum : ∑ f : Fin κ → E, (if J (List.ofFn f) (commits h₀) then 0 else 1 : ENNReal) ≤ N := by
    calc ∑ f : Fin κ → E, (if J (List.ofFn f) (commits h₀) then 0 else 1 : ENNReal)
        ≤ ∑ f : Fin κ → E, (if OodSep P' Q' (List.ofFn f) then 0 else 1 : ENNReal) := by
          gcongr with f
          by_cases hs : OodSep P' Q' (List.ofFn f)
          · simp [hs, hJ _ (List.length_ofFn) hs]
          · split_ifs <;> simp
      _ = ((univ.filter fun f : Fin κ → E ↦ ¬ OodSep P' Q' (List.ofFn f)).card : ENNReal) := by
          rw [Finset.card_filter, Nat.cast_sum]
          exact Finset.sum_congr rfl fun f _ ↦ by
            by_cases h : OodSep P' Q' (List.ofFn f) <;> simp [h]
      _ = N := by
          have hcard : (univ.filter fun f : Fin κ → E ↦ ¬ OodSep P' Q' (List.ofFn f)).card = N := by
            refine Finset.card_bij' (fun f _ ↦ Vector.ofFn f) (fun v _ ↦ fun j : Fin κ ↦ v[j.val])
              ?_ ?_ ?_ ?_
            · intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
              rwa [Vector.toList_ofFn]
            · intro v hv
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
              rwa [← Vector.toList_ofFn, Vector.ofFn_getElem]
            · intro f _; funext j; simp
            · intro v _; exact Vector.ofFn_getElem
          rw [hcard]
  have hN : (N : ENNReal) ≤ ((P'.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) : ℕ) :
      ENNReal) := by exact_mod_cast card_oodSep_bad_le P' hκ Q'
  calc (Fintype.card E : ENNReal)⁻¹ ^ κ * ∑ f : Fin κ → E, _
      ≤ (Fintype.card E : ENNReal)⁻¹ ^ κ *
        ((P'.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) : ℕ) : ENNReal) := by
        gcongr; exact hsum.trans hN
    _ = eOod P' κ := by
        obtain ⟨k, rfl⟩ : ∃ k, κ = k + 1 := ⟨κ - 1, by omega⟩
        rw [eOod, ENNReal.div_eq_inv_mul, Nat.add_sub_cancel]
        push_cast
        rw [pow_succ, mul_comm ((Fintype.card E : ENNReal)⁻¹ ^ k), mul_assoc]
        have h1 : (Fintype.card E : ENNReal)⁻¹ ^ k * (Fintype.card E : ENNReal) ^ k = 1 := by
          rw [← mul_pow, ENNReal.inv_mul_cancel (by simp) (by simp), one_pow]
        calc (Fintype.card E : ENNReal)⁻¹ * ((Fintype.card E : ENNReal)⁻¹ ^ k *
              ((P'.listMax.choose 2 : ENNReal) * ((k + 1 : ENNReal) * (Fintype.card E) ^ k)))
            = (Fintype.card E : ENNReal)⁻¹ * ((P'.listMax.choose 2 : ENNReal) * (k + 1)) *
              ((Fintype.card E : ENNReal)⁻¹ ^ k * (Fintype.card E : ENNReal) ^ k) := by ring
          _ = _ := by rw [h1, mul_one]

open Classical in
/-- **The query group of a level with a next commitment.** -/
theorem escRet_queryFrag_le (P P' : LevelCode) {ℓ' : ℕ} (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (z : List E) (y : E) (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hsep : OodSep P' Q' z) (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * eqEval z r +
          1 * lam * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * y + 1 * lam * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFrag per (P.κ + P.R) t c) ≤
      eQuery P P' t := by
  unfold escRet
  rw [retExp_commits (fun g cs ↦ if J g cs then 0 else 1), List.append_nil]
  obtain ⟨A, hA, hcatch⟩ := exists_agreeSet P P' hκ Q' C Φ σ z y hviol hsep
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
    · have hgood : QueryGood P P' hκ Q' C Φ σ z y qs := by
        by_contra hng; exact hall (hcatch qs hng)
      have hcard := card_lambda_bad_le P P' hκ Q' C Φ σ z y qs hr hgood
      refine le_trans ?_ le_add_self
      rw [avg_ite_le, ENNReal.div_eq_inv_mul]
      gcongr
      have hsub := Finset.card_le_card (s := univ.filter fun lam ↦ ¬ J (qs, lam, qs.map W)
          (commits h₀)) (t := univ.filter fun lam : E ↦ ¬ Viol P' Q'
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

end
end LeanVM.Protocol.Whir.Sound
