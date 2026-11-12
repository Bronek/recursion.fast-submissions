-- New for lvm2 (WP PI-GRIND). The escape of a WHIR query group with in-answer grinding.
/-
  LeanVM.Protocol.Whir.Sound.Grind

  The proof of work before a level's positions (`powCheck g`, `LvmWhirProg`) divides the query
  group's escape probability by `2^g`.
-/

import LvmWhirGroupEscape

/-!
# The query group with a proof of work

With `g > 0` a WHIR level reads the nonce (a prover move, so the query group starts at the
boundary it ends) and then draws the PoW challenge `c`, rejecting unless its top `g` bits are zero
(`powOK g c`: `int(c) < 2^(192 − g)`). The PoW challenge, the positions, `λ` and the openings are
one group (no prover move between them), so the Fiat–Shamir compiler charges them as one event at
the nonce query (`LvmPotential`), and the group's escape is the joint one:

* `card_powOK`: exactly `2^(192 − g)` challenges pass (`int` is a bijection onto `[0, 2^192)`);
* `escRet_powCheck_le`: if the rest of the group escapes with probability at most `e` from every
  history with the same commitments, the group with the proof of work escapes with probability
  at most `2^-g · e` (the rest of the group does not read the PoW challenge);
* `escRet_queryFragG_le_ud`, `escRet_queryFragG_le_finViol`: the query groups of
  `LvmWhirGroupEscape` with the proof of work, at `2^-g · eQueryUd` and `2^-g · eQueryFinal`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier VerifierProgram Finset

section

/-- **The passing challenges**: `2^(192 − g)` of the `2^192`, for `g ≤ 192`. -/
theorem card_powOK (g : ℕ) (hg : g ≤ 192) :
    (univ.filter fun c : E ↦ powOK g c).card = 2 ^ (192 - g) := by
  have h1 : (univ.filter fun c : E ↦ powOK g c).card =
      (univ.filter fun x : Fin ((2 ^ 64) ^ 3) ↦ (x : ℕ) < 2 ^ (192 - g)).card := by
    rw [← Finset.card_map eNatEquiv.toEmbedding]
    congr 1
    ext x
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [powOK, ← eNatEquiv_val, Equiv.apply_symm_apply]
  rw [h1, Fin.card_filter_val_lt]
  refine min_eq_right ?_
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The fraction of passing challenges is `2^-g`. -/
theorem frac_powOK (g : ℕ) (hg : g ≤ 192) :
    (Fintype.card E : ENNReal)⁻¹ * ((univ.filter fun c : E ↦ powOK g c).card : ENNReal) =
      (2 : ENNReal)⁻¹ ^ g := by
  rw [card_powOK g hg, card_E]
  have h : (2 : ENNReal) ^ 192 = 2 ^ g * 2 ^ (192 - g) := by
    rw [← pow_add, Nat.add_sub_cancel' hg]
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, h, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

open Classical in
/-- **The proof of work divides a group's escape by `2^g`.** -/
theorem escRet_powCheck_le {α : Type} (g : ℕ) (hg : g ≤ 192) (Post : α → List Ev → Prop)
    (h₀ : List Ev) (q : VerifierProgram α) (e : ENNReal)
    (hq : ∀ h, commits h = commits h₀ → escRet Post h [] q ≤ e) :
    escRet Post h₀ [] ((powCheck g).bind fun _ ↦ q) ≤ (2 : ENNReal)⁻¹ ^ g * e := by
  by_cases g0 : g = 0
  · subst g0
    simpa [powCheck] using hq h₀ rfl
  simp only [powCheck, g0, ↓reduceIte]
  rw [VerifierProgram.bind_assoc]
  change retExp _ h₀ [] (VerifierProgram.sample fun c ↦
    ((VerifierProgram.require (powOK g c)).bind fun _ ↦ q)) ≤ _
  simp only [retExp, List.nil_append]
  have hc : ∀ c : E, retExp (fun a h ↦ if Post a h then 0 else 1) h₀ [Ev.sample c]
      ((VerifierProgram.require (powOK g c)).bind fun _ ↦ q) ≤ if powOK g c then e else 0 := by
    intro c
    by_cases hp : powOK g c
    · simp only [VerifierProgram.require, hp, ↓reduceIte, VerifierProgram.ret_bind]
      rw [show [Ev.sample c] = [Ev.sample c] ++ [] from rfl, retExp_shift]
      exact hq _ (commits_append_sample h₀ c)
    · simp [VerifierProgram.require, hp, VerifierProgram.bind, retExp]
  calc (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, _
      ≤ (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, (if powOK g c then e else 0) := by
        gcongr with c; exact hc c
    _ = (Fintype.card E : ENNReal)⁻¹ * ((univ.filter fun c : E ↦ powOK g c).card : ENNReal) * e := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_assoc]
    _ = (2 : ENNReal)⁻¹ ^ g * e := by rw [frac_powOK g hg]

/-! ## The query groups -/

/-- The query group with the proof of work. -/
def queryFragG (g per depth t i : ℕ) : VerifierProgram (List ℕ × E × List (List K)) :=
  (powCheck g).bind fun _ ↦ queryFrag per depth t i

theorem noMoves_powCheck (g : ℕ) : NoMoves (powCheck g) := by
  unfold powCheck
  split
  · exact NoMoves.ret ()
  · refine noMoves_sampleE.bind fun c ↦ ?_
    unfold VerifierProgram.require
    split
    · exact NoMoves.ret ()
    · exact NoMoves.fail

theorem noMoves_queryFragG (g per depth t i : ℕ) : NoMoves (queryFragG g per depth t i) :=
  (noMoves_powCheck g).bind fun _ ↦ noMoves_queryFrag per depth t i

open Classical in
/-- **The query group of a level with a next commitment, with the proof of work.** -/
theorem escRet_queryFragG_le_ud (g : ℕ) (hg : g ≤ 192) (P P' : LevelCode) {ℓ' : ℕ}
    (hκ : P.κ = ℓ' + P'.κ) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (Q' : (Fin ℓ' → Bool) → Fin P'.n → E) (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (hviol : Viol P (fun _ : Fin 0 → Bool ↦ C) Φ σ)
    (hone : (iList P'.code P'.thr Q').card ≤ 1)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      Viol P' Q' (fun r ↦ Φ r + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length) r)
        (σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k]) →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFragG g per (P.κ + P.R) t c) ≤
      (2 : ENNReal)⁻¹ ^ g * eQueryUd P P' t := by
  refine escRet_powCheck_le g hg _ h₀ _ _ fun h hh ↦ ?_
  rw [← hh] at hW
  refine escRet_queryFrag_le_ud P P' hκ per t c hper hpd h hW Q' C Φ σ hviol hone
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

open Classical in
/-- **The query group of the final level, with the proof of work.** -/
theorem escRet_queryFragG_le_finViol (g : ℕ) (hg : g ≤ 192) (P : LevelCode) (per t c : ℕ)
    (hper : 1 ≤ per) (hpd : per * (P.κ + P.R) ≤ 192)
    (h₀ : List Ev) {wd : ℕ} {W : Word} (hW : (commits h₀)[c]? = some (P.κ + P.R, wd, W))
    (C : Fin P.n → E) (Φ : List E → E) (σ : E)
    (G : (Fin P.κ → Bool) → E) (hD : FinViol P C Φ σ G)
    (J : List ℕ × E × List (List K) → List (ℕ × ℕ × Word) → Prop)
    (hJ : ∀ (qs : List ℕ) (lam : E), (∀ q ∈ qs, q < P.n) → qs.length = t →
      ∑ x, (Φ (bitsL x) + 1 * lam * Verifier.inducedWeight P.κ qs (powers lam qs.length)
          (bitsL x)) * G x ≠
        σ + 1 * lam * ∑ k : Fin qs.length, lam ^ (k : ℕ) * wordAt C qs[k] →
      J (qs, lam, qs.map W) (commits h₀)) :
    escRet (fun g h ↦ J g (commits h)) h₀ [] (queryFragG g per (P.κ + P.R) t c) ≤
      (2 : ENNReal)⁻¹ ^ g * eQueryFinal P t := by
  refine escRet_powCheck_le g hg _ h₀ _ _ fun h hh ↦ ?_
  rw [← hh] at hW
  refine escRet_queryFrag_le_finViol P per t c hper hpd h hW C Φ σ G hD
    (fun g cs ↦ J g cs) fun qs lam hr hlen hv ↦ ?_
  rw [hh]
  exact hJ qs lam hr hlen hv

/-! ## The moves before the proof of work, and the discount -/

/-- The discount `2^-g` only lowers an escape. -/
theorem grind_disc_le (g : ℕ) (x : ENNReal) : (2 : ENNReal)⁻¹ ^ g * x ≤ x :=
  mul_le_of_le_one_left' (pow_le_one₀ zero_le (by norm_num))

/-- **The separating challenge and the nonce keep a commitment invariant** (lead and follower's
allowance `T`; at `g = 0` there is nothing). -/
noncomputable def grindPreInv (I : CInv) (g : ℕ) {εmax T : ENNReal} (hT : T ≤ εmax) :
    Spec (grindPre g) (fun h ↦ I (commits h)) (fun _ h ↦ I (commits h)) εmax T T :=
  Spec.ite (fun _ ↦ (Spec.ret (Post := fun _ h ↦ I (commits h)) ()).congr
      (VerifierProgram.pure_eq ()).symm)
    (fun _ ↦ ((Spec.sampleE (Pre := fun h ↦ I (commits h)) (Post := fun _ h ↦ I (commits h))
        (T := 0) 0 fun h₀ hI ↦ by simp [hI]).bind' fun _ ↦
      (readInv I (T := T) hT).bind' fun _ ↦
        (Spec.ret (Post := fun _ h ↦ I (commits h)) ()).congr
          (VerifierProgram.pure_eq ()).symm).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl
          (by simp) le_rfl)

end
end LeanVM.Protocol.Whir.Sound
