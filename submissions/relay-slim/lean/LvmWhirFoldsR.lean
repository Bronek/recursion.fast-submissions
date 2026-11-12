-- New for lvm2 (WP JB-L, J2): the fold rounds, the end of the final level's fold rounds, the root and the batching
-- step with the relativised doom `ViolR` (twins of `LvmWhirFolds`, `LvmWhirLevelFinal.resC_of_afterFold`,
-- `LvmWhirStart.levelPre_zero` and `LvmWhirSpec.card_batch_bad_le`).
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the fold rounds with the relativised doom)
-/

import LvmWhirPathR
import LvmWhirFolds
import LvmWhirSpec

/-!
# The fold rounds, relativised

The twins of `FoldInv`, `FoldMid`, `foldRoundsSpec` (`LvmWhirFolds`) and `LevelPre`, `AfterFold`
(`LvmWhirDefs`, `LvmWhirLevelMid`) with the doom `ViolR P Gd s.folds …` (every member of the list
that is on no path of a good candidate violates the running claim) in place of `Viol`. The fold
step's count is `card_foldStep_bad_le`'s (`card_foldStep_bad_le_R`), so the escape is `eFold P ℓ`
as before.

* `goodRes_or_resC`: after the final level's fold rounds, **every residual of the right length is
  good (`GoodRes`) or in the residual's doom (`ResC`)**: if its encoding is in the folded word's
  list, it is tracked (and violates the claim) or on the path of a good candidate.
* `WhirPreR`, `StackedPreR`: the root's relation, only the candidates that are not good violate
  the claim(s); `levelPre_zeroR`: the starting doom `LevelPreR` for the good root set `gdRoot`
  (a root member is a candidate's encoding, on that candidate's path only).
* `card_batch_bad_le_R`: the batching step counts the non-good candidates only.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd VerifierProgram Finset

section

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (ℓ pre : ℕ) (Gd : Set (Column μ))

/-- **The fold invariant, relativised**, after the challenges `lf` of level `i`. -/
def FoldInvR (s : WhirStateT) (lf : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.folds.length = pre + lf.length ∧ lf.length ≤ ℓ ∧ P.κ + pre + ℓ = μ ∧ GluedOK μ s ∧
    QuadOK s.quad s.target ∧
    ViolR P Gd s.folds (rowsOf (ℓ - lf.length) (foldsN lf (laneO i cs P.n))) (runW w ℓ₀ s) s.target

/-- The relativised doom right after a fold challenge, before the next round polynomial. -/
def FoldMidR (s : WhirStateT) (lf : List E) (c : E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  s.folds.length = pre + lf.length ∧ lf.length < ℓ ∧ P.κ + pre + ℓ = μ ∧ GluedOK μ s ∧
    ViolR P Gd (s.folds ++ [c])
      (rowsOf (ℓ - (lf.length + 1)) (foldsN (lf ++ [c]) (laneO i cs P.n)))
      (fun r ↦ runW w ℓ₀ s (c :: r)) (polyEval s.quad c)

/-- **The relativised doom at the start of level `i`** and the commitments' shape. -/
def LevelPreR (s : WhirStateT) (cs : List (ℕ × ℕ × Word)) : Prop :=
  FoldInvR μ ℓ₀ w i P ℓ pre Gd s [] cs ∧ ShapeOK i P ℓ cs

/-- After the fold rounds: the relativised invariant with all `ℓ` challenges. -/
def AfterFoldR (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (FoldInvR μ ℓ₀ w i P ℓ pre Gd r.1 r.2 cs ∧ ShapeOK i P ℓ cs) ∧ r.2.length = ℓ

variable {μ ℓ₀ w i P ℓ pre Gd}

open Classical in
/-- One round's escape: at most `2·listMax + 2^(ℓ−1)·mcaMax` challenges break the invariant. -/
theorem card_foldBad_le_eFoldR (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (s : WhirStateT)
    (lf : List E) (hlf : lf.length < ℓ) (cs : List (ℕ × ℕ × Word))
    (hI : FoldInvR μ ℓ₀ w i P ℓ pre Gd s lf cs) :
    (univ.filter fun c ↦ ¬ FoldMidR μ ℓ₀ w i P ℓ pre Gd s lf c cs).card ≤
      2 * P.listMax + 2 ^ (ℓ - 1) * P.mcaMax := by
  obtain ⟨hlen, -, hκ, hg, ⟨c₀, c₁, c₂, hq, hσ⟩, hviol⟩ := hI
  set m := ℓ - (lf.length + 1) with hm
  have hm1 : ℓ - lf.length = m + 1 := by omega
  have hma : IsMultiaffine (m + 1 + P.κ) (runW w ℓ₀ s) := by
    have := isMultiaffine_runW hw hℓ₀ s (by omega) hg
    rwa [show μ - s.folds.length = m + 1 + P.κ by omega] at this
  rw [hm1] at hviol
  rw [hq] at hσ
  have hstep := card_foldStep_bad_le_R P Gd s.folds (runW w ℓ₀ s) hma
    (foldsN lf (laneO i cs P.n)) s.target c₀ c₁ c₂ hσ hviol
  refine (Finset.card_le_card fun c hc ↦ ?_).trans (hstep.trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, FoldMidR, not_and] at hc ⊢
    intro hv
    refine hc hlen hlf hκ hg ?_
    rw [hq]
    rwa [foldsN, List.foldl_append, List.foldl_cons, List.foldl_nil]
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
      (by omega))) _

open Classical in
/-- The escape count as the calculus averages it. -/
theorem avg_foldBad_leR (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (s : WhirStateT)
    (lf : List E) (hlf : lf.length < ℓ) (cs : List (ℕ × ℕ × Word))
    (hI : FoldInvR μ ℓ₀ w i P ℓ pre Gd s lf cs) :
    (Fintype.card E : ENNReal)⁻¹ *
      ((univ.filter fun c ↦ ¬ FoldMidR μ ℓ₀ w i P ℓ pre Gd s lf c cs).card : ENNReal) ≤
        eFold P ℓ := by
  rw [eFold, ENNReal.div_eq_inv_mul]
  gcongr
  exact_mod_cast card_foldBad_le_eFoldR hw hℓ₀ s lf hlf cs hI

/-- After the round polynomial: the relativised invariant with one more challenge. -/
theorem foldInvR_step (s : WhirStateT) (lf : List E) (c : E) (cs : List (ℕ × ℕ × Word))
    (quad : List E) (hmid : FoldMidR μ ℓ₀ w i P ℓ pre Gd s lf c cs)
    (hq : QuadOK quad (polyEval s.quad c)) :
    FoldInvR μ ℓ₀ w i P ℓ pre Gd
      { s with target := polyEval s.quad c, quad := quad, folds := s.folds ++ [c] }
      (lf ++ [c]) cs := by
  obtain ⟨hlen, hlf, hκ, hg, hviol⟩ := hmid
  refine ⟨by simp [hlen]; omega, by simp; omega, hκ, fun g hgm ↦ ?_, hq, ?_⟩
  · obtain ⟨h1, h2⟩ := hg g hgm
    exact ⟨by simp; omega, h2⟩
  · have hfun := funext (runW_fold w ℓ₀ s c (polyEval s.quad c) quad
      fun g hgm ↦ (hg g hgm).1)
    rw [hfun, List.length_append, List.length_singleton]
    exact hviol

variable (μ ℓ₀ w i P ℓ pre Gd)

/-- **The fold rounds' specification, relativised** (`foldRoundsSpec` with `FoldInvR`). -/
noncomputable def foldRoundsSpecR {εmax : ENNReal}
    (V : List (ℕ × ℕ × Word) → List (ℕ × ℕ × Word)) (X : CInv) (hw : IsMultiaffine μ w)
    (hℓ₀ : ℓ₀ ≤ μ) (hε : eFold P ℓ ≤ εmax) :
    (n : ℕ) → (s : WhirStateT) → (lf : List E) →
      Spec (foldRoundsT n s lf)
        (fun h ↦ (FoldInvR μ ℓ₀ w i P ℓ pre Gd s lf (V (commits h)) ∧ X (commits h)) ∧
          lf.length + n = ℓ)
        (fun r h ↦ (FoldInvR μ ℓ₀ w i P ℓ pre Gd r.1 r.2 (V (commits h)) ∧ X (commits h)) ∧
          r.2.length = ℓ)
        εmax (eFold P ℓ) 0
  | 0, s, lf => (Spec.ret (s, lf)).mono (fun _ h ↦ ⟨h.1, by simpa using h.2⟩)
      (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | n + 1, s, lf =>
    ((Spec.sampleE (Pre := fun h ↦ (FoldInvR μ ℓ₀ w i P ℓ pre Gd s lf (V (commits h)) ∧
          X (commits h)) ∧ lf.length + (n + 1) = ℓ)
        (Post := fun c h ↦ (FoldMidR μ ℓ₀ w i P ℓ pre Gd s lf c (V (commits h)) ∧
          X (commits h)) ∧ lf.length + (n + 1) = ℓ) (εmax := εmax) (T := 0) (eFold P ℓ)
        fun h₀ hp ↦ by
        refine le_trans ?_ (avg_foldBad_leR hw hℓ₀ s lf (by omega) (V (commits h₀)) hp.1.1)
        gcongr with c
        intro hm
        simp only [commits_sample]
        exact ⟨⟨hm, hp.1.2⟩, hp.2⟩).bind' fun c ↦
      (roundPolyInv (fun cs ↦ (FoldMidR μ ℓ₀ w i P ℓ pre Gd s lf c (V cs) ∧ X cs) ∧
          lf.length + (n + 1) = ℓ) (polyEval s.quad c) (T := eFold P ℓ) hε).bind' fun quad ↦
        (foldRoundsSpecR V X hw hℓ₀ hε n
          { s with target := polyEval s.quad c, quad := quad, folds := s.folds ++ [c] }
          (lf ++ [c])).mono
          (fun h hp ↦ ⟨⟨foldInvR_step s lf c (V (commits h)) quad hp.2.1.1 hp.1, hp.2.1.2⟩, by
            simp; omega⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

variable {μ ℓ₀ w i P ℓ pre Gd}

/-- **The end of the final level's fold rounds**: every residual of the right length is good
(its encoding is in the folded word's list and it is the path of a good candidate) or in the
residual's doom `ResC`. -/
theorem goodRes_or_resC {r : WhirStateT × List E} {res : List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs)
    (hres : res.length = 2 ^ (μ - r.1.folds.length)) :
    GoodRes P i Gd r res cs ∨ ResC μ ℓ₀ w i P ℓ pre r res cs := by
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, hviol⟩, hsh⟩, hlf⟩ := h
  rw [hlf, Nat.sub_self, rowsOf_zero] at hviol
  by_cases hmem : (fun _ : Fin 0 → Bool ↦ enc P.κ P.R (resMsg res)) ∈
      iList P.code P.thr (fun _ : Fin 0 → Bool ↦ foldedW i P r cs)
  · by_cases htr : Tracked Gd r.1.folds
        (decode P (fun _ : Fin 0 → Bool ↦ enc P.κ P.R (resMsg res)))
    · -- Tracked: it violates the running claim.
      refine Or.inr ⟨⟨hres, ⟨h1, h2, h3, h4, h5⟩, hsh, hlf⟩, Or.inl ?_⟩
      have := hviol _ hmem htr
      rwa [decode_enc P (fun _ ↦ resMsg res), claimSum_zero] at this
    · -- On the path of a good candidate.
      refine Or.inl ⟨hmem, ?_⟩
      simp only [Tracked, not_forall, not_not] at htr
      obtain ⟨q, hq, hp⟩ := htr
      rw [decode_enc P (fun _ ↦ resMsg res)] at hp
      exact ⟨q, hq, fun x ↦ by simpa using hp Fin.elim0 x⟩
  · exact Or.inr ⟨⟨hres, ⟨h1, h2, h3, h4, h5⟩, hsh, hlf⟩, Or.inr hmem⟩

end

/-! ## The root -/

/-- **The root's relation, relativised**: the shape of `WhirPreUd`, and every candidate of the
root's word that is not good violates the claim `(w, t)`. -/
def WhirPreR (cfg : UdConfig) (P₀ : LevelCode) (Good : Column cfg.μ → Prop) (w : List E → E)
    (t : E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  cfg.c₀ < cfg.n₀ ∧ cs.length = cfg.n₀ ∧
    (∃ W, cs[cfg.c₀]? = some (P₀.κ + P₀.R, 2 ^ laneBits, W) ∧ WellShaped (2 ^ laneBits) W) ∧
    ∀ q ∈ Candidates cfg.μ P₀.R P₀.thr (wordOf cs cfg.c₀), ¬ Good q →
      ¬ StackClaim.Holds cfg.μ (w, t) q

/-- **The stacked opening's relation, relativised**: the shape of `StackedPreUd`, and every
candidate of the root's word that is not good violates one of the claims. -/
def StackedPreR (cfg : UdConfig) (P₀ : LevelCode) (Good : Column cfg.μ → Prop)
    (claims : List StackClaim) (cs : List (ℕ × ℕ × Word)) : Prop :=
  cfg.c₀ < cfg.n₀ ∧ cs.length = cfg.n₀ ∧
    (∃ W, cs[cfg.c₀]? = some (P₀.κ + P₀.R, 2 ^ laneBits, W) ∧ WellShaped (2 ^ laneBits) W) ∧
    ∀ q ∈ Candidates cfg.μ P₀.R P₀.thr (wordOf cs cfg.c₀), ¬ Good q →
      ∃ c ∈ claims, ¬ StackClaim.Holds cfg.μ c q

/-- **The starting doom, relativised**: from `WhirPreR` and the first round polynomial,
`LevelPreR` of level `0` on the opening's view for the good root set (a member of the root's list
is the encoding of a candidate, on no path but its own). -/
theorem levelPre_zeroR {cfg : UdConfig} (P₀ : LevelCode) (hκ : P₀.κ = cfg.μ - laneBits)
    (hμ : laneBits ≤ cfg.μ) (Good : Column cfg.μ → Prop) (w : List E → E) (t : E)
    (quad : List E) (cs : List (ℕ × ℕ × Word)) (hpre : WhirPreR cfg P₀ Good w t cs)
    (hq : QuadOK quad t) :
    LevelPreR cfg.μ laneBits w 0 P₀ laneBits 0 (gdRoot P₀ Good (viewC cfg.c₀ cfg.n₀ cs))
      ⟨t, quad, [], []⟩ (viewC cfg.c₀ cfg.n₀ cs) := by
  obtain ⟨hc, hlen, hW, hcand⟩ := hpre
  obtain ⟨hsh, hwo⟩ := shapeOK_viewC_start hc hlen hW
  refine ⟨⟨by simp, by simp, by omega, by simp [GluedOK], hq, ?_⟩, hsh⟩
  rw [← hwo] at hcand
  generalize viewC cfg.c₀ cfg.n₀ cs = cs' at hcand ⊢
  rcases P₀ with ⟨κ, R', h64, hκ1, hR1, thr, lM, mM, facts⟩
  simp only at hκ
  subst hκ
  intro V hV htr
  simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil] at hV
  have hV' : V ∈ iList (rsCode (domain (cfg.μ - laneBits) R' h64) (2 ^ (cfg.μ - laneBits)))
      (LevelCode.thr ⟨cfg.μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩)
      (rowsOf laneBits (laneO 0 cs' (2 ^ (cfg.μ - laneBits + R')))) := hV
  rw [rowsOf_laneO_zero, mem_iList_comp _ _ (bitsEquiv laneBits)] at hV'
  clear hV
  have hV := hV'
  simp only [Equiv.apply_symm_apply] at hV
  obtain ⟨q, hqc, hVq⟩ := exists_candidate_of_mem_iList hμ h64
    (LevelCode.two_pow_le_thr ⟨cfg.μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩) hV
  have hVe : V = fun u ↦ enc (cfg.μ - laneBits) R' (blockOf q (bitsEquiv laneBits u)) := by
    funext u
    have := congrFun hVq (bitsEquiv laneBits u)
    simpa [encStack] using this
  have hdec : decode ⟨cfg.μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩ V =
      fun u ↦ blockOf q (bitsEquiv laneBits u) := by
    rw [hVe]
    exact decode_enc ⟨cfg.μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩ _
  have hrun : runW w laneBits ⟨t, quad, [], []⟩ = fun r ↦ w (rotL laneBits r) := by
    funext r
    simp [runW]
  -- The member is `q`'s encoding, on `q`'s path only: `q` is not good.
  have hgood : ¬ Good q := fun hg ↦ htr q ⟨hqc, hg⟩ (by
    rw [hdec]
    exact (pathAt_rootMsg_iff hμ q q).mpr rfl)
  rw [hdec, hrun, claimSum_encStack hμ]
  exact hcand q hqc hgood

open Classical in
/-- **The batching step, relativised**: at most `(J − 1)·listMax₀` challenges `ρ` let a candidate
that is not good satisfy the batched claim when every such candidate violates one of the claims. -/
theorem card_batch_bad_le_R {μ R : ℕ} (P₀ : LevelCode) (hκ : P₀.κ = μ - laneBits)
    (hR : P₀.R = R) (hμ : laneBits ≤ μ) (Good : Column μ → Prop) (claims : List StackClaim)
    (W₀ : Word)
    (hviol : ∀ q ∈ Candidates μ R P₀.thr W₀, ¬ Good q → ∃ c ∈ claims, ¬ StackClaim.Holds μ c q) :
    (univ.filter fun ρ : E ↦ ∃ q ∈ Candidates μ R P₀.thr W₀, ¬ Good q ∧
        StackClaim.Holds μ (fun point ↦ dot (powers ρ claims.length)
          (claims.map fun c ↦ c.1 point), dot (powers ρ claims.length) (claims.map (·.2))) q).card ≤
      P₀.listMax * (claims.length - 1) := by
  rcases P₀ with ⟨κ, R', h64, hκ1, hR1, thr, lM, mM, facts⟩
  simp only at hκ hR
  subst hκ hR
  set P₀ : LevelCode := ⟨μ - laneBits, R', h64, hκ1, hR1, thr, lM, mM, facts⟩
  set L := iList (rsCode (domain (μ - laneBits) R' h64) (2 ^ (μ - laneBits))) P₀.thr
    (laneWord μ R' W₀)
  -- The discrepancy of a candidate.
  let d : Column μ → Fin claims.length → E := fun q k ↦
    (∑ j : Fin (2 ^ μ), claims[k].1 (boolPoint μ j) * ofK (q.values.getD j 0)) - claims[k].2
  have hhold : ∀ ρ q, StackClaim.Holds μ (fun point ↦ dot (powers ρ claims.length)
      (claims.map fun c ↦ c.1 point), dot (powers ρ claims.length) (claims.map (·.2))) q ↔
      ∑ k : Fin claims.length, d q k * ρ ^ (k : ℕ) = 0 := by
    intro ρ q
    simp only [StackClaim.Holds, dot_powers_map]
    exact batch_iff (fun k j ↦ claims[k].1 (boolPoint μ j)) (fun j ↦ ofK (q.values.getD j 0))
      (fun k ↦ claims[k].2) ρ
  refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans ((card_filter_exists_le L (fun
      (V : Fin (2 ^ laneBits) → Fin (2 ^ (μ - laneBits + R')) → E) (ρ : E) ↦
      ∃ q ∈ Candidates μ R' P₀.thr W₀, ¬ Good q ∧ encStack μ R' q = V ∧
        ∑ k : Fin claims.length, d q k * ρ ^ (k : ℕ) = 0) (N := claims.length - 1)
      fun V _ ↦ ?_).trans ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    obtain ⟨q, hq, hng, hh⟩ := hρ
    exact ⟨encStack μ R' q, mem_iList_of_candidate h64 hq, q, hq, hng, rfl, (hhold ρ q).mp hh⟩
  · by_cases hex : ∃ q ∈ Candidates μ R' P₀.thr W₀, ¬ Good q ∧ encStack μ R' q = V
    · obtain ⟨q₀, hq₀, hng₀, rfl⟩ := hex
      obtain ⟨c, hc, hnot⟩ := hviol q₀ hq₀ hng₀
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
      have hd : ∃ k, d q₀ k ≠ 0 := ⟨⟨k, hk⟩, by
        simp only [d, sub_ne_zero]
        exact hnot⟩
      refine (Finset.card_le_card fun ρ hρ ↦ ?_).trans (card_powerBatch_eq_zero_le (d q₀) hd)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
      obtain ⟨q, -, -, hqV, hz⟩ := hρ
      rwa [encStack_injective hμ h64 hqV] at hz
    · refine le_trans (Finset.card_le_card (t := ∅) fun ρ hρ ↦ ?_) (by simp)
      rw [Finset.mem_filter] at hρ
      obtain ⟨q, hq, hng, hqV, -⟩ := hρ.2
      exact absurd ⟨q, hq, hng, hqV⟩ hex
  · exact Nat.mul_le_mul_right _ (P₀.card_iList_le _)

end LeanVM.Protocol.Whir.Sound
