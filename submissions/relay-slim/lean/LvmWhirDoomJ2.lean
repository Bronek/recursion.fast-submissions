-- New for lvm2 (WP J2P-L, roll 5): the extractor's facts for J2′'s two-level `C_rec` at the Johnson radius:
-- the list version of X-REC2's `ud_extract2` (lvm2/XREC2 `LvmWhirDoom2`), fed by JB-L's `GoodRes`; luck over the
-- list per round; the cert's candidate-pair count.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: J2′ extraction)
-/

import LvmWhirParamsJp
import LvmWhirDoomJ

/-!
# J2′: from `GoodRes` to the two-level decoder's facts

X-REC2's two-level extractor decodes level 1 first (the level-1 member `V` on the agreement set of
the level-1 rows folded by `α₁` with `Enc₁(f₂)`), then level 0 as v1 with `f₁ := joinMsg (decode V)`.
In unique decoding (`ud_extract2`) it gets `V`, `q` and their relations from uniqueness. At the Johnson
radius they come from the good branch of the relativised opening (`PostR`, JB-L):

* `GoodRes` + the final good set `gdFinal` give a good root candidate `q`, a member `V` of the level-1
  list on `q`'s path after `α₀` (`ConsAt`), and the residual `f₂` = `q`'s path after `α₀ ++ α₁`.
* `pathAt_zero_iff_foldMsg`: a level-0-folded message is on `q`'s path after `α₀` iff it is `q`'s
  level-0 fold `foldMsg α₀ q` (the multilinear extension at `α₀` on the lane variables).
* `sum_eqW_path`: folding a path by `α₁` is the path after `α₀ ++ α₁`.
* **`j_extract2`**: from those, exactly `ud_extract2`'s conclusions about `q` and `V` (the relations
  `joinMsg (decode V) = foldMsg α₀ q`, `f₂ = Σ_u eq(α₁, u)·decode V u`, the thresholds and the
  agreement-set equalities off each level's luck), without uniqueness.
* **Luck over the list**: `foldAllLuckL_cons` splits it by rounds (the folded list contains the
  folds of the list); per round `card_foldLuckL_le` (`L·n`); `luckL_rec20Jp`: J2′'s total
  `(6·304·2^15 + 4·311·2^12)/|E| ≤ 2^-165`.
* `candPairsJ_ncard_le`: the cert's candidate pairs (`C_main` J1's root at `codesMain24J`, `C_rec` J2′'s
  at `codesRec20Jp`) are at most `98 · 304` (`kgSpec`'s `L₀`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset

section

/-! ## Paths and folds -/

/-- **Folding a path by `α₁` is the path after `α₀ ++ α₁`.** -/
theorem sum_eqW_path {μ ℓ κ : ℕ} (q : Column μ) (fs : List E) (α₁ : Fin ℓ → E)
    (g : (Fin ℓ → Bool) → (Fin κ → Bool) → E) (hg : PathAt q fs g) (x : Fin κ → Bool) :
    (∑ u, eqW α₁ u • g u) x = qMle q (fs ++ List.ofFn α₁ ++ bitsL x) := by
  induction ℓ generalizing fs with
  | zero =>
    rw [Finset.sum_apply, Fintype.sum_unique]
    simp only [eqW, Finset.univ_eq_empty, Finset.prod_empty, one_smul, List.ofFn_zero,
      List.append_nil]
    rw [hg, bitsL_zero, List.append_nil]
  | succ m ih =>
    have hfold := ih (fs ++ [α₁ 0]) (Fin.tail α₁) (foldRows (α₁ 0) g) (pathAt_fold hg (α₁ 0))
    have hl : fs ++ List.ofFn α₁ ++ bitsL x = fs ++ [α₁ 0] ++ List.ofFn (Fin.tail α₁) ++ bitsL x := by
      simp only [List.ofFn_succ, List.append_assoc, List.cons_append]
      rfl
    rw [hl, ← hfold, Finset.sum_apply, Finset.sum_apply, sum_cube_succ]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul, foldRows, eqW, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.tail, ite_true, Bool.false_eq_true, ite_false]
    ring

/-- **A level-0-folded message is on `q`'s path after `α₀` iff it is `q`'s level-0 fold.** -/
theorem pathAt_zero_iff_foldMsg {μ : ℕ} (q : Column μ) (α₀ : Fin laneBits → E)
    (g : (Fin 0 → Bool) → (Fin (μ - laneBits) → Bool) → E) :
    PathAt q (List.ofFn α₀) g ↔ g Fin.elim0 = foldMsg α₀ q := by
  have hroot : PathAt q [] (rootMsg q) := fun u x ↦ by rw [List.nil_append, qMle_bitsL]
  have hfm : ∀ x, foldMsg α₀ q x = qMle q (List.ofFn α₀ ++ bitsL x) := fun x ↦ by
    have := sum_eqW_path q [] α₀ (rootMsg q) hroot x
    rw [List.nil_append] at this
    exact this
  constructor
  · intro h
    funext x
    rw [hfm, h Fin.elim0 x, bitsL_zero, List.append_nil]
  · intro h u x
    rw [Subsingleton.elim u Fin.elim0, h, hfm, bitsL_zero, List.append_nil]

/-! ## The extractor's facts -/

/-- **The extractor's facts at J2′** (the list version of `ud_extract2`): a good candidate `q` of the
root, a member `V` of the level-1 list on `q`'s path after `α₀`, and the residual `f₂` on `q`'s path
after `α₀ ++ α₁` give `ud_extract2`'s relations for `q` and `V`. -/
theorem j_extract2 {μ R A ℓ₁ : ℕ} (h64 : μ - laneBits + R ≤ 64) (P₁ : LevelCode)
    (hκ : μ - laneBits = ℓ₁ + P₁.κ) (Good : Column μ → Prop) (W₀ : Word) (α₀ : Fin laneBits → E)
    (Q' : (Fin ℓ₁ → Bool) → Fin P₁.n → E) (α₁ : Fin ℓ₁ → E) (f₂ : (Fin P₁.κ → Bool) → E)
    (q : Column μ) (hq : q ∈ Candidates μ R A W₀) (hgood : Good q)
    (V : (Fin ℓ₁ → Bool) → Fin P₁.n → E) (hV : V ∈ iList P₁.code P₁.thr Q')
    (hpath : PathAt q (List.ofFn α₀) (decode P₁ V))
    (hf : ∀ x, f₂ x = qMle q (List.ofFn α₀ ++ List.ofFn α₁ ++ bitsL x)) :
    Good q ∧ joinMsg hκ (decode P₁ V) = foldMsg α₀ q ∧
      f₂ = ∑ u, eqW α₁ u • decode P₁ V u ∧
      P₁.thr ≤ (agreeSet Q' V).card ∧
      (¬ FoldAllLuck α₁ Q' V →
        agreeSet (foldAll α₁ Q') (fun _ ↦ enc P₁.κ P₁.R f₂) = agreeSet Q' V) ∧
      A ≤ (agreeSet (laneRows μ R W₀) (encRows μ R q)).card ∧
      (¬ FoldAllLuck α₀ (laneRows μ R W₀) (encRows μ R q) →
        agreeSet (foldAll α₀ (laneRows μ R W₀))
            (fun _ ↦ enc (μ - laneBits) R (foldMsg α₀ q)) =
          agreeSet (laneRows μ R W₀) (encRows μ R q)) := by
  classical
  have hcw : IsInterleavedCodeword P₁.code V := ((mem_iList _ _ _ _).mp hV).1
  have hjoin : joinMsg hκ (decode P₁ V) = foldMsg α₀ q :=
    (pathAt_zero_iff_foldMsg q α₀ _).mp ((pathAt_joinMsg_iff hκ q _ _).mpr hpath)
  have hf₂ : f₂ = ∑ u, eqW α₁ u • decode P₁ V u := by
    funext x
    rw [hf x, sum_eqW_path q _ α₁ _ hpath x]
  set C := rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
  have hmem : encRows μ R q ∈ iList C A (laneRows μ R W₀) := by
    rw [encRows_eq]; exact comp_mem_iList C (bitsEquiv laneBits) (mem_iList_of_candidate h64 hq)
  have hencV : (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R f₂) = foldAll α₁ V := by
    have hV' : foldAll α₁ V = foldAll α₁ (fun u ↦ enc P₁.κ P₁.R (decode P₁ V u)) :=
      congrArg (foldAll α₁) (funext fun u ↦ (enc_decode P₁ hcw u).symm)
    rw [hV', foldAll_enc, hf₂]
  have heq : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R (foldMsg α₀ q)) =
      foldAll α₀ (encRows μ R q) := (foldAll_encRows α₀ q).symm
  refine ⟨hgood, hjoin, hf₂,
    (isClose_iff_le_card_agreeSet _ _ _).mp ((mem_iList _ _ _ _).mp hV).2, fun hluck ↦ ?_,
    (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2, fun hluck ↦ ?_⟩
  · rw [hencV]
    exact agreeSet_foldAll_eq (not_not.mp hluck)
  · rw [heq]
    exact agreeSet_foldAll_eq (not_not.mp hluck)

/-! ## Luck over the list -/

/-- **Luck over the list splits by rounds**: lucky for `cons s α` is a first round's luck of some
member, or the rest's luck over the folded list. -/
theorem foldAllLuckL_cons {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Submodule E (ι → E))
    (A : ℕ) {m : ℕ} (s : E) (α : Fin m → E) (O : (Fin (m + 1) → Bool) → ι → E)
    (h : FoldAllLuckL C A (Fin.cons s α : Fin (m + 1) → E) O) :
    (∃ U ∈ iList C A (splitLow O),
        ¬ agreeSet (fold s (splitLow O)) (fold s U) ⊆ agreeSet (splitLow O) U) ∨
      FoldAllLuckL C A α (fold s (splitLow O)) := by
  obtain ⟨U, hU, hl⟩ := h
  have hU' : splitLow U ∈ iList C A (splitLow O) := by
    rw [iList_splitLow]; exact Finset.mem_image_of_mem _ hU
  rcases foldAllLuck_cons s α O U hl with h1 | h2
  · exact Or.inl ⟨splitLow U, hU', h1⟩
  · exact Or.inr ⟨fold s (splitLow U), fold_mem_iList C hU' s, h2⟩

/-- **J2′'s luck in total** (P20): 6 rounds over the root's list (`L₀ = 304`, `n₀ = 2^15`) and 4 over
level 1's (`L₁ = 311`, `n₁ = 2^12`): `≤ 2^-165`. -/
theorem luckL_rec20Jp :
    ((6 * 304 * 2 ^ 15 + 4 * 311 * 2 ^ 12 : ℕ) : ENNReal) / Fintype.card E ≤ (2 : ENNReal)⁻¹ ^ 165 := by
  rw [card_E_ennreal, ← two_pow_cast]
  exact natCast_div_le_inv_pow (by positivity) (by norm_num)

/-! ## The cert's candidate pairs -/

/-- **The candidate pairs** of `C_main` (J1's code) and `C_rec` (J2′'s) are at most `98 · 304`. -/
theorem candPairsJ_ncard_le (W₁ W₂ : Word) :
    ({p : Column 24 × Column 19 | p.1 ∈ Candidates 24 1 (codesMain24J 0).thr W₁ ∧
        p.2 ∈ Candidates 19 2 (codesRec20Jp 0).thr W₂}).ncard ≤ 98 * 304 := by
  change (Candidates 24 1 (codesMain24J 0).thr W₁ ×ˢ
    Candidates 19 2 (codesRec20Jp 0).thr W₂).ncard ≤ 98 * 304
  rw [Set.ncard_prod]
  exact Nat.mul_le_mul (candidates_main24J_ncard_le W₁) (candidates_rec20Jp_ncard_le W₂)

end
end LeanVM.Protocol.Whir.Sound
