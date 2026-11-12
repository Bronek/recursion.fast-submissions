-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/LJOod.lean` @ 1b74a2a2 (archive/pcs/S1P) (Flock LJ1/LJ2, on the
-- longfellow port `LvmJB*`, Apache License 2.0, see `LICENSE-longfellow`). Changed: imports `JB*`/`LJ*`
-- renamed `LvmJB*`/`LvmLJ*`; nothing else.
-- LJ1: SJ §5.1 (L3b) `ood_sep` and (L3c) `gamma_bad`, statements verbatim from SJStmts.lean.
import LvmLJDefs

open Polynomial Finset JBAgreement

namespace LJ

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The roots of a non-zero polynomial of degree `< D`, as a filter of `K`: at most `D - 1`. -/
theorem card_filter_eval_eq_zero_le {p : K[X]} (hp : p ≠ 0) {D : ℕ} (hD : p.natDegree < D) :
    (univ.filter fun ζ : K => p.eval ζ = 0).card ≤ D - 1 := by
  have h := Polynomial.card_le_degree_of_subset_roots (p := p)
    (Z := univ.filter fun ζ : K => p.eval ζ = 0) (by
      intro ζ hζ
      have hζ' : ζ ∈ univ.filter fun ζ : K => p.eval ζ = 0 := hζ
      simp only [mem_filter, mem_univ, true_and] at hζ'
      exact (Polynomial.mem_roots hp).2 hζ')
  omega

/-- **(L3b) OOD separation**: a random `ζ` separates a list of `≤ L` messages in a basis of degree `< D`
except on `C(L,2)·(D − 1)` values. -/
theorem ood_sep {N D L : ℕ} (S : Finset (Fin N → K)) (hS : S.card ≤ L) (B : Fin N → K[X])
    (hB : LinearIndependent K B) (hdeg : ∀ j, (B j).natDegree < D) :
    (univ.filter fun ζ : K => ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      ∑ j, a j * (B j).eval ζ = ∑ j, b j * (B j).eval ζ).card ≤ L.choose 2 * (D - 1) := by
  -- the difference polynomial of a pair
  let dP : (Fin N → K) → (Fin N → K) → K[X] := fun a b => ∑ j, (a j - b j) • B j
  have hdP_eval : ∀ a b ζ, (dP a b).eval ζ = ∑ j, a j * (B j).eval ζ - ∑ j, b j * (B j).eval ζ := by
    intro a b ζ
    simp only [dP, eval_finsetSum, eval_smul, smul_eq_mul, ← sum_sub_distrib, sub_mul]
  have hdP_ne : ∀ a b, a ≠ b → dP a b ≠ 0 := by
    intro a b hab h0
    apply hab
    funext j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hB (fun j => a j - b j) h0 j)
  have hdP_deg : ∀ a b, a ≠ b → (dP a b).natDegree < D := by
    intro a b hab
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; exact absurd (Subsingleton.elim a b) hab
      · exact h
    have hD : 0 < D := lt_of_le_of_lt (Nat.zero_le _) (hdeg ⟨0, hN⟩)
    have : (dP a b).natDegree ≤ D - 1 :=
      natDegree_sum_le_of_forall_le _ _ fun j _ =>
        (natDegree_smul_le _ _).trans (by have := hdeg j; omega)
    omega
  -- one root set per unordered pair
  let R : Finset (Fin N → K) → Finset K := fun t =>
    univ.filter fun ζ : K => ∃ a ∈ t, ∃ b ∈ t, a ≠ b ∧
      ∑ j, a j * (B j).eval ζ = ∑ j, b j * (B j).eval ζ
  have hR : ∀ t ∈ S.powersetCard 2, (R t).card ≤ D - 1 := by
    intro t ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 ht).2
    refine le_trans (card_le_card ?_) (card_filter_eval_eq_zero_le (hdP_ne a b hab) (hdP_deg a b hab))
    intro ζ hζ
    simp only [R, mem_filter, mem_univ, true_and, mem_insert, mem_singleton] at hζ ⊢
    rw [hdP_eval, sub_eq_zero]
    obtain ⟨a', ha', b', hb', hne, heq⟩ := hζ
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact heq
    · exact heq.symm
    · exact absurd rfl hne
  have hsub : (univ.filter fun ζ : K => ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      ∑ j, a j * (B j).eval ζ = ∑ j, b j * (B j).eval ζ) ⊆ (S.powersetCard 2).biUnion R := by
    intro ζ hζ
    simp only [mem_filter, mem_univ, true_and] at hζ
    obtain ⟨a, ha, b, hb, hab, heq⟩ := hζ
    refine mem_biUnion.2 ⟨{a, b}, mem_powersetCard.2 ⟨?_, card_pair hab⟩, ?_⟩
    · intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    · simp only [R, mem_filter, mem_univ, true_and]
      exact ⟨a, by simp, b, by simp, hab, heq⟩
  calc _ ≤ ((S.powersetCard 2).biUnion R).card := card_le_card hsub
    _ ≤ ∑ t ∈ S.powersetCard 2, (R t).card := card_biUnion_le
    _ ≤ ∑ _t ∈ S.powersetCard 2, (D - 1) := sum_le_sum hR
    _ = S.card.choose 2 * (D - 1) := by rw [sum_const, card_powersetCard, smul_eq_mul]
    _ ≤ L.choose 2 * (D - 1) := Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hS)

/-- **(L3c) The `γ` row**: each non-pinned element (non-zero OOD defect `d V`) has one bad `γ`. -/
theorem gamma_bad {α : Type*} (S : Finset α) (c d : α → K) (hd : ∀ V ∈ S, d V ≠ 0) :
    (univ.filter fun γ : K => ∃ V ∈ S, c V + γ * d V = 0).card ≤ S.card := by
  classical
  refine le_trans (card_le_card (t := S.image fun V => -c V / d V) ?_) card_image_le
  intro γ hγ
  simp only [mem_filter, mem_univ, true_and] at hγ
  obtain ⟨V, hV, h0⟩ := hγ
  refine mem_image.2 ⟨V, hV, ?_⟩
  field_simp [hd V hV]
  linear_combination -h0

end LJ
