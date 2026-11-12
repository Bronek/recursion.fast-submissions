-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/LJFold.lean` @ 1b74a2a2 (archive/pcs/S1P) (Flock LJ1/LJ2, on the
-- longfellow port `LvmJB*`, Apache License 2.0, see `LICENSE-longfellow`). Changed: imports `JB*`/`LJ*`
-- renamed `LvmJB*`/`LvmLJ*`; nothing else.
-- LJ1: SJ §5.1 (L2) `explBy_step` (the nesting step of the fold), statement verbatim from SJStmts.lean.
import LvmLJDefs

open Polynomial Finset JBAgreement

namespace LJ

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Row `i` of `2^(l+1)` rows sits in pair `i / 2`. -/
def half {l : ℕ} (i : Fin (2 ^ (l + 1))) : Fin (2 ^ l) :=
  ⟨i.val / 2, by have := i.isLt; have h2 : 2 ^ (l + 1) = 2 ^ l * 2 := pow_succ 2 l; omega⟩

/-- Interleave two row tuples: row `2r` is `A r`, row `2r+1` is `B r`. -/
def interleave {l : ℕ} {α : Type*} (A B : Fin (2 ^ l) → α) : Fin (2 ^ (l + 1)) → α :=
  fun i => if i.val % 2 = 0 then A (half i) else B (half i)

theorem evens_interleave {l : ℕ} {α : Type*} (A B : Fin (2 ^ l) → α) : evens (interleave A B) = A := by
  funext r
  have h1 : (2 * r.val) % 2 = 0 := by omega
  have h2 : half (l := l) ⟨2 * r.val, by have := two_mul_lt r; omega⟩ = r := Fin.ext (by simp [half])
  simp only [evens, interleave, h1, ite_true, h2]

theorem odds_interleave {l : ℕ} {α : Type*} (A B : Fin (2 ^ l) → α) : odds (interleave A B) = B := by
  funext r
  have h1 : ¬ (2 * r.val + 1) % 2 = 0 := by omega
  have h2 : half (l := l) ⟨2 * r.val + 1, two_mul_lt r⟩ = r := Fin.ext (by simp [half]; omega)
  simp only [odds, interleave, h1, ite_false, h2]

/-- Every row of `2^(l+1)` rows is an even or an odd row. -/
theorem row_cases {l : ℕ} {α : Type*} (W : Fin (2 ^ (l + 1)) → α) (i : Fin (2 ^ (l + 1))) :
    W i = evens W (half i) ∨ W i = odds W (half i) := by
  rcases Nat.mod_two_eq_zero_or_one i.val with h | h
  · left; simp only [evens, half]; congr 1; ext; simp; omega
  · right; simp only [odds, half]; congr 1; ext; simp; omega

/-- **(L2) The nesting step**: off the JB bad set of the line `(evens W, odds W − evens W)`, explanation
survives one fold round. With `explBy_refl`, four steps give `Expl_i(4)` with per-round bad sets of size
`< johnsonThreshold`, each fixed before its challenge. -/
theorem explBy_step {a l : ℕ} (dom : ι → K) (U : Fin a → ι → K) (W : Fin (2 ^ (l + 1)) → ι → K)
    (fold : (Fin a → K[X]) → (Fin (2 ^ (l + 1)) → K[X])) (k e : ℕ)
    (hE : ExplBy dom U W fold k e) (z : K)
    (hz : ¬ iHasUnexplainedProximate dom (evens W) (fun r x => odds W r x - evens W r x) k e z) :
    ExplBy dom U (foldRows z W) (fun V => foldPolys z (fold V)) k e := by
  intro P hP hclose
  -- `hz`: the proximate `P` of the line point is explained by a pair `(P₀, P₁)`
  obtain ⟨P₀, P₁, hP₀, hP₁, hexp⟩ : ∃ P₀ P₁ : Fin (2 ^ l) → K[X], (∀ r, (P₀ r).natDegree < k) ∧
      (∀ r, (P₁ r).natDegree < k) ∧
      iExplains dom (evens W) (fun r x => odds W r x - evens W r x) z P P₀ P₁ := by
    by_contra hno
    push Not at hno
    exact hz ⟨P, hP, hclose, fun P₀ P₁ h₀ h₁ => hno P₀ P₁ h₀ h₁⟩
  -- the unfolded pair: `Q (2r) = P₀ r`, `Q (2r+1) = P₀ r + P₁ r`
  set Q : Fin (2 ^ (l + 1)) → K[X] := interleave P₀ (fun r => P₀ r + P₁ r) with hQ
  have hQe : evens Q = P₀ := evens_interleave _ _
  have hQo : odds Q = fun r => P₀ r + P₁ r := odds_interleave _ _
  have hQdeg : ∀ i, (Q i).natDegree < k := by
    intro i
    rcases row_cases Q i with h | h <;> rw [h]
    · rw [hQe]; exact hP₀ _
    · rw [hQo]; exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt (hP₀ _) (hP₁ _))
  have hsub : colDisagree W (evalRows dom Q) ⊆ colDisagree (foldRows z W) (evalRows dom P) := by
    intro x hx
    by_contra hx'
    rw [mem_colDisagree] at hx hx'
    push Not at hx'
    have hagr := hexp.2 x hx'
    obtain ⟨i, hi⟩ := hx
    apply hi
    simp only [evalRows]
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h
    · have hW : W i = evens W (half i) := by
        simp only [evens, half]; congr 1; ext; simp; omega
      have hQi : Q i = P₀ (half i) := by simp only [hQ, interleave, h, ite_true]
      rw [hW, hQi, (hagr (half i)).1]
    · have hW : W i = odds W (half i) := by
        simp only [odds, half]; congr 1; ext; simp; omega
      have hne : ¬ i.val % 2 = 0 := by omega
      have hQi : Q i = P₀ (half i) + P₁ (half i) := by simp only [hQ, interleave, hne, ite_false]
      have h₀ := (hagr (half i)).1
      have h₁ := (hagr (half i)).2
      simp only at h₁
      rw [hW, hQi, eval_add, ← h₀, ← h₁]
      ring
  obtain ⟨V, hVdeg, hVfold, hVsub⟩ := hE Q hQdeg ((card_le_card hsub).trans hclose)
  refine ⟨V, hVdeg, ?_, hVsub.trans hsub⟩
  funext r
  simp only [foldPolys, hVfold, hQe, hQo, hexp.1 r]
  ring

end LJ
