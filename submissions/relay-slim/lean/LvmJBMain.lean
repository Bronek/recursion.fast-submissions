-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBMain.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBCounting
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Correlated agreement, given the branch

This file bridges the abstract counting result `card_pairDisagree_le` to the
Reed-Solomon statement: once the branch argument has produced a single affine family
`v₀ + Z v₁` explaining the proximates of many parameters `z`, ordinary correlated
agreement follows.

The remaining input — that such a `v₀, v₁` exist — is exactly what §1-§3 supply, and
is stated here as a hypothesis (`hbranch`) rather than proved.
-/

namespace JBAgreement

open Finset Polynomial

variable {F : Type*} [Field F]
variable {ι : Type*}

/-- Evaluation of a polynomial on the evaluation domain: a Reed-Solomon codeword. -/
def RSeval (dom : ι → F) (p : F[X]) : ι → F := fun x => p.eval (dom x)

@[simp] lemma RSeval_apply (dom : ι → F) (p : F[X]) (x : ι) :
    RSeval dom p x = p.eval (dom x) := rfl

/-- The line point `v₀ + z • v₁` evaluated on the domain splits as expected. -/
lemma RSeval_line (dom : ι → F) (v₀ v₁ : F[X]) (z : F) (x : ι) :
    (v₀ + C z * v₁).eval (dom x) = RSeval dom v₀ x + z * RSeval dom v₁ x := by
  simp [RSeval]

variable [DecidableEq F] [Fintype ι] [DecidableEq ι]

/-- **Correlated agreement, given the branch.**

Suppose the branch argument has produced polynomials `v₀, v₁` such that for every
parameter `z` in a set `S` of size greater than `e + 1`, the line point `u₀ + z • u₁`
differs from the codeword `(v₀ + z • v₁)` evaluated on the domain in at most `e`
coordinates.  Then the *pair* `(u₀, u₁)` already differs from `(v₀, v₁)` on the domain
in at most `e` coordinates: the agreement is correlated. -/
theorem correlatedAgreement_of_branch
    (dom : ι → F) (u₀ u₁ : ι → F) (v₀ v₁ : F[X]) (e : ℕ) (S : Finset F)
    (hS : e + 1 < S.card)
    (hagree : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x)
                (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) :
    (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e := by
  refine card_pairDisagree_le (e := e) (S := S) ?_ hS
  intro z hz
  have := hagree z hz
  simpa only [RSeval_line dom v₀ v₁] using this

/-- The correlated agreement *set* is large: at least `n - e` coordinates carry
simultaneous agreement of `u₀` with `v₀` and of `u₁` with `v₁`. -/
theorem card_correlatedAgreement_set_ge
    (dom : ι → F) (u₀ u₁ : ι → F) (v₀ v₁ : F[X]) (e : ℕ) (S : Finset F)
    (hS : e + 1 < S.card)
    (hagree : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x)
                (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) :
    Fintype.card ι - e ≤
      (univ.filter fun x => u₀ x = v₀.eval (dom x) ∧ u₁ x = v₁.eval (dom x)).card := by
  have hbad := correlatedAgreement_of_branch dom u₀ u₁ v₀ v₁ e S hS hagree
  -- The good set is the complement of `pairDisagree`.
  have hcompl :
      (univ.filter fun x => u₀ x = v₀.eval (dom x) ∧ u₁ x = v₁.eval (dom x))
        = univ \ pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_pairDisagree, RSeval_apply,
      not_or, not_not]
  rw [hcompl, card_sdiff_of_subset (subset_univ _), card_univ]
  omega

end JBAgreement
