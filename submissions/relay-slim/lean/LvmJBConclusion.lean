-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBConclusion.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBMutual
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Exact strong-agreement conclusion

This file contains only the conclusion shared by the exact certificate
theorems.  It deliberately contains no real-valued envelope or asymptotic
wrapper.
-/

namespace JBAgreement

open Polynomial Finset

/-- One dimension-`k` polynomial pair explains the two words up to `e` pair
errors and satisfies the full mutual/list conclusion at the same radius. -/
def StrongAgreementConclusion
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (dom : ι → F) (u₀ u₁ : ι → F) (k e : ℕ) : Prop :=
  ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
    (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e ∧
    (∀ S₂ : Finset F, e + 1 < S₂.card →
      (∀ z ∈ S₂, (disagree (fun x => u₀ x + z * u₁ x)
          (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) →
      (S₂.filter fun z =>
        lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z ≠
          corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e)

end JBAgreement
