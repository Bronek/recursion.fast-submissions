-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBCertificateMinimum.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBComplete
import LvmJBConclusion

/-!
# Exact certificate minimum

This file minimizes the exact four-integer certificate ledger.  It contains no
real-valued envelope or asymptotic wrapper.
-/

namespace JBAgreement

open Polynomial Finset

/-! ## The exact inner term -/

/-- A certificate for the numerical hypotheses of the checked four-parameter
interpolation kernel.  This type belongs to the implementation layer: callers
use `innerStrongTerm`, which minimizes over all such certificates. -/
structure StrongCertificate (k n e : ℕ) where
  multiplicity : ℕ
  weightedDegree : ℕ
  yDegree : ℕ
  zDegree : ℕ
  yDegree_le : k * yDegree ≤ weightedDegree
  coefficient_surplus :
    n * (multiplicity * (multiplicity + 1)) * (zDegree + yDegree + 1) <
      ((yDegree + 1) * (2 * (weightedDegree + 1)) -
        k * (yDegree * (yDegree + 1))) * (zDegree + 1)
  root_surplus : weightedDegree < multiplicity * (n - e)
  agreement_slack : 1 ≤ n - e - k

/-- The exact number of exceptional parameters charged by a numerical
certificate.  A parameter set of cardinality strictly larger than this term is
enough for the strong (correlated-and-mutual) conclusion. -/
def StrongCertificate.term {k n e : ℕ} (c : StrongCertificate k n e) : ℕ :=
  c.yDegree * (e + 2) +
    (n - k) * (4 * k * (c.yDegree * c.zDegree) + c.yDegree) / (n - e - k) +
    c.zDegree + 3 * (c.yDegree * c.zDegree)

/-- The best exceptional-parameter term furnished by the checked
interpolation argument.  It is a natural-number infimum, hence is attained
whenever a numerical certificate exists. -/
noncomputable def innerStrongTerm (k n e : ℕ) : ℕ :=
  sInf {q : ℕ | ∃ c : StrongCertificate k n e, c.term = q}

/-- Least integral cardinality threshold corresponding to `innerStrongTerm`. -/
noncomputable def innerStrongThreshold (k n e : ℕ) : ℕ :=
  innerStrongTerm k n e + 1

theorem innerStrongTerm_le {k n e : ℕ} (c : StrongCertificate k n e) :
    innerStrongTerm k n e ≤ c.term := by
  exact Nat.sInf_le ⟨c, rfl⟩

theorem exists_certificate_at_innerStrongTerm {k n e : ℕ}
    (h : Nonempty (StrongCertificate k n e)) :
    ∃ c : StrongCertificate k n e, c.term = innerStrongTerm k n e := by
  have hset :
      ({q : ℕ | ∃ c : StrongCertificate k n e, c.term = q} : Set ℕ).Nonempty := by
    obtain ⟨c⟩ := h
    exact ⟨c.term, c, rfl⟩
  simpa [innerStrongTerm] using Nat.sInf_mem hset

section Exact

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- More than `innerStrongTerm` proximate line
parameters force a single dimension-`k` pair with at most `e` pair disagreements.
The same pair satisfies the mutual/list conclusion.  The interpolation integers
are hidden in the attained minimum. -/
theorem correlatedAgreement_innerStrong
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (S : Finset F)
    (hclose : ∀ z ∈ S, ∃ p : F[X], p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e)
    (hk : 1 ≤ k)
    (hcert : Nonempty (StrongCertificate k (Fintype.card ι) e))
    (hS : innerStrongTerm k (Fintype.card ι) e < S.card) :
    StrongAgreementConclusion dom u₀ u₁ k e := by
  obtain ⟨c, hc⟩ := exists_certificate_at_innerStrongTerm hcert
  have hyDegree : (k - 1) * c.yDegree ≤ c.weightedDegree :=
    (Nat.mul_le_mul_right c.yDegree (Nat.sub_le k 1)).trans c.yDegree_le
  have hcoefficient :
      Fintype.card ι * (c.multiplicity * (c.multiplicity + 1)) *
          (c.zDegree + c.yDegree + 1) <
        ((c.yDegree + 1) * (2 * (c.weightedDegree + 1)) -
            (k - 1) * (c.yDegree * (c.yDegree + 1))) * (c.zDegree + 1) := by
    apply c.coefficient_surplus.trans_le
    apply Nat.mul_le_mul_right
    apply Nat.sub_le_sub_left
    exact Nat.mul_le_mul_right _ (Nat.sub_le k 1)
  apply correlatedAgreement_unconditional_sharp_noFieldSize dom hdom u₀ u₁ k e hk
    S hclose c.multiplicity c.weightedDegree c.yDegree c.zDegree
    hyDegree hcoefficient c.root_surplus c.agreement_slack
  rw [← hc] at hS
  exact hS

/-- Weak-cardinality form of `correlatedAgreement_innerStrong`. -/
theorem correlatedAgreement_innerStrong_threshold
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (S : Finset F)
    (hclose : ∀ z ∈ S, ∃ p : F[X], p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e)
    (hk : 1 ≤ k)
    (hcert : Nonempty (StrongCertificate k (Fintype.card ι) e))
    (hS : innerStrongThreshold k (Fintype.card ι) e ≤ S.card) :
    StrongAgreementConclusion dom u₀ u₁ k e := by
  apply correlatedAgreement_innerStrong dom hdom u₀ u₁ k e S hclose hk hcert
  rw [innerStrongThreshold] at hS
  omega

end Exact

end JBAgreement
