-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/LJDefs.lean` @ 1b74a2a2 (archive/pcs/S1P) (Flock LJ1/LJ2, on the
-- longfellow port `LvmJB*`, Apache License 2.0, see `LICENSE-longfellow`). Changed: imports `JB*`/`LJ*`
-- renamed `LvmJB*`/`LvmLJ*`; nothing else.
-- LJ1: the definitions of SJ's generic lemmas, copied verbatim from `design/SJ-files/SJStmts.lean`
-- (namespace `SJ` → `LJ`). Statements of the lemmas themselves are in the per-lemma modules.
import LvmJBStrongMutual
import LvmJBComplete
import Mathlib.LinearAlgebra.Lagrange

open Polynomial Finset JBAgreement

namespace LJ

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Interleaved words -/

/-- Column disagreement of two `m`-row words (`matrixErrorCoordinates`). -/
def colDisagree {m : ℕ} (U V : Fin m → ι → K) : Finset ι :=
  univ.filter fun x => ∃ r, U r x ≠ V r x

/-- (helper, not in SJStmts) membership in `colDisagree`. -/
theorem mem_colDisagree {m : ℕ} (U V : Fin m → ι → K) (x : ι) :
    x ∈ colDisagree U V ↔ ∃ r, U r x ≠ V r x := by
  unfold colDisagree; rw [mem_filter]; simp

/-- Rows of polynomials evaluated on the domain. -/
def evalRows {m : ℕ} (dom : ι → K) (P : Fin m → K[X]) : Fin m → ι → K :=
  fun r x => (P r).eval (dom x)

/-- `explains`, row-wise: `P = P₀ + z P₁` and the line's agreement set lies in the pair's joint one. -/
def iExplains {m : ℕ} (dom : ι → K) (U₀ U₁ : Fin m → ι → K) (z : K) (P P₀ P₁ : Fin m → K[X]) : Prop :=
  (∀ r, P r = P₀ r + C z * P₁ r) ∧
    ∀ x, (∀ r, U₀ r x + z * U₁ r x = (P r).eval (dom x)) →
      ∀ r, U₀ r x = (P₀ r).eval (dom x) ∧ U₁ r x = (P₁ r).eval (dom x)

/-- `HasUnexplainedProximate`, row-wise (column distance). -/
def iHasUnexplainedProximate {m : ℕ} (dom : ι → K) (U₀ U₁ : Fin m → ι → K) (k e : ℕ) (z : K) : Prop :=
  ∃ P : Fin m → K[X], (∀ r, (P r).natDegree < k) ∧
    (colDisagree (fun r x => U₀ r x + z * U₁ r x) (evalRows dom P)).card ≤ e ∧
    ∀ P₀ P₁ : Fin m → K[X], (∀ r, (P₀ r).natDegree < k) → (∀ r, (P₁ r).natDegree < k) →
      ¬ iExplains dom U₀ U₁ z P P₀ P₁

/-! ## The nested fold -/

theorem two_mul_lt {l : ℕ} (r : Fin (2 ^ l)) : 2 * r.val + 1 < 2 ^ (l + 1) := by
  have h := r.isLt; rw [pow_succ]; omega

/-- Even rows, odd rows. -/
def evens {l : ℕ} {α : Type*} (U : Fin (2 ^ (l + 1)) → α) : Fin (2 ^ l) → α :=
  fun r => U ⟨2 * r.val, by have := two_mul_lt r; omega⟩
def odds {l : ℕ} {α : Type*} (U : Fin (2 ^ (l + 1)) → α) : Fin (2 ^ l) → α :=
  fun r => U ⟨2 * r.val + 1, two_mul_lt r⟩

/-- One Ligerito fold round on words (`foldN`) and on polynomial rows. -/
def foldRows {l : ℕ} (z : K) (W : Fin (2 ^ (l + 1)) → ι → K) : Fin (2 ^ l) → ι → K :=
  fun r x => evens W r x + z * (odds W r x - evens W r x)
noncomputable def foldPolys {l : ℕ} (z : K) (Q : Fin (2 ^ (l + 1)) → K[X]) : Fin (2 ^ l) → K[X] :=
  fun r => evens Q r + C z * (odds Q r - evens Q r)

/-- **`W` is explained by `U` through `fold`**: every `e`-close codeword tuple of `W` is `fold V` for an
`e`-close tuple `V` of `U` whose joint agreement set contains `P`'s. -/
def ExplBy {a b : ℕ} (dom : ι → K) (U : Fin a → ι → K) (W : Fin b → ι → K)
    (fold : (Fin a → K[X]) → (Fin b → K[X])) (k e : ℕ) : Prop :=
  ∀ P : Fin b → K[X], (∀ r, (P r).natDegree < k) → (colDisagree W (evalRows dom P)).card ≤ e →
    ∃ V : Fin a → K[X], (∀ r, (V r).natDegree < k) ∧ fold V = P ∧
      colDisagree U (evalRows dom V) ⊆ colDisagree W (evalRows dom P)

/-- Base case: a word explains itself. -/
theorem explBy_refl {a : ℕ} (dom : ι → K) (U : Fin a → ι → K) (k e : ℕ) :
    ExplBy dom U U id k e :=
  fun P hP _ => ⟨P, hP, rfl, subset_refl _⟩

/-! ## GKR hand-off (generic) -/

/-- `eq` on the Boolean cube. -/
def eqB {n : ℕ} (r : Fin n → K) (x : Fin n → Bool) : K := ∏ i, if x i then r i else 1 - r i

end LJ
