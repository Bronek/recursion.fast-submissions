/-
  The ws-leaf entry: a witness-sending argument whose verifier recomputes the leaf statements, so
  that its native prover walks no chain (`WlVerifier.lean`). `declared` is the rendered challenge's,
  copied verbatim, as the comparator requires.
-/
import WlVerifier

namespace RecursionFast.Challenge
open RecursionFast
open scoped NNReal

/-- The declared claim (rendered): the knowledge error, the completeness error, the verifier query
bound and the fuel `fuel_base + fuel_per_word · t` for an input tape of `t` words. -/
noncomputable def declared : Declared where
  ε := ((0 : ℝ≥0) / 1)
  δ := ((0 : ℝ≥0) / 1)
  qV := 0
  fuel t := 68719476736 + 16 * t

/-- The submission: `WsLeaf.wsSub`. -/
def submission : Submission := WsLeaf.wsSub

/-- **The certificate against the rendered claim**: `WsLeaf.certificate`, with the submission's
numbers equal to the declared ones. -/
theorem certified : CertificateR declared submission :=
  ⟨WsLeaf.certificate, by simp [declared, submission, WsLeaf.wsSub],
    by simp [declared, submission, WsLeaf.wsSub], le_rfl, fun t =>
      ⟨by simp [declared, submission, WsLeaf.wsSub, WsLeaf.X.fuelW, WsLeaf.X.fuelBaseW,
          WsLeaf.X.fuelPerWordW],
       by simp only [declared, extractorBudget]; omega⟩⟩

end RecursionFast.Challenge
