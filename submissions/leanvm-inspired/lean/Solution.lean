/-
  The solution of the challenge (`harness/challenge/Challenge.lean.in`, rendered from this entry's
  `claim.json` by `harness/render-challenge.py`) for `leanvm-inspired`. Everything except
  `submission` and `certified` is the rendered stub, copied verbatim.

  `submission` is the guarded submission (`LvmFinGuard.subG`): `V` dispatches on `π[0]` (`'S'` → the
  compiled `V_S` at P20 on the node program's tables (`LvmVFast.VS20F`) when the static check
  `staticOkB` holds, otherwise witness sending), `P` is the witness-sending encoding, `E`/`ext` are
  WP-13a's extractor. `certified` is `LvmFinCert.certificateFin`.
-/
import RecursionFast.Contract
import LvmFinCert

namespace RecursionFast.Challenge
open RecursionFast
open scoped NNReal

/-- The declared claim (rendered): the knowledge error, the completeness error, the verifier query
bound and the fuel `fuel_base + fuel_per_word · t` for an input tape of `t` words. -/
noncomputable def declared : Declared where
  ε := ((1 : ℝ≥0) / 340282366920938463463374607431768211456)
  δ := ((0 : ℝ≥0) / 1)
  qV := 16384
  fuel t := 70368744177664 + 8192 * t

/-- The submission: `leanvm-inspired`, guarded by the static check of the node program. -/
def submission : Submission := Lvm.Fin.subG Lvm.Fin.staticOkB Lvm.VF.VS20F

/-- **The certificate against the rendered claim** (`Contract/Certificate.lean`). -/
theorem certified : CertificateR declared submission := Lvm.Fin.certificateFin

end RecursionFast.Challenge
