-- New for lvm2 (WP S2-CERT): the submission at the node program's tables `M3.tabsP20` (`LvmQAsmV`),
-- split out of WP-14's `LvmSubmissionS` so that the certificate's modules do not import the node
-- program's data (`LvmSubmissionS` is generic in the tables).
import LvmSubmissionS
import LvmQAsmV

/-!
# The submission at `M3.tabsP20`

`submission := subWith VS20 EX20 extX` and `Open := OpenS VS20 EX20` as v1 (WP-14), now
`submissionT M3.tabsP20` and `OpenT M3.tabsP20` by `rfl`; `certificateR_open` from
`certificateR_openT`; O1 at `VS20` (`hq_VS20`).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **O1**: `V_S` at P20 asks at most `qV = 16384` queries on every oracle path. -/
theorem hq_VS20 (H : ByteArray → Digest) (vk c : Digest) (π : Proof) :
    ((VS20 vk c π).queries H).length ≤ Lvm.T.qVlvm :=
  hq_VSL M3.tabsP20 H vk c π

end Lvm

namespace Lvm.T

open RecursionFast Lvm.ASM
open RecursionFast.WitnessSending (decode)
open scoped NNReal

/-- The extractor specification: WP-13a's `EX` with the search branch under `accV VS20`. -/
def EX20 : Digest → Proof → Log → Option Wit := Lvm.X.EX (accV Lvm.VS20)

/-- **The current submission**: `V_S` at P20, WP-13a's extractor. -/
def submission : Submission := subWith Lvm.VS20 EX20 Lvm.X.extX

theorem submission_eq : submission = submissionT Lvm.M3.tabsP20 := rfl

/-- O4: on witness-sending proofs `EX` decodes (WP-13a `EX_W`). -/
theorem EX20_W (c : Digest) (π : Proof) (L : Log) (h : isS π = false) : EX20 c π L = decode π :=
  EXt_W Lvm.M3.tabsP20 c π L h

/-- **The open obligations of the current submission.** -/
abbrev Open : Type := OpenS Lvm.VS20 EX20

/-- **The certificate of the current submission** against `claim.json`, from its open
obligations. -/
theorem certificateR_open (o : Open) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submission :=
  certificateR_openT Lvm.M3.tabsP20 o

end Lvm.T
