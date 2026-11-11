-- WP-14 (ASM). New for lvm: the current submission (V_S at P20, WP-13a's extractor) and its open
-- obligations, in the reduced form of the assembly (`LvmCertSExt.kcertS`).
import LvmCertSExt
import LvmCertSGood
import LvmXSpec
import LvmCertSQ

/-!
# The submission and its open obligations

`submission := subWith VS20 (EX (accV VS20)) extX`: `V_S` at P20 (WP-11a), WP-13a's extractor
program `extX` and its specification `EX` (the search branch under `accV VS20`).

**Closed** here: O1 the query bound (`hq_VS20`, `LvmCertSQ`), O2 `Computes extX (EX A) fuel`
(`computesX`), O3 the program's size (`extX_caps`),
O4 `EX` on `W` proofs (`EX_W`), O5a the knowledge certificate from its parts (`kcertS`), O7, O8, O9,
O11.

**`OpenS VS E`**, the obligations left (statements final; each a field):

| field | obligation | owner |
|---|---|---|
| `mid`, `Good`, `Lm`, `hmid`, `hLm` | O6: the middle phases' specification from the doom root | WP-8/9 phases, WP-14 composes |
| `hsh` | the middle phases commit nothing, grind nowhere, return multiaffine `C_rec` claims | WP-14 (structural) |
| `child`, `hnode` | O10: `NodeSound` | WP-8/9/10/11b/12, WP-14 assembles |
| `refines` | O5b: `V_S` accepting implies the compiled `S.V` accepting | WP-14a |
| `ext_eq` | O5c: on accepted `'S'` proofs over logs of potential below `1`, `E = S.Ex K.ext` or a witness | WP-14d (`LvmCertSExq.ext_eq_S`) |
-/

set_option autoImplicit false

namespace Lvm.T

open RecursionFast Lvm.ASM
open RecursionFast.WitnessSending (encode decode encodeF)
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

/-- **The open obligations** of `subWith VS E ext`'s `S` branch. -/
structure OpenS (VS : SProg) (E : Digest → Proof → Log → Option Wit) : Type where
  /-- The middle phases of `P_S`. -/
  mid : List UInt8 → VerifierProgram OpenClaims
  /-- The M3 relation on a candidate pair. -/
  Good : GoodRel
  /-- The middle phases' lead. -/
  Lm : ℝ≥0∞
  /-- O6: the middle phases from the doom root. -/
  hmid : MidSpec mid Good εS Lm
  hLm : Lm ≤ εS
  /-- The middle phases' shape. -/
  hsh : MidShape mid
  /-- The left child read from `C_rec`'s candidate. -/
  child : LeanVM.Protocol.Column 19 → Signed
  /-- O10: the arithmetisation's soundness. -/
  hnode : ∀ vk, NodeSound VS vk Good child
  /-- O5b: `V_S` refines the compiled verifier. -/
  refines : ∀ vk L c π, isS π = true → (VS vk c π).runLog L = some true →
    ((schemeS vk (PSWith mid)).V c π).runLog L = some true
  /-- O5c: the extractor is the specification extractor on good logs (`final_good` gives the
  replayed history's facts there), or returns a witness (WP-14d: FR's search outside the
  extractor's domain, which a log entry of `≥ 2^64` bytes or a tape over `2^64` words reaches). -/
  ext_eq : ∀ vk L c π, isS π = true → L.length ≤ logCap →
    Lvm.FS.Scheme.μ (kcertS hmid hLm hsh (hnode vk)) L < 1 →
    ((schemeS vk (PSWith mid)).V c π).runLog L = some true →
    (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨
      E c π L = (schemeS vk (PSWith mid)).Ex (kcertS hmid hLm hsh (hnode vk)).ext c π L

/-- **`SSound` from the open obligations.** -/
theorem sSound_of_openS {VS : SProg} {E : Digest → Proof → Log → Option Wit} (o : OpenS VS E)
    (vk : Digest) : SSound VS E vk :=
  sSound_of VS E vk (PSWith o.mid) (kcertS o.hmid o.hLm o.hsh (o.hnode vk))
    (εFS_kcertS o.hmid o.hLm o.hsh (o.hnode vk)) (o.refines vk)
    fun L c π hS hl hμ hv ↦ o.ext_eq vk L c π hS hl hμ hv

/-! ## The current submission -/

/-- The extractor specification: WP-13a's `EX` with the search branch under `accV VS20`. -/
def EX20 : Digest → Proof → Log → Option Wit := Lvm.X.EX (accV Lvm.VS20)

/-- **The current submission**: `V_S` at P20, WP-13a's extractor. -/
def submission : Submission := subWith Lvm.VS20 EX20 Lvm.X.extX

/-- O4: on witness-sending proofs `EX` decodes (WP-13a `EX_W`). -/
theorem EX20_W (c : Digest) (π : Proof) (L : Log) (h : isS π = false) : EX20 c π L = decode π := by
  refine Lvm.X.EX_W _ c π L fun h0 ↦ ?_
  have : π.data.getD 0 0 = 0x53 := by
    rw [Array.getD_eq_getD_getElem?, h0]; rfl
  simp [isS, this, sByte] at h

/-- **The open obligations of the current submission.** -/
abbrev Open : Type := OpenS Lvm.VS20 EX20

/-- **The certificate of the current submission** against `claim.json`, from its open
obligations. -/
theorem certificateR_open (o : Open) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ submission :=
  certificateR_claim Lvm.VS20 EX20 Lvm.X.extX
    ⟨fun H vk c π _ ↦ Lvm.hq_VS20 H vk c π, Lvm.X.computesX _, Lvm.X.extX_caps.2, EX20_W,
      sSound_of_openS o⟩

end Lvm.T
