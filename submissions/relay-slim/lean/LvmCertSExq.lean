-- WP-14d (EXQ), lvm2 X-REC2 / S4-S2 (helper XA): O5c for `EXt tabs`. The proof is
-- `LvmCertSExq2.ext_eq_gen` (two `C_rec` levels on S2J, generic in `V_S`); here `V_S := VSt tabs`,
-- and the search's bounds from the contract (`sFits_of_acc` on the submission). WP-14d's helpers
-- moved to `LvmCertSExq2`.
import LvmSubmissionS
import LvmCertSExq2

/-!
# O5c: `EX = S.Ex K.ext` on good logs

**`ext_eq_S`**: for `mid` with `MidSpec`, `MidShape`, `MidFollows` (WP-14a, the middle phases'
event kinds are the schedule's) and `child` of WP-13a's form (`ChildX`, WP-14c's `childS`):
on an accepted `'S'` proof over a log with `μ K L < 1`, `EXt tabs = S.Ex K.ext` or `EXt tabs` returns
a witness (an `S` node outside the extractor's domain: the search). lvm2 S4 on S2J: `C_rec` has two
WHIR levels with `g`-bit proofs of work; `ext_eq_gen` (`LvmCertSExq2`) replays the history through
level 1's commitment, level 0's proof of work and opening, and feeds `EX_node` DEC's and WP-13b's
decoders' inputs.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

open Classical in
/-- **O5c** for `EXt tabs` (lvm2 S2-CERT: generic in the node program's tables; v1's `EX20`): on
an accepted `'S'` proof over a log of potential below `1`, WP-13a's
`EX` is the specification extractor of `kcertS` (WP-13b's decoder on the replayed history), or
returns a witness of the relation. Hypotheses beyond `kcertS`'s: the middle phases' event kinds
(`MidFollows`, WP-14a) and the child's form (`ChildX`, WP-14c's `childS`). -/
theorem ext_eq_S {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}
    (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {tabs : Lvm.Pub → List Lvm.M3.Tab}
    {child : Column 19 → Signed} (hnode : ∀ vk, NodeSound (Lvm.T.VSt tabs) vk Good child)
    (hch : ChildX child) (hfol : MidFollows mid) (vk : RecursionFast.Digest) (L : Log)
    (c : RecursionFast.Digest) (π : RecursionFast.Proof) (_hS : isS π = true)
    (_hl : L.length ≤ logCap)
    (hμ : Scheme.μ (kcertS hmid hLm hsh (hnode vk)) L < 1)
    (hacc : ((schemeS vk (PSWith mid)).V c π).runLog L = some true) :
    (∃ w, Lvm.T.EXt tabs c π L = some w ∧ Rel (accV (Lvm.T.VSt tabs) vk) c w) ∨
      Lvm.T.EXt tabs c π L = (schemeS vk (PSWith mid)).Ex (kcertS hmid hLm hsh (hnode vk)).ext c π L :=
  ext_eq_gen hmid hLm hsh hnode hch hfol (fun _ _ _ hp => Lvm.X.sFits_of_acc
    (S := Lvm.T.submissionT tabs) (by show Lvm.T.qVlvm ≤ Lvm.X.qMax; decide)
    (by rw [show (Lvm.T.submissionT tabs).acc = accV (Lvm.T.VSt tabs) from
      subWith_acc (Lvm.T.VSt tabs) (Lvm.T.EXt tabs) Lvm.X.extX]; exact hp))
    vk L c π hμ hacc

end Lvm.ASM
