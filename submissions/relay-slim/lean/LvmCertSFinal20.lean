-- New for lvm2 (WP S2-CERT): WP-16b's certificate glue at WP-16a's P20 node program (`M3.tabsP20`,
-- `LvmQAsmV`), split out of `LvmCertSFinal` (now generic in the tables): INB's `hinb20` gives
-- `NodeHyp` from `NodeBase` (`nodeHyp20`), `PUB`'s closed form gives `AccMidHyp` (`accMidHyp_P20`),
-- and `certificateR_node20` is v1's `certificateR_node` for `Lvm.T.submission`.
import LvmCertSFinal
import LvmSubmissionS20
import LvmAccNodeTabs
import LvmQAsmInb

/-!
# The certificate at `M3.tabsP20`

* **`nodeHyp20`**: `NodeHyp` for WP-16a's P20 program from `NodeBase`, the position classes' cell
  bounds and Q_arith's no-`readd` fact (INB's `hinb20`);
* **`accMidHyp_P20`**: phase 3b's instance facts from `MidHyp` and `PUB`'s closed form
  (`LvmAccNodeTabs.pubEv_P20`);
* **`openS_of20`**: `Lvm.T.Open` from `FinalHyp M3.tabsP20`;
* **`certificateR_node20`**: the certificate of `Lvm.T.submission` from `MidHyp M3.tabsP20` and
  `NodeHyp …` (`fixStatic_P20`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm Lvm.M3 Lvm.VEq Lvm.Acc

section Node20

open Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.SigBits Lvm.NS LeanVM.Protocol
open Lvm.QAsm (cfg20 lay sigIn qarith nK aux QData PosCellsLt)

variable {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {D : QData}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) pl groups (arrsX x)
    (aux cfg20 D), t.τ ≤ lay26.μ} {bpl : ℕ → ℕ → Bool × ℕ} {rest : List Tab} {pb : ℕ}

/-- **`NodeHyp` for WP-16a's P20 program** from `NodeBase`, the position classes' cell bounds and
Q_arith's no-`readd` fact `hna` (INB's `hinb20`). -/
theorem nodeHyp20
    (B : NodeBase (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ'
      bpl rest pb M3.tabsP20)
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hna : Lvm.Loop.Build.noReaddSegs (qarith cfg20 (Lvm.QAsm.p2C cfg20)).2 = true) :
    NodeHyp (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' bpl rest
      pb M3.tabsP20 :=
  { B with hinb := Lvm.QAsm.hinb20 (D := D) B.hT B.hst B.hQ B.hqlt hpc hna }

end Node20

/-- **Phase 3b's instance facts at P20** from O6's (`MidHyp`), with `PUB`'s closed form decided on
WP-16a's tables (`LvmAccNodeTabs.pubEv_P20`). -/
theorem accMidHyp_P20 (M : MidHyp M3.tabsP20) : AccMidHyp M3.tabsP20 :=
  accMidHyp_of M fun x t f e ht hc r _ ↦ Lvm.QAsm.pubEv_P20 (pubX x) t f e ht hc r

/-- **The open obligations of the current submission** from `FinalHyp M3.tabsP20`. -/
noncomputable def openS_of20 (H : FinalHyp M3.tabsP20) : Lvm.T.Open := openS_of H

section NodeCert20

open Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.SigBits Lvm.NS LeanVM.Protocol

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}
  {bpl : ℕ → ℕ → Bool × ℕ} {rest : List Tab} {pb : ℕ}

/-- **The certificate of `Lvm.T.submission` from O6's table checks and O10's `nodeSound_acc`
hypotheses** for a concrete node program on WP-16a's tables; phase 3b's instance facts and
`FixStatic` are decided on the P20 tables (`accMidHyp_P20`, `fixStatic_P20`). -/
theorem certificateR_node20 (M : MidHyp M3.tabsP20)
    (N : NodeHyp lay I qa nK nE pl groups arrsX aux hτ' bpl rest pb M3.tabsP20) :
    CertificateR ⟨(1 : NNReal) / 340282366920938463463374607431768211456, (0 : NNReal) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ Lvm.T.submission :=
  certificateR_node M (accMidHyp_P20 M) Lvm.QAsm.fixStatic_P20 N

end NodeCert20

end Lvm.ASM
