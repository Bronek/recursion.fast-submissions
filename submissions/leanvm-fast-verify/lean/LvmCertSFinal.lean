-- WP-16b (CERT). New for lvm: the open obligations `Lvm.T.Open` (`LvmSubmissionS.OpenS`) of the
-- submission, plugged with WP-14a's middle phases `midS` and `refines_VSL`, O6 (`LvmCertSMid3`),
-- WP-14c's `childS` and `NodeSound`, WP-14d's `ext_eq_S` with WP-14a's `midFollows_midS`.
-- AC-N (A23): `midS` with phase 3b (= AC-S's `midSA`), O6 from AC-S's `midSpec_midSA`, `Good :=
-- GoodA` (`GoodS ∧ AccOk acc_in`), `NodeSound` from `LvmAccNode.nodeSound_acc` (Q_arith's `harith`
-- in A23's form: `decideCore ∧ accOutOf = acc_in`).
import LvmAccSpecCert
import LvmCertSExq
import LvmVEqRefines
import LvmVEqFolMid
import LvmAccNode
import LvmAccNodeTabs
import LvmQAsmInb

/-!
# The open obligations, plugged

**`openS_of (H : FinalHyp)`**: `Lvm.T.Open` (so `Solution.certified_of` gives the certificate) from
`FinalHyp`, the facts left about the frozen tables `M3.tabsP20` of `VS20`:

* `mid : MidHyp M3.tabsP20` (O6: `fitsR` and WP-9b's table checks, `LvmCertSMid3`);
* `acc : AccMidHyp M3.tabsP20` (A23: AC-S's phase-3b instance facts; `accMidHyp_of`);
* `node`: `NodeSound` for `GoodN ∧ AccOkN` at `VS20` (O10; **`node_of`** gives it from
  **`NodeHyp`**, the hypotheses of `nodeSound_acc` for a concrete node program, and `FixStatic`).

**`certificateR_node`**: the certificate from `MidHyp` and `NodeHyp …` (`AccMidHyp` by
`accMidHyp_P20`, `FixStatic` by `fixStatic_P20`, both on WP-16a's P20 tables).

The fields: `mid := midS M3.tabsP20` (`= midSA`), `Good := GoodA …` (WP-16b's `GoodS` and
`AccOk acc_in`), `Lm := εS`, `hmid := midSpec_midSA`, `hsh := midShape_midSA`, `child := childS`,
`hnode := nodeSound_goodA ∘ node`, `refines := refines_VSL`, `ext_eq := ext_eq_S … (fun _ ↦ rfl)
(midFollows_midS …)`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm Lvm.M3 Lvm.VEq Lvm.Acc

/-! ## O10: `nodeSound_layout`'s hypotheses -/

section Node

open Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.SigBits Lvm.NS LeanVM.Protocol

variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)
  (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrsX : List UInt8 → List InArr) (aux : List Tab)
  (hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ)
  (bpl : ℕ → ℕ → Bool × ℕ) (rest : List Tab) (pb : ℕ)

/-- **WP-14c's `nodeSound_layout` hypotheses but `hinb`**, for the node program `Qn lay I qa nK nE`
with the placement `pl`, groups, input arrays `arrsX` and aux tables `aux` (`= Q_sig's BITS ++ rest`),
at the tables `TS M3.tabsP20` of `VS20`: static facts of the program and its placement (decidable),
QL's Q_link facts (`hqlt`, `hpos`), and Q_arith (`harith`, A23's form: the child's `decideCore` and
its folded accumulator equal to the statement's `acc_in`). -/
structure NodeBase : Prop where
  hT : ∀ x, TS M3.tabsP20 x = lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux
  hst : ∀ x, AuxStatic lay I qa nK nE pl groups aux (arrsX x)
  hlay : ∀ x, LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux)
  hτT : ∀ x, ∀ t ∈ TS M3.tabsP20 x, t.τ ≤ lay26.μ
  hS : StreamOk P20
  hQ : QOk P20 lay
  hws : 2 ^ lay.m ≤ 17 * 2 ^ 14
  hfg : lay.fg = I.flag
  hln : I.ln = 20
  hqlt : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS M3.tabsP20) hτT x qm qr →
    ∀ y < (qltData P20 lay).length,
      (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (lay.qt + y) = (qltData P20 lay).getD y 0
  hpos : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS M3.tabsP20) hτT x qm qr →
    ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
      ∀ z < ((opens P20).getD k default).L.height,
      (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k
          (bitBase P20 lay k + ((opens P20).getD k default).L.height * j + z) =
        if ansBit P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) (((opens P20).getD k default).pe + j / 8)
          (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0
  hNs : lay.sb + 2 ^ lay.m ≤ max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E)
  haux : aux = (sigSpecs I (qsig I (p1 lay nK nE)).1 bpl).map BitsTab.BSpec.tab ++ rest
  hR : SigRegLt ((Qn lay I qa nK nE).cells .K) I
  hP : (p2 lay I nK nE).k ≤ (Qn lay I qa nK nE).cells .K
  hSt : ∀ x, Bundle (arrsX x) 17 14 lay.sb true fun l => l * 2 ^ 14
  hhd : I.hd = lay.sb + 11
  hSg : ∀ x, Bundle (arrsX x) 1 10 I.sg true fun _ => 17 * 2 ^ 14
  hX : ∀ x, Bundle (arrsX x) 17 9 I.xs false fun l => ksY2 + 2 ^ 19 + l * 2 ^ 14
  hY : ∀ x, Bundle (arrsX x) 4 9 I.ys false fun l => 50 * 2 ^ 20 + 2 ^ 15 * (50 + l) + 2 ^ 14
  hyc : I.yc = I.ys + 4 * 430
  hyls : I.yls = I.ys + 4 * 447
  hyns : I.yns = I.ys + 4 * 448
  hMd : ∀ x, Bundle (arrsX x) 4 0 I.md false
    fun l => 50 * 2 ^ 20 + 2 ^ 15 * (50 + l) + (spongeBlocks P20 - 1)
  hPub : ∀ x, PubAt (arrsX x) x pb
  hfl : I.flag = pb
  hvkI : I.vk = pb + 1
  hcLI : I.cL = pb + 5
  hslI : I.sl = pb + 18
  harith : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS M3.tabsP20) hτT x qm qr →
    InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr →
    LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) →
    LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) →
    Ok (ctxOf (Qn lay I qa nK nE)) (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr) qa
      (p2 lay I nK nE) →
    decideCore P20 (M3.real P20 M3.tabsP20) vk (hdrOf x).cL
        (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = true ∧
      accOutOf P20 (M3.real P20 M3.tabsP20) vk (hdrOf x).cL
        (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = (pubX x).accIn

/-- **WP-14c's `nodeSound_layout` hypotheses**: `NodeBase` and QL's `hinb` (every computed-address
read finds its cell; INB's `hinb20` for WP-16a's P20 program, `nodeHyp20`). -/
structure NodeHyp : Prop extends NodeBase lay I qa nK nE pl groups arrsX aux hτ' bpl rest pb where
  hinb : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS M3.tabsP20) hτT x qm qr →
    ((Qn lay I qa nK nE).interp (inKOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
      (stackOf lay26 qm qr)) (inEOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
      (stackOf lay26 qm qr))).inb = true

variable {lay I qa nK nE pl groups arrsX aux hτ' bpl rest pb}

/-- **O10 from `NodeHyp`** (`nodeSound_acc`) and `FixStatic` (`Φ` is one polynomial), for any proof
of the tables' heights. -/
theorem node_of (N : NodeHyp lay I qa nK nE pl groups arrsX aux hτ' bpl rest pb)
    (hΦ : FixStatic P20 M3.tabsP20) (hτ : ∀ x, ∀ t ∈ TS M3.tabsP20 x, t.τ ≤ lay26.μ)
    (vk : RecursionFast.Digest) :
    NodeSound VS20 vk (fun x qm qr ↦ GoodN (TS M3.tabsP20) hτ x qm qr ∧ AccOkN M3.tabsP20 x) childS :=
  nodeSound_acc (M3.real P20 M3.tabsP20) vk (fixVals_real P20 M3.tabsP20 hΦ) N.hT N.hst N.hlay
    (N.hinb vk) N.hS N.hQ N.hws N.hfg N.hln (N.hqlt vk) (N.hpos vk) N.hNs bpl rest N.haux N.hR N.hP
    N.hSt N.hhd N.hSg N.hX N.hY N.hyc N.hyls N.hyns N.hMd N.hPub N.hfl N.hvkI N.hcLI N.hslI (N.harith vk)

end Node

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
      bpl rest pb)
    (hpc : PosCellsLt (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) cfg20)
    (hna : Lvm.Loop.Build.noReaddSegs (qarith cfg20 (Lvm.QAsm.p2C cfg20)).2 = true) :
    NodeHyp (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 pl groups arrsX (aux cfg20 D) hτ' bpl rest
      pb :=
  { B with hinb := Lvm.QAsm.hinb20 (D := D) B.hT B.hst B.hQ B.hqlt hpc hna }

end Node20

/-- `midS` (WP-14a's middle phases with A23's phase 3b) is AC-S's `midSA`. -/
theorem midS_eq_midSA (tabs : Pub → List Tab) : midS tabs = midSA tabs := rfl

/-- **Phase 3b's instance facts at P20** from O6's (`MidHyp`), with `PUB`'s closed form decided on
WP-16a's tables (`LvmAccNodeTabs.pubEv_P20`). -/
theorem accMidHyp_P20 (M : MidHyp M3.tabsP20) : AccMidHyp M3.tabsP20 :=
  accMidHyp_of M fun x t f e ht hc r _ ↦ Lvm.QAsm.pubEv_P20 (pubX x) t f e ht hc r

/-- **The facts left for the certificate** about the frozen tables `M3.tabsP20`. -/
structure FinalHyp : Prop where
  /-- O6: the tables fit `P20` and pass WP-9b's checks. -/
  mid : MidHyp M3.tabsP20
  /-- O6, A23: phase 3b's instance facts (AC-S's `AccInst` at every statement). -/
  acc : AccMidHyp M3.tabsP20
  /-- O10: the arithmetisation's soundness for WP-14c's good pair with `AccOk acc_in`. -/
  node : ∀ vk, NodeSound VS20 vk
    (fun x qm qr ↦ Lvm.NS.GoodN (TS M3.tabsP20) mid.hτ x qm qr ∧ AccOkN M3.tabsP20 x) Lvm.NS.childS

/-- **The open obligations of the submission** from `FinalHyp`. -/
noncomputable def openS_of (H : FinalHyp) : Lvm.T.Open where
  mid := midS M3.tabsP20
  Good := GoodA M3.tabsP20 H.mid.hτ
  Lm := εS
  hmid := midS_eq_midSA M3.tabsP20 ▸ midSpec_midSA H.mid H.acc
  hLm := le_rfl
  hsh := midS_eq_midSA M3.tabsP20 ▸ midShape_midSA H.mid
  child := Lvm.NS.childS
  hnode vk := nodeSound_goodA (H.node vk)
  refines := refines_VSL M3.tabsP20 H.mid.fit H.mid.width
  ext_eq vk L c π hS hl hμ hv :=
    ext_eq_S (midS_eq_midSA M3.tabsP20 ▸ midSpec_midSA H.mid H.acc) le_rfl
      (midS_eq_midSA M3.tabsP20 ▸ midShape_midSA H.mid)
      (fun vk ↦ nodeSound_goodA (H.node vk)) (fun _ ↦ rfl) (midFollows_midS _ H.mid.fit) vk L c π
      hS hl hμ hv

/-- **The certificate of the submission against `claim.json`** from `FinalHyp`. -/
theorem certificateR_final (H : FinalHyp) :
    CertificateR ⟨(1 : NNReal) / 340282366920938463463374607431768211456, (0 : NNReal) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ Lvm.T.submission :=
  Lvm.T.certificateR_open (openS_of H)

section NodeCert

open Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.SigBits Lvm.NS LeanVM.Protocol

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}
  {bpl : ℕ → ℕ → Bool × ℕ} {rest : List Tab} {pb : ℕ}

/-- **The certificate from O6's table checks and O10's `nodeSound_acc` hypotheses** for a concrete
node program (WP-16a's `Q`, placement, groups, arrays and aux tables); phase 3b's instance facts and
`FixStatic` are decided on the P20 tables (`accMidHyp_P20`, `fixStatic_P20`). -/
theorem certificateR_node (M : MidHyp M3.tabsP20)
    (N : NodeHyp lay I qa nK nE pl groups arrsX aux hτ' bpl rest pb) :
    CertificateR ⟨(1 : NNReal) / 340282366920938463463374607431768211456, (0 : NNReal) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ Lvm.T.submission :=
  certificateR_final ⟨M, accMidHyp_P20 M, fun vk ↦ node_of N Lvm.QAsm.fixStatic_P20 M.hτ vk⟩

end NodeCert

end Lvm.ASM
