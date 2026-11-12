-- New for lvm (WP-16a2, FIN-DEC): the final assembly (BLUEPRINT A24, WP-16a2 §3): HAR's static facts at
-- `P20` (`harStatic20`), the node program's `NodeBase` from the static facts (`LvmQAsmFacts`, FIN-TF's
-- `LvmQAsmFactsNode`), FIN-BV's memory facts and FIN-HB's `harith20`; the open obligations under the
-- guard's facts (`openFin`) and the certificate of the guarded submission (`certificateFin`).
import LvmFinDec
import LvmQAsmFactsNode
import LvmFinHB
import LvmFinGuard
import LvmCertSFinal20
import LvmVFast

/-!
# The certificate

* **`harStatic20`**: `HarStatic cfg20 data20 T P4 … P8` at the stream's lanes and the first positions
  of phases 4–8 (`harStatic_of` from `harNum20`, the table shape facts `shpOk_P20` through HAR's
  `shapesOf_eq`, the layer checks (the tape's `layOk_15`, `KS`'s `layOk_11`), `okE_P20`, HAR-WH's
  `lay20`).
* **`nodeBase20 S`**: `NodeBase` for WP-16a's `P20` node program (`hτ' := hτL20`, `bpl := bplOf data20`,
  `rest := rest20`, `haux20`'s split), from A24's facts `S`.
* **`openFin S`**: `Lvm.T.Open` from `midHyp20 S`, `accMidHyp_P20`, `nodeHyp20` and `fixStatic_P20`.
* **`certificateFin`**: the certificate of `subG staticOkB VF.VS20F` against the declared claim
  (`certificateR_guard`: with the guard off `V_S` rejects every `S` proof).
-/

set_option autoImplicit false

namespace Lvm.Fin

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits
open Lvm.NS Lvm.VEq Lvm.ASM Lvm.QAsm
open scoped NNReal

/-! ## HAR's static facts at `P20` -/

/-- The table phase's shapes are those of the sumcheck tables at `default`. -/
theorem shapes20 : Har.shapesOf cfg20 data20 = (sumcheckTabs (M3.tabsP20 default)).map Tab.shape :=
  Har.shapesOf_eq cfg20 data20 M3.G20 default

/-- **`harith_core`'s static facts at `P20`** (the stream's lanes, the first positions of phases 4–8). -/
theorem harStatic20 : Har.HarStatic cfg20 data20 (streamLanes P20) (Har.phaseByte P20 .tape + 24)
    (Har.phaseByte P20 .wire) (Har.phaseByte P20 .ks) (Har.phaseByte P20 .ksLink) (8 * Har.openU P20) := by
  have hS : ShpOk cfg20.p (Har.shapesOf cfg20 data20) (streamLanes P20) (Har.phaseByte P20 .tape + 24) := by
    rw [cfg20_p, shapes20]; exact shpOk_P20
  obtain ⟨htT, hpubT, hpubτ, hRmax, hnf, hzL, hP4⟩ := hS
  refine harStatic_of harNum20 ?_ ?_ ?_ htT hpubT hpubτ hRmax hnf hzL hP4 ?_ ?_
  · rw [cfg20_p]; exact Q1.layOk_15
  · rw [cfg20_p]; exact Q1.layOk_11
  · rw [cfg20_p, sizes_P20.2.2.2.2.2.2.2.2]; exact okE_P20 _ _
  · rw [cfg20_p]; exact (Har.lay20 (Har.posBase cfg20) (Har.pwBase cfg20)).1
  · rw [cfg20_p]; exact (Har.lay20 (Har.posBase cfg20) (Har.pwBase cfg20)).2.1

/-! ## `NodeBase` of the `P20` node program -/

/-- The tables' heights (`NodeBase`'s `hτ'`, from `hτT20` and `hT20`). -/
theorem hτL20 : ∀ x, ∀ t ∈ lvmTabs Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20),
    t.τ ≤ lay26.μ :=
  fun x t ht => hτT20 x t (by rw [hT20]; exact ht)

/-- The aux tables after Q_sig's six `BITS` tables (`haux20`): the position classes, the `s'` shifts. -/
abbrev rest20 : List Tab :=
  ((posSpecs cfg20 fun c => bplOf data20 (6 + c)) ++ [sSpec cfg20 (bplOf data20 (6 + nPosCls cfg20)),
    powSpec cfg20 (bplOf data20 (7 + nPosCls cfg20))]).map
    BitsTab.BSpec.tab

/-- **QL's `hinb`** for the `P20` node program (INB's `hinb20` with A24's `hna`). -/
theorem hinbL20 (S : StaticFacts) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS M3.tabsP20) hτT20 x qm qr →
      (Q20n.interp (inKOf Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20) lay26 (hτL20 x)
        (stackOf lay26 qm qr)) (inEOf Q20n (plOf data20) data20.groups (arrs20 x) (aux cfg20 data20) lay26
        (hτL20 x) (stackOf lay26 qm qr))).inb = true :=
  hinb20 (D := data20) (hτ' := hτL20) hT20 (hst20 S) hQ20 hqlt20 posCellsLt20 S.hna

theorem hnk20 : hashedLen P20 / 8 + 5 ≤ nK cfg20 := by
  have h := hashedLen_nK20; rw [show cfg20.p = P20 from rfl] at h; exact h

/-- **FIN-BV's memory facts** at the `P20` node program. -/
theorem bv20 (S : StaticFacts) : BVFacts hτL20 hτT20 where
  sb vk c x qm qr P := sBits20 hT20 (hst20 S) (hinbL20 S) hbs20 vk c x qm qr P.ok P.b1 P.good
  nb vk c x qm qr P := nBits20 hT20 (hst20 S) (hinbL20 S) haux20 hR20 hP20 vk c x qm qr P.ok P.b1 P.good
  n1 vk c x qm qr P :=
    n1_20 hT20 (hst20 S) (hinbL20 S) hS20 haux20 hR20 hP20 vk c x qm qr P.ok P.b1 P.good P.inm P.ll
  nN vk c x qm qr P :=
    nN_20 hT20 (hst20 S) (hinbL20 S) hS20 haux20 hR20 hP20 vk c x qm qr P.ok P.b1 P.good P.inm P.ll
  pw vk c x qm qr P := pw20 hT20 (hst20 S) (hinbL20 S) hS20 hnk20 powStatic20.1 powStatic20.2.1
    powStatic20.2.2 vk c x qm qr P.ok P.b1 P.good
  posr vk c x qm qr P := posOkR20 hT20 (hst20 S) (hinbL20 S) hS20 hQ20 posCellsLt20 posLanesR20 vk c x qm qr
    P.ok P.b1 P.good P.inm P.ll
  posm vk c x qm qr P := posOkM20 hT20 (hst20 S) (hinbL20 S) hS20 hQ20 posCellsLt20 posLanesM20 vk c x qm qr
    P.ok P.b1 P.good P.inm P.ll

/-- **`NodeBase` for WP-16a's `P20` node program** from A24's facts. -/
theorem nodeBase20 (S : StaticFacts) :
    NodeBase (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 (plOf data20) data20.groups arrs20
      (aux cfg20 data20) hτL20 (bplOf data20) rest20 (pbB cfg20) M3.tabsP20 where
  hT := hT20
  hst := hst20 S
  hlay := hlay20
  hτT := hτT20
  hS := hS20
  hQ := hQ20
  hws := hws20
  hfg := hfg20
  hln := hln20
  hqlt := hqlt20
  hpos := hpos20 hT20 (hst20 S) (hinbL20 S) hlay20 hS20 hQ20 hSt20 posCellsLt20
  hNs := hNs20
  haux := haux20
  hR := hR20
  hP := hP20
  hSt := hSt20
  hhd := hhd20
  hSg := hSg20
  hX := hX20
  hY := hY20
  hyc := hyc20
  hyls := hyls20
  hyns := hyns20
  hMd := hMd20
  hPub := hPub20
  hfl := hfl20
  hvkI := hvkI20
  hcLI := hcLI20
  hslI := hslI20
  harith := harith20 harStatic20 S (bv20 S)

/-! ## The certificate -/

theorem subG_true : subG true Lvm.VS20 = Lvm.T.submission := rfl

/-- **The certificate of the guarded submission** from the open obligations under `b = true`. -/
theorem certificateR_guard {b : Bool} (h : b = true → Lvm.T.Open) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subG b Lvm.VS20) :=
  certificateR_guardT Lvm.M3.tabsP20 h

/-- The compiled guarded submission (`VS20F`, V-PERF) is the specified one. -/
theorem subG_F (b : Bool) : subG b Lvm.VF.VS20F = subG b Lvm.VS20 := by rw [Lvm.VF.VS20F_eq]

/-- **The open obligations** from A24's facts. -/
noncomputable def openFin (S : StaticFacts) : Lvm.T.Open :=
  openS_of ⟨midHyp20 S, accMidHyp_P20 (midHyp20 S), fun vk =>
    node_of (nodeHyp20 (nodeBase20 S) posCellsLt20 S.hna) fixStatic_P20 (midHyp20 S).hτ vk⟩

/-- **The certificate of the guarded submission** against the declared claim. -/
theorem certificateFin :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subG staticOkB VF.VS20F) := by
  rw [subG_F]
  exact certificateR_guard fun h => openFin (staticFacts h)

end Lvm.Fin
