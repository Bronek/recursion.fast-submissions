-- New for lvm (AC-N, A23 §12.6 "Node level"): `NodeSound` with the split arithmetic hypothesis.
-- Q_arith's segments now give `decideCore` on the child's stream and that the child's folded
-- accumulator is the statement's incoming one (`accOutOf Σ' = acc_in`); the good pair carries
-- `AccOk acc_in`; together they are the child's `decideF` (AC-V's `decideF_eq`), and WP-14c's
-- `nodeSound_layout` does the rest.
import LvmNodeSoundLayout
import LvmAccNodePub

/-!
# `NodeSound` with the accumulator

* `accOk_congr`, **`decideF_of_core`**: `decideF = decideCore ∧ AccOk (accOutOf Σ)`, and `AccOk`
  reads the header only through the fixed columns' closed forms (`M3.fixVals`), which are the same
  polynomial for every header (`FixStatic`: `Φ` is one polynomial);
* **`AccIn m x`**: the statement's incoming accumulator holds (`AccOk (pubX x).accIn`);
  **`GoodNA m T hτ`** `= GoodN T hτ ∧ AccIn m` (BLUEPRINT §12.6: `Good := GoodN ∧ AccOk (accIn x)`);
* **`nodeSound_acc`**: `NodeSound (VS P20 m) vk (GoodNA m T hτ) childS` from `nodeSound_layout`'s
  static, placement and Q_link hypotheses, `FixStatic`, and **`harith` in A23's form**: Q_arith's
  segments (with the input map, `LaneLink`, `LinkOk`) ⇒ `decideCore P20 m vk c_L Σ' = true ∧
  accOutOf P20 m vk c_L Σ' = (pubX x).accIn`.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits LeanVM.Protocol
open Lvm.VEq (pubX)

/-! ## `decideF` from `decideCore` and the accumulator -/

/-- `AccOk` reads the header only through the closed forms of `fixCols`. -/
theorem accOk_congr {P : Params} {m : M3} {pub pub' : Pub} (h : m.fixVals pub = m.fixVals pub')
    (a : Acc) : AccOk P m pub a = AccOk P m pub' a := by
  unfold AccOk PhiC; rw [h]

/-- **The child's `decideF`** from `decideCore`, its folded accumulator being `pub.acc_in`, and
`AccOk pub.acc_in`, when the closed forms do not depend on the header. -/
theorem decideF_of_core {P : Params} {m : M3} {vk c : RecursionFast.Digest} {sig : ByteArray} {pub : Pub}
    (hΦ : m.fixVals (pubOf vk c sig) = m.fixVals pub) (hc : decideCore P m vk c sig = true)
    (ha : accOutOf P m vk c sig = pub.accIn) (hA : AccOk P m pub pub.accIn = true) :
    decideF P m vk c sig = true := by
  rw [decideF_eq, hc, ha, accOk_congr hΦ, hA]; rfl

/-- `FixStatic` of the real instance: its closed forms do not depend on the header. -/
theorem fixVals_real (p : Params) (tabs : Pub → List Tab) (h : FixStatic p tabs) (pub pub' : Pub) :
    (M3.real p tabs).fixVals pub = (M3.real p tabs).fixVals pub' := (h pub pub').2

/-! ## The good pair with the accumulator -/

/-- **The statement's incoming accumulator holds** (A23: `AccOk (accIn x)`, a header fact). -/
def AccIn (m : M3) (x : List UInt8) : Prop := AccOk P20 m (pubX x) (pubX x).accIn = true

/-- **The good candidate pair** (A23, BLUEPRINT §12.6): WP-14c's `GoodN` and `AccIn`. -/
def GoodNA (m : M3) (T : List UInt8 → List Tab) (hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ) : GoodRel :=
  fun x qm qr ↦ GoodN T hτ x qm qr ∧ AccIn m x

/-! ## `NodeSound` -/

section Acc

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}

/-- **`NodeSound` for the node program with A23's accumulator**: `nodeSound_layout`'s hypotheses,
`hΦ` (the closed forms of `fixCols` are the same for every header; `FixStatic` for `M3.real`), and
`harith` in the new form, Q_arith's only arithmetic hypothesis. -/
theorem nodeSound_acc (m : M3) (vk : RecursionFast.Digest)
    {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}
    (hΦ : ∀ pub pub', m.fixVals pub = m.fixVals pub')
    (hT : ∀ x, T x = lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux)
    (hst : ∀ x, AuxStatic lay I qa nK nE pl groups aux (arrsX x))
    (hlay : ∀ x, LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux))
    (hinb : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn lay I qa nK nE).interp (inKOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
        (stackOf lay26 qm qr)) (inEOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
        (stackOf lay26 qm qr))).inb = true)
    (hS : StreamOk P20) (hQ : QOk P20 lay) (hws : 2 ^ lay.m ≤ 17 * 2 ^ 14) (hfg : lay.fg = I.flag)
    (hln : I.ln = 20)
    (hqlt : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ y < (qltData P20 lay).length,
        (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (lay.qt + y) = (qltData P20 lay).getD y 0)
    (hpos : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ k < (opens P20).length, ∀ j < ((opens P20).getD k default).L.t,
        ∀ z < ((opens P20).getD k default).L.height,
        (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k
            (bitBase P20 lay k + ((opens P20).getD k default).L.height * j + z) =
          if ansBit P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) (((opens P20).getD k default).pe + j / 8)
            (j % 8 * ((opens P20).getD k default).L.height + z) then 1 else 0)
    (hNs : lay.sb + 2 ^ lay.m ≤ max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E))
    (bpl : ℕ → ℕ → Bool × ℕ) (rest : List Tab)
    (haux : aux = (sigSpecs I (qsig I (p1 lay nK nE)).1 bpl).map BitsTab.BSpec.tab ++ rest)
    (hR : SigRegLt ((Qn lay I qa nK nE).cells .K) I)
    (hP : (p2 lay I nK nE).k ≤ (Qn lay I qa nK nE).cells .K)
    (hSt : ∀ x, Bundle (arrsX x) 17 14 lay.sb true fun l => l * 2 ^ 14) (hhd : I.hd = lay.sb + 11)
    (hSg : ∀ x, Bundle (arrsX x) 1 10 I.sg true fun _ => 17 * 2 ^ 14)
    (hX : ∀ x, Bundle (arrsX x) 17 9 I.xs false fun l => CMain.xOff20 + l * 2 ^ 14)
    (hY : ∀ x, Bundle (arrsX x) 4 9 I.ys false fun l => CMain.ksOff20 + 2 ^ 15 * (50 + l) + 2 ^ 14)
    (hyc : I.yc = I.ys + 4 * 430) (hyls : I.yls = I.ys + 4 * 447) (hyns : I.yns = I.ys + 4 * 448)
    (hMd : ∀ x, Bundle (arrsX x) 4 0 I.md false
      fun l => CMain.ksOff20 + 2 ^ 15 * (50 + l) + (spongeBlocks P20 - 1))
    {pb : ℕ} (hPub : ∀ x, PubAt (arrsX x) x pb) (hfl : I.flag = pb) (hvkI : I.vk = pb + 1)
    (hcLI : I.cL = pb + 5) (hslI : I.sl = pb + 18)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) → LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) →
      Ok (ctxOf (Qn lay I qa nK nE)) (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr) qa
        (p2 lay I nK nE) →
      decideCore P20 m vk (hdrOf x).cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = true ∧
        accOutOf P20 m vk (hdrOf x).cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) =
          (pubX x).accIn) :
    NodeSound (VS P20 m) vk (GoodNA m T hτ) childS :=
  nodeSound_layout m vk (fun _ _ _ h ↦ h.1) hT hst hlay hinb hS hQ hws hfg hln hqlt hpos hNs bpl rest
    haux hR hP hSt hhd hSg hX hY hyc hyls hyns hMd hPub hfl hvkI hcLI hslI
    fun c x qm qr hok hb hG mp hLL hlink hOk ↦
      have h := harith c x qm qr hok hb hG.1 mp hLL hlink hOk
      decideF_of_core (hΦ _ _) h.1 h.2 hG.2

end Acc

end Lvm.NS
