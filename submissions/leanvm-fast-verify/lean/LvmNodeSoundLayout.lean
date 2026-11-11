-- WP-14c (NodeSound, O10). New for lvm: `NodeSound` with the input map discharged from the input
-- arrays' placement (`LvmNodeSoundIn.inMapN_of`): what is left are layout facts, QL's Q_link
-- facts and Q_arith.
import LvmNodeSoundIn

/-!
# `NodeSound` from the layout

**`nodeSound_layout`** is `nodeSound_main` with `hmap` (the input map) replaced by the placement of the
input arrays (A19): the stream as a 17-bundle on `C_rec` (lane `j` at `sb + j`, column `j mod 17`),
`σ'` on `C_rec`'s column 17, the `KS` `X` lanes as a 17-bundle on `C_main`, `KS`'s output lanes 0–3
of rows `[2^14, 2^14 + 2^9)` as a 4-bundle (Q_sig's digest regions at fixed offsets in it), the
trace-digest row `B − 1` as a 4-bundle, and the `PUB` array of the header's 615 lanes (`hdrLanes x`)
with Q_sig's `flag`, `vk`, `c_L`, `σ_leaf` regions in it. Every hypothesis is now a static fact of
the assembled program (decidable), one of QL's Q_link facts, or Q_arith.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits LeanVM.Protocol

section Layout

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}

/-- **`NodeSound` for the node program, the input map from the arrays' placement.** -/
theorem nodeSound_layout (m : M3) (vk : RecursionFast.Digest)
    {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ} {Good : GoodRel}
    (hGood : ∀ x qm qr, Good x qm qr → GoodN T hτ x qm qr)
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
    -- the input arrays' placement (A19)
    (hSt : ∀ x, Bundle (arrsX x) 17 14 lay.sb true fun l => l * 2 ^ 14) (hhd : I.hd = lay.sb + 11)
    (hSg : ∀ x, Bundle (arrsX x) 1 10 I.sg true fun _ => 17 * 2 ^ 14)
    (hX : ∀ x, Bundle (arrsX x) 17 9 I.xs false fun l => ksY2 + 2 ^ 19 + l * 2 ^ 14)
    (hY : ∀ x, Bundle (arrsX x) 4 9 I.ys false fun l => 50 * 2 ^ 20 + 2 ^ 15 * (50 + l) + 2 ^ 14)
    (hyc : I.yc = I.ys + 4 * 430) (hyls : I.yls = I.ys + 4 * 447) (hyns : I.yns = I.ys + 4 * 448)
    (hMd : ∀ x, Bundle (arrsX x) 4 0 I.md false
      fun l => 50 * 2 ^ 20 + 2 ^ 15 * (50 + l) + (spongeBlocks P20 - 1))
    {pb : ℕ} (hPub : ∀ x, PubAt (arrsX x) x pb) (hfl : I.flag = pb) (hvkI : I.vk = pb + 1)
    (hcLI : I.cL = pb + 5) (hslI : I.sl = pb + 18)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → Good x qm qr →
      InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) → LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) →
      Ok (ctxOf (Qn lay I qa nK nE)) (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr) qa
        (p2 lay I nK nE) →
      decideF P20 m vk (hdrOf x).cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = true) :
    NodeSound (VS P20 m) vk Good childS :=
  nodeSound_main m vk hGood hT hst hinb hS hQ hws hfg hln hqlt hpos hNs bpl rest haux hR hP
    (fun c x qm qr hok hb hG ↦
      have st := hst x
      inMapN_of ⟨st.wf, st.grp, st.inOk, st.auxSeeds, st.cnt, st.len, st.inj,
          m3Holds_congr (hT x) hG.1, hinb c x qm qr hok hb hG⟩ (hlay x) hws (hSt x) hhd (hSg x) (hX x)
        (hY x) hyc hyls hyns (hMd x) (hPub x) hfl hvkI hcLI hslI hb (okS_vk hok))
    harith

end Layout

end Lvm.NS
