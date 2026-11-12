-- WP-14c (NodeSound, O10). New for lvm: the left child's acceptance from what the circuit's memory
-- gives, part by part (Q_link, Q_sig, Q_arith) and through the input map (BLUEPRINT §4.6, A19).
import LvmNodeSound
import LvmQLinkBridge
import LvmQLinkSound
import LvmQSigSound
import LvmPlanP20

/-!
# The left child from the circuit's memory

`ws = wsOf W` are the stream lanes of the child (`W = laneOf w`: lane `u` at `C_rec` word
`crecIdx u`; `17·2^14` lanes, `streamCap P20`). In a memory `M` where the circuit's parts hold with
the gate on, **`accV_childW_of`** gives the acceptance of the child `childW w` under `c_L` from
exactly what each part provides:

| hypothesis | what | owner |
|---|---|---|
| `hlink` | `LinkOk P20 (decode P20 ws)` | Q_link: QL's `qlink_sound` + `linkOk_of_laneLink` |
| `harith` | `decideF P20 m vk c_L (traceBytesB (decode P20 ws)) = true` | Q_arith (`Q_arith_eq`): QA1/QA2/QL |
| `hsig`, `hchild` | `SigOk` on the digest cells, `ChildOk` | Q_sig: WP-12 `qsig_sound_in` |
| `hvk`, `hcL`, `hsl` | the `PUB` cells: `vk`, `c_L`, `σ_leaf` | input map (A19, `inKOf_pub`) |
| `hmd` | the trace-digest cells are `traceDigest` of the decoded trace | `KS` (WP-8 `traceDigest_of_KS`) + input map |
| `hsg` | the `σ'` cells are `C_rec`'s column 17 | input map (`C_rec` input array) |
| `hhd` | Q_sig's child-header cells are stream lanes `11 …` | layout (`I.hd = sb + 11`) |
| `htr` | `readTraceL W = decode P20 (wsOf W)` (WP-13a's reader = QL's) | WP-14c |
| `hparse` | `ChildOk` with the `PUB` cells ⇒ `parseOk` on the reassembled child | WP-14c |
| `hσl` | `σ_leaf` signs `traceDigest []` | `V`'s native check (`okS`, `b = 1`) |
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig

/-- **The child's stream lanes**: `17·2^14` lanes of `W` (`C_rec`'s stream columns). -/
def wsOf (W : ℕ → Word) : List Word := (List.range (17 * 2 ^ 14)).map W

/-- Every planned query is within `queryCap` (the plan's one-pass decision, `LvmPlanP20`). -/
theorem planCap_P20 : ((plan P20).all fun e => decide (e.len ≤ queryCap)) = true :=
  List.all_eq_true.mpr fun e he => decide_eq_true (Lvm.PlanChk.cap_P20 e he)

theorem planCap_P20' : ∀ i < (plan P20).length, ((plan P20).getD i default).len ≤ queryCap := by
  intro i hi
  have h := List.all_eq_true.mp planCap_P20 _ (List.getElem_mem hi)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h

/-- **The header bridge** (stated here; proved in `LvmNodeSoundHdr`): Q_sig's `ChildOk` on the
stream's header lanes, with the `PUB` cells, is `V_S`'s native check on the reassembled child. -/
def HdrBridge : Prop :=
  ∀ (M : Mem) (I : SigIn) (ws : List Word) (vk cL : RecursionFast.Digest) (σl : Sig),
    LinkOk P20 (decode P20 ws) → hashedLen P20 ≤ 8 * ws.length →
    (∀ k < 615, M.k (I.hd + k) = laneK ws (11 + k)) → ChildOk I M.k → I.ln = 20 →
    digAt M.k I.vk = vk → digAt M.k I.cL = cL → sigAt' M.k I.sl = σl →
    SigOk vk (traceDigest []) σl = true →
    parseOk P20 vk cL (reassemble P20 (decode P20 ws)) = true

/-- **The trace bridge** (stated here; proved in `LvmNodeSoundTr`): WP-13a's reader of the stream
lanes is QL's `decode`. -/
def TrBridge : Prop := ∀ W : ℕ → Word, Lvm.X.readTraceL W = decode P20 (wsOf W)

/-- **The left child is accepted** (generic in the M3 instance `m` of `V_S`). -/
theorem accV_childW_of (hH : HdrBridge) (hT : TrBridge) (m : M3) {M : Mem} {I : SigIn}
    (w : ℕ → Word) {vk cL : RecursionFast.Digest} {σl : Sig}
    (hlink : LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf w))))
    (harith : decideF P20 m vk cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf w)))) = true)
    (hsig : SigOk (digAt M.k I.vk) (digAt M.k I.md) (sigAt' M.k I.sg) = true)
    (hchild : ChildOk I M.k) (hln : I.ln = 20)
    (hvk : digAt M.k I.vk = vk) (hcL : digAt M.k I.cL = cL) (hsl : sigAt' M.k I.sl = σl)
    (hmd : digAt M.k I.md = traceDigest (decode P20 (wsOf (Lvm.X.laneOf w))))
    (hsg : sigAt' M.k I.sg = Lvm.X.sigOfF (Lvm.X.sigCol w))
    (hhd : ∀ k < 615, M.k (I.hd + k) = laneK (wsOf (Lvm.X.laneOf w)) (11 + k))
    (hσl : SigOk vk (traceDigest []) σl = true) :
    accV (VS P20 m) vk cL (childW w) = true := by
  have hws : hashedLen P20 ≤ 8 * (wsOf (Lvm.X.laneOf w)).length := by
    rw [wsOf, List.length_map, List.length_range, sizes_P20.2.2.2.2.2.1]; norm_num
  unfold childW
  rw [hT]
  refine accV_reassemble P20 m vk cL _ _ planOk_P20 (by rw [plan_P20]; decide) planCap_P20'
    (by rw [sizes_P20.1]; norm_num) hlink
    (hH M I _ vk cL σl hlink hws hhd hchild hln hvk hcL hsl hσl) harith ?_
  rw [← hsg, ← hmd, ← hvk]
  exact hsig

end Lvm.NS
