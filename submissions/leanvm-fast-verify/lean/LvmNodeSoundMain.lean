-- WP-14c (NodeSound, O10). New for lvm: `NodeSound` for `GoodN`, generic over the node program's
-- parts and its input map (BLUEPRINT §4.6, §7.1 row 4, A19); every remaining hypothesis is named
-- with its owner.
import LvmNodeSoundCirc
import LvmNodeSoundGood
import LvmNodeSoundTr
import LvmNodeSoundKS
import LvmNodeSoundHdr
import LvmCertSNodeBits

/-!
# `NodeSound` for the node program

**`nodeSound_main`**: `NodeSound (VS P20 m) vk Good childS` (any `Good` that implies `GoodN T hτ`;
A23's `GoodA`, `LvmAccNode`) for the node program
`Q = toProgram nK nE (qprog lay I qa)` (Q_link, Q_sig, Q_arith) on the tables
`lvmTabs Q pl groups (arrsX x) aux` (the input arrays depend on the statement through `PUB`), from:

| hypothesis | content | owner |
|---|---|---|
| `hT` | `T x` (O6's `sumcheckTabs (tabs (pubX x))`) is the node program's tables | final assembly (`lvmTabsC_eq`, filter = id) |
| `hst` | `AuxStatic`: `wf`, `GrpOk`, `InOk`, aux seed nothing, read columns inside widths, read count, `GInj` | final assembly (decided: `segsOk`, `grpOkCore`, `inOkB`, `tabsOkB`) |
| `hinb` | the interpreter's `inb` on the committed inputs (`b = 1`) | QL (position bits are bits + `QOk`'s bounds) |
| `hS`, `hQ`, `hws`, `hNs`, `hfg` | Q_link's static checks, its stream region inside the cells, one gate cell for Q_link and Q_sig | QL (decided per layout) |
| `hqlt` | Q_link's `QLT` cells hold the static table `qltData` | QL / INT-2 (a static input kind, QL's proposal) |
| `hpos` | Q_link's position-bit cells are the answers' bits (QIn.bits) | QL (its position `BITS` tables, as `sigBitsOk` for Q_sig) |
| `rest`, `haux`, `hR`, `hP` | `aux` starts with Q_sig's six `BITS` tables; their input regions (14 bounds) and Q_sig's segment lie below the cell count (then `SigTabsIn`, `SigCellsLt` by `LvmCertSNodeBits`) | final assembly (decided on the layout) |
| `hmap` | `InMapN`: the stream lanes, the flag, the `KS` `X`/`Y` cells (values of the committed pair; `SigKSin` and the trace digest then follow from `GoodK`, `LvmNodeSoundKS`), the `PUB` cells, `σ'`'s cells, the child header's cells | input map: `inKOf_pub`/`inKOf_com` on the concrete arrays |
| `harith` | Q_arith's segments on the committed memory, with the input map and Q_link's `LaneLink`/`LinkOk`, for a `Good` pair ⇒ `decideF … = true` (A23: from `decideCore` and `accOutOf = acc_in`, `LvmAccNode.nodeSound_acc`) | Q_arith (`Q_arith_eq`): HAR, AC-Q |
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits LeanVM.Protocol

/-! ## `okS` facts -/

theorem okS_vk {vk c : RecursionFast.Digest} {x : List UInt8} (hok : okS vk c x = true) :
    (hdrOf x).vk = vk := by
  unfold okS at hok
  generalize hdrOf x = hd at hok ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.1.1.2

theorem okS_sig {vk c : RecursionFast.Digest} {x : List UInt8} (hok : okS vk c x = true)
    (hb : (hdrOf x).b = 1) : SigOk vk (traceDigest []) (hdrOf x).sig = true := by
  unfold okS at hok
  generalize hdrOf x = hd at hok hb ⊢
  simp only [Bool.and_eq_true, hb, one_ne_zero, if_false] at hok
  exact hok.2.2

/-- Transport of `M3Holds` along an equality of the tables. -/
theorem m3Holds_congr {L : Lay} {t t' : List Tab} (h : t = t') {hτ : ∀ u ∈ t, u.τ ≤ L.μ}
    {hτ' : ∀ u ∈ t', u.τ ≤ L.μ} {q : Column L.μ} (hm : M3Holds (inst L t hτ) () q) :
    M3Holds (inst L t' hτ') () q := by
  subst h; exact hm

/-! ## The header's lanes (the `PUB` values) -/

/-- The statement's bytes where the header reader finds them (`hdrOf x = Header.ofProof (hdrBytesX x)`). -/
def hdrBytesX (x : List UInt8) : ByteArray := ⟨(List.replicate 8 0 ++ x).toArray⟩

/-- **Header lane `k`** of a statement: the little-endian word at byte `8 + 8k`. -/
def hdrLane (x : List UInt8) (k : ℕ) : FK := ⟨UInt64.ofNat (u64At (hdrBytesX x) (8 + 8 * k))⟩

/-! ## The node program's hypotheses -/

section Main

variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)
  (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrsX : List UInt8 → List InArr) (aux : List Tab)
  (hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ)

/-- **`AuxHyps` without `M3Holds` and `inb`**: the static checks (decided on the concrete program). -/
structure AuxStatic (arrs : List InArr) : Prop where
  wf : (Qn lay I qa nK nE).wf = true
  grp : GrpOk (Qn lay I qa nK nE) groups
  inOk : InOk (Qn lay I qa nK nE) arrs
  auxSeeds : ∀ t ∈ aux, t.seeds = []
  cnt : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w
  len : nReads (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux) < 2 ^ 64 - 1
  inj : GInj (max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E))

/-- The memory of the node program on the pair `(qm, qr)` of statement `x`. -/
noncomputable abbrev memX (x : List UInt8) (qm : Column 26) (qr : Column 19) : Mem :=
  memN lay I qa nK nE pl groups (arrsX x) aux lay26 (hτ' x) (stackOf lay26 qm qr)

/-- **The input map** (A19) on the committed memory of a node statement `x` (`b = 1`) and a pair:
where each part's inputs are and what they hold. -/
structure InMapN (vk : RecursionFast.Digest) (x : List UInt8) (qm : Column 26) (qr : Column 19) : Prop where
  /-- The stream lanes (Q_link's and Q_sig's stream region; `C_rec`'s stream columns). -/
  stream : ∀ j < 2 ^ lay.m, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (lay.sb + j) =
    laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j
  /-- Q_sig's gate is on. -/
  flag : (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.flag = 1
  /-- `KS`'s `X` message lanes (rows `2^14 + r`) on Q_sig's message cells (A19 route (a)). -/
  xs : ∀ r < 449, ∀ l < 17, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.xs + 17 * r + l) =
    FK.ofBF64 (msgX qm r l)
  /-- `KS`'s output lanes `0 … 3` on Q_sig's digest cells: chain steps, key leaf and path, the two
  statements. -/
  ys : ∀ r < 399, ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.ys + 4 * r + l) =
    FK.ofBF64 (Yq qm (2 ^ 14 + r) l)
  yc : ∀ t ≤ 16, ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.yc + 4 * t + l) =
    FK.ofBF64 (Yq qm (2 ^ 14 + 430 + t) l)
  yls : ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.yls + l) =
    FK.ofBF64 (Yq qm (2 ^ 14 + 447) l)
  yns : ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.yns + l) =
    FK.ofBF64 (Yq qm (2 ^ 14 + 448) l)
  /-- `PUB`: the key, the left statement, the leaf signature. -/
  vk : digAt (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.vk = vk
  cL : digAt (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.cL = (hdrOf x).cL
  sl : sigAt' (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.sl = (hdrOf x).sig
  /-- The trace-digest cells: `KS` row `B − 1`'s output lanes `0 … 3`. -/
  md : ∀ l < 4, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.md + l) =
    FK.ofBF64 (Yq qm (spongeBlocks P20 - 1) l)
  /-- `σ'`'s cells: `C_rec`'s column 17. -/
  sg : sigAt' (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k I.sg =
    Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr))
  /-- Q_sig's child-header cells are the stream's lanes `11 …`. -/
  hd : ∀ k < 615, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.hd + k) =
    laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k)
  /-- (A23) the whole `PUB` array from `I.flag`: the header's 702 lanes, `acc_in`'s 87 among them
  (`LvmAccNodePub`: `hdrLanes x = (pubX x).hdrLanes`; Q_acc reads the current `acc_in` there). -/
  pub : ∀ j < pubLanes, (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (I.flag + j) = hdrLane x j

variable {lay I qa nK nE pl groups arrsX aux hτ'}

/-- **`NodeSound` for the node program** (see the module docstring for the hypotheses). -/
theorem nodeSound_main (m : M3) (vk : RecursionFast.Digest)
    {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ} {Good : GoodRel}
    (hGood : ∀ x qm qr, Good x qm qr → GoodN T hτ x qm qr)
    (hT : ∀ x, T x = lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux)
    (hst : ∀ x, AuxStatic lay I qa nK nE pl groups aux (arrsX x))
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
    (hmap : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr)
    (harith : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → Good x qm qr →
      InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) → LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) →
      Ok (ctxOf (Qn lay I qa nK nE)) (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr) qa
        (p2 lay I nK nE) →
      decideF P20 m vk (hdrOf x).cL (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = true) :
    NodeSound (VS P20 m) vk Good childS := by
  refine nodeSound_of (fun c x qm qr hok hG ↦ chain_of_goodN hok (hGood _ _ _ hG))
    fun c x qm qr hok hb hG' ↦ ?_
  have hG := hGood _ _ _ hG'
  have st := hst x
  have H : AuxHyps (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x) (stackOf lay26 qm qr) :=
    ⟨st.wf, st.grp, st.inOk, st.auxSeeds, st.cnt, st.len, st.inj,
      m3Holds_congr (hT x) hG.1, hinb c x qm qr hok hb hG⟩
  have mp := hmap c x qm qr hok hb hG
  have hwsl : 2 ^ lay.m ≤ (wsOf (Lvm.X.laneOf (wOfCol qr))).length := by
    rw [wsOf, List.length_map, List.length_range]; exact hws
  have hqin : QIn P20 lay (wsOf (Lvm.X.laneOf (wOfCol qr)))
      (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr) :=
    ⟨by rw [hfg]; exact mp.flag, mp.stream, hqlt c x qm qr hok hb hG, hpos c x qm qr hok hb hG⟩
  obtain ⟨hLL, hlink, hpad⟩ := link_of_aux H hS hQ hqin hwsl hNs
  have hks := sigKSin_of_goodK hG.2 mp.xs mp.ys mp.yc mp.yls mp.yns
  have hTabs : SigTabsIn I (qsig I (p1 lay nK nE)).1 bpl aux := by
    rw [haux]; exact sigTabsIn_append _ _ bpl rest
  obtain ⟨hsig, hchild⟩ := sig_of_aux H mp.flag hks bpl hTabs (sigCellsLt_qsig bpl hR hP) hln
  have hmd := (digAt_of_cells mp.md).trans (traceDigest_of_goodK hG.2 hLL hpad)
  have har := harith c x qm qr hok hb hG' mp hLL hlink (parts_of_aux H).2.2
  exact accV_childW_of hdrBridge trBridge m (wOfCol qr) hlink har hsig hchild hln mp.vk mp.cL mp.sl hmd mp.sg
    mp.hd (okS_sig hok hb)

end Main

end Lvm.NS
