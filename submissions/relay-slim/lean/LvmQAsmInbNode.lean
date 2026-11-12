-- New for lvm (INB): WP-14c's `hinb` (`nodeSound_layout`) for the node program, generic over its
-- parts as `nodeSound_layout` is. The route: the seed (committed) memory satisfies every row
-- (WP-10 `holds_seedMem`, no `inb`), its `readd` addresses are in region (`qlink_in`; Q_sig and
-- Q_arith have no `readd`), so the interpreter finds every cell (`inb_of_mem`).
import LvmQAsmInbLink
import LvmQAsmInbSite
import LvmQAsmInbBits
import LvmNodeSoundMain

/-!
# `hinb` for the node program

**`hinb_node`**: for `Q = Qn lay I qa nK nE` on the tables `lvmTabs Q pl groups (arrsX x) aux`, for
every statement `x` with `b = 1` and every pair meeting `GoodN`, `(Q.interp inK inE).inb = true`
(`inK`, `inE` read off the pair's stack), in exactly `nodeSound_layout`'s form. Hypotheses, all
static except `hqlt` (`nodeSound_layout`'s own):

* `hT`, `hst` (`AuxStatic`), `hQ` (`QOk P20 lay`): `nodeSound_layout`'s;
* `hqlt`: `nodeSound_layout`'s (Q_link's `QLT` cells hold `qltData`), with `hqtK` (those cells are
  inputs);
* `hcov`: every cap bit cell of every padded position of every opening is a `bit` output of a real
  row of a `BITS` table in `aux` whose cells are inside `Q` (the position classes);
* `hsig`, `harr`: Q_sig's and Q_arith's segments have no `readd` (decided).

No `inb` is used: the proof runs on the seed memory (`holds_seedMem`), and the `BITS` outputs are
read there (`out_sound0`). The bits are needed for *every* padded position because the cap loops
run every iteration of a chunk (only their assertions are gated).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open Lvm.SigBits Lvm.BitsTab Lvm.Inb LeanVM.Protocol

/-! ## Any parameter set -/

/-- The node program's shape for parameter set `p` (`qprog` at `P20`, `QAsm.qprogC`). -/
def qprogP {α : Type} (p : Params) (lay : Layout) (I : SigIn) (qa : BM α) : BM α := do
  qlink p lay
  let _ ← qsig I
  qa

/-- **The position classes cover the cap bits**: every bit cell of every (padded) position of every
opening is a `bit z` output of a real row of a `BITS` table in `aux`, its cells inside `Q`. -/
def CapCov (p : Params) (Q : Program) (lay : Layout) (aux : List Tab) : Prop :=
  ∀ k < (opens p).length, ∀ j < padT ((opens p).getD k default).L.t,
    ∀ z < ((opens p).getD k default).L.height,
    ∃ S : BitsTab.BSpec, S.tab ∈ aux ∧ S.n ≤ 2 ^ S.τ ∧ ∃ x < S.n,
      (S.rd = true → S.wc x < Q.cells .K) ∧ (∀ jo < S.outs.length, S.oc jo x < Q.cells .K) ∧
      ∃ jo < S.outs.length, ∃ z' < 64, S.out jo = .bit z' ∧
        S.oc jo x = bitBase p lay k + ((opens p).getD k default).L.height * j + z

/-! ## Any builder program: `inb` from the seed memory's `readd`s -/

section Seed

variable {α : Type} {m : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (toProgram nK nE m) pl groups arrs aux, t.τ ≤ L.μ}

/-- The seed (committed) memory of a stack `q`. -/
noncomputable abbrev seedOf (q : Column L.μ) : Loop.Mem :=
  (toProgram nK nE m).seedMem (witOf (toProgram nK nE m) pl groups arrs aux L hτ q)
    (inKOf (toProgram nK nE m) pl groups arrs aux L hτ q) (inEOf (toProgram nK nE m) pl groups arrs aux L hτ q)

theorem seedOf_inK (q : Column L.μ) {n : ℕ} (hn : n < nK) :
    (seedOf (m := m) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux) (hτ := hτ) q).k n =
      (inKOf (toProgram nK nE m) pl groups arrs aux L hτ q).getD n 0 := by
  show (if n < nK then _ else _) = _; rw [if_pos hn]

/-- **`inb` from the seed memory**: for any gadget `m`, if its segments' `readd`s are in region in
the seed memory whenever its rows hold there, the interpreter finds every cell. Each part of a node
program proves its `SegsIn` (by `InOk` lemmas: `qlink_in`, `readdBits_in`, `loop_in`, or
`segsIn_of_noReadd`), using the seed memory's facts (`seedOf_inK`, `seedK_bit`). -/
theorem inb_of_seed {q : Column L.μ} (hwf : (toProgram nK nE m).wf = true)
    (H0 : AuxH0 (toProgram nK nE m) pl groups arrs aux L hτ q)
    (hIn : SegsHold (ctxOf (toProgram nK nE m)) (seedOf (m := m) (pl := pl) (groups := groups) (arrs := arrs)
        (aux := aux) (hτ := hτ) q) ⟨nK, nE⟩ (m ⟨nK, nE⟩).2 →
      SegsIn (seedOf (m := m) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux) (hτ := hτ) q)
        ⟨nK, nE⟩ (m ⟨nK, nE⟩).2) :
    ((toProgram nK nE m).interp (inKOf (toProgram nK nE m) pl groups arrs aux L hτ q)
      (inEOf (toProgram nK nE m) pl groups arrs aux L hτ q)).inb = true := by
  have hsz := And.intro (inKOf_size (toProgram nK nE m) pl groups arrs aux L hτ q)
    (inEOf_size (toProgram nK nE m) pl groups arrs aux L hτ q)
  obtain ⟨hH, -⟩ := (toProgram nK nE m).holds_seedMem hwf
    (loop_cons _ pl groups arrs aux L hτ H0.grp _ H0.holds)
    (loop_bus _ pl groups arrs aux L hτ H0.grp H0.inOk H0.auxSeeds H0.cnt H0.len _ H0.holds) H0.inj
  have hin : (toProgram nK nE m).Inputs (seedOf (m := m) (pl := pl) (groups := groups) (arrs := arrs)
      (aux := aux) (hτ := hτ) q) (inKOf (toProgram nK nE m) pl groups arrs aux L hτ q)
      (inEOf (toProgram nK nE m) pl groups arrs aux L hτ q) :=
    ⟨fun n hn => by simp [seedOf, Program.seedMem, hn], fun n hn => by simp [seedOf, Program.seedMem, hn]⟩
  exact (toProgram nK nE m).inb_of_mem hwf _ _ hsz _ hin hH H0.inj
    (toProgram_in nK nE m _ (hIn ((toProgram_holds nK nE m _).mp hH)))

end Seed

section Gen

variable {α : Type} {p : Params} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux, t.τ ≤ L.μ}

/-- **Every `readd` of the node program finds its cell** on any stack `q` with `M3Holds`: the
program check and `WP-9b`'s static facts (`AuxH0`), Q_link's static checks, the `QLT` input cells
holding `qltData`, the position classes covering the cap bits, no `readd` in Q_sig and Q_arith. -/
theorem inb_of_m3 {q : Column L.μ} (hwf : (toProgram nK nE (qprogP p lay I qa)).wf = true)
    (H0 : AuxH0 (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux L hτ q)
    (hQ : QOk p lay)
    (htabK : ∀ y < (qltData p lay).length, lay.qt + y < nK ∧
      (inKOf (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux L hτ q).getD (lay.qt + y) 0 =
        (qltData p lay).getD y 0)
    (hcov : CapCov p (toProgram nK nE (qprogP p lay I qa)) lay aux)
    (hsig : noReaddSegs (qsig I ((⟨nK, nE⟩ : Ptr).adv (qlink p lay ⟨nK, nE⟩).2)).2 = true)
    (harr : noReaddSegs (qa (((⟨nK, nE⟩ : Ptr).adv (qlink p lay ⟨nK, nE⟩).2).adv
      (qsig I ((⟨nK, nE⟩ : Ptr).adv (qlink p lay ⟨nK, nE⟩).2)).2)).2 = true) :
    ((toProgram nK nE (qprogP p lay I qa)).interp
      (inKOf (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux L hτ q)
      (inEOf (toProgram nK nE (qprogP p lay I qa)) pl groups arrs aux L hτ q)).inb = true := by
  refine inb_of_seed hwf H0 fun hh => ?_
  have htab : ∀ y < (qltData p lay).length, (seedOf (m := qprogP p lay I qa) (pl := pl) (groups := groups)
      (arrs := arrs) (aux := aux) (hτ := hτ) q).k (lay.qt + y) = (qltData p lay).getD y 0 := fun y hy => by
    rw [seedOf_inK q (htabK y hy).1]; exact (htabK y hy).2
  have hbits : ∀ k < (opens p).length, ∀ j < padT ((opens p).getD k default).L.t,
      ∀ z < ((opens p).getD k default).L.height,
      (seedOf (m := qprogP p lay I qa) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux) (hτ := hτ) q).k
          (bitBase p lay k + ((opens p).getD k default).L.height * j + z) = 0 ∨
        (seedOf (m := qprogP p lay I qa) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux) (hτ := hτ) q).k
          (bitBase p lay k + ((opens p).getD k default).L.height * j + z) = 1 := by
    intro k hk j hj z hz
    obtain ⟨S, hS, hn, xr, hx, hw, ho, jo, hjo, z', hz', hb, hc⟩ := hcov k hk j hj z hz
    have := seedK_bit _ pl groups arrs aux L hτ q H0 S hS hx hn hw ho hjo hb hz'
    rw [hc] at this
    exact this
  generalize seedOf (m := qprogP p lay I qa) (pl := pl) (groups := groups) (arrs := arrs) (aux := aux)
    (hτ := hτ) q = M at hh htab hbits ⊢
  have hh' := (hold_bind (ctxOf (toProgram nK nE (qprogP p lay I qa))) M (qlink p lay)
    (fun _ => (qsig I >>= fun _ => qa)) ⟨nK, nE⟩).mp hh
  exact (in_bind M (qlink p lay) (fun _ => (qsig I >>= fun _ => qa)) ⟨nK, nE⟩).mpr
    ⟨qlink_in hQ htab hbits _ hh'.1, (in_bind M _ _ _).mpr ⟨segsIn_of_noReadd M _ _ hsig,
      segsIn_of_noReadd M _ _ harr⟩⟩

end Gen

/-! ## The node program (`nodeSound_layout`'s form) -/

section Inb

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}

/-- **`hinb` for the node program** (`nodeSound_layout`'s hypothesis, `vk` outermost). `hqlt` is
`nodeSound_layout`'s own; it is used only on input cells (`interpMem_inK`, no `inb`). -/
theorem hinb_node {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}
    (hT : ∀ x, T x = lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux)
    (hst : ∀ x, AuxStatic lay I qa nK nE pl groups aux (arrsX x))
    (hQ : QOk P20 lay)
    (hqtK : lay.qt + (qltData P20 lay).length ≤ nK)
    (hcov : CapCov P20 (Qn lay I qa nK nE) lay aux)
    (hsig : noReaddSegs (qsig I (p1 lay nK nE)).2 = true)
    (harr : noReaddSegs (qa (p2 lay I nK nE)).2 = true)
    (hqlt : ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ∀ y < (qltData P20 lay).length,
        (memX lay I qa nK nE pl groups arrsX aux hτ' x qm qr).k (lay.qt + y) = (qltData P20 lay).getD y 0) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN T hτ x qm qr →
      ((Qn lay I qa nK nE).interp (inKOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
        (stackOf lay26 qm qr)) (inEOf (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)
        (stackOf lay26 qm qr))).inb = true := by
  intro vk c x qm qr hok hb hG
  have st := hst x
  have hM3 : M3Holds (lvmInst (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x)) ()
      (stackOf lay26 qm qr) := m3Holds_congr (hT x) hG.1
  have hsz := inKOf_size (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x) (stackOf lay26 qm qr)
  refine inb_of_m3 (p := P20) st.wf ⟨st.grp, st.inOk, st.auxSeeds, st.cnt, st.len, st.inj, hM3⟩ hQ
    (fun y hy => ⟨by omega, ?_⟩) hcov hsig harr
  rw [← hqlt vk c x qm qr hok hb hG y hy]
  exact ((Qn lay I qa nK nE).interpMem_inK _ _ (lt_of_lt_of_eq (show lay.qt + y < nK by omega) hsz.symm)).symm

end Inb

end Lvm.NS
