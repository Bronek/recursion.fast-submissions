-- WP-14c (NodeSound, O10). New for lvm: the node program's parts from the M3 instance: WP-10's
-- `loopir_sound` (hypotheses from WP-9/9b's `AuxHyps`) makes the interpreter's memory hold every
-- segment of `Q = Q_link ++ Q_sig ++ Q_arith` (QL's assembly order) with every assertion; then
-- QL's `qlink_sound`, WP-12's `qsig_sound_in` with WP-12b's `sigBitsOk`.
import LvmNodeSoundLeft
import LvmSigBits

/-!
# The circuit's parts on the committed pair

`qprog lay I qa = do qlink P20 lay; let _ ← qsig I; qa` (QL's order), `Q = toProgram nK nE (qprog …)`,
`M = Q.interpMem (inKOf q) (inEOf q)` on the stack `q` of a candidate pair. Pointers: Q_link at
`p0 = ⟨nK, nE⟩`, Q_sig at `p1`, Q_arith at `p2`.

* **`segs_of_aux`**: `AuxHyps` (`loopir_sound`'s hypotheses: static checks, `M3Holds`, `inb`) ⇒
  every segment of `Q` holds in `M` and every assertion holds.
* **`link_of_aux`**: with Q_link's inputs where its layout says (`QIn`) and its static checks
  (`StreamOk`, `QOk`), the stream meets `LaneLink`, is a trace of the schedule (`LinkOk` of
  `decode`) and its padding is pinned.
* **`sig_of_aux`**: with the `KS` cells (`SigKSin`) and the six `BITS` tables in `aux` with their
  cells below the cell count, Q_sig's `SigOk` and `ChildOk`.
* **`arith_of_aux`**: Q_arith's segments hold and assert at `p2` (what `Q_arith_eq` consumes).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3 Lvm.SigBits

/-- **The node program** (QL's assembly order): Q_link, Q_sig, Q_arith. -/
def qprog {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) : BM α := do
  qlink P20 lay
  let _ ← qsig I
  qa

theorem ctxOf_cells (Q : Program) : (ctxOf Q).cells = Q.cells := rfl

section Parts

variable {α : Type} (lay : Layout) (I : SigIn) (qa : BM α) (nK nE : ℕ)

/-- The node program as a LoopIR program. -/
abbrev Qn : Program := toProgram nK nE (qprog lay I qa)

/-- Q_link's pointer. -/
def p0 : Ptr := ⟨nK, nE⟩

/-- Q_sig's pointer. -/
def p1 : Ptr := (p0 nK nE).adv (qlink P20 lay (p0 nK nE)).2

/-- Q_arith's pointer. -/
def p2 : Ptr := (p1 lay nK nE).adv (qsig I (p1 lay nK nE)).2

variable (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, t.τ ≤ L.μ)

/-- The interpreter's memory on the inputs read off the stack `q`. -/
noncomputable def memN (q : LeanVM.Protocol.Column L.μ) : Mem :=
  (Qn lay I qa nK nE).interpMem (inKOf (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    (inEOf (Qn lay I qa nK nE) pl groups arrs aux L hτ q)

variable {lay I qa nK nE pl groups arrs aux L hτ}

/-- **Every segment holds and asserts** in the interpreter's memory (`loopir_sound`). -/
theorem segs_of_aux {q : LeanVM.Protocol.Column L.μ}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q) :
    SegsHold (ctxOf (Qn lay I qa nK nE)) (memN lay I qa nK nE pl groups arrs aux L hτ q) (p0 nK nE)
        (qprog lay I qa (p0 nK nE)).2 ∧
      SegsAssert (memN lay I qa nK nE pl groups arrs aux L hτ q) (p0 nK nE) (qprog lay I qa (p0 nK nE)).2 := by
  have hsz := And.intro (inKOf_size (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    (inEOf_size (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
  obtain ⟨-, hok⟩ := Program.loopir_sound _ H.wf _ _ hsz _ (loop_cons _ pl groups arrs aux L hτ H.grp q H.holds)
    (loop_bus _ pl groups arrs aux L hτ H.grp H.inOk H.auxSeeds H.cnt H.len q H.holds) H.inj H.inb
  obtain ⟨hh, hiff, -⟩ := toProgram_interp nK nE (qprog lay I qa) H.wf _ _ hsz H.inj H.inb
  exact ⟨hh, hiff.mp hok⟩

/-- The three parts' segments, at their pointers. -/
theorem parts_of_aux {q : LeanVM.Protocol.Column L.μ}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q) :
    Ok (ctxOf (Qn lay I qa nK nE)) (memN lay I qa nK nE pl groups arrs aux L hτ q) (qlink P20 lay) (p0 nK nE) ∧
      Ok (ctxOf (Qn lay I qa nK nE)) (memN lay I qa nK nE pl groups arrs aux L hτ q) (qsig I) (p1 lay nK nE) ∧
      Ok (ctxOf (Qn lay I qa nK nE)) (memN lay I qa nK nE pl groups arrs aux L hτ q) qa (p2 lay I nK nE) := by
  obtain ⟨hh, ha⟩ := segs_of_aux H
  have e : qprog lay I qa = (qlink P20 lay >>= fun _ => (qsig I >>= fun _ => qa)) := rfl
  rw [e, hold_bind, hold_bind] at hh
  rw [e, assert_bind, assert_bind] at ha
  exact ⟨⟨hh.1, ha.1⟩, ⟨hh.2.1, ha.2.1⟩, ⟨hh.2.2, ha.2.2⟩⟩

/-- **Q_link's conclusion** on the committed pair. -/
theorem link_of_aux {q : LeanVM.Protocol.Column L.μ}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q) {ws : List Word}
    (hS : StreamOk P20) (hQ : QOk P20 lay) (hin : QIn P20 lay ws (memN lay I qa nK nE pl groups arrs aux L hτ q))
    (hws : 2 ^ lay.m ≤ ws.length)
    (hNs : lay.sb + 2 ^ lay.m ≤ max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E)) :
    LaneLink P20 ws ∧ LinkOk P20 (decode P20 ws) ∧ PadOkB (wordsBytes ws) (hashedLen P20) := by
  obtain ⟨hl, -, -⟩ := parts_of_aux H
  have hN : (ctxOf (Qn lay I qa nK nE)).cells .K ≤
      max ((Qn lay I qa nK nE).cells .K) ((Qn lay I qa nK nE).cells .E) := by
    rw [ctxOf_cells]; exact le_max_left _ _
  obtain ⟨hL, hP⟩ := qlink_sound hS hQ hin hws H.inj hN hNs hl.1 hl.2
  exact ⟨hL, linkOk_of_laneLink hS hL, hP⟩

/-- **Q_sig's conclusion** on the committed pair (`qsig_sound_in`, `BITS` by `sigBitsOk`). -/
theorem sig_of_aux {q : LeanVM.Protocol.Column L.μ}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    (hg : (memN lay I qa nK nE pl groups arrs aux L hτ q).k I.flag = 1)
    (hks : SigKSin I (memN lay I qa nK nE pl groups arrs aux L hτ q).k)
    (bpl : ℕ → ℕ → Bool × ℕ) (hT : SigTabsIn I (qsig I (p1 lay nK nE)).1 bpl aux)
    (hC : SigCellsLt (Qn lay I qa nK nE) I (qsig I (p1 lay nK nE)).1 bpl) (hln : I.ln = 20) :
    SigOk (digAt (memN lay I qa nK nE pl groups arrs aux L hτ q).k I.vk)
        (digAt (memN lay I qa nK nE pl groups arrs aux L hτ q).k I.md)
        (sigAt' (memN lay I qa nK nE pl groups arrs aux L hτ q).k I.sg) = true ∧
      ChildOk I (memN lay I qa nK nE pl groups arrs aux L hτ q).k := by
  obtain ⟨-, hs, -⟩ := parts_of_aux H
  exact qsig_sound_in ⟨by omega, by omega⟩ hs hg hks
    (sigBitsOk _ pl groups arrs aux L hτ q H I _ bpl hT hC ⟨by omega, by omega⟩)
    fun a b ha hb h => FK.FKx_pow_inj (by omega) (by omega) h

end Parts

end Lvm.NS
