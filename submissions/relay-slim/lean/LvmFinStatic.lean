-- New for lvm (WP-16a2, BLUEPRINT A24): the static facts of the P20 node program that the kernel
-- cannot evaluate (they run the builder through HAR's table gadget), as one closed Bool `staticOkB`
-- that the compiled `V` checks once per process (`LvmFinGuard`), and their soundness lemmas.
import LvmQAsmV
import LvmQAsmInbCore
import LvmQAsmHarMain
import LvmM3Check

/-!
# `staticOkB` (A24)

Bundled (natively evaluated, never in the kernel): Q_arith has no `readd` (`hna`), the program check
(`AuxStatic.wf`, through QL's one-pass `segsOk`), the groups' tiling (`AuxStatic.grp`), the cell bound
(`AuxStatic.inj`), and `harith_core`'s claim checks `hwr`/`hwm` (`ClaimsWF`). Each is read on the
linear-time builders of V-PERF (`VF.qprogF`, `VF.qarithF`, `VF.phases47F`, equal to the node
program's, `qprogF_eq`, `qarithF_eq`, `phases47F_eq`). Every other static fact stays a kernel proof.
-/

set_option autoImplicit false

namespace Lvm.Fin

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QAsm Lvm.M3 Lvm.Har

theorem phases47F_eq (C : QCfg) : VF.phases47F C = phases47 C := by
  unfold VF.phases47F phases47
  rw [VF.tapeGadgetF_eq, VF.gkrGadgetF_eq]

theorem qarithF_eq (C : QCfg) : VF.qarithF C = qarith C := by
  unfold VF.qarithF qarith
  rw [phases47F_eq]

theorem qprogF_eq (C : QCfg) : VF.qprogF C = qprogC C := by
  unfold VF.qprogF qprogC
  rw [qarithF_eq]

/-! ## The program check in one pass per block (adapted from WP-16a-QFX's uncommitted
`LvmQAsmFactsFast`): `blockOkAt` recomputes a row's rank (a prefix of the template) per row, quadratic
in the template (6.3 s natively at `P20`); `rowsOkF` advances a pointer, with the block's widths
computed once. -/

/-- A block's rows from the pointer `c` on (the pointer advanced past each row). -/
def rowsOkF (dims : List Nat) (tw : Ty → Nat) : Ptr → List Row → Bool
  | _, [] => true
  | c, r :: rs => rowOkC c.at dims tw r && rowsOkF dims tw (c.adv [.row r]) rs

/-- The widths `k`, `e` as a function of the memory (built inside the per-row check: the compiler
must not re-evaluate `B.tw` per operand). -/
def twKE (k e : Nat) : Ty → Nat
  | .K => k
  | .E => e

/-- A block's rows with the widths passed as numbers (evaluated once, at the call). -/
def rowsOkKE (dims : List Nat) (k e : Nat) : Ptr → List Row → Bool
  | _, [] => true
  | c, r :: rs => rowOkC c.at dims (twKE k e) r && rowsOkKE dims k e (c.adv [.row r]) rs

theorem rowsOkKE_eq (dims : List Nat) (k e : Nat) : ∀ (c : Ptr) (rs : List Row),
    rowsOkKE dims k e c rs = rowsOkF dims (twKE k e) c rs
  | _, [] => rfl
  | c, r :: rs => by rw [rowsOkKE, rowsOkF, rowsOkKE_eq dims k e _ rs]

theorem twKE_tw (B : Block) : twKE (B.tw .K) (B.tw .E) = B.tw := by
  funext τ; cases τ <;> rfl

/-- `blockOkAt` in one pass. -/
def blockOkF (p : Ptr) (B : Block) : Bool := rowsOkKE B.dims (B.tw .K) (B.tw .E) p B.tpl

/-- `segsOk` with `blockOkF`. -/
def segsOkF : Ptr → List Seg → Bool
  | _, [] => true
  | p, .row r :: δ => rowOkC p.at [] (fun _ => 0) r && segsOkF (p.adv [.row r]) δ
  | p, .blk B :: δ => blockOkF p B && segsOkF (p.adv [.blk B]) δ

theorem adv_row_at (c : Ptr) (r : Row) (τ : Ty) : (c.adv [.row r]).at τ = c.at τ + r.w τ := by
  cases τ <;> simp [Ptr.adv, Ptr.at, segsW, Seg.w]

theorem rowsOkF_eq (dims : List Nat) (tw : Ty → Nat) : ∀ (c : Ptr) (rs : List Row),
    rowsOkF dims tw c rs = (List.range rs.length).all fun t =>
      rowOkC (fun τ => c.at τ + ((rs.take t).map (Row.w τ)).sum) dims tw (rs.getD t default)
  | c, [] => by simp [rowsOkF]
  | c, r :: rs => by
    rw [rowsOkF, rowsOkF_eq dims tw _ rs, List.length_cons, List.range_succ_eq_map, List.all_cons,
      List.all_map]
    have h0 : (fun τ => c.at τ + (((r :: rs).take 0).map (Row.w τ)).sum) = c.at := by
      funext τ; simp
    have h1 : ∀ t, (fun τ => c.at τ + (((r :: rs).take (t + 1)).map (Row.w τ)).sum) =
        fun τ => (c.adv [.row r]).at τ + ((rs.take t).map (Row.w τ)).sum := fun t => by
      funext τ; rw [adv_row_at]; simp [Nat.add_assoc]
    simp only [h0, List.getD_cons_zero, Function.comp_def, h1, List.getD_cons_succ]

theorem blockOkF_eq (p : Ptr) (B : Block) : blockOkF p B = blockOkAt p B := by
  rw [blockOkF, rowsOkKE_eq, twKE_tw, rowsOkF_eq]; rfl

theorem segsOkF_eq : ∀ (p : Ptr) (δ : List Seg), segsOkF p δ = segsOk p δ
  | _, [] => rfl
  | p, .row r :: δ => by rw [segsOkF, segsOk, segsOkF_eq _ δ]
  | p, .blk B :: δ => by rw [segsOkF, segsOk, segsOkF_eq _ δ, blockOkF_eq]

/-! The builder runs once (closed constants, evaluated at start-up, shared by the checks):
Q_link's and Q_sig's segments, the pointer `p2C cfg20`, phases 4–7 (`VF.phases47F`), the rest. -/

/-- Q_link's segments at `P20`. -/
def segL20 : List Seg := (Lvm.QLink.qlink cfg20.p (lay cfg20) ⟨nK cfg20, 0⟩).2
/-- Q_sig's segments at `P20`. -/
def segS20 : List Seg := (Lvm.QSig.qsig (sigIn cfg20) (p1C cfg20)).2
/-- Q_arith's pointer. -/
def p2F : Ptr := p2C cfg20
/-- Phases 4–7 (linear-time GKR builder). -/
def ph47F : P47Out × List Seg := VF.phases47F cfg20 p2F
/-- The rest of Q_arith. -/
def restF : Unit × List Seg := qarithRest cfg20 ph47F.1 (p2F.adv ph47F.2)

theorem arith_segs : ph47F.2 ++ restF.2 = (VF.qarithF cfg20 (p2C cfg20)).2 := rfl

theorem prog_segs : segL20 ++ (segS20 ++ (ph47F.2 ++ restF.2)) = (VF.qprogF cfg20 ⟨nK cfg20, 0⟩).2 := rfl

/-- Q_arith has no `readd`. -/
def okNoRd20 : Bool := noReaddSegs (ph47F.2 ++ restF.2)

/-- The program check, in one pass over the segments. -/
def okWf20 : Bool := segsOkF ⟨nK cfg20, 0⟩ (segL20 ++ (segS20 ++ (ph47F.2 ++ restF.2)))

/-- The placement record's groups tile the program's pieces (`VF.piecesF`, linear time). -/
def okGrp20 : Bool := grpOkCore ((VF.piecesF M3.Q20).map (pinfo M3.Q20)) data20.groups

/-- Fewer than `2^64 − 1` cells of each type. -/
def okInj20 : Bool := decide (max (M3.Q20.cells .K) (M3.Q20.cells .E) < 2 ^ 64 - 1)

/-- Q_arith's claim lists (`harith_core`'s `hwr`, `hwm`). -/
def okClaims20 : Bool :=
  let cs := (qarithCs cfg20 data20 ph47F.1 (p2F.adv ph47F.2)).1
  ClaimsWF P20.nuRec (onCom cs .crec) && ClaimsWF P20.nuMain (onCom cs .main)

/-- **The static guard** (A24): every bundled check. -/
def staticOkB : Bool := okNoRd20 && okWf20 && okGrp20 && okInj20 && okClaims20

/-! ## Soundness of the guard -/

/-- The bundled facts, in their consumers' forms. -/
structure StaticFacts : Prop where
  hna : noReaddSegs (qarith cfg20 (p2C cfg20)).2 = true
  wf : (Q cfg20).wf = true
  grp : GrpOk (Q cfg20) data20.groups
  inj : GInj (max ((Q cfg20).cells .K) ((Q cfg20).cells .E))
  hwr : ClaimsWF cfg20.p.nuRec
    (onCom (qarithCs cfg20 data20 (phases47 cfg20 (p2C cfg20)).1
      ((p2C cfg20).adv (phases47 cfg20 (p2C cfg20)).2)).1 .crec) = true
  hwm : ClaimsWF cfg20.p.nuMain
    (onCom (qarithCs cfg20 data20 (phases47 cfg20 (p2C cfg20)).1
      ((p2C cfg20).adv (phases47 cfg20 (p2C cfg20)).2)).1 .main) = true

/-- **What `staticOkB = true` gives.** -/
theorem staticFacts (h : staticOkB = true) : StaticFacts := by
  simp only [staticOkB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hw⟩, hg⟩, hi⟩, hc⟩ := h
  have hQ : M3.Q20 = Q cfg20 := M3.Q20_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← qarithF_eq, ← arith_segs]; exact hn
  · exact toProgram_wf _ _ _ (by rw [← qprogF_eq, ← prog_segs, ← segsOkF_eq]; exact hw)
  · rw [← hQ]; exact grpOk_of_B (by rw [grpOkB, ← VF.piecesF_eq]; exact hg)
  · have hm : max ((Q cfg20).cells .K) ((Q cfg20).cells .E) < 2 ^ 64 - 1 := by
      rw [← hQ]; exact of_decide_eq_true hi
    intro a b ha hb hab
    exact FK.FKx_pow_inj (by omega) (by omega) hab
  · simp only [okClaims20, ph47F, p2F, Bool.and_eq_true, phases47F_eq] at hc; exact hc.1
  · simp only [okClaims20, ph47F, p2F, Bool.and_eq_true, phases47F_eq] at hc; exact hc.2

end Lvm.Fin
