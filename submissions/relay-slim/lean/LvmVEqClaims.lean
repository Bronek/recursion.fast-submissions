-- New for lvm (WP-14a, H3): V_S's claim lists (LvmDecide `chFixedClaims`, LvmDecideV0 `ksOutputClaims0`,
-- `sumClaim`, `BlockClaim.onStack`) against LvmVEqMid's over `E`, through LvmVEqRel's `BCRel`/`CRel`/`SCRel`.
import LvmVEqRel
import LvmVEqArith

/-!
# The claim lists over `E`

* `point_rel`, `sumClaim_rel`: a native column claim (`BlockClaim.point`) and a native sum claim
  (`sumClaim`) agree with their `E` twins (`BClaim.point`, `sumClaimE`) on mapped arguments;
* `onStack_rel`: agreeing block claims put agreeing claims on the stack; `on_rel`: per commitment,
  for agreeing lists;
* `tapeClaims_rel` (lvm2 S2: the tape's claims), `ksOutputClaims_rel` (KS's 25 output
  lanes) at `P20`; `dBlk_eq`, `ksYPart_rel`: the P20 layout of `M3.real` is LvmVEqMid's.

Helpers live in `Lvm.VEq.Lk` (no clash with the other phases' helpers).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_mul tE_ofK)

namespace Lk

/-! ## Lists -/

theorem forall₂_map_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} :
    ∀ (l : List α), (∀ a ∈ l, R (f a) (g a)) → List.Forall₂ R (l.map f) (l.map g)
  | [], _ => .nil
  | a :: l, h => .cons (h a (by simp)) (forall₂_map_map l fun b hb ↦ h b (by simp [hb]))

theorem forall₂_append {α β : Type} {R : α → β → Prop} {a c : List α} {b d : List β}
    (h1 : List.Forall₂ R a b) (h2 : List.Forall₂ R c d) : List.Forall₂ R (a ++ c) (b ++ d) :=
  List.rel_append h1 h2

/-! ## Claims -/

/-- **A column claim.** -/
theorem point_rel (b : Lvm.Placement) (z : List FE) (v : FE) {b' : VPlacement} {z' : List E} {v' : E}
    (hb : b' = plE b) (hz : z' = z.map FE.toExt3) (hv : v' = FE.toExt3 v) :
    BCRel (BlockClaim.point b z v) (BClaim.point b' z' v') := by
  subst hb hz hv
  exact ⟨rfl, rfl, fun xs ↦ (toExt3_eqEval z xs).symm⟩

/-- A part of a native sum claim over `E`. -/
def partE (q : FE × Lvm.Placement × List FE) : E × VPlacement × List E :=
  (FE.toExt3 q.1, plE q.2.1, q.2.2.map FE.toExt3)

/-- **A sum claim.** -/
theorem sumClaim_rel (nu : ℕ) (parts : List (FE × Lvm.Placement × List FE)) (v : FE)
    {parts' : List (E × VPlacement × List E)} {v' : E} (hp : parts' = parts.map partE)
    (hv : v' = FE.toExt3 v) : BCRel (sumClaim nu parts v) (sumClaimE nu parts' v') := by
  subst hp hv
  refine ⟨rfl, rfl, fun xs ↦ ?_⟩
  simp only [sumClaim, sumClaimE, toExt3_sumE, List.map_map]
  congr 1
  refine List.map_congr_left fun q _ ↦ ?_
  obtain ⟨c, b, z⟩ := q
  simp only [Function.comp, partE, tE_mul, toExt3_eqAbove, toExt3_eqEval, ← List.map_take]
  rfl

/-! ## The P20 layout -/

/-- `D`'s block at `P20` (lvm2 S2). -/
theorem dBlk_eq : plE (dBlock P20) = dBlkE := by
  rw [dBlock, layout0_P20]; rfl

/-- `KS`'s `Y` lane `l` of `P20`. -/
theorem ksYPart_rel (l : ℕ) (pt : List FE) :
    plE (ksYPart P20 (layout0 P20) l pt).1 = (ksYPartE l (pt.map FE.toExt3)).1 ∧
      (ksYPart P20 (layout0 P20) l pt).2.map FE.toExt3 = (ksYPartE l (pt.map FE.toExt3)).2 := by
  by_cases hl : l < 14 <;> refine ⟨?_, ?_⟩ <;>
    simp only [ksYPart, ksYPartE, hl, ↓reduceIte, List.map_append, map_selectorPoint] <;> rfl

end Lk

open Lk

/-- **On the stack.** -/
theorem onStack_rel {c : BlockClaim} {c' : BClaim} (h : BCRel c c') : SCRel c.onStack c'.onStack := by
  obtain ⟨hb, hv, hw⟩ := h
  refine ⟨hv, fun xs ↦ ?_⟩
  simp only [BlockClaim.onStack, BClaim.onStack, hb, tE_mul]
  rw [← List.map_take, hw]
  exact congrArg (· * _) (toExt3_eqAbove c.block xs).symm

/-- **Per commitment.** -/
theorem on_rel {l : List (Com × BlockClaim)} {l' : List (Com × BClaim)} (h : List.Forall₂ CRel l l')
    (com : Com) :
    List.Forall₂ SCRel ((l.filter (·.1 == com)).map (·.2.onStack))
      ((l'.filter (·.1 == com)).map (·.2.onStack)) := by
  induction h with
  | nil => exact .nil
  | @cons a b _ _ hab _ ih =>
    obtain ⟨h1, h2⟩ := hab
    by_cases hc : (b.1 == com) = true
    · simp only [List.filter_cons, h1, hc, ↓reduceIte, List.map_cons]
      exact .cons (onStack_rel h2) ih
    · simp only [List.filter_cons, h1, hc, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-! ## The claim lists -/

/-- **The tape's claims** (lvm2 S2, T1, T4, T5) against `tapeClaimsE`, given related `r`, lanes
and ring. -/
theorem tapeClaims_rel (tp : TapeRes) (wo : WireOut) (tpE : Lvm.KG.TapeOutE) (pub : Pub)
    (hr : tpE.1 = tp.r.map FE.toExt3) (hv : tpE.2.1 = tp.v.map FE.toExt3)
    (hring1 : tpE.2.2.2.d.ring.1 = FE.toExt3 wo.ring.1)
    (hring2 : ∀ xs, tpE.2.2.2.d.ring.2 (xs.map FE.toExt3) = FE.toExt3 (wo.ring.2 xs)) :
    List.Forall₂ BCRel (tapeClaims P20 tp wo pub) (tapeClaimsE tpE pub) := by
  have hb := dBlk_eq.symm
  simp only [tapeClaims, tapeClaimsE]
  refine forall₂_append (forall₂_append ?_ ?_) ?_
  · exact forall₂_map_map _ fun l _ ↦ point_rel _ _ _ hb
      (by simp only [hr, List.map_append, map_selectorPoint])
      (by rw [hv]; exact getD_map_toExt3 tp.v l)
  · exact List.Forall₂.cons ⟨rfl, hring1, hring2⟩ List.Forall₂.nil
  · exact forall₂_map_map _ fun ⟨w, l⟩ _ ↦ point_rel _ _ _ hb
      (by simp only [List.map_append, map_selectorPoint]; rfl) (tE_ofK w).symm

/-- **`KS`'s 25 output lanes.** -/
theorem ksOutputClaims_rel (rk v : List FE) :
    List.Forall₂ CRel (ksOutputClaims0 P20 rk v)
      (ksOutputClaimsE (rk.map FE.toExt3) (v.map FE.toExt3)) := by
  simp only [ksOutputClaims0, ksOutputClaimsE]
  refine forall₂_map_map _ fun l _ ↦ ⟨rfl, ?_⟩
  obtain ⟨h1, h2⟩ := ksYPart_rel l rk
  exact point_rel _ _ _ h1.symm h2.symm (getD_map_toExt3 v l)

end Lvm.VEq
