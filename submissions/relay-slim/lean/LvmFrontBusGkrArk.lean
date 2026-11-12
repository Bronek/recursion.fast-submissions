-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/BusGkrArk.lean` (formal rev 40f877dc) as `LvmFrontBusGkrArk` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.BusGkrArk

  The grand product's relations, step by step, as the verifier program's doom needs them.
-/

import LvmGrandProductSecurity

/-!
# The grand product's relations, step by step

The verifier program's doom is stated on the grand product's relations (`familyT`'s stages,
`childRelT`, `stepOutT`, `layerRel`, `relOut`), and needs:

* `familyT_consistent'`, `familyT_sound'`: the layer's tracked family is consistent and sound;
* `card_interpNext_le'`: a combination challenge restores `childRelT` at one value at most;
* `interpDone_mem_stepOutT_iff'`: the interpolated statement is in the step's output relation
  exactly when the statement before it is in `childRelT` after all the challenges;
* `stepOutT_constTrack_iff`: inside the argument, the step's output relation is the next layer's
  relation; `stepOutT_progTrack_iff`: at the last step, it is the argument's output relation.

lvm (WP-2): the first four restated private facts of leanVM's `GrandProductSecurity`; lvm's
`LvmGrandProductSecurity` makes them public, so here they are the same facts under the primed
names the bus phase uses. The `SampleableType` and `OracleInterface` instance arguments (VCVio,
ArkLib) are dropped: no statement here uses them.
-/

namespace LeanVM.Protocol.Gkr

open CompPoly CMlPolynomialEval

section

variable {F : Type} [Field F] [Finite F] {X : Type} {ι : Type} {O : ι → Type}
  (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ)) (ρ m : ℕ)

/-- The honest polynomials of the tracked family are consistent. -/
theorem familyT_consistent' (T : RiderTrack μ riders ρ m) :
    (familyT nside μ leaves riders ρ m T).Consistent m :=
  familyT_consistent nside μ leaves riders ρ m T

/-- The tracked family's invariant is sound. -/
theorem familyT_sound' (T : RiderTrack μ riders ρ m) :
    (familyT nside μ leaves riders ρ m T).Sound m :=
  familyT_sound nside μ leaves riders ρ m T

/-- A statement outside the relation after `i` combination challenges is inside it after one more
at one challenge at most. -/
theorem card_interpNext_le' (T : RiderTrack μ riders ρ m) {i : ℕ}
    (s : InterpStmt X F nside m ρ i) (o : ∀ j, O j)
    (hs : ((s, o), ()) ∉ childRelT nside μ leaves riders ρ m T i) :
    Nat.card {c // ((interpNext nside ρ m s c, o), ()) ∈
      childRelT nside μ leaves riders ρ m T (i + 1)} ≤ 1 :=
  card_interpNext_le nside μ leaves riders ρ m T s o hs

/-- The interpolated statement is in the step's output relation exactly when the statement before
it is in the relation after all `ρ` combination challenges. -/
theorem interpDone_mem_stepOutT_iff' (T : RiderTrack μ riders ρ m)
    (s : InterpStmt X F nside m ρ ρ) (o : ∀ i, O i) :
    ((interpDone nside ρ m s, o), ()) ∈ stepOutT nside μ leaves riders ρ m T ↔
      ((s, o), ()) ∈ childRelT nside μ leaves riders ρ m T ρ :=
  interpDone_mem_stepOutT_iff nside μ leaves riders ρ m T s o

/-- Inside the argument, a step's output relation is the next layer's relation. -/
theorem stepOutT_constTrack_iff (s : LayerStmt X F nside (m + ρ)) (o : ∀ i, O i) :
    ((s, o), ()) ∈ stepOutT nside μ leaves riders ρ m (constTrack μ riders ρ m) ↔
      ((s, o), ()) ∈ layerRel nside μ leaves riders (m + ρ) :=
  Iff.rfl

/-- At the last step, a step's output relation is the argument's output relation, across the
equality of layers. -/
theorem stepOutT_progTrack_iff (h : m + ρ = μ) (s : LayerStmt X F nside (m + ρ)) (o : ∀ i, O i) :
    ((s, o), ()) ∈ stepOutT nside μ leaves riders ρ m (progTrack μ riders ρ m h) ↔
      (((s.1, (Vector.cast h s.2.1, s.2.2)), o), ()) ∈ relOut nside μ leaves riders := by
  show ((∀ r ∈ riders s.1 o, evalMle r.2 (lowPoint (Vector.cast h s.2.1) r.1) = 0) ∧
    ∀ t, evalMle (layerTable (leaves s.1 o t) (m + ρ)) s.2.1 = s.2.2 t) ↔
    ((∀ t, evalMle (leaves s.1 o t) (Vector.cast h s.2.1) = s.2.2 t) ∧
      ∀ r ∈ riders s.1 o, evalMle r.2 (lowPoint (Vector.cast h s.2.1) r.1) = 0)
  rw [and_comm]
  refine and_congr (forall_congr' fun t ↦ ?_) Iff.rfl
  subst h
  simp

end
end LeanVM.Protocol.Gkr
