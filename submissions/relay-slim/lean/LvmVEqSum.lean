-- New for lvm (WP-14a, H1): V_S's sumcheck rounds and grand-product GKR (LvmDecideSumcheck) refine the
-- verifier language's (LvmVCore) on the stream, values related by `FE.toExt3`.
import LvmVEqPrim
import LvmVEqArith

/-!
# Sumcheck and GKR: V_S refines the verifier language

`Lvm.sumcheckRoundPoly`, `Lvm.sumcheck`, `Lvm.gkrStep`, `Lvm.gkrLayers`, `Lvm.verifyGkrGrandProducts`
(over `FE`, on the reader `DM`) refine their `LvmVCore` twins (over `E`) wherever V_S's checks hold
(`RefAt`), generic in the commitment table `cap shp` and the stream `sig`; the values are related by
`FE.toExt3` (a GKR state by `gsE`). Each native function never clears a failed check (`MonoD`).
The DSL's `gkrLayers 1` is `gkrStep 1 >>= gkrLayers 0`, the native's `gkrStep 1`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (FE_eq_of_beq)

/-! ## `MonoD` -/

theorem monoD_sumcheckRoundPoly (count : ℕ) (claim : FE) :
    ∀ eq, MonoD (Lvm.sumcheckRoundPoly count claim eq)
  | none => monoD_readE.bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ MonoD.pure _
  | some _ => (monoD_readEs _).bind fun _ ↦ MonoD.pure _

theorem monoD_sumcheck (count : ℕ) : ∀ (eqs : List (Option FE)) (claim : FE),
    MonoD (Lvm.sumcheck claim count eqs)
  | [], _ => MonoD.pure _
  | e :: eqs, claim => (monoD_sumcheckRoundPoly count claim e).bind fun _ ↦
      monoD_sampleE.bind fun _ ↦ (monoD_sumcheck count eqs _).bind fun ⟨_, _⟩ ↦ MonoD.pure _

theorem monoD_gkrStep (step : ℕ) (s : Lvm.GkrState) : MonoD (Lvm.gkrStep step s) :=
  monoD_sampleE.bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
    (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ MonoD.pure _

theorem monoD_gkrLayers : ∀ (n : ℕ) (s : Lvm.GkrState), MonoD (Lvm.gkrLayers n s)
  | 0, _ => MonoD.pure _
  | 1, s => monoD_gkrStep 1 s
  | n + 2, s => by
    rw [Lvm.gkrLayers]
    split
    · exact (monoD_gkrStep 1 s).bind fun _ ↦ monoD_gkrLayers (n + 1) _
    · exact (monoD_gkrStep 2 s).bind fun _ ↦ monoD_gkrLayers n _

theorem monoD_verifyGkrGrandProducts (depth : ℕ) : MonoD (Lvm.verifyGkrGrandProducts depth) :=
  monoD_readE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (monoD_gkrLayers _ _).bind fun _ ↦ MonoD.pure _

/-! ## Refinement -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **A round polynomial**: its coefficients. -/
theorem ref_sumcheckRoundPoly (count : ℕ) (claim : FE) : ∀ eq : Option FE,
    RefAt cap shp sig (Lvm.sumcheckRoundPoly count claim eq)
      (Verifier.sumcheckRoundPoly count (FE.toExt3 claim) (eq.map FE.toExt3))
      (fun xs ys ↦ ys = xs.map FE.toExt3)
  | none => by
    refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ MonoD.pure _) ref_readE ?_
    rintro x _ rfl
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
    rintro xs _ rfl
    exact RefAt.pure (by simp [toExt3_sumE])
  | some e => by
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
    rintro xs _ rfl
    exact RefAt.pure (by simp [toExt3_sumE])

/-- **The sumcheck**: its challenges and final claim. -/
theorem ref_sumcheck (count : ℕ) : ∀ (eqs : List (Option FE)) (claim : FE),
    RefAt cap shp sig (Lvm.sumcheck claim count eqs)
      (Verifier.sumcheck (FE.toExt3 claim) count (eqs.map (Option.map FE.toExt3)))
      (fun r r' ↦ r' = (r.1.map FE.toExt3, FE.toExt3 r.2))
  | [], _ => RefAt.pure rfl
  | e :: eqs, claim => by
    refine RefAt.bind (fun _ ↦ monoD_sampleE.bind fun _ ↦
      (monoD_sumcheck count eqs _).bind fun ⟨_, _⟩ ↦ MonoD.pure _)
      (ref_sumcheckRoundPoly count claim e) ?_
    rintro m _ rfl
    refine RefAt.bind (fun _ ↦ (monoD_sumcheck count eqs _).bind fun ⟨_, _⟩ ↦ MonoD.pure _)
      ref_sampleE ?_
    rintro c _ rfl
    have h := ref_sumcheck count eqs (Lvm.polyEval m c)
    rw [toExt3_polyEval] at h
    refine RefAt.bind (fun ⟨_, _⟩ ↦ MonoD.pure _) h ?_
    rintro ⟨pt, f⟩ _ rfl
    exact RefAt.pure rfl

/-- A native GKR state over `E`. -/
def gsE (s : Lvm.GkrState) : Verifier.GkrState := ⟨s.values.map FE.toExt3, s.point.map FE.toExt3⟩

theorem map_some_map (l : List FE) :
    (l.map some).map (Option.map FE.toExt3) = (l.map FE.toExt3).map some := by
  simp

/-- **A GKR step.** -/
theorem ref_gkrStep (step : ℕ) (s : Lvm.GkrState) :
    RefAt cap shp sig (Lvm.gkrStep step s) (Verifier.gkrStep step (gsE s)) fun r r' ↦ r' = gsE r := by
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
    (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ MonoD.pure _) ref_sampleE ?_
  rintro c _ rfl
  have h := ref_sumcheck (2 ^ step + 1) (s.point.map some) (Lvm.polyEval s.values c)
    (cap := cap) (shp := shp) (sig := sig)
  rw [toExt3_polyEval, map_some_map] at h
  refine RefAt.bind (fun ⟨_, _⟩ ↦
    (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ MonoD.pure _) h ?_
  rintro ⟨x, cl⟩ _ rfl
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro c0 _ rfl
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro c1 _ rfl
  refine RefAt.bind (fun _ ↦
      (MonoD.require _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro c2 _ rfl
  refine RefAt.bind (fun _ ↦ (monoD_samples _).bind fun _ ↦ MonoD.pure _)
    (RefAt.require fun hc ↦ ?_) ?_
  · have := congrArg FE.toExt3 (FE_eq_of_beq hc)
    simpa [toExt3_polyEval, toExt3_prodE] using this
  rintro _ _ _
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_samples _) ?_
  rintro y _ rfl
  exact RefAt.pure (by simp [gsE, toExt3_multilinearEval])

/-- **The GKR layers** (the DSL's `gkrLayers 1` binds `gkrLayers 0` after the step). -/
theorem ref_gkrLayers : ∀ (n : ℕ) (s : Lvm.GkrState),
    RefAt cap shp sig (Lvm.gkrLayers n s) (Verifier.gkrLayers n (gsE s)) fun r r' ↦ r' = gsE r
  | 0, _ => RefAt.pure rfl
  | 1, s => by
    rw [Lvm.gkrLayers, ← bind_pure (Lvm.gkrStep 1 s)]
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_gkrStep 1 s) ?_
    rintro r _ rfl
    exact RefAt.pure rfl
  | n + 2, s => by
    rw [Lvm.gkrLayers, Verifier.gkrLayers]
    split
    · refine RefAt.bind (fun _ ↦ monoD_gkrLayers _ _) (ref_gkrStep 1 s) ?_
      rintro r _ rfl
      exact ref_gkrLayers (n + 1) r
    · refine RefAt.bind (fun _ ↦ monoD_gkrLayers _ _) (ref_gkrStep 2 s) ?_
      rintro r _ rfl
      exact ref_gkrLayers n r

/-- **The grand-product GKR**: the count root, the point, the three trees' values. -/
theorem ref_verifyGkrGrandProducts (depth : ℕ) :
    RefAt cap shp sig (Lvm.verifyGkrGrandProducts depth) (Verifier.verifyGkrGrandProducts depth)
      fun r r' ↦ r' = (FE.toExt3 r.1, r.2.1.map FE.toExt3, r.2.2.map FE.toExt3) := by
  refine RefAt.bind (fun _ ↦ monoD_readE.bind fun _ ↦ (monoD_gkrLayers _ _).bind fun _ ↦
    MonoD.pure _) ref_readE ?_
  rintro a _ rfl
  refine RefAt.bind (fun _ ↦ (monoD_gkrLayers _ _).bind fun _ ↦ MonoD.pure _) ref_readE ?_
  rintro b _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_gkrLayers depth ⟨[a, a, b], []⟩) ?_
  rintro r _ rfl
  exact RefAt.pure rfl

end Ref

end Lvm.VEq
