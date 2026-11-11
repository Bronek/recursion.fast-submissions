-- New for lvm (WP-14a, H3): V_S's phases 5 and 7 (LvmVEqPhases `dChLink`, `dKsLink`, the CH and KS links of
-- `M3.real P20`) refine WP-8's DSL programs (`Lvm.KG.chLinkProg`, `ksLinkProg`) on the stream, their claims
-- related by `CRel` to LvmVEqMid's `chLinkClaimsE`, `ksLinkClaimsE`.
import LvmVEqLinkArith
import LvmVEqSum

/-!
# The `CH` and `KS` links: V_S refines the verifier language

(lvm2 S2: v1's `CH` link is gone from V_S, so `ref_dChLink` is deleted.) v1's `ref_dChLink`: wherever V_S's phase 5 ends with its checks held, WP-8's `chLinkProg 20 52` read off
the stream returns `lo` at the same cursor with V_S's link claims `CRel`-related to
`chLinkClaimsE lo`; `ref_dKsLink` the same for phase 7, `ksLinkProg 15 14 (contRows P20)` and
`ksLinkClaimsE`. Read for read: the samples and scalars by `ref_samples`/`ref_readEs`, the sumchecks
by H1's `ref_sumcheck` (their claims transported by LvmVEqLinkArith), the caller-placed ring switches
by `ref_ringRaw`, the final `require` by the transported check (`toExt3_chOk`, `toExt3_ksOk`).
`monoD_dChLink`, `monoD_dKsLink` hold for every `p`, `m`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakGkr Finset Lk
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_ofK FE_eq_of_beq)

/-! ## `MonoD` -/

theorem monoD_dChLink (p : Params) (m : M3) (r v : List FE) (pub : Pub) :
    MonoD (dChLink p m r v pub) :=
  (monoD_samples _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_ringRaw _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
      (monoD_ringRaw _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦
        (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dKsLink (p : Params) (m : M3) (rk : List FE) (pub : Pub) : MonoD (dKsLink p m rk pub) :=
  (monoD_samples _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _

/-! ## Refinement -/

section Ref

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

namespace Lk

theorem forall₂_map_both {α β γ δ : Type} {R : γ → δ → Prop} {f : α → γ} {g : β → δ} {l : List α}
    {l' : List β} (h : List.Forall₂ (fun a b ↦ R (f a) (g b)) l l') :
    List.Forall₂ R (l.map f) (l'.map g) :=
  List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 h)

theorem ref_samplesL (n : ℕ) :
    RefAt cap shp sig (DM.samples n) (Compile.VerifierProgram.sampleChallenges n)
      fun xs ys ↦ ys = xs.map FE.toExt3 ∧ xs.length = n :=
  refAt_withD (ref_samples n) (Q := fun xs ↦ xs.length = n) (length_samples n sig)

theorem ref_readEsL (n : ℕ) :
    RefAt cap shp sig (DM.readEs n) (Compile.VerifierProgram.readScalars n)
      fun xs ys ↦ ys = xs.map FE.toExt3 ∧ xs.length = n :=
  refAt_withD (ref_readEs n) (Q := fun xs ↦ xs.length = n) (length_readEs n sig)

theorem ref_sumcheckL (count : ℕ) (eqs : List (Option FE)) (claim : FE) :
    RefAt cap shp sig (Lvm.sumcheck claim count eqs)
      (Verifier.sumcheck (FE.toExt3 claim) count (eqs.map (Option.map FE.toExt3)))
      fun r r' ↦ r' = (r.1.map FE.toExt3, FE.toExt3 r.2) ∧ r.1.length = eqs.length :=
  refAt_withD (ref_sumcheck count eqs claim) (Q := fun r ↦ r.1.length = eqs.length)
    (length_sumcheck count eqs claim sig)

end Lk

/-- **V_S's phase 7 (the `KS` link) refines WP-8's `ksLinkProg`.** -/
theorem ref_dKsLink (tabs : Pub → List M3.Tab) (rk : List FE) (pub : Pub) :
    Ref20 sig (dKsLink P20 (M3.real P20 tabs) rk pub) (Lvm.KG.ksLinkProg (11 + 4) 14 (contRows P20))
      (fun cl out ↦ List.Forall₂ CRel cl (ksLinkClaimsE out.1 out.2.1 out.2.2)) := by
  unfold dKsLink Lvm.KG.ksLinkProg
  -- ρ, λ
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_samplesL _) ?_
  rintro kchal _ ⟨rfl, hk⟩
  replace hk : kchal.length = 20 := hk
  -- the shift sumcheck (claim 0)
  have h2 := ref_sumcheckL (cap := capS) (shp := shpS) (sig := sig) 3 (List.replicate 15 none) 0
  simp only [tE_zero, List.map_replicate, Option.map_none] at h2
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) h2 ?_
  rintro ⟨rho', f⟩ _ ⟨rfl, hr⟩
  replace hr : rho'.length = 15 := hr
  -- the four scalars
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro vals _ rfl
  -- the check and the claims
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hok ↦ ?_) fun _ _ _ ↦ RefAt.pure ?_
  · have h := congrArg FE.toExt3 (FE_eq_of_beq hok)
    dsimp only at h ⊢
    simp only [show P20.ksLog = 15 from rfl, show P20.recRowsLog = 14 from rfl] at h
    rw [toExt3_ksOk _ _ _ hk hr] at h
    simpa only [Nat.reduceAdd] using h
  · dsimp only
    simp only [M3.real, M3.ofParts, Lvm.ksLink0, ksLinkClaimsE]
    have hom (l : ℕ) : (Verifier.eqKernel ((kchal.map FE.toExt3).drop 15)).getD l 0 =
        FE.toExt3 ((Lvm.eqKernel (kchal.drop P20.ksLog)).getD l 0) := by
      rw [← List.map_drop, ← map_eqKernel, getD_map_toExt3]; rfl
    refine .cons ⟨rfl, sumClaim_rel _ _ _ ?_ (getD_map_toExt3 _ _)⟩
      (.cons ⟨rfl, sumClaim_rel _ _ _ ?_ (getD_map_toExt3 _ _)⟩
        (.cons ⟨rfl, sumClaim_rel _ _ _ ?_ (getD_map_toExt3 _ _)⟩
          (.cons ⟨rfl, sumClaim_rel _ _ _ ?_ (getD_map_toExt3 _ _)⟩ .nil))) <;>
      rw [List.map_map] <;> refine List.map_congr_left fun l _ ↦ ?_ <;>
      simp only [Function.comp, partE, hom, (ksYPart_rel l rho').1, (ksYPart_rel l rho').2,
        List.map_append, map_selectorPoint, ← List.map_take]
    all_goals rfl

end Ref

end Lvm.VEq
