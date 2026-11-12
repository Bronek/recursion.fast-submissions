-- New for lvm2 (WP T-V, stage S2): V_S's tape phase (`dTape`: T1, T2) refines the tape caller's
-- first three binds (`LvmKeccakCallerTape.tapeProg`) on the stream.
import LvmVEqKec
import LvmDecideTape
import LvmKeccakGkr

/-!
# The tape phase: V_S refines the verifier language

`Lvm.verifyKeccakLayerG depth segs` and `keccakLayersG` (over `FE`, on the reader `DM`) refine T-G's
`verifyKeccakLayerS ⟨depth, segs⟩` and `keccakLayersS` (over `E`) for every shape, as v1's layer
refines VCore's in `LvmVEqKec`; only the round constant's share changes (`toExt3_iotaG`). The tape's
first claim maps to T-G's (`kcE_tapeFirstClaimF`), `tapeGkrF` refines `tapeGkr` (through its flat
form `tapeGkr_eq`), and each native function never clears a failed check (`MonoD`).

Headline: **`ref_dTape w`**, V_S's `dTape w` refines
`sampleChallenges w >>= fun r ↦ readScalars 25 >>= fun v ↦ tapeGkr w r v >>= fun claim ↦ ret (r, v, claim)`
(the first three binds of `tapeProg`) with `TapeRel w`: the point and the scalars mapped, their
lengths, the claim by `kcE`, and the claim's weights' and point's lengths (`RetD`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (tE_add tE_mul tE_zero tE_one FE_eq_of_beq)

/-! ## The generic layer's round constant -/

/-- The round constant's share of a layer at `segs` segments of `depth` rounds. -/
theorem toExt3_iotaG (depth segs : ℕ) (point weights : List FE) (packLog step : ℕ) :
    FE.toExt3 (Lvm.sumE ((List.range segs).map fun segment ↦
      (Lvm.eqKernel (point.drop packLog)).getD segment 0 * Lvm.sumE ((List.range 64).filterMap fun z ↦
        if (Lvm.keccakRC.getD (depth * (segment + 1) - step - 1) 0).toNat.testBit z then
          some (weights.getD z 0) else none))) =
    Verifier.sumE ((List.range segs).map fun segment ↦
      (Verifier.eqKernel ((point.map FE.toExt3).drop packLog)).getD segment 0 *
        Verifier.sumE ((List.range 64).filterMap fun z ↦
          if (keccakRC.getD (depth * (segment + 1) - step - 1) 0).toNat.testBit z then
            some ((weights.map FE.toExt3).getD z 0) else none)) := by
  rw [toExt3_sumE, List.map_map, show Lvm.keccakRC = keccakRC from rfl]
  congr 1
  refine List.map_congr_left fun seg _ ↦ ?_
  rw [Function.comp_apply, tE_mul, toExt3_sumE, ← getD_map_toExt3, map_eqKernel, List.map_drop,
    List.map_filterMap]
  congr 2
  refine List.filterMap_congr fun z _ ↦ ?_
  by_cases h : (keccakRC.getD (depth * (seg + 1) - step - 1) 0).toNat.testBit z
  · simp only [h, ↓reduceIte, Option.map_some, getD_map_toExt3]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Option.map_none]

/-! ## Returns -/

theorem retD_keccakPackRounds : ∀ (rs : List FE) (value scale : FE),
    RetD (fun r : FE × FE × List FE ↦ r.2.2.length = rs.length) (Lvm.keccakPackRounds rs value scale)
  | [], _, _ => RetD.pure rfl
  | _ :: rs, _, _ => RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      (retD_keccakPackRounds rs _ _).bind fun ⟨_, _, _⟩ h ↦ RetD.pure (by simp [h])

theorem length_keccakLinearTranspose (w : List FE) : (Lvm.keccakLinearTranspose w).length = 1600 := by
  rw [← List.length_map (f := FE.toExt3), map_keccakLinearTranspose,
    KeccakGkr.keccakLinearTranspose_length]

theorem retD_verifyKeccakLayerG (depth segs logSteps step : ℕ) (c : Lvm.KeccakClaim) :
    RetD (fun c' : Lvm.KeccakClaim ↦ c'.weights.length = 1600 ∧ c'.point.length = c.point.length)
      (verifyKeccakLayerG depth segs logSteps step c) :=
  RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
    (retD_keccakPackRounds _ _ _).bind fun ⟨_, _, _⟩ h ↦ RetD.bind_true fun ⟨_, _⟩ ↦
      RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
        RetD.pure ⟨length_keccakLinearTranspose _, h⟩

theorem retD_keccakLayersG (depth segs logSteps : ℕ) : ∀ (steps : List ℕ) (c : Lvm.KeccakClaim),
    c.weights.length = 1600 →
    RetD (fun c' : Lvm.KeccakClaim ↦ c'.weights.length = 1600 ∧ c'.point.length = c.point.length)
      (keccakLayersG depth segs logSteps steps c)
  | [], _, h => RetD.pure ⟨h, rfl⟩
  | _ :: steps, _, _ => (retD_verifyKeccakLayerG _ _ _ _ _).bind fun c' ⟨h1, h2⟩ sig s ↦
      have h := retD_keccakLayersG depth segs logSteps steps c' h1 sig s
      ⟨h.1, h.2.trans h2⟩

/-- **The tape's input claim**: `1600` weights, the instance point less its four low coordinates. -/
theorem retD_tapeGkrF (logSteps : ℕ) (inst output : List FE) :
    RetD (fun r : List FE × Lvm.KeccakClaim ↦
        r.2.weights.length = 1600 ∧ r.2.point.length = inst.length - 4)
      (tapeGkrF logSteps inst output) :=
  RetD.bind_true fun _ ↦ (retD_keccakLayersG _ _ _ _ _ (by simp [tapeFirstClaimF, Lvm.keccakBits])).bind
    fun _ h ↦ RetD.pure (by simpa [tapeFirstClaimF] using h)

/-! ## `MonoD` -/

theorem monoD_verifyKeccakLayerG (depth segs logSteps step : ℕ) (c : Lvm.KeccakClaim) :
    MonoD (verifyKeccakLayerG depth segs logSteps step c) :=
  (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_keccakPackRounds _ _ _).bind fun ⟨_, _, _⟩ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        MonoD.pure _

theorem monoD_keccakLayersG (depth segs logSteps : ℕ) : ∀ (steps : List ℕ) (c : Lvm.KeccakClaim),
    MonoD (keccakLayersG depth segs logSteps steps c)
  | [], _ => MonoD.pure _
  | s :: steps, c => (monoD_verifyKeccakLayerG depth segs logSteps s c).bind fun _ ↦
      monoD_keccakLayersG depth segs logSteps steps _

theorem monoD_tapeGkrF (logSteps : ℕ) (inst output : List FE) :
    MonoD (tapeGkrF logSteps inst output) :=
  (monoD_samples _).bind fun _ ↦ (monoD_keccakLayersG _ _ _ _ _).bind fun _ ↦ MonoD.pure _

/-- **V_S's tape phase never clears a failed check.** -/
theorem monoD_dTape (logN : ℕ) : MonoD (dTape logN) :=
  (monoD_samples _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_tapeGkrF _ _ _).bind fun ⟨_, _⟩ ↦ MonoD.pure _

/-! ## The tape's first claim -/

theorem kcE_tapeFirstClaimF (inst lp out : List FE) :
    kcE (tapeFirstClaimF inst lp out) =
      KeccakGkr.tapeFirstClaim (inst.map FE.toExt3) (lp.map FE.toExt3) (out.map FE.toExt3) := by
  unfold tapeFirstClaimF KeccakGkr.tapeFirstClaim KeccakGkr.firstWeights kcE
  simp only [tE_mul, ← getD_map_toExt3, map_eqKernel, toExt3_dot, List.map_take, List.map_drop,
    List.map_map, Function.comp_def, toExt3_eOfNat]
  rfl

/-! ## Refinement -/

/-- What V_S's tape phase and the tape caller's first three binds relate: the instance point and the
scalars (with their lengths), the input claim (`kcE`), its weights' and point's lengths. -/
def TapeRel (w : ℕ) (t : Lvm.TapeRes) (o : List E × List E × Verifier.KeccakClaim) : Prop :=
  o.1 = t.r.map FE.toExt3 ∧ o.2.1 = t.v.map FE.toExt3 ∧ t.r.length = w ∧ t.v.length = 25 ∧
    o.2.2 = kcE t.claim ∧ t.claim.weights.length = 1600 ∧ t.claim.point.length = w - 4

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- A native step followed by a pure map refines the program alone. -/
theorem RefAt.bind_pure_left {α β β' : Type} {d : DM β} {g : β → β'} {P : VerifierProgram α}
    {R : β → α → Prop} {R' : β' → α → Prop} (h : RefAt cap occ shp sig d P R)
    (hR : ∀ b a, R b a → R' (g b) a) :
    RefAt cap occ shp sig (d >>= fun b ↦ Pure.pure (g b)) P R' := by
  intro s hok
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  exact ⟨a, h1, h2, h3, hR _ _ h4⟩

/-- **A layer at a shape.** -/
theorem ref_verifyKeccakLayerG (depth segs logSteps step : ℕ) (c : Lvm.KeccakClaim) :
    RefAt cap occ shp sig (verifyKeccakLayerG depth segs logSteps step c)
      (KeccakGkr.verifyKeccakLayerS ⟨depth, segs⟩ logSteps step (kcE c)) fun r r' ↦ r' = kcE r := by
  unfold verifyKeccakLayerG KeccakGkr.verifyKeccakLayerS
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_keccakPackRounds _ _ _).bind fun ⟨_, _, _⟩ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        MonoD.pure _) (ref_readEs _) ?_
  rintro product _ rfl
  refine RefAt.bind (fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_keccakPackRounds _ _ _).bind fun ⟨_, _, _⟩ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        MonoD.pure _)
    (RefAt.require fun hc ↦ req_of (toExt3_check1 (toExt3_projected _ _)
      (toExt3_iotaG _ _ _ _ _ _) (toExt3_sumE _)) rfl hc) ?_
  rintro _ _ _
  refine RefAt.bind (fun _ ↦
    (monoD_keccakPackRounds _ _ _).bind fun ⟨_, _, _⟩ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        MonoD.pure _) ref_sampleE ?_
  rintro s _ rfl
  have hp := ref_keccakPackRounds c.point (Lvm.polyEval product s) 1 (cap := cap) (occ := occ) (shp := shp)
    (sig := sig)
  rw [toExt3_polyEval, tE_one] at hp
  refine RefAt.bind (fun ⟨_, _, _⟩ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        MonoD.pure _) hp ?_
  rintro ⟨value, scale, point⟩ _ rfl
  have hs := (ref_sumcheck 4 (List.replicate Lvm.localBits none) value (cap := cap) (occ := occ) (shp := shp)
    (sig := sig)).retD (retD_sumcheck 4 _ value)
  simp only [List.map_replicate, Option.map_none] at hs
  refine RefAt.bind (fun ⟨_, _⟩ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ MonoD.pure _) hs ?_
  rintro ⟨lp, value⟩ _ ⟨rfl, hlen⟩
  simp only [List.length_replicate] at hlen
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    MonoD.pure _) (ref_readEs _) ?_
  rintro t _ rfl
  refine RefAt.bind (fun _ ↦ monoD_sampleE.bind fun _ ↦ MonoD.pure _)
    (RefAt.require fun hc ↦ req_of (toExt3_check2 rfl (toExt3_weighted _ _ hlen)
      (by rw [toExt3_sumE, map_keccakInstanceWeights]) (getD_map_toExt3 _ _).symm
      (getD_map_toExt3 _ _).symm (getD_map_toExt3 _ _).symm) rfl hc) ?_
  rintro _ _ _
  refine RefAt.bind (fun _ ↦ MonoD.pure _) ref_sampleE ?_
  rintro beta _ rfl
  refine RefAt.pure (kc_ext ?_ (map_keccakInstanceWeights s).symm rfl ?_)
  · simp only [tE_add, tE_mul, getD_map_toExt3]
  · rw [map_keccakLinearTranspose, map_layerWeights lp hlen beta]

/-- **The layers at a shape.** -/
theorem ref_keccakLayersG (depth segs logSteps : ℕ) : ∀ (steps : List ℕ) (c : Lvm.KeccakClaim),
    RefAt cap occ shp sig (keccakLayersG depth segs logSteps steps c)
      (KeccakGkr.keccakLayersS ⟨depth, segs⟩ logSteps steps (kcE c)) fun r r' ↦ r' = kcE r
  | [], _ => RefAt.pure rfl
  | s :: steps, c => by
    rw [keccakLayersG, KeccakGkr.keccakLayersS]
    refine RefAt.bind (fun _ ↦ monoD_keccakLayersG depth segs logSteps steps _)
      (ref_verifyKeccakLayerG depth segs logSteps s c) ?_
    rintro c' _ rfl
    exact ref_keccakLayersG depth segs logSteps steps c'

/-- **T2**: the tape's GKR. -/
theorem ref_tapeGkrF (logSteps : ℕ) (inst output : List FE) :
    RefAt cap occ shp sig (tapeGkrF logSteps inst output)
      (KeccakGkr.tapeGkr logSteps (inst.map FE.toExt3) (output.map FE.toExt3))
      fun r c ↦ c = kcE r.2 := by
  rw [KeccakGkr.tapeGkr_eq]
  unfold tapeGkrF
  refine RefAt.bind (fun _ ↦ (monoD_keccakLayersG _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (ref_samples _) ?_
  rintro lp _ rfl
  rw [← kcE_tapeFirstClaimF]
  exact RefAt.bind_pure_left (ref_keccakLayersG tapeDepth 1 logSteps (List.range tapeDepth) _)
    fun _ _ h ↦ h

/-- **V_S's tape phase refines the tape caller's first three binds.** -/
theorem ref_dTape (w : ℕ) :
    RefAt cap occ shp sig (dTape w)
      (VerifierProgram.sampleChallenges w >>= fun r ↦ VerifierProgram.readScalars 25 >>= fun v ↦
        KeccakGkr.tapeGkr w r v >>= fun claim ↦ VerifierProgram.ret (r, v, claim))
      (TapeRel w) := by
  unfold dTape
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (monoD_tapeGkrF _ _ _).bind fun ⟨_, _⟩ ↦ MonoD.pure _)
    ((ref_samples w).retD (retD_samples w)) ?_
  rintro r _ ⟨rfl, hr⟩
  refine RefAt.bind (fun _ ↦ (monoD_tapeGkrF _ _ _).bind fun ⟨_, _⟩ ↦ MonoD.pure _)
    ((ref_readEs _).retD (retD_readEs _)) ?_
  rintro v _ ⟨rfl, hv⟩
  refine RefAt.bind (fun ⟨_, _⟩ ↦ MonoD.pure _)
    ((ref_tapeGkrF w r v).retD (retD_tapeGkrF w r v)) ?_
  rintro ⟨lp, c⟩ _ ⟨rfl, h1, h2⟩
  exact RefAt.pure ⟨rfl, rfl, hr, hv, rfl, h1, by rw [h2, hr]⟩

end Ref

end Lvm.VEq
