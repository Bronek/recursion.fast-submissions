-- New for lvm (WP-14a, H2): V_S's phases 4 and 6 (`dKec`: the caller's instance point and lanes, the
-- Keccak GKR, ring switching) refine WP-8's caller program (`Lvm.KG.callerProg`) on the stream.
import LvmVEqKecAlg

/-!
# The Keccak GKR and ring switching: V_S refines the verifier language

`Lvm.keccakPackRounds`, `verifyKeccakLayer`, `keccakLayers`, `keccakOpen`, `verifyKeccak`,
`ringSwitch` (over `FE`, on the reader `DM`) refine their `LvmVCore` twins (over `E`) wherever V_S's
checks hold (`RefAt`), generic in the commitment table `cap shp` and the stream `sig`; values are
related by `FE.toExt3` (a claim by `kcE`, `verifyKeccak`'s output by `koE`), the pure parts by
`LvmVEqKecAlg`. The language's `verifyKeccak` branches on `1 < keccakSegments`, which holds
(`keccakSegments = 2`); its committed-output block is reassociated (`bind_assoc`) to V_S's
straight line. Each native function never clears a failed check (`MonoD`).

Headline: **`ref_dKec h`**, V_S's `dKec h` refines `Lvm.KG.callerProg h` with `KecRel h`, and
**`keccakClaims_rel`**: related outputs give related block claims (`BCRel`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (tE_add tE_mul tE_zero tE_one FE_eq_of_beq)

/-! ## Returns of native steps -/

/-- Every value the native step returns satisfies `Q`. -/
def RetD {β : Type} (Q : β → Prop) (d : DM β) : Prop := ∀ sig s, Q (runD d sig s).1

theorem RetD.bind {β β' : Type} {Q' : β → Prop} {Q : β' → Prop} {d : DM β} {d' : β → DM β'}
    (h : RetD Q' d) (h' : ∀ b, Q' b → RetD Q (d' b)) : RetD Q (d >>= d') :=
  fun sig s ↦ h' _ (h sig s) sig _

theorem RetD.bind_true {β β' : Type} {Q : β' → Prop} {d : DM β} {d' : β → DM β'}
    (h' : ∀ b, RetD Q (d' b)) : RetD Q (d >>= d') :=
  fun sig _ ↦ h' _ sig _

theorem RetD.pure {β : Type} {Q : β → Prop} {b : β} (h : Q b) : RetD Q (Pure.pure b : DM β) :=
  fun _ _ ↦ h

theorem retD_samples : ∀ n, RetD (fun xs : List FE ↦ xs.length = n) (DM.samples n)
  | 0 => RetD.pure rfl
  | n + 1 => RetD.bind_true fun _ ↦ (retD_samples n).bind fun _ h ↦ RetD.pure (by simp [h])

theorem retD_readEs : ∀ n, RetD (fun xs : List FE ↦ xs.length = n) (DM.readEs n)
  | 0 => RetD.pure rfl
  | n + 1 => RetD.bind_true fun _ ↦ (retD_readEs n).bind fun _ h ↦ RetD.pure (by simp [h])

theorem retD_sumcheck (count : ℕ) : ∀ (eqs : List (Option FE)) (claim : FE),
    RetD (fun r : List FE × FE ↦ r.1.length = eqs.length) (Lvm.sumcheck claim count eqs)
  | [], _ => RetD.pure rfl
  | _ :: eqs, _ => RetD.bind_true fun _ ↦ RetD.bind_true fun _ ↦
      (retD_sumcheck count eqs _).bind fun ⟨_, _⟩ h ↦ RetD.pure (by simp [h])

/-- A refinement with a fact on the native value. -/
theorem RefAt.retD {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} {α β : Type} {d : DM β}
    {P : VerifierProgram α} {R : β → α → Prop} {Q : β → Prop} (h : RefAt cap occ shp sig d P R)
    (hq : RetD Q d) : RefAt cap occ shp sig d P fun b a ↦ R b a ∧ Q b := fun s hok ↦ by
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, hq sig s⟩

/-! ## Checks over `E` -/

/-- V_S's `x == y` against the language's `x' = y'`. -/
theorem req_of {x y : FE} {x' y' : E} (hx : FE.toExt3 x = x') (hy : FE.toExt3 y = y') :
    (x == y) = true → x' = y' := fun h ↦ hx ▸ hy ▸ congrArg FE.toExt3 (FE_eq_of_beq h)

theorem toExt3_check1 {p i m : FE} {p' i' m' : E} (h1 : FE.toExt3 p = p') (h2 : FE.toExt3 i = i')
    (h3 : FE.toExt3 m = m') : FE.toExt3 (p + i * m) = p' + i' * m' := by
  rw [tE_add, tE_mul, h1, h2, h3]

theorem toExt3_check2 {sc w κ t0 t1 t2 : FE} {sc' w' κ' t0' t1' t2' : E} (h1 : FE.toExt3 sc = sc')
    (h2 : FE.toExt3 w = w') (h3 : FE.toExt3 κ = κ') (h4 : FE.toExt3 t0 = t0')
    (h5 : FE.toExt3 t1 = t1') (h6 : FE.toExt3 t2 = t2') :
    FE.toExt3 (sc * w * (κ * t0 + (κ + t1) * t2)) = sc' * w' * (κ' * t0' + (κ' + t1') * t2') := by
  simp only [tE_mul, tE_add, h1, h2, h3, h4, h5, h6]

theorem toExt3_mul_of {a b : FE} {a' b' : E} (h1 : FE.toExt3 a = a') (h2 : FE.toExt3 b = b') :
    FE.toExt3 (a * b) = a' * b' := by
  rw [tE_mul, h1, h2]

theorem kc_ext {a a' : E} {b b' c c' d d' : List E} (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : (⟨a, b, c, d⟩ : Verifier.KeccakClaim) = ⟨a', b', c', d'⟩ := by
  subst h1 h2 h3 h4; rfl

/-! ## `MonoD` -/

theorem monoD_keccakPackRounds : ∀ (rs : List FE) (value scale : FE),
    MonoD (Lvm.keccakPackRounds rs value scale)
  | [], _, _ => MonoD.pure _
  | r :: rs, value, _ => (monoD_sumcheckRoundPoly 3 value (some r)).bind fun _ ↦
      monoD_sampleE.bind fun _ ↦ (monoD_keccakPackRounds rs _ _).bind fun ⟨_, _, _⟩ ↦ MonoD.pure _

theorem monoD_verifyKeccakLayer (logSteps step : ℕ) (c : Lvm.KeccakClaim) :
    MonoD (Lvm.verifyKeccakLayer logSteps step c) :=
  (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_keccakPackRounds _ _ _).bind fun ⟨_, _, _⟩ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        MonoD.pure _

theorem monoD_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (c : Lvm.KeccakClaim),
    MonoD (Lvm.keccakLayers logSteps steps c)
  | [], _ => MonoD.pure _
  | s :: steps, c => (monoD_verifyKeccakLayer logSteps s c).bind fun _ ↦
      monoD_keccakLayers logSteps steps _

theorem monoD_keccakOpen (logSteps : ℕ) (c : Lvm.KeccakClaim) (first count : ℕ) (value : FE) :
    MonoD (Lvm.keccakOpen logSteps c first count value) :=
  (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦ MonoD.pure _

theorem monoD_verifyKeccak (logSteps : ℕ) (inst output : List FE) :
    MonoD (Lvm.verifyKeccak logSteps inst output) :=
  (monoD_samples _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ monoD_readE.bind fun _ ↦
    (monoD_keccakLayers _ _ _).bind fun _ ↦ (monoD_keccakOpen _ _ _ _ _).bind fun ⟨_, _, _⟩ ↦
      monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind
        fun ⟨_, _⟩ ↦ (monoD_keccakOpen _ _ _ _ _).bind fun ⟨_, _, _⟩ ↦ (monoD_readEs _).bind
          fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_ringSwitch (point s : List FE) : MonoD (Lvm.ringSwitch point s) :=
  (monoD_samples _).bind fun _ ↦ MonoD.pure _

/-- **V_S's phases 4 and 6 never clear a failed check.** -/
theorem monoD_dKec (h : ℕ) : MonoD (dKec h) :=
  (monoD_samples h).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ (monoD_verifyKeccak _ _ _).bind
    fun _ ↦ (monoD_ringSwitch _ _).bind fun _ ↦ MonoD.pure _

/-! ## Refinement -/

/-- `verify_keccak`'s output over `E` (the language's: the committed-output word claim on
`q_keccak`, the slice point, the slices). -/
def koE (ko : Lvm.KeccakOut) : List Verifier.ColumnClaim × List E × List E :=
  ([⟨Verifier.qkeccak, ko.wordPoint.map FE.toExt3, FE.toExt3 ko.word⟩],
    ko.slicePoint.map FE.toExt3, ko.slices.map FE.toExt3)

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **The pack and segment rounds of a layer.** -/
theorem ref_keccakPackRounds : ∀ (rs : List FE) (value scale : FE),
    RefAt cap occ shp sig (Lvm.keccakPackRounds rs value scale)
      (Verifier.keccakPackRounds (rs.map FE.toExt3) (FE.toExt3 value) (FE.toExt3 scale))
      fun r r' ↦ r' = (FE.toExt3 r.1, FE.toExt3 r.2.1, r.2.2.map FE.toExt3)
  | [], _, _ => RefAt.pure rfl
  | r :: rs, value, scale => by
    refine RefAt.bind (fun _ ↦ monoD_sampleE.bind fun _ ↦
      (monoD_keccakPackRounds rs _ _).bind fun ⟨_, _, _⟩ ↦ MonoD.pure _)
      (ref_sumcheckRoundPoly 3 value (some r)) ?_
    rintro m _ rfl
    refine RefAt.bind (fun _ ↦ (monoD_keccakPackRounds rs _ _).bind fun ⟨_, _, _⟩ ↦ MonoD.pure _)
      ref_sampleE ?_
    rintro ch _ rfl
    have h := ref_keccakPackRounds rs ((1 + r + ch) * Lvm.polyEval m ch) (scale * (1 + r + ch))
    rw [tE_mul, tE_mul, tE_add, tE_add, tE_one, toExt3_polyEval] at h
    refine RefAt.bind (fun ⟨_, _, _⟩ ↦ MonoD.pure _) h ?_
    rintro ⟨v, sc, pt⟩ _ rfl
    exact RefAt.pure rfl

/-- **A layer**: the claim on the states a layer further down. -/
theorem ref_verifyKeccakLayer (logSteps step : ℕ) (c : Lvm.KeccakClaim) :
    RefAt cap occ shp sig (Lvm.verifyKeccakLayer logSteps step c)
      (Verifier.verifyKeccakLayer logSteps step (kcE c)) fun r r' ↦ r' = kcE r := by
  unfold Lvm.verifyKeccakLayer Verifier.verifyKeccakLayer
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_keccakPackRounds _ _ _).bind fun ⟨_, _, _⟩ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        MonoD.pure _) (ref_readEs _) ?_
  rintro product _ rfl
  refine RefAt.bind (fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_keccakPackRounds _ _ _).bind fun ⟨_, _, _⟩ ↦ (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
        MonoD.pure _)
    (RefAt.require fun hc ↦ req_of (toExt3_check1 (toExt3_projected _ _) (toExt3_iota _ _ _ _)
      (toExt3_sumE _)) rfl hc) ?_
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

/-- **The layers.** -/
theorem ref_keccakLayers (logSteps : ℕ) : ∀ (steps : List ℕ) (c : Lvm.KeccakClaim),
    RefAt cap occ shp sig (Lvm.keccakLayers logSteps steps c)
      (Verifier.keccakLayers logSteps steps (kcE c)) fun r r' ↦ r' = kcE r
  | [], _ => RefAt.pure rfl
  | s :: steps, c => by
    rw [Lvm.keccakLayers, Verifier.keccakLayers]
    refine RefAt.bind (fun _ ↦ monoD_keccakLayers logSteps steps _)
      (ref_verifyKeccakLayer logSteps s c) ?_
    rintro c' _ rfl
    exact ref_keccakLayers logSteps steps c'

/-- **An opening of `q_keccak`**: the slot, the weights there, what is left to match. -/
theorem ref_keccakOpen (logSteps : ℕ) (c : Lvm.KeccakClaim) (first count : ℕ) (value : FE) :
    RefAt cap occ shp sig (Lvm.keccakOpen logSteps c first count value)
      (Verifier.keccakOpen logSteps (kcE c) first count (FE.toExt3 value))
      fun r r' ↦ r' = (r.1.map FE.toExt3, r.2.1.map FE.toExt3, FE.toExt3 r.2.2) := by
  unfold Lvm.keccakOpen Verifier.keccakOpen
  rw [slotBits_eq]
  have hs := ref_sumcheck 3 (List.replicate Verifier.qkeccakSlotBits none) value (cap := cap) (occ := occ)
    (shp := shp) (sig := sig)
  simp only [List.map_replicate, Option.map_none] at hs
  refine RefAt.bind (fun ⟨_, _⟩ ↦ MonoD.pure _) hs ?_
  rintro ⟨slot, v⟩ _ rfl
  refine RefAt.pure ?_
  simp only [Prod.mk.injEq, true_and, and_true]
  rw [← map_keccakSlotWeights, ← map_slotFold, ← List.headD_map (f := List.map FE.toExt3)]
  rfl

/-- **`verify_keccak`**: the committed-output word claim, the slice point and the slices. -/
theorem ref_verifyKeccak (logSteps : ℕ) (inst output : List FE) :
    RefAt cap occ shp sig (Lvm.verifyKeccak logSteps inst output)
      (Verifier.verifyKeccak logSteps (inst.map FE.toExt3) (output.map FE.toExt3))
      fun r r' ↦ r' = koE r := by
  unfold Lvm.verifyKeccak Verifier.verifyKeccak
  simp only [show 1 < Verifier.keccakSegments from by decide, ↓reduceIte]
  rw [segmentBits_eq]
  refine RefAt.bind (fun _ ↦ (monoD_samples _).bind fun _ ↦ monoD_readE.bind fun _ ↦
    (monoD_keccakLayers _ _ _).bind fun _ ↦ (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦
    monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_samples _) ?_
  rintro seg _ rfl
  refine RefAt.bind (fun _ ↦ monoD_readE.bind fun _ ↦
    (monoD_keccakLayers _ _ _).bind fun _ ↦ (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦
    monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_samples _) ?_
  rintro lanePoint _ rfl
  refine RefAt.bind (fun _ ↦
    (monoD_keccakLayers _ _ _).bind fun _ ↦ (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦
    monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_readE ?_
  rintro com _ rfl
  rw [← kcE_keccakFirstClaim]
  refine RefAt.bind (fun _ ↦ (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦
    monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_keccakLayers logSteps _ _) ?_
  rintro claim _ rfl
  refine RefAt.bind (fun _ ↦
    monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_keccakOpen _ _ _ _ _) ?_
  rintro ⟨slot, weights, value⟩ _ rfl
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_readE ?_
  rintro word _ rfl
  refine RefAt.bind (fun _ ↦ (monoD_sumcheck _ _ _).bind fun _ ↦
    (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (RefAt.require fun hc ↦ req_of (toExt3_mul_of (toExt3_headD _) rfl) rfl hc) ?_
  rintro _ _ _
  rw [pure_bind]
  have hs := (ref_sumcheck 3 (List.replicate 4 none) claim.value (cap := cap) (occ := occ) (shp := shp)
    (sig := sig))
  simp only [List.map_replicate, Option.map_none] at hs
  refine RefAt.bind (fun _ ↦ (monoD_keccakOpen _ _ _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro ⟨low, value⟩ _ rfl
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_keccakOpen _ _ _ _ _) ?_
  rintro ⟨slot', weights', value'⟩ _ rfl
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEs _) ?_
  rintro slices _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ req_of (toExt3_mul_of
    (toExt3_multilinearEval _ _) (toExt3_dot _ _)) rfl hc) ?_
  rintro _ _ _
  refine RefAt.pure ?_
  simp [koE, kcE, List.map_append, List.map_take]

/-- **Ring switching**: the target, and the weight on every image point. -/
theorem ref_ringSwitch (point s : List FE) :
    RefAt cap occ shp sig (Lvm.ringSwitch point s)
      (Verifier.ringSwitch (point.map FE.toExt3) (s.map FE.toExt3))
      fun r r' ↦ r'.1 = FE.toExt3 r.1 ∧ ∀ xs, r'.2 (xs.map FE.toExt3) = FE.toExt3 (r.2 xs) := by
  unfold Lvm.ringSwitch Verifier.ringSwitch
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_samples _) ?_
  rintro ch _ rfl
  refine RefAt.pure ⟨?_, fun xs ↦ ?_⟩
  · rw [toExt3_polyEval, toExt3_gen]
    simp only [List.map_map]
    congr 1
    exact List.map_congr_left fun v _ ↦ (toExt3_phiMap v ch).symm
  · rw [toExt3_ringWeight, map_ringCoefficients]

/-- The relation of V_S's phase output and WP-8's caller program's: the instance point and the
lanes (with their lengths), the committed-output word claim, the ring-switching target, and its
weight on every image point. -/
def KecRel (h : ℕ) (r : List FE × List FE × Lvm.KeccakOut × (FE × (List FE → FE)))
    (co : CallerOut) : Prop :=
  co.1 = r.1.map FE.toExt3 ∧ co.2.1 = r.2.1.map FE.toExt3 ∧ r.1.length = h ∧ r.2.1.length = 25 ∧
    co.2.2.1.1.map (fun c ↦ (c.point, c.value)) =
      [(r.2.2.1.wordPoint.map FE.toExt3, FE.toExt3 r.2.2.1.word)] ∧
    co.2.2.2.1 = FE.toExt3 r.2.2.2.1 ∧ ∀ xs, co.2.2.2.2 (xs.map FE.toExt3) = FE.toExt3 (r.2.2.2.2 xs)

/-- **V_S's phases 4 and 6 refine WP-8's caller program.** -/
theorem ref_dKec (h : ℕ) : RefAt cap occ shp sig (dKec h) (Lvm.KG.callerProg h) (KecRel h) := by
  unfold dKec Lvm.KG.callerProg
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (monoD_verifyKeccak _ _ _).bind fun _ ↦
    (monoD_ringSwitch _ _).bind fun _ ↦ MonoD.pure _) ((ref_samples h).retD (retD_samples h)) ?_
  rintro r _ ⟨rfl, hr⟩
  refine RefAt.bind (fun _ ↦ (monoD_verifyKeccak _ _ _).bind fun _ ↦
    (monoD_ringSwitch _ _).bind fun _ ↦ MonoD.pure _) ((ref_readEs _).retD (retD_readEs _)) ?_
  rintro v _ ⟨rfl, hv⟩
  refine RefAt.bind (fun _ ↦ (monoD_ringSwitch _ _).bind fun _ ↦ MonoD.pure _)
    (ref_verifyKeccak h r v) ?_
  rintro ko _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_ringSwitch _ _) ?_
  rintro ring ring' ⟨h1, h2⟩
  exact RefAt.pure ⟨rfl, rfl, hr, hv, rfl, h1, h2⟩

end Ref

/-- **Related outputs give related block claims** (V_S's `keccakClaims` against the language's
`keccakClaimsE`, on the same block). -/
theorem keccakClaims_rel {h : ℕ} {r : List FE × List FE × Lvm.KeccakOut × (FE × (List FE → FE))}
    {co : CallerOut} (hk : KecRel h r co) (blk : Lvm.Placement) :
    List.Forall₂ BCRel (keccakClaims blk r.2.2.1 r.2.2.2) (keccakClaimsE (plE blk) co) := by
  obtain ⟨-, -, -, -, h5, h6, h7⟩ := hk
  have hw : co.2.2.1.1.map (fun c ↦ BClaim.point (plE blk) c.point c.value) =
      [BClaim.point (plE blk) (r.2.2.1.wordPoint.map FE.toExt3) (FE.toExt3 r.2.2.1.word)] := by
    have := congrArg (List.map fun p : List E × E ↦ BClaim.point (plE blk) p.1 p.2) h5
    simpa [List.map_map] using this
  unfold keccakClaims keccakClaimsE
  rw [hw]
  exact List.Forall₂.cons ⟨rfl, rfl, fun xs ↦ (toExt3_eqEval _ _).symm⟩
    (List.Forall₂.cons ⟨rfl, h6, h7⟩ List.Forall₂.nil)

end Lvm.VEq
