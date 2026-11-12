-- New for lvm2 (WP T-V, stage S2): V_S's wire phase (LvmDecideTape `dWire`, over `FE`) refines T-W's
-- chain wiring program (`Lvm.KG.wireChProg`, over `E`) on the stream; the `FE` twins of T-K's kernels
-- and T-W's dot products are their originals through `FE.toExt3`.
import LvmVEqKec
import LvmWireSpec
import LvmChainTablePad
import LvmDecideTape

/-!
# The wire phase: V_S refines the verifier language

* **The twins** (`LvmDecideTape` against `LvmWireKernel`, `LvmWireSpec`): `toExt3_eqAtF`,
  `toExt3_iotaF`, `ms4E_msTailF` (T-K's automaton, entry by entry), `toExt3_msEvalF`,
  `p2E_thrTailF`, `toExt3_thrEvalF`, `toExt3_c43DotF`, `toExt3_padDotF` (the digest's lanes
  `digestLanes d` carry the bits `digestBits d`, `digestLanes_bit`), `toExt3_wireTargetF`,
  `toExt3_slotWF` and its dot form `toExt3_slotDot`.
* **`ref_dWire`**: wherever V_S's wire phase ends with its checks held, `wireChProg p.logN
  (dSelBits p) (dSel p) d pub.n (kcE claim)` read off the stream returns at the same cursor an output
  related by `WireRel`, provided the header's `s` lanes are the digest's (`pub.s = digestLanes d`).
  Read for read: the wiring sumcheck (`ref_sumcheck`), `g_D`, the check against `msEval`, then
  `D`'s slot reduction (`ref_dSlotD`: two rounds, 64 slices, the slot check, the ring switch). The
  native slot block is reassociated (`dWire_eq`) to the language's `slotProg` bind.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Finset
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_cons bitE)
open Lvm.M3 (tE_add tE_mul tE_zero tE_one FE_eq_of_beq)

/-! ## Helpers -/

namespace Wr

theorem sumE_range (f : ℕ → FE) (n : ℕ) :
    FE.toExt3 (Lvm.sumE ((List.range n).map f)) = ∑ j ∈ range n, FE.toExt3 (f j) := by
  rw [toExt3_sumE, List.map_map, sumE_map_range]
  rfl

theorem getD_eqKernel (p : List FE) {i : ℕ} (hi : i < 2 ^ p.length) :
    FE.toExt3 ((Lvm.eqKernel p).getD i 0) = eqAt (p.map FE.toExt3) i := by
  rw [← getD_map_toExt3, map_eqKernel, LeanVM.Protocol.KeccakGkr.eqKernel_getD, List.length_map,
    ite_eq_left hi]

end Wr

/-! ## T-K's kernels -/

theorem toExt3_eqAtF : ∀ (pt : List FE) (w : ℕ), FE.toExt3 (eqAtF pt w) = eqAt (pt.map FE.toExt3) w
  | [], _ => tE_one
  | r :: rs, w => by
    rw [eqAtF, List.map_cons, eqAt_cons, tE_mul, toExt3_eqAtF rs, apply_ite FE.toExt3, tE_add, tE_one]

theorem toExt3_iotaF (ρ μ : List FE) (i : ℕ) :
    FE.toExt3 (iotaF ρ μ i) = Lvm.WK.iota (ρ.map FE.toExt3) (μ.map FE.toExt3) i := by
  rw [iotaF, Lvm.WK.iota, tE_mul, toExt3_eqAtF, getD_map_toExt3]

theorem toExt3_eqBitF (a : FE) (b : Bool) : FE.toExt3 (eqBitF a b) = Lvm.WK.eqBit (FE.toExt3 a) b := by
  cases b
  · show FE.toExt3 (1 + a) = 1 + FE.toExt3 a
    rw [tE_add, tE_one]
  · rfl

theorem nextSF_eq : nextSF = Lvm.WK.nextS := rfl

/-- An automaton vector over `E`. -/
def ms4E (q : MS4F) : Lvm.WK.MS4 :=
  ⟨FE.toExt3 q.v00, FE.toExt3 q.v01, FE.toExt3 q.v10, FE.toExt3 q.v11⟩

theorem ms4E_get (q : MS4F) (c s : Bool) : (ms4E q).get c s = FE.toExt3 (q.get c s) := by
  cases c <;> cases s <;> rfl

theorem ms4E_mk (a b c d : FE) :
    ms4E ⟨a, b, c, d⟩ = ⟨FE.toExt3 a, FE.toExt3 b, FE.toExt3 c, FE.toExt3 d⟩ := rfl

theorem ms4E_msStepF (a r : FE) (tb : Bool) (q : MS4F) :
    ms4E (msStepF a r tb q) = Lvm.WK.msStep (FE.toExt3 a) (FE.toExt3 r) tb (ms4E q) := by
  simp only [msStepF, Lvm.WK.msStep, ms4E_mk, tE_add, tE_mul, tE_one, toExt3_eqBitF, ← ms4E_get,
    nextSF_eq]

/-- **T-K's automaton** over the high bits, entry by entry. -/
theorem ms4E_msTailF : ∀ (σ ρ : List FE) (t : ℕ),
    ms4E (msTailF σ ρ t) = Lvm.WK.msTail (σ.map FE.toExt3) (ρ.map FE.toExt3) t
  | a :: σ, r :: ρ, t => by
    rw [List.map_cons, List.map_cons, msTailF, Lvm.WK.msTail, ms4E_msStepF, ms4E_msTailF σ ρ]
  | [], ρ, t => by
    show ms4E ⟨1, if 1 ≤ t then 1 else 0, 0, 0⟩ = ⟨1, if 1 ≤ t then 1 else 0, 0, 0⟩
    rw [ms4E_mk, tE_one, apply_ite FE.toExt3, tE_one, tE_zero]
  | _ :: _, [], t => by
    show ms4E ⟨1, if 1 ≤ t then 1 else 0, 0, 0⟩ = ⟨1, if 1 ≤ t then 1 else 0, 0, 0⟩
    rw [ms4E_mk, tE_one, apply_ite FE.toExt3, tE_one, tE_zero]

/-- **`K̃_ch(σ)`**: V_S's `msEvalF` is T-K's `msEval`. -/
theorem toExt3_msEvalF (ρ μ σ : List FE) (base t : ℕ) :
    FE.toExt3 (msEvalF ρ μ σ base t) =
      Lvm.WK.msEval (ρ.map FE.toExt3) (μ.map FE.toExt3) (σ.map FE.toExt3) base t := by
  simp only [msEvalF, Lvm.WK.msEval, List.length_map, ← List.map_drop, ← List.map_take,
    ← ms4E_msTailF, tE_mul, toExt3_eqAtF, toExt3_sumE, List.map_map]
  congr 2
  refine List.map_congr_left fun d _ ↦ ?_
  simp only [Function.comp_apply, tE_mul, toExt3_eqAtF, getD_map_toExt3, ms4E_get]

theorem tE_ite (c : Prop) [Decidable c] (x y : FE) :
    FE.toExt3 (if c then x else y) = if c then FE.toExt3 x else FE.toExt3 y :=
  apply_ite _ _ _ _

/-- A pair over `E`. -/
def p2E (q : FE × FE) : E × E := (FE.toExt3 q.1, FE.toExt3 q.2)

theorem p2E_thrTailF : ∀ (ρ : List FE) (t : ℕ),
    p2E (thrTailF ρ t) = Lvm.WK.thrTail (ρ.map FE.toExt3) t
  | [], t => by
    show (FE.toExt3 1, FE.toExt3 (if 1 ≤ t then 1 else 0)) = (1, if 1 ≤ t then 1 else 0)
    rw [tE_one, apply_ite FE.toExt3, tE_one, tE_zero]
  | r :: ρ, t => by
    rw [List.map_cons, Lvm.WK.thrTail, ← p2E_thrTailF ρ (t / 2)]
    simp only [thrTailF, p2E, tE_add, tE_mul, tE_one, tE_ite]
    rw [nextSF_eq]

/-- **`Σ_{i ≤ t} ι(i)`**: V_S's `thrEvalF` is T-K's `thrEval`. -/
theorem toExt3_thrEvalF (ρ μ : List FE) (t : ℕ) :
    FE.toExt3 (thrEvalF ρ μ t) = Lvm.WK.thrEval (ρ.map FE.toExt3) (μ.map FE.toExt3) t := by
  simp only [thrEvalF, Lvm.WK.thrEval, ← p2E_thrTailF, toExt3_sumE, List.map_map]
  congr 1
  refine List.map_congr_left fun d _ ↦ ?_
  simp only [Function.comp_apply, tE_mul, getD_map_toExt3, apply_ite FE.toExt3, p2E]

/-! ## T-W's dot products -/

theorem pad43Bit_false (j : ℕ) :
    Lvm.KG.pad43Bit (fun _ ↦ false) j = decide (j ∈ ({0, 1, 6, 264, 1087} : Finset ℕ)) := by
  unfold Lvm.KG.pad43Bit
  by_cases h1 : j < 8
  · rw [ite_eq_left h1]
    interval_cases j <;> rfl
  · rw [ite_eq_right h1]
    by_cases h2 : j < 264
    · rw [ite_eq_left h2]
      exact (decide_eq_false (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)).symm
    · rw [ite_eq_right h2]
      exact decide_eq_decide.2 (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)

/-- `⟨ω, c43⟩` is the five constant positions. -/
theorem c43Dot_eq (ω : List E) :
    Lvm.KG.c43Dot ω = ω.getD 0 0 + ω.getD 1 0 + ω.getD 6 0 + ω.getD 264 0 + ω.getD 1087 0 := by
  have hb : ∀ j, ω.getD j 0 * bitE (Lvm.KG.pad43Bit (fun _ ↦ false) j) =
      if j ∈ ({0, 1, 6, 264, 1087} : Finset ℕ) then ω.getD j 0 else 0 := by
    intro j
    rw [pad43Bit_false]
    by_cases h : j ∈ ({0, 1, 6, 264, 1087} : Finset ℕ) <;> simp [h, bitE]
  rw [Lvm.KG.c43Dot, Lvm.KG.padDot, Finset.sum_congr rfl fun j _ ↦ hb j, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 fun x hx ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega]
  simp [add_assoc]

theorem toExt3_c43DotF (w : List FE) :
    FE.toExt3 (c43DotF w.toArray) = Lvm.KG.c43Dot (w.map FE.toExt3) := by
  rw [c43Dot_eq, c43DotF]
  simp only [tE_add, arr_getD_toArray, getD_map_toExt3]

/-- **The digest's lanes carry its bits**: bit `p % 64` of lane `p / 64` of `digestLanes d` is
`digestBits d p`. -/
theorem digestLanes_bit (d : RecursionFast.Digest) {p : ℕ} (hp : p < 256) :
    ((digestLanes d).getD (p / 64) 0).val.toNat.testBit (p % 64) = Lvm.KG.digestBits d p := by
  have hl : (digestLanes d).getD (p / 64) 0 = ⟨RecursionFast.Keccak.blockLane d.toArray (p / 64)⟩ := by
    rw [digestLanes, getD_map_range _ _ _ _ (by omega)]
    rfl
  rw [hl, Lvm.KG.digestBits_lane d hp]
  exact BitVec.testBit_toNat _

/-- **`⟨ω, Pad43(d)⟩`**: V_S's `padDotF` on the digest's lanes is T-W's `padDot`. -/
theorem toExt3_padDotF (w : List FE) (d : RecursionFast.Digest) :
    FE.toExt3 (padDotF w.toArray (digestLanes d)) =
      Lvm.KG.padDot (w.map FE.toExt3) (Lvm.KG.digestBits d) := by
  rw [padDotF, tE_add, toExt3_c43DotF, Lvm.KG.padDot_split, Wr.sumE_range]
  congr 1
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [digestLanes_bit d (Finset.mem_range.1 hp)]
  cases Lvm.KG.digestBits d p
  · simp only [Bool.false_eq_true, ↓reduceIte, tE_zero, LeanVM.Protocol.KeccakGkr.bitE_false,
      mul_zero]
  · simp only [↓reduceIte, LeanVM.Protocol.KeccakGkr.bitE_true, mul_one, arr_getD_toArray,
      getD_map_toExt3]

/-- **The wiring target**: V_S's `wireTargetF` on the digest's lanes is T-W's `wireTarget`. -/
theorem toExt3_wireTargetF (d : RecursionFast.Digest) (n : ℕ) (c : Lvm.KeccakClaim) :
    FE.toExt3 (wireTargetF (digestLanes d) n c) = Lvm.KG.wireTarget d n (kcE c) := by
  simp only [wireTargetF, Lvm.KG.wireTarget, kcE, tE_add, tE_mul, toExt3_iotaF, toExt3_padDotF,
    toExt3_c43DotF, toExt3_thrEvalF]

/-- **`D`'s slot weights at `τ`** (two slot bits). -/
theorem toExt3_slotWF (w τ : List FE) (hτ : τ.length = 2) :
    (slotWF w.toArray τ).map FE.toExt3 =
      (List.range 64).map (Lvm.KG.slotWE 2 (Lvm.KG.dW (w.map FE.toExt3)) (τ.map FE.toExt3)) := by
  rw [slotWF, List.map_map]
  refine List.map_congr_left fun z _ ↦ ?_
  rw [Function.comp_apply, Wr.sumE_range, Lvm.KG.slotWE, show (2 : ℕ) ^ 2 = 4 from rfl]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [tE_mul, Wr.getD_eqKernel _ (by rw [hτ]; exact Finset.mem_range.1 hl), Lvm.KG.dW,
    arr_getD_toArray, getD_map_toExt3]

/-- The slot check's right-hand side. -/
theorem toExt3_slotDot (w τ sv : List FE) (hτ : τ.length = 2) :
    FE.toExt3 (Lvm.dot (slotWF w.toArray τ) sv) =
      ∑ z ∈ range 64, Lvm.KG.slotWE 2 (Lvm.KG.dW (w.map FE.toExt3)) (τ.map FE.toExt3) z *
        (sv.map FE.toExt3).getD z 0 := by
  rw [toExt3_dot, toExt3_slotWF w τ hτ, dot_eq_sum_left, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  rw [getD_map_range _ _ _ _ (Finset.mem_range.1 hz)]

/-! ## The native slot block -/

/-- V_S's slot reduction of `D` (the tail of `dWire`): two rounds, 64 slices, the slot check, the
ring switch at `pt ‖ τ ‖ sel(blk)`. -/
def dSlotD (claim : Lvm.KeccakClaim) (pt : List FE) (sb blk : ℕ) (v : FE) :
    DM ((List FE × FE) × List FE × (FE × (List FE → FE))) := do
  let sl ← Lvm.sumcheck v 3 [none, none]
  let sv ← readEs kBits
  require (sl.2 == Lvm.dot (slotWF claim.weights.toArray sl.1) sv)
  let ring ← Lvm.ringSwitch (pt ++ sl.1 ++ Lvm.selectorPoint blk sb) sv
  pure (sl, sv, ring)

/-- `dWire` with its slot block reassociated. -/
theorem dWire_eq (p : Params) (pub : Pub) (claim : Lvm.KeccakClaim) :
    dWire p pub claim = (do
      let sc ← Lvm.sumcheck (wireTargetF pub.s pub.n claim) 3 (List.replicate p.logN none)
      let g ← readEs 1
      require (sc.2 == msEvalF claim.point claim.mu sc.1 0 (pub.n - 1) * g.getD 0 0)
      let x ← dSlotD claim sc.1 (dSelBits p) (dSel p) (g.getD 0 0)
      pure ⟨sc, g, x.1, x.2.1, x.2.2⟩) := by
  simp only [dWire, dSlotD, bind_assoc, pure_bind]

/-! ## `MonoD` -/

theorem monoD_dSlotD (claim : Lvm.KeccakClaim) (pt : List FE) (sb blk : ℕ) (v : FE) :
    MonoD (dSlotD claim pt sb blk v) :=
  (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_ringSwitch _ _).bind fun _ ↦ MonoD.pure _

/-- **V_S's wire phase never clears a failed check.** -/
theorem monoD_dWire (p : Params) (pub : Pub) (claim : Lvm.KeccakClaim) :
    MonoD (dWire p pub claim) := by
  rw [dWire_eq]
  exact (monoD_sumcheck _ _ _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    (MonoD.require _).bind fun _ ↦ (monoD_dSlotD _ _ _ _ _).bind fun _ ↦ MonoD.pure _

/-! ## Refinement -/

/-- The relation of V_S's slot block and T-W's `slotProg`: the slot point and claim, the slices,
the ring switch (target, and weight on every image point), the lengths. -/
def SlotRel (x : (List FE × FE) × List FE × (FE × (List FE → FE))) (out : Lvm.KG.SlotOut) : Prop :=
  out.sl = (x.1.1.map FE.toExt3, FE.toExt3 x.1.2) ∧ out.sv = x.2.1.map FE.toExt3 ∧
    out.ring.1 = FE.toExt3 x.2.2.1 ∧ (∀ xs, out.ring.2 (xs.map FE.toExt3) = FE.toExt3 (x.2.2.2 xs)) ∧
    x.1.1.length = 2 ∧ x.2.1.length = 64

/-- **The relation of V_S's wire phase and T-W's `wireChProg`**: the wiring point and final claim,
`g_D`, the slot point and claim, the 64 slices, the ring switch on `C_main` (as in `KecRel`), the
lengths (`|σ| = w`, `|g| = 1`, `|τ| = 2`, 64 slices). -/
def WireRel (w : ℕ) (wo : WireOut) (out : Lvm.KG.WireChOut) : Prop :=
  out.sc = (wo.sc.1.map FE.toExt3, FE.toExt3 wo.sc.2) ∧ out.g = wo.g.map FE.toExt3 ∧
    out.d.sl = (wo.sl.1.map FE.toExt3, FE.toExt3 wo.sl.2) ∧ out.d.sv = wo.sv.map FE.toExt3 ∧
    out.d.ring.1 = FE.toExt3 wo.ring.1 ∧
    (∀ xs, out.d.ring.2 (xs.map FE.toExt3) = FE.toExt3 (wo.ring.2 xs)) ∧
    wo.sc.1.length = w ∧ wo.g.length = 1 ∧ wo.sl.1.length = 2 ∧ wo.sv.length = 64

section Ref

variable {cap : ℕ → ℕ → ℕ} {occ : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **`D`'s slot reduction.** -/
theorem ref_dSlotD (claim : Lvm.KeccakClaim) (pt : List FE) (sb blk : ℕ) (v : FE) :
    RefAt cap occ shp sig (dSlotD claim pt sb blk v)
      (Lvm.KG.slotProg 2 sb blk (Lvm.KG.dW (claim.weights.map FE.toExt3)) (pt.map FE.toExt3)
        (FE.toExt3 v)) SlotRel := by
  unfold dSlotD Lvm.KG.slotProg
  have hs := (ref_sumcheck 3 [none, none] v (cap := cap) (occ := occ) (shp := shp) (sig := sig)).retD
    (retD_sumcheck 3 _ v)
  simp only [List.map_cons, List.map_nil, Option.map_none] at hs
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_ringSwitch _ _).bind fun _ ↦ MonoD.pure _) hs ?_
  rintro ⟨τ, f⟩ _ ⟨rfl, hτ⟩
  replace hτ : τ.length = 2 := hτ
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_ringSwitch _ _).bind fun _ ↦
    MonoD.pure _) ((ref_readEs kBits).retD (retD_readEs kBits)) ?_
  rintro sv _ ⟨rfl, hsv⟩
  refine RefAt.bind (fun _ ↦ (monoD_ringSwitch _ _).bind fun _ ↦ MonoD.pure _)
    (RefAt.require fun hc ↦ req_of rfl (toExt3_slotDot _ _ _ hτ) hc) ?_
  rintro _ _ _
  have hr := ref_ringSwitch (pt ++ τ ++ Lvm.selectorPoint blk sb) sv (cap := cap) (occ := occ) (shp := shp)
    (sig := sig)
  rw [List.map_append, List.map_append, map_selectorPoint] at hr
  refine RefAt.bind (fun _ ↦ MonoD.pure _) hr ?_
  rintro ring _ ⟨h1, h2⟩
  exact RefAt.pure ⟨rfl, rfl, h1, h2, hτ, hsv⟩

/-- **V_S's wire phase refines T-W's chain wiring program**, given that the header's `s` lanes are
the digest `d`'s. -/
theorem ref_dWire (p : Params) (pub : Pub) (claim : Lvm.KeccakClaim) (d : RecursionFast.Digest)
    (hs : pub.s = digestLanes d) :
    RefAt cap occ shp sig (dWire p pub claim)
      (Lvm.KG.wireChProg p.logN (dSelBits p) (dSel p) d pub.n (kcE claim)) (WireRel p.logN) := by
  rw [dWire_eq]
  unfold Lvm.KG.wireChProg
  have h1 := (ref_sumcheck 3 (List.replicate p.logN none) (wireTargetF pub.s pub.n claim) (cap := cap) (occ := occ)
    (shp := shp) (sig := sig)).retD (retD_sumcheck 3 _ _)
  rw [hs, toExt3_wireTargetF, List.map_replicate, Option.map_none] at h1
  rw [hs]
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    (monoD_dSlotD _ _ _ _ _).bind fun _ ↦ MonoD.pure _) h1 ?_
  rintro ⟨σ, f⟩ _ ⟨rfl, hσ⟩
  replace hσ : σ.length = p.logN := by simpa using hσ
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_dSlotD _ _ _ _ _).bind fun _ ↦
    MonoD.pure _) ((ref_readEs 1).retD (retD_readEs 1)) ?_
  rintro g _ ⟨rfl, hg⟩
  refine RefAt.bind (fun _ ↦ (monoD_dSlotD _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAt.require fun hc ↦ req_of rfl (toExt3_mul_of (toExt3_msEvalF _ _ _ _ _)
      (getD_map_toExt3 _ _).symm) hc) ?_
  rintro _ _ _
  rw [getD_map_toExt3]
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dSlotD claim σ (dSelBits p) (dSel p) (g.getD 0 0)) ?_
  rintro x out ⟨e1, e2, e3, e4, e5, e6⟩
  exact RefAt.pure ⟨rfl, rfl, e1, e2, e3, e4, hσ, hg, e5, e6⟩

end Ref

end Lvm.VEq
