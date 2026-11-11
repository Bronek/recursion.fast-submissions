-- New for lvm (WP-14a, H3): V_S's CH/KS link formulas (LvmDecideV0: `shiftEval`, `eqMasked`, `omegaCH`,
-- `padWeight`, `padConst`, the link targets and checks, `contShift`) and its caller-placed ring switch
-- (LvmDecide `ringRaw`) over `E`: WP-8's `shiftEvalE`, `eqMaskedE`, `omegaE`, `padWeightE`, `padConstE`,
-- `chShiftTargetE`, `chSc2TargetE`, `wtE`, `contShiftE` and leanVM's `ringSwitch` (LvmVCore).
import LvmVEqClaims

/-!
# The link formulas over `E`

`FE.toExt3` of each native link formula is WP-8's `E` formula at the mapped arguments. V_S's
equality kernels are tables (`eqKernel`, `eqKernelA`) where WP-8 uses `eqAt`; they agree below
`2^|p|` (`toExt3_getD_eqKernel`, `toExt3_getD_eqKernelA`, WP-2's `eqKernel_getD`), so the lemmas
take the lengths of the challenge lists (`λ` 3, `ζ` 6, `μ` 2, the `KS` points 15).

`ringRaw s` (V_S's caller-placed ring switch: target and Frobenius coefficients) refines leanVM's
`ringSwitch pt s` at any point `pt`: same target, weight `ringWeight pt · coeffs` (`ref_ringRaw`).
The lengths of the native `samples`, `readEs`, `sumcheck` values (`length_*`) enter through
`refAt_withD`. Everything here is in `Lvm.VEq.Lk`.
-/

set_option autoImplicit false

namespace Lvm.VEq.Lk

open Lvm Lvm.VEq DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakGkr Finset
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_ofK)

/-! ## Folds and sums -/

theorem toExt3_foldl {β γ : Type} (ψ : β → γ) (f : FE → β → FE) (g : E → γ → E)
    (h : ∀ a b, FE.toExt3 (f a b) = g (FE.toExt3 a) (ψ b)) :
    ∀ (l : List β) (a : FE), FE.toExt3 (l.foldl f a) = (l.map ψ).foldl g (FE.toExt3 a)
  | [], _ => rfl
  | b :: l, a => by
    simp only [List.foldl_cons, List.map_cons]
    rw [toExt3_foldl ψ f g h l, h]

theorem sumE_map_eq_sum (f : ℕ → E) (n : ℕ) :
    Verifier.sumE ((List.range n).map f) = ∑ j ∈ range n, f j := by
  rw [Whir.Complete.sumE_eq, Lvm.KG.list_sum_map_range]

theorem toExt3_sumE_range (f : ℕ → FE) (n : ℕ) :
    FE.toExt3 (Lvm.sumE ((List.range n).map f)) = ∑ j ∈ range n, FE.toExt3 (f j) := by
  rw [toExt3_sumE, List.map_map, sumE_map_eq_sum]; rfl

/-! ## Equality kernels -/

theorem length_eqKernel_FE (p : List FE) : (Lvm.eqKernel p).length = 2 ^ p.length := by
  rw [← List.length_map (f := FE.toExt3), map_eqKernel, eqKernel_length, List.length_map]

theorem size_eqKernelA (p : List FE) : (Lvm.eqKernelA p).size = 2 ^ p.length := by
  rw [← Array.length_toList, eqKernelA_toList, length_eqKernel_FE]

theorem toExt3_getD_eqKernel (p : List FE) {i : ℕ} (hi : i < 2 ^ p.length) :
    FE.toExt3 ((Lvm.eqKernel p).getD i 0) = eqAt (p.map FE.toExt3) i := by
  rw [← getD_map_toExt3, map_eqKernel, eqKernel_getD, List.length_map, ite_eq_left hi]

theorem toExt3_getD_eqKernelA (p : List FE) {i : ℕ} (hi : i < 2 ^ p.length) :
    FE.toExt3 ((Lvm.eqKernelA p).getD i 0) = eqAt (p.map FE.toExt3) i := by
  rw [getD_eqKernelA, toExt3_getD_eqKernel p hi]

/-! ## `shiftEval`, `eqMasked` -/

theorem toExt3_shiftEval (x y : List FE) :
    FE.toExt3 (Lvm.shiftEval x y) = Lvm.KG.shiftEvalE (x.map FE.toExt3) (y.map FE.toExt3) := by
  unfold Lvm.shiftEval Lvm.KG.shiftEvalE
  simp only [toExt3_sumE, toExt3_prodE, List.map_map, Function.comp_def, tE_mul, tE_add, tE_one,
    getD_map_toExt3, List.length_map]

theorem toExt3_eqMasked (x y : List FE) :
    FE.toExt3 (Lvm.eqMasked x y) = Lvm.KG.eqMaskedE (x.map FE.toExt3) (y.map FE.toExt3) := by
  simp only [Lvm.eqMasked, Lvm.KG.eqMaskedE, Lvm.eqOnes, tE_add, tE_mul, toExt3_eqEval, toExt3_prodE]

/-! ## The `CH` link's weights -/

theorem omegaCH_getD (lam zeta : List FE) {m p : ℕ} (hm : m < 2 ^ lam.length)
    (hp : p < 2 ^ zeta.length) :
    FE.toExt3 (((Lvm.omegaCH lam zeta).getD m #[]).getD p 0) =
      Lvm.KG.omegaE (lam.map FE.toExt3) (zeta.map FE.toExt3) m p := by
  have hL : m < (Lvm.eqKernelA lam).size := by rw [size_eqKernelA]; exact hm
  have hZ : p < (Lvm.eqKernelA zeta).size := by rw [size_eqKernelA]; exact hp
  have h : ((Lvm.omegaCH lam zeta).getD m #[]).getD p 0 =
      (Lvm.eqKernelA lam).getD m 0 * (Lvm.eqKernelA zeta).getD p 0 := by
    simp [Lvm.omegaCH, Array.getD, hL, hZ]
  rw [h, tE_mul, toExt3_getD_eqKernelA lam hm, toExt3_getD_eqKernelA zeta hp]
  rfl

theorem toExt3_padWeight (lam zeta : List FE) (hl : lam.length = 3) (hz : zeta.length = 6) {m q : ℕ}
    (hm : m < 4) (hq : q < 64) :
    FE.toExt3 (Lvm.padWeight (Lvm.omegaCH lam zeta) m q) =
      Lvm.KG.padWeightE (lam.map FE.toExt3) (zeta.map FE.toExt3) m q := by
  unfold Lvm.padWeight Lvm.KG.padWeightE
  split_ifs <;> exact omegaCH_getD _ _ (by rw [hl]; norm_num; omega) (by rw [hz]; norm_num; omega)

theorem toExt3_padConst (lam zeta : List FE) (hl : lam.length = 3) (hz : zeta.length = 6) :
    FE.toExt3 (Lvm.padConst (Lvm.omegaCH lam zeta)) =
      Lvm.KG.padConstE (lam.map FE.toExt3) (zeta.map FE.toExt3) := by
  unfold Lvm.padConst Lvm.KG.padConstE
  rw [tE_add, toExt3_sumE, List.map_filterMap,
    omegaCH_getD _ _ (by rw [hl]; norm_num) (by rw [hz]; norm_num)]
  congr 1
  rw [← sumE_filterMap_range]
  congr 1
  refine List.filterMap_congr fun p hp ↦ ?_
  have hp' := List.mem_range.1 hp
  split_ifs
  · exact congrArg some
      (omegaCH_getD lam zeta (m := 0) (p := p) (by rw [hl]; norm_num) (by rw [hz]; norm_num; omega))
  · rfl

/-- The `CH` link's challenges at `P20`. -/
theorem chSplit_P20 (chal : List FE) :
    Lvm.chSplit P20 chal = (chal.take 20, (chal.drop 20).take 3, chal.drop 23) := rfl

theorem toExt3_chShiftTarget0 (chal : List FE) (hc : chal.length = 29) :
    FE.toExt3 (Lvm.chShiftTarget0 P20 chal) = Lvm.KG.chShiftTargetE 20 (chal.map FE.toExt3) := by
  simp only [Lvm.chShiftTarget0, chSplit_P20, Lvm.KG.chShiftTargetE, Lvm.KG.chLam, Lvm.KG.chZeta,
    Lvm.KG.chRho, tE_mul, tE_add, tE_one, Lvm.eqOnes, toExt3_prodE, ← List.map_take, ← List.map_drop]
  rw [toExt3_padConst _ _ (by simp [hc]) (by simp [hc])]

theorem toExt3_chSc2Target0 (chal : List FE) (shift : List FE × FE) (inS : List FE)
    (hc : chal.length = 29) (hin : inS.length = 64) :
    FE.toExt3 (Lvm.chSc2Target0 P20 chal shift inS) =
      Lvm.KG.chSc2TargetE 20 (chal.map FE.toExt3) (shift.1.map FE.toExt3, FE.toExt3 shift.2)
        (inS.map FE.toExt3) := by
  simp only [Lvm.chSc2Target0, chSplit_P20, Lvm.KG.chSc2TargetE, Lvm.KG.chZeta, Lvm.KG.chRho,
    tE_mul, tE_add, toExt3_shiftEval, toExt3_dot, map_eqKernel, ← List.map_take, ← List.map_drop,
    Nat.reduceAdd]
  congr 2
  have hz : ((chal.drop 23).map FE.toExt3).length = 6 := by simp [hc]
  rw [dot_eq _ _ (by simp [eqKernel_length, hc, hin])]
  simp only [eqKernel_length, hz]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' := Finset.mem_range.1 hp
  rw [eqKernel_getD, hz, ite_eq_left (by norm_num; omega)]

/-- The `CH` link's check. -/
theorem toExt3_chOk (lam zeta mu rho rho' yS : List FE) (hl : lam.length = 3) (hz : zeta.length = 6)
    (hmu : mu.length = 2) :
    FE.toExt3 (Lvm.eqMasked rho rho' * Lvm.sumE ((List.range 64).map fun q =>
        Lvm.sumE ((List.range 4).map fun m =>
          (Lvm.eqKernel mu).getD m 0 * Lvm.padWeight (Lvm.omegaCH lam zeta) m q) * yS.getD q 0)) =
      Lvm.KG.eqMaskedE (rho.map FE.toExt3) (rho'.map FE.toExt3) *
        ∑ q ∈ range 64, Lvm.KG.wtE (lam.map FE.toExt3) (zeta.map FE.toExt3) (mu.map FE.toExt3) q *
          (yS.map FE.toExt3).getD q 0 := by
  rw [tE_mul, toExt3_eqMasked, toExt3_sumE_range]
  congr 1
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [tE_mul, toExt3_sumE_range, getD_map_toExt3]
  congr 1
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm' := Finset.mem_range.1 hm
  rw [tE_mul, toExt3_getD_eqKernel mu (by rw [hmu]; norm_num; omega),
    toExt3_padWeight lam zeta hl hz hm' (Finset.mem_range.1 hq)]

/-! ## The `KS` link -/

/-- `contRows P20` is in `[1, 2^15)`. -/
theorem contRows_bound : ∀ i ∈ contRows P20, 1 ≤ i ∧ i < 2 ^ 15 := by
  have hs : spongeBlocks P20 = 14709 := sizes_P20.2.2.2.2.2.2.2.2
  have h14 : P20.recRowsLog = 14 := rfl
  intro i hi
  simp only [contRows, List.mem_append, List.mem_map, List.mem_range, hs, h14, Nat.reducePow,
    Nat.reduceAdd, Nat.reduceSub] at hi
  rcases hi with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> norm_num <;> omega

theorem toExt3_contShift (rho rho' : List FE) (h1 : rho.length = 15) (h2 : rho'.length = 15) :
    FE.toExt3 (Lvm.contShift P20 rho rho') =
      Lvm.KG.contShiftE (contRows P20) (rho.map FE.toExt3) (rho'.map FE.toExt3) := by
  rw [Lvm.Q1.contShift_fast]
  unfold Lvm.contShiftRef Lvm.KG.contShiftE
  have hb0 := contRows_bound
  generalize contRows P20 = rows at hb0 ⊢
  have hf : ∀ (g : ℕ → FE) (l : List ℕ), l.foldl (fun acc i => acc + g i) 0 = Lvm.sumE (l.map g) :=
    fun g l ↦ by rw [Lvm.sumE, List.foldl_map]
  rw [hf, toExt3_sumE, List.map_map, Whir.Complete.sumE_eq]
  congr 1
  refine List.map_congr_left fun i hi ↦ ?_
  have hb := hb0 i hi
  simp only [Function.comp, tE_mul]
  rw [toExt3_getD_eqKernelA _ (by rw [h1]; omega), toExt3_getD_eqKernelA _ (by rw [h2]; omega)]

/-- The `KS` link's check. -/
theorem toExt3_ksOk (kchal rho' vals : List FE) (hk : kchal.length = 20) (hr : rho'.length = 15) :
    FE.toExt3 (Lvm.contShift P20 (kchal.take 15) rho' * vals.getD 0 0 +
        Lvm.eqEval (kchal.take 15) rho' * (vals.getD 1 0 + (1 + rho'.getD 14 0) * vals.getD 2 0 +
          rho'.getD 14 0 * vals.getD 3 0)) =
      Lvm.KG.contShiftE (contRows P20) ((kchal.map FE.toExt3).take 15) (rho'.map FE.toExt3) *
          (vals.map FE.toExt3).getD 0 0 +
        Verifier.eqEval ((kchal.map FE.toExt3).take 15) (rho'.map FE.toExt3) *
          ((vals.map FE.toExt3).getD 1 0 + (1 + (rho'.map FE.toExt3).getD 14 0) *
            (vals.map FE.toExt3).getD 2 0 + (rho'.map FE.toExt3).getD 14 0 * (vals.map FE.toExt3).getD 3 0) := by
  rw [← List.map_take, ← toExt3_contShift _ _ (by simp [hk]) hr, ← toExt3_eqEval]
  simp only [tE_add, tE_mul, tE_one, getD_map_toExt3]

/-! ## Ring switching -/

theorem toExt3_phiMap (v : FE) (ch : List FE) :
    FE.toExt3 (Lvm.phiMap v ch) = Verifier.phiMap (FE.toExt3 v) (ch.map FE.toExt3) := by
  unfold Lvm.phiMap Verifier.phiMap
  rw [toExt3_foldl (Prod.map FE.toExt3 id) _
    (fun value (cs : E × ℕ) ↦ value + cs.1 * value ^ (2 ^ cs.2)) fun a b ↦ ?_]
  · rw [← List.zip_map_left]; rfl
  · obtain ⟨c, s⟩ := b
    simp only [tE_add, tE_mul, toExt3_frob, Prod.map, id]

theorem map_ringCoefficients (ch : List FE) :
    (Lvm.ringCoefficients ch).map FE.toExt3 = Verifier.ringCoefficients (ch.map FE.toExt3) := by
  unfold Lvm.ringCoefficients Verifier.ringCoefficients
  rw [List.map_map, show Lvm.kBits = Verifier.kBits from rfl]
  refine List.map_congr_left fun k _ ↦ ?_
  simp only [Function.comp]
  rw [toExt3_foldl (Prod.map FE.toExt3 id) _
    (fun acc (fs : E × ℕ) ↦ acc * fs.1 ^ (2 ^ (k % fs.2))) fun a b ↦ ?_, tE_one]
  · rw [List.zip_map_left, List.filter_map]; rfl
  · obtain ⟨f, s⟩ := b
    simp only [tE_mul, toExt3_frob, Prod.map, id]

theorem toExt3_ringProduct (l rP : List FE) (c : FE) :
    FE.toExt3 ((List.zip l rP).foldl (fun product (vc : FE × FE) => product * (1 + vc.1 + vc.2)) c) =
      (List.zip (l.map FE.toExt3) (rP.map FE.toExt3)).foldl
        (fun product (vc : E × E) => product * (1 + vc.1 + vc.2)) (FE.toExt3 c) := by
  rw [toExt3_foldl (Prod.map FE.toExt3 FE.toExt3) _
    (fun product (vc : E × E) => product * (1 + vc.1 + vc.2)) fun a b ↦ ?_, List.zip_map]
  simp only [tE_mul, tE_add, tE_one, Prod.map]

theorem toExt3_ringWeight (r rP cs : List FE) :
    FE.toExt3 (Lvm.ringWeight r rP cs) =
      Verifier.ringWeight (r.map FE.toExt3) (rP.map FE.toExt3) (cs.map FE.toExt3) := by
  unfold Lvm.ringWeight Verifier.ringWeight
  suffices h : ∀ (cs : List FE) (acc : FE × List FE),
      (FE.toExt3 (cs.foldl (fun (acc : FE × List FE) c =>
          ((acc.1 + (List.zip acc.2 rP).foldl (fun product (vc : FE × FE) =>
            product * (1 + vc.1 + vc.2)) c), acc.2.map FE.sq)) acc).1,
        (cs.foldl (fun (acc : FE × List FE) c =>
          ((acc.1 + (List.zip acc.2 rP).foldl (fun product (vc : FE × FE) =>
            product * (1 + vc.1 + vc.2)) c), acc.2.map FE.sq)) acc).2.map FE.toExt3) =
      (cs.map FE.toExt3).foldl (fun (acc : E × List E) c =>
          ((acc.1 + (List.zip acc.2 (rP.map FE.toExt3)).foldl (fun product (vc : E × E) =>
            product * (1 + vc.1 + vc.2)) c), acc.2.map (· ^ 2))) (FE.toExt3 acc.1, acc.2.map FE.toExt3) by
    have := congrArg Prod.fst (h cs (0, r))
    simp only [tE_zero] at this
    exact this
  intro cs
  induction cs with
  | nil => intro acc; rfl
  | cons c cs ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp only [tE_add, toExt3_ringProduct, List.map_map]
    congr 3
    funext x
    exact toExt3_sq_eq_pow x

/-! ## Native lengths and the ring switch's refinement -/

theorem length_samples : ∀ (n : ℕ) (sig : ByteArray) (s : RS), (runD (DM.samples n) sig s).1.length = n
  | 0, _, _ => rfl
  | n + 1, sig, _ => congrArg (· + 1) (length_samples n sig _)

theorem length_readEs : ∀ (n : ℕ) (sig : ByteArray) (s : RS), (runD (DM.readEs n) sig s).1.length = n
  | 0, _, _ => rfl
  | n + 1, sig, _ => congrArg (· + 1) (length_readEs n sig _)

theorem length_sumcheck (count : ℕ) : ∀ (eqs : List (Option FE)) (claim : FE) (sig : ByteArray) (s : RS),
    (runD (Lvm.sumcheck claim count eqs) sig s).1.1.length = eqs.length
  | [], _, _, _ => rfl
  | _ :: eqs, _, sig, _ => congrArg (· + 1) (length_sumcheck count eqs _ sig _)

section Ref

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- A fact about the native step's value. -/
theorem refAt_withD {α β : Type} {d : DM β} {P : LeanVM.Protocol.Compile.VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (h : RefAt cap shp sig d P R) (hq : ∀ s, Q (runD d sig s).1) :
    RefAt cap shp sig d P fun b a ↦ R b a ∧ Q b := fun s hok ↦ by
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  exact ⟨a, h1, h2, h3, h4, hq s⟩

theorem monoD_ringRaw (s : List FE) : MonoD (Lvm.ringRaw s) :=
  (monoD_samples _).bind fun _ ↦ MonoD.pure _

/-- **V_S's caller-placed ring switch** refines leanVM's `ringSwitch` at any point: the same
target, the weight `ringWeight pt · coeffs` on the coefficients' images. -/
theorem ref_ringRaw (s : List FE) (pt : List E) :
    RefAt cap shp sig (Lvm.ringRaw s) (Verifier.ringSwitch pt (s.map FE.toExt3))
      fun r r' ↦ r' = (FE.toExt3 r.1, fun x ↦ Verifier.ringWeight pt x (r.2.map FE.toExt3)) := by
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_samples ringStages) ?_
  rintro ch _ rfl
  refine RefAt.pure ?_
  simp only [toExt3_polyEval, toExt3_gen, List.map_map, map_ringCoefficients, Function.comp_def,
    toExt3_phiMap]

end Ref

end Lvm.VEq.Lk
