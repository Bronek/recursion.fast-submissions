-- New for lvm (WP-14a, H2): the native Keccak GKR and ring switching (LvmDecideKeccak, over `FE`)
-- compute the verifier language's values (LvmVCore, over `E`) through `FE.toExt3`: the pure parts.
import LvmVEqSum
import LvmVEqRel
import LvmQKeccakConst

/-!
# Keccak GKR and ring switching over `E`: the arithmetic

One transport lemma per pure piece of `LvmDecideKeccak` into its `LvmVCore` twin:

* the embedding's tables (`rmfeEmbed_eq`, `rmfeProject_eq`, from `Q1.rmfe_eq_V`) and the
  constants (`slotBits_eq`, `segmentBits_eq`);
* `map_keccakInstanceWeights`, `map_keccakLinearTranspose` (the arrays mapped entry by entry),
  `kcE_keccakFirstClaim` (a claim over `E`: `kcE`), `map_keccakSlotWeights`, `map_slotFold`
  (`keccakOpen`'s fold of the rows by the slot's challenges);
* a layer's checks: `toExt3_projected`, `toExt3_iota`, and the split kernel: V_S weighs bit
  `j = 64·lane + z` by `eq_z[z] · eq_lane[lane]` where the language weighs it by
  `eqKernel localPoint` (`toExt3_weighted`, `map_layerWeights`, for an `11`-coordinate point);
* ring switching: `toExt3_phiMap`, `map_ringCoefficients`, `toExt3_ringWeight` (V_S's `FE.frob k`
  and `FE.sq` are the language's `^ (2^k)` and `^ 2`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol Finset
open Lvm.M3 (tE_add tE_mul tE_zero tE_one)
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_append eqAt_mod eqKernel_getD eqKernel_length)

/-! ## Constants -/

theorem rmfeEmbed_eq : Lvm.rmfeEmbed = Verifier.rmfeEmbed := congrArg Prod.fst Lvm.Q1.rmfe_eq_V

theorem rmfeProject_eq : Lvm.rmfeProject = Verifier.rmfeProject := congrArg Prod.snd Lvm.Q1.rmfe_eq_V

theorem slotBits_eq : Lvm.keccakSlotBits = Verifier.qkeccakSlotBits := by decide

theorem segmentBits_eq : Lvm.segmentBits = Verifier.keccakSegmentBits := by decide

/-! ## Lists and arrays -/

theorem arr_getD_map (a : Array FE) (i : ℕ) :
    (a.map FE.toExt3).getD i 0 = FE.toExt3 (a.getD i 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? <;> simp

theorem arr_getD_toArray {α : Type} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem toExt3_toArray_getD (l : List FE) (i : ℕ) :
    FE.toExt3 (l.toArray.getD i 0) = (l.map FE.toExt3).toArray.getD i 0 := by
  rw [arr_getD_toArray, arr_getD_toArray, getD_map_toExt3]

theorem getD_map_range {α : Type} (n i : ℕ) (f : ℕ → α) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

theorem getD_map_lists (rows : List (List FE)) (i : ℕ) :
    (rows.map (List.map FE.toExt3)).getD i [] = (rows.getD i []).map FE.toExt3 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases rows[i]? <;> rfl

/-- Set-folds of arrays, mapped. -/
theorem map_foldl_set {γ : Type} (L : List γ) (idx : γ → ℕ) (v : γ → FE) (g : Array FE) :
    (L.foldl (fun g z ↦ g.setIfInBounds (idx z) (v z)) g).map FE.toExt3 =
      L.foldl (fun g z ↦ g.setIfInBounds (idx z) (FE.toExt3 (v z))) (g.map FE.toExt3) := by
  induction L generalizing g with
  | nil => rfl
  | cons z L ih => simp only [List.foldl_cons, ih, Array.map_setIfInBounds]

theorem map_foldl_foldl_set {γ δ : Type} (L : List γ) (M : List δ) (idx : γ → δ → ℕ)
    (v : γ → δ → FE) (g : Array FE) :
    (L.foldl (fun g x ↦ M.foldl (fun g z ↦ g.setIfInBounds (idx x z) (v x z)) g) g).map FE.toExt3 =
      L.foldl (fun g x ↦ M.foldl (fun g z ↦ g.setIfInBounds (idx x z) (FE.toExt3 (v x z))) g)
        (g.map FE.toExt3) := by
  induction L generalizing g with
  | nil => rfl
  | cons x L ih => simp only [List.foldl_cons, ih, map_foldl_set]

theorem map_modify_set (rows : Array (Array FE)) (i k : ℕ) (v : FE) :
    (rows.modify i fun row ↦ row.setIfInBounds k v).map (Array.map FE.toExt3) =
      (rows.map (Array.map FE.toExt3)).modify i fun row ↦ row.setIfInBounds k (FE.toExt3 v) := by
  refine Array.ext (by simp) fun j h1 h2 ↦ ?_
  simp only [Array.getElem_map, Array.getElem_modify]
  split <;> simp [Array.map_setIfInBounds]

theorem map_foldl_modify {γ : Type} (M : List γ) (idx key : γ → ℕ) (v : γ → FE)
    (g : Array (Array FE)) :
    (M.foldl (fun g z ↦ g.modify (idx z) fun row ↦ row.setIfInBounds (key z) (v z)) g).map
        (Array.map FE.toExt3) =
      M.foldl (fun g z ↦ g.modify (idx z) fun row ↦ row.setIfInBounds (key z) (FE.toExt3 (v z)))
        (g.map (Array.map FE.toExt3)) := by
  induction M generalizing g with
  | nil => rfl
  | cons z M ih => simp only [List.foldl_cons, ih, map_modify_set]

theorem map_foldl_foldl_modify {γ δ : Type} (L : List γ) (M : List δ) (idx key : γ → δ → ℕ)
    (v : γ → δ → FE) (g : Array (Array FE)) :
    (L.foldl (fun g x ↦ M.foldl (fun g z ↦
        g.modify (idx x z) fun row ↦ row.setIfInBounds (key x z) (v x z)) g) g).map
        (Array.map FE.toExt3) =
      L.foldl (fun g x ↦ M.foldl (fun g z ↦
        g.modify (idx x z) fun row ↦ row.setIfInBounds (key x z) (FE.toExt3 (v x z))) g)
        (g.map (Array.map FE.toExt3)) := by
  induction L generalizing g with
  | nil => rfl
  | cons x L ih => simp only [List.foldl_cons, ih, map_foldl_modify]

theorem map_rows (rows : Array (Array FE)) :
    (rows.toList.map Array.toList).map (List.map FE.toExt3) =
      (rows.map (Array.map FE.toExt3)).toList.map Array.toList := by
  simp [Array.toList_map, List.map_map, Function.comp_def]

/-- `dot` as a sum over the left list's indices (the right list padded by zeros). -/
theorem dot_eq_sum_left : ∀ (a b : List E),
    Verifier.dot a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0
  | [], _ => by simp [Verifier.dot]
  | x :: a, [] => by simp [Verifier.dot]
  | x :: a, y :: b => by
    rw [LeanVM.Protocol.Whir.Complete.dot_cons, dot_eq_sum_left a b, List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

/-- `Σ_{j < 64 n} f j` by lanes. -/
theorem sum_range_lanes (n : ℕ) (f : ℕ → E) :
    ∑ j ∈ range (64 * n), f j = ∑ l ∈ range n, ∑ z ∈ range 64, f (64 * l + z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 64 * (n + 1) = 64 * n + 64 by ring, Finset.sum_range_add, ih]
    exact (Finset.sum_range_succ (fun l ↦ ∑ z ∈ range 64, f (64 * l + z)) n).symm

theorem sumE_map_range (n : ℕ) (f : ℕ → E) :
    Verifier.sumE ((List.range n).map f) = ∑ i ∈ range n, f i := by
  rw [LeanVM.Protocol.KeccakGkr.sumE_eq_sum]
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-! ## Claims over `E` -/

/-- A native Keccak claim over `E`. -/
def kcE (c : Lvm.KeccakClaim) : Verifier.KeccakClaim :=
  ⟨FE.toExt3 c.value, c.mu.map FE.toExt3, c.point.map FE.toExt3, c.weights.map FE.toExt3⟩

/-! ## The embedding's weights and the linear map -/

theorem map_keccakInstanceWeights (s : FE) :
    (Lvm.keccakInstanceWeights s).map FE.toExt3 = Verifier.keccakInstanceWeights (FE.toExt3 s) := by
  unfold Lvm.keccakInstanceWeights Verifier.keccakInstanceWeights
  simp only [rmfeEmbed_eq, List.map_map, show Lvm.embedBits = Verifier.embedBits from rfl]
  refine List.map_congr_left fun e _ ↦ ?_
  rw [Function.comp_apply, toExt3_sumE, List.map_filterMap]
  congr 1
  refine List.filterMap_congr fun b _ ↦ ?_
  by_cases h : e.testBit b
  · simp only [h, ↓reduceIte, Option.map_some, ← map_powers, getD_map_toExt3]
  · simp [h]

theorem map_keccakLinearTranspose (w : List FE) :
    (Lvm.keccakLinearTranspose w).map FE.toExt3 = Verifier.keccakLinearTranspose (w.map FE.toExt3) := by
  have hg : (List.foldl (fun g lane ↦ List.foldl (fun g z ↦ g.setIfInBounds (64 * lane + z)
      (w.toArray.getD (64 * Lvm.keccakPi lane + (z + Lvm.keccakRho.getD lane 0) % 64) 0)) g
      (List.range 64)) (Array.replicate Lvm.keccakBits (0 : FE)) (List.range 25)).map FE.toExt3 =
      List.foldl (fun g lane ↦ List.foldl (fun g z ↦ g.setIfInBounds (64 * lane + z)
      ((w.map FE.toExt3).toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g
      (List.range 64)) (Array.replicate Verifier.keccakBits (0 : E)) (List.range 25) := by
    rw [map_foldl_foldl_set]
    simp only [Array.map_replicate, tE_zero, toExt3_toArray_getD]
    rfl
  unfold Lvm.keccakLinearTranspose Verifier.keccakLinearTranspose
  simp only [List.map_flatMap, List.map_map, Function.comp_def, tE_add, toExt3_sumE,
    ← arr_getD_map, List.map_toArray, hg]
  rfl

/-! ## The openings -/

theorem map_keccakSlotWeights (logSteps : ℕ) (c : Lvm.KeccakClaim) (first count : ℕ) :
    (Lvm.keccakSlotWeights logSteps c first count).map (List.map FE.toExt3) =
      Verifier.keccakSlotWeights logSteps (kcE c) first count := by
  unfold Lvm.keccakSlotWeights Verifier.keccakSlotWeights kcE
  rw [map_rows, map_foldl_foldl_modify]
  simp only [tE_mul, ← getD_map_toExt3, map_eqKernel, List.map_drop, toExt3_toArray_getD,
    Array.map_replicate, tE_zero, slotBits_eq]
  rfl

/-- `keccakOpen`'s fold of the rows by the slot's challenges, mapped. -/
theorem map_slotFold (slot : List FE) (rows : List (List FE)) :
    (slot.foldl (fun rows challenge ↦ (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows).map (List.map FE.toExt3) =
    (slot.map FE.toExt3).foldl (fun rows challenge ↦ (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) (rows.map (List.map FE.toExt3)) := by
  induction slot generalizing rows with
  | nil => rfl
  | cons ch slot ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons]
    congr 1
    rw [List.map_map, List.length_map]
    refine List.map_congr_left fun i _ ↦ ?_
    rw [Function.comp_apply, getD_map_lists, getD_map_lists,
      map_zipWith_of (g' := fun lo hi ↦ lo + FE.toExt3 ch * (lo + hi))
        fun x y ↦ by rw [tE_add, tE_mul, tE_add]]

theorem kcE_keccakFirstClaim (inst segment lanePoint output : List FE) (committed : FE) :
    kcE (Lvm.keccakFirstClaim inst segment lanePoint output committed) =
      Verifier.keccakFirstClaim (inst.map FE.toExt3) (segment.map FE.toExt3)
        (lanePoint.map FE.toExt3) (output.map FE.toExt3) (FE.toExt3 committed) := by
  unfold Lvm.keccakFirstClaim Verifier.keccakFirstClaim kcE
  simp only [tE_add, tE_mul, ← getD_map_toExt3, map_eqKernel, toExt3_dot, List.map_take,
    List.map_drop, List.map_append, List.map_map, Function.comp_def, toExt3_eOfNat]
  rfl

/-! ## Ring switching -/

theorem toExt3_phiMap (v : FE) (ch : List FE) :
    FE.toExt3 (Lvm.phiMap v ch) = Verifier.phiMap (FE.toExt3 v) (ch.map FE.toExt3) := by
  unfold Lvm.phiMap Verifier.phiMap
  rw [List.zip_map_left, List.foldl_map, show Lvm.ringMapShifts = Verifier.ringMapShifts from rfl]
  generalize List.zip ch Verifier.ringMapShifts = l
  induction l generalizing v with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨c, s⟩ := p
    simp only [List.foldl_cons]
    rw [ih]
    simp [toExt3_frob]

theorem toExt3_coeff (k : ℕ) : ∀ (ch : List FE) (sh : List ℕ) (acc : FE),
    FE.toExt3 (((List.zip ch sh).filter fun (_, s) ↦ k &&& s ≠ 0).foldl
        (fun acc (f, s) ↦ acc * FE.frob (k % s) f) acc) =
      ((List.zip (ch.map FE.toExt3) sh).filter fun (_, s) ↦ k &&& s ≠ 0).foldl
        (fun acc (f, s) ↦ acc * f ^ (2 ^ (k % s))) (FE.toExt3 acc)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | c :: ch, s :: sh, acc => by
    rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons, List.filter_cons, List.filter_cons]
    split_ifs
    · rw [List.foldl_cons, List.foldl_cons, toExt3_coeff k ch sh]
      congr 1
      show FE.toExt3 (acc * FE.frob (k % s) c) = FE.toExt3 acc * FE.toExt3 c ^ (2 ^ (k % s))
      rw [tE_mul, toExt3_frob]
    · exact toExt3_coeff k ch sh acc

theorem map_ringCoefficients (ch : List FE) :
    (Lvm.ringCoefficients ch).map FE.toExt3 = Verifier.ringCoefficients (ch.map FE.toExt3) := by
  unfold Lvm.ringCoefficients Verifier.ringCoefficients
  rw [List.map_map, show Lvm.kBits = Verifier.kBits from rfl,
    show Lvm.ringMapShifts = Verifier.ringMapShifts from rfl]
  refine List.map_congr_left fun k _ ↦ ?_
  exact (toExt3_coeff k ch Verifier.ringMapShifts 1).trans (by rw [tE_one])

theorem toExt3_ringProduct : ∀ (vs rP : List FE) (c : FE),
    FE.toExt3 ((List.zip vs rP).foldl
        (fun product (value, challenge) ↦ product * (1 + value + challenge)) c) =
      (List.zip (vs.map FE.toExt3) (rP.map FE.toExt3)).foldl
        (fun product (value, challenge) ↦ product * (1 + value + challenge)) (FE.toExt3 c)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | v :: vs, x :: rP, c => by
    simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
    rw [toExt3_ringProduct vs rP]
    simp

theorem toExt3_ringWeightAux (rPrime : List FE) : ∀ (cs : List FE) (a : FE) (vs : List FE),
    FE.toExt3 (cs.foldl (fun (acc : FE × List FE) c ↦
      (acc.1 + (List.zip acc.2 rPrime).foldl
        (fun product (value, challenge) ↦ product * (1 + value + challenge)) c,
        acc.2.map FE.sq)) (a, vs)).1 =
    ((cs.map FE.toExt3).foldl (fun (acc : E × List E) c ↦
      (acc.1 + (List.zip acc.2 (rPrime.map FE.toExt3)).foldl
        (fun product (value, challenge) ↦ product * (1 + value + challenge)) c,
        acc.2.map (· ^ 2))) (FE.toExt3 a, vs.map FE.toExt3)).1
  | [], _, _ => rfl
  | c :: cs, a, vs => by
    simp only [List.foldl_cons, List.map_cons]
    rw [toExt3_ringWeightAux rPrime cs, tE_add, toExt3_ringProduct, List.map_map, List.map_map]
    congr 4
    funext x
    exact toExt3_sq_eq_pow x

theorem toExt3_ringWeight (r rPrime cs : List FE) :
    FE.toExt3 (Lvm.ringWeight r rPrime cs) =
      Verifier.ringWeight (r.map FE.toExt3) (rPrime.map FE.toExt3) (cs.map FE.toExt3) := by
  unfold Lvm.ringWeight Verifier.ringWeight
  exact (toExt3_ringWeightAux rPrime cs 0 r).trans (by rw [tE_zero])

/-! ## A layer -/

theorem keccakAlong_mod (j k : ℕ) : Verifier.keccakAlong j k % 64 = j % 64 := by
  simp only [Verifier.keccakAlong]; omega

theorem keccakAlong_div (j k : ℕ) :
    Verifier.keccakAlong j k / 64 = Lvm.keccakAlong (64 * (j / 64)) k / 64 := by
  simp only [Verifier.keccakAlong, Lvm.keccakAlong]; omega

theorem keccakAlong_lt' {j : ℕ} (k : ℕ) (hj : j < 1600) : Verifier.keccakAlong j k < 1600 := by
  simp only [Verifier.keccakAlong]; omega

theorem keccakAlongLane_lt {l : ℕ} (k : ℕ) (hl : l < 25) : Lvm.keccakAlong (64 * l) k / 64 < 25 := by
  simp only [Lvm.keccakAlong]; omega

/-- V_S's low kernel (the bit `z` of a lane). -/
theorem eqA_take (lp : List FE) (hl : lp.length = 11) {z : ℕ} (hz : z < 64) :
    FE.toExt3 ((Lvm.eqKernelA (lp.take 6)).getD z 0) = eqAt ((lp.map FE.toExt3).take 6) z := by
  rw [getD_eqKernelA, ← getD_map_toExt3, map_eqKernel, eqKernel_getD, List.map_take,
    ite_eq_left (by simp [hl]; omega)]

/-- V_S's high kernel (the lane). -/
theorem eqA_drop (lp : List FE) (hl : lp.length = 11) {l : ℕ} (hz : l < 32) :
    FE.toExt3 ((Lvm.eqKernelA (lp.drop 6)).getD l 0) = eqAt ((lp.map FE.toExt3).drop 6) l := by
  rw [getD_eqKernelA, ← getD_map_toExt3, map_eqKernel, eqKernel_getD, List.map_drop,
    ite_eq_left (by simp [hl]; omega)]

/-- **The split kernel**: the language's kernel at `j` is V_S's two factors. -/
theorem eqKernel_split (p : List E) (hp : p.length = 11) {j : ℕ} (hj : j < 2048) :
    (Verifier.eqKernel p).getD j 0 = eqAt (p.take 6) (j % 64) * eqAt (p.drop 6) (j / 64) := by
  have h := eqAt_append (p.take 6) (p.drop 6) j
  rw [List.take_append_drop, List.length_take, hp, eqAt_mod (p.take 6), List.length_take, hp] at h
  rw [eqKernel_getD, hp, ite_eq_left (by omega), h]
  rfl

/-- The projection of the product polynomial (a layer's first check). -/
theorem toExt3_projected (mu product : List FE) :
    FE.toExt3 (Lvm.sumE ((List.range Lvm.productBits).map fun c ↦
      Lvm.sumE ((List.zip mu Lvm.rmfeProject).filterMap fun (m, mask) ↦
        if mask.testBit c then some m else none) * product.getD c 0)) =
    Verifier.sumE ((List.range Verifier.productBits).map fun c ↦
      Verifier.sumE ((List.zip (mu.map FE.toExt3) Verifier.rmfeProject).filterMap fun (m, mask) ↦
        if mask.testBit c then some m else none) * (product.map FE.toExt3).getD c 0) := by
  rw [toExt3_sumE, List.map_map, rmfeProject_eq, show Lvm.productBits = Verifier.productBits from rfl]
  congr 1
  refine List.map_congr_left fun c _ ↦ ?_
  rw [Function.comp_apply, tE_mul, toExt3_sumE, getD_map_toExt3, List.map_filterMap,
    List.zip_map_left, List.filterMap_map]
  congr 2
  refine List.filterMap_congr fun ⟨m, mask⟩ _ ↦ ?_
  by_cases h : mask.testBit c <;> simp [h]

/-- The round constant's share (a layer's first check). -/
theorem toExt3_iota (point weights : List FE) (packLog step : ℕ) :
    FE.toExt3 (Lvm.sumE ((List.range Lvm.gkrSegments).map fun segment ↦
      (Lvm.eqKernel (point.drop packLog)).getD segment 0 * Lvm.sumE ((List.range 64).filterMap fun z ↦
        if (Lvm.keccakRC.getD (Lvm.gkrDepth * (segment + 1) - step - 1) 0).toNat.testBit z then
          some (weights.getD z 0) else none))) =
    Verifier.sumE ((List.range Verifier.keccakSegments).map fun segment ↦
      (Verifier.eqKernel ((point.map FE.toExt3).drop packLog)).getD segment 0 *
        Verifier.sumE ((List.range 64).filterMap fun z ↦
          if (keccakRC.getD (Verifier.keccakDepth * (segment + 1) - step - 1) 0).toNat.testBit z then
            some ((weights.map FE.toExt3).getD z 0) else none)) := by
  rw [toExt3_sumE, List.map_map, show Lvm.gkrSegments = Verifier.keccakSegments from rfl,
    show Lvm.gkrDepth = Verifier.keccakDepth from rfl, show Lvm.keccakRC = keccakRC from rfl]
  congr 1
  refine List.map_congr_left fun seg _ ↦ ?_
  rw [Function.comp_apply, tE_mul, toExt3_sumE, ← getD_map_toExt3, map_eqKernel, List.map_drop,
    List.map_filterMap]
  congr 2
  refine List.filterMap_congr fun z _ ↦ ?_
  by_cases h : (keccakRC.getD (Verifier.keccakDepth * (seg + 1) - step - 1) 0).toNat.testBit z
  · simp only [h, ↓reduceIte, Option.map_some, getD_map_toExt3]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Option.map_none]

/-- **The weighted sum of a layer's second check**: V_S's split kernel against the language's
`dot (eq[:1600]) weights`. -/
theorem toExt3_weighted (lp w : List FE) (hl : lp.length = 11) :
    FE.toExt3 (Lvm.sumE ((List.range 25).map fun l ↦ (Lvm.eqKernelA (lp.drop 6)).getD l 0 *
      Lvm.sumE ((List.range 64).map fun z ↦
        (Lvm.eqKernelA (lp.take 6)).getD z 0 * w.toArray.getD (64 * l + z) 0))) =
    Verifier.dot ((Verifier.eqKernel (lp.map FE.toExt3)).take Verifier.keccakBits)
      (w.map FE.toExt3) := by
  have hpl : (lp.map FE.toExt3).length = 11 := by simp [hl]
  rw [dot_eq_sum_left, List.length_take, eqKernel_length, hpl,
    show min Verifier.keccakBits (2 ^ 11) = 64 * 25 from rfl, sum_range_lanes, toExt3_sumE,
    List.map_map, sumE_map_range]
  refine Finset.sum_congr rfl fun l hl' ↦ ?_
  have hl'' := Finset.mem_range.1 hl'
  rw [Function.comp_apply, tE_mul, toExt3_sumE, List.map_map, sumE_map_range, Finset.mul_sum,
    eqA_drop lp hl (by omega)]
  refine Finset.sum_congr rfl fun z hz ↦ ?_
  have hz' := Finset.mem_range.1 hz
  rw [Function.comp_apply, tE_mul, eqA_take lp hl hz', toExt3_toArray_getD, arr_getD_toArray,
    List.getD_eq_getElem?_getD (l := List.take _ _), List.getElem?_take,
    ite_eq_left (show 64 * l + z < Verifier.keccakBits by simp [Verifier.keccakBits]; omega),
    ← List.getD_eq_getElem?_getD, eqKernel_split _ hpl (by omega),
    show (64 * l + z) % 64 = z by omega, show (64 * l + z) / 64 = l by omega]
  ring

/-- **The batched weights of a layer**: V_S's per-lane factor against the language's kernel. -/
theorem map_layerWeights (lp : List FE) (hl : lp.length = 11) (beta : FE) :
    ((List.range Lvm.keccakBits).map fun j ↦ (Lvm.eqKernelA (lp.take 6)).getD (j % 64) 0 *
      ((List.range 25).map fun l ↦ (Lvm.eqKernelA (lp.drop 6)).getD l 0 + beta *
        ((Lvm.eqKernelA (lp.drop 6)).getD (Lvm.keccakAlong (64 * l) 4 / 64) 0 + beta *
          (Lvm.eqKernelA (lp.drop 6)).getD (Lvm.keccakAlong (64 * l) 3 / 64) 0)).toArray.getD
            (j / 64) 0).map FE.toExt3 =
    (List.range Verifier.keccakBits).map fun j ↦ (Verifier.eqKernel (lp.map FE.toExt3)).getD j 0 +
      FE.toExt3 beta * ((Verifier.eqKernel (lp.map FE.toExt3)).getD (Verifier.keccakAlong j 4) 0 +
        FE.toExt3 beta * (Verifier.eqKernel (lp.map FE.toExt3)).getD (Verifier.keccakAlong j 3) 0) := by
  have hpl : (lp.map FE.toExt3).length = 11 := by simp [hl]
  rw [List.map_map, show Lvm.keccakBits = Verifier.keccakBits from rfl]
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' : j < 1600 := List.mem_range.1 hj
  have h4 := keccakAlong_lt' 4 hj'
  have h3 := keccakAlong_lt' 3 hj'
  rw [Function.comp_apply, arr_getD_toArray ((List.range 25).map _), getD_map_range _ _ _ _ (by omega),
    tE_mul, tE_add,
    tE_mul, tE_add, tE_mul, eqA_take lp hl (by omega), eqA_drop lp hl (by omega),
    eqA_drop lp hl (by have := keccakAlongLane_lt 4 (show j / 64 < 25 by omega); omega),
    eqA_drop lp hl (by have := keccakAlongLane_lt 3 (show j / 64 < 25 by omega); omega),
    eqKernel_split _ hpl (by omega), eqKernel_split _ hpl (by omega),
    eqKernel_split _ hpl (by omega), keccakAlong_mod, keccakAlong_mod, keccakAlong_div,
    keccakAlong_div]
  ring

end Lvm.VEq
