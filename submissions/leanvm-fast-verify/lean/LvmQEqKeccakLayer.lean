import LvmQEqKeccakLayer2

/-!
# QA1: Q_arith_eq for one Keccak GKR layer

`layer_spec`: on the cells of one iteration of the layer template (`layerTB`, any memory where the
loop holds: `THold`), if the carried values represent `F`'s claim (`Rep`, with the layer's RC and
`first` constants and the stream view), then the copy rows represent the claim `F`'s
`verifyKeccakLayer` returns (`layerSpec`), the layer moves the position by `8·str`, and the two
gated assertions hold iff `F`'s two checks do (gate `1`; the converse for any gate).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- The carried lane weights `B`. -/
def repB (P : Nat) (cv : Nat → FE) : List FE := (List.range 25).map fun l => cv (19 + P + l)

/-- The carried slice challenges `a`. -/
def repA (P : Nat) (cv : Nat → FE) : List FE := (List.range 6).map fun i => cv (44 + P + i)

/-- **The carried values `cv` represent `F`'s claim `C`** (the first claim's weights when `first`). -/
structure Rep (P : Nat) (cv : Nat → FE) (C : KeccakClaim) (first : Bool) : Prop where
  value : cv 0 = C.value
  mu : (List.range 16).map (fun i => cv (1 + i)) = C.mu
  kappa : cv 17 = sumE C.mu
  point : (List.range (P + 1)).map (fun i => cv (18 + i)) = C.point
  weights : C.weights = if first then firstW (repB P cv)
    else keccakLinearTranspose (prodW (eqAt (repA P cv)) (repB P cv))
  flips : ∀ i < 7, cv (50 + P + i) = if first then (repB P cv).getD 0 0 * FE.ofK (FK.x ^ iotaPos i)
    else flipForm (repB P cv) (eqAt (repA P cv)) i

/-- `F`'s array `eq` table is its list one. -/
theorem eqKernelA_toArray (p : List FE) : eqKernelA p = (eqKernel p).toArray := by
  unfold eqKernelA eqKernel
  suffices h : ∀ (acc : List FE), p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) acc.toArray =
      (p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) acc).toArray from h [1]
  induction p with
  | nil => intro acc; rfl
  | cons r rs ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    simp

theorem getD_eqKernelA (p : List FE) (i : Nat) : (eqKernelA p).getD i 0 = eqAt p i := by
  rw [eqKernelA_toArray, array_getD_toArray']; rfl

/-- `F`'s iota sum on a represented claim's weights is the carried flips' (both kinds of claim). -/
theorem iota_rep {P : Nat} {cv : Nat → FE} {C : KeccakClaim} {first : Bool} (hR : Rep P cv C first)
    {rc : UInt64} (hrc : rc ∈ keccakRC) :
    iotaF rc C.weights = sumE ((List.range 7).map fun i => rcBit rc i * cv (50 + P + i)) := by
  rw [hR.weights]
  cases first with
  | true =>
    simp only [ite_true]
    rw [iota_first hrc]
    refine congrArg sumE (List.map_congr_left fun i hi => ?_)
    rw [hR.flips i (List.mem_range.mp hi)]
    simp only [ite_true]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [iota_flips hrc]
    refine congrArg sumE (List.map_congr_left fun i hi => ?_)
    rw [hR.flips i (List.mem_range.mp hi)]
    simp only [Bool.false_eq_true, ite_false]

theorem drop_last {l : List FE} {P : Nat} (h : l.length = P + 1) : l.drop P = [l.getD P 0] := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.length_singleton, Nat.lt_one_iff] at h2
  subst h2
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp

theorem sumE_range_two (f : Nat → FE) : sumE ((List.range 2).map f) = f 0 + f 1 := by
  show 0 + f 0 + f 1 = f 0 + f 1
  rw [zero_add]

/-- `F`'s iota term: the two segments' `eq` weights on the claim's last point coordinate. -/
theorem iotaLayer_eq {P step : Nat} {C : KeccakClaim} (hpt : C.point.length = P + 1) :
    iotaLayerF (P + 4) step C =
      (1 + C.point.getD P 0) * iotaF (keccakRC.getD (gkrDepth * 1 - step - 1) 0) C.weights +
        C.point.getD P 0 * iotaF (keccakRC.getD (gkrDepth * 2 - step - 1) 0) C.weights := by
  unfold iotaLayerF
  rw [Nat.add_sub_cancel, drop_last hpt]
  rw [show eqKernel [C.point.getD P 0] = [1 + C.point.getD P 0, C.point.getD P 0] by
    simp [eqKernel]]
  rw [show gkrSegments = 2 from rfl, sumE_range_two, Nat.zero_add, show (1 + 1 : Nat) = 2 from rfl,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_cons_zero]
  unfold iotaF
  rfl

theorem weightedLayerF_eq (lp : List FE) (C : KeccakClaim) :
    weightedLayerF lp C = weightedF (eqKernel (lp.drop 6)) (eqKernel (lp.take 6)) C.weights := by
  unfold weightedLayerF weightedF
  rw [eqKernelA_toArray, eqKernelA_toArray]
  simp only [array_getD_toArray']

/-- `F`'s final-check weight on a represented claim: `(Σ eq_L·B)·indexMle` (first) or the lane forms. -/
theorem weighted_rep {P : Nat} {cv : Nat → FE} {C : KeccakClaim} {first : Bool} (hR : Rep P cv C first)
    {lp : List FE} (hlp : lp.length = 11) :
    weightedLayerF lp C = if first then
        ((List.range 25).map fun l => (eqKernel (lp.drop 6)).getD l 0 * (repB P cv).getD l 0).sum *
          indexMle (lp.take 6)
      else ((List.range 25).map fun l => (eqKernel (lp.drop 6)).getD l 0 *
        laneForm (repB P cv) (rotSum (eqAt (lp.take 6)) (eqAt (repA P cv))) l).sum := by
  rw [weightedLayerF_eq, hR.weights]
  cases first with
  | true =>
    simp only [ite_true]
    rw [weighted_first _ _ _ (by simp [hlp]), sumE_eq_sum]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    unfold weightedF
    rw [sumE_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    rw [lane_dot (eqAt (repA P cv)) (fun z => (eqKernel (lp.take 6)).getD z 0) (repB P cv) (List.mem_range.mp hl)]
    rfl

theorem laneWF_eq (lp : List FE) (beta : FE) :
    laneWF lp beta = ((List.range 25).map fun l => eqAt (lp.drop 6) l + beta *
      (eqAt (lp.drop 6) (keccakAlong (64 * l) 4 / 64) + beta * eqAt (lp.drop 6) (keccakAlong (64 * l) 3 / 64))).toArray := by
  unfold laneWF
  simp only [getD_eqKernelA]
/-! ## `layerSpec`'s fields, its intermediate values named -/

theorem layerSpec_claim (v : Nat → FE) (ls step : Nat) (C : KeccakClaim) (p : Nat) {sF : FE}
    (hs : v (p + 40 + 24 * productBits) = sF) {pkF : FE × FE × List FE × Nat}
    (hpk : packSpec v C.point (polyEval (scalarsAt v (p + 40) productBits) sF) 1 (p + 72 + 24 * productBits) = pkF)
    {scF : List FE × FE} (hsc : scSpec v 4 pkF.2.2.2 pkF.1 (List.replicate localBits none) = scF)
    {p3 : Nat} (hp3 : pkF.2.2.2 + localBits * roundLen 4 = p3) {tF : List FE} (ht : scalarsAt v (p3 + 40) 3 = tF)
    {βF : FE} (hβ : v (p3 + 40 + 24 * 3) = βF) :
    (layerSpec v ls step C p).claim = ⟨tF.getD 0 0 + βF * (tF.getD 1 0 + βF * tF.getD 2 0), keccakInstanceWeights sF, pkF.2.2.1,
          keccakLinearTranspose ((List.range keccakBits).map fun j =>
            (eqKernelA (scF.1.take 6)).getD (j % 64) 0 * (laneWF scF.1 βF).getD (j / 64) 0)⟩ := by
  subst hs hpk hsc hp3 ht hβ
  rfl

theorem layerSpec_ok1 (v : Nat → FE) (ls step : Nat) (C : KeccakClaim) (p : Nat) {sF : FE}
    (hs : v (p + 40 + 24 * productBits) = sF) {pkF : FE × FE × List FE × Nat}
    (hpk : packSpec v C.point (polyEval (scalarsAt v (p + 40) productBits) sF) 1 (p + 72 + 24 * productBits) = pkF)
    {scF : List FE × FE} (hsc : scSpec v 4 pkF.2.2.2 pkF.1 (List.replicate localBits none) = scF)
    {p3 : Nat} (hp3 : pkF.2.2.2 + localBits * roundLen 4 = p3) {tF : List FE} (ht : scalarsAt v (p3 + 40) 3 = tF)
    {βF : FE} (hβ : v (p3 + 40 + 24 * 3) = βF) :
    (layerSpec v ls step C p).ok1 = (projF C (scalarsAt v (p + 40) productBits) + iotaLayerF ls step C * sumE C.mu == C.value) := by
  subst hs hpk hsc hp3 ht hβ
  rfl

theorem layerSpec_ok2 (v : Nat → FE) (ls step : Nat) (C : KeccakClaim) (p : Nat) {sF : FE}
    (hs : v (p + 40 + 24 * productBits) = sF) {pkF : FE × FE × List FE × Nat}
    (hpk : packSpec v C.point (polyEval (scalarsAt v (p + 40) productBits) sF) 1 (p + 72 + 24 * productBits) = pkF)
    {scF : List FE × FE} (hsc : scSpec v 4 pkF.2.2.2 pkF.1 (List.replicate localBits none) = scF)
    {p3 : Nat} (hp3 : pkF.2.2.2 + localBits * roundLen 4 = p3) {tF : List FE} (ht : scalarsAt v (p3 + 40) 3 = tF)
    {βF : FE} (hβ : v (p3 + 40 + 24 * 3) = βF) :
    (layerSpec v ls step C p).ok2 = (pkF.2.1 * weightedLayerF scF.1 C * (sumE (keccakInstanceWeights sF) * tF.getD 0 0 +
          (sumE (keccakInstanceWeights sF) + tF.getD 1 0) * tF.getD 2 0) == scF.2) := by
  subst hs hpk hsc hp3 ht hβ
  rfl

theorem layerSpec_pos (v : Nat → FE) (ls step : Nat) (C : KeccakClaim) (p : Nat) {sF : FE}
    (hs : v (p + 40 + 24 * productBits) = sF) {pkF : FE × FE × List FE × Nat}
    (hpk : packSpec v C.point (polyEval (scalarsAt v (p + 40) productBits) sF) 1 (p + 72 + 24 * productBits) = pkF)
    {scF : List FE × FE} (hsc : scSpec v 4 pkF.2.2.2 pkF.1 (List.replicate localBits none) = scF)
    {p3 : Nat} (hp3 : pkF.2.2.2 + localBits * roundLen 4 = p3) {tF : List FE} (ht : scalarsAt v (p3 + 40) 3 = tF)
    {βF : FE} (hβ : v (p3 + 40 + 24 * 3) = βF) :
    (layerSpec v ls step C p).pos = p3 + 72 + 24 * 3 := by
  subst hs hpk hsc hp3 ht hβ
  rfl

/-- **The layer**, read along `layerTB`'s chain from the walking invariant `TInv`. -/
theorem layer_core {c : LCfg} {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat}
    (h0 : TInv xv V TA L True (layerTB c) 0) (hcb : c.cb + c.C = L)
    {C : KeccakClaim} {first : Bool} (hR : Rep c.P (fun j => xv (c.pv j)) C first)
    {step : Nat} (hstep : step < gkrDepth)
    (hrc : ∀ i < 7, xv (c.k i) = rcBit (keccakRC.getD (gkrDepth * 1 - step - 1) 0) i ∧
      xv (c.k (7 + i)) = rcBit (keccakRC.getD (gkrDepth * 2 - step - 1) 0) i)
    (hfirst : xv (c.k 14) = if first then 1 else 0)
    {v : Nat → FE} {off p : Nat} (hv : ∀ m < c.q + c.str, lv xv [c.str] m = v (8 * m + off))
    (hp : p + 40 = 8 * c.q + off) :
    Rep c.P (fun j => V (c.cb + j)) (layerSpec v (c.P + 4) step C p).claim false ∧
    (layerSpec v (c.P + 4) step C p).pos = p + 8 * c.str ∧
    (TA → xv (c.k 15) = 1 →
      (layerSpec v (c.P + 4) step C p).ok1 = true ∧ (layerSpec v (c.P + 4) step C p).ok2 = true) ∧
    ((layerSpec v (c.P + 4) step C p).ok1 = true → (layerSpec v (c.P + 4) step C p).ok2 = true → TA) := by
  have hstr : c.str = 366 + 15 * (c.P + 1) := rfl
  have hPB : productBits = 47 := rfl
  have hLB : localBits = 11 := rfl
  have hRL : roundLen 4 = 144 := rfl
  have hRmu : (List.range 16).map (fun i => xv (c.pv (1 + i))) = C.mu := hR.mu
  have hRpt : (List.range (c.P + 1)).map (fun i => xv (c.pv (18 + i))) = C.point := hR.point
  have hCptL : C.point.length = c.P + 1 := by rw [← hRpt, List.length_map, List.length_range]
  have hσ : C.point.getD c.P 0 = xv (c.pv (18 + c.P)) := by
    rw [← hRpt, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  obtain ⟨sF, hsF⟩ : ∃ x, v (p + 40 + 24 * productBits) = x := ⟨_, rfl⟩
  obtain ⟨pkF, hpkF⟩ : ∃ x, packSpec v C.point (polyEval (scalarsAt v (p + 40) productBits) sF) 1
      (p + 72 + 24 * productBits) = x := ⟨_, rfl⟩
  obtain ⟨scF, hscF⟩ : ∃ x, scSpec v 4 pkF.2.2.2 pkF.1 (List.replicate localBits none) = x := ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ x, pkF.2.2.2 + localBits * roundLen 4 = x := ⟨_, rfl⟩
  obtain ⟨tF, htF⟩ : ∃ x, scalarsAt v (p3 + 40) 3 = x := ⟨_, rfl⟩
  obtain ⟨βF, hβF⟩ : ∃ x, v (p3 + 40 + 24 * 3) = x := ⟨_, rfl⟩
  have hpkEnd : pkF.2.2.2 = p + 1200 + 120 * (c.P + 1) := by
    rw [← hpkF, packSpec_pos, hCptL, hPB]
  have hp3' : p3 = p + 2784 + 120 * (c.P + 1) := by rw [← hp3, hpkEnd, hLB, hRL]; omega
  have hscL : scF.1.length = 11 := by rw [← hscF, scSpec_length, List.length_replicate]; rfl
  rw [layerSpec_claim v (c.P + 4) step C p hsF hpkF hscF hp3 htF hβF,
    layerSpec_ok1 v (c.P + 4) step C p hsF hpkF hscF hp3 htF hβF,
    layerSpec_ok2 v (c.P + 4) step C p hsF hpkF hscF hp3 htF hβF,
    layerSpec_pos v (c.P + 4) step C p hsF hpkF hscF hp3 htF hβF]
  dsimp only [layerTB] at h0
  -- zero, one, the product, `s`
  obtain ⟨z, n1, ez, h1, h0⟩ := peelN h0 (noA_gZero _)
  have hz : z.valF xv V = 0 := by rw [← ez]; exact gZero_spec h1
  obtain ⟨one, n2, eone, h2, h0⟩ := peelN h0 (noA_gOne _)
  have hone : one.valF xv V = 1 := by rw [← eone, gOne_spec h2, hz, add_zero]
  obtain ⟨prod, n3, eprod, h3, h0⟩ := peelN h0 (noA_mapTB (fun _ => noA_gLoad _ _) _)
  have hprodL : prod.length = 47 := by rw [← eprod, mapTB_length]; rfl
  have hprod : prod.map (Src.valF xv V) = scalarsAt v (p + 40) productBits := by
    rw [← eprod]
    refine forall₂_map_eq (mapTB_spec_mem (P := fun k x => x = v (p + 40 + 24 * k)) _ (fun k hk m hm => ?_) _ h3)
    have hk' : k < 47 := List.mem_range.mp hk
    rw [gLoad_lv hm, hv _ (by rw [hstr]; omega)]
    exact congrArg v (by omega)
  obtain ⟨s, n4, es, h4, h0⟩ := peelN h0 (noA_gLoad _ _)
  have hs : s.valF xv V = sF := by
    rw [← es, gLoad_lv h4, hv _ (by rw [hstr]; omega), ← hsF, hPB]; exact congrArg v (by omega)
  -- check 1: projection and iota
  obtain ⟨proj, n5, eproj, h5, h0⟩ := peelN h0 (noA_gProj _ _ _ _)
  have hmuS : ((List.range 16).map fun i => c.pv (1 + i)).map (Src.valF xv V) = C.mu := by
    rw [List.map_map]; exact hRmu
  have hproj : proj.valF xv V = projF C (scalarsAt v (p + 40) productBits) := by
    rw [← eproj, gProj_spec hz _ _ _ _ h5, hmuS, hprodL]
    unfold projF
    refine congrArg sumE (List.map_congr_left fun k hk => ?_)
    have hk' : k < 47 := List.mem_range.mp hk
    rw [getD_valF _ (by omega), hprod]
  obtain ⟨seg0, n6, eseg0, h6, h0⟩ := peelN h0 (noA_gOne _)
  obtain ⟨in0, n7, ein0, h7, h0⟩ := peelN h0 (noA_gDot _ _)
  obtain ⟨in1, n8, ein1, h8, h0⟩ := peelN h0 (noA_gDot _ _)
  obtain ⟨iota, n9, eiota, h9, h0⟩ := peelN h0 (noA_gDot _ _)
  obtain ⟨e1, n10, ee1, h10, h0⟩ := peelN h0 (noA_gMul _ _ _)
  obtain ⟨e1', n11, ee1', h11, h0⟩ := peelN h0 (noA_gAdd _ _)
  obtain ⟨n12, h0⟩ := peelA h0
  have hptP : ((List.range (c.P + 1)).map fun i => c.pv (18 + i)).getD c.P default = c.pv (18 + c.P) := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  have hflS : ∀ i < 7, ((List.range 7).map fun i => c.pv (50 + c.P + i)).getD i default = c.pv (50 + c.P + i) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  have RC1m : keccakRC.getD (gkrDepth * 1 - step - 1) 0 ∈ keccakRC :=
    rc_mem (by simp only [gkrDepth] at hstep ⊢; omega)
  have RC2m : keccakRC.getD (gkrDepth * 2 - step - 1) 0 ∈ keccakRC :=
    rc_mem (by simp only [gkrDepth] at hstep ⊢; omega)
  have hin0 : in0.valF xv V = iotaF (keccakRC.getD (gkrDepth * 1 - step - 1) 0) C.weights := by
    rw [iota_rep hR RC1m, ← ein0, gDot_spec _ _ _ h7, hz, zero_add, List.map_map, sumE_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    show (c.k i).valF xv V * (((List.range 7).map fun i => c.pv (50 + c.P + i)).getD i default).valF xv V = _
    rw [hflS i hi', show (c.k i).valF xv V = xv (c.k i) from rfl, (hrc i hi').1]
    rfl
  have hin1 : in1.valF xv V = iotaF (keccakRC.getD (gkrDepth * 2 - step - 1) 0) C.weights := by
    rw [iota_rep hR RC2m, ← ein1, gDot_spec _ _ _ h8, hz, zero_add, List.map_map, sumE_eq_sum]
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    have hi' := List.mem_range.mp hi
    show (c.k (7 + i)).valF xv V * (((List.range 7).map fun i => c.pv (50 + c.P + i)).getD i default).valF xv V = _
    rw [hflS i hi', show (c.k (7 + i)).valF xv V = xv (c.k (7 + i)) from rfl, (hrc i hi').2]
    rfl
  have hseg0 : seg0.valF xv V = 1 + C.point.getD c.P 0 := by
    rw [← eseg0, gOne_spec h6, hptP, hσ]; rfl
  have hiota : iota.valF xv V = iotaLayerF (c.P + 4) step C := by
    rw [iotaLayer_eq hCptL, ← hin0, ← hin1, ← hseg0, ← eiota, gDot_spec _ _ _ h9, hz, hptP]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, zero_add, add_zero]
    rw [show (c.pv (18 + c.P)).valF xv V = C.point.getD c.P 0 from hσ.symm]
  have he1' : e1'.valF xv V =
      (iotaLayerF (c.P + 4) step C * sumE C.mu + projF C (scalarsAt v (p + 40) productBits)) + C.value := by
    rw [← ee1', gAdd_spec h11, ← ee1, gMul_spec h10, hiota, hproj,
      show (c.pv 17).valF xv V = sumE C.mu from hR.kappa, show (c.pv 0).valF xv V = C.value from hR.value]
  have hK1 : e1'.valF xv V = 0 ↔
      (projF C (scalarsAt v (p + 40) productBits) + iotaLayerF (c.P + 4) step C * sumE C.mu == C.value) = true := by
    rw [he1', fe_beq_iff, fe_add_eq_zero, add_comm (iotaLayerF _ _ _ * _)]
  -- instance weights, the pack value, the rounds
  obtain ⟨mk, n13, emk, h13, h0⟩ := peelN h0 (noA_gInst _ _ _ _)
  have hmk := gInst_spec hz hone rmfeEmbed _ h13
  rw [emk, hs] at hmk
  obtain ⟨hmk1, hmk2⟩ := hmk
  have hmu' : mk.1.map (Src.valF xv V) = keccakInstanceWeights sF := hmk1
  have hkap : mk.2.valF xv V = sumE (keccakInstanceWeights sF) := by rw [hmk2, hmu', sumE_eq_sum]
  have hmkL : mk.1.length = 16 := by
    have := congrArg List.length hmu'
    rw [List.length_map] at this
    rw [this]
    unfold keccakInstanceWeights
    rw [List.length_map, rmfeEmbed_eq]
    rfl
  obtain ⟨v0, n14, ev0, h14, h0⟩ := peelN h0 (noA_gHorner _ _ _)
  have hv0 : v0.valF xv V = polyEval (scalarsAt v (p + 40) productBits) sF := by
    have hsplit : scalarsAt v (p + 40) productBits =
        (List.range 46).map (fun k => v (p + 40 + 24 * k)) ++ [v (p + 40 + 24 * 46)] := by
      rw [hPB]
      simp only [scalarsAt, List.range_succ, List.map_append, List.map_singleton]
    have h46 : (prod.getD 46 default).valF xv V = v (p + 40 + 24 * 46) := by
      rw [getD_valF _ (by omega), hprod, hsplit, List.getD_append_right _ _ _ _ (by simp)]
      simp
    rw [← ev0, gHorner_spec _ _ _ _ h14, hs, h46, hsplit, polyEval_horner, List.map_map, ← List.map_reverse]
    refine congrArg (hornerVal _ _) (List.map_congr_left fun k hk => ?_)
    have hk' : k < 46 := List.mem_range.mp (List.mem_reverse.mp hk)
    show (prod.getD k default).valF xv V = _
    rw [getD_valF _ (by omega), hprod, hsplit, List.getD_append _ _ _ _ (by simpa using hk')]
    simp [hk']
  obtain ⟨pk, n15, epk, h15, h0⟩ := peelN h0 (noA_gPackRounds _ _ _ _ _ _)
  have hptS : ((List.range (c.P + 1)).map fun i => c.pv (18 + i)).map (Src.valF xv V) = C.point := by
    rw [List.map_map]; exact hRpt
  have hpk := gPackRounds_spec hz hv _ (c.q + 150) (p + 72 + 24 * productBits)
    (by simp only [List.length_map, List.length_range]; rw [hstr]; omega) (by rw [hPB]; omega) v0 one _ h15
  rw [epk, hptS, hv0, hone, hpkF] at hpk
  obtain ⟨hpk1, hpk2, hpk3⟩ := hpk
  have hpkL : pk.2.2.length = c.P + 1 := by
    have := congrArg List.length hpk3
    rw [List.length_map, ← hpkF, packSpec_length, hCptL] at this
    exact this
  obtain ⟨lc, n16, elc, h16, h0⟩ := peelN h0 (noA_gLocalRounds _ _ _ _)
  have hlc := gLocalRounds_spec hv 11 (c.q + 150 + 15 * (c.P + 1)) pkF.2.2.2
    (by rw [hstr]; omega) (by rw [hpkEnd]; omega) pk.1 _ h16
  rw [elc, hpk1, show List.replicate 11 (none : Option FE) = List.replicate localBits none from rfl, hscF] at hlc
  obtain ⟨hlc1, hlc2⟩ := hlc
  have hlcL : lc.2.length = 11 := by
    have := congrArg List.length hlc2
    rwa [List.length_map, hscL] at this
  -- `t`, `β`
  obtain ⟨t, n17, et, h17, h0⟩ := peelN h0 (noA_mapTB (fun _ => noA_gLoad _ _) _)
  have ht : t.map (Src.valF xv V) = tF := by
    rw [← et, ← htF]
    refine forall₂_map_eq (mapTB_spec_mem (P := fun k x => x = v (p3 + 40 + 24 * k)) _ (fun k hk m hm => ?_) _ h17)
    have hk' : k < 3 := List.mem_range.mp hk
    rw [gLoad_lv hm, hv _ (by rw [hstr]; omega)]
    exact congrArg v (by rw [hp3']; omega)
  have htL : t.length = 3 := by rw [← et, mapTB_length, List.length_range]
  have htk : ∀ k < 3, (t.getD k default).valF xv V = tF.getD k 0 := fun k hk => by
    rw [getD_valF _ (by omega), ht]
  obtain ⟨beta, n18, ebeta, h18, h0⟩ := peelN h0 (noA_gLoad _ _)
  have hbeta : beta.valF xv V = βF := by
    rw [← ebeta, gLoad_lv h18, hv _ (by rw [hstr]; omega), ← hβF]; exact congrArg v (by rw [hp3']; omega)
  -- the `eq` tables
  obtain ⟨tbLo, n19, etbLo, h19, h0⟩ := peelN h0 (noA_gEqTab _ _ _)
  obtain ⟨tbHi, n20, etbHi, h20, h0⟩ := peelN h0 (noA_gEqTab _ _ _)
  obtain ⟨taLo, n21, etaLo, h21, h0⟩ := peelN h0 (noA_gEqTab _ _ _)
  obtain ⟨taHi, n22, etaHi, h22, h0⟩ := peelN h0 (noA_gEqTab _ _ _)
  obtain ⟨eL, n23, eeL, h23, h0⟩ := peelN h0 (noA_gEqTab _ _ _)
  have hA : ((List.range 6).map fun i => c.pv (44 + c.P + i)).map (Src.valF xv V) =
      repA c.P (fun j => xv (c.pv j)) := by
    rw [List.map_map]; rfl
  have hAL : (repA c.P (fun j => xv (c.pv j))).length = 6 := by simp [repA]
  have hbL : (scF.1.take 6).length = 6 := by simp [hscL]
  have htbLo : tbLo.map (Src.valF xv V) = eqKernel ((scF.1.take 6).take 3) := by
    rw [← etbLo, eqTab_one hz hone _ _ h19, List.map_take, hlc2, List.take_take]; rfl
  have htbHi : tbHi.map (Src.valF xv V) = eqKernel ((scF.1.take 6).drop 3) := by
    rw [← etbHi, eqTab_one hz hone _ _ h20, List.map_take, List.map_drop, hlc2, List.drop_take]
  have htaLo : taLo.map (Src.valF xv V) = eqKernel ((repA c.P (fun j => xv (c.pv j))).take 3) := by
    rw [← etaLo, eqTab_one hz hone _ _ h21, List.map_take, hA]
  have htaHi : taHi.map (Src.valF xv V) = eqKernel ((repA c.P (fun j => xv (c.pv j))).drop 3) := by
    rw [← etaHi, eqTab_one hz hone _ _ h22, List.map_drop, hA]
  have heL : eL.map (Src.valF xv V) = eqKernel (scF.1.drop 6) := by
    rw [← eeL, eqTab_one hz hone _ _ h23, List.map_drop, hlc2]
  have heLL : eL.length = 32 := by
    have := congrArg List.length heL
    rw [List.length_map, eqKernel_length, List.length_drop, hscL] at this
    exact this
  -- the shift tables
  obtain ⟨L0, n24, eL0, h24, h0⟩ := peelN h0 (noA_mapTB (fun _ => noA_gLowTab _ _ _ _ _) _)
  have hL0 : vals xv V L0 = (List.range 8).map (lowTab (repA c.P (fun j => xv (c.pv j))) (scF.1.take 6) 0) := by
    rw [← eL0]
    exact forall₂_map_eq (mapTB_spec (P := fun rl x => x = lowTab _ _ 0 rl)
      (fun rl m hm => gLowTab_spec hz htaLo htbLo (by rw [hAL]; norm_num) (by rw [hbL]; norm_num) 0 rl m hm) _ _ h24)
  obtain ⟨L1, n25, eL1, h25, h0⟩ := peelN h0 (noA_mapTB (fun _ => noA_gLowTab _ _ _ _ _) _)
  have hL1 : vals xv V L1 = (List.range 8).map (lowTab (repA c.P (fun j => xv (c.pv j))) (scF.1.take 6) 1) := by
    rw [← eL1]
    exact forall₂_map_eq (mapTB_spec (P := fun rl x => x = lowTab _ _ 1 rl)
      (fun rl m hm => gLowTab_spec hz htaLo htbLo (by rw [hAL]; norm_num) (by rw [hbL]; norm_num) 1 rl m hm) _ _ h25)
  obtain ⟨H, n26, eH, h26, h0⟩ := peelN h0 (noA_mapTB (fun _ => noA_gHighTab _ _ _ _) _)
  have hH : vals xv V H = (List.range 8).map (highTab (repA c.P (fun j => xv (c.pv j))) (scF.1.take 6)) := by
    rw [← eH]
    exact forall₂_map_eq (mapTB_spec (P := fun k x => x = highTab _ _ k)
      (fun k m hm => gHighTab_spec hz htaHi htbHi hAL hbL k m hm) _ _ h26)
  obtain ⟨sh, n27, esh, h27, h0⟩ := peelN h0 (noA_mapTB (fun _ => noA_gShift _ _ _ _ _) _)
  have hsh0 : sh.map (Src.valF xv V) =
      (List.range 64).map (shiftLH (repA c.P (fun j => xv (c.pv j))) (scF.1.take 6)) := by
    rw [← esh]
    exact forall₂_map_eq (mapTB_spec_mem (P := fun r x => x = shiftLH _ _ r) _
      (fun r hr m hm => gShift_spec hz hL0 hL1 hH (List.mem_range.mp hr) m hm) _ h27)
  have hshL : sh.length = 64 := by rw [← esh, mapTB_length, List.length_range]
  have hsh : ∀ r < 64, (sh.getD r default).valF xv V =
      rotSum (eqAt (scF.1.take 6)) (eqAt (repA c.P (fun j => xv (c.pv j)))) r := by
    intro r hr
    rw [getD_valF _ (by omega), hsh0, shift_LH hAL hbL hr, List.getD_eq_getElem _ _ (by simpa using hr),
      List.getElem_map, List.getElem_range]
  -- the final check's weight
  have hBS : vals xv V ((List.range 25).map fun l => c.pv (19 + c.P + l)) = repB c.P (fun j => xv (c.pv j)) := by
    simp only [vals, List.map_map]; rfl
  obtain ⟨Wk, n28, eWk, h28, h0⟩ :=
    peelN h0 (noA_gSumMap _ _ fun _ => noA_bind (noA_gLaneForm _ _ _ _) fun _ => noA_gMul _ _ _)
  have hWk : Wk.valF xv V = ((List.range 25).map fun l => (eqKernel (scF.1.drop 6)).getD l 0 *
      laneForm (repB c.P (fun j => xv (c.pv j)))
        (rotSum (eqAt (scF.1.take 6)) (eqAt (repA c.P (fun j => xv (c.pv j))))) l).sum := by
    rw [← eWk]
    refine gSumMap_spec' hz (fun l hl m hm => ?_) _ h28
    obtain ⟨g1, g2⟩ := (thold_bind _ _).mp hm
    rw [tb_bind, gMul_spec g2, gLaneForm_spec hz (by simp) _ hl _ g1, hz, add_zero, getD_valF _ (by omega), heL,
      hBS, laneForm_congr _ hsh l]
  obtain ⟨dfB, n29, edfB, h29, h0⟩ := peelN h0 (noA_gSumMap _ _ fun _ => noA_gMul _ _ _)
  have hdfB : dfB.valF xv V = ((List.range 25).map fun l =>
      (eqKernel (scF.1.drop 6)).getD l 0 * (repB c.P (fun j => xv (c.pv j))).getD l 0).sum := by
    rw [← edfB]
    refine gSumMap_spec' hz (fun l hl m hm => ?_) _ h29
    rw [gMul_spec hm, hz, add_zero, getD_valF _ (by omega), heL, getD_vals _ (by simp; omega), hBS]
  obtain ⟨idx, n30, eidx, h30, h0⟩ := peelN h0 (noA_gIndex _ _ _ _)
  have hidx : idx.valF xv V = indexMle (scF.1.take 6) := by
    rw [← eidx, gIndex_spec hz _ _ _ _ h30, hone, pow_zero, pow_one]
    show indexMleFrom gen ((lc.2.take 6).map (Src.valF xv V)) 1 = _
    rw [List.map_take, hlc2]
    rfl
  obtain ⟨Wf, n31, eWf, h31, h0⟩ := peelN h0 (noA_gMul _ _ _)
  obtain ⟨d, n32, ed, h32, h0⟩ := peelN h0 (noA_gAdd _ _)
  obtain ⟨W, n33, eW, h33, h0⟩ := peelN h0 (noA_gMul _ _ _)
  have hW : W.valF xv V = weightedLayerF scF.1 C := by
    rw [weighted_rep hR hscL, ← eW, gMul_spec h33, ← ed, gAdd_spec h32, ← eWf, gMul_spec h31, hz, add_zero,
      hdfB, hidx, hWk, show (c.k 14).valF xv V = xv (c.k 14) from rfl, hfirst]
    cases first
    · simp only [Bool.false_eq_true, ite_false, zero_mul, zero_add]
    · simp only [ite_true, one_mul, add_assoc, FE_add_self, add_zero]
  -- check 2
  obtain ⟨kt0, n34, ekt0, h34, h0⟩ := peelN h0 (noA_gMul _ _ _)
  obtain ⟨k1, n35, ek1, h35, h0⟩ := peelN h0 (noA_gAdd _ _)
  obtain ⟨mm, n36, emm, h36, h0⟩ := peelN h0 (noA_gMul _ _ _)
  obtain ⟨sw, n37, esw, h37, h0⟩ := peelN h0 (noA_gMul _ _ _)
  obtain ⟨e2, n38, ee2, h38, h0⟩ := peelN h0 (noA_gMul _ _ _)
  obtain ⟨n39, h0⟩ := peelA h0
  have he2 : e2.valF xv V = pkF.2.1 * weightedLayerF scF.1 C * (sumE (keccakInstanceWeights sF) * tF.getD 0 0 +
      (sumE (keccakInstanceWeights sF) + tF.getD 1 0) * tF.getD 2 0) + scF.2 := by
    rw [← ee2, gMul_spec h38, ← esw, gMul_spec h37, ← emm, gMul_spec h36, ← ek1, gAdd_spec h35, ← ekt0,
      gMul_spec h34, hz, hW, hkap, hpk2, hlc1, htk 0 (by norm_num), htk 1 (by norm_num), htk 2 (by norm_num)]
    ring
  have hK2 : e2.valF xv V = 0 ↔ (pkF.2.1 * weightedLayerF scF.1 C * (sumE (keccakInstanceWeights sF) * tF.getD 0 0 +
      (sumE (keccakInstanceWeights sF) + tF.getD 1 0) * tF.getD 2 0) == scF.2) = true := by
    rw [he2, fe_beq_iff, fe_add_eq_zero]
  -- the next claim
  obtain ⟨tt, n40, ett, h40, h0⟩ := peelN h0 (noA_gMul _ _ _)
  obtain ⟨v', n41, ev', h41, h0⟩ := peelN h0 (noA_gMul _ _ _)
  have hv' : v'.valF xv V = tF.getD 0 0 + βF * (tF.getD 1 0 + βF * tF.getD 2 0) := by
    rw [← ev', gMul_spec h41, ← ett, gMul_spec h40, hbeta, htk 0 (by norm_num), htk 1 (by norm_num),
      htk 2 (by norm_num)]
    ring
  obtain ⟨B', n42, eB', h42, h0⟩ := peelN h0 (noA_gLaneW _ _)
  have hB' : B'.map (Src.valF xv V) = (List.range 25).map fun l => eqAt (scF.1.drop 6) l + βF *
      (eqAt (scF.1.drop 6) (keccakAlong (64 * l) 4 / 64) + βF * eqAt (scF.1.drop 6) (keccakAlong (64 * l) 3 / 64)) := by
    rw [← eB']
    refine (gLaneW_spec (by omega) beta _ h42).trans ?_
    rw [show vals xv V eL = eqKernel (scF.1.drop 6) from heL, hbeta]
    rfl
  have hB'L : B'.length = 25 := by
    have := congrArg List.length hB'
    rwa [List.length_map, List.length_map, List.length_range] at this
  obtain ⟨A', n43, eA', h43, h0⟩ := peelN h0 (noA_gEqTab _ _ _)
  have hA' : A'.map (Src.valF xv V) = eqKernel (scF.1.take 6) := by
    rw [← eA', eqTab_one hz hone _ _ h43, List.map_take, hlc2]
  have hA'L : A'.length = 64 := by
    have := congrArg List.length hA'
    rw [List.length_map, eqKernel_length, hbL] at this
    exact this
  obtain ⟨fl, n44, efl, h44, h0⟩ := peelN h0 (noA_mapTB (fun _ => noA_gFlip _ _ _ _) _)
  have hfl : fl.map (Src.valF xv V) =
      (List.range 7).map (flipForm (B'.map (Src.valF xv V)) (eqAt (scF.1.take 6))) := by
    rw [← efl]
    refine forall₂_map_eq (mapTB_spec (P := fun i x => x = flipForm (B'.map (Src.valF xv V)) (eqAt (scF.1.take 6)) i)
      (fun i m hm => ?_) _ _ h44)
    rw [gFlip_spec hz (by omega) hA'L i m hm, show vals xv V A' = eqKernel (scF.1.take 6) from hA']
    rfl
  have hflL : fl.length = 7 := by rw [← efl, mapTB_length, List.length_range]
  -- the copy rows
  obtain ⟨hcp, h0⟩ := peelL h0 (noA_mapTB (fun _ => noA_gCopy _) _)
  obtain ⟨hLn, hTA⟩ := inv_end h0
  rw [mapTB_gCopy_length] at hLn
  simp only [List.length_append, List.length_singleton, hmkL, hpkL, hB'L, List.length_take, hlcL, hflL] at hLn
  have hcbN : n44 = c.cb := by
    rw [hLn] at hcb
    simp only [LCfg.C] at hcb
    omega
  have hcp' := cp_of hcp
  rw [hcbN] at hcp'
  obtain ⟨c6, cfl⟩ := cp_append hcp'
  obtain ⟨c5, cA⟩ := cp_append c6
  obtain ⟨c4, cB⟩ := cp_append c5
  obtain ⟨c3, cPt⟩ := cp_append c4
  obtain ⟨c2, cK⟩ := cp_append c3
  obtain ⟨cV, cM⟩ := cp_append c2
  simp only [List.length_append, List.length_singleton, hmkL, hpkL, hB'L, List.length_take, hlcL] at cM cK cPt cB cA cfl
  have hrA : repA c.P (fun j => V (c.cb + j)) = scF.1.take 6 := by
    rw [← hlc2, ← List.map_take, ← cp_range cA (k := 6) (by simp [hlcL])]
    unfold repA
    exact List.map_congr_left fun i _ => congrArg V (by omega)
  have hrB : repB c.P (fun j => V (c.cb + j)) = B'.map (Src.valF xv V) := by
    rw [← cp_range cB hB'L]
    unfold repB
    exact List.map_congr_left fun i _ => congrArg V (by omega)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- value
    show V (c.cb + 0) = tF.getD 0 0 + βF * (tF.getD 1 0 + βF * tF.getD 2 0)
    rw [cp_get cV 0 (by simp)]
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
    exact hv'
  · -- μ
    show (List.range 16).map (fun i => V (c.cb + (1 + i))) = keccakInstanceWeights sF
    rw [← hmu', ← cp_range cM hmkL]
    exact List.map_congr_left fun i _ => congrArg V (by omega)
  · -- κ
    show V (c.cb + 17) = sumE (keccakInstanceWeights sF)
    have := cp_get cK 0 (by simp)
    rw [show c.cb + 17 = c.cb + (1 + 16) + 0 by omega, this]
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero]
    exact hkap
  · -- the point
    show (List.range (c.P + 1)).map (fun i => V (c.cb + (18 + i))) = pkF.2.2.1
    rw [← hpk3, ← cp_range cPt hpkL]
    exact List.map_congr_left fun i _ => congrArg V (by omega)
  · -- the weights
    show keccakLinearTranspose ((List.range keccakBits).map fun j =>
        (eqKernelA (scF.1.take 6)).getD (j % 64) 0 * (laneWF scF.1 βF).getD (j / 64) 0) =
      if false = true then _ else _
    simp only [Bool.false_eq_true, ite_false]
    rw [hrA, hrB, hB']
    refine congrArg keccakLinearTranspose (List.map_congr_left fun j _ => ?_)
    rw [getD_eqKernelA, laneWF_eq, array_getD_toArray']
  · -- the flips
    intro i hi
    show V (c.cb + (50 + c.P + i)) = if false = true then _ else _
    simp only [Bool.false_eq_true, ite_false]
    rw [hrA, hrB]
    have := cp_get cfl i (by rw [hflL]; exact hi)
    rw [show c.cb + (50 + c.P + i) = c.cb + (1 + 16 + 1 + (c.P + 1) + 25 + min 6 11) + i by omega, this, hfl,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  · -- the position
    rw [hp3', hstr]; omega
  · intro hta hg
    obtain ⟨⟨-, q1⟩, q2⟩ := hTA.mp hta
    rw [show (c.k 15).valF xv V = xv (c.k 15) from rfl, hg, one_mul] at q1 q2
    exact ⟨hK1.mp q1, hK2.mp q2⟩
  · intro o1 o2
    exact hTA.mpr ⟨⟨trivial, by rw [hK1.mpr o1, mul_zero]⟩, by rw [hK2.mpr o2, mul_zero]⟩

/-- **One layer** (Q_arith_eq of `verifyKeccakLayer`). -/
theorem layer_spec {c : LCfg} {xv : Src → FE} {V : Nat → FE} (hH : THold xv V 0 (layerTB c 0).2)
    (hcb : c.cb + c.C = (layerTB c 0).2.length)
    {C : KeccakClaim} {first : Bool} (hR : Rep c.P (fun j => xv (c.pv j)) C first)
    {step : Nat} (hstep : step < gkrDepth)
    (hrc : ∀ i < 7, xv (c.k i) = rcBit (keccakRC.getD (gkrDepth * 1 - step - 1) 0) i ∧
      xv (c.k (7 + i)) = rcBit (keccakRC.getD (gkrDepth * 2 - step - 1) 0) i)
    (hfirst : xv (c.k 14) = if first then 1 else 0)
    {v : Nat → FE} {off p : Nat} (hv : ∀ m < c.q + c.str, lv xv [c.str] m = v (8 * m + off))
    (hp : p + 40 = 8 * c.q + off) :
    Rep c.P (fun j => V (c.cb + j)) (layerSpec v (c.P + 4) step C p).claim false ∧
    (layerSpec v (c.P + 4) step C p).pos = p + 8 * c.str ∧
    (TAssert xv V (layerTB c 0).2 → xv (c.k 15) = 1 →
      (layerSpec v (c.P + 4) step C p).ok1 = true ∧ (layerSpec v (c.P + 4) step C p).ok2 = true) ∧
    ((layerSpec v (c.P + 4) step C p).ok1 = true → (layerSpec v (c.P + 4) step C p).ok2 = true →
      TAssert xv V (layerTB c 0).2) :=
  layer_core (inv_start hH) hcb hR hstep hrc hfirst hv hp

end Lvm.Q1
