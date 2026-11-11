import LvmQLinkArithCH

/-!
# QA1 links: the `CH` link gadget and its soundness against `F`

`chLinkGadget n D Q gate`: block A, the shift sumcheck (`2^D ≥ n` iterations), block B, the two-round
sumcheck, block C. **`chLink_sound`**: in every memory where the gadget's rows hold, whose input lanes
are the stream's (`Streamed`), with the phase starting at position `P` (`P + 40 = 8Q`) and gate `1`:
if the gadget's assertion holds, then `chLink0`'s check on what `F` reads in phase 5
(`chLinkView`, `LvmQLinkArithRead`) is `true`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Small facts -/

theorem lnk_fe_beq (x y : FE) : (x == y) = true ↔ x = y := by
  cases x; cases y
  show ((_ == _ && _ == _) && _ == _) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem lnk_scSpec_length (v : Nat → FE) (count : Nat) : ∀ (p : Nat) (claim : FE) (es : List (Option FE)),
    (scSpec v count p claim es).1.length = es.length
  | _, _, [] => rfl
  | p, claim, e :: es => by simp [scSpec, lnk_scSpec_length v count _ _ es]

theorem take_range_map (f : Nat → FE) {n N : Nat} (h : n ≤ N) :
    ((List.range N).map f).take n = (List.range n).map f := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem drop_range_map (f : Nat → FE) (n N : Nat) :
    ((List.range N).map f).drop n = (List.range (N - n)).map fun i => f (n + i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_drop, List.getElem_map, List.getElem_range]

/-! ## The gadget -/

/-- The shift sumcheck's first message lane. -/
def chQ1 (n Q : Nat) : Nat := Q + 9 * (n + 9)
/-- The `in` slices' first lane. -/
def chQB (n Q : Nat) : Nat := chQ1 n Q + 15 * n
/-- The two-round sumcheck's first message lane. -/
def chQ2 (n Q : Nat) : Nat := chQB n Q + 246
/-- The `Y` slices' first lane. -/
def chQC (n Q : Nat) : Nat := chQ2 n Q + 30

/-- `ρ`'s cells (block A's loads `0 … n − 1`). -/
def rhoC (oA : LoopOut) (n : Nat) : List Cell := (List.range n).map fun i => oA.cell i 0
/-- `ρ'`'s cells (the shift sumcheck's challenges). -/
def rho'C (sh : LoopOut) (n : Nat) : List Cell := (List.range n).map fun i => sh.cell 2 i
/-- `eq(ζ, ·)`'s cells. -/
def eZC (oA : LoopOut) (n : Nat) : List Cell := (List.range 64).map fun k => oA.cell (n + 96 + k) 0
/-- `eq(λ, ·)`'s cells. -/
def eLC (oA : LoopOut) (n : Nat) : List Cell := (List.range 8).map fun k => oA.cell (n + 20 + k) 0

/-- **The `CH` link gadget** (phase 5's arithmetic). -/
def chLinkGadget (n D Q : Nat) (gate : Cell) : BM Unit := do
  let oA ← loop [] (tplOf (chGlueA n Q))
  let sh ← scGadget D 2 (chQ1 n Q) .plain (oA.cell (2 * n + 165) 0)
  let oB ← loop [] (tplOf (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))))
  let sc2 ← scGadget 1 2 (chQ2 n Q) .plain (oB.cell (8 * n + 130) 0)
  let _ ← loop [] (tplOf (chGlueC (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n) (rho'C sh n)
    (oA.cell (2 * n + 163) 0) (oB.cell (8 * n + 123) 0) (sc2.cell 5 1) gate))
  pure ()

/-! ## Soundness -/

theorem chGlueC_last (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) (hm : mu.length = 2) :
    (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).getD (151 + rho'.length) default =
      ⟨.assert0, .K, [.loc (150 + rho'.length), cellSrc gate]⟩ := by
  have hlen := chGlueC_length QC mu eL eZ rho' prodRho eqE f2 gate hm
  rw [show 151 + rho'.length = (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).length - 1 by omega,
    List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
  simp [chGlueC, List.getLast?_append, List.getLast?_cons]

theorem cell_iterV {M : Mem} (o : LoopOut) {t len : Nat} (ht : t < len) :
    (o.cell t 0).val M = (iterV M o len 0).getD t 0 := (iterV_getD M o ht).symm

/-- **The `CH` link circuit is sound for `F`'s phase-5 check.** -/
theorem chLink_sound (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {tfv : Pub → List FE → List FE}
    {tfs : Pub → List (List FE × List FE) → List FE} {tpc : Pub → List (List FE × List FE) → Bool}
    (blk : Placement) (ySlot D : Nat) {c : Ctx} {M : Mem} {ptr : Ptr}
    {sig : ByteArray} {T P Q : Nat} (r w : List FE) (pub : Pub) (gate : Cell)
    (hn : 1 ≤ p.logN) (hD : p.logN ≤ 2 ^ D) (hPQ : P + 40 = 8 * Q)
    (hokA : SLok (chGlueA p.logN Q) = true)
    (hokB : ∀ oA sh : LoopOut, SLok (chGlueB (chQB p.logN Q) (rhoC oA p.logN) (rho'C sh p.logN) (eZC oA p.logN)
      (sh.cell 5 (p.logN - 1))) = true)
    (hokC : ∀ oA sh sc2 oB : LoopOut, SLok (chGlueC (chQC p.logN Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA p.logN)
      (eZC oA p.logN) (rho'C sh p.logN) (oA.cell (2 * p.logN + 163) 0) (oB.cell (8 * p.logN + 123) 0)
      (sc2.cell 5 1) gate) = true)
    (hS : Streamed M sig T) (hT : chQC p.logN Q + 3 * 64 + 3 ≤ T) (hg : gate.val M = 1)
    (h : SegsHold c M ptr (chLinkGadget p.logN D Q gate ptr).2)
    (hA : SegsAssert M ptr (chLinkGadget p.logN D Q gate ptr).2) :
    (chLink0 p blk ySlot (chLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P r w pub)).1 = true := by
  set n := p.logN with hndef
  -- decomposition
  simp only [chLinkGadget] at h hA
  rw [hold_bind] at h; obtain ⟨hhA, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhS, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhB, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hh2, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhC, -⟩ := h
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨haC, -⟩ := hA
  -- names
  generalize hoA : (loop [] (tplOf (chGlueA n Q)) ptr).1 = oA at hhS hhB hh2 hhC haC
  have hFA : Fix (iterXv M oA 0) (chGlueA n Q) (iterV M oA (chGlueA n Q).length 0) := by
    rw [← hoA]; exact fix_of_loop hokA hhA (by simp)
  generalize hVA : iterV M oA (chGlueA n Q).length 0 = VA at hFA
  have hlA := chGlueA_length n Q
  have hcA : ∀ t < 2 * n + 166, (oA.cell t 0).val M = VA.getD t 0 := by
    intro t ht; rw [← hVA, cell_iterV (len := (chGlueA n Q).length) oA (by rw [hlA]; exact ht)]
  obtain ⟨A1, -, -, AL, AZ, AP, AT⟩ := chGlueA_val hS hFA hn (by simp [chQC, chQ2, chQB, chQ1] at hT; omega)
  -- F's challenges
  set f : Nat → FE := fun i => feAt sig (P + 40 + 72 * i) with hf
  have hchal : samplesAt (feAt sig) P (n + 3 + 6) = (List.range (n + 9)).map f := rfl
  have hVf : ∀ i < n + 9, VA.getD i 0 = f i := by
    intro i hi; rw [A1 i hi, hf]; congr 1; omega
  have hrhoF : (samplesAt (feAt sig) P (n + 3 + 6)).take n = (List.range n).map f := by
    rw [hchal, take_range_map _ (by omega)]
  have hlamF : ((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3 = [f n, f (n + 1), f (n + 2)] := by
    rw [hchal, drop_range_map, show n + 9 - n = 9 by omega, take_range_map _ (by omega)]
    simp [List.range_succ]
  have hzetaF : (samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3) = (List.range 6).map fun i => f (n + 3 + i) := by
    rw [hchal, drop_range_map, show n + 9 - (n + 3) = 6 by omega]
  have hlamV : [VA.getD n 0, VA.getD (n + 1) 0, VA.getD (n + 2) 0] = [f n, f (n + 1), f (n + 2)] := by
    rw [hVf n (by omega), hVf (n + 1) (by omega), hVf (n + 2) (by omega)]
  have hzetaV : ((List.range 6).map fun i => VA.getD (n + 3 + i) 0) = (List.range 6).map fun i => f (n + 3 + i) := by
    apply List.map_congr_left; intro i hi; rw [hVf _ (by simp at hi; omega)]
  have hrhoV : ((List.range n).map fun i => VA.getD i 0) = (List.range n).map f := by
    apply List.map_congr_left; intro i hi; rw [hVf _ (by simp at hi; omega)]
  rw [hlamV, hzetaV, hrhoV] at AT
  rw [hrhoV] at AP
  -- the shift sumcheck's claim is F's
  have hclaimA : (oA.cell (2 * n + 165) 0).val M =
      chShiftTarget0 p (samplesAt (feAt sig) P (n + 3 + 6)) := by
    rw [hcA _ (by omega), AT, chShiftTarget0_eq p _ (by simp [samplesAt, hndef]), hrhoF, hlamF, hzetaF]
  -- the shift sumcheck
  have hq1 : 8 * chQ1 n Q - 40 = chP1 p P := by simp only [chQ1, chP1, ← hndef]; omega
  have hSC := sc_spec_plain (R := n) (by omega) (scTpl_ok_2 _) hD (by simp [chQ1]; omega) hS
    (by simp [chQC, chQ2, chQB, chQ1, roundLanes] at hT ⊢; omega) hhS
  set pS := ptr.adv (loop [] (tplOf (chGlueA n Q)) ptr).2 with hpS
  generalize hsh : (scGadget D 2 (chQ1 n Q) .plain (oA.cell (2 * n + 165) 0) pS).1 = sh at hSC hhB hh2 hhC haC
  rw [hq1, hclaimA] at hSC
  set shiftF := scSpec (feAt sig) 3 (chP1 p P) (chShiftTarget0 p (samplesAt (feAt sig) P (n + 3 + 6)))
    (List.replicate n none) with hshiftF
  have hSlen : shiftF.1.length = n := by rw [hshiftF, lnk_scSpec_length]; simp
  have S1 : (rho'C sh n).map (Cell.val M) = shiftF.1 := by
    apply List.ext_getElem
    · simp [rho'C, hSlen]
    · intro i h1 h2
      have hi : i < n := by simpa [rho'C] using h1
      simp only [rho'C, List.getElem_map, List.getElem_range]
      rw [(hSC i hi).1, List.getD_eq_getElem _ _ h2]
  have S2 : (sh.cell 5 (n - 1)).val M = shiftF.2 := by
    rw [(hSC (n - 1) (by omega)).2, show n - 1 + 1 = n by omega, List.take_of_length_le (by simp)]
  -- block B
  have hrhoC : (rhoC oA n).map (Cell.val M) = (samplesAt (feAt sig) P (n + 3 + 6)).take n := by
    rw [hrhoF, rhoC, List.map_map]
    apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.mp hi
    show (oA.cell i 0).val M = f i
    rw [hcA i (by omega), hVf i (by omega)]
  have heZ : ∀ k < 64, ((eZC oA n).getD k default).val M =
      eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) k := by
    intro k hk
    have : (eZC oA n).getD k default = oA.cell (n + 96 + k) 0 := by
      simp [eZC, List.getD_eq_getElem?_getD, hk]
    rw [this, hcA _ (by omega), hzetaF, ← hzetaV, ← AZ k hk, eZs_eq n k hk, val_loc]
  have heL : ∀ k < 8, ((eLC oA n).getD k default).val M =
      eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) k := by
    intro k hk
    have : (eLC oA n).getD k default = oA.cell (n + 20 + k) 0 := by
      simp [eLC, List.getD_eq_getElem?_getD, hk]
    rw [this, hcA _ (by omega), hlamF, ← hlamV, ← AL k hk, eLs_eq n k hk, val_loc]
  have hFB := fix_of_loop (hokB oA sh) hhB (jf := 0) (by simp)
  obtain ⟨-, B2, B3⟩ := chGlueB_val hS hFB (by simp [rhoC]; omega) (by simp [rhoC, rho'C])
    (by simp only [chQC, chQ2] at hT; omega)
  set pB := pS.adv (scGadget D 2 (chQ1 n Q) Mode.plain (oA.cell (2 * n + 165) 0) pS).2 with hpB
  generalize hoB : (loop [] (tplOf (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1)))) pB).1 = oB
    at hFB B2 B3 hh2 hhC haC
  have hlenB : (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))).length = 8 * n + 131 := by
    simp only [chGlueB, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length,
      List.length_cons, List.length_nil, rhoC]
    rw [shiftRecIns_length _ _ _ _ _ _ (by simp [rho'C])]; simp; omega
  simp only [rhoC, List.length_map, List.length_range] at B2 B3
  rw [show ((List.range n).map fun i => oA.cell i 0) = rhoC oA n from rfl, hrhoC, S1] at B2 B3
  rw [S2] at B3
  set inSF := scalarsAt (feAt sig) (chP2 p P + 40) kBits with hinSF
  have hinS : ∀ k < 64, feAt sig (8 * (chQB n Q + 3 * k)) = inSF.getD k 0 := by
    intro k hk
    rw [hinSF, scalarsAt, List.getD_eq_getElem?_getD]
    simp only [kBits, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
    congr 1
    simp only [chQB, chQ1, chP2, chP1, roundLen, ← hndef]; omega
  have hclaimB : (oB.cell (8 * n + 130) 0).val M = chSc2Target0 p (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF := by
    have hsum : ∑ k ∈ Finset.range 64, ((eZC oA n).getD k default).val M * feAt sig (8 * (chQB n Q + 3 * k)) =
        ∑ q ∈ Finset.range 64, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) q * inSF.getD q 0 :=
      Finset.sum_congr rfl fun k hk => by
        have hk' := Finset.mem_range.mp hk
        rw [heZ k hk', hinS k hk']
    rw [cell_iterV (len := (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))).length) oB
      (by rw [hlenB]; omega), B3, chSc2Target0_eq p _ _ _ (by simp [samplesAt, hndef])
      (by simp [hinSF, kBits, scalarsAt]), hsum]
    ring
  -- the two-round sumcheck
  have hq2 : 8 * chQ2 n Q - 40 = chP3 p P := by
    simp only [chQ2, chQB, chQ1, chP3, chP2, chP1, roundLen, kBits, ringStages, ← hndef]; omega
  have hSC2 := sc_spec_plain (R := 2) (D := 1) (by omega) (scTpl_ok_2 _) (by norm_num) (by simp [chQ2, chQB, chQ1] <;> omega) hS
    (by simp [chQC, roundLanes] at hT ⊢ <;> omega) hh2
  set p2 := pB.adv (loop [] (tplOf (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1)))) pB).2
    with hp2
  generalize hsc2 : (scGadget 1 2 (chQ2 n Q) .plain (oB.cell (8 * n + 130) 0) p2).1 = sc2 at hSC2 hhC haC
  rw [hq2, hclaimB] at hSC2
  set sc2F := scSpec (feAt sig) 3 (chP3 p P) (chSc2Target0 p (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF)
    [none, none] with hsc2F
  change ∀ i < 2, Cell.val M (sc2.cell 2 i) = sc2F.1.getD i 0 ∧ Cell.val M (sc2.cell 5 i) =
    (scSpec (feAt sig) 3 (chP3 p P) (chSc2Target0 p (samplesAt (feAt sig) P (n + 3 + 6)) shiftF inSF)
      (([none, none] : List (Option FE)).take (i + 1))).2 at hSC2
  have hmu : [sc2.cell 2 0, sc2.cell 2 1].map (Cell.val M) = sc2F.1 := by
    have hl : sc2F.1.length = 2 := by rw [hsc2F, lnk_scSpec_length]; rfl
    have h2 : sc2F.1 = [sc2F.1.getD 0 0, sc2F.1.getD 1 0] := by
      match hm : sc2F.1, hl with
      | [a, b], _ => rfl
    rw [h2, ← (hSC2 0 (by omega)).1, ← (hSC2 1 (by omega)).1]
    rfl
  have hf2 : (sc2.cell 5 1).val M = sc2F.2 := by
    rw [(hSC2 1 (by omega)).2]; rfl
  -- block C
  have hokC' := hokC oA sh sc2 oB
  have hFC := fix_of_loop hokC' hhC (jf := 0) (by simp)
  have hlenC := chGlueC_length (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n) (rho'C sh n)
    (oA.cell (2 * n + 163) 0) (oB.cell (8 * n + 123) 0) (sc2.cell 5 1) gate rfl
  have hrl : (rho'C sh n).length = n := by simp [rho'C]
  have hlast := chGlueC_last (chQC n Q) [sc2.cell 2 0, sc2.cell 2 1] (eLC oA n) (eZC oA n) (rho'C sh n)
    (oA.cell (2 * n + 163) 0) (oB.cell (8 * n + 123) 0) (sc2.cell 5 1) gate rfl
  have hAs := assert_of_loop hokC' haC (jf := 0) (by simp) (t := 151 + (rho'C sh n).length)
    (by rw [hlenC]; omega) (by rw [hlast])
  rw [hlast] at hAs
  simp only [List.getD_cons_zero, List.getD_cons_succ, val_loc] at hAs
  have C := chGlueC_sound hS hFC rfl (by omega) (by rw [hrl]; omega) hAs hg
  rw [hf2, hmu, S1] at C
  have hprodRho : (oA.cell (2 * n + 163) 0).val M = ((samplesAt (feAt sig) P (n + 3 + 6)).take n).prod := by
    rw [hcA _ (by omega), AP, hrhoF]
  have heqE : (oB.cell (8 * n + 123) 0).val M = eqEval ((samplesAt (feAt sig) P (n + 3 + 6)).take n) shiftF.1 := by
    rw [cell_iterV (len := (chGlueB (chQB n Q) (rhoC oA n) (rho'C sh n) (eZC oA n) (sh.cell 5 (n - 1))).length) oB
      (by rw [hlenB]; omega), B2]
  rw [hprodRho, heqE] at C
  set ySF := scalarsAt (feAt sig) (chP4 p P + 40) kBits with hySF
  have hyS : ∀ q < 64, feAt sig (8 * (chQC n Q + 3 * q)) = ySF.getD q 0 := by
    intro q hq
    rw [hySF, scalarsAt, List.getD_eq_getElem?_getD]
    simp only [kBits, List.getElem?_map, List.getElem?_range hq, Option.map_some, Option.getD_some]
    congr 1
    simp only [chQC, chQ2, chQB, chQ1, chP4, chP3, chP2, chP1, roundLen, kBits, ringStages, ← hndef]; omega
  have hα : ∑ m ∈ Finset.range 4, eqW sc2F.1 m * ((eLC oA n).getD m default).val M =
      ∑ m ∈ Finset.range 4, eqW sc2F.1 m * eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) m :=
    Finset.sum_congr rfl fun m hm => by rw [heL m (by have := Finset.mem_range.mp hm; omega)]
  have hβ : ∑ m ∈ Finset.range 4, eqW sc2F.1 m * ((eLC oA n).getD (m + 1) default).val M =
      ∑ m ∈ Finset.range 4, eqW sc2F.1 m * eqW (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3) (m + 1) :=
    Finset.sum_congr rfl fun m hm => by rw [heL (m + 1) (by have := Finset.mem_range.mp hm; omega)]
  have hS1 : ∑ q ∈ Finset.range 56, ((eZC oA n).getD (q + 8) default).val M * feAt sig (8 * (chQC n Q + 3 * q)) =
      ∑ q ∈ Finset.range 56, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) (q + 8) * ySF.getD q 0 :=
    Finset.sum_congr rfl fun q hq => by
      have := Finset.mem_range.mp hq
      rw [heZ (q + 8) (by omega), hyS q (by omega)]
  have hS2 : ∑ q ∈ Finset.range 8, ((eZC oA n).getD q default).val M * feAt sig (8 * (chQC n Q + 3 * (q + 56))) =
      ∑ q ∈ Finset.range 8, eqW ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3)) q * ySF.getD (q + 56) 0 :=
    Finset.sum_congr rfl fun q hq => by
      have := Finset.mem_range.mp hq
      rw [heZ q (by omega), hyS (q + 56) (by omega)]
  rw [hα, hβ, hS1, hS2] at C
  -- F's check
  have hok : (chLink0 p blk ySlot (chLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P r w pub)).1 =
      (sc2F.2 == eqMasked ((samplesAt (feAt sig) P (n + 3 + 6)).take n) shiftF.1 *
        sumE ((List.range 64).map fun q => sumE ((List.range 4).map fun m =>
          (eqKernel sc2F.1).getD m 0 * padWeight (omegaCH (((samplesAt (feAt sig) P (n + 3 + 6)).drop n).take 3)
            ((samplesAt (feAt sig) P (n + 3 + 6)).drop (n + 3))) m q) * ySF.getD q 0)) := by
    rfl
  rw [hok, lnk_fe_beq, chLink_sum_eq _ _ _ _ (by simp [samplesAt] <;> omega) (by simp [samplesAt] <;> omega)
    (by rw [hsc2F, lnk_scSpec_length]; rfl), C]
  unfold eqMasked eqOnes
  rw [prodE_eq_prod, prodE_eq_prod]
  ring

end Lvm.Q1
