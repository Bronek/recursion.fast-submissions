-- New for lvm (HAR-RC): the claims of the link phases (5: `CH` link, `chLink0`'s two ring claims and
-- 17 constant-lane claims; 7: `KS` link, `ksLink0`'s four `sumClaim`s) as cells, every challenge and
-- scalar loaded from its stream lanes. Reused: QA1's reading (`chLinkView`, `ksLinkView`, lane
-- functions `chQ1 … chQC`, `take_range_map`, `drop_range_map`, `scSpec_fst_getD`), HAR's
-- `chLinkPh_run`/`ksLinkPh_run`, QA2's `eqTab_eq` (the `KS` link's `eq(λ, ·)`), this family's `ringG`.
import LvmQAsmArith2Claim
import LvmQLinkArithCHSound
import LvmQWhirBatch

/-!
# Q_arith: the claims of the link phases

* **`chLinkG n Q z o blk ySlot`** (phase 5 from the reader at `P`, `P + 40 = 8 Q`): loads `ρ'` (the
  shift sumcheck's `n` challenges), `λ` (3), `μ` (the two-round sumcheck's 2 challenges), the two
  ring switches (`ringG` on the `in`/`Y` slices and their challenges), one constant cell; returns
  `chLinkC`: the two ring claims at `(ρ', λ, 0, 0, 0)` and `(ρ', μ, slot bits)`, the 17 constant
  lanes at `(ρ', slot l)`. **`chLinkG_val`**: the cells are `(chLink0 p blk ySlot (chLinkView …)).2`;
  `chLinkPh_claims`: `F`'s phase-5 claims (`chLinkPh`) for `m = M3.ofParts p …` (any bus/table parts).
* **`ksLinkG p Q z o`** (phase 7): loads `λ` (5), `ρ'` (`ksLog`), the four scalars; `eq(λ, ·)` by
  QA2's `eqTab`; returns `ksLinkC`: the four `sumClaim`s. **`ksLinkG_val`**, `ksLinkPh_claims`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig DM

variable {c : Ctx} {M : Mem}

/-! ## `F`'s side -/

theorem scSpec_fst (v : Nat → FE) (count : Nat) (es : List (Option FE)) (p : Nat) (claim : FE) :
    (scSpec v count p claim es).1 =
      (List.range es.length).map fun i => v (p + i * roundLen count + 40 + 24 * (count - 1)) := by
  refine List.ext_getElem (by rw [lnk_scSpec_length]; simp) fun i h1 h2 => ?_
  have e := scSpec_fst_getD v count i es p claim (by rw [lnk_scSpec_length] at h1; exact h1)
  rw [List.getD_eq_getElem _ _ h1] at e
  rw [e]
  simp

/-! ## The `CH` link -/

/-- `ρ'`'s lanes (the shift sumcheck's answers), `λ`'s (samples `n … n + 2`), `μ`'s (the two-round
sumcheck's answers). -/
def chRhoL (n Q : Nat) : List Nat := (List.range n).map fun i => chQ1 n Q + 6 + 15 * i
def chLamL (n Q : Nat) : List Nat := (List.range 3).map fun j => Q + 9 * (n + j)
def chMuL (n Q : Nat) : List Nat := (List.range 2).map fun j => chQ2 n Q + 6 + 15 * j

/-- The `CH` link's claims as cells. -/
def chLinkC (blk : Placement) (ySlot z o : Nat) (rho' lam mu : List Cell) (rIn rY : RingOut)
    (c80 : Nat) : List CClaim :=
  [⟨.main, .ring blk (rho' ++ lam ++ [ec z, ec z, ec z]) rIn.cs, rIn.target⟩,
    ⟨.main, .ring blk (rho' ++ mu ++ selC z o (ySlot >>> 2) (slotLog - 2)) rY.cs, rY.target⟩] ++
  (List.range 17).map fun j =>
    ⟨.main, .point blk (rho' ++ selC z o (8 + j) slotLog), if 8 + j = 16 then ec c80 else ec z⟩

/-- **The `CH` link's claims** (phase 5; `P + 40 = 8 Q`). -/
def chLinkG (n Q z o : Nat) (blk : Placement) (ySlot : Nat) : BM (List CClaim) := do
  let rho' ← loadAt (chRhoL n Q)
  let lam ← loadAt (chLamL n Q)
  let mu ← loadAt (chMuL n Q)
  let rIn ← ringG (chQB n Q + 192) (chQB n Q) z
  let rY ← ringG (chQC n Q + 192) (chQC n Q) z
  let c80 ← const .E ⟨(0x80 : UInt64) <<< 56⟩ (ec z)
  pure (chLinkC blk ySlot z o rho' lam mu rIn rY c80.n)

theorem chLinkC_val (p : Params) (blk : Placement) {ySlot z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1)
    (rho' lam mu : List Cell) (rIn rY : RingOut) (c80 : Nat) (i : ChLinkIn)
    (hrho : vs M rho' = i.shift.1) (hlam : vs M lam = ((i.chal.drop p.logN).take 3))
    (hmu : vs M mu = i.sc2.1) (hIn : rIn.target.val M = i.ringIn.1 ∧ vs M rIn.cs = i.ringIn.2)
    (hY : rY.target.val M = i.ringY.1 ∧ vs M rY.cs = i.ringY.2)
    (hc : M.e c80 = FE.ofK ⟨(0x80 : UInt64) <<< 56⟩) :
    (chLinkC blk ySlot z o rho' lam mu rIn rY c80).map (CClaim.val M) = (chLink0 p blk ySlot i).2 := by
  have e1 : vs M (rho' ++ lam ++ [ec z, ec z, ec z]) = i.shift.1 ++ (i.chal.drop p.logN).take 3 ++ [0, 0, 0] := by
    rw [vs_append, vs_append, hrho, hlam]; simp [vs, hz]
  have e2 : vs M (rho' ++ mu ++ selC z o (ySlot >>> 2) (slotLog - 2)) =
      i.shift.1 ++ i.sc2.1 ++ selectorPoint (ySlot >>> 2) (slotLog - 2) := by
    rw [vs_append, vs_append, hrho, hmu, selC_vs hz ho]
  simp only [chLinkC, chLink0, chSplit, List.map_append, List.map_cons, List.map_nil, List.map_map]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · simp only [CClaim.val, e1, e2, hIn.1, hIn.2, hY.1, hY.2]
  · refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, CClaim.val, vs_append, hrho, selC_vs hz ho]
    split_ifs with h
    · simp [hc]
    · simp [hz, ofK_zero]

/-- **Q_arith_eq, the `CH` link's claims**: with the reader at `P` (`P + 40 = 8 Q`) the cells are
`chLink0`'s claims on what `F` reads in phase 5 (any `M3` `m`: the claims use only challenges, the
ring switches and constants). -/
theorem chLinkG_val (p : Params) (m : M3) (blk : Placement) {ySlot z o Q P T : Nat} {sig : ByteArray}
    {ptr : Ptr} (r w : List FE) (pub : Pub) (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T)
    (hT : chQC p.logN Q + 240 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1)
    (h : SegsHold c M ptr (chLinkG p.logN Q z o blk ySlot ptr).2) :
    (chLinkG p.logN Q z o blk ySlot ptr).1.map (CClaim.val M) =
      (chLink0 p blk ySlot (chLinkView p m (feAt sig) P r w pub)).2 := by
  simp only [chLinkG] at h ⊢
  rw [hold_bind] at h; obtain ⟨h1, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h2, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h3, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h4, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h5, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h6, -⟩ := h
  simp only [bind_apply, pure_apply]
  have hQB : chQB p.logN Q + 192 + 48 ≤ T := by simp only [chQC, chQ2] at hT; omega
  have hQ1 : chQ1 p.logN Q ≤ chQB p.logN Q := by simp only [chQB]; omega
  obtain ⟨rI1, rI2⟩ := ringG_spec hS hQB (by omega) hz h4
  obtain ⟨rY1, rY2⟩ := ringG_spec hS hT (by omega) hz h5
  have hslIn : slAt sig (chQB p.logN Q) = scalarsAt (feAt sig) (chP2 p P + 40) kBits := by
    simp only [slAt, scalarsAt]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [chP2, chP1, chQB, chQ1, roundLen]; omega
  have hchIn : chsAt sig (chQB p.logN Q + 192) = samplesAt (feAt sig) (chP2 p P + 24 * kBits) ringStages := by
    simp only [chsAt, samplesAt]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [chP2, chP1, chQB, chQ1, roundLen, kBits]; omega
  have hslY : slAt sig (chQC p.logN Q) = scalarsAt (feAt sig) (chP4 p P + 40) kBits := by
    simp only [slAt, scalarsAt]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [chP4, chP3, chP2, chP1, chQC, chQ2, chQB, chQ1, roundLen, kBits, ringStages]; omega
  have hchY : chsAt sig (chQC p.logN Q + 192) = samplesAt (feAt sig) (chP4 p P + 24 * kBits) ringStages := by
    simp only [chsAt, samplesAt]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [chP4, chP3, chP2, chP1, chQC, chQ2, chQB, chQ1, roundLen, kBits, ringStages]; omega
  refine chLinkC_val p blk hz ho _ _ _ _ _ _ _ ?_ ?_ ?_ ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_
  · -- `ρ'`
    rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [chRhoL, List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      simp only [chQC, chQ2, chQB] at hT; omega) h1]
    simp only [chLinkView, scSpec_fst, List.length_replicate, chRhoL, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    exact congrArg (feAt sig) (by simp only [chP1, chQ1, roundLen]; omega)
  · -- `λ`
    rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [chLamL, List.mem_map, List.mem_range] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      simp only [chQC, chQ2, chQB, chQ1] at hT; omega) h2]
    simp only [chLinkView, samplesAt, chLamL, List.map_map]
    rw [drop_range_map, show p.logN + 3 + 6 - p.logN = 9 by omega, take_range_map _ (by omega)]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    exact congrArg (feAt sig) (by omega)
  · -- `μ`
    rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [chMuL, List.mem_map, List.mem_range] at hq
      obtain ⟨j, hj, rfl⟩ := hq
      simp only [chQC] at hT; omega) h3]
    simp only [chLinkView, scSpec_fst, chMuL, List.map_map, List.length_cons, List.length_nil]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    exact congrArg (feAt sig) (by
      simp only [chP3, chP2, chP1, chQ2, chQB, chQ1, roundLen, kBits, ringStages]; omega)
  · rw [rI2, hslIn, hchIn]; rfl
  · rw [rI1, hchIn]; rfl
  · rw [rY2, hslY, hchY]; rfl
  · rw [rY1, hchY]; rfl
  · exact constE_spec h6

/-- **`F`'s phase-5 claims** (`chLinkPh`, `m = M3.ofParts p …` (any bus/table parts)) from the reader at `P`. -/
theorem chLinkPh_claims (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)}
    {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool} {z o Q T : Nat} {sig : ByteArray} {ptr : Ptr}
    (r w : List FE) (pub : Pub) (s : RS) (hn : 1 ≤ p.logN) (hPQ : pos s + 40 = 8 * Q)
    (hS : Streamed M sig T) (hT : chQC p.logN Q + 240 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1)
    (h : SegsHold c M ptr (chLinkG p.logN Q z o (M3.ofParts p bf tb tcl fv fs pck).chBlock 52 ptr).2) :
    (chLinkPh p (M3.ofParts p bf tb tcl fv fs pck) r w pub sig s).1.2 =
      (chLinkG p.logN Q z o (M3.ofParts p bf tb tcl fv fs pck).chBlock 52 ptr).1.map (CClaim.val M) := by
  rw [chLinkPh_run p _ r w pub sig s hn]
  exact (chLinkG_val p _ _ r w pub hPQ hS hT hz ho h).symm

/-! ## The `KS` link -/

/-- `λ`'s lanes (samples `ksLog … ksLog + 4`), `ρ'`'s (the shift sumcheck's answers), the four
scalars'. -/
def ksLamL (p : Params) (Q : Nat) : List Nat := (List.range laneBits).map fun j => Q + 9 * (p.ksLog + j)
def ksRhoL (p : Params) (Q : Nat) : List Nat :=
  (List.range p.ksLog).map fun i => Q + 9 * (p.ksLog + laneBits) + 6 + 15 * i
def ksValL (p : Params) (Q : Nat) : List Nat :=
  (List.range 4).map fun k => Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 3 * k

/-- The `KS` link's claims as cells (`om`: `eq(λ, ·)`, `rho'`, `vals`: the four scalars). -/
def ksLinkC (p : Params) (z o : Nat) (om rho' vals : List Cell) : List CClaim :=
  let L := layout0 p
  let lo := rho'.take p.recRowsLog
  [⟨.main, .sum p.nuMain ((List.range 25).map fun l =>
      (om.getD l default, (ksYPartC p l rho' z o).1, (ksYPartC p l rho' z o).2)), vals.getD 0 default⟩,
    ⟨.main, .sum p.nuMain ((List.range 25).map fun l =>
      (om.getD l default, ⟨p.ksLog + slotLog, L.ks⟩, rho' ++ selC z o l slotLog)), vals.getD 1 default⟩,
    ⟨.crec, .sum p.nuRec ((List.range 17).map fun l =>
      (om.getD l default, ⟨p.recRowsLog, l * 2 ^ p.recRowsLog⟩, lo)), vals.getD 2 default⟩,
    ⟨.main, .sum p.nuMain ((List.range 17).map fun l =>
      (om.getD l default, ⟨p.recRowsLog, L.x + l * 2 ^ p.recRowsLog⟩, lo)), vals.getD 3 default⟩]

/-- **The `KS` link's claims** (phase 7; `P + 40 = 8 Q`). -/
def ksLinkG (p : Params) (Q z o : Nat) : BM (List CClaim) := do
  let pl ← getPtr
  let _ ← loadAt (ksLamL p Q)
  let rho' ← loadAt (ksRhoL p Q)
  let vals ← loadAt (ksValL p Q)
  let eb ← eqTab (fun i => ec (pl.e + i)) (ec z) (ec o) false laneBits
  pure (ksLinkC p z o ((List.range 32).map fun l => ec (eb + l)) rho' vals)

theorem vs_take (M : Mem) (l : List Cell) (n : Nat) : vs M (l.take n) = (vs M l).take n := by
  simp [vs, List.map_take]

theorem ksLinkC_val (p : Params) {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1)
    (om rho' vals : List Cell) (i : KsLinkIn) (hom : vs M om = eqKernel (i.chal.drop p.ksLog))
    (homl : om.length = 32) (hrho : vs M rho' = i.shift.1) (hvals : vs M vals = i.vals)
    (hvl : vals.length = 4) :
    (ksLinkC p z o om rho' vals).map (CClaim.val M) = (ksLink0 p i).2 := by
  have hc : ∀ l < 32, (om.getD l default).val M = (eqKernel (i.chal.drop p.ksLog)).getD l 0 := by
    intro l hl; rw [vs_getD M om (by omega), hom]
  have hv : ∀ k < 4, (vals.getD k default).val M = i.vals.getD k 0 := by
    intro k hk; rw [vs_getD M vals (by omega), hvals]
  simp only [ksLinkC, ksLink0, List.map_cons, List.map_nil, CClaim.val, List.map_map, vs_take, hrho,
    hv 0 (by omega), hv 1 (by omega), hv 2 (by omega), hv 3 (by omega)]
  refine List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_, List.cons_eq_cons.2 ⟨?_,
    List.cons_eq_cons.2 ⟨?_, rfl⟩⟩⟩⟩
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    have e := ksYPartC_val (M := M) p l rho' hz ho
    rw [hrho] at e
    simp only [Function.comp_apply, hc l (by omega)]
    rw [← e]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by omega), vs_append, hrho, selC_vs hz ho]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by omega), vs_take, hrho]
  · congr 2
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, hc l (by omega), vs_take, hrho]

theorem eqKernel_getD_A (pt : List FE) (x : Nat) : (eqKernel pt).getD x 0 = (eqKernelA pt).getD x 0 := by
  rw [← eqKernelA_toList, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- **Q_arith_eq, the `KS` link's claims**: with the reader at `P` (`P + 40 = 8 Q`) the cells are
`ksLink0`'s claims on what `F` reads in phase 7 (any `M3` `m`). -/
theorem ksLinkG_val (p : Params) (m : M3) {z o Q P T : Nat} {sig : ByteArray} {ptr : Ptr}
    (rk : List FE) (pub : Pub) (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T)
    (hT : Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1)
    (h : SegsHold c M ptr (ksLinkG p Q z o ptr).2) :
    (ksLinkG p Q z o ptr).1.map (CClaim.val M) = (ksLink0 p (ksLinkView p m (feAt sig) P rk pub)).2 := by
  simp only [ksLinkG] at h ⊢
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h; obtain ⟨-, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h1, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h2, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h3, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h4, -⟩ := h
  rw [bind_fst_eq (getPtr_out _) (getPtr_adv _)]
  simp only [bind_apply, pure_apply]
  set lamF : List FE := (List.range laneBits).map fun j => feAt sig (P + 40 + 72 * (p.ksLog + j))
    with hlamF
  have hlam : (ksLinkView p m (feAt sig) P rk pub).chal.drop p.ksLog = lamF := by
    simp only [ksLinkView, samplesAt]
    rw [drop_range_map, show p.ksLog + laneBits - p.ksLog = laneBits by omega]
  have hll : lamF.length = laneBits := by simp [hlamF]
  have hL := loadAt_e hS (ksLamL p Q) ptr (fun q hq => by
    simp only [ksLamL, List.mem_map, List.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    simp only [laneBits] at hj hT ⊢; omega) h1
  have hE := eqTab_eq (fun i => ec (ptr.e + i)) (ec z) (ec o) false lamF (by rw [hll]; exact h4) hz
    (fun _ => rfl) ho (fun i hi => by
      rw [hll] at hi
      rw [Cell.val_E, hL i (by simp [ksLamL, hi])]
      simp only [ksLamL, hlamF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
        Option.map_some, Option.getD_some]
      congr 1; omega)
  rw [hll] at hE
  refine ksLinkC_val p hz ho _ _ _ _ ?_ (by simp) ?_ ?_ (by rw [loadAt_out]; simp [ksValL])
  · rw [hlam]
    refine List.ext_getElem (by simp [vs, Build.eqKernel_length, hll, laneBits]) fun x h1 h2 => ?_
    simp only [vs, List.length_map, List.length_range] at h1
    simp only [vs, List.getElem_map, List.getElem_range, Cell.val_E]
    have e := hE x (by simpa [laneBits] using h1)
    simp only [if_false, Bool.false_eq_true] at e
    rw [e, ← eqKernel_getD_A, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksRhoL, List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, rfl⟩ := hq
      simp only [laneBits] at hT ⊢; omega) h2]
    simp only [ksLinkView, scSpec_fst, List.length_replicate, ksRhoL, List.map_map]
    refine List.map_congr_left fun i _ => congrArg (feAt sig) ?_
    simp only [ksP1, roundLen, laneBits]; omega
  · rw [loadAt_vs hS _ _ (fun q hq => by
      simp only [ksValL, List.mem_map, List.mem_range] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      omega) h3]
    simp only [ksLinkView, scalarsAt, ksValL, List.map_map]
    refine List.map_congr_left fun k _ => congrArg (feAt sig) ?_
    simp only [ksP2, ksP1, roundLen, laneBits]; omega

/-- **`F`'s phase-7 claims** (`ksLinkPh`, any `m`) from the reader at `P`. -/
theorem ksLinkPh_claims (p : Params) (m : M3) {z o Q T : Nat} {sig : ByteArray} {ptr : Ptr}
    (rk : List FE) (pub : Pub) (s : RS) (hn : 1 ≤ p.ksLog) (hPQ : pos s + 40 = 8 * Q)
    (hS : Streamed M sig T) (hT : Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ T)
    (hz : M.e z = 0) (ho : M.e o = 1) (hm : m.ksLink = ksLink0 p)
    (h : SegsHold c M ptr (ksLinkG p Q z o ptr).2) :
    (ksLinkPh p m rk pub sig s).1.2 = (ksLinkG p Q z o ptr).1.map (CClaim.val M) := by
  rw [ksLinkPh_run p m rk pub sig s hn, hm]
  exact (ksLinkG_val p m rk pub hPQ hS hT hz ho h).symm

/-! ## Instances: `P20`, `P8` (reader positions from `phaseFirst`, WP-16a's `aLane`) -/

open Lvm.QAsm in
/-- The lanes this family reads at a parameter set lie in the stream (`streamLanes`), the links'
lanes are their phases' first positions, and `KS`'s ring switch ends where `KS`'s link begins. -/
def RCLanes (p : Params) : Prop :=
  5 ≤ aLane p 2 ∧ 5 ≤ aLane p 6 ∧
  gkrEnd (p.logN - 4) (aLane p 2) + 48 ≤ streamLanes p ∧
  gkrEnd (p.ksLog - 4) (aLane p 6) + 48 ≤ streamLanes p ∧
  chQC p.logN (aLane p 3) + 240 ≤ streamLanes p ∧
  aLane p 7 + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ streamLanes p ∧
  phaseByte p .chLink + 40 = 8 * aLane p 3 ∧ phaseByte p .ksLink + 40 = 8 * aLane p 7 ∧
  8 * gkrEnd (p.ksLog - 4) (aLane p 6) - 40 + 72 * ringStages = phaseByte p .ksLink ∧
  8 * gkrEnd (p.logN - 4) (aLane p 2) - 40 + 72 * ringStages = phaseByte p .chLink

theorem rcLanes20 : RCLanes P20 := by
  unfold RCLanes; decide +kernel

theorem rcLanes8 : RCLanes P8 := by
  unfold RCLanes; decide +kernel

/-- **`P20`'s phase-5 claims** from the reader at the phase's first position. -/
theorem chLinkPh_claims20 {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool}
    {z o : Nat} {sig : ByteArray} {ptr : Ptr} (r w : List FE) (pub : Pub) (s : RS)
    (hs : pos s = phaseByte P20 .chLink) (hS : Streamed M sig (streamLanes P20)) (hz : M.e z = 0)
    (ho : M.e o = 1)
    (h : SegsHold c M ptr (chLinkG P20.logN (aLane P20 3) z o
      (M3.ofParts P20 bf tb tcl fv fs pck).chBlock 52 ptr).2) :
    (chLinkPh P20 (M3.ofParts P20 bf tb tcl fv fs pck) r w pub sig s).1.2 =
      (chLinkG P20.logN (aLane P20 3) z o (M3.ofParts P20 bf tb tcl fv fs pck).chBlock 52 ptr).1.map
        (CClaim.val M) :=
  chLinkPh_claims P20 r w pub s (by decide) (by rw [hs]; exact rcLanes20.2.2.2.2.2.2.1) hS
    rcLanes20.2.2.2.2.1 hz ho h

/-- **`P20`'s phase-7 claims** from the reader at the phase's first position. -/
theorem ksLinkPh_claims20 {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool}
    {z o : Nat} {sig : ByteArray} {ptr : Ptr} (rk : List FE) (pub : Pub) (s : RS)
    (hs : pos s = phaseByte P20 .ksLink) (hS : Streamed M sig (streamLanes P20)) (hz : M.e z = 0)
    (ho : M.e o = 1) (h : SegsHold c M ptr (ksLinkG P20 (aLane P20 7) z o ptr).2) :
    (ksLinkPh P20 (M3.ofParts P20 bf tb tcl fv fs pck) rk pub sig s).1.2 =
      (ksLinkG P20 (aLane P20 7) z o ptr).1.map (CClaim.val M) :=
  ksLinkPh_claims P20 _ rk pub s (by decide) (by rw [hs]; exact rcLanes20.2.2.2.2.2.2.2.1) hS
    rcLanes20.2.2.2.2.2.1 hz ho rfl h

/-- **`P20`'s `KS` ring switch** (after `KS`'s GKR at WP-16a's lane `aLane P20 6`): `F`'s `ringAt` at the
GKR's end is the gadget's claim, and the switch ends at the `KS` link's first position. -/
theorem ksRing20 {sig : ByteArray} {z : Nat} {p : Ptr} (instV outV : List FE)
    (hinst : instV.length = P20.ksLog) (ok : Bool) (hS : Streamed M sig (streamLanes P20))
    (hz : M.e z = 0) (h : SegsHold c M p (ringGkr (P20.ksLog - 4) (aLane P20 6) z p).2) :
    RingRel M (vkSpec (feAt sig) P20.ksLog instV outV (8 * aLane P20 6 - 40) ok).1.slicePoint
      (ringAt (feAt sig) (8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40)
        (vkSpec (feAt sig) P20.ksLog instV outV (8 * aLane P20 6 - 40) ok).1.slicePoint
        (vkSpec (feAt sig) P20.ksLog instV outV (8 * aLane P20 6 - 40) ok).1.slices)
      (ringGkr (P20.ksLog - 4) (aLane P20 6) z p).1 ∧
    8 * gkrEnd (P20.ksLog - 4) (aLane P20 6) - 40 + 72 * ringStages = phaseByte P20 .ksLink :=
  ⟨ringGkr_ringAt (by decide) rcLanes20.2.1 instV outV hinst ok hS rcLanes20.2.2.2.1 hz h,
    rcLanes20.2.2.2.2.2.2.2.2.1⟩

/-- **`P20`'s `CH` ring switch** (after `CH`'s GKR at WP-16a's lane `aLane P20 2`). -/
theorem chRing20 {sig : ByteArray} {z : Nat} {p : Ptr} (instV outV : List FE)
    (hinst : instV.length = P20.logN) (ok : Bool) (hS : Streamed M sig (streamLanes P20))
    (hz : M.e z = 0) (h : SegsHold c M p (ringGkr (P20.logN - 4) (aLane P20 2) z p).2) :
    RingRel M (vkSpec (feAt sig) P20.logN instV outV (8 * aLane P20 2 - 40) ok).1.slicePoint
      (ringAt (feAt sig) (8 * gkrEnd (P20.logN - 4) (aLane P20 2) - 40)
        (vkSpec (feAt sig) P20.logN instV outV (8 * aLane P20 2 - 40) ok).1.slicePoint
        (vkSpec (feAt sig) P20.logN instV outV (8 * aLane P20 2 - 40) ok).1.slices)
      (ringGkr (P20.logN - 4) (aLane P20 2) z p).1 ∧
    8 * gkrEnd (P20.logN - 4) (aLane P20 2) - 40 + 72 * ringStages = phaseByte P20 .chLink :=
  ⟨ringGkr_ringAt (by decide) rcLanes20.1 instV outV hinst ok hS rcLanes20.2.2.1 hz h,
    rcLanes20.2.2.2.2.2.2.2.2.2⟩

/-- `chLinkG_val` in `F`'s form `m.chLink (chLinkView …)` (`m = M3.ofParts p …`). -/
theorem chLinkG_val' (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool}
    {z o Q P T : Nat} {sig : ByteArray} {ptr : Ptr} (r w : List FE) (pub : Pub)
    (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T) (hT : chQC p.logN Q + 240 ≤ T) (hz : M.e z = 0)
    (ho : M.e o = 1)
    (h : SegsHold c M ptr (chLinkG p.logN Q z o (M3.ofParts p bf tb tcl fv fs pck).chBlock 52 ptr).2) :
    (chLinkG p.logN Q z o (M3.ofParts p bf tb tcl fv fs pck).chBlock 52 ptr).1.map (CClaim.val M) =
      ((M3.ofParts p bf tb tcl fv fs pck).chLink
        (chLinkView p (M3.ofParts p bf tb tcl fv fs pck) (feAt sig) P r w pub)).2 :=
  chLinkG_val p _ _ r w pub hPQ hS hT hz ho h

/-- `ksLinkG_val` in `F`'s form `m.ksLink (ksLinkView …)` (`m = M3.ofParts p …`). -/
theorem ksLinkG_val' (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool}
    {z o Q P T : Nat} {sig : ByteArray} {ptr : Ptr} (rk : List FE) (pub : Pub)
    (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T)
    (hT : Q + 9 * (p.ksLog + laneBits) + 15 * p.ksLog + 12 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1)
    (h : SegsHold c M ptr (ksLinkG p Q z o ptr).2) :
    (ksLinkG p Q z o ptr).1.map (CClaim.val M) =
      ((M3.ofParts p bf tb tcl fv fs pck).ksLink
        (ksLinkView p (M3.ofParts p bf tb tcl fv fs pck) (feAt sig) P rk pub)).2 :=
  ksLinkG_val p _ rk pub hPQ hS hT hz ho h

end Lvm.Har
