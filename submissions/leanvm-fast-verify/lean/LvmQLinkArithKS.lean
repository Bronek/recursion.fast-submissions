import LvmQLinkArithCHSound

/-!
# QA1 links: the `KS` link circuit (phase 7) and its soundness against `F`

The shift sumcheck from a zero claim (`ksShiftTarget = 0` in `M3.ofParts` (ex `M3.v0`)), then block E (`ksGlueE`,
`39n + 15` rows, `n = ksLog`): the `n` challenges `ρ`, the four scalars `Y_ω, in_ω, M_ω, X_ω`,
`contShift` as `pre(B − 1) + pre(K + 31) + pre(K)` (three `preRecIns`, `K = 2^r + 399`,
`contShift_eq`), `eqEval(ρ, ρ')` (`n` `lin` + `n` products), and the gated assertion
`gate·(f − contShift·Y − eqEval·(in + (1 + x_r)M + x_r X)) = 0` (`ksLink0`'s check).
**`ksLink_sound`**: if the assertion holds (gate `1`), `ksLink0`'s check on what `F` reads in phase 7
(`ksLinkView`) is `true`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- `pre(H)`'s source after a `preRecIns` at `a` over `n ≥ 1` coordinates. -/
def preP (a n : Nat) : Src := .loc (a + 12 * (n - 1) + 8)

/-- **Block E** (positions in the doc above). -/
def ksGlueE (n QR QV H1 H2 H3 : Nat) (rho' : List Cell) (xr f gate : Cell) : List Ins :=
  let z : Src := .loc (n + 4)
  let base : Src × Src × Src := (z, z, .loc (n + 5))
  let rS : List Src := (List.range n).map Src.loc
  let r'S : List Src := rho'.map cellSrc
  let g := 39 * n + 8
  loadsAt QR 9 n ++ (loadsAt QV 3 4 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (preRecIns z (n + 6) rS r'S H1 base ++ (preRecIns z (13 * n + 6) rS r'S H2 base ++
    (preRecIns z (25 * n + 6) rS r'S H3 base ++
    ([addI (preP (n + 6) n) (preP (13 * n + 6) n), addI (.loc (37 * n + 6)) (preP (25 * n + 6) n)] ++
    (((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)) ++
    (mulChainIns z (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i)) ++
    [linI 0 1 (cellSrc xr) (cellSrc xr), mulI (.loc g) (.loc (n + 2)) (.loc (n + 1)),
      mulI (cellSrc xr) (.loc (n + 3)) (.loc (g + 1)), mulI (.loc (39 * n + 7)) (.loc (g + 2)) z,
      mulI (.loc (37 * n + 7)) (.loc n) (.loc (g + 3)), addI (cellSrc f) (.loc (g + 4)),
      ⟨.assert0, .K, [.loc (g + 5), cellSrc gate]⟩]))))))))

theorem ksGlueE_length (n QR QV H1 H2 H3 : Nat) (rho' : List Cell) (xr f gate : Cell) (hl : rho'.length = n) :
    (ksGlueE n QR QV H1 H2 H3 rho' xr f gate).length = 39 * n + 15 := by
  simp only [ksGlueE, List.length_append, loadsAt, List.length_map, List.length_range, mulChainIns_length,
    List.length_cons, List.length_nil]
  rw [preRecIns_length _ _ _ _ _ _ (by simp [hl]), preRecIns_length _ _ _ _ _ _ (by simp [hl]),
    preRecIns_length _ _ _ _ _ _ (by simp [hl])]
  simp; omega

theorem preRecOut_fst (a : Nat) (xs ys : List Src) (base : Src × Src × Src) (hn : 1 ≤ xs.length)
    (hl : xs.length = ys.length) : (preRecOut a xs ys base).1 = preP a xs.length := by
  match xs, ys, hn, hl with
  | x0 :: x, y0 :: y, _, _ => simp [preRecOut, preP]

theorem getD_rangeMap0 (g : Nat → FE) {n i : Nat} (hi : i < n) : ((List.range n).map g).getD i 0 = g i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem getD_mapCell (M : Mem) (l : List Cell) {i : Nat} (hi : i < l.length) :
    (l.map (Cell.val M)).getD i 0 = (l.getD i default).val M := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- **Block E's assertion**: with gate `1`, `f = (Σ pre)·Y + eqEval·(in + (1 + x_r)M + x_r X)`. -/
theorem ksGlueE_sound {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {n QR QV H1 H2 H3 : Nat} {rho' : List Cell} {xr f gate : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (ksGlueE n QR QV H1 H2 H3 rho' xr f gate) V) (hn : 1 ≤ n) (hl : rho'.length = n)
    (hH : H1 < 2 ^ n ∧ H2 < 2 ^ n ∧ H3 < 2 ^ n)
    (hTR : QR + 9 * n + 2 < T + 9) (hTV : QV + 3 * 4 + 2 < T + 3)
    (hA : (Src.val (iterXv M o jf) V (cellSrc gate)) * V.getD (39 * n + 13) 0 = 0) (hg : gate.val M = 1) :
    f.val M = (preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H1 +
        preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H2 +
        preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) H3) *
        feAt sig (8 * QV) +
      eqEval ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) *
        (feAt sig (8 * (QV + 3)) + (1 + xr.val M) * feAt sig (8 * (QV + 6)) + xr.val M * feAt sig (8 * (QV + 9))) := by
  have hlen := ksGlueE_length n QR QV H1 H2 H3 rho' xr f gate hl
  set rS : List Src := (List.range n).map Src.loc with hrS
  set r'S : List Src := rho'.map cellSrc with hr'S
  set base : Src × Src × Src := (.loc (n + 4), .loc (n + 4), .loc (n + 5)) with hbase
  have hs : Seg (ksGlueE n QR QV H1 H2 H3 rho' xr f gate) 0
    (loadsAt QR 9 n ++ (loadsAt QV 3 4 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (preRecIns (.loc (n + 4)) (n + 6) rS r'S H1 base ++ (preRecIns (.loc (n + 4)) (13 * n + 6) rS r'S H2 base ++
    (preRecIns (.loc (n + 4)) (25 * n + 6) rS r'S H3 base ++
    ([addI (preP (n + 6) n) (preP (13 * n + 6) n), addI (.loc (37 * n + 6)) (preP (25 * n + 6) n)] ++
    (((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)) ++
    (mulChainIns (.loc (n + 4)) (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i)) ++
    [linI 0 1 (cellSrc xr) (cellSrc xr), mulI (.loc (39 * n + 8)) (.loc (n + 2)) (.loc (n + 1)),
      mulI (cellSrc xr) (.loc (n + 3)) (.loc (39 * n + 8 + 1)), mulI (.loc (39 * n + 7)) (.loc (39 * n + 8 + 2)) (.loc (n + 4)),
      mulI (.loc (37 * n + 7)) (.loc n) (.loc (39 * n + 8 + 3)), addI (cellSrc f) (.loc (39 * n + 8 + 4)),
      ⟨.assert0, .K, [.loc (39 * n + 8 + 5), cellSrc gate]⟩]))))))))) := seg_whole _
  have lP : ∀ a H, (preRecIns (.loc (n + 4)) a rS r'S H base).length = 12 * n := by
    intro a H; rw [preRecIns_length _ _ _ _ _ _ (by simp [hrS, hr'S, hl])]; simp [hrS]
  have lM : (mulChainIns (.loc (n + 4)) (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => .loc (37 * n + 8 + i))).length = n := by
    rw [mulChainIns_length]; simp
  obtain ⟨sL1, s1⟩ := seg_split hs
  obtain ⟨sL2, s2⟩ := seg_split s1
  obtain ⟨sZ, s3⟩ := seg_split s2
  obtain ⟨sP1, s4⟩ := seg_split s3
  obtain ⟨sP2, s5⟩ := seg_split s4
  obtain ⟨sP3, s6⟩ := seg_split s5
  obtain ⟨sAD, s7⟩ := seg_split s6
  obtain ⟨sAR, s8⟩ := seg_split s7
  obtain ⟨sMC, sF⟩ := seg_split s8
  replace sL2 := seg_at (m := n) sL2 (by simp [loadsAt])
  replace sZ := seg_at (m := n + 4) sZ (by simp [loadsAt])
  replace sP1 := seg_at (m := n + 6) sP1 (by simp [loadsAt])
  replace sP2 := seg_at (m := 13 * n + 6) sP2 (by simp [loadsAt, lP] <;> omega)
  replace sP3 := seg_at (m := 25 * n + 6) sP3 (by simp [loadsAt, lP] <;> omega)
  replace sAD := seg_at (m := 37 * n + 6) sAD (by simp [loadsAt, lP] <;> omega)
  replace sAR := seg_at (m := 37 * n + 8) sAR (by simp [loadsAt, lP] <;> omega)
  replace sMC := seg_at (m := 38 * n + 8) sMC (by simp [loadsAt, lP] <;> omega)
  replace sF := seg_at (m := 39 * n + 8) sF (by simp [loadsAt, lP, lM] <;> omega)
  have hR : ∀ i < n, V.getD i 0 = feAt sig (8 * (QR + 9 * i)) := by
    intro i hi
    have := loadsAt_val hS hF sL1 (by rw [hlen]; omega) (by omega) hi
    rwa [Nat.zero_add] at this
  have hK : ∀ k < 4, V.getD (n + k) 0 = feAt sig (8 * (QV + 3 * k)) := fun k hk =>
    loadsAt_val hS hF sL2 (by rw [hlen]; omega) (by omega) hk
  have hz : V.getD (n + 4) 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
    rw [Nat.add_zero] at this
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD (n + 5) 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [linI])
    rw [show n + 4 + 1 = n + 5 by omega] at this
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc (n + 4)).val (iterXv M o jf) V = 0 := hz
  have hrv : rS.map (Src.val (iterXv M o jf) V) = (List.range n).map fun i => feAt sig (8 * (QR + 9 * i)) := by
    rw [hrS, List.map_map]; apply List.map_congr_left; intro i hi
    exact hR i (List.mem_range.mp hi)
  have hr'v : r'S.map (Src.val (iterXv M o jf) V) = rho'.map (Cell.val M) := by
    rw [hr'S, List.map_map]; apply List.map_congr_left; intro c _
    exact iterXv_cell M o jf c
  have hlS : rS.length = r'S.length := by simp [hrS, hr'S, hl]
  have hnS : rS.length = n := by simp [hrS]
  have pre : ∀ a H, H < 2 ^ n → Seg (ksGlueE n QR QV H1 H2 H3 rho' xr f gate) a (preRecIns (.loc (n + 4)) a rS r'S H base) →
      a + 12 * n ≤ 39 * n + 15 →
      (preP a n).val (iterXv M o jf) V = preSum ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i)))
        (rho'.map (Cell.val M)) H := by
    intro a H hH sP hle
    have := preRec_val hF hzs a rS r'S H base hlS (by rw [hnS]; exact hH) hz hz h1 sP (by rw [hlen, hnS]; omega)
    rw [preCF_eq _ _ _ (by simp [hrv, hr'v, hl]), hrv, hr'v] at this
    have e := congrArg Prod.fst this
    simp only at e
    rw [show preP a n = (preRecOut a rS r'S base).1 by rw [preRecOut_fst _ _ _ _ (by omega) hlS, hnS], e]
  have p1 := pre (n + 6) H1 hH.1 sP1 (by omega)
  have p2 := pre (13 * n + 6) H2 hH.2.1 sP2 (by omega)
  have p3 := pre (25 * n + 6) H3 hH.2.2 sP3 (by omega)
  have a0 := fix_seg hF sAD (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [addI, linI])
  have a1 := fix_seg hF sAD (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_addI, val_loc, Nat.add_zero] at a0 a1
  rw [p1, p2] at a0
  rw [show 37 * n + 6 + 1 = 37 * n + 7 by omega, a0, p3] at a1
  -- eqEval
  have hAR : ∀ i < n, V.getD (37 * n + 8 + i) 0 = 1 + feAt sig (8 * (QR + 9 * i)) + (rho'.getD i default).val M := by
    intro i hi
    have hrow : ((List.range n).map fun i => linI 1 1 (.loc i) (r'S.getD i default)).getD i default =
        linI 1 1 (.loc i) (r'S.getD i default) := by simp [List.getD_eq_getElem?_getD, hi]
    rw [fix_seg hF sAR (by rw [hlen]; simp <;> omega) (by simpa using hi) (by rw [hrow]; simp [linI]), hrow,
      eval_linI', val_loc, hR i hi]
    have : (r'S.getD i default).val (iterXv M o jf) V = (rho'.getD i default).val M := by
      rw [hr'S, List.getD_eq_getElem _ _ (by simp [hl, hi]), List.getElem_map, List.getD_eq_getElem _ _ (by simp [hl, hi])]
      exact iterXv_cell M o jf _
    rw [this, show FE.ofK 1 = 1 from rfl, one_mul]; ring
  have hMC := mulChain_val hF hzs ((List.range n).map fun i => Src.loc (37 * n + 8 + i)) (38 * n + 8) (.loc (n + 5)) sMC
    (by rw [hlen]; simp <;> omega)
  have hsrc : sumSrc (38 * n + 8) (.loc (n + 5)) ((List.range n).map fun i => Src.loc (37 * n + 8 + i)) = .loc (39 * n + 7) := by
    simp only [sumSrc, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range]
    rw [if_neg (by omega), show 38 * n + 8 + n - 1 = 39 * n + 7 by omega]
  rw [hsrc, val_loc, val_loc, h1, one_mul, List.map_map] at hMC
  have hE : V.getD (39 * n + 7) 0 = eqEval ((List.range n).map fun i => feAt sig (8 * (QR + 9 * i))) (rho'.map (Cell.val M)) := by
    rw [hMC, eqEval_range _ _ (by simp [hl]), list_prod_range]
    simp only [List.length_map, List.length_range]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [Function.comp_def, val_loc]
    rw [hAR i hi', getD_rangeMap0 _ hi', getD_mapCell _ _ (by rw [hl]; exact hi')]
  -- the final rows
  have f0 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
  have f1 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [mulI])
  have f2 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 2) (by simp) (by simp [mulI])
  have f3 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 3) (by simp) (by simp [mulI])
  have f4 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 4) (by simp) (by simp [mulI])
  have f5 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 5) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_linI', eval_mulI, eval_addI, val_loc, Nat.add_zero,
    iterXv_cell] at f0 f1 f2 f3 f4 f5
  have hcell : ∀ c : Cell, (cellSrc c).val (iterXv M o jf) V = c.val M := fun c => iterXv_cell M o jf c
  simp only [hcell] at f0 f1 f2 f3 f4 f5 hA
  rw [show 39 * n + 13 = 39 * n + 8 + 5 by omega] at hA
  have k0 : V.getD n 0 = feAt sig (8 * QV) := by have := hK 0 (by omega); simpa using this
  have k1 : V.getD (n + 1) 0 = feAt sig (8 * (QV + 3)) := by have := hK 1 (by omega); simpa using this
  have k2 : V.getD (n + 2) 0 = feAt sig (8 * (QV + 6)) := by have := hK 2 (by omega); simpa using this
  have k3 : V.getD (n + 3) 0 = feAt sig (8 * (QV + 9)) := by have := hK 3 (by omega); simpa using this
  rw [hg, one_mul, f5, f4, f3, f2, f1, f0, a1, hE, hz, k0, k1, k2, k3] at hA
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl] at hA
  linear_combination hA

/-! ## The gadget and its soundness -/

/-- The `KS` shift sumcheck's first message lane (`n = ksLog`). -/
def ksQ1 (n Q : Nat) : Nat := Q + 9 * (n + laneBits)
/-- The four scalars' first lane. -/
def ksQV (n Q : Nat) : Nat := ksQ1 n Q + 15 * n

/-- **The `KS` link gadget** (phase 7's arithmetic): a zero claim, the shift sumcheck, block E. -/
def ksLinkGadget (p : Params) (D Q : Nat) (gate : Cell) : BM Unit := do
  let oD ← loop [] (tplOf [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)])
  let sh ← scGadget D 2 (ksQ1 p.ksLog Q) .plain (oD.cell 0 0)
  let _ ← loop [] (tplOf (ksGlueE p.ksLog Q (ksQV p.ksLog Q) (spongeBlocks p - 1) (2 ^ p.recRowsLog + 399 + 31)
    (2 ^ p.recRowsLog + 399) (rho'C sh p.ksLog) (sh.cell 2 p.recRowsLog) (sh.cell 5 (p.ksLog - 1)) gate))
  pure ()

/-- **The `KS` link circuit is sound for `F`'s phase-7 check.** -/
theorem ksLink_sound (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {tfv : Pub → List FE → List FE}
    {tfs : Pub → List (List FE × List FE) → List FE} {tpc : Pub → List (List FE × List FE) → Bool}
    (D : Nat) {c : Ctx} {M : Mem} {ptr : Ptr} {sig : ByteArray} {T P Q : Nat}
    (rk : List FE) (pub : Pub) (gate : Cell)
    (hn : 1 ≤ p.ksLog) (hr : p.recRowsLog < p.ksLog) (hD : p.ksLog ≤ 2 ^ D) (hPQ : P + 40 = 8 * Q)
    (hB : 1 ≤ spongeBlocks p) (hB2 : spongeBlocks p ≤ 2 ^ p.ksLog) (hK : 2 ^ p.recRowsLog + 431 ≤ 2 ^ p.ksLog)
    (hokE : ∀ sh : LoopOut, SLok (ksGlueE p.ksLog Q (ksQV p.ksLog Q) (spongeBlocks p - 1)
      (2 ^ p.recRowsLog + 399 + 31) (2 ^ p.recRowsLog + 399) (rho'C sh p.ksLog) (sh.cell 2 p.recRowsLog)
      (sh.cell 5 (p.ksLog - 1)) gate) = true)
    (hS : Streamed M sig T) (hT : ksQV p.ksLog Q + 3 * 4 + 3 ≤ T) (hg : gate.val M = 1)
    (h : SegsHold c M ptr (ksLinkGadget p D Q gate ptr).2)
    (hA : SegsAssert M ptr (ksLinkGadget p D Q gate ptr).2) :
    (ksLink0 p (ksLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P rk pub)).1 = true := by
  set n := p.ksLog with hndef
  simp only [ksLinkGadget] at h hA
  rw [hold_bind] at h; obtain ⟨hhD, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhS, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hhE, -⟩ := h
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨-, hA⟩ := hA
  rw [assert_bind] at hA; obtain ⟨haE, -⟩ := hA
  -- the zero claim
  generalize hoD : (loop [] (tplOf [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)]) ptr).1 = oD at hhS hhE haE
  have hFD : Fix (iterXv M oD 0) [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)]
      (iterV M oD 1 0) := by
    rw [← hoD]; exact fix_of_loop rfl hhD (by simp)
  have hz : (oD.cell 0 0).val M = 0 := by
    rw [cell_iterV (len := 1) oD (by omega),
      fix_at hFD (n := 0) (i := linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)) (by simp) rfl (by simp [linI]),
      eval_linI']
    show iterXv M oD 0 (.ext ⟨.K, Q, []⟩) + FE.ofK 1 * iterXv M oD 0 (.ext ⟨.K, Q, []⟩) + FE.ofK 0 = 0
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero, CharTwo.add_self_eq_zero]
  -- the shift sumcheck
  have hq1 : 8 * ksQ1 n Q - 40 = ksP1 p P := by simp only [ksQ1, ksP1, laneBits, ← hndef]; omega
  have hSC := sc_spec_plain (R := n) (by omega) (scTpl_ok_2 _) hD (by simp [ksQ1]; omega) hS
    (by simp [ksQV, ksQ1, roundLanes, laneBits] at hT ⊢; omega) hhS
  set pS := ptr.adv (loop [] (tplOf [linI 1 0 (.ext ⟨.K, Q, []⟩) (.ext ⟨.K, Q, []⟩)]) ptr).2 with hpS
  generalize hsh : (scGadget D 2 (ksQ1 n Q) .plain (oD.cell 0 0) pS).1 = sh at hSC hhE haE
  rw [hq1, hz] at hSC
  set shiftF := scSpec (feAt sig) 3 (ksP1 p P) 0 (List.replicate n none) with hshiftF
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
  have Sx : (sh.cell 2 p.recRowsLog).val M = shiftF.1.getD p.recRowsLog 0 := (hSC _ hr).1
  -- block E
  have hokE' := hokE sh
  have hFE := fix_of_loop hokE' hhE (jf := 0) (by simp)
  have hlenE := ksGlueE_length n Q (ksQV n Q) (spongeBlocks p - 1) (2 ^ p.recRowsLog + 399 + 31)
    (2 ^ p.recRowsLog + 399) (rho'C sh n) (sh.cell 2 p.recRowsLog) (sh.cell 5 (n - 1)) gate (by simp [rho'C])
  have hlast : (ksGlueE n Q (ksQV n Q) (spongeBlocks p - 1) (2 ^ p.recRowsLog + 399 + 31) (2 ^ p.recRowsLog + 399)
      (rho'C sh n) (sh.cell 2 p.recRowsLog) (sh.cell 5 (n - 1)) gate).getD (39 * n + 14) default =
      ⟨.assert0, .K, [.loc (39 * n + 8 + 5), cellSrc gate]⟩ := by
    rw [show 39 * n + 14 = (ksGlueE n Q (ksQV n Q) (spongeBlocks p - 1) (2 ^ p.recRowsLog + 399 + 31)
      (2 ^ p.recRowsLog + 399) (rho'C sh n) (sh.cell 2 p.recRowsLog) (sh.cell 5 (n - 1)) gate).length - 1 by omega,
      List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?]
    simp [ksGlueE, List.getLast?_append, List.getLast?_cons]
  have hAs := assert_of_loop hokE' haE (jf := 0) (by simp) (t := 39 * n + 14) (by rw [hlenE]; omega)
    (by rw [hlast])
  rw [hlast] at hAs
  simp only [List.getD_cons_zero, List.getD_cons_succ, val_loc] at hAs
  rw [show 39 * n + 8 + 5 = 39 * n + 13 by omega] at hAs
  have E := ksGlueE_sound hS hFE hn (by simp [rho'C])
    ⟨by omega, by omega, by omega⟩ (by simp only [ksQV, ksQ1] at hT; omega) (by omega) hAs hg
  rw [S1, S2, Sx] at E
  -- F's view
  set f : Nat → FE := fun i => feAt sig (P + 40 + 72 * i) with hf
  have hrhoF : (samplesAt (feAt sig) P (n + laneBits)).take n = (List.range n).map fun i => feAt sig (8 * (Q + 9 * i)) := by
    rw [samplesAt, take_range_map _ (by omega)]
    apply List.map_congr_left; intro i _; congr 1; omega
  set valsF := scalarsAt (feAt sig) (ksP2 p P + 40) 4 with hvalsF
  have hv : ∀ k < 4, feAt sig (8 * (ksQV n Q + 3 * k)) = valsF.getD k 0 := by
    intro k hk
    rw [hvalsF, scalarsAt, List.getD_eq_getElem?_getD]
    simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
    congr 1
    simp only [ksQV, ksQ1, ksP2, ksP1, roundLen, laneBits, ← hndef]; omega
  have v0 := hv 0 (by omega); have v1 := hv 1 (by omega); have v2 := hv 2 (by omega); have v3 := hv 3 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at v0 v1 v2 v3
  rw [show ksQV n Q + 3 * 2 = ksQV n Q + 6 by omega] at v2
  rw [show ksQV n Q + 3 * 3 = ksQV n Q + 9 by omega] at v3
  rw [v0, v1, v2, v3] at E
  have hok : (ksLink0 p (ksLinkView p (M3.ofParts p bf tb tcl tfv tfs tpc) (feAt sig) P rk pub)).1 =
      (shiftF.2 == contShift p ((samplesAt (feAt sig) P (n + laneBits)).take n) shiftF.1 * valsF.getD 0 0 +
        eqEval ((samplesAt (feAt sig) P (n + laneBits)).take n) shiftF.1 *
          (valsF.getD 1 0 + (1 + shiftF.1.getD p.recRowsLog 0) * valsF.getD 2 0 +
            shiftF.1.getD p.recRowsLog 0 * valsF.getD 3 0)) := rfl
  rw [hok, lnk_fe_beq, contShift_eq p _ _ (by simp [samplesAt]; omega) hSlen hB hB2 hK, hrhoF, ← E]

end Lvm.Q1
