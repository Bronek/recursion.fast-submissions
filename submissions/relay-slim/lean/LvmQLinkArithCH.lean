import LvmQLinkArithRows
import LvmQLinkArithRead

/-!
# QA1 links: the `CH` link circuit (phase 5)

Three straight-line blocks around two sumcheck gadgets (`scGadget`):

* **A** (`chGlueA`, `2n + 166` rows, `n = logN`): load the `n + 9` challenges `ρ, λ, ζ`; `eq(λ, ·)` (8) and
  `eq(ζ, ·)` (64) as `eqKernel`; `Pad43`'s constant bits; `Πρ`; the shift sumcheck's claim
  `C·(1 + Πρ)` (= `chShiftTarget0`, `chGlueA_target`).
* the shift sumcheck (`n` rounds, degree 2);
* **B** (`chGlueB`): the 64 `in` slices, `Σ_p eq(ζ,p)·inS_p`, `(eqEval, shiftEval)(ρ, ρ')`, the second
  sumcheck's claim (= `chSc2Target0`);
* the two-round sumcheck;
* **C** (`chGlueC`): the 64 `Y` slices, `eq(μ, ·)`, `α`, `β`, the two halves of `Σ_q W̃(μ,q)·yS_q`,
  `eqMasked`, and the gated assertion `gate·(f₂ − eqMasked·Σ) = 0` (`chLink0`'s check).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-! ## Helpers -/

/-- A cell as an operand of a template. -/
def cellSrc (c : Cell) : Src := .ext c.addr

theorem iterXv_cell (M : Mem) (o : LoopOut) (jf : Nat) (c : Cell) : iterXv M o jf (cellSrc c) = c.val M := by
  simp only [iterXv, cellSrc, Src.toOpd, Opd.val_abs, Cell.addr, Addr.at, dot_nil, Nat.add_zero]
  rfl

theorem iterXv_fixed (M : Mem) (o : LoopOut) (jf : Nat) (τ : Ty) (b : Nat) :
    iterXv M o jf (.ext ⟨τ, b, []⟩) = M.rd τ b := by
  simp only [iterXv, Src.toOpd, Opd.val_abs, Addr.at]
  rfl

theorem seg_whole (ins : List Ins) : Seg ins 0 ins := by intro i _; simp

/-- A load of the fixed lanes `q, q + 1, q + 2` is the stream's scalar at byte `8q`. -/
theorem load_fixed {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (o : LoopOut) (jf : Nat)
    (V : List FE) {q : Nat} (hq : q + 2 < T) :
    (loadI q []).eval (iterXv M o jf) V = feAt sig (8 * q) := by
  show iterXv M o jf (.ext ⟨.K, q, []⟩) + FE.y * iterXv M o jf (.ext ⟨.K, q + 1, []⟩) +
    FE.y * FE.y * iterXv M o jf (.ext ⟨.K, q + 2, []⟩) = _
  rw [iterXv_fixed, iterXv_fixed, iterXv_fixed]
  exact load_feAt hS hq

/-- The loads of `N` scalars at lanes `q + s·i`. -/
def loadsAt (q s N : Nat) : List Ins := (List.range N).map fun i => loadI (q + s * i) []

theorem loadsAt_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {ins : List Ins} {V : List FE} (hF : Fix (iterXv M o jf) ins V) {n q s N : Nat}
    (hseg : Seg ins n (loadsAt q s N)) (hlen : n + N ≤ ins.length) (hT : q + s * N + 2 < T + s) {i : Nat}
    (hi : i < N) : V.getD (n + i) 0 = feAt sig (8 * (q + s * i)) := by
  have hrow : (loadsAt q s N).getD i default = loadI (q + s * i) [] := by
    simp [loadsAt, List.getD_eq_getElem?_getD, hi]
  rw [fix_seg hF hseg (by simpa [loadsAt] using hlen) (by simpa [loadsAt] using hi)
    (by rw [hrow]; simp [loadI]), hrow]
  apply load_fixed hS
  have : s * i + s ≤ s * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  omega

/-! ## Block A: the shift sumcheck's claim -/

/-- `λ`'s sources (challenges `n … n + 2`). -/
def lamS (n : Nat) : List Src := [.loc n, .loc (n + 1), .loc (n + 2)]
/-- `ζ`'s sources (challenges `n + 3 … n + 8`). -/
def zetaS (n : Nat) : List Src := (List.range 6).map fun i => .loc (n + 3 + i)
/-- `ρ`'s sources (challenges `0 … n − 1`). -/
def rhoS (n : Nat) : List Src := (List.range n).map Src.loc

/-- `eq(λ, k)`'s source. -/
def eLs (n k : Nat) : Src := (eqTabOut (n + 11) [.loc (n + 10)] (lamS n)).getD k default
/-- `eq(ζ, k)`'s source. -/
def eZs (n k : Nat) : Src := (eqTabOut (n + 28) [.loc (n + 10)] (zetaS n)).getD k default

/-- `Pad43`'s constant bits `eq(λ,0)(eq(ζ,0) + eq(ζ,1) + eq(ζ,6)) + eq(λ,4)eq(ζ,8)` at `n + 160 … n + 163`. -/
def padRows (n : Nat) : List Ins :=
  [addI (eZs n 0) (eZs n 1), addI (.loc (n + 160)) (eZs n 6), mulI (eLs n 0) (.loc (n + 161)) (.loc (n + 9)),
    mulI (eLs n 4) (eZs n 8) (.loc (n + 162))]

/-- **Block A**: loads (`0 … n + 8`, lanes `Q + 9i`), zero (`n + 9`), one (`n + 10`), `eq(λ,·)`
(`n + 11`, 17 rows), `eq(ζ,·)` (`n + 28`, 132 rows), `Pad43`'s bits (`n + 160`), `Πρ` (`n + 164`,
`n` rows), `1 + Πρ` (`2n + 164`), the claim (`2n + 165`). -/
def chGlueA (n Q : Nat) : List Ins :=
  loadsAt Q 9 (n + 9) ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n) ++
    (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n) ++
    (padRows n ++
    (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n) ++
    [linI 0 1 (.loc (2 * n + 163)) (.loc (2 * n + 163)), mulI (.loc (n + 163)) (.loc (2 * n + 164)) (.loc (n + 9))])))))

theorem eqTab3_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 3) :
    (eqTabGo z m [o] l).length = 17 := by
  match l, hl with
  | [a, b, c], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem eqTab6_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 6) :
    (eqTabGo z m [o] l).length = 132 := by
  match l, hl with
  | [a, b, c, d, e, f], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem chGlueA_length (n Q : Nat) : (chGlueA n Q).length = 2 * n + 166 := by
  simp only [chGlueA, List.length_append, loadsAt, List.length_map, List.length_range,
    eqTab3_length _ _ _ _ (rfl : (lamS n).length = 3),
    eqTab6_length _ _ _ _ (by simp [zetaS] : (zetaS n).length = 6), padRows, mulChainIns_length, rhoS,
    List.length_cons, List.length_nil]
  omega

theorem seg_split {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) :
    Seg ins n A ∧ Seg ins (n + A.length) B := ⟨seg_append_left h, seg_append_right h⟩

theorem seg_at {ins : List Ins} {n m : Nat} {seg : List Ins} (h : Seg ins n seg) (e : n = m) : Seg ins m seg :=
  e ▸ h

theorem eqKernel_map_getD (l : List FE) {k : Nat} (hk : k < 2 ^ l.length) :
    (eqKernel l).getD k 0 = eqW l k := eqKernel_getD l hk

/-- Block A's values, on any fixed point of its rows over a streamed memory. -/
theorem chGlueA_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {n Q : Nat} {V : List FE} (hF : Fix (iterXv M o jf) (chGlueA n Q) V) (hn : 1 ≤ n)
    (hT : Q + 9 * (n + 9) + 2 < T + 9) :
    (∀ i < n + 9, V.getD i 0 = feAt sig (8 * (Q + 9 * i))) ∧
    V.getD (n + 9) 0 = 0 ∧ V.getD (n + 10) 0 = 1 ∧
    (∀ k < 8, (eLs n k).val (iterXv M o jf) V =
      eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] k) ∧
    (∀ k < 64, (eZs n k).val (iterXv M o jf) V = eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) k) ∧
    V.getD (2 * n + 163) 0 = ((List.range n).map fun i => V.getD i 0).prod ∧
    V.getD (2 * n + 165) 0 =
      (eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] 0 *
        (eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 0 +
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 1 +
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 6) +
        eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] 4 *
          eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) 8) *
      (1 + ((List.range n).map fun i => V.getD i 0).prod) := by
  have hlen := chGlueA_length n Q
  have hs : Seg (chGlueA n Q) 0 (loadsAt Q 9 (n + 9) ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n) ++
    (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n) ++
    (padRows n ++
    (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n) ++
    [linI 0 1 (.loc (2 * n + 163)) (.loc (2 * n + 163)), mulI (.loc (n + 163)) (.loc (2 * n + 164)) (.loc (n + 9))])))))) :=
    seg_whole _
  have lL : (loadsAt Q 9 (n + 9)).length = n + 9 := by simp [loadsAt]
  have lEL : (eqTabGo (.loc (n + 9)) (n + 11) [.loc (n + 10)] (lamS n)).length = 17 := eqTab3_length _ _ _ _ rfl
  have lEZ : (eqTabGo (.loc (n + 9)) (n + 28) [.loc (n + 10)] (zetaS n)).length = 132 :=
    eqTab6_length _ _ _ _ (by simp [zetaS])
  have lM : (mulChainIns (.loc (n + 9)) (n + 164) (.loc (n + 10)) (rhoS n)).length = n := by
    rw [mulChainIns_length]; simp [rhoS]
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sEL, s3⟩ := seg_split s2
  obtain ⟨sEZ, s4⟩ := seg_split s3
  obtain ⟨sP, s5⟩ := seg_split s4
  obtain ⟨sM, sF⟩ := seg_split s5
  replace sZ := seg_at (m := n + 9) sZ (by simp [lL])
  replace sEL := seg_at (m := n + 11) sEL (by simp [lL] <;> omega)
  replace sEZ := seg_at (m := n + 28) sEZ (by simp [lL, lEL] <;> omega)
  replace sP := seg_at (m := n + 160) sP (by simp [lL, lEL, lEZ] <;> omega)
  replace sM := seg_at (m := n + 164) sM (by simp [lL, lEL, lEZ, padRows] <;> omega)
  replace sF := seg_at (m := 2 * n + 164) sF (by simp [lL, lEL, lEZ, lM, padRows] <;> omega)
  -- loads
  have hL : ∀ i < n + 9, V.getD i 0 = feAt sig (8 * (Q + 9 * i)) := by
    intro i hi
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hi
    rwa [Nat.zero_add] at this
  -- zero and one
  have hz : V.getD (n + 9) 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 0) (by first | decide | simp) (by simp [linI])
    rw [Nat.add_zero] at this
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD (n + 10) 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 1) (by first | decide | simp) (by simp [linI])
    rw [show n + 9 + 1 = n + 10 by omega] at this
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc (n + 9)).val (iterXv M o jf) V = 0 := hz
  -- eq tables
  have hEL := eqTab_val hF hzs (lamS n) (n + 11) [.loc (n + 10)] sEL
    (by rw [eqTab3_length _ _ _ _ rfl, hlen]; omega)
  have hEZ := eqTab_val hF hzs (zetaS n) (n + 28) [.loc (n + 10)] sEZ
    (by rw [eqTab6_length _ _ _ _ (by simp [zetaS]), hlen]; omega)
  simp only [List.map_cons, List.map_nil, val_loc, h1] at hEL hEZ
  have hlam : (lamS n).map (Src.val (iterXv M o jf) V) = [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] := by
    simp [lamS]
  have hzeta : (zetaS n).map (Src.val (iterXv M o jf) V) = (List.range 6).map fun i => V.getD (n + 3 + i) 0 := by
    simp [zetaS]
  rw [hlam] at hEL
  rw [hzeta] at hEZ
  have eL : ∀ k < 8, (eLs n k).val (iterXv M o jf) V = eqW [V.getD n 0, V.getD (n + 1) 0, V.getD (n + 2) 0] k := by
    intro k hk
    have hlenout : k < (eqTabOut (n + 11) [.loc (n + 10)] (lamS n)).length := by
      have := congrArg List.length hEL
      rw [List.length_map, foldl_eqStep_length] at this; simp at this; omega
    rw [eLs, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlenout, hEL, ← eqKernel_foldl, eqKernel_getD _ (by simp; omega)]
  have eZ : ∀ k < 64, (eZs n k).val (iterXv M o jf) V = eqW ((List.range 6).map fun i => V.getD (n + 3 + i) 0) k := by
    intro k hk
    have hlenout : k < (eqTabOut (n + 28) [.loc (n + 10)] (zetaS n)).length := by
      have := congrArg List.length hEZ
      rw [List.length_map, foldl_eqStep_length] at this; simp at this; omega
    rw [eZs, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlenout, hEZ, ← eqKernel_foldl, eqKernel_getD _ (by simp; omega)]
  -- Pad43's bits
  have p0 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 0) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p1 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 1) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p2 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 2) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  have p3 := fix_seg hF sP (by rw [hlen]; simp [padRows]; omega) (i := 3) (by simp [padRows]) (by simp [padRows, addI, linI, mulI])
  simp only [padRows, List.getD_cons_zero, List.getD_cons_succ, eval_addI, eval_mulI, val_loc, hz, add_zero,
    Nat.add_zero] at p0 p1 p2 p3
  rw [show n + 160 + 1 = n + 161 by omega] at p1
  rw [show n + 160 + 2 = n + 162 by omega, p1, p0] at p2
  rw [show n + 160 + 3 = n + 163 by omega, p2] at p3
  rw [eL 0 (by omega), eL 4 (by omega), eZ 0 (by omega), eZ 1 (by omega), eZ 6 (by omega),
    eZ 8 (by omega)] at p3
  -- Πρ
  have hM := mulChain_val hF hzs (rhoS n) (n + 164) (.loc (n + 10))
    sM (by rw [hlen]; simp [rhoS]; omega)
  have hsrc : sumSrc (n + 164) (.loc (n + 10)) (rhoS n) = .loc (2 * n + 163) := by
    simp only [sumSrc, rhoS, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range]
    rw [if_neg (by omega), show n + 164 + n - 1 = 2 * n + 163 by omega]
  rw [hsrc, val_loc, val_loc, h1, one_mul] at hM
  have hrho : (rhoS n).map (Src.val (iterXv M o jf) V) = (List.range n).map fun i => V.getD i 0 := by
    simp [rhoS]
  rw [hrho] at hM
  -- the claim
  have f0 := fix_seg hF sF (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 0) (by first | decide | simp) (by simp [linI])
  have f1 := fix_seg hF sF (by rw [hlen]; first | omega | (simp; omega) | simp) (i := 1) (by first | decide | simp) (by simp [mulI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_linI', eval_mulI, val_loc, Nat.add_zero] at f0 f1
  rw [show 2 * n + 164 + 1 = 2 * n + 165 by omega, f0, hz, p3, hM] at f1
  refine ⟨hL, hz, h1, eL, eZ, hM, ?_⟩
  rw [f1, show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]
  ring

/-! ## Block B: the second sumcheck's claim -/

/-- **Block B**: the 64 `in` slices (lanes `QB + 3k`), zero (64), one (65), `Σ_k eq(ζ,k)·inS_k` (66, 64 rows,
at 129), `(eqEval, shiftEval)(ρ, ρ')` (130, `8n` rows), the claim `S·dot + f₁` (`8n + 130`). -/
def chGlueB (QB : Nat) (rho rho' eZ : List Cell) (f1 : Cell) : List Ins :=
  loadsAt QB 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (dotIns 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), .loc k)) ++
    (shiftRecIns (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64) ++
    [mulI (.loc (8 * rho.length + 129)) (.loc 129) (cellSrc f1)])))

theorem chGlueB_val {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {QB : Nat} {rho rho' eZ : List Cell} {f1 : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (chGlueB QB rho rho' eZ f1) V) (hn : 1 ≤ rho.length) (hl : rho.length = rho'.length)
    (hT : QB + 3 * 64 + 2 < T + 3) :
    (∀ k < 64, V.getD k 0 = feAt sig (8 * (QB + 3 * k))) ∧
    V.getD (8 * rho.length + 123) 0 = eqEval (rho.map (Cell.val M)) (rho'.map (Cell.val M)) ∧
    V.getD (8 * rho.length + 130) 0 = shiftEval (rho.map (Cell.val M)) (rho'.map (Cell.val M)) *
      (∑ k ∈ Finset.range 64, (eZ.getD k default).val M * feAt sig (8 * (QB + 3 * k))) + f1.val M := by
  have hs : Seg (chGlueB QB rho rho' eZ f1) 0 (loadsAt QB 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (dotIns 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), .loc k)) ++
    (shiftRecIns (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64) ++
    [mulI (.loc (8 * rho.length + 129)) (.loc 129) (cellSrc f1)])))) := seg_whole _
  have lS := shiftRecIns_length (.loc 64) 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64)
    (by simpa using hl)
  have hlen : (chGlueB QB rho rho' eZ f1).length = 8 * rho.length + 131 := by
    simp only [chGlueB, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length, lS,
      List.length_cons, List.length_nil]; omega
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sD, s3⟩ := seg_split s2
  obtain ⟨sR, sF⟩ := seg_split s3
  replace sZ := seg_at (m := 64) sZ (by simp [loadsAt])
  replace sD := seg_at (m := 66) sD (by simp [loadsAt])
  replace sR := seg_at (m := 130) sR (by simp [loadsAt, dotIns_length])
  replace sF := seg_at (m := 8 * rho.length + 130) sF (by simp [loadsAt, dotIns_length, lS]; omega)
  have hL : ∀ k < 64, V.getD k 0 = feAt sig (8 * (QB + 3 * k)) := by
    intro k hk
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hk
    rwa [Nat.zero_add] at this
  have hz : V.getD 64 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 65 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hD := dot_val hF ((List.range 64).map fun k => (cellSrc (eZ.getD k default), Src.loc k)) 66 (.loc 64) sD
    (by rw [hlen]; simp <;> omega)
  have hDs : dotSrc 66 (.loc 64) ((List.range 64).map fun k => (cellSrc (eZ.getD k default), Src.loc k)) = .loc 129 := by
    simp [dotSrc]
  rw [hDs, val_loc, val_loc, hz, zero_add] at hD
  have hR := shiftRec_val hF (zero := .loc 64) hz 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) (.loc 64)
    (by simpa using hl) h1 hz sR (by rw [hlen]; simp <;> omega)
  have hE : shiftRecE 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 65) = .loc (8 * rho.length + 123) := by
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, rho = c :: cs := ⟨rho.head (by intro h; simp [h] at hn), rho.tail, by simp⟩
    obtain ⟨c', cs', rfl⟩ : ∃ c cs, rho' = c :: cs := ⟨rho'.head (by intro h; simp [h] at hl <;> omega), rho'.tail, by simp⟩
    simp [shiftRecE] <;> omega
  have hSs : shiftRecS 130 (rho.map cellSrc) (rho'.map cellSrc) (.loc 64) = .loc (8 * rho.length + 129) := by
    obtain ⟨c, cs, rfl⟩ : ∃ c cs, rho = c :: cs := ⟨rho.head (by intro h; simp [h] at hn), rho.tail, by simp⟩
    obtain ⟨c', cs', rfl⟩ : ∃ c cs, rho' = c :: cs := ⟨rho'.head (by intro h; simp [h] at hl <;> omega), rho'.tail, by simp⟩
    simp [shiftRecS] <;> omega
  have hmap : ∀ l : List Cell, (l.map cellSrc).map (Src.val (iterXv M o jf) V) = l.map (Cell.val M) := by
    intro l; simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  rw [hE, hSs, val_loc, val_loc, hmap, hmap] at hR
  have f0 := fix_seg hF sF (by rw [hlen]; simp) (i := 0) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, eval_mulI, val_loc, Nat.add_zero] at f0
  have hsum : (List.map (fun ab => ab.1.val (iterXv M o jf) V * ab.2.val (iterXv M o jf) V)
      (List.map (fun k => (cellSrc (eZ.getD k default), Src.loc k)) (List.range 64))).sum =
      ∑ k ∈ Finset.range 64, (eZ.getD k default).val M * feAt sig (8 * (QB + 3 * k)) := by
    rw [List.map_map, list_sum_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    show iterXv M o jf (cellSrc (eZ.getD k default)) * V.getD k 0 = _
    rw [iterXv_cell, hL k hk']
  refine ⟨hL, hR.1, ?_⟩
  rw [f0, hR.2, hD, hsum]
  show _ + iterXv M o jf (cellSrc f1) = _
  rw [iterXv_cell]

/-! ## Block C: the `CH` link's check -/

/-- `eq(μ, m)`'s source in block C. -/
def eMus (mu : List Cell) (m : Nat) : Src := (eqTabOut 66 [.loc 65] (mu.map cellSrc)).getD m default

/-- **Block C**: the 64 `Y` slices (lanes `QC + 3q`), zero (64), one (65), `eq(μ,·)` (66, 8 rows),
`α` (74, at 77), `β` (78, at 81), `S₁ = Σ_{q<56} eq(ζ,q+8)·yS_q` (82, at 137), `S₂` (138, at 145),
`β S₂` (146), `α S₁ + β S₂` (147), `Πρ'` (148, `n` rows), `eqMasked = Πρ·Πρ' + eqEval` (`148 + n`),
the target (`149 + n`), `f₂ + target` (`150 + n`), the gated assertion (`151 + n`). -/
def chGlueC (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) : List Ins :=
  loadsAt QC 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc) ++
    (dotIns 74 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD m default))) ++
    (dotIns 78 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD (m + 1) default))) ++
    (dotIns 82 (.loc 64) ((List.range 56).map fun q => (cellSrc (eZ.getD (q + 8) default), .loc q)) ++
    (dotIns 138 (.loc 64) ((List.range 8).map fun q => (cellSrc (eZ.getD q default), .loc (q + 56))) ++
    ([mulI (.loc 81) (.loc 145) (.loc 64), mulI (.loc 77) (.loc 137) (.loc 146)] ++
    (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc) ++
    [mulI (cellSrc prodRho) (.loc (147 + rho'.length)) (cellSrc eqE),
      mulI (.loc (148 + rho'.length)) (.loc 147) (.loc 64),
      addI (cellSrc f2) (.loc (149 + rho'.length)),
      ⟨.assert0, .K, [.loc (150 + rho'.length), cellSrc gate]⟩]))))))))

theorem eqTab2_length (z : Src) (m : Nat) (o : Src) (l : List Src) (hl : l.length = 2) :
    (eqTabGo z m [o] l).length = 8 := by
  match l, hl with
  | [a, b], _ => simp [eqTabGo, eqLevelIns_length, eqLevelOut]

theorem chGlueC_length (QC : Nat) (mu eL eZ rho' : List Cell) (prodRho eqE f2 gate : Cell) (hm : mu.length = 2) :
    (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate).length = 152 + rho'.length := by
  simp only [chGlueC, List.length_append, loadsAt, List.length_map, List.length_range, dotIns_length,
    mulChainIns_length, eqTab2_length _ _ _ _ (by simpa using hm : (mu.map cellSrc).length = 2),
    List.length_cons, List.length_nil]
  omega

/-- **Block C's assertion**: with gate `1`, `f₂ = (Πρ·Πρ' + eqEval)·(α S₁ + β S₂)`. -/
theorem chGlueC_sound {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {o : LoopOut} {jf : Nat}
    {QC : Nat} {mu eL eZ rho' : List Cell} {prodRho eqE f2 gate : Cell} {V : List FE}
    (hF : Fix (iterXv M o jf) (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate) V) (hm : mu.length = 2)
    (hT : QC + 3 * 64 + 2 < T + 3)
    (hn : 1 ≤ rho'.length)
    (hA : (Src.val (iterXv M o jf) V (cellSrc gate)) * V.getD (150 + rho'.length) 0 = 0) (hg : gate.val M = 1) :
    f2.val M = (prodRho.val M * (rho'.map (Cell.val M)).prod + eqE.val M) *
      ((∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD m default).val M) *
          (∑ q ∈ Finset.range 56, (eZ.getD (q + 8) default).val M * feAt sig (8 * (QC + 3 * q))) +
        (∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD (m + 1) default).val M) *
          (∑ q ∈ Finset.range 8, (eZ.getD q default).val M * feAt sig (8 * (QC + 3 * (q + 56))))) := by
  set n := rho'.length with hndef
  have hlen := chGlueC_length QC mu eL eZ rho' prodRho eqE f2 gate hm
  have hs : Seg (chGlueC QC mu eL eZ rho' prodRho eqE f2 gate) 0
    (loadsAt QC 3 64 ++ ([linI 1 0 (.loc 0) (.loc 0), linI 1 1 (.loc 0) (.loc 0)] ++
    (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc) ++
    (dotIns 74 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD m default))) ++
    (dotIns 78 (.loc 64) ((List.range 4).map fun m => (eMus mu m, cellSrc (eL.getD (m + 1) default))) ++
    (dotIns 82 (.loc 64) ((List.range 56).map fun q => (cellSrc (eZ.getD (q + 8) default), .loc q)) ++
    (dotIns 138 (.loc 64) ((List.range 8).map fun q => (cellSrc (eZ.getD q default), .loc (q + 56))) ++
    ([mulI (.loc 81) (.loc 145) (.loc 64), mulI (.loc 77) (.loc 137) (.loc 146)] ++
    (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc) ++
    [mulI (cellSrc prodRho) (.loc (147 + n)) (cellSrc eqE),
      mulI (.loc (148 + n)) (.loc 147) (.loc 64),
      addI (cellSrc f2) (.loc (149 + n)),
      ⟨.assert0, .K, [.loc (150 + n), cellSrc gate]⟩]))))))))) := seg_whole _
  have lEM : (eqTabGo (.loc 64) 66 [.loc 65] (mu.map cellSrc)).length = 8 := eqTab2_length _ _ _ _ (by simpa using hm)
  have lMC : (mulChainIns (.loc 64) 148 (.loc 65) (rho'.map cellSrc)).length = n := by
    rw [mulChainIns_length]; simp [hndef]
  obtain ⟨sL, s1⟩ := seg_split hs
  obtain ⟨sZ, s2⟩ := seg_split s1
  obtain ⟨sEM, s3⟩ := seg_split s2
  obtain ⟨sDA, s4⟩ := seg_split s3
  obtain ⟨sDB, s5⟩ := seg_split s4
  obtain ⟨sD1, s6⟩ := seg_split s5
  obtain ⟨sD2, s7⟩ := seg_split s6
  obtain ⟨sMM, s8⟩ := seg_split s7
  obtain ⟨sMC, sF⟩ := seg_split s8
  replace sZ := seg_at (m := 64) sZ (by simp [loadsAt])
  replace sEM := seg_at (m := 66) sEM (by simp [loadsAt])
  replace sDA := seg_at (m := 74) sDA (by simp [loadsAt, lEM])
  replace sDB := seg_at (m := 78) sDB (by simp [loadsAt, lEM, dotIns_length])
  replace sD1 := seg_at (m := 82) sD1 (by simp [loadsAt, lEM, dotIns_length])
  replace sD2 := seg_at (m := 138) sD2 (by simp [loadsAt, lEM, dotIns_length])
  replace sMM := seg_at (m := 146) sMM (by simp [loadsAt, lEM, dotIns_length])
  replace sMC := seg_at (m := 148) sMC (by simp [loadsAt, lEM, dotIns_length])
  replace sF := seg_at (m := 148 + n) sF (by simp [loadsAt, lEM, dotIns_length, lMC] <;> omega)
  have hL : ∀ q < 64, V.getD q 0 = feAt sig (8 * (QC + 3 * q)) := by
    intro q hq
    have := loadsAt_val hS hF sL (by rw [hlen]; omega) (by omega) hq
    rwa [Nat.zero_add] at this
  have hz : V.getD 64 0 = 0 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]
    exact CharTwo.add_self_eq_zero _
  have h1 : V.getD 65 0 = 1 := by
    have := fix_seg hF sZ (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [linI])
    rw [this]; simp only [List.getD_cons_succ, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 1 = 1 from rfl, one_mul, CharTwo.add_self_eq_zero, zero_add]
  have hzs : (Src.loc 64).val (iterXv M o jf) V = 0 := hz
  have hmap : ∀ l : List Cell, (l.map cellSrc).map (Src.val (iterXv M o jf) V) = l.map (Cell.val M) := by
    intro l; simp only [List.map_map]; apply List.map_congr_left; intro c _
    show iterXv M o jf (cellSrc c) = _; exact iterXv_cell M o jf c
  have hcell : ∀ c : Cell, (cellSrc c).val (iterXv M o jf) V = c.val M := fun c => iterXv_cell M o jf c
  -- eq(μ, ·)
  have hEM := eqTab_val hF hzs (mu.map cellSrc) 66 [.loc 65] sEM (by rw [lEM, hlen]; omega)
  simp only [List.map_cons, List.map_nil, val_loc, h1, hmap] at hEM
  have eMu : ∀ m < 4, (eMus mu m).val (iterXv M o jf) V = eqW (mu.map (Cell.val M)) m := by
    intro m hm4
    have hlo : m < (eqTabOut 66 [.loc 65] (mu.map cellSrc)).length := by
      have := congrArg List.length hEM
      rw [List.length_map, foldl_eqStep_length] at this; simp [hm] at this; omega
    rw [eMus, ← getD_map_lt (Src.val (iterXv M o jf) V) _ hlo, hEM, ← eqKernel_foldl,
      eqKernel_getD _ (by simp [hm]; omega)]
  -- the dot products
  have hDA := dot_val hF _ 74 (.loc 64) sDA (by rw [hlen]; simp <;> omega)
  have hDB := dot_val hF _ 78 (.loc 64) sDB (by rw [hlen]; simp <;> omega)
  have hD1 := dot_val hF _ 82 (.loc 64) sD1 (by rw [hlen]; simp <;> omega)
  have hD2 := dot_val hF _ 138 (.loc 64) sD2 (by rw [hlen]; simp <;> omega)
  simp only [dotSrc, List.map_eq_nil_iff, List.range_eq_nil, List.length_map, List.length_range,
    OfNat.ofNat_ne_zero, if_false, val_loc, hz, zero_add, List.map_map] at hDA hDB hD1 hD2
  rw [list_sum_range] at hDA hDB hD1 hD2
  simp only [Function.comp_def, hcell, val_loc] at hDA hDB hD1 hD2
  have hA4 : ∑ x ∈ Finset.range 4, (eMus mu x).val (iterXv M o jf) V * (eL.getD x default).val M =
      ∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD m default).val M :=
    Finset.sum_congr rfl fun m hm' => by rw [eMu m (Finset.mem_range.mp hm')]
  have hB4 : ∑ x ∈ Finset.range 4, (eMus mu x).val (iterXv M o jf) V * (eL.getD (x + 1) default).val M =
      ∑ m ∈ Finset.range 4, eqW (mu.map (Cell.val M)) m * (eL.getD (m + 1) default).val M :=
    Finset.sum_congr rfl fun m hm' => by rw [eMu m (Finset.mem_range.mp hm')]
  have h56 : ∑ x ∈ Finset.range 56, (eZ.getD (x + 8) default).val M * V.getD x 0 =
      ∑ q ∈ Finset.range 56, (eZ.getD (q + 8) default).val M * feAt sig (8 * (QC + 3 * q)) :=
    Finset.sum_congr rfl fun q hq => by rw [hL q (by have := Finset.mem_range.mp hq; omega)]
  have h8 : ∑ x ∈ Finset.range 8, (eZ.getD x default).val M * V.getD (x + 56) 0 =
      ∑ q ∈ Finset.range 8, (eZ.getD q default).val M * feAt sig (8 * (QC + 3 * (q + 56))) :=
    Finset.sum_congr rfl fun q hq => by rw [hL (q + 56) (by have := Finset.mem_range.mp hq; omega)]
  rw [hA4] at hDA
  rw [hB4] at hDB
  rw [h56] at hD1
  rw [h8] at hD2
  -- the products and the check
  have m0 := fix_seg hF sMM (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [mulI])
  have m1 := fix_seg hF sMM (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [mulI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, val_loc, hz, add_zero, Nat.add_zero] at m0 m1
  have hMC := mulChain_val hF hzs (rho'.map cellSrc) 148 (.loc 65) sMC (by rw [hlen]; simp <;> omega)
  have hsrc : sumSrc 148 (.loc 65) (rho'.map cellSrc) = .loc (147 + n) := by
    simp only [sumSrc, List.map_eq_nil_iff, List.length_map]
    rw [if_neg (by intro h; rw [h] at hndef; simp at hndef; omega), show 148 + rho'.length - 1 = 147 + n by omega]
  rw [hsrc, val_loc, val_loc, h1, one_mul, hmap] at hMC
  have f0 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 0) (by simp) (by simp [mulI])
  have f1 := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 1) (by simp) (by simp [mulI])
  have f2' := fix_seg hF sF (by rw [hlen]; simp <;> omega) (i := 2) (by simp) (by simp [addI, linI])
  simp only [List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_addI, val_loc, hz, add_zero,
    Nat.add_zero, hcell] at f0 f1 f2'
  rw [show 148 + n + 1 = 149 + n by omega] at f1
  rw [show 148 + n + 2 = 150 + n by omega] at f2'
  rw [hcell, hg, one_mul, f2', f1, f0, hMC, m1, m0, hDA, hDB, hD1, hD2] at hA
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  linear_combination hA

/-! ## Where the tables are -/

theorem getD_range_loc (b k N : Nat) (hk : k < N) :
    ((List.range N).map fun i => Src.loc (b + i)).getD k default = .loc (b + k) := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem eLs_eq (n k : Nat) (hk : k < 8) : eLs n k = .loc (n + 20 + k) := by
  simp only [eLs, lamS, eqTabOut, eqLevelOut, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  rw [show n + 11 + 1 + 2 * (0 + 1) + 1 + 2 * (2 * (0 + 1)) + 1 = n + 20 by omega, getD_range_loc _ _ _ (by omega)]

theorem eZs_eq (n k : Nat) (hk : k < 64) : eZs n k = .loc (n + 96 + k) := by
  have hz : zetaS n = [.loc (n + 3 + 0), .loc (n + 3 + 1), .loc (n + 3 + 2), .loc (n + 3 + 3), .loc (n + 3 + 4),
      .loc (n + 3 + 5)] := rfl
  simp only [eZs, hz, eqTabOut, eqLevelOut, List.length_cons, List.length_nil,
    List.length_map, List.length_range]
  rw [show n + 28 + 1 + 2 * (0 + 1) + 1 + 2 * (2 * (0 + 1)) + 1 + 2 * (2 * (2 * (0 + 1))) + 1 +
      2 * (2 * (2 * (2 * (0 + 1)))) + 1 + 2 * (2 * (2 * (2 * (2 * (0 + 1))))) + 1 = n + 96 by omega,
    getD_range_loc _ _ _ (by omega)]

theorem eMus_eq (c₀ c₁ : Cell) (m : Nat) (hm : m < 4) : eMus [c₀, c₁] m = .loc (70 + m) := by
  simp only [eMus, List.map_cons, List.map_nil, eqTabOut, eqLevelOut, List.length_cons, List.length_nil,
    List.length_map, List.length_range]
  rw [show 66 + 1 + 2 * (0 + 1) + 1 = 70 by omega, getD_range_loc _ _ _ (by omega)]

end Lvm.Q1
