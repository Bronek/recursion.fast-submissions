-- new for lvm (WP-9b): the fixed columns' closed forms are their extensions. Built on WP-10's
-- `LvmLoopMle` (`pieceEval_eq`, `mle_split`, `mle_pow`, `mle_lin`, `mle_congr`) and `LvmSelfEval`
-- (`mle_eq_sum`, `mle_comm`, the proof pattern of `mle_fixF`).
import LvmM3Fid
import LvmM3LoopTab
import LvmSelfEval

/-!
# The fixed columns' closed forms

* `toExt3_mle`: the native extension `Loop.mle` (bit `i` the variable `r_i`) is CompPoly's
  `evalMle` (the first coordinate folding adjacent entries) through `FE.toExt3`;
  `toExt3_mle_fixed`: for a fixed column, at a point of `E`, it is the column's `eval₂Mle`.
* `fixFEval_eq`: the closed form of a piece's `F` column (`fixmul`'s multiplier, the glue matrix
  at the loop index's first two coordinates) is its extension, for every glue height.
* `pieceFixEval_eq`: every closed form of a piece's fixed column is its extension.
* `grpEval_eq`: a group's fixed column (pieces stacked at aligned offsets) has extension
  `Σ_m eq(sel_m, r_{≥h_m})·(piece m's at r_{<h_m})`, its closed form `grpEval`.
* `inArr_eval_eq`: an input array's address column `x ↦ g^(base + stride·x)` has extension
  `g^base · powEval r (g^stride)`.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval Lvm.Loop
open LeanVM.Protocol.EndToEnd.Front (vecOf)

/-! ## The native extension is CompPoly's -/

theorem toExt3_ofK' (c : FK) : FE.toExt3 (FE.ofK c) = algebraMap K E (FK.toBF64 c) := by
  rw [FE.toExt3_ofK]

/-- **The native extension through `FE.toExt3`** is CompPoly's `evalMle` of the mapped table at the
mapped point. -/
theorem toExt3_mle : ∀ (r : List FE) (f : ℕ → FE),
    FE.toExt3 (Loop.mle r f) =
      evalMle (Vector.ofFn fun i : Fin (2 ^ r.length) ↦ FE.toExt3 (f i)) (vecOf r.length (r.map FE.toExt3))
  | [], f => by simp [Loop.mle]
  | r :: rs, f => by
    have hl : Loop.mle (r :: rs) f =
        Loop.mle rs (fun x ↦ (1 - r) * f (2 * x) + r * f (2 * x + 1)) := by
      rw [mle_lin]; rfl
    rw [hl, toExt3_mle rs, evalMle_succ]
    congr 1
    · apply Vector.ext
      intro j hj
      have hh : (vecOf (r :: rs).length ((r :: rs).map FE.toExt3)).head = FE.toExt3 r := by
        simp [vecOf, Vector.head]
      rw [Vector.getElem_ofFn, ← Vector.get_eq_getElem (evalMleLayer _ _) ⟨j, hj⟩, evalMleLayer_get, hh]
      simp only [Vector.get_ofFn, FE.toExt3_add, FE.toExt3_mul, FE.toExt3_sub, FE.toExt3_one]
    · apply Vector.ext
      intro j hj
      simp [vecOf, Vector.tail, Nat.add_comm 1 j, hj]

theorem toExt3_mle_of_length {n : ℕ} (r : List FE) (hr : r.length = n) (f : ℕ → FE) :
    FE.toExt3 (Loop.mle r f) =
      evalMle (Vector.ofFn fun i : Fin (2 ^ n) ↦ FE.toExt3 (f i)) (vecOf n (r.map FE.toExt3)) := by
  subst hr; exact toExt3_mle r f

/-- **A fixed column's extension**: at a point of `E` of the column's height, the native extension
of its cells at the point read in `FE` is the column's `eval₂Mle`. -/
theorem toExt3_mle_fixed {τ : ℕ} (f : ℕ → FK) (z : Vector E τ) :
    FE.toExt3 (Loop.mle (z.toList.map FE.ofExt3) fun x ↦ FE.ofK (f x)) =
      eval₂Mle (fixedColumn τ f).values (algebraMap K E) z := by
  rw [toExt3_mle_of_length _ (by simp : (z.toList.map FE.ofExt3).length = τ)]
  have hz : vecOf τ ((z.toList.map FE.ofExt3).map FE.toExt3) = z := by
    apply Vector.ext
    intro i hi
    simp [vecOf, List.map_map, Function.comp_def, hi]
  rw [hz, eval₂Mle]
  congr 1
  apply Vector.ext
  intro i hi
  simp [fixedColumn, CMlPolynomialEval.map, toExt3_ofK']

/-! ## List folds as sums -/

theorem foldl_add_acc : ∀ (l : List FE) (a : FE), l.foldl (· + ·) a = a + l.sum
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_add_acc l, List.sum_cons]; ring

theorem foldl_add_eq_sum (l : List FE) : l.foldl (· + ·) 0 = l.sum := by
  rw [foldl_add_acc, zero_add]

theorem foldl_mul_acc : ∀ (l : List FE) (a : FE), l.foldl (· * ·) a = a * l.prod
  | [], a => by simp
  | x :: l, a => by rw [List.foldl_cons, foldl_mul_acc l, List.prod_cons]; ring

/-- A sum over an indexed list is a sum over the indices. -/
theorem sum_zipIdxFE {α : Type} [Inhabited α] (F : α → ℕ → FE) :
    ∀ (l : List α) (k : ℕ), ((l.zipIdx k).map fun p ↦ F p.1 p.2).sum =
      ∑ i ∈ Finset.range l.length, F (l.getD i default) (k + i)
  | [], _ => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdxFE F l (k + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show k + 1 + i = k + (i + 1) by omega]

/-! ## Extensions of special tables -/

/-- At a point of zeros the extension is the table's first cell. -/
theorem mle_zeros : ∀ (k : ℕ) (g : ℕ → FE), Loop.mle (List.replicate k 0) g = g 0
  | 0, g => rfl
  | k + 1, g => by
    rw [List.replicate_succ, Loop.mle, mle_zeros k, mle_zeros k]; simp

/-- The extension of the indicator of row `0`, scaled. -/
theorem mle_delta0 : ∀ (zs : List FE) (A : FE),
    Loop.mle zs (fun z ↦ if z = 0 then A else 0) = A * (zs.map (1 - ·)).prod
  | [], A => by simp [Loop.mle]
  | z :: zs, A => by
    rw [Loop.mle]
    have h1 : (fun x : ℕ ↦ if 2 * x = 0 then A else 0) = fun x ↦ if x = 0 then A else 0 := by
      funext x; congr 1; simp
    have h2 : (fun x : ℕ ↦ if 2 * x + 1 = 0 then A else (0 : FE)) = fun _ ↦ 0 := by
      funext x; simp
    rw [h1, h2, mle_delta0 zs, mle_const, List.map_cons, List.prod_cons]; ring

/-- **A column of `2^h` rows on `2^|r|` rows** (zero past `2^h`, truncated at `2^|r|`): the extension
of the `2^h`-row column at `r`'s low `h` coordinates (padded with zeros), times `Π (1 - r_i)` over
the coordinates above `h`. -/
theorem mle_trunc (rx : List FE) (h : ℕ) (u : ℕ → FE) :
    Loop.mle rx (fun y ↦ if y < 2 ^ h then u y else 0) =
      Loop.mle (rx.take h ++ List.replicate (h - rx.length) 0) u *
        ((rx.drop h).map (1 - ·)).foldl (· * ·) 1 := by
  rw [foldl_mul_acc, one_mul]
  by_cases hh : h ≤ rx.length
  · have ht : (rx.take h).length = h := by simp; omega
    rw [show h - rx.length = 0 by omega, List.replicate_zero, List.append_nil]
    conv_lhs => rw [← List.take_append_drop h rx]
    rw [mle_split, ht]
    rw [mle_congr (rx.drop h) (w := fun z ↦ if z = 0 then Loop.mle (rx.take h) u else 0)
      (fun z _ ↦ ?_), mle_delta0]
    by_cases hz : z = 0
    · subst hz
      simp only [Nat.mul_zero, Nat.add_zero, if_true]
      exact mle_congr _ fun x hx ↦ by rw [ht] at hx; simp [hx]
    · rw [if_neg hz]
      refine Eq.trans (mle_congr _ (w := fun _ ↦ (0 : FE)) fun x hx ↦ ?_) (mle_const _ 0)
      have : ¬ x + 2 ^ h * z < 2 ^ h := by
        have : 2 ^ h ≤ 2 ^ h * z := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hz)
        omega
      simp [ht, this]
  · have hd : rx.drop h = [] := List.drop_eq_nil_of_le (by omega)
    rw [List.take_of_length_le (by omega), hd, List.map_nil, List.prod_nil, mul_one, mle_split,
      mle_zeros]
    apply mle_congr
    intro x hx
    have : x < 2 ^ h := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [this]

/-- The `eq` kernel's entries are the `eq` weights. -/
theorem eqKernel'_getD_aux : ∀ (rs out : List FE) (k : ℕ), out.length = 2 ^ k → ∀ c,
    (rs.foldl (fun out r ↦ out.map (· * (1 - r)) ++ out.map (· * r)) out).getD c 0 =
      if c < 2 ^ (k + rs.length) then out.getD (c % 2 ^ k) 0 * Loop.eqW rs (c / 2 ^ k) else 0
  | [], out, k, hl, c => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero, Loop.eqW, mul_one]
    split_ifs with hc
    · rw [Nat.mod_eq_of_lt hc]
    · exact List.getD_eq_default _ _ (by omega)
  | r :: rs, out, k, hl, c => by
    rw [List.foldl_cons, eqKernel'_getD_aux rs _ (k + 1) (by simp [hl, pow_succ]; ring) c,
      List.length_cons, show k + 1 + rs.length = k + (rs.length + 1) by omega]
    split_ifs with hc
    · rw [Loop.eqW, Nat.div_div_eq_div_mul, ← pow_succ]
      have hm : c % 2 ^ (k + 1) = c % 2 ^ k + 2 ^ k * (c / 2 ^ k % 2) := by
        rw [pow_succ]; exact Nat.mod_mul
      have hlt : c % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ k) with h2 | h2
      · rw [hm, h2, Nat.mul_zero, Nat.add_zero, List.getD_append _ _ _ _ (by simp [hl]; omega),
          List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_map,
          List.getD_eq_getElem _ _ (by omega), if_neg (by omega)]
        ring
      · rw [hm, h2, Nat.mul_one, List.getD_append_right _ _ _ _ (by simp [hl]),
          List.length_map, hl, Nat.add_sub_cancel_right,
          List.getD_eq_getElem _ _ (by simp [hl]; omega), List.getElem_map,
          List.getD_eq_getElem _ _ (by omega), if_pos rfl]
        ring
    · rfl

theorem eqKernel'_getD (rc : List FE) (c : ℕ) :
    (eqKernel' rc).getD c 0 = if c < 2 ^ rc.length then Loop.eqW rc c else 0 := by
  rw [eqKernel', eqKernel'_getD_aux rc [1] 0 rfl c]
  simp [Nat.mod_one]

/-- `eqSel` is the `eq` weight. -/
theorem eqSel_aux (s : ℕ) : ∀ (z : List FE) (k : ℕ) (a : FE),
    ((z.zipIdx k).map fun (r, i) ↦ if (s >>> i) % 2 = 1 then r else 1 - r).foldl (· * ·) a =
      a * Loop.eqW z (s >>> k)
  | [], _, a => by simp [Loop.eqW]
  | r :: z, k, a => by
    rw [List.zipIdx_cons, List.map_cons, List.foldl_cons, eqSel_aux s z (k + 1), Loop.eqW,
      Nat.shiftRight_succ]
    ring

theorem eqSel_eq (s : ℕ) (z : List FE) : eqSel s z = Loop.eqW z s := by
  rw [eqSel, eqSel_aux s z 0 1, one_mul, Nat.shiftRight_zero]

/-- **`eq` splits at a power of two.** -/
theorem eqW_append : ∀ (r₁ r₂ : List FE) (x s : ℕ), x < 2 ^ r₁.length →
    Loop.eqW (r₁ ++ r₂) (x + 2 ^ r₁.length * s) = Loop.eqW r₁ x * Loop.eqW r₂ s
  | [], r₂, x, s, hx => by
    have : x = 0 := by simpa using hx
    subst this; simp [Loop.eqW]
  | r :: r₁, r₂, x, s, hx => by
    rw [List.cons_append, Loop.eqW, Loop.eqW, List.length_cons, pow_succ]
    have h1 : (x + 2 ^ r₁.length * 2 * s) % 2 = x % 2 := by
      rw [show 2 ^ r₁.length * 2 * s = 2 * (2 ^ r₁.length * s) by ring, Nat.add_mul_mod_self_left]
    have h2 : (x + 2 ^ r₁.length * 2 * s) / 2 = x / 2 + 2 ^ r₁.length * s := by
      rw [show 2 ^ r₁.length * 2 * s = 2 * (2 ^ r₁.length * s) by ring, Nat.add_mul_div_left _ _
        (by norm_num)]
    rw [h1, h2, eqW_append r₁ r₂ _ _ (by rw [List.length_cons, pow_succ] at hx; omega)]
    ring

/-! ## A piece's `F` column -/

section Pieces

variable (Q : Program)

theorem ofK_zero' : FE.ofK 0 = 0 := rfl

theorem fval_ne_F (p : Piece) {c : FCol} (hc : c ≠ .F) (x : ℕ) : Q.fval p c x = Q.fvalBasic p c x := by
  cases c <;> first | rfl | exact absurd rfl hc

theorem fixMat_getD (j : List ℕ) : Q.fixMat j = Q.fixMat [j.getD 0 0, j.getD 1 0] := by
  simp [Program.fixMat]

theorem unflat_getD0 (D : List ℕ) (n : ℕ) : (unflat D n).getD 0 0 = n % 2 ^ (D.getD 0 0) := by
  rcases D with _ | ⟨d0, ds⟩ <;> simp [unflat, Nat.mod_one]

theorem unflat_getD1 (D : List ℕ) (n : ℕ) :
    (unflat D n).getD 1 0 = n / 2 ^ (D.getD 0 0) % 2 ^ (D.getD 1 0) := by
  rcases D with _ | ⟨d0, _ | ⟨d1, ds⟩⟩ <;> simp [unflat, Nat.mod_one]

theorem getD_add_le_sum (D : List ℕ) : D.getD 0 0 + D.getD 1 0 ≤ D.sum := by
  rcases D with _ | ⟨d0, _ | ⟨d1, ds⟩⟩ <;> simp <;> omega

theorem glue_ne_F {pc : Piece × FCol} (h : pc ∈ Q.glueCols) : pc.2 ≠ .F := by
  simp only [Program.glueCols, List.mem_flatMap, List.mem_map, List.mem_filter] at h
  obtain ⟨_, -, c, ⟨-, hc⟩, rfl⟩ := h
  simpa using hc

/-- The closed form of glue column `pc` on `2^|rx|` rows (`fixFEval`'s term). -/
def glueTerm (rx : List FE) (pc : Piece × FCol) : FE :=
  Q.pieceEval pc.1 pc.2 (rx.take (Q.height pc.1) ++ List.replicate (Q.height pc.1 - rx.length) 0) *
    ((rx.drop (Q.height pc.1)).map (1 - ·)).foldl (· * ·) 1

/-- Glue column `c` (zero past its piece's height) on `2^|rx|` rows has extension `glueTerm`. -/
theorem mle_glue (rx : List FE) (c : ℕ) :
    Loop.mle rx (fun y ↦ FE.ofK (Q.fixMat [c, y])) =
      if c < Q.glueCols.length then glueTerm Q rx (Q.glueCols.getD c default) else 0 := by
  split_ifs with hc
  · have hmem : Q.glueCols.getD c default ∈ Q.glueCols := by
      rw [List.getD_eq_getElem _ _ hc]; exact List.getElem_mem hc
    have hfm : ∀ y, FE.ofK (Q.fixMat [c, y]) =
        if y < 2 ^ Q.height (Q.glueCols.getD c default).1 then
          FE.ofK (Q.fvalBasic (Q.glueCols.getD c default).1 (Q.glueCols.getD c default).2 y) else 0 := by
      intro y
      simp only [Program.fixMat, List.getD_cons_zero, List.getD_cons_succ, List.getElem?_eq_getElem hc,
        List.getD_eq_getElem _ _ hc]
      split_ifs <;> rfl
    simp only [hfm]
    rw [mle_trunc, glueTerm, Q.pieceEval_eq _ _ (glue_ne_F Q hmem) _ (by simp; omega)]
    congr 1
    apply mle_congr
    intro x _
    rw [fval_ne_F Q _ (glue_ne_F Q hmem)]
  · have : ∀ y, FE.ofK (Q.fixMat [c, y]) = 0 := fun y ↦ by
      simp [Program.fixMat, List.getElem?_eq_none (by omega : Q.glueCols.length ≤ c), ofK_zero']
    simp only [this]
    exact mle_const _ 0

/-- **The `F` column's closed form is its extension**, for every glue height. -/
theorem fixFEval_eq (p : Piece) (r : List FE) (hr : r.length = Q.height p) :
    fixFEval Q p r = Loop.mle r (fun x ↦ FE.ofK (Q.fval p .F x)) := by
  have hfx : fixFEval Q p r = ((Q.glueCols.zipIdx).map fun pc ↦
      (eqKernel' (r.take ((Q.blk p.blk).dims.getD 0 0))).getD pc.2 0 *
        glueTerm Q ((r.drop ((Q.blk p.blk).dims.getD 0 0)).take ((Q.blk p.blk).dims.getD 1 0)) pc.1).foldl
          (· + ·) 0 := by
    unfold fixFEval
    apply congrArg (fun l ↦ List.foldl (· + ·) (0 : FE) l)
    apply List.map_congr_left
    rintro ⟨⟨_, _⟩, _⟩ _
    exact mul_assoc _ _ _
  have hS := getD_add_le_sum (Q.blk p.blk).dims
  set dc := (Q.blk p.blk).dims.getD 0 0 with hdc
  set dx := (Q.blk p.blk).dims.getD 1 0 with hdx
  have hlen : dc + dx ≤ r.length := by
    rw [hr]; unfold Program.height Block.lsize; omega
  have hrc : (r.take dc).length = dc := by simp; omega
  have hrx : ((r.drop dc).take dx).length = dx := by simp; omega
  let H : ℕ → ℕ → FE := fun c y ↦ FE.ofK (Q.fixMat [c, y])
  have hF : ∀ x, FE.ofK (Q.fval p .F x) = H (x % 2 ^ dc) (x / 2 ^ dc % 2 ^ dx) := by
    intro x
    show FE.ofK (Q.fixMat (unflat (Q.blk p.blk).dims (x % 2 ^ (Q.blk p.blk).dims.sum))) = _
    rw [fixMat_getD, unflat_getD0, unflat_getD1, ← hdc, ← hdx]
    have e1 : x % 2 ^ (Q.blk p.blk).dims.sum % 2 ^ dc = x % 2 ^ dc :=
      Nat.mod_mod_of_dvd x (pow_dvd_pow 2 (by omega))
    have e2 : x % 2 ^ (Q.blk p.blk).dims.sum / 2 ^ dc % 2 ^ dx = x / 2 ^ dc % 2 ^ dx := by
      rw [show 2 ^ (Q.blk p.blk).dims.sum = 2 ^ dc * 2 ^ ((Q.blk p.blk).dims.sum - dc) by
        rw [← pow_add]; congr 1; omega, Nat.mod_mul_right_div_self]
      exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))
    rw [e1, e2]
  have h1 : ∀ z, Loop.mle (r.take dc) (fun c ↦ FE.ofK (Q.fval p .F (c + 2 ^ (r.take dc).length * z))) =
      Loop.mle (r.take dc) (fun c ↦ H c (z % 2 ^ dx)) := fun z ↦ mle_congr _ fun c hc ↦ by
    rw [hrc] at hc ⊢
    rw [hF, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hc, Nat.zero_add]
  have h2 : ∀ w, Loop.mle ((r.drop dc).take dx) (fun y ↦ (fun z ↦ Loop.mle (r.take dc)
      (fun c ↦ H c (z % 2 ^ dx))) (y + 2 ^ ((r.drop dc).take dx).length * w)) =
      Loop.mle ((r.drop dc).take dx) (fun y ↦ Loop.mle (r.take dc) fun c ↦ H c y) :=
    fun w ↦ mle_congr _ fun y hy ↦ by
      rw [hrx] at hy ⊢
      simp only
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  have hmle : Loop.mle r (fun x ↦ FE.ofK (Q.fval p .F x)) =
      Loop.mle (r.take dc) (fun c ↦ Loop.mle ((r.drop dc).take dx) (fun y ↦ H c y)) := by
    calc Loop.mle r (fun x ↦ FE.ofK (Q.fval p .F x))
        = Loop.mle (r.take dc ++ r.drop dc) (fun x ↦ FE.ofK (Q.fval p .F x)) := by
          rw [List.take_append_drop]
      _ = Loop.mle (r.drop dc) (fun z ↦ Loop.mle (r.take dc) (fun c ↦ H c (z % 2 ^ dx))) := by
          rw [mle_split]; exact congrArg _ (funext h1)
      _ = Loop.mle ((r.drop dc).take dx ++ (r.drop dc).drop dx)
            (fun z ↦ Loop.mle (r.take dc) (fun c ↦ H c (z % 2 ^ dx))) := by
          rw [List.take_append_drop]
      _ = Loop.mle ((r.drop dc).drop dx)
            (fun _ ↦ Loop.mle ((r.drop dc).take dx) (fun y ↦ Loop.mle (r.take dc) fun c ↦ H c y)) := by
          rw [mle_split]; exact congrArg _ (funext h2)
      _ = Loop.mle ((r.drop dc).take dx) (fun y ↦ Loop.mle (r.take dc) fun c ↦ H c y) := mle_const _ _
      _ = Loop.mle (r.take dc) (fun c ↦ Loop.mle ((r.drop dc).take dx) (fun y ↦ H c y)) :=
          mle_comm _ _ _
  rw [hmle, mle_eq_sum, hrc]
  simp only [H, mle_glue]
  rw [hfx, foldl_add_eq_sum, sum_zipIdxFE (fun pc c ↦ (eqKernel' (r.take dc)).getD c 0 *
    glueTerm Q ((r.drop dc).take dx) pc)]
  let f : ℕ → FE := fun c ↦ (eqKernel' (r.take dc)).getD c 0 *
    if c < Q.glueCols.length then glueTerm Q ((r.drop dc).take dx) (Q.glueCols.getD c default) else 0
  have hL : ∑ c ∈ Finset.range (2 ^ dc), eqW (r.take dc) c *
      (if c < Q.glueCols.length then glueTerm Q ((r.drop dc).take dx) (Q.glueCols.getD c default) else 0) =
      ∑ c ∈ Finset.range (max (2 ^ dc) Q.glueCols.length), f c := by
    refine (Finset.sum_congr rfl fun c hc ↦ ?_).trans
      (Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun c _ hc ↦ ?_)
    · simp only [f, eqKernel'_getD, hrc, if_pos (Finset.mem_range.mp hc)]
    · have hc' : ¬ c < 2 ^ dc := by simpa using hc
      simp only [f, eqKernel'_getD, hrc, hc', if_false, zero_mul]
  have hR : ∑ i ∈ Finset.range Q.glueCols.length, (eqKernel' (r.take dc)).getD (0 + i) 0 *
      glueTerm Q ((r.drop dc).take dx) (Q.glueCols.getD i default) =
      ∑ c ∈ Finset.range (max (2 ^ dc) Q.glueCols.length), f c := by
    refine (Finset.sum_congr rfl fun c hc ↦ ?_).trans
      (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun c _ hc ↦ ?_)
    · simp only [f, Nat.zero_add, if_pos (Finset.mem_range.mp hc)]
    · have hc' : ¬ c < Q.glueCols.length := by simpa using hc
      simp only [f, hc', if_false, mul_zero]
  rw [hL, hR]

/-- **Every closed form of a piece's fixed column is its extension.** -/
theorem pieceFixEval_eq (p : Piece) (c : FCol) (r : List FE) (hr : r.length = Q.height p) :
    pieceFixEval Q p c r = Loop.mle r (fun x ↦ FE.ofK (Q.fval p c x)) := by
  cases c with
  | F => exact fixFEval_eq Q p r hr
  | res => exact Q.pieceEval_eq p .res (by decide) r hr
  | arg o => exact Q.pieceEval_eq p (.arg o) (by simp) r hr
  | k => exact Q.pieceEval_eq p .k (by decide) r hr
  | k' => exact Q.pieceEval_eq p .k' (by decide) r hr

/-! ## Groups -/

/-- A group's fixed column at row `y`, member by member (members disjoint, listed once). -/
theorem ofK_grpFix (g : Grp)
    (hdisj : ∀ m ∈ g.mem, ∀ m' ∈ g.mem, ∀ y, Grp.Holds Q m y = true → Grp.Holds Q m' y = true → m = m')
    (c : FCol) (y : ℕ) :
    FE.ofK (grpFix Q g c y) = ∑ m ∈ g.mem.toFinset,
      if Grp.Holds Q m y = true then FE.ofK (Q.fval (Q.pieces.getD m.1 default) c (y - m.2)) else 0 := by
  by_cases h : ∃ m ∈ g.mem, Grp.Holds Q m y = true
  · obtain ⟨m0, hm0, hy⟩ := h
    have hat : g.at Q y = some (m0.1, y - m0.2) := by
      have hsome : (g.mem.find? fun m ↦ Grp.Holds Q m y).isSome := by
        rw [List.find?_isSome]; exact ⟨_, hm0, hy⟩
      obtain ⟨m, hm'⟩ := Option.isSome_iff_exists.mp hsome
      have := hdisj m (List.mem_of_find?_eq_some hm') m0 hm0 y
        (List.find?_some (p := fun m ↦ Grp.Holds Q m y) hm') hy
      subst this
      simp [Grp.at, hm']
    rw [Finset.sum_eq_single m0 (fun m hm hne ↦ ?_) (fun h ↦ absurd (List.mem_toFinset.mpr hm0) h)]
    · rw [if_pos hy]; simp only [grpFix, hat]
    · rw [if_neg]; intro hm'; exact hne (hdisj m (List.mem_toFinset.mp hm) m0 hm0 y hm' hy)
  · have h' : ∀ m ∈ g.mem, Grp.Holds Q m y = false := fun m hm ↦ by
      cases hh : Grp.Holds Q m y
      · rfl
      · exact absurd ⟨m, hm, hh⟩ h
    have hat : g.at Q y = none := by
      simp only [Grp.at, Option.map_eq_none_iff, List.find?_eq_none]
      intro m hm; simp [h' m hm]
    rw [Finset.sum_eq_zero (fun m hm ↦ by rw [h' m (List.mem_toFinset.mp hm)]; rfl)]
    simp [grpFix, hat, ofK_zero']

theorem sum_window (N off H : ℕ) (hle : off + H ≤ N) (F : ℕ → FE) :
    ∑ y ∈ Finset.range N, (if off ≤ y ∧ y < off + H then F y else 0) =
      ∑ x ∈ Finset.range H, F (off + x) := by
  rw [← Finset.sum_filter]
  have : (Finset.range N).filter (fun y ↦ off ≤ y ∧ y < off + H) = Finset.Ico off (off + H) := by
    ext y; simp; omega
  rw [this, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- **A group's fixed column's closed form is its extension**: the members are pieces at aligned
offsets inside the group's rows, pairwise disjoint, listed once. -/
theorem grpEval_eq (g : Grp)
    (hmem : ∀ m ∈ g.mem, ∃ p, Q.pieces[m.1]? = some p ∧ m.2 + 2 ^ Q.height p ≤ 2 ^ g.τ ∧
      2 ^ Q.height p ∣ m.2)
    (hdisj : ∀ m ∈ g.mem, ∀ m' ∈ g.mem, ∀ y, Grp.Holds Q m y = true → Grp.Holds Q m' y = true → m = m')
    (hnd : g.mem.Nodup) (c : FCol) (r : List FE) (hr : r.length = g.τ) :
    grpEval Q g c r = Loop.mle r (fun y ↦ FE.ofK (grpFix Q g c y)) := by
  rw [mle_eq_sum, hr]
  simp only [ofK_grpFix Q g hdisj c, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold grpEval
  rw [foldl_add_eq_sum, ← List.sum_toFinset _ hnd]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  obtain ⟨p, hp, hle, hdvd⟩ := hmem m (List.mem_toFinset.mp hm)
  obtain ⟨n, off⟩ := m
  have hpd : Q.pieces.getD n default = p := by simp [List.getD_eq_getElem?_getD, hp]
  simp only [hpd]
  have hh : Q.height p ≤ r.length := by
    rw [hr]
    have : 2 ^ Q.height p ≤ 2 ^ g.τ := le_trans (Nat.le_add_left _ _) hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hth : (r.take (Q.height p)).length = Q.height p := by simp; omega
  obtain ⟨s, hs⟩ := hdvd
  simp only at hs hle
  have hRHS : ∑ y ∈ Finset.range (2 ^ g.τ), eqW r y *
      (if Grp.Holds Q (n, off) y = true then FE.ofK (Q.fval p c (y - off)) else 0) =
      ∑ x ∈ Finset.range (2 ^ Q.height p),
        eqW (r.drop (Q.height p)) s * (eqW (r.take (Q.height p)) x * FE.ofK (Q.fval p c x)) := by
    have e : ∀ y, eqW r y * (if Grp.Holds Q (n, off) y = true then FE.ofK (Q.fval p c (y - off)) else 0) =
        if off ≤ y ∧ y < off + 2 ^ Q.height p then eqW r y * FE.ofK (Q.fval p c (y - off)) else 0 := by
      intro y
      simp only [Grp.Holds, hpd, Bool.and_eq_true, decide_eq_true_eq]
      split_ifs <;> simp
    simp only [e]
    rw [sum_window _ _ _ hle]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    rw [Nat.add_sub_cancel_left]
    conv_lhs => rw [← List.take_append_drop (Q.height p) r]
    rw [hs, show 2 ^ Q.height p * s + x = x + 2 ^ (r.take (Q.height p)).length * s by rw [hth]; ring,
      eqW_append _ _ _ _ (by rw [hth]; exact Finset.mem_range.mp hx)]
    ring
  rw [hRHS, ← Finset.mul_sum, pieceFixEval_eq Q p c _ hth, mle_eq_sum, hth, eqSel_eq,
    hs, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

/-! ## Input arrays -/

/-- **An input array's address column** `x ↦ g^(base + stride·x)` has extension
`g^base · powEval r (g^stride)`. -/
theorem inArr_eval_eq (a : InArr) (r : List FE) :
    FE.ofK (FK.x ^ a.base) * powEval r (FK.x ^ a.stride) =
      Loop.mle r (fun x ↦ FE.ofK (FK.x ^ (a.base + a.stride * x))) := by
  rw [← mle_pow, ← mle_smul]
  apply mle_congr
  intro x _
  rw [← ofK_mul', pow_add, pow_mul]

end Pieces

/-! ## The lvm tables -/

/-- **The public arrays' evaluators are their values' extensions** (BLUEPRINT A19's `PUB`: V's
evaluation of the public column from π's header; WP-14/INT-2 prove it of the real `PUB`). -/
def PubOk (arrs : List InArr) : Prop :=
  ∀ a ∈ arrs, ∀ f e, a.pub = some (f, e) → ∀ r : List FE, r.length = a.τ →
    e r = Loop.mle r fun x ↦ FE.ofK (f x)

/-- **The lvm tables' closed forms are their fixed columns' extensions**: the groups' members are
pieces at aligned offsets inside the group's rows, pairwise disjoint (`GrpOk`'s `mem`, `disj`),
listed once; the public arrays' evaluators are theirs (`PubOk`); the auxiliary tables' closed
forms are theirs. -/
theorem fixOk_lvmTabs_of (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp)
    (arrs : List InArr) (aux : List Tab)
    (hmem : ∀ g ∈ groups, ∀ m ∈ g.mem, ∃ p, Q.pieces[m.1]? = some p ∧
      m.2 + 2 ^ Q.height p ≤ 2 ^ g.τ ∧ 2 ^ Q.height p ∣ m.2)
    (hdisj : ∀ g ∈ groups, ∀ m ∈ g.mem, ∀ m' ∈ g.mem, ∀ y, Grp.Holds Q m y = true →
      Grp.Holds Q m' y = true → m = m')
    (hnd : ∀ g ∈ groups, g.mem.Nodup) (hpub : PubOk arrs) (haux : FixOk aux) :
    FixOk (lvmTabs Q pl groups arrs aux) := by
  intro t ht f ev hfe r hr
  simp only [lvmTabs, List.mem_append, List.mem_map, List.mem_range] at ht
  rcases ht with (⟨i, hi, rfl⟩ | ⟨a, ha, rfl⟩) | ht
  · have hg : groups.getD i default ∈ groups := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    simp only [grpTab, shapeTab, List.mem_map] at hfe
    obtain ⟨u, -, hu⟩ := hfe
    cases u with
    | fix c =>
      simp only [ColSrc.fix.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      exact grpEval_eq Q _ (hmem _ hg) (hdisj _ hg) (hnd _ hg) c r hr
    | _ => simp at hu
  · simp only [InArr.tab, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hfe
    rcases hfe with hv | hv | hv
    · unfold InArr.vcols at hv
      split at hv
      · rename_i fe hfe'
        obtain ⟨_, -, hv⟩ := List.mem_map.mp hv
        simp only [ColSrc.fix.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        exact hpub a ha _ _ hfe' r hr
      · obtain ⟨_, -, hv⟩ := List.mem_map.mp hv
        cases hv
    · cases hv
    · simp only [ColSrc.fix.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact inArr_eval_eq a r
  · exact haux t ht f ev hfe r hr

end Lvm.M3
