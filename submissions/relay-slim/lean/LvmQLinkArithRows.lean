import LvmQLinkArith

/-!
# QA1 links: row combinators for the link circuits

Template combinators (`Ins` lists at an absolute position, QA1's `Fix` semantics, `LvmQSumcheckCore`) and
their values on any fixed point:

* `eqTabGo`: `eqKernel` itself, one level per coordinate (a `lin` for `1 + r`, then `2^k` rows
  `old·(1 + r)` and `2^k` rows `old·r`); **`eqTab_val`**: the last level's values are
  `rs.foldl eqStep olds` (so `eqKernel` of the point when `olds = [1]`);
* `mulChainIns` (`s·c₀·c₁…`), `dotIns` (`s + Σ aᵢbᵢ`), with `mulChain_val`, `dot_val`;
* `shiftRecIns`: `(eqEval, shiftEval)` from the last coordinate down (`shiftEval_cons`), 8 rows
  per coordinate; **`shiftRec_val`**;
* `preRecIns`: `preCF` for a static bound, 12 rows per coordinate; **`preRec_val`**.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-! ## Generic helpers -/

theorem fix_seg {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {n : Nat}
    {seg : List Ins} (hseg : Seg ins n seg) (hlen : n + seg.length ≤ ins.length) {i : Nat}
    (hi : i < seg.length) (hw : (seg.getD i default).op ≠ .assert0) :
    V.getD (n + i) 0 = (seg.getD i default).eval xv V :=
  fix_at hF (by omega) (hseg i hi) hw

theorem seg_cons_tail {ins : List Ins} {n : Nat} {a : Ins} {seg : List Ins} (h : Seg ins n (a :: seg)) :
    Seg ins (n + 1) seg := seg_sub h [a] seg rfl

theorem seg_append_left {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) : Seg ins n A := by
  intro i hi
  rw [h i (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
    ← List.getD_eq_getElem?_getD]

theorem seg_append_right {ins : List Ins} {n : Nat} {A B : List Ins} (h : Seg ins n (A ++ B)) :
    Seg ins (n + A.length) B := seg_sub h A B rfl

theorem getD_range_map {α : Type} [Inhabited α] (f : Nat → α) {k i : Nat} (hi : i < k) :
    ((List.range k).map f).getD i default = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem list_ext_getD (l l' : List FE) (h : l.length = l'.length)
    (h' : ∀ i < l.length, l.getD i 0 = l'.getD i 0) : l = l' := by
  apply List.ext_getElem h
  intro i h1 h2
  have := h' i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem getD_map_lt (f : Src → FE) (l : List Src) {i : Nat} (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i default) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

@[simp] theorem val_loc (xv : Src → FE) (V : List FE) (k : Nat) : (Src.loc k).val xv V = V.getD k 0 := rfl

theorem eval_linI' (xv : Src → FE) (V : List FE) (k k' : FK) (a b : Src) :
    (linI k k' a b).eval xv V = a.val xv V + FE.ofK k * b.val xv V + FE.ofK k' := rfl

/-! ## `eqKernel` -/

/-- One level's rows at `n`: `1 + r`, then `old_i·(1 + r)`, then `old_i·r`. -/
def eqLevelIns (zero : Src) (n : Nat) (olds : List Src) (r : Src) : List Ins :=
  linI 0 1 r r :: (List.range (2 * olds.length)).map fun i =>
    if i < olds.length then mulI (olds.getD i default) (.loc n) zero
    else mulI (olds.getD (i - olds.length) default) r zero

/-- The level's results. -/
def eqLevelOut (n m : Nat) : List Src := (List.range (2 * m)).map fun i => .loc (n + 1 + i)

/-- **The `eq` table of a point**, from the table `olds` (`[1]` for `eqKernel`). -/
def eqTabGo (zero : Src) : Nat → List Src → List Src → List Ins
  | _, _, [] => []
  | n, olds, r :: rs => eqLevelIns zero n olds r ++ eqTabGo zero (n + 1 + 2 * olds.length) (eqLevelOut n olds.length) rs

/-- Where the table's values are. -/
def eqTabOut : Nat → List Src → List Src → List Src
  | _, olds, [] => olds
  | n, olds, _ :: rs => eqTabOut (n + 1 + 2 * olds.length) (eqLevelOut n olds.length) rs

theorem eqLevelIns_length (zero : Src) (n : Nat) (olds : List Src) (r : Src) :
    (eqLevelIns zero n olds r).length = 1 + 2 * olds.length := by
  simp [eqLevelIns]; omega

theorem eqLevel_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) {n : Nat} {olds : List Src} {r : Src} (hseg : Seg ins n (eqLevelIns zero n olds r))
    (hlen : n + 1 + 2 * olds.length ≤ ins.length) :
    (eqLevelOut n olds.length).map (Src.val xv V) = eqStep (olds.map (Src.val xv V)) (r.val xv V) := by
  have hL := eqLevelIns_length zero n olds r
  have h0 : V.getD n 0 = 1 + r.val xv V := by
    have := fix_seg hF hseg (by omega) (i := 0) (by omega) (by simp [eqLevelIns, linI])
    rw [Nat.add_zero] at this
    rw [this]
    simp only [eqLevelIns, List.getD_cons_zero, eval_linI']
    rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]; ring
  apply list_ext_getD
  · simp [eqLevelOut, eqStep_length]
  · intro i hi
    have hi' : i < 2 * olds.length := by simpa [eqLevelOut] using hi
    have hrow : (eqLevelIns zero n olds r).getD (i + 1) default =
        if i < olds.length then mulI (olds.getD i default) (.loc n) zero
        else mulI (olds.getD (i - olds.length) default) r zero := by
      simp only [eqLevelIns, List.getD_cons_succ]
      exact getD_range_map _ hi'
    have hv := fix_seg hF hseg (by omega) (i := i + 1) (by omega) (by rw [hrow]; split <;> simp [mulI])
    rw [eqStep_getD _ _ (by simpa using hi'), List.length_map,
      getD_map_lt _ _ (by simpa [eqLevelOut] using hi)]
    simp only [eqLevelOut]
    rw [getD_range_map _ hi']
    show V.getD (n + 1 + i) 0 = _
    rw [show n + 1 + i = n + (i + 1) by omega, hv, hrow]
    split
    · rename_i hlt
      rw [eval_mulI, hz, add_zero, getD_map_lt _ _ hlt]
      show _ * V.getD n 0 = _
      rw [h0]
    · rename_i hlt
      rw [eval_mulI, hz, add_zero, getD_map_lt _ _ (by omega)]

theorem eqTab_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) : ∀ (rs : List Src) (n : Nat) (olds : List Src),
    Seg ins n (eqTabGo zero n olds rs) → n + (eqTabGo zero n olds rs).length ≤ ins.length →
    (eqTabOut n olds rs).map (Src.val xv V) = (rs.map (Src.val xv V)).foldl eqStep (olds.map (Src.val xv V))
  | [], n, olds, _, _ => rfl
  | r :: rs, n, olds, hseg, hlen => by
    have hL := eqLevelIns_length zero n olds r
    simp only [eqTabGo, List.length_append] at hseg hlen
    have h1 := eqLevel_val hF hz (seg_append_left hseg) (by omega)
    have h2 := seg_append_right hseg
    rw [hL, show n + (1 + 2 * olds.length) = n + 1 + 2 * olds.length by omega] at h2
    have ih := eqTab_val hF hz rs (n + 1 + 2 * olds.length) (eqLevelOut n olds.length) h2 (by omega)
    simp only [eqTabOut, List.map_cons, List.foldl_cons]
    rw [ih, h1]

/-! ## Chains -/

/-- `s·c₀·c₁·…`, one `muladd` per factor (`zero` the addend). -/
def mulChainIns (zero : Src) : Nat → Src → List Src → List Ins
  | _, _, [] => []
  | n, s, c :: cs => mulI s c zero :: mulChainIns zero (n + 1) (.loc n) cs

theorem mulChainIns_length (zero : Src) : ∀ (n : Nat) (s : Src) (cs : List Src),
    (mulChainIns zero n s cs).length = cs.length
  | _, _, [] => rfl
  | n, s, c :: cs => by simp [mulChainIns, mulChainIns_length zero (n + 1) (.loc n) cs]

theorem mulChain_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) : ∀ (cs : List Src) (n : Nat) (s : Src), Seg ins n (mulChainIns zero n s cs) →
    n + cs.length ≤ ins.length → (sumSrc n s cs).val xv V = s.val xv V * (cs.map (Src.val xv V)).prod
  | [], n, s, _, _ => by simp [sumSrc]
  | c :: cs, n, s, hseg, hlen => by
    have h0 : V.getD n 0 = s.val xv V * c.val xv V := by
      have := fix_seg hF hseg (by rw [mulChainIns_length]; simpa using hlen) (i := 0) (by simp [mulChainIns])
        (by simp [mulChainIns, mulI])
      rw [Nat.add_zero] at this
      rw [this]
      simp [mulChainIns, eval_mulI, hz]
    have ih := mulChain_val hF hz cs (n + 1) (.loc n) (seg_cons_tail hseg) (by simp at hlen; omega)
    have hs : sumSrc n s (c :: cs) = sumSrc (n + 1) (.loc n) cs := by
      cases cs with
      | nil => simp [sumSrc]
      | cons _ _ => simp [sumSrc]; omega
    rw [hs, ih]
    show V.getD n 0 * _ = _
    rw [h0, List.map_cons, List.prod_cons, mul_assoc]

/-- `s + a₀b₀ + a₁b₁ + …`, one `muladd` per pair. -/
def dotIns : Nat → Src → List (Src × Src) → List Ins
  | _, _, [] => []
  | n, s, (a, b) :: ps => mulI a b s :: dotIns (n + 1) (.loc n) ps

/-- Where the dot product is. -/
def dotSrc (n : Nat) (s : Src) (ps : List (Src × Src)) : Src := if ps = [] then s else .loc (n + ps.length - 1)

theorem dotIns_length : ∀ (n : Nat) (s : Src) (ps : List (Src × Src)), (dotIns n s ps).length = ps.length
  | _, _, [] => rfl
  | n, s, (a, b) :: ps => by simp [dotIns, dotIns_length (n + 1) (.loc n) ps]

theorem dot_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) :
    ∀ (ps : List (Src × Src)) (n : Nat) (s : Src), Seg ins n (dotIns n s ps) → n + ps.length ≤ ins.length →
    (dotSrc n s ps).val xv V = s.val xv V + (ps.map fun ab => ab.1.val xv V * ab.2.val xv V).sum
  | [], n, s, _, _ => by simp [dotSrc]
  | (a, b) :: ps, n, s, hseg, hlen => by
    have h0 : V.getD n 0 = a.val xv V * b.val xv V + s.val xv V := by
      have := fix_seg hF hseg (by rw [dotIns_length]; simpa using hlen) (i := 0) (by simp [dotIns])
        (by simp [dotIns, mulI])
      rw [Nat.add_zero] at this
      rw [this]
      simp [dotIns, eval_mulI]
    have ih := dot_val hF ps (n + 1) (.loc n) (seg_cons_tail hseg) (by simp at hlen; omega)
    have hs : dotSrc n s ((a, b) :: ps) = dotSrc (n + 1) (.loc n) ps := by
      cases ps with
      | nil => simp [dotSrc]
      | cons _ _ => simp [dotSrc]; omega
    rw [hs, ih]
    show V.getD n 0 + _ = _
    rw [h0, List.map_cons, List.sum_cons]
    ring

/-! ## The shift kernel, from the last coordinate down -/

/-- The 8 rows of one coordinate at `m`, from the tail's `eqEval` (`Et`) and `shiftEval` (`St`). -/
def shiftLevel (zero : Src) (m : Nat) (x0 y0 Et St : Src) : List Ins :=
  [linI 1 1 x0 y0, mulI (.loc m) Et zero, linI 0 1 x0 x0, mulI (.loc (m + 2)) y0 zero,
    linI 0 1 y0 y0, mulI x0 (.loc (m + 4)) zero, mulI (.loc (m + 5)) St zero,
    mulI (.loc (m + 3)) Et (.loc (m + 6))]

/-- `eqEval`'s source after the coordinates `xs`, `ys` (`E0` before any). -/
def shiftRecE (n : Nat) : List Src → List Src → Src → Src
  | _ :: x, _ :: _, _ => .loc (n + 8 * x.length + 1)
  | _, _, E0 => E0

/-- `shiftEval`'s source. -/
def shiftRecS (n : Nat) : List Src → List Src → Src → Src
  | _ :: x, _ :: _, _ => .loc (n + 8 * x.length + 7)
  | _, _, S0 => S0

/-- **`(eqEval, shiftEval)` of two points**, the last coordinate first, 8 rows per coordinate. -/
def shiftRecIns (zero : Src) (n : Nat) : List Src → List Src → Src → Src → List Ins
  | x0 :: x, y0 :: y, E0, S0 => shiftRecIns zero n x y E0 S0 ++
      shiftLevel zero (n + 8 * x.length) x0 y0 (shiftRecE n x y E0) (shiftRecS n x y S0)
  | _, _, _, _ => []

theorem shiftRecIns_length (zero : Src) (n : Nat) : ∀ (xs ys : List Src) (E0 S0 : Src),
    xs.length = ys.length → (shiftRecIns zero n xs ys E0 S0).length = 8 * xs.length
  | [], [], _, _, _ => rfl
  | x0 :: x, y0 :: y, E0, S0, h => by
    simp only [shiftRecIns, List.length_append, shiftLevel, List.length_cons, List.length_nil]
    rw [shiftRecIns_length zero n x y E0 S0 (by simpa using h)]; ring
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem shiftRec_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) (n : Nat) : ∀ (xs ys : List Src) (E0 S0 : Src), xs.length = ys.length →
    E0.val xv V = 1 → S0.val xv V = 0 →
    Seg ins n (shiftRecIns zero n xs ys E0 S0) → n + 8 * xs.length ≤ ins.length →
    (shiftRecE n xs ys E0).val xv V = eqEval (xs.map (Src.val xv V)) (ys.map (Src.val xv V)) ∧
    (shiftRecS n xs ys S0).val xv V = shiftEval (xs.map (Src.val xv V)) (ys.map (Src.val xv V))
  | [], [], E0, S0, _, hE, hS, _, _ => by simp [shiftRecE, shiftRecS, hE, hS, eqEval_nil, shiftEval_nil]
  | x0 :: x, y0 :: y, E0, S0, h, hE, hS, hseg, hlen => by
    have hl : x.length = y.length := by simpa using h
    have hT := shiftRecIns_length zero n x y E0 S0 hl
    simp only [shiftRecIns] at hseg
    have ih := shiftRec_val hF hz n x y E0 S0 hl hE hS (seg_append_left hseg) (by simp at hlen; omega)
    have hs := seg_append_right hseg
    rw [hT] at hs
    set m := n + 8 * x.length with hm
    have hlen' : m + (shiftLevel zero m x0 y0 (shiftRecE n x y E0) (shiftRecS n x y S0)).length ≤ ins.length := by
      simp [shiftLevel]; simp at hlen; omega
    have v : ∀ i, i < 8 → V.getD (m + i) 0 =
        ((shiftLevel zero m x0 y0 (shiftRecE n x y E0) (shiftRecS n x y S0)).getD i default).eval xv V := by
      intro i hi
      exact fix_seg hF hs hlen' (by simp [shiftLevel]; omega) (by
        interval_cases i <;> simp [shiftLevel, linI, mulI])
    have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
    have v3 := v 3 (by omega); have v4 := v 4 (by omega); have v5 := v 5 (by omega)
    have v6 := v 6 (by omega); have v7 := v 7 (by omega)
    simp only [shiftLevel, List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_linI', Nat.add_zero] at v0 v1 v2 v3 v4 v5 v6 v7
    simp only [val_loc] at v1 v3 v5 v6 v7
    simp only [ih.1, ih.2, hz, add_zero] at v1 v3 v5 v6 v7
    simp only [shiftRecE, shiftRecS, List.map_cons, val_loc]
    rw [show n + 8 * x.length + 1 = m + 1 by omega, show n + 8 * x.length + 7 = m + 7 by omega,
      eqEval_cons, shiftEval_cons _ _ _ _ (by simpa using hl), v1, v7, v6, v5, v3, v0, v2, v4]
    rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]
    constructor <;> ring
  | [], _ :: _, _, _, h, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _, _ => by simp at h

/-! ## The interval shift sum `pre(H)`, from the last coordinate down -/

/-- The 12 rows of one coordinate at `m` (bound bit `h`), from the tail's `P`, `E`, `Pt`. -/
def preLevel (zero : Src) (m : Nat) (h : Bool) (x0 y0 P E Pt : Src) : List Ins :=
  [linI 0 1 y0 y0, linI 0 1 x0 x0,
    mulI (.loc m) x0 zero, mulI y0 (.loc (m + 1)) zero, mulI (.loc m) (.loc (m + 1)) zero, mulI y0 x0 zero,
    addI E (if h then Pt else zero),
    mulI (.loc (m + 3)) P zero, mulI (.loc (m + 2)) (.loc (m + 6)) (.loc (m + 7)),
    mulI (.loc (m + 5)) E zero, mulI (.loc (m + 4)) (.loc (m + 6)) (.loc (m + 9)),
    mulI (if h then .loc (m + 5) else .loc (m + 4)) Pt zero]

/-- The sources of `(pre, E, Pt)` after the coordinates `xs`, `ys` (`base` before any). -/
def preRecOut (n : Nat) : List Src → List Src → Src × Src × Src → Src × Src × Src
  | _ :: x, _ :: _, _ => (.loc (n + 12 * x.length + 8), .loc (n + 12 * x.length + 10), .loc (n + 12 * x.length + 11))
  | _, _, base => base

/-- **`preCF xs ys H`**, the last coordinate first, 12 rows per coordinate. -/
def preRecIns (zero : Src) (n : Nat) : List Src → List Src → Nat → Src × Src × Src → List Ins
  | x0 :: x, y0 :: y, H, base => preRecIns zero n x y (H / 2) base ++
      preLevel zero (n + 12 * x.length) (H % 2 = 1) x0 y0 (preRecOut n x y base).1 (preRecOut n x y base).2.1
        (preRecOut n x y base).2.2
  | _, _, _, _ => []

theorem preRecIns_length (zero : Src) (n : Nat) : ∀ (xs ys : List Src) (H : Nat) (base : Src × Src × Src),
    xs.length = ys.length → (preRecIns zero n xs ys H base).length = 12 * xs.length
  | [], [], _, _, _ => rfl
  | x0 :: x, y0 :: y, H, base, h => by
    simp only [preRecIns, List.length_append, preLevel, List.length_cons, List.length_nil]
    rw [preRecIns_length zero n x y (H / 2) base (by simpa using h)]; ring
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem preRec_val {xv : Src → FE} {ins : List Ins} {V : List FE} (hF : Fix xv ins V) {zero : Src}
    (hz : zero.val xv V = 0) (n : Nat) : ∀ (xs ys : List Src) (H : Nat) (base : Src × Src × Src),
    xs.length = ys.length → H < 2 ^ xs.length →
    base.1.val xv V = 0 → base.2.1.val xv V = 0 → base.2.2.val xv V = 1 →
    Seg ins n (preRecIns zero n xs ys H base) → n + 12 * xs.length ≤ ins.length →
    ((preRecOut n xs ys base).1.val xv V, (preRecOut n xs ys base).2.1.val xv V,
      (preRecOut n xs ys base).2.2.val xv V) = preCF (xs.map (Src.val xv V)) (ys.map (Src.val xv V)) H
  | [], [], H, base, _, hH, h1, h2, h3, _, _ => by
    simp only [List.length_nil, pow_zero] at hH
    have : H = 0 := by omega
    subst this
    simp [preRecOut, preCF, h1, h2, h3]
  | x0 :: x, y0 :: y, H, base, h, hH, h1, h2, h3, hseg, hlen => by
    have hl : x.length = y.length := by simpa using h
    have hT := preRecIns_length zero n x y (H / 2) base hl
    simp only [preRecIns] at hseg
    have ih := preRec_val hF hz n x y (H / 2) base hl
      (by simp only [List.length_cons, pow_succ] at hH; omega) h1 h2 h3 (seg_append_left hseg)
      (by simp at hlen; omega)
    have hs := seg_append_right hseg
    rw [hT] at hs
    set m := n + 12 * x.length with hm
    set L := preLevel zero m (H % 2 = 1) x0 y0 (preRecOut n x y base).1 (preRecOut n x y base).2.1
        (preRecOut n x y base).2.2 with hL
    have hlen' : m + L.length ≤ ins.length := by
      simp [hL, preLevel]; simp at hlen; omega
    have v : ∀ i, i < 12 → V.getD (m + i) 0 = (L.getD i default).eval xv V := by
      intro i hi
      exact fix_seg hF hs hlen' (by simp [hL, preLevel]; omega) (by
        interval_cases i <;> simp [hL, preLevel, linI, mulI, addI] <;> split <;> simp [mulI])
    have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
    have v3 := v 3 (by omega); have v4 := v 4 (by omega); have v5 := v 5 (by omega)
    have v6 := v 6 (by omega); have v7 := v 7 (by omega); have v8 := v 8 (by omega)
    have v9 := v 9 (by omega); have v10 := v 10 (by omega); have v11 := v 11 (by omega)
    simp only [hL, preLevel, List.getD_cons_zero, List.getD_cons_succ, eval_mulI, eval_linI', eval_addI,
      Nat.add_zero, val_loc, hz, add_zero] at v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
    rw [show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl] at v0 v1
    have hpre : preCF ((x0 :: x).map (Src.val xv V)) ((y0 :: y).map (Src.val xv V)) H =
        preStep (x0.val xv V) (y0.val xv V) (H % 2 = 1) (preCF (x.map (Src.val xv V)) (y.map (Src.val xv V)) (H / 2)) := rfl
    rw [hpre, ← ih]
    rw [show preRecOut n (x0 :: x) (y0 :: y) base = (Src.loc (m + 8), Src.loc (m + 10), Src.loc (m + 11))
      from rfl]
    simp only [val_loc]
    unfold preStep
    by_cases hb : H % 2 = 1
    · have hd : decide (H % 2 = 1) = true := by simp [hb]
      simp only [hd, eq_self_iff_true, if_true, ite_true] at v6 v11 ⊢
      simp only [val_loc] at v11
      rw [v8, v10, v11, v7, v9, v6, v2, v3, v4, v5, v0, v1]
      simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by first | trivial | ring⟩
    · have hd : decide (H % 2 = 1) = false := by simp [hb]
      simp only [hd, Bool.false_eq_true, ite_false, hz, add_zero] at v6 v11 ⊢
      simp only [val_loc] at v11
      rw [v8, v10, v11, v7, v9, v6, v2, v3, v4, v5, v0, v1]
      simp only [Prod.mk.injEq]; refine ⟨by ring, by ring, by first | trivial | ring⟩
  | [], _ :: _, _, _, h, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _, _, _, _ => by simp at h

end Lvm.Q1
