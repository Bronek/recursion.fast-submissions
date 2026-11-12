-- new for lvm (AC-S, BLUEPRINT §12.2): `Φ` as a multilinear extension. Built on WP-10's `Loop.mle`
-- rules (`mle_split`, `mle_congr`, `mle_const`, `mle_eq_sum`), WP-9b's `toExt3_mle_fixed` and
-- `FixOk`, QL's `eqKernel_getD` (`LvmQLinkArith`) and AC-V's `fixColsR`/`PhiC` (`LvmDecide*`).
import LvmAccSpec
import LvmDecide
import LvmDecideM3Real
import LvmM3FidFix
import LvmQLinkArith

/-!
# `Φ` is a multilinear polynomial in `D = τ* + dk` variables

BLUEPRINT §12.2: `Φ(x, k) = F_k(x mod 2^{τ_k})` for `k < nFix`, `0` otherwise, on `{0,1}^D`
(`x` the low `τ*` bits). Its extension is `Φ̃(p, κ) = Σ_k eq(κ, k)·F̃_k(p.take τ_k)`, which is how
AC-V's native `PhiC` computes it (one sweep of the closed forms, then a dot product with
`eqKernel κ`).

* `PhiF cs τs pt`: that evaluator over any column list (`PhiC P (M3.real P tabs) pub = PhiF
  (fixColsR …) P.tableRounds`, `phiC_real`); `phiCells`: `Φ`'s cells;
* **`phiF_eq_mle`**: when every closed form is its cells' extension and `nFix ≤ 2^dk`, `PhiF` is
  `Loop.mle` of `Φ`'s cells; **`phiE_eq_eval₂Mle`**: over `E` it is `eval₂Mle` of `Φ`'s fixed
  column (CompPoly);
* **`phiC_eq_eval₂Mle`** (BLUEPRINT §12.6 "`PhiC = eval₂Mle Φ`"): the native `PhiC` of the real
  instance, from WP-9b's `FixOk` of the sumcheck tables;
* **`lineDeg_phiE`**: `Φ̃ ∘ line` has degree at most `D` (`lineDeg_mle`).
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval Finset
open Lvm.Loop (mle eqW)
open Lvm.M3 (FixCol fixColsR fixValsR sumcheckTabs Tab ColSrc FixOk fixedColumn)
open LeanVM.Protocol.EndToEnd.Front (vecOf)
open LeanVM.Protocol.KeccakGkr (eqAt eqAt_cons eqKernel_length eqKernel_getD)

/-! ## Sums of lists -/

theorem foldl_add_sum (l : List FE) (a : FE) : l.foldl (· + ·) a = a + l.sum := Lvm.M3.foldl_add_acc l a

/-- `dot` of a long list with a short one: the sum over the short one. -/
theorem dot_eq_sum_fe : ∀ (l r : List FE), r.length ≤ l.length →
    Lvm.dot l r = ∑ j ∈ range r.length, l.getD j 0 * r.getD j 0
  | _, [], _ => by simp [Lvm.dot]
  | [], _ :: _, h => by simp at h
  | x :: l, y :: r, h => by
    have ih := dot_eq_sum_fe l r (by simpa using h)
    simp only [Lvm.dot, List.zipWith_cons_cons, List.foldl_cons, zero_add, foldl_add_sum] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- **`dot (eqKernel κ) v`** is the `eq(κ, ·)`-weighted sum of `v`. -/
theorem dot_eqKernel_fe (κ v : List FE) (hv : v.length ≤ 2 ^ κ.length) :
    Lvm.dot (Lvm.eqKernel κ) v = ∑ j ∈ range v.length, eqW κ j * v.getD j 0 := by
  rw [dot_eq_sum_fe _ _ (by rw [Lvm.Q1.eqKernel_length_lk]; exact hv)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Lvm.Q1.eqKernel_getD κ (lt_of_lt_of_le (mem_range.mp hj) hv)]

/-! ## `Φ` over a column list -/

/-- **`Φ̃` over a column list** (AC-V's `PhiC`): the closed forms at `p.take τ_k`, `p` the first
`τs` coordinates, dotted with `eq(κ, ·)`, `κ` the rest. -/
def PhiF (cs : List FixCol) (τs : ℕ) (pt : List FE) : FE :=
  Lvm.dot (Lvm.eqKernel (pt.drop τs)) (cs.map fun c ↦ c.ev ((pt.take τs).take c.τ))

/-- **`Φ`'s cells**: cell `x + 2^τs·k` is column `k`'s cell `x mod 2^{τ_k}`, `0` past the columns. -/
def phiCells (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs : ℕ) (n : ℕ) : FK :=
  match cs[n / 2 ^ τs]? with
  | some c => cell c ((n % 2 ^ τs) % 2 ^ c.τ)
  | none => 0

/-- A column read modulo `2^τ` has the extension of its first `2^τ` cells at the first `τ`
coordinates. -/
theorem mle_mod (r : List FE) {τ : ℕ} (hτ : τ ≤ r.length) (u : ℕ → FE) :
    mle r (fun x ↦ u (x % 2 ^ τ)) = mle (r.take τ) u := by
  have ht : (r.take τ).length = τ := by simp; omega
  conv_lhs => rw [← List.take_append_drop τ r]
  rw [Lvm.Loop.mle_split, ht]
  rw [Lvm.Loop.mle_congr (r.drop τ) (w := fun _ ↦ mle (r.take τ) u) fun y _ ↦
    Lvm.Loop.mle_congr _ fun x hx ↦ by
      rw [ht] at hx
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]]
  exact Lvm.Loop.mle_const _ _

/-- **`Φ̃` is the multilinear extension of `Φ`'s cells**, when every closed form is its cells'
extension at its height (`hev`, WP-9b's `FixOk`), every height is at most `τs`, and the columns
fit `2^dk`. -/
theorem phiF_eq_mle (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ)
    (hτ : ∀ c ∈ cs, c.τ ≤ τs)
    (hev : ∀ c ∈ cs, ∀ r : List FE, r.length = c.τ → c.ev r = mle r fun x ↦ FE.ofK (cell c x))
    (hn : cs.length ≤ 2 ^ dk) (pt : List FE) (hpt : pt.length = τs + dk) :
    PhiF cs τs pt = mle pt fun n ↦ FE.ofK (phiCells cs cell τs n) := by
  have hp : (pt.take τs).length = τs := by simp; omega
  have hk : (pt.drop τs).length = dk := by simp; omega
  conv_rhs => rw [← List.take_append_drop τs pt]
  rw [Lvm.Loop.mle_split, hp, PhiF, dot_eqKernel_fe _ _ (by simpa [hk] using hn)]
  rw [Lvm.Loop.mle_congr (pt.drop τs) (w := fun y ↦ if h : y < cs.length then
      (cs[y]'h).ev ((pt.take τs).take (cs[y]'h).τ) else 0) fun y hy ↦ ?_,
    Lvm.Loop.mle_eq_sum, hk]
  · rw [← Finset.sum_range_add_sum_Ico _ (show cs.length ≤ 2 ^ dk from hn)]
    rw [Finset.sum_eq_zero (s := Ico cs.length (2 ^ dk)) fun y hy ↦ by
      rw [dif_neg (by have := (mem_Ico.mp hy).1; omega), mul_zero], add_zero, List.length_map]
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    have hy' := mem_range.mp hy
    rw [dif_pos hy', List.getD_eq_getElem _ _ (by simpa using hy'), List.getElem_map]
  · have hdiv : ∀ x < 2 ^ τs, (x + 2 ^ τs * y) / 2 ^ τs = y := fun x hx ↦ by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, zero_add]
    have hmod : ∀ x < 2 ^ τs, (x + 2 ^ τs * y) % 2 ^ τs = x := fun x hx ↦ by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    split_ifs with hyc
    · have hc := List.getElem_mem hyc
      rw [Lvm.Loop.mle_congr (pt.take τs) (w := fun x ↦ FE.ofK (cell cs[y] (x % 2 ^ cs[y].τ)))
        fun x hx ↦ by
          rw [hp] at hx
          simp only [phiCells, hdiv x hx, hmod x hx, List.getElem?_eq_getElem hyc]]
      have hm := mle_mod (pt.take τs) (τ := cs[y].τ) (by rw [hp]; exact hτ _ hc)
        (fun x ↦ FE.ofK (cell cs[y] x))
      rw [hm, hev _ hc _ (by simp; have := hτ _ hc; omega)]
    · rw [Lvm.Loop.mle_congr (pt.take τs) (w := fun _ ↦ 0) fun x hx ↦ by
          rw [hp] at hx
          simp only [phiCells, hdiv x hx, List.getElem?_eq_none (show cs.length ≤ y by omega),
            Lvm.M3.ofK_zero']]
      exact Lvm.Loop.mle_const _ _

/-- `Φ`'s fixed column on `D = τs + dk` variables. -/
def phiCol (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ) : Column (τs + dk) :=
  fixedColumn (τs + dk) (phiCells cs cell τs)

/-- `Φ̃` read over `E` (the DSL's evaluator: the native one through `FE.toExt3`). -/
def phiE (cs : List FixCol) (τs : ℕ) (pt : List E) : E :=
  FE.toExt3 (PhiF cs τs (pt.map FE.ofExt3))

/-- **`Φ̃` over `E` is `eval₂Mle` of `Φ`'s column** (CompPoly's multilinear extension). -/
theorem phiE_eq_eval₂Mle (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ)
    (hτ : ∀ c ∈ cs, c.τ ≤ τs)
    (hev : ∀ c ∈ cs, ∀ r : List FE, r.length = c.τ → c.ev r = mle r fun x ↦ FE.ofK (cell c x))
    (hn : cs.length ≤ 2 ^ dk) (pt : List E) (hpt : pt.length = τs + dk) :
    phiE cs τs pt = eval₂Mle (phiCol cs cell τs dk).values (algebraMap K E) (vecOf (τs + dk) pt) := by
  rw [phiE, phiF_eq_mle cs cell τs dk hτ hev hn _ (by simpa using hpt), phiCol,
    ← Lvm.M3.toExt3_mle_fixed, LeanVM.Protocol.EndToEnd.Front.toList_vecOf _ hpt]

/-- **`Φ̃ ∘ line` has degree at most `D`** (BLUEPRINT §12.6, the `t` step's `D/|E|`). -/
theorem lineDeg_phiE (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ)
    (hτ : ∀ c ∈ cs, c.τ ≤ τs)
    (hev : ∀ c ∈ cs, ∀ r : List FE, r.length = c.τ → c.ev r = mle r fun x ↦ FE.ofK (cell c x))
    (hn : cs.length ≤ 2 ^ dk) (a b : List E) (ha : a.length = τs + dk) (hb : b.length = τs + dk) :
    ∃ g : Polynomial E, g.natDegree ≤ τs + dk ∧ ∀ t, g.eval t = phiE cs τs (line a b t) := by
  obtain ⟨g, hg, hgv⟩ := lineDeg_mle (phiCol cs cell τs dk) a b ha hb
  refine ⟨g, hg, fun t ↦ ?_⟩
  rw [hgv, phiE_eq_eval₂Mle cs cell τs dk hτ hev hn _ (by rw [length_line, ha, hb, min_self])]

/-! ## The real instance: `PhiC = eval₂Mle Φ` -/

/-- A fixed column's cells, read off the tables (`0` if the column is not fixed). -/
def cellOf (T : List Tab) (c : FixCol) : ℕ → FK :=
  match T[c.tab]?.bind fun t ↦ t.cols[c.col]? with
  | some (.fix f _) => f
  | _ => fun _ ↦ 0

/-- Every column of `fixCols` is a fixed column of its table, with the table's height and the
column's closed form. -/
theorem mem_fixColsR {T : List Tab} {pubTab : ℕ} {c : FixCol} (hc : c ∈ fixColsR T pubTab) :
    ∃ t ∈ T, t.τ = c.τ ∧ ColSrc.fix (cellOf T c) c.ev ∈ t.cols := by
  unfold fixColsR at hc
  obtain ⟨⟨t, j⟩, htj, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨src, i⟩, hsi, hc⟩ := List.mem_filterMap.mp hc
  have ht : T[j]? = some t := List.mem_zipIdx_iff_getElem?.mp htj
  have hs : t.cols[i]? = some src := List.mem_zipIdx_iff_getElem?.mp hsi
  cases src with
  | com _ _ => simp at hc
  | fix f e =>
    simp only at hc
    split_ifs at hc
    obtain rfl := Option.some.inj hc
    refine ⟨t, List.mem_of_getElem? ht, rfl, ?_⟩
    have hcell : cellOf T ⟨j, t.τ, i, e⟩ = f := by simp [cellOf, ht, hs]
    rw [hcell]
    exact List.mem_of_getElem? hs

/-- `FixOk` of the tables gives every column of `fixCols` its cells' extension. -/
theorem fixCols_ev {T : List Tab} (pubTab : ℕ) (hfix : FixOk T) :
    ∀ c ∈ fixColsR T pubTab, ∀ r : List FE, r.length = c.τ →
      c.ev r = mle r fun x ↦ FE.ofK (cellOf T c x) := by
  intro c hc r hr
  obtain ⟨t, ht, hτ, hm⟩ := mem_fixColsR hc
  exact hfix t ht _ _ hm r (hτ ▸ hr)

theorem fixCols_τ {T : List Tab} (pubTab τs : ℕ) (hτ : ∀ t ∈ T, t.τ ≤ τs) :
    ∀ c ∈ fixColsR T pubTab, c.τ ≤ τs := by
  intro c hc
  obtain ⟨t, ht, he, -⟩ := mem_fixColsR hc
  exact he ▸ hτ t ht

/-- The native `PhiC` of the real instance is `PhiF` of its `fixCols`. -/
theorem phiC_real (P : Params) (tabs : Pub → List Tab) (pub : Pub) (pt : List FE) :
    PhiC P (M3.real P tabs) pub pt = PhiF (fixColsR (sumcheckTabs (tabs pub)) P.pubTab) P.tableRounds pt :=
  rfl

/-- **`PhiC = eval₂Mle Φ`** (BLUEPRINT §12.6) for the real instance: from WP-9b's `FixOk` of the
sumcheck tables, their heights at most `tableRounds`, and `nFix ≤ 2^accLog`, at a point of
`tableRounds + accLog` coordinates (`= accVars` under `fitsR`). -/
theorem phiC_eq_eval₂Mle (P : Params) (tabs : Pub → List Tab) (pub : Pub)
    (hfix : FixOk (sumcheckTabs (tabs pub)))
    (hτ : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ P.tableRounds)
    (hn : (fixColsR (sumcheckTabs (tabs pub)) P.pubTab).length ≤ 2 ^ P.accLog)
    (pt : List E) (hpt : pt.length = P.tableRounds + P.accLog) :
    FE.toExt3 (PhiC P (M3.real P tabs) pub (pt.map FE.ofExt3)) =
      eval₂Mle (phiCol (fixColsR (sumcheckTabs (tabs pub)) P.pubTab)
        (cellOf (sumcheckTabs (tabs pub))) P.tableRounds P.accLog).values (algebraMap K E)
        (vecOf _ pt) :=
  phiE_eq_eval₂Mle _ _ _ _ (fixCols_τ _ _ hτ) (fixCols_ev _ hfix) hn pt hpt

/-! ## The instance's `AccHyp`: the fold identity -/

/-- `dot` of a long list with a short one over `E`. -/
theorem dot_eq_sum_e : ∀ (l r : List E), r.length ≤ l.length →
    Verifier.dot l r = ∑ j ∈ range r.length, l.getD j 0 * r.getD j 0
  | _, [], _ => by simp [Verifier.dot]
  | [], _ :: _, h => by simp at h
  | x :: l, y :: r, h => by
    have ih := dot_eq_sum_e l r (by simpa using h)
    have hf : ∀ (m : List E) (a : E), m.foldl (· + ·) a = a + m.sum := fun m ↦ by
      induction m with
      | nil => intro a; simp
      | cons z m ihm => intro a; rw [List.foldl_cons, ihm, List.sum_cons]; ring
    simp only [Verifier.dot, List.zipWith_cons_cons, zero_add, hf, List.sum_cons] at ih ⊢
    rw [ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

/-- **`dot (eqKernel κ) v` over `E`** is the `eq(κ, ·)`-weighted sum of `v`. -/
theorem dot_eqKernel_e (κ v : List E) (hv : v.length ≤ 2 ^ κ.length) :
    Verifier.dot (Verifier.eqKernel κ) v = ∑ j ∈ range v.length, eqAt κ j * v.getD j 0 := by
  rw [dot_eq_sum_e _ _ (by rw [eqKernel_length]; exact hv)]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [eqKernel_getD, if_pos (lt_of_lt_of_le (mem_range.mp hj) hv)]

theorem toExt3_sum (s : Finset ℕ) (f : ℕ → FE) :
    FE.toExt3 (∑ k ∈ s, f k) = ∑ k ∈ s, FE.toExt3 (f k) :=
  map_sum FE.ringEquivExt3 f s

/-- The native equality weight read over `E`. -/
theorem toExt3_eqW : ∀ (l : List E) (w : ℕ), FE.toExt3 (eqW (l.map FE.ofExt3) w) = eqAt l w
  | [], _ => by simp [eqW]
  | r :: l, w => by
    simp only [List.map_cons, eqW, eqAt_cons, FE.toExt3_mul, toExt3_eqW l]
    split_ifs
    · simp
    · rw [FE.toExt3_sub, FE.toExt3_one, FE.toExt3_ofExt3, CharTwo.sub_eq_add]

/-- The fixed claims' errors: claim value minus closed form at the table point, `0` past the
columns. -/
def deltaOf (cs : List FixCol) (vs r : List E) (w : ℕ) : E :=
  if h : w < cs.length then
    vs.getD w 0 - FE.toExt3 ((cs[w]'h).ev ((r.map FE.ofExt3).take (cs[w]'h).τ))
  else 0

/-- **The instance's `AccHyp`**: `Φ = phiE cs τs` (the native `PhiC`), `y_own = dot (eqKernel κ) vs`
(the sent evaluations of `fixCols`), `b(κ) = r ++ κ` with `|r| = τs`, `|a| = D = τs + dk`. -/
theorem accHyp_phi (cs : List FixCol) (cell : FixCol → ℕ → FK) (τs dk : ℕ)
    (hτ : ∀ c ∈ cs, c.τ ≤ τs)
    (hev : ∀ c ∈ cs, ∀ r : List FE, r.length = c.τ → c.ev r = mle r fun x ↦ FE.ofK (cell c x))
    (hn : cs.length ≤ 2 ^ dk) (a r vs : List E) (ha : a.length = τs + dk) (hr : r.length = τs)
    (hvs : vs.length = cs.length) :
    AccHyp dk (τs + dk) a (fun κ ↦ Verifier.dot (Verifier.eqKernel κ) vs) (fun κ ↦ r ++ κ)
      (phiE cs τs) (deltaOf cs vs r) where
  line_deg κ hκ := lineDeg_phiE cs cell τs dk hτ hev hn a _ ha (by simp [hr, hκ])
  at0 κ hκ := line_zero _ _ (by simp [ha, hr, hκ])
  at1 κ hκ := line_one _ _ (by simp [ha, hr, hκ])
  fold κ hκ := by
    have hl : ((r ++ κ).map FE.ofExt3).take τs = r.map FE.ofExt3 := by
      rw [List.map_append, List.take_append_of_le_length (by simp [hr]), List.take_of_length_le
        (by simp [hr])]
    have hd : ((r ++ κ).map FE.ofExt3).drop τs = κ.map FE.ofExt3 := by
      rw [List.map_append, List.drop_append_of_le_length (by simp [hr]), List.drop_of_length_le
        (by simp [hr]), List.nil_append]
    rw [phiE, PhiF, hl, hd, dot_eqKernel_fe _ _ (by simpa [hκ] using hn), toExt3_sum,
      dot_eqKernel_e _ _ (by rw [hvs, hκ]; exact hn), List.length_map, hvs, ← Finset.sum_sub_distrib,
      ← Finset.sum_range_add_sum_Ico _ hn,
      Finset.sum_eq_zero (s := Ico cs.length (2 ^ dk)) fun w hw ↦ by
        rw [deltaOf, dif_neg (by have := (mem_Ico.mp hw).1; omega), mul_zero], add_zero]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := mem_range.mp hw
    rw [FE.toExt3_mul, toExt3_eqW, deltaOf, dif_pos hw', mul_sub,
      List.getD_eq_getElem (cs.map _) _ (by simpa using hw'), List.getElem_map]

end Lvm.Acc
