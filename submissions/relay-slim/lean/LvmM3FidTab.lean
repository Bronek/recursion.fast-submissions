-- adapted from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TableFidLeanIsa.lean`,
-- `.../Front/TableFidLeanIsaBus.lean` (`foldl_max_le`, `le_foldl_max_of_mem`) and
-- `.../Complete/TableMath.lean` (`weightFactor`, `getD_tableWeights`) (formal rev 40f877dc):
-- `powersFrom_eq`, `eq_factor`, `flatten_getD`, `refTableTerms_snd`, `ofFn_vecOf`, `prodWeight_eq`,
-- `tableValues_eq`, `rounds/target/formula/claims` for any number of tables (leanVM's are at six
-- leanISA tables), `sampleN_bind_congr`, `abGuard`, `abProg_bind_guard`, `abSpec4`; new for lvm
-- (WP-9b): `tableFidL` (the table phase's identities at the lvm instance) and `lbusTableSpec`
-- (the bus phase and the table sumcheck with no fidelity hypothesis).
import LvmM3FidBus

/-!
# The table phase's identities at the lvm instance

For the lvm instance `I = inst L tabs hτ` with every table a sumcheck table (`AllSc`), every
message of at most thirteen value limbs (`KeysOk`) and every table of positive width, at every
read of the bus phase with four fingerprint challenges, the GKR point on `μ_bus` coordinates and
three values:

* `tableFidL`: the table phase's identities (`TableFidG`) for the program objects of `LvmM3Fid`
  (`vTables`, `vLayout`, `busResV`, `colOfL`): the rounds are `τ_max` (`rounds_lvm`), the target is
  the protocol's batched claim (`target_lvm`, from `totals_busResV`), the final check's value is
  the protocol's formula (`formula_lvm`: weights `prodWeight_eq`, values `tableValues_eq`,
  constraints `eval₂_toMv`, forms `formAt_busResV`), every protocol claim is the program's
  (`claims_lvm`);
* `lbusTableSpec`: the lvm bus phase then the table sumcheck, with no fidelity hypothesis left
  (`lvmBusSpec4`: the bus phase with the four challenges recorded, from `abSpec4`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.Compile LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open Finset
open scoped NNReal ENNReal

/-! ## Generic facts (leanVM) -/

/-- `powers_from(acc, base, n)` is `acc · base^i` for `i < n`. -/
theorem powersFrom_eq (base : E) : ∀ (n : ℕ) (acc : E),
    powersFrom acc base n = (List.range n).map fun i ↦ acc * base ^ i
  | 0, _ => rfl
  | n + 1, acc => by
    rw [powersFrom, powersFrom_eq base n, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [pow_zero, mul_one, Function.comp_def, pow_succ']
    exact congrArg (_ :: ·) (List.map_congr_left fun i _ ↦ by ring)

theorem powers_eq (ξ : E) (n : ℕ) : powers ξ n = (List.range n).map (ξ ^ ·) := by
  rw [powers, powersFrom_eq]; simp

/-- A fold of `max` is below a bound above the start and every entry. -/
theorem foldl_max_le {b : ℕ} : ∀ (l : List ℕ) (i0 : ℕ), i0 ≤ b → (∀ x ∈ l, x ≤ b) →
    l.foldl max i0 ≤ b
  | [], _, h, _ => h
  | x :: l, i0, h, hl =>
    foldl_max_le l _ (max_le h (hl x (by simp))) fun y hy ↦ hl y (by simp [hy])

/-- An entry is below the fold of `max`. -/
theorem le_foldl_max_of_mem {x : ℕ} : ∀ {l : List ℕ} {i0 : ℕ}, x ∈ l → x ≤ l.foldl max i0
  | y :: l, i0, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact (le_max_right _ _).trans (le_foldl_max_init l _)
    · exact le_foldl_max_of_mem h
where
  le_foldl_max_init : ∀ (l : List ℕ) (i0 : ℕ), i0 ≤ l.foldl max i0
    | [], _ => le_rfl
    | y :: l, i0 => (le_max_left i0 y).trans (le_foldl_max_init l _)

/-- The equality factor in characteristic two. -/
theorem eq_factor (a b : E) : (1 - a) * (1 - b) + a * b = 1 + b + a := by
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  linear_combination (a * b) * Whir.Complete.two_eq_zero_E

/-- The factor of coordinate `v` in the weight of a table of log-height `h`. -/
def weightFactor (e : List E) (h v : ℕ) (c : E) : E :=
  if v < h then 1 + e.getD v 0 + c else c

private theorem foldl_weights (heights : List ℕ) (e : List E) :
    ∀ (r : List E) (k : ℕ) (W : List E), W.length = heights.length →
      (r.zipIdx k).foldl (fun weights (challenge, coord) ↦
        List.zipWith (fun weight height ↦ weight *
          if coord < height then 1 + e.getD coord 0 + challenge else challenge) weights heights)
        W = List.zipWith (fun w height ↦ w * ∏ i ∈ range r.length,
          weightFactor e height (k + i) (r.getD i 0)) W heights
  | [], k, W, hW => by
    simp only [List.zipIdx_nil, List.foldl_nil, List.length_nil, prod_range_zero, mul_one]
    apply List.ext_getElem (by simp [hW])
    intro i h1 h2
    simp
  | c :: r, k, W, hW => by
    rw [List.zipIdx_cons, List.foldl_cons,
      foldl_weights heights e r (k + 1) _ (by simp [hW])]
    apply List.ext_getElem (by simp [hW])
    intro i h1 h2
    simp only [List.getElem_zipWith, List.length_cons]
    rw [prod_range_succ', mul_assoc]
    refine congrArg (W[i]'(by simp_all) * ·) ?_
    rw [mul_comm]
    refine congrArg₂ (· * ·) (prod_congr rfl fun j _ ↦ ?_) ?_
    · rw [show k + (j + 1) = k + 1 + j by ring]
      rfl
    · simp [weightFactor]

/-- The verifier's weights, one per table. -/
theorem length_tableWeights (heights : List ℕ) (e r : List E) :
    (tableWeights heights e r).length = heights.length := by
  rw [Verifier.tableWeights, foldl_weights heights e r 0 _ (by simp)]
  simp

/-- **The verifier's table weight** of a table of log-height `h` at `r`:
`Π_{v < h} (1 + e_v + r_v) · Π_{h ≤ v} r_v`. -/
theorem getD_tableWeights (heights : List ℕ) (e r : List E) (t : ℕ) (ht : t < heights.length) :
    (tableWeights heights e r).getD t 0 =
      ∏ v ∈ range r.length, weightFactor e (heights.getD t 0) v (r.getD v 0) := by
  rw [Verifier.tableWeights, foldl_weights heights e r 0 _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_zipWith,
    List.getD_eq_getElem _ _ ht]
  simp

/-- Entry `i` of list `t` of a list of lists, inside the concatenation. -/
theorem flatten_getD : ∀ (l : List (List E)) (t i : ℕ), t < l.length → i < (l.getD t []).length →
    l.flatten.getD ((∑ u ∈ range t, (l.getD u []).length) + i) 0 = (l.getD t []).getD i 0
  | [], _, _, h, _ => by simp at h
  | a :: l, 0, i, _, hi => by
    simp only [List.getD_cons_zero] at hi ⊢
    rw [Finset.sum_range_zero, zero_add, List.flatten_cons, List.getD_append _ _ _ _ hi]
  | a :: l, t + 1, i, ht, hi => by
    simp only [List.getD_cons_succ, List.length_cons] at hi ht ⊢
    rw [Finset.sum_range_succ', List.getD_cons_zero, List.flatten_cons]
    simp only [List.getD_cons_succ]
    rw [add_comm _ a.length, add_assoc, List.getD_append_right _ _ _ _ (by omega),
      Nat.add_sub_cancel_left]
    exact flatten_getD l t i (by omega) hi

/-- The claims the final loop returns: the given ones, then every table's values, each on its
column at the point's first `height` coordinates. -/
theorem refTableTerms_snd (tables : List Table) (cps fps pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      (refTableTerms tables cps fps pt rows evs cursor final claims).2 = claims ++
        (List.zip rows evs).flatMap fun p ↦ p.2.zipIdx.map fun (value, column) ↦
          (⟨(globalColumnBases tables).getD p.1.1.opcode 0 + column, pt.take p.1.2.1, value⟩ :
            Verifier.ColumnClaim)
  | [], _, _, _, claims => by simp [refTableTerms]
  | _ :: _, [], _, _, claims => by simp [refTableTerms]
  | (table, height, forms, weight) :: rest, ev :: evs, cursor, final, claims => by
    rw [refTableTerms, refTableTerms_snd tables cps fps pt rest evs]
    simp

/-- The final value of the loop: the given one plus every table's weighted terms, the constraint
powers taken from the cursor on. -/
theorem refTableTerms_fst (tables : List Table) (cps fps pt : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (evs : List (List E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim), rows.length = evs.length →
      (refTableTerms tables cps fps pt rows evs cursor final claims).1 = final +
        ∑ i ∈ range rows.length, ((rows.getD i default).2.2.2 *
          (dot ((cps.drop (cursor + ∑ i' ∈ range i, (rows.getD i' default).1.nConstraints)).take
              (rows.getD i default).1.nConstraints)
            ((rows.getD i default).1.constraints (evs.getD i [])) +
          dot fps ((rows.getD i default).2.2.1.map (·.evaluate ((evs.getD i []).getD · 0)))))
  | [], _, _, _, _, _ => by simp [refTableTerms]
  | _ :: _, [], _, _, _, h => by simp at h
  | (table, height, forms, weight) :: rest, ev :: evs, cursor, final, claims, h => by
    have h' : rest.length = evs.length := by simpa using h
    have e := refTableTerms_fst tables cps fps pt rest evs (cursor + table.nConstraints)
      (final + weight * (dot ((cps.drop cursor).take table.nConstraints) (table.constraints ev) +
        dot fps (forms.map (·.evaluate (ev.getD · 0))))) (claims ++ ev.zipIdx.map
          fun (value, column) ↦ ⟨(globalColumnBases tables).getD table.opcode 0 + column,
            pt.take height, value⟩) h'
    refine e.trans ?_
    rw [List.length_cons, Finset.sum_range_succ' _ rest.length, add_assoc, add_comm (weight * _)]
    refine congrArg (final + ·) (congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) ?_)
    · have hs : ∑ i' ∈ range (i + 1),
          (((table, height, forms, weight) :: rest).getD i' default).1.nConstraints =
          ∑ i' ∈ range i, (rest.getD i' default).1.nConstraints + table.nConstraints := by
        rw [Finset.sum_range_succ']; rfl
      rw [List.getD_cons_succ, List.getD_cons_succ, hs, add_assoc cursor, add_comm table.nConstraints]
    · simp only [List.getD_cons_zero, Finset.sum_range_zero, add_zero]

/-- The low coordinates of a list read as a vector. -/
theorem ofFn_vecOf (p : List E) {μ m : ℕ} (hm : m ≤ μ) (hp : p.length = μ) :
    (List.ofFn fun j : Fin m ↦ (vecOf μ p)[j.val]'(by omega)) = p.take m := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_ofFn, vecOf, Vector.getElem_ofFn, List.getElem_take]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- A sum over a list's positions, as a sum over the indices. -/
theorem sum_fin_length {α : Type} (l : List α) (c : ℕ) (ξ : E) (g : α → E) :
    ∑ i : Fin l.length, ξ ^ (c + i.val) * g l[i] =
      ∑ k ∈ range l.length, ξ ^ (c + k) * (l.map g).getD k 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map]
  rfl

/-- A sum over a list's entries, as a sum over its positions. -/
theorem sum_map_get {α M : Type} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ j : Fin l.length, f (l.get j) = (l.map f).sum := by
  have h : (List.finRange l.length).map (fun j ↦ f (l.get j)) =
      ((List.finRange l.length).map l.get).map f := by rw [List.map_map]; rfl
  rw [Fin.sum_univ_def, h, List.map_get_finRange]

/-- The constraint powers from `c` on, `m` of them, against `m` values. -/
theorem dot_cps (ξ : E) (n c m : ℕ) (l : List E) (hl : l.length = m) (hcm : c + m ≤ n) :
    dot ((((powers ξ (n + 3)).take n).drop c).take m) l =
      ∑ i ∈ range m, ξ ^ (c + i) * l.getD i 0 := by
  have hlen : ((((powers ξ (n + 3)).take n).drop c).take m).length = m := by
    simp [powers_eq]; omega
  rw [Whir.Complete.dot_eq_sum _ _ (by rw [hlen, hl]), hlen]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.mp hi
  rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi')]
  simp [powers_eq]

/-- The form powers: `ξ^n, ξ^(n+1), ξ^(n+2)`. -/
theorem fps_eq (ξ : E) (n : ℕ) : (powers ξ (n + 3)).drop n = (List.range 3).map fun s ↦ ξ ^ (n + s) := by
  rw [powers_eq, List.range_add, List.map_append, List.drop_append_of_le_length (by simp),
    List.drop_eq_nil_of_le (by simp), List.nil_append, List.map_map]
  rfl

/-! ## The lvm instance -/

section Lvm

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)

/-- The lvm tables are the instance's sumcheck tables, in order. -/
def stEq : Fin tabs.length ≃ (inst L tabs hτ).SumcheckTables where
  toFun j := ⟨j, sumcheckTable_of L tabs hτ hsc j⟩
  invFun t := t.1
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem stEq_val (j : Fin tabs.length) : (stEq L tabs hτ hsc j).1 = j := rfl

include hsc in
/-- **The rounds**: `τ_max` is the largest log-height. -/
theorem rounds_lvm : (vLayout tabs).tableLogHeights.foldl max 0 = (inst L tabs hτ).τmax := by
  apply le_antisymm
  · refine foldl_max_le _ _ (Nat.zero_le _) fun x hx ↦ ?_
    simp only [vLayout, List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := List.get_of_mem ht
    exact (inst L tabs hτ).τ_le_τmax (stEq L tabs hτ hsc j)
  · refine Finset.sup_le fun j _ ↦ ?_
    exact le_foldl_max_of_mem (List.mem_map_of_mem (f := Tab.τ) (List.get_mem _ _))

theorem vTables_getD (j : ℕ) (hj : j < tabs.length) : (vTables tabs).getD j default = vTable j tabs[j] := by
  rw [List.getD_eq_getElem _ _ (by rw [length_vTables]; exact hj)]
  simp [vTables, List.getElem_zipIdx]

theorem nConstraints_vTable (j : ℕ) (t : Tab) : (vTable j t).nConstraints = t.cons.length := by
  simp [Table.nConstraints, vTable]

theorem width_vTable (j : ℕ) (t : Tab) : (vTable j t).width = t.w := by
  simp [Table.width, vTable]

include hsc in
/-- **The number of constraints** is the program's. -/
theorem nCons_eq : nCons (vTables tabs) = (inst L tabs hτ).B := by
  unfold M3Instance.B nCons
  rw [← (stEq L tabs hτ hsc).sum_comp]
  simp only [stEq_val]
  change _ = ∑ j : Fin tabs.length, ((tabs.get j).cons.map (CPoly.toMv _)).length
  simp only [List.length_map]
  rw [sum_map_get tabs fun t ↦ t.cons.length, vTables, zipIdx_eq_finRange, List.map_map,
    List.map_map, ← Fin.sum_univ_def, ← sum_map_get]
  exact Finset.sum_congr rfl fun j _ ↦ by simp [nConstraints_vTable]

/-- Kept sizes of the sumcheck tables before `j`: every table is one. -/
theorem prefix_onSumcheck (f : Fin (inst L tabs hτ).ntab → ℕ) (g : ℕ → ℕ)
    (hfg : ∀ j, f j = g j.val) (j : Fin tabs.length) :
    ∑ j' : Fin (stEq L tabs hτ hsc j).1.val,
        onSumcheck (inst L tabs hτ) f (Fin.castLE (stEq L tabs hτ hsc j).1.isLt.le j') =
      ∑ u ∈ range j, g u := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j' _ ↦ ?_
  simp only [onSumcheck, if_pos (sumcheckTable_of L tabs hτ hsc _), hfg]
  rfl

variable {L tabs hτ} in
/-- The rows of the final loop, entry by entry. -/
theorem rowsOf_getD (bus : BusResult) (pt : List E) (hf : bus.forms.length = tabs.length)
    (j : ℕ) (hj : j < tabs.length) :
    (rowsOf (vTables tabs) (vLayout tabs) bus pt).getD j default =
      (vTable j tabs[j], tabs[j].τ, bus.forms.getD j [],
        (Verifier.tableWeights (tabs.map (·.τ)) bus.point pt).getD j 0) := by
  have hw := length_tableWeights (tabs.map (·.τ)) bus.point pt
  rw [List.length_map] at hw
  rw [List.getD_eq_getElem _ _ (by simp [rowsOf, vLayout, length_vTables, hf, hw, hj])]
  simp only [rowsOf, vLayout, List.getElem_zip, List.getElem_map]
  rw [← vTables_getD tabs j hj, List.getD_eq_getElem _ _ (by rw [length_vTables]; exact hj),
    List.getD_eq_getElem _ _ (by rw [hf]; exact hj), List.getD_eq_getElem _ _ (by rw [hw]; exact hj)]

theorem length_rowsOf (bus : BusResult) (pt : List E) (hf : bus.forms.length = tabs.length) :
    (rowsOf (vTables tabs) (vLayout tabs) bus pt).length = tabs.length := by
  have hw := length_tableWeights (tabs.map (·.τ)) bus.point pt
  simp [rowsOf, vLayout, length_vTables, hf, hw]

theorem length_forms (b : LBus) : (busResV tabs b).forms.length = tabs.length := by
  simp [busResV, busFinalV]

theorem length_forms_getD (b : LBus) (j : ℕ) (hj : j < tabs.length) :
    ((busResV tabs b).forms.getD j []).length = 3 := by
  simp only [busResV, busFinalV]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range,
    List.length_map]
  simp [sidesV, sideBlocksV]

/-- What a read of the right shape is: one list per table, of the table's width. -/
theorem readShape_facts (bus : BusResult) (pt : List E) (hf : bus.forms.length = tabs.length)
    (evs : List (List E)) (hs : ReadShape (rowsOf (vTables tabs) (vLayout tabs) bus pt) evs) :
    evs.length = tabs.length ∧ ∀ j (hj : j < tabs.length), (evs.getD j []).length = tabs[j].w := by
  have hl := hs.length_eq
  rw [length_rowsOf tabs bus pt hf] at hl
  refine ⟨hl.symm, fun j hj ↦ ?_⟩
  obtain ⟨-, h⟩ := List.forall₂_iff_get.mp hs
  have := h j (by rw [length_rowsOf tabs bus pt hf]; exact hj) (by rw [← hl]; exact hj)
  rw [List.getD_eq_getElem _ _ (by rw [← hl]; exact hj)]
  have hr := rowsOf_getD bus pt hf j hj
  rw [List.getD_eq_getElem _ _ (by rw [length_rowsOf tabs bus pt hf]; exact hj)] at hr
  simp only [List.get_eq_getElem] at this
  rw [this, hr, width_vTable]

/-- **The values read are the protocol's**: column `i` of table `j` among the values of all the
columns is entry `i` of table `j`'s read. -/
theorem tableValues_eq (evs : List (List E)) (hlen : evs.length = tabs.length)
    (hw : ∀ j (hj : j < tabs.length), (evs.getD j []).length = tabs[j].w) (j : Fin tabs.length)
    (i : Fin ((inst L tabs hτ).width (stEq L tabs hτ hsc j).1)) :
    tableValues (inst L tabs hτ) (vecOf _ evs.flatten) (stEq L tabs hτ hsc j) i =
      (evs.getD j []).getD i 0 := by
  unfold tableValues
  simp only [vecOf, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [show (((columnPos (inst L tabs hτ)) ⟨stEq L tabs hτ hsc j, i⟩ : Fin _) : ℕ) = _
    from position_val _ _ _, prefix_onSumcheck L tabs hτ hsc _ (fun u ↦ (evs.getD u []).length)
      (fun j' ↦ by rw [hw j' j'.isLt]; rfl)]
  exact flatten_getD evs j i (by rw [hlen]; exact j.isLt)
    (by rw [hw j j.isLt]; exact i.isLt)

end Lvm

/-! ## The identities -/

theorem getD_map_evaluate (l : List Form) (k : ℕ) (col : ℕ → E) :
    (l.map (·.evaluate col)).getD k 0 = (l.getD k {}).evaluate col := by
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [evaluate_eq]

section Fid

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)

/-- Table `u`'s constraint count (`0` past the tables). -/
def consLen (tabs : List Tab) (u : ℕ) : ℕ := (tabs[u]?.map fun t ↦ t.cons.length).getD 0

theorem consLen_eq (u : ℕ) (hu : u < tabs.length) : consLen tabs u = tabs[u].cons.length := by
  simp [consLen, List.getElem?_eq_getElem hu]

theorem nCons_eq_sum : nCons (vTables tabs) = ∑ u ∈ range tabs.length, consLen tabs u := by
  unfold nCons
  rw [vTables, zipIdx_eq_finRange, List.map_map, List.map_map, ← Fin.sum_univ_def,
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ ↦ by
    simp [nConstraints_vTable, consLen_eq tabs j j.isLt]

/-- The protocol's statement after the lvm bus phase. -/
noncomputable abbrev sOf (b : LBus) : (inst L tabs hτ).Stmt × BusOut (inst L tabs hτ) :=
  lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)

/-- **The weights**: the protocol's weight of table `j` at the reversed challenges is the
verifier's. -/
theorem prodWeight_eq (b : LBus) (ch : List E) (hch : ch.length = (inst L tabs hτ).τmax)
    (j : Fin tabs.length) :
    prodWeight (TableSumcheck.tableWeights (inst L tabs hτ) (sOf L tabs hτ hsc b).2.point
        (stEq L tabs hτ hsc j)) (vecOf _ ch).reverse =
      (Verifier.tableWeights (tabs.map (·.τ)) b.point ch.reverse).getD j 0 := by
  rw [getD_tableWeights _ _ _ _ (by simp), List.length_reverse, hch, prodWeight,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun a _ ↦ ?_
  have hz : ((vecOf (inst L tabs hτ).τmax ch).reverse)[a.val] = ch.reverse.getD a 0 := by
    rw [Vector.getElem_reverse, List.getD_eq_getElem _ _ (by simp [hch]), List.getElem_reverse]
    simp only [vecOf, Vector.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ (by omega)]
    congr 1
    omega
  have hζ : ((sOf L tabs hτ hsc b).2.point)[a.val] = b.point.getD a 0 := by
    simp [sOf, lbusStmt, Bus.busOut, Bus.point, Gkr.lowPoint, layerStmtOf, vecOf]
  have hτj : (tabs.map (·.τ)).getD j 0 = (inst L tabs hτ).τ (stEq L tabs hτ hsc j).1 := by
    simp [List.getD_eq_getElem?_getD]
  rw [Fin.getElem_fin, hz, hτj]
  simp only [TableSumcheck.tableWeights, weightFactor]
  split_ifs with h
  · simp only [Fin.getElem_fin, hζ]
    exact eq_factor _ _
  · simp

include hsc in
/-- **The target**: the form powers against the program's totals are the protocol's batched
claim. -/
theorem target_lvm (b : LBus) (hp : b.point.length = (inst L tabs hτ).μBus) (ξ : E) :
    dot (fpsOf (vTables tabs) ξ) (busResV tabs b).totals =
      powerBatch (claimed (inst L tabs hτ) (sOf L tabs hτ hsc b)) ξ := by
  have h3 : (busResV tabs b).totals.length = 3 := by simp [busResV, busFinalV]
  rw [powerBatch, claimed, Fin.sum_univ_add]
  simp only [Fin.append_left, zero_mul, Finset.sum_const_zero, zero_add, Fin.append_right,
    Fin.val_natAdd]
  rw [fpsOf, nCons_eq L tabs hτ hsc, fps_eq, Whir.Complete.dot_eq_sum _ _ (by rw [h3]; simp),
    List.length_map, List.length_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range, mul_comm,
    totals_busResV L tabs hτ hsc b hp i]

/-- The values read as the table's row: below the width the protocol's values, zero above. -/
theorem rowE_tableValues (evs : List (List E)) (hlen : evs.length = tabs.length)
    (hw : ∀ j (hj : j < tabs.length), (evs.getD j []).length = tabs[j].w) (j : Fin tabs.length) :
    rowE (tableValues (inst L tabs hτ) (vecOf _ evs.flatten) (stEq L tabs hτ hsc j)) =
      fun i ↦ (evs.getD j []).getD i 0 := by
  funext i
  unfold rowE
  split_ifs with hi
  · exact tableValues_eq L tabs hτ hsc evs hlen hw j ⟨i, hi⟩
  · exact (List.getD_eq_default _ _ (by rw [hw j j.isLt]; exact not_lt.mp hi)).symm

/-- **The final check's value is the protocol's formula**. -/
theorem formula_lvm (hkey : KeysOk tabs) (b : LBus) (ha : b.alphas.length = 4)
    (hp : b.point.length = (inst L tabs hτ).μBus) (ξ : E) (ch : List E) (evs : List (List E))
    (hch : ch.length = (inst L tabs hτ).τmax)
    (hs : ReadShape (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse) evs) :
    (refTableTerms (vTables tabs) (cpsOf (vTables tabs) ξ) (fpsOf (vTables tabs) ξ) ch.reverse
        (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse) evs 0 0 []).1 =
      TableSumcheck.formula (inst L tabs hτ) (sOf L tabs hτ hsc b, ξ)
        (vecOf (inst L tabs hτ).τmax ch).reverse
        (vecOf (inst L tabs hτ).tableColumns evs.flatten) := by
  have hf := length_forms tabs b
  obtain ⟨hlen, hw⟩ := readShape_facts tabs _ ch.reverse hf evs hs
  rw [refTableTerms_fst _ _ _ _ _ _ _ _ _ (by rw [length_rowsOf tabs _ _ hf, hlen]), zero_add,
    length_rowsOf tabs _ _ hf]
  unfold TableSumcheck.formula
  rw [← (stEq L tabs hτ hsc).sum_comp, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcur : ∑ i' ∈ range j.val,
      ((rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse).getD i' default).1.nConstraints =
      ∑ u ∈ range j.val, consLen tabs u :=
    Finset.sum_congr rfl fun u hu ↦ by
      have hu' : u < tabs.length := (Finset.mem_range.mp hu).trans j.isLt
      rw [rowsOf_getD _ _ hf u hu', nConstraints_vTable, consLen_eq tabs u hu']
  rw [hcur, rowsOf_getD _ _ hf j j.isLt, zero_add]
  simp only
  rw [show (busResV tabs b).point = b.point from rfl, ← prodWeight_eq L tabs hτ hsc b ch hch j]
  refine congrArg (_ * ·) ?_
  have hcol := rowE_tableValues L tabs hτ hsc evs hlen hw j
  set e := tableValues (inst L tabs hτ) (vecOf _ evs.flatten) (stEq L tabs hτ hsc j)
  unfold rowValue
  dsimp only
  refine congrArg₂ (· + ·) ?_ ?_
  · -- the constraints
    have hpos : ∀ i, (constraintPos (inst L tabs hτ) ⟨stEq L tabs hτ hsc j, i⟩ : ℕ) =
        (∑ u ∈ range j.val, consLen tabs u) + i := fun i ↦ by
      rw [show ((constraintPos (inst L tabs hτ) ⟨stEq L tabs hτ hsc j, i⟩ : Fin _) : ℕ) = _
        from position_val _ _ _, prefix_onSumcheck L tabs hτ hsc _ (consLen tabs)
          (fun j' ↦ by rw [consLen_eq tabs j' j'.isLt]; simp)]
    have hR : ∑ i : Fin ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1).length,
        ξ ^ (constraintPos (inst L tabs hτ) ⟨stEq L tabs hτ hsc j, i⟩ : ℕ) *
          evalRow ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1)[i] e =
        ∑ i : Fin ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1).length,
          ξ ^ ((∑ u ∈ range j.val, consLen tabs u) + i.val) *
            evalRow ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1)[i] e :=
      Finset.sum_congr rfl fun i _ ↦ by rw [hpos i]
    have hm : ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1).length =
        tabs[j.val].cons.length := by
      show ((tabs.get j).cons.map _).length = _
      simp
    have hcm : (∑ u ∈ range j.val, consLen tabs u) + tabs[j.val].cons.length ≤
        nCons (vTables tabs) := by
      rw [nCons_eq_sum, ← consLen_eq tabs j j.isLt, ← Finset.sum_range_succ]
      exact Finset.sum_le_sum_of_subset fun x hx ↦
        Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le j.isLt)
    have hmap : ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1).map (evalRow · e) =
        (vTable j tabs[j.val]).constraints (evs.getD j []) := by
      show ((tabs.get j).cons.map _).map _ = (tabs[j.val].cons.map _)
      rw [List.map_map]
      refine List.map_congr_left fun P _ ↦ ?_
      simp only [Function.comp_apply, evalRow]
      rw [eval₂_toMv, hcol]
    rw [hR, sum_fin_length ((inst L tabs hτ).constraints (stEq L tabs hτ hsc j).1) _ ξ
      (fun P ↦ evalRow P e), hm, hmap, cpsOf, nConstraints_vTable,
      dot_cps ξ _ _ _ _ (by simp [vTable]) hcm]
  · -- the forms
    have h3 := length_forms_getD tabs b j j.isLt
    rw [fpsOf, nCons_eq L tabs hτ hsc, fps_eq,
      Whir.Complete.dot_eq_sum _ _ (by rw [List.length_map, List.length_map, h3, List.length_range]),
      List.length_map, List.length_range, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
      getD_map_evaluate]
    refine congrArg (_ * ·) ?_
    rw [formAt_busResV L tabs hτ hsc hkey b ha hp k (stEq L tabs hτ hsc j) e, hcol]
    rfl

/-- A sumcheck table's point, listed: the point's first `τ` coordinates. -/
theorem toList_lowPoint (I : M3Instance) (r : Vector E I.τmax) (t : I.SumcheckTables) :
    (I.lowPoint r t).toList = r.toList.take (I.τ t.1) := by
  apply List.ext_getElem (by simp [I.τ_le_τmax t])
  intro i h1 h2
  rw [List.getElem_take, Vector.getElem_toList, Vector.getElem_toList]
  simp only [M3Instance.lowPoint, Vector.getElem_cast]
  rw [Vector.getElem_take]

/-- **The protocol's output claims are among the program's.** -/
theorem claims_lvm (b : LBus) (ξ : E) (ch : List E) (claim : E) (evs : List (List E))
    (hch : ch.length = (inst L tabs hτ).τmax)
    (hs : ReadShape (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse) evs) :
    ∀ c ∈ (tableOut (inst L tabs hτ) (tableStmtG (inst L tabs hτ) (sOf L tabs hτ hsc b) ξ ch claim)
      (vecOf (inst L tabs hτ).tableColumns evs.flatten)).2.columns.toList,
      (⟨colOfL L tabs hτ c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
        (busResV tabs b).claims ++ (refTableTerms (vTables tabs) (cpsOf (vTables tabs) ξ)
          (fpsOf (vTables tabs) ξ) ch.reverse
          (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse) evs 0 0 []).2 := by
  intro c hc
  have hf := length_forms tabs b
  obtain ⟨hlen, hw⟩ := readShape_facts tabs _ ch.reverse hf evs hs
  simp only [tableOut, tableStmtG, Vector.toList_append, List.mem_append] at hc
  rcases hc with hc | hc
  · exfalso
    have h0 : ((sOf L tabs hτ hsc b).2.columns.toList).length = 0 := by
      rw [Vector.length_toList]; exact busClaims_zero L tabs hτ
    rw [List.eq_nil_of_length_eq_zero h0] at hc
    exact List.not_mem_nil hc
  simp only [finalClaims, Vector.toList_ofFn, List.mem_ofFn] at hc
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨⟨t, i⟩, hk⟩ : ∃ p, (columnPos (inst L tabs hτ)).symm k = p := ⟨_, rfl⟩
  obtain ⟨j, rfl⟩ := (stEq L tabs hτ hsc).surjective t
  have hk' : k = columnPos (inst L tabs hτ) ⟨stEq L tabs hτ hsc j, i⟩ := by
    rw [← hk, Equiv.apply_symm_apply]
  subst hk'
  have hv : (vecOf (inst L tabs hτ).tableColumns evs.flatten)[columnPos (inst L tabs hτ)
      ⟨stEq L tabs hτ hsc j, i⟩] = (evs.getD j []).getD i 0 :=
    tableValues_eq L tabs hτ hsc evs hlen hw j i
  simp only [finalClaim, Equiv.symm_apply_apply, hv]
  refine List.mem_append_right _ ?_
  rw [refTableTerms_snd, List.nil_append, List.mem_flatMap]
  have hjr : j.val < (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse).length := by
    rw [length_rowsOf tabs _ _ hf]; exact j.isLt
  have hje : j.val < evs.length := by rw [hlen]; exact j.isLt
  refine ⟨((rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b) ch.reverse).getD j default,
    evs.getD j []), ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hjr, List.getD_eq_getElem _ _ hje]
    have hz : j.val < (List.zip (rowsOf (vTables tabs) (vLayout tabs) (busResV tabs b)
        ch.reverse) evs).length := by rw [List.length_zip]; omega
    exact List.mem_iff_getElem.mpr ⟨j.val, hz, List.getElem_zip⟩
  · have hi : i.val < (evs.getD j []).length := by rw [hw j j.isLt]; exact i.isLt
    refine List.mem_map.mpr ⟨((evs.getD j []).getD i 0, i), ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hi]
      have := List.getElem_zipIdx (l := evs.getD j []) (j := 0) (i := i.val) (by simpa using hi)
      rw [zero_add] at this
      exact this ▸ List.getElem_mem _
    · rw [rowsOf_getD _ _ hf j j.isLt]
      simp only [colOfL, vTable, stEq_val]
      rw [toList_lowPoint, Vector.toList_reverse, toList_vecOf ch hch]
      have hsnd : (((columnPos (inst L tabs hτ)).symm (columnPos (inst L tabs hτ)
          ⟨stEq L tabs hτ hsc j, i⟩)).2 : ℕ) = i := by rw [hk]
      have hfst : ((columnPos (inst L tabs hτ)).symm (columnPos (inst L tabs hτ)
          ⟨stEq L tabs hτ hsc j, i⟩)).1 = stEq L tabs hτ hsc j := by rw [hk]
      rw [hsnd, hfst]
      rfl

/-- **The table phase's identities at the lvm instance** (leanVM `TableFid`, discharged). -/
theorem tableFidL (hkey : KeysOk tabs) (b : LBus) (ha : b.alphas.length = 4)
    (hp : b.point.length = (inst L tabs hτ).μBus) :
    TableFidG (vTables tabs) (inst L tabs hτ) (vLayout tabs) (colOfL L tabs hτ)
      (sOf L tabs hτ hsc b) (busResV tabs b) where
  rounds := rounds_lvm L tabs hτ hsc
  target := target_lvm L tabs hτ hsc b hp
  formula ξ ch evs hch hs := formula_lvm L tabs hτ hsc hkey b ha hp ξ ch evs hch hs
  claims ξ ch claim evs hch hs := claims_lvm L tabs hτ hsc b ξ ch claim evs hch hs


end Fid

/-! ## The fingerprint challenges are four (leanVM `TableFidLeanIsa`) -/

section Spec4

variable {εmax : ℝ≥0∞}

/-- `n` challenges are a list of `n`: continuations that agree on such lists give one program. -/
theorem sampleN_bind_congr {β : Type} : ∀ (n : ℕ) (k k' : List E → VerifierProgram β),
    (∀ as, as.length = n → k as = k' as) →
      (VerifierProgram.sampleChallenges n).bind k = (VerifierProgram.sampleChallenges n).bind k'
  | 0, k, k', h => h [] rfl
  | n + 1, k, k', h => by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq,
        VerifierProgram.bind_assoc]
    exact congrArg (VerifierProgram.sampleChallenge.bind ·) (funext fun x ↦
      sampleN_bind_congr n _ _ fun as has ↦ h (x :: as) (by simp [has]))

/-- The guard that the fingerprint challenges are four. -/
def abGuard (ab : List E × E) : VerifierProgram (List E × E) :=
  if ab.1.length = 4 then VerifierProgram.ret ab else VerifierProgram.fail

/-- The wire's fingerprint challenges are four: guarding it changes nothing. -/
theorem abProg_bind_guard : abProg.bind abGuard = abProg := by
  unfold abProg
  rw [VerifierProgram.bind_assoc]
  refine sampleN_bind_congr 4 _ _ fun as has ↦ ?_
  rw [VerifierProgram.bind_assoc]
  refine congrArg (VerifierProgram.sampleChallenge.bind ·) (funext fun b ↦ ?_)
  simp [abGuard, has]

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt)

/-- **The fingerprint challenges, four of them**: `abSpec` with the length of the challenges
recorded. -/
noncomputable def abSpec4 {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hlt : abError I L₀ < 1) :
    Spec abProg (HDoom cands (Seam.commit I) input)
      (fun ab h ↦ ab.1.length = 4 ∧
        HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) εmax
      (abError I L₀ + 0) 0 :=
  let P4 : List E × E → List Ev → Prop := fun ab h ↦ ab.1.length = 4 ∧
    HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h
  let G : ∀ ab : List E × E, Spec (abGuard ab)
      (fun h ↦ HDoom cands (Bus.afterChallenge I) (input, (toAlpha ab.1, ab.2)) h) P4 εmax 0 0 :=
    fun ab ↦ if h : ab.1.length = 4 then
      Spec.congr (p := VerifierProgram.ret ab) (by simp [abGuard, h])
        ((Spec.ret (Post := P4) ab).mono (fun _ hp ↦ ⟨h, hp⟩) (fun _ _ hq ↦ hq) le_rfl le_rfl
          le_rfl)
    else Spec.congr (p := VerifierProgram.fail) (by simp [abGuard, h]) Spec.fail
  Spec.congr abProg_bind_guard ((abSpec I cands input hI hfin hcard hlt (T := 0)).bind' G)

/-- **The lvm bus phase with its four challenges recorded** (`lvmBusSpec` from `abSpec4`). -/
noncomputable def lvmBusSpec4 (vals : Vector E I.busClaims) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {Lk : ℝ≥0∞} (hLk : Lk ≤ εmax) :
    Spec (lvmBusProg I.μBus) (HDoom cands (Seam.commit I) input)
      (fun b h ↦ b.alphas.length = 4 ∧ LBusAt I hI cands input vals b h) εmax
      (abError I L₀ + 0) Lk :=
  (abSpec4 I hI cands input hfin hcard hab).bind' fun ab ↦
    if h4 : ab.1.length = 4 then
      ((gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam).mono
        (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun r ↦
        let P : List Ev → Prop := fun h ↦ r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
            HDoom cands (Seam.bus I) (lbusStmt I hI input ⟨ab.1, ab.2, r.2.1, r.2.2⟩ vals) h
        (Spec.require (T := 0) (Post := fun _ h ↦ P h)
          fun _ hp hc ↦ by
            obtain ⟨hl, hv, W, hW, hR⟩ := hp.resolve_left hc
            exact ⟨hl, hv, W, hW, values_keep I hI hR vals⟩).bind' fun _ ↦
        (Spec.readE (Post := fun _ h ↦ P h)
          (fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩) hLk).bind' fun _ ↦
        (Spec.require (Post := fun _ h ↦ P h) fun _ hp _ ↦ hp).bind' fun _ ↦
        (Spec.ret (Post := fun b h ↦ b.alphas.length = 4 ∧ LBusAt I hI cands input vals b h)
          _).mono (fun _ hp ↦ ⟨h4, hp⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else specOfFalse fun _ hp ↦ h4 hp.1

end Spec4

/-! ## The bus phase and the table sumcheck at the lvm instance, no fidelity hypothesis -/

section Spec

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)
  (cands : Word → Set (∀ i, TheOracle (inst L tabs hτ) i)) {εmax : ℝ≥0∞}

theorem width_pos_vTables (hw : ∀ t ∈ tabs, 0 < t.w) : ∀ t ∈ vTables tabs, 0 < t.width := by
  intro t ht
  simp only [vTables, zipIdx_eq_finRange, List.map_map, List.mem_map] at ht
  obtain ⟨j, -, rfl⟩ := ht
  simp only [Function.comp_apply, width_vTable]
  exact hw _ (List.get_mem _ _)

/-- **The lvm bus phase, then the table sumcheck, with no fidelity hypothesis**: from the
commitment's doom to the table seam on the wire, for the program objects of `LvmM3Fid`. Only the
side conditions (every table reads or seeds, at most thirteen value limbs, positive widths, a
nonzero bus depth) and the errors of `lvmBusTableSpec` remain. -/
noncomputable def lbusTableSpec (hkey : KeysOk tabs) (hw : ∀ t ∈ tabs, 0 < t.w) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lvmBusTableProg (vTables tabs) (vLayout tabs) (inst L tabs hτ).μBus (busResV tabs))
      (HDoom cands (Seam.commit (inst L tabs hτ)) ())
      (TablePost (inst L tabs hτ) cands () (colOfL L tabs hτ)) εmax
      (abError (inst L tabs hτ) L₀ + 0) T :=
  (lvmBusSpec4 (inst L tabs hτ) (condOf L tabs hτ hsc) cands () (vals0 L tabs hτ) hfin hcard hμ
      hab he4 hT hlam hxi).bind
    (fun b ↦ if hb : b.alphas.length = 4 ∧ b.point.length = (inst L tabs hτ).μBus ∧
        b.values.length = 3 then
      (tablePhaseSpecG (vTables tabs) (inst L tabs hτ) cands (vLayout tabs) (colOfL L tabs hτ)
        (sOf L tabs hτ hsc b) (busResV tabs b) (tableFidL L tabs hτ hsc hkey b hb.1 hb.2.1)
        (width_pos_vTables tabs hw) le_rfl hfin hcard he3 hTf).mono
        (fun _ hp ↦ hp.2.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else specOfFalse fun _ hp ↦ hb ⟨hp.1, hp.2.1, hp.2.2.1⟩)

end Spec

/-! ## Non-vacuity -/

/-- A one-row table seeding one cell (an input array's shape). -/
def seedTab : Tab where
  τ := 0
  cols := [.com false 0, .com false 1]
  cons := []
  reads := []
  seeds := [(⟨0, CPoly.var 1, [CPoly.var 0]⟩, 0)]
  deg := by
    refine ⟨fun C hC ↦ by simp at hC, fun r hr ↦ by simp at hr, fun s hs ↦ ?_⟩
    simp only [List.mem_singleton] at hs; subst hs
    refine ⟨fun m hm ↦ by simp [CPoly.var] at hm; subst hm; simp, fun P hP ↦ ?_⟩
    simp only [List.mem_singleton] at hP; subst hP
    intro m hm; simp [CPoly.var] at hm; subst hm; simp

/-- **Non-vacuity of `lbusTableSpec`'s side conditions**: a seeding table meets them. -/
theorem seedTab_conditions : AllSc [seedTab] ∧ KeysOk [seedTab] ∧ ∀ t ∈ [seedTab], 0 < t.w := by
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩ <;> simp only [List.mem_singleton] at ht <;>
    subst ht
  · exact Or.inr (by simp [seedTab])
  · exact ⟨fun r hr ↦ by simp [seedTab] at hr, fun s hs ↦ by simp [seedTab] at hs; subst hs; simp⟩
  · simp [seedTab, Tab.w]

end Lvm.M3
