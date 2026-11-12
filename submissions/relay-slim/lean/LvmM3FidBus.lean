-- adapted from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TableFidLeanIsaBus.lean` (formal
-- rev 40f877dc): `formAt_append`, `formAt_flatMap`, `formAt_form`, `evalRow_oneRow`,
-- `fingerprintWeights_toAlpha`, `sum_zipIdx`; new for lvm (WP-9b): the lvm instance's leaf
-- decomposition is the program's (`busResV`, `LvmM3Fid`): `totals_busResV`, `formAt_busResV`.
import LvmM3Fid
import LvmFrontBusStack
import LvmFrontEqKernel

/-!
# The lvm bus result is the protocol's

For the lvm instance `I = inst L tabs hτ` with every table a sumcheck table (`AllSc`), at a read of
the bus phase with four fingerprint challenges, the GKR point on `μ_bus` coordinates and three
values:

* `totals_busResV`: the program's side totals `v + 1 + Σ_b w_b` are the protocol's
  (`Bus.total`: no boundary block, and no padding row since `rows = 2^τ`, so no public part);
* `formAt_busResV`: the program's form of a side and a table, evaluated at the table's values, is the
  protocol's (`Bus.forms`), when every message has at most thirteen value limbs (`KeysOk`).

The program's blocks are the protocol's sources in order (`sideBlocksV_eq`, through `vsrc`), its
stacking is the protocol's sorted layout (`stackBlocksV_eq`, `sum_sides`), its block weight
`eq_above` is the selector weight (`eqAbove_eq_selectorWeight`), and a block's leaf form is its
flush's fingerprint form (`formAt_src`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front
open CompPoly CMlPolynomialEval
open LeanVM.Protocol.TableSumcheck (formAt evalRow)

/-! ## Sums and forms over `E` -/

theorem foldl_add_E (a : E) (l : List E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := by
  rw [sumE, foldl_add_E, zero_add]

theorem foldl_mul_col (col : ℕ → E) (c : E) (l : List ℕ) :
    l.foldl (fun acc i ↦ acc * col i) c = c * (l.map col).prod := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- A form's value: `Σ c · Π column(i)`. -/
theorem evaluate_eq (f : Form) (col : ℕ → E) :
    f.evaluate col = (f.terms.map fun t ↦ t.2 * (t.1.map col).prod).sum := by
  rw [Form.evaluate, sumE_eq_sum]
  exact congrArg List.sum (List.map_congr_left fun t _ ↦ foldl_mul_col col t.2 t.1)

theorem evaluate_append (a b : List (List ℕ × E)) (col : ℕ → E) :
    (⟨a ++ b⟩ : Form).evaluate col = (⟨a⟩ : Form).evaluate col + (⟨b⟩ : Form).evaluate col := by
  simp only [evaluate_eq, List.map_append, List.sum_append]

theorem evaluate_flatMap {X : Type} (g : X → List (List ℕ × E)) (col : ℕ → E) (l : List X) :
    (⟨l.flatMap g⟩ : Form).evaluate col = (l.map fun x ↦ (⟨g x⟩ : Form).evaluate col).sum := by
  induction l with
  | nil => simp [evaluate_eq]
  | cons x l ih => rw [List.flatMap_cons, evaluate_append, ih, List.map_cons, List.sum_cons]

theorem evaluate_scale (w : E) (ts : List (List ℕ × E)) (col : ℕ → E) :
    (⟨ts.map fun t ↦ (t.1, w * t.2)⟩ : Form).evaluate col = w * (⟨ts⟩ : Form).evaluate col := by
  simp only [evaluate_eq, List.map_map, Function.comp_def, ← List.sum_map_mul_left, mul_assoc]

/-- A table's bucket on a side, evaluated: its blocks' weighted values. -/
theorem evaluate_bucketV (s : List (VBlock × E)) (j : ℕ) (col : ℕ → E) :
    (⟨bucketV s j⟩ : Form).evaluate col =
      (s.map fun bw ↦ bw.2 * if bw.1.tab = j then bw.1.form.evaluate col else 0).sum := by
  rw [bucketV, evaluate_flatMap, List.map_reverse, List.sum_reverse]
  induction s with
  | nil => simp
  | cons bw s ih =>
    by_cases h : bw.1.tab = j
    · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, ih,
        List.map_cons, List.sum_cons, if_pos h, evaluate_scale]
    · rw [List.filter_cons_of_neg (by simpa using h), ih, List.map_cons, List.sum_cons, if_neg h,
        mul_zero, zero_add]

/-- The value of a `CPoly` at a row. -/
theorem evalV_eq (v : ℕ → E) (P : CPoly) :
    CPoly.evalV v P = (P.map fun m ↦ kE m.1 * (m.2.map v).prod).sum := by
  rw [CPoly.evalV, foldl_add_E, zero_add]
  refine congrArg List.sum (List.map_congr_left fun m _ ↦ ?_)
  rw [← List.prod_eq_foldl]

theorem evaluate_cpolyFormV (w : E) (P : CPoly) (col : ℕ → E) :
    (cpolyFormV w P).evaluate col = w * CPoly.evalV col P := by
  rw [cpolyFormV, evaluate_eq, evalV_eq, List.map_map, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun m _ ↦ by simp [mul_assoc])

theorem evaluate_const (c : E) (col : ℕ → E) : (Form.const c).evaluate col = c := by
  simp [Form.const, evaluate_eq]

theorem evaluate_formSumV (fs : List Form) (col : ℕ → E) :
    (formSumV fs).evaluate col = (fs.map (·.evaluate col)).sum := by
  rw [formSumV, evaluate_flatMap]

/-- A sum over a list with its indices is a sum over the indices. -/
theorem sum_zipIdx {α : Type} (g : ℕ → α → E) (d : α) :
    ∀ (l : List α) (n : ℕ), ((l.zipIdx n).map fun x ↦ g x.2 x.1).sum =
      ∑ k ∈ Finset.range l.length, g (n + k) (l.getD k d)
  | [], _ => by simp
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx g d l (n + 1),
      List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ ↦ by rw [add_assoc, add_comm 1 k])
      rfl

/-- **A leaf form's value**: `β + eq(α,0)·sep + eq(α,1)·addr + eq(α,2)·cnt + Σ_l eq(α,3+l)·val_l`. -/
theorem evaluate_leafFormV (eqα : List E) (β : E) (k : Key) (cnt : CPoly) (col : ℕ → E) :
    (leafFormV eqα β k cnt).evaluate col = β + eqα.getD 0 0 * kE k.sep +
      eqα.getD 1 0 * CPoly.evalV col k.addr + eqα.getD 2 0 * CPoly.evalV col cnt +
      ∑ l ∈ Finset.range k.val.length, eqα.getD (3 + l) 0 * CPoly.evalV col (k.val.getD l []) := by
  rw [leafFormV, evaluate_formSumV, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, evaluate_const,
    evaluate_cpolyFormV, add_zero, List.map_map, Function.comp_def]
  rw [sum_zipIdx (fun l P ↦ eqα.getD (3 + l) 0 * CPoly.evalV col P) [] k.val 0]
  simp only [zero_add]
  ring

/-! ## The instance -/

section Inst

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- Every table of the instance is a sumcheck table. -/
theorem sumcheckTable_of (hsc : AllSc tabs) (j : Fin tabs.length) :
    (inst L tabs hτ).SumcheckTable j := by
  right; left
  show (tabs.get j).flushes ≠ []
  have hl : (tabs.get j).flushes.length =
      2 * (tabs.get j).reads.length + 2 * (tabs.get j).seeds.length := by
    simp [Tab.flushes]; ring
  apply List.ne_nil_of_length_pos
  rw [hl]
  rcases hsc (tabs.get j) (List.get_mem _ _) with h | h
  · have := List.length_pos_of_ne_nil h; omega
  · have := List.length_pos_of_ne_nil h; omega

/-- The bus conditions of the instance when every table is a sumcheck table. -/
theorem condOf (hsc : AllSc tabs) : Bus.Conditions (inst L tabs hτ) :=
  inst_conditions L tabs hτ fun t ht _ ↦ hsc t ht

end Inst

/-! ## A table's flushes, as keys and counts -/

/-- A table's flushes: side, key and count, in `Tab.flushes`' order. -/
def Tab.kcs (t : Tab) : List (Side × Key × CPoly) :=
  t.reads.map (fun r ↦ (.pull, r.1, CPoly.var r.2)) ++
    t.reads.map (fun r ↦ (.push, r.1, [(FK.x, [r.2])])) ++
    t.seeds.map (fun s ↦ (.push, s.1, CPoly.const 1)) ++
    t.seeds.map (fun s ↦ (.pull, s.1, CPoly.var s.2))

theorem flushes_eq_kcs (t : Tab) : t.flushes = t.kcs.map fun x ↦ (x.1, x.2.1.vec t.w x.2.2) := by
  simp [Tab.flushes, Tab.kcs, Tab.readVec, Tab.bumpVec, Tab.seedVec, Tab.finVec,
    Function.comp_def]

theorem length_kcs (t : Tab) : t.kcs.length = t.flushes.length := by
  rw [flushes_eq_kcs, List.length_map]

/-- The default key and count. -/
def kc0 : Side × Key × CPoly := (.push, ⟨0, [], []⟩, [])

/-- Flush `f` of a table is its key's message at its count. -/
theorem flushes_getElem (t : Tab) (f : ℕ) (hf : f < t.flushes.length) :
    t.flushes[f] = ((t.kcs.getD f kc0).1, (t.kcs.getD f kc0).2.1.vec t.w (t.kcs.getD f kc0).2.2) := by
  have hf' : f < t.kcs.length := by rw [length_kcs]; exact hf
  simp only [List.getElem_of_eq (flushes_eq_kcs t) hf, List.getElem_map,
    List.getD_eq_getElem _ _ hf']

/-- The filtered indices of a list, read back through `getD`. -/
theorem filter_finRange_getD {A B : Type} (p : A → Bool) (G : A → B) (d : A) :
    ∀ (l : List A), ((List.finRange l.length).filter fun i ↦ p (l.getD i.val d)).map
      (fun i ↦ G (l.getD i.val d)) = (l.filter p).map G
  | [] => rfl
  | a :: l => by
    have ih := filter_finRange_getD p G d l
    rw [List.length_cons, List.finRange_succ, List.filter_cons, List.filter_map]
    have e1 : ((fun i : Fin (l.length + 1) ↦ p ((a :: l).getD i.val d)) ∘ Fin.succ) =
        fun i : Fin l.length ↦ p (l.getD i.val d) := funext fun _ ↦ rfl
    have e2 : ((fun i : Fin (l.length + 1) ↦ G ((a :: l).getD i.val d)) ∘ Fin.succ) =
        fun i : Fin l.length ↦ G (l.getD i.val d) := funext fun _ ↦ rfl
    have e0 : (a :: l).getD (0 : Fin (l.length + 1)).val d = a := rfl
    rw [e1, e0]
    by_cases h : p a
    · rw [if_pos h, List.map_cons, List.map_map, e2, ih, List.filter_cons_of_pos h, List.map_cons, e0]
    · rw [if_neg h, List.map_map, e2, ih, List.filter_cons_of_neg h]

theorem zipIdx_eq_finRange {α : Type} (l : List α) :
    l.zipIdx = (List.finRange l.length).map fun j ↦ (l.get j, j.val) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_zipIdx]

/-! ## The program's blocks are the protocol's sources -/

section Sources

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (eqα : List E) (β : E)

/-- **The program's block of a source** of the lvm instance. -/
def vsrc : Bus.Source (inst L tabs hτ) → VBlock
  | .boundary b => ⟨0, b.κ, {}⟩
  | .flush j f => ⟨j.val, (tabs.get j).τ,
      leafFormV eqα β ((tabs.get j).kcs.getD f.val kc0).2.1 ((tabs.get j).kcs.getD f.val kc0).2.2⟩
  | .count j c => ⟨j.val, (tabs.get j).τ, Form.col c.val⟩

theorem vsrc_κ (s : Bus.Source (inst L tabs hτ)) : (vsrc L tabs hτ eqα β s).κ = s.κ := by
  cases s <;> rfl

/-- Table `j`'s flushes of side `s`, as the program's blocks. -/
theorem side_map_vsrc (s : Side) (j : Fin tabs.length) :
    (((List.finRange ((inst L tabs hτ).flushes j).length).filter fun f ↦
        decide (((inst L tabs hτ).flushes j)[f].1 = s)).map (Bus.Source.flush j)).map
      (vsrc L tabs hτ eqα β) =
    ((tabs.get j).kcs.filter fun x ↦ decide (x.1 = s)).map fun x ↦
      (⟨j.val, (tabs.get j).τ, leafFormV eqα β x.2.1 x.2.2⟩ : VBlock) := by
  rw [List.map_map]
  have hlen : ((inst L tabs hτ).flushes j).length = (tabs.get j).kcs.length :=
    (length_kcs _).symm
  have key := filter_finRange_getD (fun x : Side × Key × CPoly ↦ decide (x.1 = s))
    (fun x ↦ (⟨j.val, (tabs.get j).τ, leafFormV eqα β x.2.1 x.2.2⟩ : VBlock)) kc0 (tabs.get j).kcs
  rw [← key]
  have : ∀ (n m : ℕ) (h : n = m) (P : Fin n → Bool) (Q : Fin m → Bool) (F : Fin n → VBlock)
      (G : Fin m → VBlock), (∀ i, P i = Q (Fin.cast h i)) → (∀ i, F i = G (Fin.cast h i)) →
      ((List.finRange n).filter P).map F = ((List.finRange m).filter Q).map G := by
    intro n m h P Q F G hP hF
    subst h
    have hP' : P = Q := funext fun i ↦ hP i
    have hF' : F = G := funext fun i ↦ hF i
    rw [hP', hF']
  refine this _ _ hlen _ _ _ _ (fun f ↦ ?_) (fun f ↦ rfl)
  show decide ((((tabs.get j).flushes)[f.val]'f.isLt).1 = s) = _
  rw [flushes_getElem]
  rfl

theorem kcs_push (t : Tab) : (t.kcs.filter fun x ↦ decide (x.1 = Side.push)) =
    t.reads.map (fun r ↦ (.push, r.1, [(FK.x, [r.2])])) ++
      t.seeds.map (fun s ↦ (.push, s.1, CPoly.const 1)) := by
  simp [Tab.kcs, List.filter_append, List.filter_map, Function.comp_def]

theorem kcs_pull (t : Tab) : (t.kcs.filter fun x ↦ decide (x.1 = Side.pull)) =
    t.reads.map (fun r ↦ (.pull, r.1, CPoly.var r.2)) ++
      t.seeds.map (fun s ↦ (.pull, s.1, CPoly.var s.2)) := by
  simp [Tab.kcs, List.filter_append, List.filter_map, Function.comp_def]

/-- **The program's blocks of a side are the protocol's sources**, in order. -/
theorem sideBlocksV_eq :
    sideBlocksV tabs eqα β = [(Bus.sources (inst L tabs hτ) 0).map (vsrc L tabs hτ eqα β),
      (Bus.sources (inst L tabs hτ) 1).map (vsrc L tabs hτ eqα β),
      (Bus.sources (inst L tabs hτ) 2).map (vsrc L tabs hτ eqα β)] := by
  have hb : (inst L tabs hτ).boundary = [] := rfl
  simp only [sideBlocksV, Bus.sources, Bus.sideSources, Bus.countSources, hb, List.filter_nil,
    List.map_nil, List.nil_append, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, List.map_flatMap, zipIdx_eq_finRange, List.flatMap_map]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [side_map_vsrc, kcs_push]
    simp [Function.comp_def]
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [side_map_vsrc, kcs_pull]
    simp [Function.comp_def]
  · refine congrArg (List.flatMap · _) (funext fun j ↦ ?_)
    rw [List.map_map]
    rfl

end Sources

/-! ## Stacking -/

/-- `stackBlocksV`'s fold: each block at the sum of the heights before it. -/
theorem stack_fold (l : List VBlock) (acc : List (VBlock × ℕ)) (o : ℕ) :
    l.foldl (fun (acc : List (VBlock × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
        (acc, o) =
      (acc ++ l.mapIdx (fun i b ↦ (b, o + ((l.take i).map fun b ↦ 2 ^ b.κ).sum)),
        o + (l.map fun b ↦ 2 ^ b.κ).sum) := by
  induction l generalizing acc o with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    simp only [List.mapIdx_cons, List.take_zero, List.map_nil, List.sum_nil, add_zero,
      List.take_succ_cons, List.map_cons, List.sum_cons, List.append_assoc, List.singleton_append,
      Prod.mk.injEq, add_assoc, true_and]

/-- A sum over a `mapIdx`, as a sum over the positions. -/
theorem sum_map_mapIdx {X Y : Type} (g : Y → E) :
    ∀ (l : List X) (f : ℕ → X → Y), ((l.mapIdx f).map g).sum = ∑ i : Fin l.length, g (f i l[i])
  | [], _ => by simp
  | a :: l, f => by
    rw [List.mapIdx_cons, List.map_cons, List.sum_cons, sum_map_mapIdx g l]
    exact (Fin.sum_univ_succ (n := l.length) (fun i ↦ g (f i (a :: l)[i]))).symm

/-- **A weighted sum over a side's stacked blocks** is the protocol's sum over its sorted blocks,
each at its selector weight. -/
theorem sum_stack {I : M3Instance} (hI : Bus.Conditions I) (k : Fin 3)
    (φ : Bus.Source I → VBlock) (hφ : ∀ s, (φ s).κ = s.κ) (point : List E)
    (hp : point.length = I.μBus) (G : VBlock → E) :
    (((stackBlocksV ((Bus.sources I k).map φ)).map fun bo ↦
        (bo.1, blockWeightV point bo.1.κ bo.2)).map fun bw ↦ bw.2 * G bw.1).sum =
      ∑ b : Fin (Bus.blocks I k).n, Bus.weight hI k b (vecOf I.μBus point) *
        G (φ (Bus.src I k b)) := by
  have hsort : ((Bus.sources I k).map φ).mergeSort (fun a b ↦ decide (b.κ ≤ a.κ)) =
      (Bus.sorted I k).map φ :=
    (List.map_mergeSort (fun a _ b _ ↦ by simp only [hφ])).symm
  have hstack : stackBlocksV ((Bus.sources I k).map φ) = ((Bus.sorted I k).map φ).mapIdx
      fun i b ↦ (b, ((((Bus.sorted I k).map φ).take i).map fun b ↦ 2 ^ b.κ).sum) := by
    rw [stackBlocksV, hsort, stack_fold]
    simp
  rw [hstack, List.map_map, sum_map_mapIdx]
  have hn : ((Bus.sorted I k).map φ).length = (Bus.blocks I k).n := by
    rw [List.length_map]; rfl
  refine Fintype.sum_equiv (finCongr hn) _ _ fun i ↦ ?_
  simp only [Function.comp_apply, List.getElem_map, finCongr_apply]
  congr 1
  have hoff : ((((Bus.sorted I k).map φ).take i.val).map fun b ↦ 2 ^ b.κ).sum =
      (Bus.blocks I k).offset (Fin.cast hn i) := by
    rw [Blocks.offset, offsetNat_sortedL (Bus.sources I k) Bus.Source.κ (Bus.blocks I k) rfl
      (fun _ ↦ rfl) _ (by simp only [Fin.val_cast]; omega), ← List.map_take, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun a _ ↦ by simp [hφ])
  have hκ : ((Bus.sorted I k).map φ)[i].κ = (Bus.blocks I k).size (Fin.cast hn i) := by
    simp only [Fin.getElem_fin, List.getElem_map, hφ]
    rfl
  have h := eqAbove_eq_selectorWeight (Bus.blocks I k) (hI.fits k) (Fin.cast hn i)
    (vecOf I.μBus point)
  rw [toList_vecOf point hp] at h
  rw [hoff, blockWeightV, hκ, h]
  simp only [Fin.getElem_fin, List.getElem_map]
  rfl

/-! ## Row polynomials at values in `E` -/

/-- Values of a table's `n` columns, read by index with zeros past the width (leanVM `rowE`). -/
def rowE {n : ℕ} (e : Fin n → E) : ℕ → E := fun i ↦ if h : i < n then e ⟨i, h⟩ else 0

theorem eval₂_xv {w : ℕ} (e : Fin w → E) (i : ℕ) :
    MvPolynomial.eval₂ (algebraMap K E) e (CPoly.xv w i) = rowE e i := by
  unfold CPoly.xv rowE; split <;> simp

/-- **A `CPoly` as a row polynomial**, at values in `E`, is its value at the row. -/
theorem eval₂_toMv {w : ℕ} (e : Fin w → E) (P : CPoly) :
    MvPolynomial.eval₂ (algebraMap K E) e (CPoly.toMv w P) = CPoly.evalV (rowE e) P := by
  rw [evalV_eq]
  have h : ∀ q, MvPolynomial.eval₂ (algebraMap K E) e q =
      MvPolynomial.eval₂Hom (algebraMap K E) e q := fun _ ↦ rfl
  rw [h]
  unfold CPoly.toMv
  induction P with
  | nil => simp
  | cons m P ih =>
    rw [List.map_cons, List.sum_cons, map_add, ih, List.map_cons, List.sum_cons, map_mul,
      MvPolynomial.eval₂Hom_C, map_list_prod, List.map_map]
    congr 2
    exact congrArg List.prod (List.map_congr_left fun i _ ↦ eval₂_xv e i)

/-! ## Forms of the protocol (leanVM `TableFidLeanIsaBus`, generic part) -/

section Generic

variable {I : M3Instance}

/-- `formAt` of a concatenation is the sum of the parts'. -/
theorem formAt_append {j : Fin I.ntab} (a b : I.Form j) (e : Fin (I.width j) → E) :
    formAt (a ++ b) e = formAt a e + formAt b e := by
  simp [formAt]

/-- `formAt` of a `flatMap` is the sum of the pieces'. -/
theorem formAt_flatMap {α : Type} {j : Fin I.ntab} (g : α → I.Form j) (e : Fin (I.width j) → E) :
    ∀ l : List α, formAt (l.flatMap g) e = (l.map fun x ↦ formAt (g x) e).sum
  | [] => by simp [formAt]
  | x :: l => by rw [List.flatMap_cons, formAt_append, formAt_flatMap g e l]; simp

/-- The constant row `1` evaluates to `1`. -/
theorem evalRow_oneRow (j : Fin I.ntab) (e : Fin (I.width j) → E) :
    evalRow (Bus.oneRow j).1 e = 1 := by
  simp [evalRow, Bus.oneRow]

/-- **A block's form is linear in its weight.** -/
theorem formAt_form (src : Bus.Source I) (hd : 1 ≤ I.d) (w : E) (α : Fin 4 → E) (β : E)
    (j : Fin I.ntab) (e : Fin (I.width j) → E) :
    formAt (src.form hd w α β j) e = w * formAt (src.form hd 1 α β j) e := by
  cases src with
  | boundary b => simp [Bus.Source.form, formAt]
  | flush j' f =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, Bus.flushForm, formAt, List.map_cons, List.sum_cons,
        List.map_map, Function.comp_def]
      rw [mul_add, ← List.sum_map_mul_left]
      exact congrArg₂ (· + ·) (by ring) (congrArg List.sum (List.map_congr_left fun i _ ↦ by ring))
    · simp [Bus.Source.form, hj, formAt]
  | count j' c =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, Bus.countForm, formAt, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      ring
    · simp [Bus.Source.form, hj, formAt]

/-- The protocol's form of a side and a sumcheck table, evaluated: the sum over the sorted blocks
of the selector weight times the block's form at weight `1`. -/
theorem formAt_forms (hI : Bus.Conditions I) (k : Fin 3) (α : Fin 4 → E) (β : E)
    (ζ : Vector E I.μBus) (j : I.SumcheckTables) (e : Fin (I.width j.1) → E) :
    formAt (Bus.forms hI k α β ζ j) e = ∑ b : Fin (Bus.blocks I k).n, Bus.weight hI k b ζ *
      formAt ((Bus.src I k b).form hI.one_le_d 1 α β j.1) e := by
  rw [Bus.forms, formAt_flatMap, ← Fin.sum_univ_def]
  exact Finset.sum_congr rfl fun b _ ↦ formAt_form _ _ _ _ _ _ _

end Generic

/-- The wire's weights are the protocol's fingerprint weights, for four `α`. -/
theorem fingerprintWeights_toAlpha {alphas : List E} (ha : alphas.length = 4) (k : Fin 16) :
    (fingerprintWeights (toAlpha alphas))[k.val] = (eqKernel alphas).getD k 0 := by
  have h := lagrangeBasis_ofFn_getD ha k
  rw [List.getD_eq_getElem _ _ (by rw [Whir.Complete.length_eqKernel, ha]; exact k.isLt)]
  exact h

/-- A flush's form at weight `1`: `β + Σ_i eq(α, i)·coord_i` (characteristic two). -/
theorem formAt_flushForm {I : M3Instance} (j : Fin I.ntab) (f : Fin (I.flushes j).length)
    (α : Fin 4 → E) (β : E) (e : Fin (I.width j) → E) :
    formAt (Bus.flushForm j f 1 α β) e = β + ∑ i : Fin 16, (fingerprintWeights α)[i.val] *
      MvPolynomial.eval₂ (algebraMap K E) e (Bus.flushPolys j f)[i] := by
  simp only [Bus.flushForm, formAt, List.map_cons, List.sum_cons, List.map_map, evalRow_oneRow,
    one_mul, mul_one]
  rw [Fin.sum_univ_def]
  refine congrArg (β + ·) (congrArg List.sum (List.map_congr_left fun i _ ↦ ?_))
  simp only [Function.comp_apply, evalRow, CharTwo.neg_eq]

/-! ## A message's coordinates -/

/-- Coordinate `i` of the message with key `k` and count `cnt`, at a row of `E` values. -/
def kvV (k : Key) (cnt : CPoly) (v : ℕ → E) (i : ℕ) : E :=
  if i = 0 then kE k.sep else if i = 1 then CPoly.evalV v k.addr
  else if i = 2 then CPoly.evalV v cnt else CPoly.evalV v (k.val.getD (i - 3) [])

theorem eval₂_vec {w : ℕ} (k : Key) (cnt : CPoly) (e : Fin w → E) (i : Fin 16) :
    MvPolynomial.eval₂ (algebraMap K E) e (k.vec w cnt)[i] = kvV k cnt (rowE e) i := by
  simp only [Key.vec, Fin.getElem_fin, Vector.getElem_ofFn, kvV]
  split_ifs <;> first | rfl | (rw [MvPolynomial.eval₂_C]; rfl) | exact eval₂_toMv e _

theorem evalV_nil (v : ℕ → E) : CPoly.evalV v [] = 0 := by simp [CPoly.evalV]

/-- **The sixteen weighted coordinates** of a message with at most thirteen value limbs. -/
theorem sum_kvV (eqα : List E) (k : Key) (cnt : CPoly) (v : ℕ → E) (hk : k.val.length ≤ 13) :
    ∑ i : Fin 16, eqα.getD i 0 * kvV k cnt v i = eqα.getD 0 0 * kE k.sep +
      eqα.getD 1 0 * CPoly.evalV v k.addr + eqα.getD 2 0 * CPoly.evalV v cnt +
      ∑ l ∈ Finset.range k.val.length, eqα.getD (3 + l) 0 * CPoly.evalV v (k.val.getD l []) := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ eqα.getD i 0 * kvV k cnt v i) 16,
    Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have h13 : ∑ i ∈ Finset.range 13, eqα.getD (i + 1 + 1 + 1) 0 * kvV k cnt v (i + 1 + 1 + 1) =
      ∑ l ∈ Finset.range k.val.length, eqα.getD (3 + l) 0 * CPoly.evalV v (k.val.getD l []) := by
    rw [← Finset.sum_range_add_sum_Ico _ hk]
    have hz : ∑ i ∈ Finset.Ico k.val.length 13,
        eqα.getD (i + 1 + 1 + 1) 0 * kvV k cnt v (i + 1 + 1 + 1) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        have hi' := (Finset.mem_Ico.mp hi).1
        simp only [kvV, show i + 1 + 1 + 1 - 3 = i by omega,
          List.getD_eq_default _ _ hi', evalV_nil]
        simp
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show i + 1 + 1 + 1 = 3 + i by omega]
    simp only [kvV, if_neg (by omega : 3 + i ≠ 0), if_neg (by omega : 3 + i ≠ 1),
      if_neg (by omega : 3 + i ≠ 2), show 3 + i - 3 = i by omega]
  rw [h13]
  simp only [kvV]
  simp
  ring

/-- The default key has no value limb. -/
theorem kcs_getD_val (t : Tab) (hk : (∀ r ∈ t.reads, r.1.val.length ≤ 13) ∧
    ∀ s ∈ t.seeds, s.1.val.length ≤ 13) (f : ℕ) : (t.kcs.getD f kc0).2.1.val.length ≤ 13 := by
  by_cases hf : f < t.kcs.length
  · rw [List.getD_eq_getElem _ _ hf]
    have hm := List.getElem_mem hf
    generalize t.kcs[f] = x at hm ⊢
    simp only [Tab.kcs, List.mem_append, List.mem_map] at hm
    rcases hm with (((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩)
    · exact hk.1 r hr
    · exact hk.1 r hr
    · exact hk.2 s hs
    · exact hk.2 s hs
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [kc0]

/-- Every message of the tables has at most thirteen value limbs (sixteen coordinates). -/
def KeysOk (tabs : List Tab) : Prop :=
  ∀ t ∈ tabs, (∀ r ∈ t.reads, r.1.val.length ≤ 13) ∧ ∀ s ∈ t.seeds, s.1.val.length ≤ 13

/-! ## The program's blocks' forms are the protocol's -/

section Result

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **A source's form at weight `1` is its program block's**, on the block's table. -/
theorem formAt_src (hkey : KeysOk tabs) {alphas : List E} (ha : alphas.length = 4) (β : E)
    (hd : 1 ≤ (inst L tabs hτ).d) (s : Bus.Source (inst L tabs hτ)) (j : Fin tabs.length)
    (e : Fin ((inst L tabs hτ).width j) → E) :
    formAt (s.form hd 1 (toAlpha alphas) β j) e =
      if (vsrc L tabs hτ (eqKernel alphas) β s).tab = j.val then
        (vsrc L tabs hτ (eqKernel alphas) β s).form.evaluate (rowE e) else 0 := by
  cases s with
  | boundary b => simp [Bus.Source.form, formAt, vsrc, evaluate_eq]
  | flush j' f =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, vsrc, if_true]
      rw [formAt_flushForm, evaluate_leafFormV]
      have hfp : Bus.flushPolys (I := inst L tabs hτ) j' f =
          ((tabs.get j').kcs.getD f.val kc0).2.1.vec (tabs.get j').w
            ((tabs.get j').kcs.getD f.val kc0).2.2 := by
        show ((tabs.get j').flushes[f.val]'f.isLt).2 = _
        rw [flushes_getElem]
      rw [hfp]
      simp only [eval₂_vec, fingerprintWeights_toAlpha ha]
      rw [sum_kvV _ _ _ _ (kcs_getD_val _ (hkey _ (List.get_mem _ _)) _)]
      ring
    · have hj' : j'.val ≠ j.val := fun h ↦ hj (Fin.ext h)
      simp [Bus.Source.form, hj, formAt, vsrc, hj']
  | count j' c =>
    by_cases hj : j' = j
    · subst hj
      simp only [Bus.Source.form, dite_true, Bus.countForm, formAt, vsrc, if_true, evaluate_eq,
        Form.col, gpow, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero,
        one_mul, add_zero, List.prod_cons, List.prod_nil, mul_one]
      simp [evalRow, rowE]
    · have hj' : j'.val ≠ j.val := fun h ↦ hj (Fin.ext h)
      simp [Bus.Source.form, hj, formAt, vsrc, hj']

/-- A side's weighted program blocks. -/
theorem sidesV_getD (alphas : List E) (β : E) (point : List E) (k : Fin 3) :
    (sidesV tabs alphas β point).getD k [] =
      (stackBlocksV ((Bus.sources (inst L tabs hτ) k).map
        (vsrc L tabs hτ (eqKernel alphas) β))).map fun bo ↦ (bo.1, blockWeightV point bo.1.κ bo.2) := by
  rw [sidesV, sideBlocksV_eq L tabs hτ]
  fin_cases k <;> rfl

/-- The lvm instance's sources are its tables' flushes and count columns. -/
theorem not_boundary (k : Fin 3) (s : Bus.Source (inst L tabs hτ)) (hs : s ∈ Bus.sources _ k)
    (b : BoundaryBlock (inst L tabs hτ).toShape) : s ≠ .boundary b := by
  rintro rfl
  have hb : (inst L tabs hτ).boundary = [] := rfl
  fin_cases k <;>
    simp [Bus.sources, Bus.sideSources, Bus.countSources, hb] at hs

/-- A table block's public part vanishes: no padding row (`rows = 2^τ`). -/
theorem publicValue_zero (α : Fin 4 → E) (β : E) (vals : Vector E (inst L tabs hτ).busClaims)
    (s : Bus.Source (inst L tabs hτ)) (hs : ∀ b, s ≠ .boundary b) (z : Vector E s.κ) :
    s.publicValue α β vals z = 0 := by
  have hpw : ∀ (m : ℕ) (z : Vector E m), Bus.padWeight (2 ^ m) z = 0 := fun m z ↦ by
    rw [Bus.padWeight, evalMle_eq_sum]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp [not_le.mpr x.isLt]
  cases s with
  | boundary b => exact absurd rfl (hs b)
  | flush j f =>
    simp only [Bus.Source.publicValue, Bus.Source.padTerm]
    exact mul_eq_zero_of_right _ (hpw _ z)
  | count j c =>
    simp only [Bus.Source.publicValue, Bus.Source.padTerm]
    exact mul_eq_zero_of_right _ (hpw _ z)

/-- **The program's side totals are the protocol's.** -/
theorem totals_busResV (hsc : AllSc tabs) (b : LBus) (hp : b.point.length = (inst L tabs hτ).μBus)
    (k : Fin 3) :
    (busResV tabs b).totals.getD k 0 =
      (lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.totals k := by
  have hI := condOf L tabs hτ hsc
  have hl : (busResV tabs b).totals.getD k 0 = b.values.getD k 0 + 1 +
      sumE (((sidesV tabs b.alphas b.beta b.point).getD k []).map (·.2)) := by
    simp only [busResV, busFinalV]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
  rw [hl, sidesV_getD L tabs hτ, sumE_eq_sum]
  have hs := sum_stack hI k (vsrc L tabs hτ (eqKernel b.alphas) b.beta)
    (vsrc_κ L tabs hτ _ _) b.point hp (fun _ ↦ 1)
  simp only [mul_one] at hs
  rw [hs]
  show _ = Bus.total _ k _ _ _ _ _
  rw [Bus.total]
  have h0 : ∀ x : Fin (Bus.blocks (inst L tabs hτ) k).n, ∀ z, (Bus.src (inst L tabs hτ) k x).publicValue (toAlpha b.alphas)
      b.beta (vals0 L tabs hτ) z = 0 := fun x z ↦
    publicValue_zero L tabs hτ _ _ _ _ (not_boundary L tabs hτ k _
      (List.mem_mergeSort.mp (List.getElem_mem _))) z
  simp only [h0, mul_zero, Finset.sum_const_zero, zero_add, CharTwo.sub_eq_add, layerStmtOf,
    valuesFn]
  ring

/-- **The program's forms are the protocol's**: the form of side `k` on table `j`, evaluated at
values `e` of the table's columns. -/
theorem formAt_busResV (hsc : AllSc tabs) (hkey : KeysOk tabs) (b : LBus)
    (ha : b.alphas.length = 4) (hp : b.point.length = (inst L tabs hτ).μBus) (k : Fin 3)
    (j : (inst L tabs hτ).SumcheckTables) (e : Fin ((inst L tabs hτ).width j.1) → E) :
    formAt ((lbusStmt (inst L tabs hτ) (condOf L tabs hτ hsc) () b (vals0 L tabs hτ)).2.forms k j) e =
      (((busResV tabs b).forms.getD j.1.val []).getD k.val {}).evaluate (rowE e) := by
  have hI := condOf L tabs hτ hsc
  have hr : ((busResV tabs b).forms.getD j.1.val []).getD k.val {} =
      ⟨bucketV ((sidesV tabs b.alphas b.beta b.point).getD k []) j.1.val⟩ := by
    have hj : (busResV tabs b).forms.getD j.1.val [] =
        (sidesV tabs b.alphas b.beta b.point).map fun s ↦ (⟨bucketV s j.1.val⟩ : Form) := by
      simp only [busResV, busFinalV]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    rw [hj, show ({} : Form) = ⟨bucketV [] j.1.val⟩ from rfl, List.getD_map]
  rw [hr, evaluate_bucketV, sidesV_getD L tabs hτ]
  have hs := sum_stack hI k (vsrc L tabs hτ (eqKernel b.alphas) b.beta)
    (vsrc_κ L tabs hτ _ _) b.point hp
    (fun vb ↦ if vb.tab = j.1.val then vb.form.evaluate (rowE e) else 0)
  rw [List.map_map] at hs ⊢
  rw [hs]
  show formAt (Bus.forms hI k _ _ _ j) e = _
  rw [formAt_forms]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [layerStmtOf]
  rw [formAt_src L tabs hτ hkey ha]

end Result

end Lvm.M3
