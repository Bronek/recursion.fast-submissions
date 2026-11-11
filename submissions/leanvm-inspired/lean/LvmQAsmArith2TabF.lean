-- New for lvm (HAR-BT): `F`'s table phase (`tabPh`) in the form the phase-3 gadget computes: the bus
-- forms' values as sums over a static stacking (`stackBlocks` of the shapes' blocks), the push and
-- pull sides merged (same stacking), block weights as `eqW` (split into a low table and a high
-- part), `BITS` output polynomials through suffix sums. Reuses WP-9b's `LvmM3FidNative`
-- (`bucketR_getD`, `sidesR`, `busFinalR_*_def`), QA2's `eqW_append`, core's `List.map_mergeSort`;
-- the rest is new (searched leanerVM `Protocol/{Bus,TableSumcheck}`, WP-9b's `LvmM3FidBus`: those
-- state the same objects over `E`, not as gadget-shaped sums).
import LvmQAsmArith2Bus
import LvmM3FidNative
import LvmQTable
import LvmQWhirBatch
import LvmBits

/-!
# Phase 3, `F` side

* **Forms** (`value_leafForm`, `value_bucketN`): a leaf form's value is
  `β + α₀·sep + α₁·addr + α₂·cnt + Σ_l α_{3+l}·val_l` at the evaluations; a side's form of table `j`
  is `Σ_b w_b · value_b` over the side's stacked blocks of table `j`.
* **Static stacking** (`stackG`, `stackBlocks_map`): `stackBlocks` of blocks that are a map of static
  blocks (`SBlk`: table, height, key, read or seed) is `stackG` of the static ones; the push and pull
  sides are maps of the same static list (`sideBlocks_eq`), so they have the same weights.
* **Weights** (`blockWeight_eqW`): `blockWeight ζ κ off = eqW (ζ.drop κ) (off >>> κ)`.
* **Geometric forms** (`geoPoly`, `evalE_geo`): `Σ_{a≤z<e} x^{z−a+d} β_z = x^d (S a + x^{e−a} S e)`
  with the suffix sums `S k = β_k + x · S (k+1)`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.M3 DM

/-! ## Sums -/

theorem foldl_add_from (l : List FE) (a : FE) : l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + x)]; ring

theorem sumE_cons (x : FE) (l : List FE) : sumE (x :: l) = x + sumE l := by
  rw [sumE, List.foldl_cons, foldl_add_from, zero_add]; rfl

theorem sumE_nil : sumE [] = 0 := rfl

theorem sumE_append (a b : List FE) : sumE (a ++ b) = sumE a + sumE b := by
  rw [sumE, List.foldl_append, foldl_add_from]; rfl

theorem sumE_reverse (l : List FE) : sumE l.reverse = sumE l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.reverse_cons, sumE_append, ih, sumE_cons, sumE_cons, sumE_nil]; ring

theorem sumE_flatMap {α : Type} (f : α → List FE) (l : List α) :
    sumE (l.flatMap f) = sumE (l.map fun a => sumE (f a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, sumE_append, ih, List.map_cons, sumE_cons]

theorem sumE_map_mul {α : Type} (w : FE) (f : α → FE) (l : List α) :
    sumE (l.map fun a => w * f a) = w * sumE (l.map f) := by
  induction l with
  | nil => simp [sumE]
  | cons a l ih => rw [List.map_cons, List.map_cons, sumE_cons, sumE_cons, ih]; ring

theorem sumE_map_add {α : Type} (f g : α → FE) (l : List α) :
    sumE (l.map fun a => f a + g a) = sumE (l.map f) + sumE (l.map g) := by
  induction l with
  | nil => simp [sumE]
  | cons a l ih => rw [List.map_cons, List.map_cons, List.map_cons, sumE_cons, sumE_cons, sumE_cons, ih]; ring

theorem foldl_mul_one (m : List FE) (a : FE) : m.foldl (· * ·) a = a * m.foldl (· * ·) 1 := by
  induction m generalizing a with
  | nil => simp
  | cons x m ihm => rw [List.foldl_cons, List.foldl_cons, ihm, ihm (1 * x)]; ring

theorem foldl_mul_from (col : Nat → FE) (c : FE) (l : List Nat) :
    l.foldl (fun acc i => acc * col i) c = c * (l.map col).foldl (· * ·) 1 := by
  induction l generalizing c with
  | nil => simp
  | cons i l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.foldl_cons, foldl_mul_one _ (1 * col i)]; ring

/-! ## Values of forms -/

/-- A monomial's value at a row of `FE` values (`CPoly.evalE`'s summand). -/
def monV (v : Nat → FE) (m : FK × List Nat) : FE := FE.ofK m.1 * (m.2.map v).foldl (· * ·) 1

theorem evalE_eq (v : Nat → FE) (P : CPoly) : CPoly.evalE v P = sumE (P.map (monV v)) := rfl

theorem evalE_append (v : Nat → FE) (P Q : CPoly) :
    CPoly.evalE v (P ++ Q) = CPoly.evalE v P + CPoly.evalE v Q := by
  rw [evalE_eq, evalE_eq, evalE_eq, List.map_append, sumE_append]

theorem value_eq (f : Form) (col : Nat → FE) :
    f.value col = sumE (f.terms.map fun t => t.2 * (t.1.map col).foldl (· * ·) 1) := by
  rw [Form.value]
  exact congrArg sumE (List.map_congr_left fun t _ => foldl_mul_from col t.2 t.1)

theorem value_cpolyForm (w : FE) (P : CPoly) (col : Nat → FE) :
    (cpolyForm w P).value col = w * CPoly.evalE col P := by
  rw [value_eq, evalE_eq, ← sumE_map_mul]
  simp only [cpolyForm, List.map_map]
  exact congrArg sumE (List.map_congr_left fun m _ => by simp [monV]; ring)

theorem value_formSum (fs : List Form) (col : Nat → FE) :
    (formSum fs).value col = sumE (fs.map (·.value col)) := by
  rw [value_eq, formSum, List.map_flatMap, sumE_flatMap]
  exact congrArg sumE (List.map_congr_left fun f _ => (value_eq f col).symm)

theorem value_const (x : FE) (col : Nat → FE) : (Form.const x).value col = x := by
  simp [value_eq, Form.const, sumE]

theorem value_col (c : Nat) (col : Nat → FE) : (Form.col c).value col = col c := by
  simp [value_eq, Form.col, sumE, gpow]

/-- The value limbs' part of a leaf form. -/
def limbsV (eqα : List FE) (col : Nat → FE) (val : List CPoly) : FE :=
  sumE (val.zipIdx.map fun (P, l) => eqα.getD (3 + l) 0 * CPoly.evalE col P)

/-- **A leaf form's value.** -/
theorem value_leafForm (eqα : List FE) (β : FE) (k : Key) (cnt : CPoly) (col : Nat → FE) :
    (leafForm eqα β k cnt).value col =
      β + eqα.getD 0 0 * FE.ofK k.sep + eqα.getD 1 0 * CPoly.evalE col k.addr +
        eqα.getD 2 0 * CPoly.evalE col cnt + limbsV eqα col k.val := by
  rw [leafForm, value_formSum, List.map_append, sumE_append]
  simp only [List.map_cons, List.map_nil, sumE_cons, sumE_nil, value_const, value_cpolyForm,
    List.map_map, limbsV]
  rw [show ((fun f : Form => f.value col) ∘ fun x : CPoly × Nat => cpolyForm (eqα.getD (3 + x.2) 0) x.1) =
    fun x => eqα.getD (3 + x.2) 0 * CPoly.evalE col x.1 from funext fun x => value_cpolyForm _ _ _]
  ring

theorem value_bucketN (s : List (NBlock × FE)) (j : Nat) (col : Nat → FE) :
    (⟨bucketN s j⟩ : Form).value col =
      sumE ((s.filter fun bw => bw.1.tab == j).map fun bw => bw.2 * bw.1.form.value col) := by
  rw [value_eq, bucketN, List.map_flatMap, sumE_flatMap]
  rw [show ∀ (l : List (NBlock × FE)) (F : NBlock × FE → FE), sumE (l.reverse.map F) = sumE (l.map F) from
    fun l F => by rw [List.map_reverse, sumE_reverse]]
  refine congrArg sumE (List.map_congr_left fun bw _ => ?_)
  rw [List.map_map, value_eq, ← sumE_map_mul]
  exact congrArg sumE (List.map_congr_left fun t _ => by simp; ring)

/-! ## Static stacking -/

/-- `stackBlocks` on any type of blocks with heights `κ`. -/
def stackG {α : Type} (κ : α → Nat) (bs : List α) : List (α × Nat) :=
  ((bs.mergeSort fun a b => decide (κ b ≤ κ a)).foldl
    (fun (acc : List (α × Nat) × Nat) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ κ b)) ([], 0)).1

theorem stackBlocks_map {α : Type} (κ : α → Nat) (f : α → NBlock) (hf : ∀ a, (f a).κ = κ a)
    (bs : List α) : stackBlocks (bs.map f) = (stackG κ bs).map fun bo => (f bo.1, bo.2) := by
  unfold stackBlocks stackG
  have hs : (bs.mergeSort fun a b => decide (κ b ≤ κ a)).map f =
      (bs.map f).mergeSort fun a b => decide (b.κ ≤ a.κ) :=
    List.map_mergeSort fun a _ b _ => by simp [hf]
  simp only
  rw [← hs]
  generalize bs.mergeSort (fun a b => decide (κ b ≤ κ a)) = l
  suffices h : ∀ (acc : List (α × Nat)) (c : Nat),
      ((l.map f).foldl (fun (acc : List (NBlock × Nat) × Nat) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
        (acc.map (fun bo => (f bo.1, bo.2)), c)).1 =
      (l.foldl (fun (acc : List (α × Nat) × Nat) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ κ b))
        (acc, c)).1.map (fun bo => (f bo.1, bo.2)) from h [] 0
  induction l with
  | nil => intro acc c; rfl
  | cons b l ih =>
    intro acc c
    simp only [List.foldl_cons, List.map_cons]
    rw [← ih]
    simp [hf]

/-- A static block of the push and pull sides: table, height, key, read (count column) or seed
(finalize column). -/
structure SBlk where
  /-- The table. -/
  tab : Nat
  /-- The height. -/
  κ : Nat
  /-- The key. -/
  key : Key
  /-- A read (else a seed). -/
  rd : Bool
  /-- The count (read) or finalize (seed) column. -/
  col : Nat

/-- A table's push/pull blocks: its reads, then its seeds. -/
def ppOfShape (t : TShape) (j : Nat) : List SBlk :=
  t.reads.map (fun r => ⟨j, t.τ, r.1, true, r.2⟩) ++ t.seeds.map (fun s => ⟨j, t.τ, s.1, false, s.2⟩)

/-- The push (and pull) side's static blocks. -/
def ppBlocks (S : List TShape) : List SBlk := S.zipIdx.flatMap fun (t, j) => ppOfShape t j

/-- A shape's read-count columns inside its width. -/
def countsS (t : TShape) : List Nat :=
  t.reads.filterMap fun r => if r.2 < t.cols.length then some r.2 else none

/-- The count side's static blocks: table, height, column. -/
def cBlocks (S : List TShape) : List (Nat × Nat × Nat) :=
  S.zipIdx.flatMap fun (t, j) => (countsS t).map fun c => (j, t.τ, c)

/-- The push side's count polynomial. -/
def cntPush (b : SBlk) : CPoly := if b.rd then [(FK.x, [b.col])] else CPoly.const 1

/-- The native blocks of a static block. -/
def fPush (eqα : List FE) (β : FE) (b : SBlk) : NBlock := ⟨b.tab, b.κ, leafForm eqα β b.key (cntPush b)⟩
def fPull (eqα : List FE) (β : FE) (b : SBlk) : NBlock := ⟨b.tab, b.κ, leafForm eqα β b.key (CPoly.var b.col)⟩
def fCnt (c : Nat × Nat × Nat) : NBlock := ⟨c.1, c.2.1, Form.col c.2.2⟩

theorem counts_val (t : Tab) : t.counts.map (·.val) = countsS t.shape := by
  unfold Tab.counts countsS
  rw [List.map_filterMap]
  refine List.filterMap_congr fun r _ => ?_
  simp only [Tab.shape, List.length_map, Tab.w]
  split <;> simp_all

/-- **The three sides are maps of the static blocks.** -/
theorem sideBlocks_eq (st : List Tab) (eqα : List FE) (β : FE) :
    sideBlocks st eqα β = [(ppBlocks (st.map Tab.shape)).map (fPush eqα β),
      (ppBlocks (st.map Tab.shape)).map (fPull eqα β), (cBlocks (st.map Tab.shape)).map fCnt] := by
  simp only [sideBlocks, ppBlocks, cBlocks, List.zipIdx_map, List.flatMap_map, List.map_flatMap,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> refine List.flatMap_congr fun tj _ => ?_
  · simp [ppOfShape, Tab.shape, fPush, cntPush, Prod.map, Function.comp_def]
  · simp [ppOfShape, Tab.shape, fPull, Prod.map, Function.comp_def]
  · simp only [Prod.map, id_eq]
    rw [← counts_val, List.map_map, List.map_map]
    rfl

/-! ## Block weights -/

theorem eOfNat_mod2 (q : Nat) : eOfNat (q % 2) = if q % 2 = 1 then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;> rw [h] <;> rfl

theorem eqEval_selector : ∀ (r : List FE) (q : Nat),
    eqEval (selectorPoint q r.length) r = Loop.eqW r q
  | [], q => rfl
  | a :: r, q => by
    have hs : selectorPoint q (r.length + 1) = eOfNat (q % 2) :: selectorPoint (q / 2) r.length := by
      simp only [selectorPoint, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ _ (by simp) (List.map_congr_left fun i _ => ?_)
      simp only [Function.comp_apply, Nat.shiftRight_eq_div_pow, pow_succ, Nat.div_div_eq_div_mul]
      simp only [Nat.mul_comm]
    rw [List.length_cons, hs, eqEval, List.zipWith_cons_cons, List.foldl_cons, foldl_mul_one,
      ← eqEval, eqEval_selector r (q / 2), Loop.eqW, eOfNat_mod2]
    split
    · simp only [one_mul]; rw [show (1 : FE) + 1 = 0 from CharTwo.add_self_eq_zero 1, zero_add]
    · simp only [one_mul, add_zero, sub_eq_add_neg, CharTwo.neg_eq]

/-- **A block weight is `eqW` of the point above the block at the block's index.** -/
theorem blockWeight_eqW (ζ : List FE) (κ off : Nat) :
    blockWeight ζ κ off = Loop.eqW (ζ.drop κ) (off >>> κ) := by
  rw [blockWeight, ← List.length_drop, eqEval_selector]

/-! ## The bus forms and totals of a table -/

/-- The push/pull side's stacked static blocks. -/
def ppS (S : List TShape) : List (SBlk × Nat) := stackG SBlk.κ (ppBlocks S)

/-- The count side's stacked static blocks. -/
def cS (S : List TShape) : List ((Nat × Nat × Nat) × Nat) := stackG (fun c => c.2.1) (cBlocks S)

theorem sidesR_eq (st : List Tab) (i : BusIn) :
    sidesR st i = [(ppS (st.map Tab.shape)).map (fun bo => (fPush (eqKernel i.alphas) i.beta bo.1,
        blockWeight i.point bo.1.κ bo.2)),
      (ppS (st.map Tab.shape)).map (fun bo => (fPull (eqKernel i.alphas) i.beta bo.1,
        blockWeight i.point bo.1.κ bo.2)),
      (cS (st.map Tab.shape)).map (fun bo => (fCnt bo.1, blockWeight i.point bo.1.2.1 bo.2))] := by
  rw [sidesR, sideBlocks_eq]
  simp only [List.map_cons, List.map_nil, ppS, cS]
  rw [stackBlocks_map SBlk.κ _ (fun _ => rfl), stackBlocks_map SBlk.κ _ (fun _ => rfl),
    stackBlocks_map (fun c : Nat × Nat × Nat => c.2.1) _ (fun _ => rfl)]
  simp [List.map_map, Function.comp_def, fPush, fPull, fCnt]

theorem filter_map_tab {α : Type} (l : List α) (g : α → NBlock × FE) (t : α → Nat)
    (hg : ∀ a, (g a).1.tab = t a) (j : Nat) (h : NBlock × FE → FE) :
    ((l.map g).filter fun bw => bw.1.tab == j).map h = (l.filter fun a => t a == j).map (h ∘ g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.filter_cons, hg]
    split <;> simp [ih]

/-- **Table `j`'s bus forms at its evaluations**: sums over the stacked static blocks of table `j`. -/
theorem forms_value (st : List Tab) (i : BusIn) {j : Nat} (hj : j < st.length) (col : Nat → FE) :
    ((busFinalR st i).forms.getD j []).map (·.value col) =
      [sumE (((ppS (st.map Tab.shape)).filter (·.1.tab == j)).map fun bo =>
          blockWeight i.point bo.1.κ bo.2 * (fPush (eqKernel i.alphas) i.beta bo.1).form.value col),
        sumE (((ppS (st.map Tab.shape)).filter (·.1.tab == j)).map fun bo =>
          blockWeight i.point bo.1.κ bo.2 * (fPull (eqKernel i.alphas) i.beta bo.1).form.value col),
        sumE (((cS (st.map Tab.shape)).filter (·.1.1 == j)).map fun bo =>
          blockWeight i.point bo.1.2.1 bo.2 * col bo.1.2.2)] := by
  have hl : j < ((List.range st.length).map fun j => ((sidesR st i).map (bucketR st.length)).map
      fun a => (⟨a.getD j []⟩ : Form)).length := by rw [List.length_map, List.length_range]; exact hj
  rw [busFinalR_forms_def, List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range,
    sidesR_eq]
  simp only [List.map_cons, List.map_nil]
  rw [bucketR_getD _ _ hj, bucketR_getD _ _ hj, bucketR_getD _ _ hj, value_bucketN, value_bucketN,
    value_bucketN, filter_map_tab _ _ (fun bo : SBlk × Nat => bo.1.tab) (fun _ => rfl),
    filter_map_tab _ _ (fun bo : SBlk × Nat => bo.1.tab) (fun _ => rfl),
    filter_map_tab _ _ (fun bo : (Nat × Nat × Nat) × Nat => bo.1.1) (fun _ => rfl)]
  simp only [Function.comp_def, fCnt, value_col]

/-- **The totals**: `v_k + 1 + Σ_b w_b`, the push and pull sides with the same weights. -/
theorem totals_eq (st : List Tab) (i : BusIn) :
    (busFinalR st i).totals =
      [i.values.getD 0 0 + 1 + sumE ((ppS (st.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2),
       i.values.getD 1 0 + 1 + sumE ((ppS (st.map Tab.shape)).map fun bo => blockWeight i.point bo.1.κ bo.2),
       i.values.getD 2 0 + 1 + sumE ((cS (st.map Tab.shape)).map fun bo => blockWeight i.point bo.1.2.1 bo.2)] := by
  rw [busFinalR_totals_def, sidesR_eq]
  simp [List.range_succ, Function.comp_def]

/-! ## `F`'s table terms -/

/-- Rows of the table sumcheck. -/
abbrev TRow := TableSpec × List Form × FE

/-- `F`'s term of a table from its evaluations (`tableTerms`' summand plus forms). -/
def termF (cp fp pt : List FE) (t : TableSpec) (forms : List Form) (cur : Nat) (ev : List FE) : FE :=
  dot ((cp.drop cur).take t.nConstraints) (t.constraints (pt.take t.logHeight) ev) +
    dot fp (forms.map (·.value (ev.getD · 0)))

/-- The evaluations `F` reads from byte `o` on, table by table. -/
def evsAt (v : Nat → FE) (pt : List FE) : List TRow → Nat → List (List FE × List FE)
  | [], _ => []
  | (t, _, _) :: rest, o => (pt.take t.logHeight, Q1.scalarsAt v o t.width) :: evsAt v pt rest (o + 24 * t.width)

/-- The terms. -/
def termsAt (v : Nat → FE) (cp fp pt : List FE) : List TRow → Nat → Nat → List FE
  | [], _, _ => []
  | (t, forms, _) :: rest, cur, o => termF cp fp pt t forms cur (Q1.scalarsAt v o t.width) ::
      termsAt v cp fp pt rest (cur + t.nConstraints) (o + 24 * t.width)

theorem tableTerms_run (cp fp pt : List FE) (sig : ByteArray) : ∀ (rows : List TRow) (cur : Nat) (f0 : FE)
    (s : RS), tableTerms cp fp pt rows cur f0 sig s =
      ((QB.finalOf (rows.map (·.2.2)) (termsAt (feAt sig) cp fp pt rows cur (s.ent + s.msg + 40)) f0,
        evsAt (feAt sig) pt rows (s.ent + s.msg + 40)),
       { s with msg := s.msg + 24 * (rows.map (·.1.width)).sum })
  | [], _, _, s => by simp [tableTerms, QB.finalOf, evsAt, termsAt]; rfl
  | (t, forms, w) :: rest, cur, f0, s => by
    unfold tableTerms
    simp only [Q1.bind_run, Q1.readEs_run, Q1.pure_run]
    rw [tableTerms_run cp fp pt sig rest]
    have e1 : s.ent + (s.msg + 24 * t.width) + 40 = s.ent + s.msg + 40 + 24 * t.width := by omega
    simp only [e1, QB.finalOf, termsAt, evsAt, List.map_cons, List.zip_cons_cons, List.foldl_cons,
      List.sum_cons, termF]
    refine Prod.ext (Prod.ext rfl rfl) ?_
    simp only [RS.mk.injEq, true_and, and_true]; ring

/-! ## `tabPh` from a position -/

/-- **`F`'s table phase from position `pos s`** (the tables `m.tables pub` being native tables). -/
theorem tabPh_run (p : Params) (m : M3) (pub : Pub) (bus : BusOut) (point : List FE) (st : List Tab)
    (hm : m.tables pub = st.map nativeTable) (sig : ByteArray) (s : RS) :
    tabPh p m pub bus point sig s =
      let ξ := feAt sig (pos s + 40)
      let nC := (st.map (·.cons.length)).sum
      let xp := powers ξ (nC + 3)
      let sc := sumcheck (dot (xp.drop nC) bus.totals) 4 (List.replicate p.tableRounds none) sig
        ⟨pos s + 72, 0, s.ok⟩
      let pt := sc.1.1.reverse
      let rows := List.zip (st.map nativeTable) (List.zip bus.forms (tableWeights (st.map (·.τ)) point pt))
      let B := pos s + 72 + 144 * p.tableRounds
      (evsAt (feAt sig) pt rows (B + 40),
        ⟨B, 24 * (rows.map (·.1.width)).sum,
          (QB.finalOf (rows.map (·.2.2)) (termsAt (feAt sig) (xp.take nC) (xp.drop nC) pt rows 0 (B + 40)) 0
            == sc.1.2) && s.ok⟩) := by
  have hR := QB.sumcheck_run 4 (by decide) sig (List.replicate p.tableRounds none)
  unfold tabPh tableSumcheck
  simp only [Q1.bind_run, Q1.sampleE_run, hm]
  rw [show s.ent + 40 + s.msg = pos s + 40 by simp [pos]; omega,
    show ({ s with ent := s.ent + 72 + s.msg, msg := 0 } : RS) = ⟨pos s + 72, 0, s.ok⟩ by
      simp [pos]; omega]
  have e1 : (st.map nativeTable).map (·.nConstraints) = st.map (·.cons.length) := by
    simp [nativeTable, Function.comp_def]
  have e2 : (st.map nativeTable).map (·.logHeight) = st.map (·.τ) := by
    simp [nativeTable, Function.comp_def]
  simp only [e1, e2]
  rw [hR _ ⟨pos s + 72, 0, s.ok⟩ rfl]
  simp only [tableTerms_run, require_run, Q1.pure_run, List.length_replicate, QB.entB,
    Nat.add_zero, Nat.zero_add, show 72 + 24 * (4 - 1) = 144 from rfl]

/-! ## Powers of `ξ` -/

theorem powers_length (b : FE) (n : Nat) : (powers b n).length = n := by
  have key : ∀ (acc : FE) (n : Nat), (powersFrom acc b n).length = n := by
    intro acc n
    induction n generalizing acc with
    | zero => rfl
    | succ n ih => simp [powersFrom, ih]
  exact key 1 n

theorem take_drop_powers (ξ : FE) (N cur n : Nat) (h : cur + n ≤ N) :
    ((powers ξ N).drop cur).take n = (List.range n).map fun i => ξ ^ (cur + i) := by
  apply List.ext_getElem
  · simp [powers_length]; omega
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
    have := Loop.Build.powers_getD ξ N (cur + i) (by simp at h2; omega)
    rw [List.getD_eq_getElem _ _ (by rw [powers_length]; simp at h2; omega)] at this
    exact this

theorem dot_cons (a b : FE) (l r : List FE) : dot (a :: l) (b :: r) = a * b + dot l r := by
  rw [dot, List.zipWith_cons_cons, List.foldl_cons, foldl_add_from, zero_add]; rfl

theorem dot_pows (ξ : FE) : ∀ (vs : List FE) (cur : Nat),
    dot ((List.range vs.length).map fun i => ξ ^ (cur + i)) vs = ξ ^ cur * polyEval vs ξ
  | [], _ => by simp [dot, polyEval]
  | v :: vs, cur => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, dot_cons]
    have := dot_pows ξ vs (cur + 1)
    rw [show ((fun i => ξ ^ (cur + i)) ∘ Nat.succ) = fun i => ξ ^ (cur + 1 + i) from
      funext fun i => by simp only [Function.comp_apply]; rw [show cur + i.succ = cur + 1 + i by omega],
      this]
    simp only [polyEval, List.foldr_cons, Nat.add_zero]
    rw [show List.foldr (fun c acc => acc * ξ + c) 0 vs = polyEval vs ξ from rfl]
    ring

theorem drop_powers3 (ξ : FE) (nC : Nat) :
    (powers ξ (nC + 3)).drop nC = [ξ ^ nC, ξ ^ (nC + 1), ξ ^ (nC + 2)] := by
  have := take_drop_powers ξ (nC + 3) nC 3 le_rfl
  rw [List.take_of_length_le (by simp [powers_length])] at this
  rw [this]; rfl

theorem dot3 (a b c x y z : FE) : dot [a, b, c] [x, y, z] = a * x + b * y + c * z := by
  rw [dot_cons, dot_cons, dot_cons, show dot [] [] = 0 from rfl, add_zero, add_assoc]

/-! ## The merged push/pull value of a static block -/

theorem evalE_cons (v : Nat → FE) (m : FK × List Nat) (P : CPoly) :
    CPoly.evalE v (m :: P) = monV v m + CPoly.evalE v P := by
  rw [evalE_eq, evalE_eq, List.map_cons, sumE_cons]

theorem evalE_nil (v : Nat → FE) : CPoly.evalE v [] = 0 := rfl

theorem dval_eq (eqα : List FE) (β fp0 fp1 : FE) (b : SBlk) (col : Nat → FE) :
    fp0 * (fPush eqα β b).form.value col + fp1 * (fPull eqα β b).form.value col =
      (fp0 + fp1) * (β + eqα.getD 0 0 * FE.ofK b.key.sep) +
        (fp0 + fp1) * eqα.getD 1 0 * CPoly.evalE col b.key.addr +
        (fp0 + fp1) * limbsV eqα col b.key.val +
        (if b.rd then eqα.getD 2 0 * (fp0 * FE.ofK FK.x + fp1) * col b.col
         else eqα.getD 2 0 * fp0 + eqα.getD 2 0 * fp1 * col b.col) := by
  simp only [fPush, fPull, value_leafForm, cntPush]
  have hv : CPoly.evalE col (CPoly.var b.col) = col b.col := by
    simp [CPoly.var, evalE_cons, evalE_nil, monV, Loop.Build.ofK_one]
  rw [hv]
  split
  · have : CPoly.evalE col [(FK.x, [b.col])] = FE.ofK FK.x * col b.col := by
      simp [evalE_cons, evalE_nil, monV]
    rw [this]; ring
  · have : CPoly.evalE col (CPoly.const 1) = 1 := by simp [CPoly.const, evalE_cons, evalE_nil, monV]; rfl
    rw [this]; ring

/-! ## Geometric polynomials over the bit columns -/

/-- Bits `z ∈ [a, e)` of the columns `1 + z` with coefficients `x^{z−a+d}` (a `BITS` output). -/
def geoPoly (a e d : Nat) : CPoly :=
  (List.range 64).map fun z => (if a ≤ z ∧ z < e then Bits.wt (z - a + d) else 0, [1 + z])

/-- The suffix sums `S k = Σ_{k ≤ z < 64} x^{z−k} · col (1 + z)`. -/
def Sv (col : Nat → FE) (k : Nat) : FE := ∑ z ∈ Finset.Ico k 64, gen ^ (z - k) * col (1 + z)

theorem Sv_succ (col : Nat → FE) {k : Nat} (hk : k < 64) : Sv col k = col (1 + k) + gen * Sv col (k + 1) := by
  rw [Sv, Finset.sum_eq_sum_Ico_succ_bot hk, Nat.sub_self, pow_zero, one_mul, Sv, Finset.mul_sum]
  refine congrArg (col (1 + k) + ·) (Finset.sum_congr rfl fun z hz => ?_)
  have := (Finset.mem_Ico.mp hz).1
  rw [← mul_assoc, ← pow_succ', show z - k = z - (k + 1) + 1 by omega]

theorem Sv_64 (col : Nat → FE) : Sv col 64 = 0 := by simp [Sv]

theorem sumE_eq_sum (l : List FE) : sumE l = l.sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [sumE_cons, ih, List.sum_cons]

theorem sum_map_range (f : Nat → FE) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n,
      Finset.sum_range_succ]; simp

theorem ofK_wt {k : Nat} (hk : k < 64) : FE.ofK (Bits.wt k) = gen ^ k := by
  rw [Bits.wt_eq_pow hk, gen]; exact map_pow FE.ofKRingHom FK.x k

/-- **A geometric polynomial by suffix sums.** -/
theorem evalE_geo (col : Nat → FE) {a e d : Nat} (hae : a ≤ e) (he : e ≤ 64) (hd : e - a + d ≤ 64) :
    CPoly.evalE col (geoPoly a e d) = gen ^ d * (Sv col a + gen ^ (e - a) * Sv col e) := by
  rw [evalE_eq, sumE_eq_sum, geoPoly, List.map_map, sum_map_range]
  have h1 : ∑ z ∈ Finset.range 64, (monV col ∘ fun z =>
      ((if a ≤ z ∧ z < e then Bits.wt (z - a + d) else 0 : FK), [1 + z])) z =
      ∑ z ∈ Finset.Ico a e, gen ^ d * (gen ^ (z - a) * col (1 + z)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range 64) (fun z => a ≤ z ∧ z < e)]
    have hf : (Finset.range 64).filter (fun z => a ≤ z ∧ z < e) = Finset.Ico a e := by
      ext z; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hf, Finset.sum_eq_zero (s := Finset.filter _ _) (fun z hz => by
      rw [Finset.mem_filter] at hz
      simp [monV, hz.2, Loop.Build.ofK_zero]), add_zero]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := Finset.mem_Ico.mp hz
    simp only [Function.comp_apply, monV, if_pos hz', List.map_cons, List.map_nil, List.foldl_cons,
      List.foldl_nil, one_mul]
    rw [ofK_wt (by omega), ← mul_assoc, ← pow_add, show z - a + d = d + (z - a) by omega]
  rw [h1, ← Finset.mul_sum]
  congr 1
  have hsplit := Finset.sum_Ico_consecutive (fun z => gen ^ (z - a) * col (1 + z)) hae he
  have h2 : ∑ z ∈ Finset.Ico e 64, gen ^ (z - a) * col (1 + z) = gen ^ (e - a) * Sv col e := by
    rw [Sv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have := (Finset.mem_Ico.mp hz).1
    rw [← mul_assoc, ← pow_add, show z - a = e - a + (z - e) by omega]
  rw [Sv, ← hsplit, h2, add_assoc, CharTwo.add_self_eq_zero, add_zero]

end Lvm.Har
