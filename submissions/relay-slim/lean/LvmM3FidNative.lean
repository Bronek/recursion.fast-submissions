-- new for lvm (WP-9b): the native M3 decision (`LvmDecideM3Real`: `busFinalR`, `nativeTable`,
-- `tableCheckR`) is the table phase's program objects over `E` (`LvmM3Fid`: `busFinalV`,
-- `vTable`, `tableCheckVB`) through the field isomorphism `FE.toExt3` (`FE.ringEquivExt3`).
import LvmDecideM3Real
import LvmM3FidFix
import LvmM3FidFixC

/-!
# The native M3 decision over `E`

The native verifier (`LvmDecideM3Real`) computes over `FE`; the program objects the table phase's
spec is stated at (`LvmM3Fid`, `LvmM3FidTab.lbusTableSpec`) are over `E`. Through `FE.toExt3`:

* **`busFinalR_forms`, `busFinalR_totals`**: the native bus leaf decomposition is `busFinalV` at the
  mapped inputs, form for form (`formE` maps a form's coefficients) and total for total (the
  native `eqKernel`, `eqEval`, `selectorPoint`, `sumE` are VCore's, the native stacking is the
  same stable sort and the same offsets, the native `Array` bucket fold is `bucketV`);
  `busFinalR_claims` (no framework claim), `busFinalR_ok` (its flag);
  `value_formE` (a form's value is the mapped form's).
* **`nativeTable_shape`, `nativeTable_cons`**: the native table has `vTable`'s height, width and
  constraint count, and its constraints are `vTable`'s at the mapped values.
* **`tableCheckVB_of_R`**: the native fixed-column check passing on the tables' evaluations, the
  program's check passes on the claims built from them (`claimsOfEvs`).

The native functions used here (`busFinalR`, `sideBlocks`, `stackBlocks`, `blockWeight`,
`leafForm`, `nativeTable`, `tableCheckR`) have the same bodies on lvm/FRZ (INT-2's frozen
`M3.real` wraps them).
-/

set_option autoImplicit false

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol

/-! ## Scalars -/

theorem tE_add (a b : FE) : FE.toExt3 (a + b) = FE.toExt3 a + FE.toExt3 b :=
  map_add FE.ringEquivExt3 a b

theorem tE_mul (a b : FE) : FE.toExt3 (a * b) = FE.toExt3 a * FE.toExt3 b :=
  map_mul FE.ringEquivExt3 a b

theorem tE_zero : FE.toExt3 0 = 0 := map_zero FE.ringEquivExt3

theorem tE_one : FE.toExt3 1 = 1 := map_one FE.ringEquivExt3

theorem tE_ofK (c : FK) : FE.toExt3 (FE.ofK c) = kE c := by
  rw [toExt3_ofK']; rfl

theorem kE_eq (c : FK) : kE c = CompPoly.Extension.Ext.ofBase (FK.toBF64 c) := rfl

theorem optD_map_tE (o : Option FE) : (o.map FE.toExt3).getD 0 = FE.toExt3 (o.getD 0) := by
  cases o <;> simp [tE_zero]

theorem tE_foldl_add (l : List FE) (a : FE) :
    FE.toExt3 (l.foldl (· + ·) a) = (l.map FE.toExt3).foldl (· + ·) (FE.toExt3 a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, List.map_cons, ih, tE_add]

theorem tE_foldl_mul (l : List FE) (a : FE) :
    FE.toExt3 (l.foldl (· * ·) a) = (l.map FE.toExt3).foldl (· * ·) (FE.toExt3 a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons, List.map_cons, ih, tE_mul]

theorem tE_sumE (l : List FE) : FE.toExt3 (Lvm.sumE l) = Verifier.sumE (l.map FE.toExt3) := by
  rw [Lvm.sumE, tE_foldl_add, tE_zero]; rfl

theorem getD_map_tE (l : List FE) (n : ℕ) : (l.map FE.toExt3).getD n 0 = FE.toExt3 (l.getD n 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[n]? <;> simp [tE_zero]

theorem map_eqKernel (p : List FE) :
    (Lvm.eqKernel p).map FE.toExt3 = Verifier.eqKernel (p.map FE.toExt3) := by
  unfold Lvm.eqKernel Verifier.eqKernel
  suffices h : ∀ out : List FE, (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).map
      FE.toExt3 = (p.map FE.toExt3).foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r))
        (out.map FE.toExt3) by
    rw [h]; simp [tE_one]
  induction p with
  | nil => intro out; rfl
  | cons r p ih =>
    intro out
    simp only [List.foldl_cons, List.map_cons, ih, List.map_append, List.map_map]
    congr 2 <;> exact List.map_congr_left fun x _ ↦ by simp [tE_mul, tE_add, tE_one]

theorem tE_eOfNat (n : ℕ) : FE.toExt3 (Lvm.eOfNat n) = LeanVM.Protocol.Verifier.eOfNat n := by
  rw [Lvm.eOfNat, tE_ofK]; rfl

theorem map_selectorPoint (s len : ℕ) :
    (Lvm.selectorPoint s len).map FE.toExt3 = Verifier.selectorPoint s len := by
  simp [Lvm.selectorPoint, Verifier.selectorPoint, List.map_map, Function.comp_def, tE_eOfNat]

theorem tE_eqEval (a b : List FE) :
    FE.toExt3 (Lvm.eqEval a b) = Verifier.eqEval (a.map FE.toExt3) (b.map FE.toExt3) := by
  unfold Lvm.eqEval Verifier.eqEval
  rw [tE_foldl_mul, tE_one]
  congr 1
  induction a generalizing b with
  | nil => rfl
  | cons x a ih => cases b with
    | nil => rfl
    | cons y b => simp [List.zipWith_cons_cons, ih, tE_add, tE_one]

theorem tE_blockWeight (ζ : List FE) (κ off : ℕ) :
    FE.toExt3 (blockWeight ζ κ off) = blockWeightV (ζ.map FE.toExt3) κ off := by
  unfold blockWeight blockWeightV Verifier.Placement.eqAbove
  rw [tE_eqEval, map_selectorPoint, List.map_drop, List.length_map]

/-! ## Forms -/

/-- A native form over `E`. -/
def formE (f : Lvm.Form) : Verifier.Form := ⟨f.terms.map fun t ↦ (t.1, FE.toExt3 t.2)⟩

/-- A native bus block over `E`. -/
def blkE (b : NBlock) : VBlock := ⟨b.tab, b.κ, formE b.form⟩

/-- A weighted native block over `E`. -/
def bwE (bw : NBlock × FE) : VBlock × E := (blkE bw.1, FE.toExt3 bw.2)

theorem formE_cpolyForm (w : FE) (P : CPoly) : formE (cpolyForm w P) = cpolyFormV (FE.toExt3 w) P := by
  simp only [formE, cpolyForm, cpolyFormV, List.map_map]
  congr 1
  exact List.map_congr_left fun m _ ↦ by simp only [Function.comp_apply, tE_mul, tE_ofK]

theorem formE_formSum (fs : List Lvm.Form) : formE (formSum fs) = formSumV (fs.map formE) := by
  simp [formE, formSum, formSumV, List.map_flatMap, List.flatMap_map]

theorem formE_col (c : ℕ) : formE (Lvm.Form.col c) = Verifier.Form.col c := by
  simp [formE, Lvm.Form.col, Verifier.Form.col, Lvm.gpow, Verifier.gpow, tE_one]

theorem formE_leafForm (eqα : List FE) (β : FE) (k : Key) (cnt : CPoly) :
    formE (leafForm eqα β k cnt) = leafFormV (eqα.map FE.toExt3) (FE.toExt3 β) k cnt := by
  unfold leafForm leafFormV
  rw [formE_formSum]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
  have hc : formE (Lvm.Form.const (β + eqα.getD 0 0 * FE.ofK k.sep)) =
      Verifier.Form.const (FE.toExt3 β + (eqα.map FE.toExt3).getD 0 0 * kE k.sep) := by
    rw [getD_map_tE, ← tE_ofK, ← tE_mul, ← tE_add]; rfl
  rw [hc, formE_cpolyForm, formE_cpolyForm, getD_map_tE, getD_map_tE]
  have hl : List.map (formE ∘ fun x : CPoly × ℕ ↦ cpolyForm (eqα.getD (3 + x.2) 0) x.1) k.val.zipIdx =
      List.map (fun x : CPoly × ℕ ↦ cpolyFormV ((eqα.map FE.toExt3).getD (3 + x.2) 0) x.1)
        k.val.zipIdx :=
    List.map_congr_left fun x _ ↦ by simp only [Function.comp_apply, formE_cpolyForm, getD_map_tE]
  rw [hl]
  simp only [getD_map_tE]

/-- **A form's value**: the native value at a row is the mapped form's at the mapped row. -/
theorem value_formE (f : Lvm.Form) (col : ℕ → FE) :
    FE.toExt3 (f.value col) = (formE f).evaluate fun i ↦ FE.toExt3 (col i) := by
  unfold Lvm.Form.value Verifier.Form.evaluate formE
  rw [tE_sumE, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  simp only [Function.comp_apply]
  generalize t.2 = a
  induction t.1 generalizing a with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, ih, tE_mul]

/-! ## Blocks -/

theorem map_sideBlocks (tabs : List Tab) (eqα : List FE) (β : FE) :
    (sideBlocks tabs eqα β).map (·.map blkE) = sideBlocksV tabs (eqα.map FE.toExt3) (FE.toExt3 β) := by
  simp [sideBlocks, sideBlocksV, List.map_flatMap, List.map_map, Function.comp_def, blkE,
    formE_leafForm, formE_col]

theorem map_stackBlocks (bs : List NBlock) :
    (stackBlocks bs).map (fun bo ↦ (blkE bo.1, bo.2)) = stackBlocksV (bs.map blkE) := by
  unfold stackBlocks stackBlocksV
  have hs : (bs.mergeSort fun a b ↦ decide (b.κ ≤ a.κ)).map blkE =
      (bs.map blkE).mergeSort fun a b ↦ decide (b.κ ≤ a.κ) :=
    List.map_mergeSort fun _ _ _ _ ↦ rfl
  simp only
  rw [← hs]
  generalize bs.mergeSort (fun a b ↦ decide (b.κ ≤ a.κ)) = l
  suffices h : ∀ (acc : List (NBlock × ℕ)) (c : ℕ),
      (l.foldl (fun (acc : List (NBlock × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
        (acc, c)).1.map (fun bo ↦ (blkE bo.1, bo.2)) =
      ((l.map blkE).foldl (fun (acc : List (VBlock × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)],
        acc.2 + 2 ^ b.κ)) (acc.map (fun bo ↦ (blkE bo.1, bo.2)), c)).1 from h [] 0
  induction l with
  | nil => intro acc c; rfl
  | cons b l ih =>
    intro acc c
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [blkE]

/-- The native sides with their block weights (`busFinalR`'s `sides`). -/
def sidesR (tabs : List Tab) (i : BusIn) : List (List (NBlock × FE)) :=
  (sideBlocks tabs (Lvm.eqKernel i.alphas) i.beta).map fun bs ↦
    (stackBlocks bs).map fun bo ↦ (bo.1, blockWeight i.point bo.1.κ bo.2)

theorem map_sides (tabs : List Tab) (i : BusIn) :
    (sidesR tabs i).map (·.map bwE) =
      sidesV tabs (i.alphas.map FE.toExt3) (FE.toExt3 i.beta) (i.point.map FE.toExt3) := by
  unfold sidesV sidesR
  rw [← map_eqKernel, ← map_sideBlocks, List.map_map, List.map_map]
  refine List.map_congr_left fun bs _ ↦ ?_
  simp only [Function.comp_apply, List.map_map]
  rw [← map_stackBlocks, List.map_map]
  exact List.map_congr_left fun bo _ ↦ by simp [bwE, tE_blockWeight, blkE]

/-! ## The bucket fold -/

/-- The native bucket fold of `busFinalR` (one table's terms per entry, prepended). -/
def bucketR (n : ℕ) (s : List (NBlock × FE)) : Array (List (List ℕ × FE)) :=
  s.foldl (fun acc bw ↦ acc.modify bw.1.tab fun ts ↦ bw.1.form.terms.map (fun t ↦ (t.1, bw.2 * t.2)) ++ ts)
    (Array.replicate n [])

/-- Table `j`'s terms of a side, the last block first. -/
def bucketN (s : List (NBlock × FE)) (j : ℕ) : List (List ℕ × FE) :=
  ((s.filter fun bw ↦ bw.1.tab == j).reverse).flatMap fun bw ↦
    bw.1.form.terms.map fun t ↦ (t.1, bw.2 * t.2)

theorem bucketR_getD (n : ℕ) (s : List (NBlock × FE)) {j : ℕ} (hj : j < n) :
    (bucketR n s).getD j [] = bucketN s j := by
  unfold bucketR bucketN
  suffices h : ∀ acc : Array (List (List ℕ × FE)), j < acc.size →
      (s.foldl (fun acc bw ↦ acc.modify bw.1.tab fun ts ↦
        bw.1.form.terms.map (fun t ↦ (t.1, bw.2 * t.2)) ++ ts) acc).getD j [] =
      ((s.filter fun bw ↦ bw.1.tab == j).reverse).flatMap (fun bw ↦
        bw.1.form.terms.map fun t ↦ (t.1, bw.2 * t.2)) ++ acc.getD j [] by
    rw [h _ (by simpa using hj)]; simp [Array.getD, hj]
  induction s with
  | nil => intro acc _; simp
  | cons bw s ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    rw [ih _ (by simpa using hacc)]
    have hget : (acc.modify bw.1.tab fun ts ↦ bw.1.form.terms.map (fun t ↦ (t.1, bw.2 * t.2)) ++ ts).getD j [] =
        if bw.1.tab = j then bw.1.form.terms.map (fun t ↦ (t.1, bw.2 * t.2)) ++ acc.getD j []
        else acc.getD j [] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Array.getD_eq_getD_getElem?]
      by_cases hb : bw.1.tab = j
      · simp only [hb, if_true]
        rw [Array.getElem?_eq_getElem hacc]; rfl
      · simp only [hb, if_false]
    rw [hget]
    by_cases ht : bw.1.tab = j
    · simp [ht, List.filter_cons, List.reverse_cons, List.flatMap_append, List.append_assoc]
    · simp [ht, List.filter_cons]

/-! ## The bus result -/

theorem formE_bucket (s : List (NBlock × FE)) (j : ℕ) :
    formE ⟨bucketN s j⟩ = ⟨bucketV (s.map bwE) j⟩ := by
  simp only [formE, bucketN, bucketV, List.filter_map, Function.comp_def, ← List.map_reverse,
    List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1
  refine List.flatMap_congr fun bw _ ↦ ?_
  simp [bwE, blkE, formE, tE_mul]

theorem busFinalR_forms_def (tabs : List Tab) (i : BusIn) :
    (busFinalR tabs i).forms = (List.range tabs.length).map fun j ↦
      ((sidesR tabs i).map (bucketR tabs.length)).map fun a ↦ (⟨a.getD j []⟩ : Lvm.Form) := rfl

theorem busFinalR_totals_def (tabs : List Tab) (i : BusIn) :
    (busFinalR tabs i).totals = (List.range 3).map fun k ↦
      i.values.getD k 0 + 1 + Lvm.sumE (((sidesR tabs i).getD k []).map (·.2)) := rfl

/-- **The native bus forms are `busFinalV`'s**, form for form. -/
theorem busFinalR_forms (tabs : List Tab) (i : BusIn) :
    (busFinalR tabs i).forms.map (·.map formE) =
      (busFinalV tabs (i.alphas.map FE.toExt3) (FE.toExt3 i.beta) (i.point.map FE.toExt3)
        (i.values.map FE.toExt3)).forms := by
  rw [busFinalR_forms_def]
  simp only [busFinalV, ← map_sides, List.map_map]
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' : j < tabs.length := List.mem_range.mp hj
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun s _ ↦ ?_
  simp only [Function.comp_apply]
  rw [← formE_bucket, bucketR_getD tabs.length s hj']

theorem getD_map_nil {α β : Type} (l : List (List α)) (f : α → β) (k : ℕ) :
    (l.map (·.map f)).getD k [] = (l.getD k []).map f := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[k]? <;> rfl

/-- **The native bus totals are `busFinalV`'s.** -/
theorem busFinalR_totals (tabs : List Tab) (i : BusIn) :
    (busFinalR tabs i).totals.map FE.toExt3 =
      (busFinalV tabs (i.alphas.map FE.toExt3) (FE.toExt3 i.beta) (i.point.map FE.toExt3)
        (i.values.map FE.toExt3)).totals := by
  rw [busFinalR_totals_def]
  simp only [busFinalV, ← map_sides, List.map_map]
  refine List.map_congr_left fun k _ ↦ ?_
  simp only [Function.comp_apply, tE_add, tE_one, tE_sumE, getD_map_tE, getD_map_nil, List.map_map]
  rfl

/-- The native bus phase makes no framework claim. -/
theorem busFinalR_claims (tabs : List Tab) (i : BusIn) : (busFinalR tabs i).claims = [] := rfl

/-- The native bus flag: three tree values and the one zero scalar. -/
theorem busFinalR_ok (tabs : List Tab) (i : BusIn) :
    (busFinalR tabs i).ok = (i.values.length == 3 && i.leafdec == [0]) := rfl

/-! ## Tables -/

theorem tE_evalE (v : ℕ → FE) (P : CPoly) :
    FE.toExt3 (CPoly.evalE v P) = CPoly.evalV (fun i ↦ FE.toExt3 (v i)) P := by
  unfold CPoly.evalE CPoly.evalV
  rw [tE_foldl_add, tE_zero, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ ↦ ?_
  simp only [Function.comp_apply, tE_mul, tE_ofK, tE_foldl_mul, tE_one, List.map_map]
  rfl

/-- The native table has `vTable`'s height, width and constraint count. -/
theorem nativeTable_shape (j : ℕ) (t : Tab) :
    (nativeTable t).logHeight = t.τ ∧ (nativeTable t).width = (vTable j t).width ∧
      (nativeTable t).nConstraints = (vTable j t).nConstraints := by
  refine ⟨rfl, by simp [nativeTable, vTable, Verifier.Table.width], ?_⟩
  simp [nativeTable, vTable, Verifier.Table.nConstraints]

/-- **The native constraints are `vTable`'s** at the mapped evaluations. -/
theorem nativeTable_cons (j : ℕ) (t : Tab) (pt ev : List FE) :
    ((nativeTable t).constraints pt ev).map FE.toExt3 = (vTable j t).constraints (ev.map FE.toExt3) := by
  simp only [nativeTable, vTable, List.map_map]
  refine List.map_congr_left fun P _ ↦ ?_
  simp only [Function.comp_apply, tE_evalE, getD_map_tE]

/-! ## The fixed-column check -/

/-- The table phase's claims from the tables' points and evaluations: column `i` of table `j` is
global column `base_j + i`, at the table's point, with its evaluation. -/
def claimsOfEvs (tabs : List Tab) (evs : List (List FE × List FE)) : List Verifier.ColumnClaim :=
  ((tabs.zip evs).zipIdx).flatMap fun x ↦ x.1.2.2.zipIdx.map fun vi ↦
    ⟨(Verifier.globalColumnBases (vTables tabs)).getD x.2 0 + vi.2, x.1.2.1.map FE.toExt3,
      FE.toExt3 vi.1⟩

theorem FE_eq_of_beq {x y : FE} (h : (x == y) = true) : x = y := by
  change (x.c₀ == y.c₀ && x.c₁ == y.c₁ && x.c₂ == y.c₂) = true at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  cases x; cases y; simp_all

theorem colLoc_raw (tabs : List Tab) {j i : ℕ} (hj : j < tabs.length) (hi : i < tabs[j].w) :
    colLoc tabs ((Verifier.globalColumnBases (vTables tabs)).getD j 0 + i) = some (j, i) := by
  have hτ : ∀ t ∈ tabs, t.τ ≤ (⟨(tabs.map (·.τ)).sum, 0⟩ : Lay).μ := fun t ht ↦ by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := (·.τ)) ht)
    simp only [Lay.μ]; omega
  exact colLoc_colOfL ⟨(tabs.map (·.τ)).sum, 0⟩ tabs hτ ⟨⟨j, hj⟩, ⟨i, hi⟩⟩

/-- **The native fixed-column check gives the program's**: if `tableCheckR` passes on the tables'
points and evaluations (no table has more evaluations than columns), `tableCheckVB` passes on the
claims built from them. -/
theorem tableCheckVB_of_R (tabs : List Tab) (evs : List (List FE × List FE))
    (hR : tableCheckR tabs evs = true)
    (hw : ∀ j (h1 : j < tabs.length) (h2 : j < evs.length), evs[j].2.length ≤ tabs[j].w) :
    tableCheckVB tabs (claimsOfEvs tabs evs) = true := by
  unfold tableCheckVB claimsOfEvs
  rw [List.all_eq_true]
  intro c hc
  obtain ⟨⟨⟨t, pt, ev⟩, j⟩, hx, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨v, i⟩, hvi, rfl⟩ := List.mem_map.mp hc
  have hzj := List.mem_zipIdx_iff_getElem?.mp hx
  have hvi' := List.mem_zipIdx_iff_getElem?.mp hvi
  simp only at hzj hvi'
  rw [List.getElem?_zip_eq_some] at hzj
  obtain ⟨htj, hej⟩ := hzj
  have hjt : j < tabs.length := (List.getElem?_eq_some_iff.mp htj).1
  have hje : j < evs.length := (List.getElem?_eq_some_iff.mp hej).1
  have ht : tabs[j] = t := (List.getElem?_eq_some_iff.mp htj).2
  have he : evs[j] = (pt, ev) := (List.getElem?_eq_some_iff.mp hej).2
  have hil : i < ev.length := (List.getElem?_eq_some_iff.mp hvi').1
  have hiw : i < tabs[j].w := by
    have := hw j hjt hje; rw [he] at this; simp only at this; omega
  have hiw' : i < t.w := by rw [← ht]; exact hiw
  have hfx : fixedEvalV tabs ((Verifier.globalColumnBases (vTables tabs)).getD j 0 + i) =
      match t.cols[i] with
      | .fix _ e => some fun pt ↦ FE.toExt3 (e (pt.map FE.ofExt3))
      | _ => none := by
    simp only [fixedEvalV, colLoc_raw tabs hjt hiw, Option.bind_some, List.getElem?_eq_getElem hjt,
      ht, Option.bind_some, List.getElem?_eq_getElem hiw']
    cases t.cols[i] <;> rfl
  simp only [hfx]
  cases hc : t.cols[i] with
  | com rec off => rfl
  | fix f e =>
    simp only
    have hmem : (t, (pt, ev)) ∈ tabs.zip evs :=
      List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨htj, hej⟩)
    unfold tableCheckR at hR
    rw [List.all_eq_true] at hR
    have h1 := hR _ hmem
    simp only [List.all_eq_true] at h1
    have h2 := h1 (t.cols[i], i) (List.mem_zipIdx_iff_getElem?.mpr (by simp [hiw']))
    rw [hc] at h2
    simp only at h2
    have hv : ev.getD i 0 = v := by
      rw [List.getD_eq_getElem?_getD, hvi']; rfl
    rw [hv] at h2
    have := FE_eq_of_beq h2
    simp [this, List.map_map, Function.comp_def]

end Lvm.M3
