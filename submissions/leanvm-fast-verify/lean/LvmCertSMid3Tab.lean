-- WP-16b (CERT). New for lvm (O6 link, the tables): the table phase's claims have their table's
-- height coordinates (a return fact of `lbusTableCheckProg`), and its assembled block claims
-- (`tableClaimsE`) holding on the commitments give WP-9b's `BlockHolds`.
import LvmCertSMid3Blk
import LvmM3MidCert

/-!
# The table claims

* **`retOK_lbusTableCheckProg`**: every return of V_S phases 2–3 meets `TabRet`;
* **`blockHolds_of_tableClaims`**: the assembled table claims hold on `(qm, qr)` ⇒ every
  returned claim is WP-9b's `BlockHolds` (under `LayOk`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-! ## The returns of the table phase -/

/-- Global column `base_j + i` (`i` inside table `j`'s width) decodes to `(j, i)`. -/
theorem colLoc_base (tabs : List Lvm.M3.Tab) {j i : ℕ} (hj : j < tabs.length) (hi : i < tabs[j].w) :
    Lvm.M3.colLoc tabs ((globalColumnBases (Lvm.M3.vTables tabs)).getD j 0 + i) = some (j, i) := by
  have hτ : ∀ t ∈ tabs, t.τ ≤ (⟨(tabs.map (·.τ)).sum, 0⟩ : Lvm.M3.Lay).μ := fun t ht ↦ by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := (·.τ)) ht)
    simp only [Lvm.M3.Lay.μ]; omega
  exact Lvm.M3.colLoc_colOfL ⟨(tabs.map (·.τ)).sum, 0⟩ tabs hτ ⟨⟨j, hj⟩, ⟨i, hi⟩⟩

/-- A running maximum bounds its start and every element. -/
theorem foldl_max_ge : ∀ (l : List ℕ) (a x : ℕ), (x ≤ a ∨ x ∈ l) → x ≤ l.foldl max a
  | [], a, x, h => by simpa using h
  | b :: l, a, x, h => foldl_max_ge l (max a b) x (by
      rcases h with h | h
      · exact Or.inl (le_max_of_le_left h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (le_max_right _ _)
        · exact Or.inr h)

/-- Zipping keeps at most the first list's total. -/
theorem sum_zip_fst_le {α β : Type} (f : α → ℕ) :
    ∀ (l : List α) (m : List β), ((l.zip m).map fun r ↦ f r.1).sum ≤ (l.map f).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have := sum_zip_fst_le f l m
    omega

open LeanVM.Protocol.Compile in
/-- **`tableTermsClaims`'s returns**: the claims meet `P` when the accumulated ones do and every
row's do, and there are as many new claims as the rows' widths. -/
theorem retOK_tableTermsClaims (tables : List Verifier.Table) (cp fp point : List E)
    (P : ColumnClaim → Prop) :
    ∀ (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), (∀ c ∈ claims, P c) →
      (∀ r ∈ rows, ∀ col < r.1.width, ∀ v : E,
        P ⟨(globalColumnBases tables).getD r.1.opcode 0 + col, point.take r.2.1, v⟩) →
      RetOK (fun x : E × List ColumnClaim ↦ (∀ c ∈ x.2, P c) ∧
          x.2.length = claims.length + (rows.map fun r ↦ r.1.width).sum)
        (tableTermsClaims tables cp fp point rows cursor final claims)
  | [], _, _, claims, hc, _ => RetOK.ret ⟨hc, by simp⟩
  | r :: rows, cursor, final, claims, hc, hr => by
    unfold tableTermsClaims
    refine (RetOK.readN r.1.width).bind fun evs hevs ↦ ?_
    refine (retOK_tableTermsClaims tables cp fp point P rows _ _ _ ?_
      (fun r' hr' ↦ hr r' (List.mem_cons_of_mem _ hr'))).mono ?_
    · intro c hc'
      rcases List.mem_append.mp hc' with h | h
      · exact hc c h
      · obtain ⟨⟨v, col⟩, hvc, rfl⟩ := List.mem_map.mp h
        have hcol := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hvc)).1
        exact hr r List.mem_cons_self col (by simp only at hcol; omega) v
    · rintro x ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [h2]
      simp [hevs]
      omega

open LeanVM.Protocol.Compile in
/-- **`tableSumcheckClaims`'s returns**: the claims meet `P` when every row's claim at a point of
`max heights` coordinates does; at most `Σ widths` claims. -/
theorem retOK_tableSumcheckClaims (tables : List Verifier.Table) (heights : List ℕ)
    (busForms : List (List Verifier.Form)) (cp fp eqp : List E) (target : E)
    (P : ColumnClaim → Prop)
    (hP : ∀ point : List E, point.length = heights.foldl max 0 →
      ∀ r ∈ List.zip tables (List.zip heights (List.zip busForms
        (Verifier.tableWeights heights eqp point))), ∀ col < r.1.width, ∀ v : E,
        P ⟨(globalColumnBases tables).getD r.1.opcode 0 + col, point.take r.2.1, v⟩) :
    RetOK (fun cl : List ColumnClaim ↦ (∀ c ∈ cl, P c) ∧ cl.length ≤ (tables.map (·.width)).sum)
      (tableSumcheckClaims tables heights busForms cp fp eqp target) := by
  unfold tableSumcheckClaims
  refine (LeanVM.Protocol.EndToEnd.Front.retOK_sumcheck 4 _ _).bind fun x hx ↦ ?_
  obtain ⟨ch, claim⟩ := x
  simp only [List.length_replicate] at hx
  refine (retOK_tableTermsClaims tables cp fp ch.reverse P _ 0 0 [] (by simp)
    (hP ch.reverse (by simpa using hx))).bind fun y hy ↦ ?_
  obtain ⟨final, cl⟩ := y
  refine RetOK.bind_true fun _ ↦ RetOK.ret ⟨hy.1, ?_⟩
  rw [hy.2, List.length_nil, zero_add]
  exact sum_zip_fst_le Verifier.Table.width _ _

/-- The verifier tables' widths are the tables'. -/
theorem sum_width_vTables (T : List Lvm.M3.Tab) :
    ((Lvm.M3.vTables T).map (·.width)).sum = (T.map (·.w)).sum := by
  suffices h : ∀ k, ((T.zipIdx k).map fun x ↦ x.1.w) = T.map (·.w) by
    simp [Lvm.M3.vTables, Lvm.M3.vTable, Verifier.Table.width, List.map_map, Function.comp_def, h]
  induction T with
  | nil => intro; rfl
  | cons t T ih => intro k; simp [List.zipIdx_cons, ih]

/-- Verifier table `k` is table `k`, numbered `k`. -/
theorem getElem_vTables (T : List Lvm.M3.Tab) (k : ℕ) (hk : k < (Lvm.M3.vTables T).length) :
    (Lvm.M3.vTables T)[k] = Lvm.M3.vTable k (T[k]'(by simpa using hk)) := by
  simp [Lvm.M3.vTables, List.getElem_zipIdx]

/-- **Every return of the table phase meets `TabRet`.** -/
theorem retOK_lbusTableCheckProg (T : List Lvm.M3.Tab) (μ : ℕ) :
    RetOK (TabRet T) (Lvm.M3.lbusTableCheckProg T μ) := by
  unfold Lvm.M3.lbusTableCheckProg Lvm.M3.lvmBusTableProg
  refine RetOK.bind (Q' := TabRet T) (RetOK.bind_true fun b ↦ ?_) fun cl hcl ↦
    RetOK.bind_true fun _ ↦ RetOK.ret hcl
  unfold tablePhaseClaims
  refine RetOK.bind_true fun xi ↦ ?_
  refine (retOK_tableSumcheckClaims _ _ _ _ _ _ _ (fun c ↦ ∀ j i,
    Lvm.M3.colLoc T c.column = some (j, i) → c.point.length = (T[j]?.map (·.τ)).getD 0) ?_).bind
    fun cl hcl ↦ RetOK.ret ?_
  · intro point hpt r hr col hcol v j i hloc
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
    have hkT : k < T.length := by
      simp only [List.length_zip, Lvm.M3.length_vTables] at hk; omega
    simp only [List.getElem_zip, getElem_vTables T k (by simpa using hkT)] at hcol hloc ⊢
    simp only [Lvm.M3.vLayout, List.getElem_map, Lvm.M3.vTable, Verifier.Table.width,
      List.length_replicate] at hcol hloc hpt ⊢
    rw [colLoc_base T hkT hcol] at hloc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hloc)
    have := foldl_max_ge (T.map (·.τ)) 0 T[k].τ
      (Or.inr (List.mem_map_of_mem (List.getElem_mem hkT)))
    simp [List.getElem?_eq_getElem hkT]
    omega
  · simp only [Lvm.M3.busResV, Lvm.M3.busFinalV, List.nil_append]
    exact ⟨hcl.1, (sum_width_vTables T) ▸ hcl.2⟩

/-! ## The table claims on the commitments -/

/-- A commitment's cell is its word's entry, `0` past it. -/
theorem comCell_lay26 (qm : Column 26) (qr : Column 19) (rec : Bool) (n : ℕ) :
    Lvm.M3.comCell Lvm.M3.lay26 qm qr rec n =
      if rec then qr.values.getD n 0 else qm.values.getD n 0 := by
  cases rec <;> simp [Lvm.M3.comCell, Vector.getD]
  all_goals (split <;> simp_all)

open CompPoly CMlPolynomialEval in
/-- A block's extension at a point of its height is the `eqAt`-weighted sum of its cells. -/
theorem eval_comBlock_sum (qm : Column 26) (qr : Column 19) (rec : Bool) (τ off : ℕ) (z : List E)
    (hz : z.length = τ) :
    eval₂Mle (Lvm.M3.comBlock Lvm.M3.lay26 qm qr rec τ off).values (algebraMap K E) (vecOf τ z) =
      ∑ n ∈ range (2 ^ τ), eqAt z n * ofK (Lvm.M3.comCell Lvm.M3.lay26 qm qr rec (off + n)) := by
  subst hz
  rw [← sum_eqEval_mul, toList_vecOf z rfl]
  rw [Fin.sum_univ_eq_sum_range (fun x => LeanVM.Protocol.Verifier.eqEval z (boolPoint z.length x) *
    ofK ((Lvm.M3.comBlock Lvm.M3.lay26 qm qr rec z.length off).values.getD x 0))]
  refine sum_congr rfl fun n hn => ?_
  rw [eqEval_boolPoint_eqAt]
  have hn' := mem_range.mp hn
  simp [Lvm.M3.comBlock, Vector.getD, hn']

/-- **The table claims' link**: `tableClaimsE` holding on the commitments gives `BlockHolds`. -/
theorem blockHolds_of_tableClaims {T : List Lvm.M3.Tab} (hlay : Lvm.M3.LayOk Lvm.M3.lay26 T)
    {cl : List ColumnClaim} (hret : TabRet T cl) {qm : Column 26} {qr : Column 19}
    (h : ∀ e ∈ tableClaimsE T cl, HoldsC qm qr e) :
    ∀ c ∈ cl, Lvm.M3.BlockHolds Lvm.M3.lay26 T qm qr c := by
  intro c hc j i hj rec off hloc hcol
  have hi : i < (T.get ⟨j, hj⟩).w := (List.getElem?_eq_some_iff.mp hcol).1
  have hal := hlay (T.get ⟨j, hj⟩) (List.get_mem _ _) i hi
  unfold Lvm.M3.Aligned at hal
  rw [hcol] at hal
  obtain ⟨hdvd, hfit, -⟩ := hal
  have hτ : (T[j]?.map (·.τ)).getD 0 = (T.get ⟨j, hj⟩).τ := by simp [List.getElem?_eq_getElem hj]
  have hz : c.point.length = (T.get ⟨j, hj⟩).τ := (hret.1 c hc j i hloc).trans hτ
  have hmem : (if rec then Com.crec else Com.main,
      BClaim.point ⟨(T.get ⟨j, hj⟩).τ, off⟩ c.point c.value) ∈ tableClaimsE T cl := by
    unfold tableClaimsE
    refine List.mem_filterMap.mpr ⟨c, hc, ?_⟩
    rw [hloc]
    have hcol' : T[j].cols[i]? = some (.com rec off) := hcol
    simp only [Option.bind_some, List.getElem?_eq_getElem hj, hcol']
    rfl
  have hh := h _ hmem
  rw [eval_comBlock_sum qm qr rec _ off c.point hz]
  simp only [comCell_lay26]
  cases rec
  · exact (holds_point hdvd hfit c.point hz c.value qm).mp hh
  · exact (holds_point hdvd hfit c.point hz c.value qr).mp hh

end Lvm.ASM
