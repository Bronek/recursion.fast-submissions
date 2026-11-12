-- New for lvm (AC-N, A23): V_S's phase 3b (AC-V's `accFold`) refines its reading over `E`
-- (AC-S's `Acc.accProgV`, `Acc.accProg` on the instance), under the promise that the folded
-- claim holds (V_S checks `AccOk` after the run, `decideF`; the language checks it in the phase).
-- Built on WP-14a's primitives (`ref_samples`, `ref_readEsL`, `ref_sampleE`, `ref_readE`), WP-9b's
-- `colLoc_raw` and AC-S's `phiE`.
import LvmAccNodeRef
import LvmVEqMid
import LvmVEqBus

/-!
# Phase 3b: `accFold` refines `accProgV`

With `cl = claimsOfEvs T evs` (the table phase's claims of the native evaluations, `ref_dTab`):

* `claimAt_claimsOfEvs`: the claim of column `(j, i)` is the native evaluation's;
* `pubOkV_of`, `fixSentV_eq`, `tablePointV_eq'`: `PUB`'s check, the sent fixed evaluations and the
  table point read over `E` are V_S's through `FE.toExt3`;
* **`ref_accFold`**: `accFold P20 (M3.real P20 tabs) pub evs` refines `accProgV P20 tabs pub cl` under
  the promise `AccOk` on its value.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (Tab claimsOfEvs colLoc vTables sumcheckTabs fixColsR fixSentR pubCheckR FixCol busFinalR)

/-! ## Refinement rules under a promise -/

section Rules

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **A native `require` with no language step**: the rest refines, knowing the check held. -/
theorem RefAtP.require_left {α β : Type} {c : Bool} {d : Unit → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} {Q : β → Prop} (hm : ∀ u, MonoD (d u))
    (h : c = true → RefAtP cap shp sig (d ()) P R Q) : RefAtP cap shp sig (DM.require c >>= d) P R Q := by
  intro s hok hq
  have e : runD (DM.require c >>= d) sig s = runD (d ()) sig { s with ok := c && s.ok } := rfl
  rw [e] at hok hq ⊢
  have hc : c = true := (Bool.and_eq_true _ _ ▸ hm () sig _ hok).1
  obtain ⟨a, h1, h2, h3, h4⟩ := h hc _ hok hq
  obtain ⟨c1, c2, c3⟩ := ivp_congr (cap := cap) (shp := shp) P sig
    (s := s) (s' := { s with ok := c && s.ok }) rfl rfl
  exact ⟨a, c1.trans h1, c2.trans h2, c3.trans h3, h4⟩

/-- **A language `require` against a native value**, justified by the promise and what is known. -/
theorem RefAtP.pure_require {β : Type} {b : β} {q : Prop} [Decidable q] {Q : β → Prop}
    (hq : Q b → q) :
    RefAtP cap shp sig (Pure.pure b : DM β) (VerifierProgram.require q) (fun _ _ ↦ True) Q := by
  intro s _ hQ
  have e : VerifierProgram.require q = VerifierProgram.ret () := by
    simp only [VerifierProgram.require, hq hQ, ↓reduceIte]
  rw [e]
  exact ⟨(), rfl, rfl, rfl, trivial⟩

end Rules

/-! ## The claims of the native evaluations -/

theorem find?_eq_of_unique {α : Type} {l : List α} {p : α → Bool} {e : α} (he : e ∈ l) (hp : p e = true)
    (hu : ∀ y ∈ l, p y = true → y = e) : l.find? p = some e := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨e, he, hp⟩)
  rw [hy, hu y (List.mem_of_find?_eq_some hy) (List.find?_some hy)]

section Claims

variable (T : List Tab) (evs : List (List FE × List FE))

open LeanVM.Protocol.Verifier in
/-- Every claim of the native evaluations is on column `(j, i)` with the `j`-th point and value. -/
theorem mem_claimsOfEvs {c : Verifier.ColumnClaim} (hc : c ∈ claimsOfEvs T evs) :
    ∃ j i, ∃ (hj : j < T.length) (hje : j < evs.length), i < evs[j].2.length ∧
      c = ⟨(globalColumnBases (vTables T)).getD j 0 + i, evs[j].1.map FE.toExt3,
        FE.toExt3 (evs[j].2.getD i 0)⟩ := by
  unfold claimsOfEvs at hc
  obtain ⟨⟨⟨t, pe⟩, j⟩, hx, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨v, i⟩, hvi, rfl⟩ := List.mem_map.mp hc
  have hx' := List.mem_zipIdx_iff_getElem?.mp hx
  rw [List.getElem?_zip_eq_some] at hx'
  obtain ⟨h1, h2⟩ := hx'
  have hj : j < T.length := (List.getElem?_eq_some_iff.mp h1).1
  have hje : j < evs.length := (List.getElem?_eq_some_iff.mp h2).1
  have ht : evs[j] = pe := (List.getElem?_eq_some_iff.mp h2).2
  have hv := List.mem_zipIdx_iff_getElem?.mp hvi
  have hi : i < pe.2.length := (List.getElem?_eq_some_iff.mp hv).1
  refine ⟨j, i, hj, hje, by rw [ht]; exact hi, ?_⟩
  have hv' : pe.2[i]? = some v := hv
  have hvd : pe.2.getD i 0 = v := by rw [List.getD_eq_getElem?_getD, hv', Option.getD_some]
  simp only [ht, hvd]

open LeanVM.Protocol.Verifier in
/-- **The claim of column `(j, i)`** among the native evaluations' claims (AC-S's `claimAt` by the
global column number). -/
theorem claimAt_claimsOfEvs (hl : EvLen T evs) {j i : ℕ} (hj : j < T.length) (hje : j < evs.length)
    (hi : i < T[j].w) :
    Lvm.Acc.claimAt (claimsOfEvs T evs) ((globalColumnBases (vTables T)).getD j 0 + i) =
      ⟨(globalColumnBases (vTables T)).getD j 0 + i, evs[j].1.map FE.toExt3,
        FE.toExt3 (evs[j].2.getD i 0)⟩ := by
  unfold Lvm.Acc.claimAt
  rw [find?_eq_of_unique (e := ⟨(globalColumnBases (vTables T)).getD j 0 + i, evs[j].1.map FE.toExt3,
      FE.toExt3 (evs[j].2.getD i 0)⟩), Option.getD_some]
  · unfold claimsOfEvs
    refine List.mem_flatMap.mpr ⟨((T[j], evs[j]), j), ?_, ?_⟩
    · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hje⟩
    · refine List.mem_map.mpr ⟨(evs[j].2.getD i 0, i), ?_, rfl⟩
      rw [List.mem_zipIdx_iff_getElem?]
      have hi' : i < evs[j].2.length := by rw [hl j hj hje]; exact hi
      rw [List.getElem?_eq_getElem hi', List.getD_eq_getElem _ _ hi']
  · simp
  · intro y hy hp
    obtain ⟨j', i', hj', hje', hi', rfl⟩ := mem_claimsOfEvs T evs hy
    simp only [beq_iff_eq] at hp
    have h1 := Lvm.M3.colLoc_raw T hj' (by rw [← hl j' hj' hje']; exact hi')
    rw [hp, Lvm.M3.colLoc_raw T hj hi, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rfl

theorem mem_fixColsR_idx {pt : ℕ} {c : FixCol} (hc : c ∈ fixColsR T pt) :
    ∃ hj : c.tab < T.length, c.col < T[c.tab].w := by
  unfold fixColsR at hc
  obtain ⟨⟨t, j⟩, htj, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨⟨src, i⟩, hsi, hc⟩ := List.mem_filterMap.mp hc
  have ht := List.mem_zipIdx_iff_getElem?.mp htj
  have hs := List.mem_zipIdx_iff_getElem?.mp hsi
  obtain ⟨hj, htj'⟩ := List.getElem?_eq_some_iff.mp ht
  cases src with
  | com _ _ => simp at hc
  | fix f e =>
    simp only at hc
    split_ifs at hc
    obtain rfl := Option.some.inj hc
    refine ⟨hj, ?_⟩
    simp only [Tab.w, htj']
    exact (List.getElem?_eq_some_iff.mp hs).1

/-- **The sent fixed evaluations over `E`** (`yOwnV`'s list) are V_S's. -/
theorem fixSentV_eq (hl : EvLen T evs) (hn : evs.length = T.length) (pt : ℕ) :
    ((fixColsR T pt).map fun c ↦ (Lvm.Acc.claimAt (claimsOfEvs T evs) (Lvm.Acc.gcol T c)).value) =
      (fixSentR T pt evs).map FE.toExt3 := by
  unfold fixSentR
  rw [List.map_map]
  refine List.map_congr_left fun c hc ↦ ?_
  obtain ⟨hj, hi⟩ := mem_fixColsR_idx T hc
  rw [Lvm.Acc.gcol, claimAt_claimsOfEvs T evs hl hj (by omega) hi, Function.comp_apply,
    List.getD_eq_getElem evs _ (by omega)]

/-- **`PUB`'s check over `E`** from V_S's. -/
theorem pubOkV_of (hl : EvLen T evs) (hn : evs.length = T.length) {pt : ℕ} (hpt : pt < T.length)
    (hw : 0 < T[pt].w) {pub : Pub} (h : pubCheckR pt pub evs = true) :
    Lvm.Acc.pubOkV T pt pub (claimsOfEvs T evs) = true := by
  unfold Lvm.Acc.pubOkV
  rw [claimAt_claimsOfEvs T evs hl hpt (by omega) hw]
  unfold pubCheckR at h
  rw [List.getD_eq_getElem _ _ (by omega)] at h
  simp only [List.map_map, Function.comp_def, FE.ofExt3_toExt3, List.map_id', decide_eq_true_eq]
  exact congrArg FE.toExt3 (Lvm.M3.FE_eq_of_beq h)

/-- The "longest so far" step. -/
def lstep {β : Type} (r p : List β) : List β := if r.length < p.length then p else r

theorem lstep_idem {β : Type} (r p : List β) : lstep (lstep r p) p = lstep r p := by
  unfold lstep; split_ifs <;> simp_all

theorem lstep_map (r p : List FE) : lstep (r.map FE.toExt3) (p.map FE.toExt3) = (lstep r p).map FE.toExt3 := by
  unfold lstep; simp only [List.length_map]; split_ifs <;> rfl

/-- A nonempty run of claims on one point folds to one step. -/
theorem foldl_rep (P : List E) : ∀ (l : List Verifier.ColumnClaim) (r : List E), l ≠ [] →
    (∀ c ∈ l, c.point = P) → l.foldl (fun r c ↦ lstep r c.point) r = lstep r P
  | [], _, h, _ => absurd rfl h
  | [c], r, _, hc => by simp [hc c (by simp)]
  | c :: c' :: l, r, _, hc => by
    rw [List.foldl_cons, hc c (by simp), foldl_rep P (c' :: l) _ (by simp)
      (fun d hd ↦ hc d (List.mem_cons_of_mem _ hd)), lstep_idem]

theorem foldl_blocks {X : Type} (F : X → List Verifier.ColumnClaim) (P : X → List FE) :
    ∀ (L : List X) (r : List FE), (∀ x ∈ L, F x ≠ [] ∧ ∀ c ∈ F x, c.point = (P x).map FE.toExt3) →
      L.foldl (fun acc x ↦ (F x).foldl (fun r c ↦ lstep r c.point) acc) (r.map FE.toExt3) =
        ((L.map P).foldl lstep r).map FE.toExt3
  | [], _, _ => rfl
  | x :: L, r, h => by
    rw [List.foldl_cons, foldl_rep _ _ _ (h x (by simp)).1 (h x (by simp)).2, lstep_map,
      foldl_blocks F P L _ fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- **The table point over `E`** is V_S's (every table has a column). -/
theorem tablePointV_eq' (hl : EvLen T evs) (hn : evs.length = T.length) (hw : ∀ t ∈ T, 0 < t.w) :
    Lvm.Acc.tablePointV (claimsOfEvs T evs) = (tablePoint evs).map FE.toExt3 := by
  have hT : tablePoint evs = (evs.map (·.1)).foldl lstep [] := by
    unfold tablePoint; rw [List.foldl_map]; rfl
  have hE : Lvm.Acc.tablePointV (claimsOfEvs T evs) =
      (claimsOfEvs T evs).foldl (fun r c ↦ lstep r c.point) (([] : List FE).map FE.toExt3) := rfl
  rw [hT, hE]
  unfold claimsOfEvs
  rw [List.foldl_flatMap, foldl_blocks _ (fun x ↦ x.1.2.1)]
  · congr 2
    have e1 : ((T.zip evs).zipIdx.map fun x ↦ x.1.2.1) = ((T.zip evs).zipIdx.map Prod.fst).map
        (·.2.1) := by rw [List.map_map]; rfl
    rw [e1, List.zipIdx_map_fst, show ((T.zip evs).map fun x ↦ x.2.1) = ((T.zip evs).map Prod.snd).map
        (·.1) by rw [List.map_map]; rfl, List.map_snd_zip (by omega)]
  · intro x hx
    have hx' := List.mem_zipIdx_iff_getElem?.mp hx
    rw [List.getElem?_zip_eq_some] at hx'
    obtain ⟨h1, h2⟩ := hx'
    obtain ⟨hj, ht⟩ := List.getElem?_eq_some_iff.mp h1
    obtain ⟨hje, he⟩ := List.getElem?_eq_some_iff.mp h2
    refine ⟨?_, fun c hc ↦ ?_⟩
    · have hlen : x.1.2.2.length = T[x.2].w := by rw [← he]; exact hl _ hj hje
      have hpos := hw _ (List.getElem_mem hj)
      intro hnil
      rw [List.map_eq_nil_iff, List.zipIdx_eq_nil_iff] at hnil
      rw [hnil] at hlen
      simp at hlen
      omega
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc
      rfl

end Claims


/-! ## Arithmetic over `E` -/

theorem hEval_map (x : FE) : ∀ l : List FE,
    Lvm.Acc.hEval (l.map FE.toExt3) (FE.toExt3 x) = FE.toExt3 (Lvm.polyEval l x)
  | [] => by simp [Lvm.Acc.hEval, Lvm.polyEval]
  | c :: l => by
    rw [List.map_cons, Lvm.Acc.hEval_cons, hEval_map x l]
    simp only [Lvm.polyEval, List.foldr_cons] at *
    rw [FE.toExt3_add, FE.toExt3_mul]
    ring

theorem line_map (t : FE) : ∀ a b : List FE,
    Lvm.Acc.line (a.map FE.toExt3) (b.map FE.toExt3) (FE.toExt3 t) = (accLine a b t).map FE.toExt3
  | [], _ => by simp [Lvm.Acc.line, accLine]
  | _ :: _, [] => by simp [Lvm.Acc.line, accLine]
  | x :: a, y :: b => by
    have ih := line_map t a b
    simp only [Lvm.Acc.line, accLine, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih, FE.toExt3_add, FE.toExt3_mul, FE.toExt3_add]

theorem sumE_map (l : List FE) : (l.map FE.toExt3).sum = FE.toExt3 (Lvm.sumE l) := by
  rw [toExt3_sumE, Verifier.sumE, ← List.sum_eq_foldl]

/-! ## Values of native steps (the evaluations' count) -/

/-- Every run's value satisfies `P`. -/
def ValP {β : Type} (d : DM β) (P : β → Prop) : Prop := ∀ sig s, P (runD d sig s).1

theorem ValP.bind {β β' : Type} {d : DM β} {d' : β → DM β'} {P : β → Prop} {P' : β' → Prop}
    (h : ValP d P) (h' : ∀ b, P b → ValP (d' b) P') : ValP (d >>= d') P' :=
  fun sig s ↦ h' _ (h sig s) sig _

theorem ValP.any {β β' : Type} {d : DM β} {d' : β → DM β'} {P' : β' → Prop}
    (h' : ∀ b, ValP (d' b) P') : ValP (d >>= d') P' :=
  fun sig s ↦ h' _ sig _

theorem ValP.pure {β : Type} {b : β} {P : β → Prop} (h : P b) : ValP (Pure.pure b : DM β) P :=
  fun _ _ ↦ h

theorem RefAt.and_valP {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} {α β : Type} {d : DM β}
    {P : VerifierProgram α} {R : β → α → Prop} {V : β → Prop} (h : RefAt cap shp sig d P R)
    (hv : ValP d V) : RefAt cap shp sig d P fun b a ↦ R b a ∧ V b :=
  fun s hok ↦ by
    obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
    exact ⟨a, h1, h2, h3, h4, hv sig s⟩

theorem valP_tableTerms (cp fp point : List FE) :
    ∀ (rows : List (TableSpec × List Lvm.Form × FE)) (cursor : ℕ) (final : FE),
      ValP (Lvm.tableTerms cp fp point rows cursor final) fun x ↦ x.2.length = rows.length
  | [], _, _ => ValP.pure rfl
  | (t, fs, w) :: rows, cursor, final => by
    unfold Lvm.tableTerms
    refine ValP.any fun ev ↦ (valP_tableTerms cp fp point rows _ _).bind fun x hx ↦ ?_
    obtain ⟨f, rs⟩ := x
    exact ValP.pure (by simpa using hx)

theorem length_tableWeightsN (heights : List ℕ) (eqp point : List FE) :
    (Lvm.tableWeights heights eqp point).length = heights.length := by
  unfold Lvm.tableWeights
  suffices h : ∀ (l : List (FE × ℕ)) (acc : List FE), acc.length = heights.length →
      (l.foldl (fun weights (x : FE × ℕ) ↦ List.zipWith (fun weight height ↦
        weight * if x.2 < height then 1 + eqp.getD x.2 0 + x.1 else x.1) weights heights) acc).length =
        heights.length from h _ _ (by simp)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x l ih => intro acc h; exact ih _ (by simp [h])

theorem valP_tableSumcheck (rounds : ℕ) (tables : List TableSpec) (fs : List (List Lvm.Form))
    (cp fp eqp : List FE) (target : FE) (hfs : tables.length ≤ fs.length) :
    ValP (Lvm.tableSumcheck rounds tables fs cp fp eqp target) fun evs ↦ evs.length = tables.length := by
  unfold Lvm.tableSumcheck
  refine ValP.any fun x ↦ ?_
  obtain ⟨ch, claim⟩ := x
  refine (valP_tableTerms _ _ _ _ _ _).bind fun y hy ↦ ?_
  obtain ⟨fin, evs⟩ := y
  refine ValP.any fun _ ↦ ValP.pure ?_
  simp only [List.length_zip, length_tableWeightsN, List.length_map] at hy
  simp only [hy]
  omega

theorem valP_dBus (p : Params) (tabs : Pub → List Tab) (pub : Pub) :
    ValP (dBus p (M3.real p tabs) pub) fun pb ↦ pb.2.forms.length = (sumcheckTabs (tabs pub)).length := by
  unfold dBus
  refine ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.any fun x ↦ ?_
  obtain ⟨cr, pt, vs⟩ := x
  refine ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.any fun _ ↦ ValP.pure ?_
  show (busFinalR _ _).forms.length = _
  simp [busFinalR]

/-- **Phases 2–3 with the evaluations' count** (every sumcheck table's point and values). -/
theorem ref_busTabL (sig : ByteArray) (tabs : Pub → List M3.Tab) (pub : Pub) (F : Fit P20 (tabs pub)) :
    Ref20 sig (dBus P20 (M3.real P20 tabs) pub >>= fun pb ↦
        dTab P20 (M3.real P20 tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev))
      (M3.lvmBusTableProg (M3.vTables (sumcheckTabs (tabs pub))) (M3.vLayout (sumcheckTabs (tabs pub)))
        P20.busDepth (M3.busResV (sumcheckTabs (tabs pub))))
      fun r cl ↦ TabRel (sumcheckTabs (tabs pub)) r cl ∧ r.2.length = (sumcheckTabs (tabs pub)).length :=
  RefAt.and_valP (ref_busTab sig tabs pub F) <| (valP_dBus P20 tabs pub).bind fun pb hpb ↦ by
    have hT : ValP (dTab P20 (M3.real P20 tabs) pub pb.1 pb.2)
        fun ev ↦ ev.length = (sumcheckTabs (tabs pub)).length := by
      unfold dTab
      refine ValP.any fun _ ↦ ?_
      have h := valP_tableSumcheck P20.tableRounds ((M3.real P20 tabs).tables pub) pb.2.forms
      simp only [real_tables, List.length_map] at h ⊢
      exact h _ _ _ _ (by rw [hpb])
    exact hT.bind fun ev hev ↦ ValP.pure hev

/-! ## Phase 3b -/

section Fold

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

theorem real_pubCheck (p : Params) (tabs : Pub → List Tab) (pub : Pub) (evs : List (List FE × List FE)) :
    (M3.real p tabs).pubCheck pub evs = pubCheckR p.pubTab pub evs := rfl

theorem real_fixSent (p : Params) (tabs : Pub → List Tab) (pub : Pub) (evs : List (List FE × List FE)) :
    (M3.real p tabs).fixSent pub evs = fixSentR (sumcheckTabs (tabs pub)) p.pubTab evs := rfl

theorem monoD_accFold (p : Params) (m : M3) (pub : Pub) (evs : List (List FE × List FE)) :
    MonoD (accFold p m pub evs) :=
  (MonoD.require _).bind fun _ ↦ (monoD_samples _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

/-- **Phase 3b refines `accProgV`** under the promise that the folded claim holds (`AccOk`, which
V_S checks after the run): `PUB`'s check, the line polynomial's values at 0 and 1, the zero scalar,
and `Φ̃(line(t)) = h(t)` hold over `E` wherever they hold natively. -/
theorem ref_accFold (tabs : Pub → List Tab) (pub : Pub) (evs : List (List FE × List FE))
    (hl : EvLen (sumcheckTabs (tabs pub)) evs) (hn : evs.length = (sumcheckTabs (tabs pub)).length)
    (hpt : P20.pubTab < (sumcheckTabs (tabs pub)).length)
    (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w) :
    RefAtP cap shp sig (accFold P20 (M3.real P20 tabs) pub evs)
      (Lvm.Acc.accProgV P20 tabs pub (claimsOfEvs (sumcheckTabs (tabs pub)) evs)) (fun _ _ ↦ True)
      (fun a ↦ AccOk P20 (M3.real P20 tabs) pub a = true) := by
  unfold accFold Lvm.Acc.accProgV Lvm.Acc.accProg
  refine RefAtP.require_left (fun _ ↦ (monoD_samples _).bind fun _ ↦ (monoD_readEs _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) fun hpc ↦ ?_
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_readEs _).bind fun _ ↦
    monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    ((ref_samples _).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro κ _ rfl -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_sampleE.bind fun _ ↦ monoD_readE.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    ((ref_readEsL _).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro h _ ⟨rfl, hlen⟩ -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ monoD_readE.bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
        MonoD.pure _)
    (ref_sampleE.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro t _ rfl -
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (MonoD.require _).bind fun _ ↦
      (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (ref_readE.toP _) (fun _ _ _ ↦ trivial) ?_
  rintro z _ rfl -
  dsimp only
  refine RefAtP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    MonoD.pure _) fun h0 ↦ ?_
  refine RefAtP.require_left (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) fun h1 ↦ ?_
  refine RefAtP.require_left (fun _ ↦ MonoD.pure _) fun hz ↦ ?_
  refine RefAtP.pure_require fun hA ↦ ?_
  set T := sumcheckTabs (tabs pub)
  have hw' : 0 < T[P20.pubTab].w := hw _ (List.getElem_mem hpt)
  refine ⟨pubOkV_of T evs hl hn hpt hw' hpc, ?_, ?_, ?_, ?_⟩
  · rw [Lvm.Acc.hEval_zero, ← toExt3_headD, Lvm.M3.FE_eq_of_beq h0]
  · rw [Lvm.Acc.hEval_one, sumE_map, Lvm.M3.FE_eq_of_beq h1, real_fixSent, Lvm.Acc.yOwnV,
      fixSentV_eq T evs hl hn, ← map_eqKernel, toExt3_dot]
  · rw [Lvm.M3.FE_eq_of_beq hz, FE.toExt3_zero]
  · have hA' := Lvm.M3.FE_eq_of_beq hA
    rw [tablePointV_eq' T evs hl hn hw, ← List.map_append, line_map, Lvm.Acc.PhiV, List.map_map,
      show (FE.ofExt3 ∘ FE.toExt3) = id from funext FE.ofExt3_toExt3, List.map_id, hEval_map]
    exact congrArg FE.toExt3 hA'

/-- **Phases 2–3b refine `busTabAccProg`** under the promise that phase 3b's folded claim holds. -/
theorem ref_busTabAcc (sig : ByteArray) (tabs : Pub → List Tab) (pub : Pub) (F : Fit P20 (tabs pub))
    (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w) :
    RefAtP capS shpS sig ((dBus P20 (M3.real P20 tabs) pub >>= fun pb ↦
        dTab P20 (M3.real P20 tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) >>= fun bt ↦
          accFold P20 (M3.real P20 tabs) pub bt.2 >>= fun acc ↦ pure (bt, acc))
      (busTabAccProg tabs pub) (fun bta cl ↦ TabRel (sumcheckTabs (tabs pub)) bta.1 cl)
      (fun bta ↦ AccOk P20 (M3.real P20 tabs) pub bta.2 = true) := by
  unfold busTabAccProg Lvm.Acc.lbusTableAccProg
  refine RefAtP.bind (Q := fun _ ↦ True) (fun _ ↦ (monoD_accFold _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ((ref_busTabL sig tabs pub F).toP _) (fun _ _ _ ↦ trivial) ?_
  rintro bt cl ⟨hR, hlen⟩ -
  have hR' := hR
  obtain ⟨-, -, rfl, hl⟩ := hR'
  refine RefAtP.bind (Q := fun acc ↦ AccOk P20 (M3.real P20 tabs) pub acc = true) (fun _ ↦ MonoD.pure _)
    (ref_accFold tabs pub bt.2 hl hlen F.pubTab hw) (fun _ _ h ↦ h) ?_
  intro acc _ _ _
  exact (RefAt.pure (b := (bt, acc)) (R := fun bta cl ↦ TabRel (sumcheckTabs (tabs pub)) bta.1 cl) hR).toP _

end Fold

end Lvm.VEq
