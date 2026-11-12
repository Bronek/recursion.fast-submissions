-- new for lvm (AC-S): what the table phase returns, for phase 3b's claim lookups. Adapted from
-- WP-16b's `retOK_tableTermsClaims`/`retOK_tableSumcheckClaims` (lvm/CERT `LvmCertSMid3Tab`), with
-- the sumcheck point kept and the columns' order tracked; WP-9b's `base_eq` (`LvmM3FidFixC`).
import LvmAccSpecPhi
import LvmM3FidFixC

/-!
# The table phase's claims: one per column, in column order, at prefixes of one point

Phase 3b (AC-N's DSL instance in `midS`) reads a fixed column's sent evaluation as the first claim
on its global column (`find?`) and the table point as the longest claim point. Both read the
claims the table sumcheck returned; **`retOK_lvmBusTableProg`**: every return `cl` of WP-9b's
`lvmBusTableProg` on tables `T` has

* strictly increasing columns (`Pairwise (· < ·)`), so a column has at most one claim;
* every claim on global column `base_j + i` (`i < w_j`) at `pt.take τ_j`, for one point `pt` of
  `max τ` coordinates;
* a claim at `pt` itself when some table of maximal height has a column.
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Sound
open Lvm.M3 (Tab vTable vTables vLayout busResV lvmBusTableProg)

/-- Table `k`'s first global column, continued past the last table. -/
def bnd (T : List Tab) (k : ℕ) : ℕ := globalColumnCount + ((T.map (·.w)).take k).sum

theorem bnd_succ (T : List Tab) {k : ℕ} (hk : k < T.length) :
    bnd T (k + 1) = bnd T k + T[k].w := by
  rw [bnd, bnd, List.sum_take_succ _ _ (by simpa using hk), List.getElem_map]; ring

theorem base_bnd (T : List Tab) {k : ℕ} (hk : k < T.length) :
    (globalColumnBases (vTables T)).getD k 0 = bnd T k := Lvm.M3.base_eq T hk

/-- A claim of table `j`'s column `i` at `pt.take τ_j`. -/
def ClaimOf (T : List Tab) (pt : List E) (c : ColumnClaim) : Prop :=
  ∃ j i, ∃ hj : j < T.length, i < T[j].w ∧ c.column = bnd T j + i ∧ c.point = pt.take T[j].τ

/-- **The shape of the table phase's claims.** -/
def ClaimShape (T : List Tab) (cl : List ColumnClaim) : Prop :=
  (cl.map (·.column)).Pairwise (· < ·) ∧
    ∃ pt : List E, pt.length = (T.map (·.τ)).foldl max 0 ∧ (∀ c ∈ cl, ClaimOf T pt c) ∧
      ((∃ t ∈ T, t.τ = (T.map (·.τ)).foldl max 0 ∧ 0 < t.w) → ∃ c ∈ cl, c.point = pt)

/-- The rows of the table loop from table `k` on. -/
def RowsFrom (T : List Tab) (k : ℕ) (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) : Prop :=
  ∀ m (hm : m < rows.length), ∃ hk : k + m < T.length,
    rows[m].1 = vTable (k + m) T[k + m] ∧ rows[m].2.1 = T[k + m].τ

theorem rowsFrom_tail {T : List Tab} {k : ℕ} {r : Verifier.Table × ℕ × List Verifier.Form × E}
    {rows : List (Verifier.Table × ℕ × List Verifier.Form × E)} (h : RowsFrom T k (r :: rows)) :
    RowsFrom T (k + 1) rows := fun m hm ↦ by
  obtain ⟨hk, h1, h2⟩ := h (m + 1) (by simp; omega)
  exact ⟨by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 m] using h1,
    by simpa [Nat.add_assoc, Nat.add_comm 1 m] using h2⟩

/-- New claims of one row: columns `base + i`, increasing. -/
theorem pairwise_newCols (base : ℕ) (evs : List E) (pt : List E) (h : ℕ) :
    ((evs.zipIdx.map fun (x : E × ℕ) ↦ (⟨base + x.2, pt.take h, x.1⟩ : ColumnClaim)).map
      (·.column)).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map, List.length_zipIdx] at hi hj
  simp [List.getElem_map, List.getElem_zipIdx]
  omega

open LeanVM.Protocol.Compile in
/-- **The table loop's returns** (adapted from WP-16b's `retOK_tableTermsClaims`). -/
theorem retOK_terms (T : List Tab) (cp fp pt : List E) (F : Prop) :
    ∀ (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) (k cursor : ℕ) (final : E)
      (claims : List ColumnClaim), RowsFrom T k rows →
      (claims.map (·.column)).Pairwise (· < ·) → (∀ c ∈ claims, c.column < bnd T k ∧ ClaimOf T pt c) →
      (F → (∃ c ∈ claims, c.point = pt) ∨ ∃ m, ∃ hm : m < rows.length, pt.length ≤ rows[m].2.1 ∧
        0 < rows[m].1.width) →
      RetOK (fun x : E × List ColumnClaim ↦ (x.2.map (·.column)).Pairwise (· < ·) ∧
          (∀ c ∈ x.2, ClaimOf T pt c) ∧ (F → ∃ c ∈ x.2, c.point = pt))
        (tableTermsClaims (vTables T) cp fp pt rows cursor final claims)
  | [], _, _, _, claims, _, hp, hc, hf => RetOK.ret ⟨hp, fun c h ↦ (hc c h).2, fun hF ↦ by
      rcases hf hF with hf | ⟨m, hm, -⟩
      · exact hf
      · simp at hm⟩
  | r :: rows, k, cursor, final, claims, hr, hp, hc, hf => by
    obtain ⟨hk, hr1, hr2⟩ := hr 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hk hr1 hr2
    unfold tableTermsClaims
    refine (RetOK.readN r.1.width).bind fun evs hevs ↦ ?_
    have hw : r.1.width = T[k].w := by rw [hr1]; simp [vTable, Table.width]
    have hop : r.1.opcode = k := by rw [hr1]; rfl
    refine retOK_terms T cp fp pt F rows (k + 1) _ _ _ (rowsFrom_tail hr) ?_ ?_ fun hF ↦ ?_
    · rw [List.map_append, List.pairwise_append]
      refine ⟨hp, ?_, ?_⟩
      · rw [hop, base_bnd T hk]; exact pairwise_newCols _ _ _ _
      · intro a ha b hb
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp ha
        obtain ⟨d, hdm, rfl⟩ := List.mem_map.mp hb
        obtain ⟨⟨v, col⟩, -, rfl⟩ := List.mem_map.mp hdm
        have := (hc c hcm).1
        simp only [hop, base_bnd T hk]
        omega
    · intro c hc'
      rcases List.mem_append.mp hc' with h | h
      · exact ⟨by have := (hc c h).1; rw [bnd_succ T hk]; omega, (hc c h).2⟩
      · obtain ⟨⟨v, col⟩, hvc, rfl⟩ := List.mem_map.mp h
        have hcol := (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hvc)).1
        simp only at hcol
        simp only [hop, base_bnd T hk, hr2]
        refine ⟨by rw [bnd_succ T hk]; omega, k, col, hk, by omega, rfl, rfl⟩
    · rcases hf hF with ⟨c, hcm, hcp⟩ | ⟨m, hm, hle, hwp⟩
      · exact .inl ⟨c, List.mem_append_left _ hcm, hcp⟩
      · rcases m with _ | m
        · simp only [List.getElem_cons_zero] at hwp hle
          refine .inl ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨(evs.getD 0 0, 0), ?_, rfl⟩), ?_⟩
          · rw [List.mem_zipIdx_iff_getElem?]
            have h0 : 0 < evs.length := by omega
            simp [List.getElem?_eq_getElem h0, List.getD_eq_getElem _ _ h0]
          · exact List.take_of_length_le hle
        · exact .inr ⟨m, by simpa using hm, by simpa using hle, by simpa using hwp⟩

theorem length_tableWeights (hs : List ℕ) (e p : List E) :
    (Verifier.tableWeights hs e p).length = hs.length := by
  unfold Verifier.tableWeights
  suffices h : ∀ (l : List (E × ℕ)) (w : List E), w.length = hs.length →
      (l.foldl (fun weights (x : E × ℕ) ↦ List.zipWith (fun weight height ↦ weight *
        if x.2 < height then 1 + e.getD x.2 0 + x.1 else x.1) weights hs) w).length = hs.length from
    h _ _ (by simp)
  intro l
  induction l with
  | nil => intro w hw; exact hw
  | cons x l ih => intro w hw; exact ih _ (by simp [hw])

theorem getElem_vTables' (T : List Tab) (m : ℕ) (hm : m < (vTables T).length) :
    (vTables T)[m] = vTable m (T[m]'(by simpa using hm)) := by
  simp [vTables, List.getElem_zipIdx]

open LeanVM.Protocol.Compile in
/-- The table sumcheck's returns (adapted from WP-16b's `retOK_tableSumcheckClaims`). -/
theorem retOK_tsc (T : List Tab) (forms : List (List Verifier.Form)) (cp fp eqp : List E)
    (target : E) (hforms : forms.length = T.length) :
    RetOK (fun cl : List ColumnClaim ↦ (cl.map (·.column)).Pairwise (· < ·) ∧
        ∃ pt : List E, pt.length = (T.map (·.τ)).foldl max 0 ∧ (∀ c ∈ cl, ClaimOf T pt c) ∧
          ((∃ t ∈ T, t.τ = (T.map (·.τ)).foldl max 0 ∧ 0 < t.w) → ∃ c ∈ cl, c.point = pt))
      (tableSumcheckClaims (vTables T) (T.map (·.τ)) forms cp fp eqp target) := by
  unfold tableSumcheckClaims
  refine (LeanVM.Protocol.EndToEnd.Front.retOK_sumcheck 4 _ _).bind fun x hx ↦ ?_
  obtain ⟨ch, claim⟩ := x
  simp only [List.length_replicate] at hx
  let F : Prop := ∃ t ∈ T, t.τ = (T.map (·.τ)).foldl max 0 ∧ 0 < t.w
  refine (retOK_terms T cp fp ch.reverse F _ 0 0 0 [] (fun m hm ↦ ?_) (by simp) (by simp)
    (fun hF ↦ .inr ?_)).bind fun y hy ↦ ?_
  · simp only [List.length_zip, Lvm.M3.length_vTables, List.length_map] at hm
    have hmT : m < T.length := by omega
    refine ⟨by omega, ?_, ?_⟩
    · simp only [List.getElem_zip, zero_add, getElem_vTables' T m (by simpa using hmT)]
    · simp only [List.getElem_zip, zero_add, List.getElem_map]
  · obtain ⟨t, ht, htτ, htw⟩ := hF
    obtain ⟨m, hmT, rfl⟩ := List.getElem_of_mem ht
    have hlen : m < (List.zip (vTables T) (List.zip (T.map (·.τ))
        (List.zip forms (Verifier.tableWeights (T.map (·.τ)) eqp ch.reverse)))).length := by
      simp [length_tableWeights, hforms, hmT]
    refine ⟨m, hlen, ?_, ?_⟩
    · simp only [List.getElem_zip, List.getElem_map, List.length_reverse, hx, ← htτ]; rfl
    · simp only [List.getElem_zip, getElem_vTables' T m (by simpa using hmT)]
      simpa [vTable, Table.width] using htw
  · obtain ⟨final, cl⟩ := y
    refine RetOK.bind_true fun _ ↦ RetOK.ret ⟨hy.1, ch.reverse, by simp [hx], hy.2.1, hy.2.2⟩

open LeanVM.Protocol.Compile in
/-- **Every return of WP-9b's bus and table phases has `ClaimShape`.** -/
theorem retOK_lvmBusTableProg (T : List Tab) (μ : ℕ) :
    RetOK (ClaimShape T) (lvmBusTableProg (vTables T) (vLayout T) μ (busResV T)) := by
  unfold lvmBusTableProg
  refine RetOK.bind_true fun b ↦ ?_
  unfold tablePhaseClaims
  refine RetOK.bind_true fun xi ↦ ?_
  refine (retOK_tsc T _ _ _ _ _ (by simp [Lvm.M3.busResV, Lvm.M3.busFinalV])).bind
    fun cl hcl ↦ RetOK.ret ?_
  simpa [Lvm.M3.busResV, Lvm.M3.busFinalV, ClaimShape] using hcl

end Lvm.Acc
