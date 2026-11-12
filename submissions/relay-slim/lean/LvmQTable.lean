-- New for lvm (WP-11b-QA2, H2): the table sumcheck's weights and final check as straight-line
-- gadgets. Searched leanerVM `Protocol/TableSumcheck.lean` (`tableWeights` over `Fin τmax`, a
-- per-coordinate pair, no product closed form we could reuse) and `ClaimWeights.lean`; the closed
-- form `tableWeights_eq` below is new.
import LvmQBusGkr

/-!
# The table sumcheck: weights and the final check (`F`'s `tableSumcheck`)

`F` (`LvmDecideSumcheck.tableSumcheck`): the rounds (plain, count 4: `LvmQBusRound.scRunP4`), the
point = the challenges reversed, the weights `tableWeights heights equalityPoint point` (per table
`Π_{c<R} (c < h ? 1 + e_c + r_c : r_c)`), the per-table terms (`tableTerms`, from the M3 tables'
constraints and bus forms: WP-9/WP-10, **inputs here**), and `require (final == claim)`.

* `tableWeights_eq`: the closed form `Π_{c < min h R} (1 + e_c + r_c) · Π_{j < R − min h R} ch_j`
  with `r_c = ch_{R−1−c}` (`ch` the challenges in round order: the suffix products of the point are
  prefix products of the challenges).
* `prefG`: a running product (one `E·E+E` row per factor, after the factor's own rows);
  `tableW`: the prefix products `A_m` (a `lin` and a product row per coordinate), the challenges'
  prefix products `B_m` (one row per round) and one row per table, `A_{min h R} · B_{R − min h R}`.
  Rows: `3R + T` (`R` `lin` 12 words, `2R + T` `E·E+E` 16 words).
* `tableFinal`: `Σ_t w_t · τ_t` (one row per table) and `assertEq` with the claim.

Theorems: **`tableW_spec`** (= `F`'s `tableWeights`), `tableTerms_final` (`F`'s final is
`finalOf weights terms`), **`tableFinal_check`** (gate on: assertion ↔ `F`'s `final == claim`).
-/

set_option autoImplicit false

namespace Lvm.QB

open Lvm DM

/-! ## `F`'s weights in closed form -/

/-- Table weight of height `h` from coordinate `k` on. -/
def wF (e pt : List FE) (k h : Nat) : FE :=
  ∏ j ∈ Finset.range pt.length, if k + j < h then 1 + e.getD (k + j) 0 + pt.getD j 0 else pt.getD j 0

theorem zipWith_zipWith_same {α β γ δ : Type} (f₁ : α → β → γ) (f₂ : γ → β → δ) :
    ∀ (ws : List α) (hs : List β),
      List.zipWith f₂ (List.zipWith f₁ ws hs) hs = List.zipWith (fun w h => f₂ (f₁ w h) h) ws hs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | w :: ws, h :: hs => by simp [zipWith_zipWith_same f₁ f₂ ws hs]

theorem zipWith_mul_one (hs : List Nat) : ∀ ws : List FE, ws.length ≤ hs.length →
    List.zipWith (fun w (_ : Nat) => w * 1) ws hs = ws
  | [], _ => by simp
  | w :: ws, h => by
    cases hs with
    | nil => simp at h
    | cons x hs =>
      simp only [List.zipWith_cons_cons, mul_one, List.cons.injEq, true_and]
      have := zipWith_mul_one hs ws (by simpa using h)
      simpa using this

/-- The fold of `tableWeights` from coordinate `k` on. -/
theorem weights_fold (e : List FE) (hs : List Nat) (pt : List FE) : ∀ (k : Nat) (ws : List FE),
    ws.length ≤ hs.length →
    (pt.zipIdx k).foldl (fun weights (x : FE × Nat) =>
      List.zipWith (fun weight height => weight * if x.2 < height then 1 + e.getD x.2 0 + x.1 else x.1)
        weights hs) ws =
      List.zipWith (fun w h => w * wF e pt k h) ws hs := by
  induction pt with
  | nil =>
    intro k ws hl
    simp only [List.zipIdx_nil, List.foldl_nil, wF, List.length_nil, Finset.range_zero,
      Finset.prod_empty]
    exact (zipWith_mul_one hs ws hl).symm
  | cons r pt ih =>
    intro k ws hl
    rw [List.zipIdx_cons, List.foldl_cons]
    have hl' : (List.zipWith (fun weight height => weight *
        if k < height then 1 + e.getD k 0 + r else r) ws hs).length ≤ hs.length := by
      rw [List.length_zipWith]; exact Nat.min_le_right _ _
    have := ih (k + 1) _ hl'
    refine this.trans ?_
    rw [zipWith_zipWith_same]
    refine congrArg (List.zipWith · ws hs) (funext fun w => funext fun h => ?_)
    simp only [wF, List.length_cons, Finset.prod_range_succ', List.getD_cons_succ,
      List.getD_cons_zero, Nat.add_zero]
    rw [mul_assoc, mul_comm (if k < h then _ else _)]
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show k + (j + 1) = k + 1 + j by omega]

/-- **`F`'s table weights**: one product per table. -/
theorem tableWeights_eq (hs : List Nat) (e pt : List FE) :
    tableWeights hs e pt = hs.map (wF e pt 0) := by
  unfold tableWeights
  dsimp only
  rw [weights_fold e hs pt 0 _ (by simp)]
  induction hs with
  | nil => rfl
  | cons h hs ih => simp only [List.map_cons, List.zipWith_cons_cons, one_mul, ih]

/-- **`F`'s weights at the reversed challenges** in closed form: with `m = min h R`,
`Π_{c<m} (1 + e_c + ch_{R−1−c}) · Π_{j < R − m} ch_j`. -/
theorem wF_rev (e chs : List FE) (h : Nat) :
    wF e chs.reverse 0 h =
      (∏ c ∈ Finset.range (min h chs.length),
        (1 + e.getD c 0 + chs.getD (chs.length - 1 - c) 0)) *
      ∏ j ∈ Finset.range (chs.length - min h chs.length), chs.getD j 0 := by
  set R := chs.length with hR
  set m := min h R with hm
  have hrev : ∀ c < R, chs.reverse.getD c 0 = chs.getD (R - 1 - c) 0 := by
    intro c hc
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_reverse,
      List.getD_eq_getElem _ _ (by omega)]
  unfold wF
  rw [List.length_reverse, ← hR, show R = m + (R - m) by omega, Finset.prod_range_add]
  rw [show m + (R - m) - m = R - m by omega]
  congr 1
  · refine Finset.prod_congr rfl fun c hc => ?_
    have hc' := Finset.mem_range.mp hc
    rw [if_pos (by omega), Nat.zero_add, hrev c (by omega)]
    congr 3; omega
  · rw [← Finset.prod_range_reflect (fun j => chs.getD j 0)]
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    rw [if_neg (by omega), hrev _ (by omega)]
    congr 1; omega

/-! ## `F`'s final: the weighted sum of the terms -/

/-- `Σ_t w_t · τ_t`, accumulated as `F` does. -/
def finalOf (ws ts : List FE) (f₀ : FE) : FE := (ws.zip ts).foldl (fun f wt => f + wt.1 * wt.2) f₀

/-- The per-table terms `tableTerms` adds (`summand + dot formPowers forms`), in order. -/
def tableTermT (constraintPowers formPowers point : List FE) :
    List (TableSpec × List Form × FE) → Nat → DM (List FE)
  | [], _ => pure []
  | (table, forms, _) :: rest, cursor => do
    let evaluations ← readEs table.width
    let tpoint := point.take table.logHeight
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints tpoint evaluations)
    let term := summand + dot formPowers (forms.map (·.value (evaluations.getD · 0)))
    let terms ← tableTermT constraintPowers formPowers point rest (cursor + table.nConstraints)
    pure (term :: terms)

/-- **`F`'s table final** is `finalOf` of the weights and the terms (same reads). -/
theorem tableTerms_final (cp fp point : List FE) (sig : ByteArray) :
    ∀ (rows : List (TableSpec × List Form × FE)) (cursor : Nat) (final : FE) (s : RS),
      (tableTerms cp fp point rows cursor final sig s).1.1 =
          finalOf (rows.map (·.2.2)) (tableTermT cp fp point rows cursor sig s).1 final ∧
        (tableTerms cp fp point rows cursor final sig s).2 = (tableTermT cp fp point rows cursor sig s).2
  | [], _, _, _ => ⟨rfl, rfl⟩
  | (table, forms, weight) :: rest, cursor, final, s => by
    have ih := fun f s' => tableTerms_final cp fp point sig rest (cursor + table.nConstraints) f s'
    show (tableTerms cp fp point rest (cursor + table.nConstraints) (final + weight * _) sig
        (readEs table.width sig s).2).1.1 = _ ∧ (tableTerms cp fp point rest _ _ sig _).2 = _
    rw [(ih _ _).1, (ih _ _).2]
    exact ⟨rfl, rfl⟩

end Lvm.QB

namespace Lvm.Loop.Build.QB

open Lvm.Loop Lvm.QB

/-! ## The weights gadget -/

/-- **A running product** `o · x₀ ⋯ x_{n−1}` (the factor `x_c` from the gadget `step c`), all
its running values `[A₀, …, A_n]`. -/
def prefG (z o : Cell) (step : Nat → BM Cell) : Nat → BM (List Cell)
  | 0 => pure [o]
  | n + 1 => do
    let as ← prefG z o step n
    let x ← step n
    let a ← mulAdd .E x (as.getD n o) z
    pure (as ++ [a])

/-- One weight per table: `A_{min h R} · B_{R − min h R}`. -/
def weightsG (z o : Cell) (A B : List Cell) (R : Nat) : List Nat → BM (List Cell)
  | [] => pure []
  | h :: hs => do
    let w ← mulAdd .E (A.getD (min h R) o) (B.getD (R - min h R) o) z
    let ws ← weightsG z o A B R hs
    pure (w :: ws)

/-- **The table weights**: `e c` the equality point's cells, `ch j` the table sumcheck's challenge
cells (round order), `R` the rounds, `hs` the tables' heights. -/
def tableW (z o : Cell) (e ch : Nat → Cell) (R : Nat) (hs : List Nat) : BM (List Cell) := do
  let A ← prefG z o (fun c => lin .E 1 1 (e c) (ch (R - 1 - c))) R
  let B ← prefG z o (fun j => pure (ch j)) R
  weightsG z o A B R hs

section
variable {c : Ctx} {M : Mem}

theorem prefG_spec {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (step : Nat → BM Cell)
    (fv : Nat → FE) (hstep : ∀ k, ASpec c M (step k) (fun x => x.val M = fv k) True) :
    ∀ n, ASpec c M (prefG z o step n)
      (fun as => as.length = n + 1 ∧ ∀ m ≤ n, (as.getD m o).val M = ∏ k ∈ Finset.range m, fv k) True
  | 0 => aspec_pure ⟨rfl, fun m hm => by
      obtain rfl : m = 0 := by omega
      simp [ho]⟩
  | n + 1 => by
    show ASpec c M (prefG z o step n >>= fun as => step n >>= fun x =>
      mulAdd .E x (as.getD n o) z >>= fun a => pure (as ++ [a])) _ _
    refine aspec_congr (aspec_bind (prefG_spec hz ho step fv hstep n) fun as has =>
      aspec_bind (hstep n) fun x hx =>
        aspec_bind (aspec_mulAdd (c := c) (M := M) .E x (as.getD n o) z) fun a ha =>
          aspec_pure (x := as ++ [a]) ?_) (fun _ h => h) (by simp)
    refine ⟨by simp [has.1], fun m hm => ?_⟩
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · rw [List.getD_append _ _ _ _ (by omega)]; exact has.2 m (by omega)
    · obtain rfl : m = n + 1 := by omega
      rw [List.getD_append_right _ _ _ _ (by omega), has.1, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [ha, hx, has.2 n le_rfl, hz, add_zero, Finset.prod_range_succ, mul_comm]

theorem weightsG_spec {z o : Cell} (hz : z.val M = 0) (A B : List Cell) (R : Nat) (fA fB : Nat → FE)
    (hA : ∀ m ≤ R, (A.getD m o).val M = fA m) (hB : ∀ m ≤ R, (B.getD m o).val M = fB m) :
    ∀ hs : List Nat, ASpec c M (weightsG z o A B R hs)
      (fun ws => vals M ws = hs.map fun h => fA (min h R) * fB (R - min h R)) True
  | [] => aspec_pure rfl
  | h :: hs => by
    show ASpec c M (mulAdd .E (A.getD (min h R) o) (B.getD (R - min h R) o) z >>= fun w =>
      weightsG z o A B R hs >>= fun ws => pure (w :: ws)) _ _
    refine aspec_congr (aspec_bind (aspec_mulAdd (c := c) (M := M) .E _ _ z) fun w hw =>
      aspec_bind (weightsG_spec hz A B R fA fB hA hB hs) fun ws hws =>
        aspec_pure (x := w :: ws) ?_) (fun _ h => h) (by simp)
    simp only [vals, List.map_cons] at hws ⊢
    rw [hws, hw, hA _ (Nat.min_le_right _ _), hB _ (Nat.sub_le _ _), hz, add_zero]

/-- **The weights gadget's values**, in closed form. -/
theorem tableW_spec {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (e ch : Nat → Cell) (R : Nat)
    (hs : List Nat) :
    ASpec c M (tableW z o e ch R hs)
      (fun ws => vals M ws = hs.map fun h =>
        (∏ k ∈ Finset.range (min h R), (1 + (e k).val M + (ch (R - 1 - k)).val M)) *
          ∏ j ∈ Finset.range (R - min h R), (ch j).val M) True := by
  have hA := prefG_spec (c := c) hz ho (fun k => lin .E 1 1 (e k) (ch (R - 1 - k)))
    (fun k => 1 + (e k).val M + (ch (R - 1 - k)).val M)
    (fun k => aspec_congr (aspec_lin .E 1 1 _ _) (fun x hx => by
      rw [hx, ofK_one, one_mul]; ring) Iff.rfl) R
  have hB := prefG_spec (c := c) hz ho (fun j => pure (ch j)) (fun j => (ch j).val M)
    (fun j => aspec_pure rfl) R
  have := aspec_bind hA fun A hA' => aspec_bind hB fun B hB' =>
    weightsG_spec (c := c) hz A B R _ _ hA'.2 hB'.2 hs
  exact aspec_congr this (fun _ h => h) (by simp)

/-- **Q_arith_eq, the table weights**: with the cells holding `F`'s equality point and the
table sumcheck's challenges (`R` of them), the outputs are `F`'s `tableWeights heights
equalityPoint (challenges.reverse)`. -/
theorem tableW_eq {z o : Cell} (hz : z.val M = 0) (ho : o.val M = 1) (e ch : Nat → Cell)
    (hs : List Nat) (eqPt chs : List FE) (he : ∀ k < chs.length, (e k).val M = eqPt.getD k 0)
    (hch : ∀ j < chs.length, (ch j).val M = chs.getD j 0) (p : Ptr)
    (h : SegsHold c M p (tableW z o e ch chs.length hs p).2) :
    vals M (tableW z o e ch chs.length hs p).1 = tableWeights hs eqPt chs.reverse := by
  rw [(tableW_spec (c := c) hz ho e ch chs.length hs p h).1, tableWeights_eq]
  refine List.map_congr_left fun hh _ => ?_
  rw [wF_rev]
  congr 1
  · refine Finset.prod_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.mp hk
    rw [he k (by omega), hch _ (by omega)]
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    rw [hch j (by omega)]

/-! ## The final check -/

/-- `acc + Σ_t w_t · τ_t` (one `E·E+E` row per table). -/
def dotFrom : Cell → List Cell → List Cell → BM Cell
  | acc, w :: ws, t :: ts => do
    let a ← mulAdd .E w t acc
    dotFrom a ws ts
  | acc, _, _ => pure acc

/-- **The table sumcheck's final check**: `Σ_t w_t · τ_t` (the terms `τ_t` are inputs) against the
sumcheck's final claim, gated. -/
def tableFinal (z gate claim : Cell) (ws ts : List Cell) : BM Unit := do
  let f ← dotFrom z ws ts
  assertEq f claim gate

theorem dotFrom_spec : ∀ (ws ts : List Cell) (acc : Cell),
    ASpec c M (dotFrom acc ws ts) (fun r => r.val M = finalOf (vals M ws) (vals M ts) (acc.val M)) True
  | w :: ws, t :: ts, acc => by
    show ASpec c M (mulAdd .E w t acc >>= fun a => dotFrom a ws ts) _ _
    refine aspec_congr (aspec_bind (aspec_mulAdd (c := c) (M := M) .E w t acc) fun a ha =>
      aspec_congr (dotFrom_spec ws ts a) (Q := fun r => r.val M =
        finalOf (vals M (w :: ws)) (vals M (t :: ts)) (acc.val M)) (fun r hr => by
          rw [hr, ha]; simp only [finalOf, vals, List.map_cons, List.zip_cons_cons, List.foldl_cons]
          rw [add_comm (w.val M * t.val M)]) Iff.rfl) (fun _ h => h) (by simp)
  | [], ts, acc => aspec_pure (by simp [finalOf, vals])
  | _ :: _, [], acc => aspec_pure (by simp [finalOf, vals])

/-- **Q_arith_eq, the table final check**: with `z = 0` and the gate on, the assertion holds iff
`F`'s `require (final == claim)` passes, `final = finalOf weights terms 0` (`tableTerms_final`). -/
theorem tableFinal_check {z gate claim : Cell} (hz : z.val M = 0) (hg : gate.val M = 1)
    (ws ts : List Cell) (p : Ptr) (h : SegsHold c M p (tableFinal z gate claim ws ts p).2) :
    SegsAssert M p (tableFinal z gate claim ws ts p).2 ↔
      (finalOf (vals M ws) (vals M ts) 0 == claim.val M) = true := by
  have := aspec_bind (dotFrom_spec (c := c) (M := M) ws ts z) fun f hf =>
    aspec_congr (aspec_assertEq (c := c) (M := M) f claim gate) (fun _ _ => trivial)
      (B := finalOf (vals M ws) (vals M ts) 0 = claim.val M)
      (by rw [hf, hz, gate_eq_iff hg])
  exact ((this p h).2.trans (by rw [true_and])).trans (FE.beq_iff _ _).symm

end

/-- Non-vacuity: the weights and the final check pass the program check. -/
theorem table_segsOk :
    segsOk ⟨1, 20⟩ (tableW (ec 0) (ec 1) (fun c => ec (2 + c)) (fun j => ec (6 + j)) 3 [1, 3, 2]
      ⟨1, 20⟩).2 = true ∧
      segsOk ⟨1, 20⟩ (tableFinal (ec 0) (kc 0) (ec 1) [ec 2, ec 3] [ec 4, ec 5] ⟨1, 20⟩).2 = true := by
  decide

end Lvm.Loop.Build.QB
