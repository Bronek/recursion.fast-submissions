import LvmQEqKeccakAlg3

/-!
# QA1: Keccak weight algebra, part 4 (`keccakOpen`'s slot weights and fold)

Adapted from rf-lvm-QA1 `LvmKeccakSlotWeights.lean` (WP-2, leanVM Keccak port, over
`LeanVM.Parameters.E`) to `F`'s copy over `Lvm.FE`. See `LvmQEqKeccakAlg` for the overview.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Finset

/-! ## Arrays of rows (adapted from WP-2) -/

/-- Entry `(o, z)` of an array of rows, `0` outside. -/
def rowsFE (rows : Array (Array FE)) (o z : ℕ) : FE := (rows.getD o #[]).getD z 0

/-- Sixty-four rows of sixty-four entries. -/
def SizedE (rows : Array (Array FE)) : Prop := rows.size = 64 ∧ ∀ o < 64, (rows.getD o #[]).size = 64

theorem modify_getDE (rows : Array (Array FE)) (i o : ℕ) (f : Array FE → Array FE) :
    (rows.modify i f).getD o #[] = if i = o ∧ o < rows.size then f (rows.getD o #[])
      else rows.getD o #[] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = o
  · subst h1
    by_cases h2 : i < rows.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem modify_stepE {rows : Array (Array FE)} (hs : SizedE rows) (i z' : ℕ) (x : FE) :
    SizedE (rows.modify i fun row ↦ row.setIfInBounds z' x) ∧
      ∀ o z, rowsFE (rows.modify i fun row ↦ row.setIfInBounds z' x) o z =
        if i = o ∧ z' = z ∧ o < 64 ∧ z < 64 then x else rowsFE rows o z := by
  refine ⟨⟨by simp [hs.1], fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
  · rw [modify_getDE]
    split_ifs
    · rw [Array.size_setIfInBounds]; exact hs.2 o ho
    · exact hs.2 o ho
  · rw [rowsFE, modify_getDE, rowsFE]
    by_cases h1 : i = o ∧ o < rows.size
    · rw [ite_eq_left h1, setIfInBounds_getD']
      have ho : o < 64 := hs.1 ▸ h1.2
      rw [hs.2 o ho]
      by_cases h2 : z' = z ∧ z' < 64
      · rw [ite_eq_left h2, ite_eq_left (show i = o ∧ z' = z ∧ o < 64 ∧ z < 64 from
          ⟨h1.1, h2.1, ho, h2.1 ▸ h2.2⟩)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
          fun h ↦ h2 ⟨h.2.1, h.2.1 ▸ h.2.2.2⟩)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
        fun h ↦ h1 ⟨h.1, hs.1 ▸ h.2.2.1⟩)]

theorem inner_rowsE (rows0 : Array (Array FE)) (hs : SizedE rows0) (b : ℕ) (V : ℕ → FE)
    (hb : b + 25 ≤ 64) : ∀ J, J ≤ 1600 →
      SizedE ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) ∧
      ∀ o z, rowsFE ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) o z =
        if b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J then V (64 * (o - b) + z)
        else rowsFE rows0 o z
  | 0, _ => ⟨hs, fun o z ↦ by simp⟩
  | J + 1, hJ => by
    obtain ⟨hs', hg⟩ := inner_rowsE rows0 hs b V hb J (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs'', hg''⟩ := modify_stepE hs' (b + J / 64) (J % 64) (V J)
    refine ⟨hs'', fun o z ↦ ?_⟩
    rw [hg'', hg]
    by_cases h1 : b + J / 64 = o ∧ J % 64 = z ∧ o < 64 ∧ z < 64
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
      congr 1; omega
    · rw [ite_eq_right h1]
      by_cases h2 : b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The weight `keccakSlotWeights` puts at row `o`, column `z`. -/
def slotWE (segments w : List FE) (first count o z : ℕ) : FE :=
  if 25 * first ≤ o ∧ o < 25 * (first + count) ∧ z < 64 then
    segments.getD (o / 25 - first) 0 * w.getD (64 * (o % 25) + z) 0 else 0

theorem outer_rowsE (segments w : List FE) (first count : ℕ) (hfc : first + count ≤ 2) :
    ∀ S, S ≤ count →
      SizedE ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl (fun rows j ↦
        rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) ∧
      ∀ o z, rowsFE ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl
        (fun rows j ↦ rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) o z = slotWE segments w first S o z
  | 0, _ => by
    refine ⟨⟨by simp, fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
    · simp [Array.getD_eq_getD_getElem?, ho]
    · simp only [List.range_zero, List.foldl_nil, rowsFE, slotWE]
      rw [ite_eq_right (by omega)]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      by_cases h : o < 64
      · by_cases h' : z < 64 <;> simp [h, h']
      · simp [h]
  | S + 1, hS => by
    obtain ⟨hs, hg⟩ := outer_rowsE segments w first count hfc S (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_rowsE _ hs (25 * (first + S))
      (fun j ↦ segments.getD S 0 * w.toArray.getD j 0) (by omega) keccakBits le_rfl
    have hk : keccakBits = 1600 := rfl
    refine ⟨hs', fun o z ↦ ?_⟩
    rw [hg', hg, slotWE, slotWE]
    by_cases h1 : 25 * (first + S) ≤ o ∧ o < 25 * (first + S) + 25 ∧ z < 64 ∧
        64 * (o - 25 * (first + S)) + z < keccakBits
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArray']
      have e1 : o / 25 - first = S := by omega
      have e2 : o % 25 = o - 25 * (first + S) := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : 25 * first ≤ o ∧ o < 25 * (first + S) ∧ z < 64
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem toListRows_getDE (A : Array (Array FE)) {o : ℕ} (ho : o < A.size) (z : ℕ) :
    ((A.toList.map Array.toList).getD o []).getD z 0 = (A.getD o #[]).getD z 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

theorem toListRows_rowE (A : Array (Array FE)) {o : ℕ} (ho : o < A.size) :
    (A.toList.map Array.toList).getD o [] = (A.getD o #[]).toList := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

/-- **`keccakSlotWeights` in closed form.** -/
theorem slotWeights_getD (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o z : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).getD z 0 =
      slotWE (eqKernel (claim.point.drop (logSteps - 4))) claim.weights first count o z := by
  obtain ⟨hs, hg⟩ := outer_rowsE (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  rw [← hg o z, rowsFE]
  unfold keccakSlotWeights
  simp only [keccakSlotBits, slotLog, show (2 : ℕ) ^ 6 = 64 from rfl]
  exact toListRows_getDE _ (by rw [hs.1]; exact ho) z

theorem slotWeights_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) : (keccakSlotWeights logSteps claim first count).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rowsE (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [keccakSlotBits, slotLog, show (2 : ℕ) ^ 6 = 64 from rfl, List.length_map,
    Array.length_toList]
  exact hs.1

theorem slotWeights_row_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rowsE (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [keccakSlotBits, slotLog, show (2 : ℕ) ^ 6 = 64 from rfl]
  rw [toListRows_rowE _ (by rw [hs.1]; exact ho), Array.length_toList]
  exact hs.2 o ho

/-! ## The fold along the slot (adapted from WP-2) -/

/-- `keccakOpen`'s fold of the rows along the slot challenges. -/
def foldAllE (slot : List FE) (rows : List (List FE)) : List (List FE) :=
  slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows

theorem zipWith_getDE (f : FE → FE → FE) (l₁ l₂ : List FE) {z : ℕ} (h₁ : z < l₁.length)
    (h₂ : z < l₂.length) : (List.zipWith f l₁ l₂).getD z 0 = f (l₁.getD z 0) (l₂.getD z 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂]

theorem mapRange_getDE (f : ℕ → List FE) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i [] = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem sum_pairs (g : ℕ → FE) : ∀ N : ℕ,
    ∑ x ∈ range (2 * N), g x = ∑ x ∈ range N, (g (2 * x) + g (2 * x + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_pairs g N, Finset.sum_range_succ]
    ring

/-- `eq(c :: pt, o)` peels the lowest bit. -/
theorem eqAt_cons (c : FE) (pt : List FE) {o : ℕ} (ho : o < 2 ^ (pt.length + 1)) :
    eqAt (c :: pt) o = (if o % 2 = 1 then c else 1 + c) * eqAt pt (o / 2) := by
  rw [eqAt_prod _ (by simpa using ho), eqAt_prod _ (by rw [pow_succ] at ho; omega)]
  unfold eqProd
  rw [List.length_cons, Finset.prod_range_succ']
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [mul_comm]
  congr 1
  · simp [Nat.testBit_zero]
  · refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Nat.testBit_div_two]

/-- **The fold is the multilinear extension along the slot**, column by column. -/
theorem foldAll_eqE : ∀ (pt : List FE) (rows : List (List FE)), rows.length = 2 ^ pt.length →
    (∀ o < rows.length, (rows.getD o []).length = 64) →
    (foldAllE pt rows).length = 1 ∧ ((foldAllE pt rows).headD []).length = 64 ∧
      ∀ z < 64, ((foldAllE pt rows).headD []).getD z 0 =
        ∑ o ∈ range (2 ^ pt.length), eqAt pt o * (rows.getD o []).getD z 0
  | [], rows, hl, hr => by
    rcases rows with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · simp at hl
    · refine ⟨rfl, hr 0 (by simp), fun z _ ↦ ?_⟩
      simp [foldAllE, eqAt, eqKernel]
    · simp at hl
  | c :: pt, rows, hl, hr => by
    have step : foldAllE (c :: pt) rows = foldAllE pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) := rfl
    have hl' : rows.length / 2 = 2 ^ pt.length := by
      rw [hl, List.length_cons, pow_succ]; omega
    have hrow : ∀ i < rows.length / 2, ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])).getD i [] =
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) []) := by
      intro i hi
      exact mapRange_getDE _ hi
    obtain ⟨h1, h2, h3⟩ := foldAll_eqE pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) (by rw [List.length_map, List.length_range, hl'])
      (fun i hi ↦ by
        have hi2 : i < rows.length / 2 := by simpa using hi
        rw [hrow i hi2, List.length_zipWith, hr _ (by omega), hr _ (by omega), min_self])
    rw [step]
    refine ⟨h1, h2, fun z hz ↦ ?_⟩
    rw [h3 z hz, List.length_cons, pow_succ, mul_comm, sum_pairs]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [hrow i (by omega), zipWith_getDE _ _ _ (by rw [hr _ (by omega)]; exact hz)
      (by rw [hr _ (by omega)]; exact hz), eqAt_cons c pt (by rw [pow_succ]; omega),
      eqAt_cons c pt (by rw [pow_succ]; omega)]
    have e1 : 2 * i % 2 = 0 := by omega
    have e2 : (2 * i + 1) % 2 = 1 := by omega
    have e3 : 2 * i / 2 = i := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    simp only [e1, e2, e3, e4, if_true, zero_ne_one, if_false]
    ring

/-! ## The two openings of `verifyKeccak` -/

/-- `keccakOpen`'s inline fold is `foldAllE`. -/
theorem keccakOpen_fold (slot : List FE) (rows : List (List FE)) :
    slot.foldl (fun rows challenge =>
      (List.range (rows.length / 2)).map fun i =>
        List.zipWith (fun lo hi => lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) rows = foldAllE slot rows := rfl

/-- The folded slot weights at column `z`. -/
theorem open_fold_getD (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (hfc : first + count ≤ 2)
    {slot : List FE} (hs : slot.length = 6) {z : ℕ} (hz : z < 64) :
    ((foldAllE slot (keccakSlotWeights logSteps claim first count)).headD []).getD z 0 =
      ∑ o ∈ range 64, eqAt slot o *
        slotWE (eqKernel (claim.point.drop (logSteps - 4))) claim.weights first count o z := by
  obtain ⟨-, -, h3⟩ := foldAll_eqE slot (keccakSlotWeights logSteps claim first count)
    (by rw [slotWeights_length _ _ _ _ hfc, hs]; rfl)
    (fun o ho => slotWeights_row_length _ _ _ _ hfc (by rwa [slotWeights_length _ _ _ _ hfc] at ho))
  rw [h3 z hz, hs, show (2 : ℕ) ^ 6 = 64 from rfl]
  refine Finset.sum_congr rfl fun o ho => ?_
  rw [slotWeights_getD _ _ _ _ hfc (Finset.mem_range.mp ho)]

theorem fold_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (hfc : first + count ≤ 2)
    {slot : List FE} (hs : slot.length = 6) :
    ((foldAllE slot (keccakSlotWeights logSteps claim first count)).headD []).length = 64 :=
  (foldAll_eqE slot (keccakSlotWeights logSteps claim first count)
    (by rw [slotWeights_length _ _ _ _ hfc, hs]; rfl)
    (fun o ho => slotWeights_row_length _ _ _ _ hfc (by rwa [slotWeights_length _ _ _ _ hfc] at ho))).2.1

/-- **The committed outputs' opening** (`first = 1`, `count = 1`): column `0` of the fold. -/
theorem open_committed (logSteps : ℕ) (claim : KeccakClaim) {slot : List FE} (hs : slot.length = 6) :
    ((foldAllE slot (keccakSlotWeights logSteps claim 1 1)).headD []).getD 0 0 =
      sumE ((List.range 25).map fun l => eqAt slot (25 + l) *
        (eqKernel (claim.point.drop (logSteps - 4))).getD 0 0 * claim.weights.getD (64 * l) 0) := by
  rw [open_fold_getD _ _ _ _ (by decide) hs (by decide), sumE_range,
    show (64 : ℕ) = 25 + (25 + 14) from rfl, Finset.sum_range_add, Finset.sum_range_add]
  have h0 : ∑ o ∈ range 25, eqAt slot o *
      slotWE (eqKernel (claim.point.drop (logSteps - 4))) claim.weights 1 1 o 0 = 0 :=
    Finset.sum_eq_zero fun o ho => by
      rw [slotWE, if_neg (by have := Finset.mem_range.mp ho; omega), mul_zero]
  have h2 : ∑ k ∈ range 14, eqAt slot (25 + (25 + k)) *
      slotWE (eqKernel (claim.point.drop (logSteps - 4))) claim.weights 1 1 (25 + (25 + k)) 0 = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [slotWE, if_neg (by omega), mul_zero]
  rw [h0, h2, zero_add, add_zero]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rw [slotWE, if_pos (by omega), show (25 + l) / 25 - 1 = 0 by omega, show (25 + l) % 25 = l by omega,
    Nat.add_zero, mul_assoc]

theorem dot_eq_sum {l r : List FE} (hl : l.length = 64) (hr : r.length = 64) :
    dot l r = ∑ z ∈ range 64, l.getD z 0 * r.getD z 0 := by
  have hz : List.zipWith (· * ·) l r = (List.range 64).map fun z => l.getD z 0 * r.getD z 0 := by
    apply List.ext_getElem
    · simp [hl, hr]
    · intro i h1 h2
      simp only [List.length_zipWith, hl, hr, min_self] at h1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ h1),
        List.getElem?_eq_getElem (hr ▸ h1)]
  unfold dot
  rw [hz, ← sumE_range]
  rfl

/-- **The inputs' opening** (`first = 0`, `count = 2`): the fold against the 64 slices. -/
theorem open_input (logSteps : ℕ) (claim : KeccakClaim) {slot slices : List FE} (hs : slot.length = 6)
    (hsl : slices.length = 64) :
    dot ((foldAllE slot (keccakSlotWeights logSteps claim 0 2)).headD []) slices =
      sumE ((List.range 2).map fun s => sumE ((List.range 25).map fun l =>
        eqAt slot (25 * s + l) * (eqKernel (claim.point.drop (logSteps - 4))).getD s 0 *
          sumE ((List.range 64).map fun z => slices.getD z 0 * claim.weights.getD (64 * l + z) 0))) := by
  rw [dot_eq_sum (fold_length _ _ _ _ (by decide) hs) hsl]
  rw [Finset.sum_congr rfl (fun z hz => by
    rw [open_fold_getD _ _ _ _ (by decide) hs (Finset.mem_range.mp hz), Finset.sum_mul]),
    Finset.sum_comm, show (64 : ℕ) = 2 * 25 + 14 from rfl, Finset.sum_range_add]
  have h2 : ∑ k ∈ range 14, ∑ z ∈ range 64, eqAt slot (2 * 25 + k) *
      slotWE (eqKernel (claim.point.drop (logSteps - 4))) claim.weights 0 2 (2 * 25 + k) z *
        slices.getD z 0 = 0 :=
    Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun z _ => by
      rw [slotWE, if_neg (by omega), mul_zero, zero_mul]
  rw [h2, add_zero, sum_range_mul', sumE_range]
  refine Finset.sum_congr rfl fun s hs' => ?_
  rw [sumE_range]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hs2 := Finset.mem_range.mp hs'
  have hl' := Finset.mem_range.mp hl
  rw [sumE_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz' := Finset.mem_range.mp hz
  rw [slotWE, if_pos (by omega), show (25 * s + l) / 25 - 0 = s by omega,
    show (25 * s + l) % 25 = l by omega]
  ring

/-- The inputs' opening on transposed product weights: lane forms against the slices. -/
theorem open_input_lt (logSteps : ℕ) (claim : KeccakClaim) (A : ℕ → FE) (B : List FE)
    (hw : claim.weights = keccakLinearTranspose (prodW A B)) {slot slices : List FE}
    (hs : slot.length = 6) (hsl : slices.length = 64) :
    dot ((foldAllE slot (keccakSlotWeights logSteps claim 0 2)).headD []) slices =
      sumE ((List.range 2).map fun s => sumE ((List.range 25).map fun l =>
        eqAt slot (25 * s + l) * (eqKernel (claim.point.drop (logSteps - 4))).getD s 0 *
          laneForm B (rotSum (fun z => slices.getD z 0) A) l)) := by
  rw [open_input logSteps claim hs hsl, hw]
  refine congrArg sumE (List.map_congr_left fun s _ => congrArg sumE (List.map_congr_left fun l hl => ?_))
  rw [lane_dot A (fun z => slices.getD z 0) B (List.mem_range.mp hl)]

/-- The committed outputs' opening on the first claim's weights (`lanes ⊗ x^z`, slice `0`). -/
theorem open_committed_first (logSteps : ℕ) (claim : KeccakClaim) (lanes : List FE)
    (hw : claim.weights = firstW lanes) {slot : List FE} (hs : slot.length = 6) :
    ((foldAllE slot (keccakSlotWeights logSteps claim 1 1)).headD []).getD 0 0 =
      sumE ((List.range 25).map fun l => eqAt slot (25 + l) *
        (eqKernel (claim.point.drop (logSteps - 4))).getD 0 0 * lanes.getD l 0) := by
  rw [open_committed logSteps claim hs, hw]
  refine congrArg sumE (List.map_congr_left fun l hl => ?_)
  have h := firstW_getD lanes (List.mem_range.mp hl) (z := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h, pow_zero, mul_one]

end Lvm.Q1
