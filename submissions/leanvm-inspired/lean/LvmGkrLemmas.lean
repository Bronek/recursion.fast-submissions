-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Complete/Gkr.lean` (formal rev
-- 40f877dc), lines 55-353 (cube points and extensions, products, layers, one GKR step's algebra)
-- and `prodE_eq` (390-392), as `LvmGkrLemmas` for lvm (WP-2). The honest GKR prover (`GkrInv`,
-- `hStep`, `hLayers`, `hGkr`, `follows_*`) is completeness and is not ported.
import LvmEqLemmas
import LvmPolyLE

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Prover (Script)

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd Finset

section

/-! ## Cube points and extensions -/

/-- The equality weight of two cube points is the indicator of their equality. -/
theorem eqEval_boolPoint_boolPoint : ∀ (m i j : ℕ), i < 2 ^ m → j < 2 ^ m →
    eqEval (boolPoint m i) (boolPoint m j) = if i = j then 1 else 0
  | 0, i, j, hi, hj => by
    obtain rfl : i = 0 := by simpa using hi
    obtain rfl : j = 0 := by simpa using hj
    simp
  | m + 1, i, j, hi, hj => by
    rw [pow_succ] at hi hj
    rw [boolPoint_succ, boolPoint_succ, eqEval_cons,
      eqEval_boolPoint_boolPoint m (i / 2) (j / 2) (by omega) (by omega)]
    by_cases hij : i = j
    · subst hij
      rcases Nat.mod_two_eq_zero_or_one i with h | h <;>
        simp [h, Nat.testBit_zero, one_add_one_E]
    · by_cases hh : i / 2 = j / 2
      · have hb : i % 2 ≠ j % 2 := fun hb ↦ hij (by omega)
        simp only [hh, ↓reduceIte, mul_one, hij, Nat.testBit_zero]
        rcases Nat.mod_two_eq_zero_or_one i with h1 | h1 <;>
          rcases Nat.mod_two_eq_zero_or_one j with h2 | h2 <;>
          simp_all [one_add_one_E]
      · simp [hh, hij]

/-- The extension of a table at a cube point is the table's entry. -/
theorem multilinearEval_boolPoint {m : ℕ} {t : List E} (ht : t.length = 2 ^ m) {l : ℕ}
    (hl : l < 2 ^ m) : multilinearEval t (boolPoint m l) = t.getD l 0 := by
  rw [multilinearEval_eq_sum m t _ ht (length_boolPoint m l)]
  rw [sum_congr rfl fun i hi ↦ by
    rw [eqEval_boolPoint_boolPoint m i l (mem_range.mp hi) hl]]
  simp [mem_range.mpr hl]

/-- **Partial evaluation by blocks.** Fixing the first `a` coordinates at `y`: the extension at
`y ++ x` is the extensions at the cube points `j ++ x`, weighted by `eq(j, y)`. -/
theorem multilinearEval_append {a d : ℕ} {t : List E} (ht : t.length = 2 ^ (a + d)) {y x : List E}
    (hy : y.length = a) (hx : x.length = d) :
    multilinearEval t (y ++ x) =
      ∑ j ∈ range (2 ^ a), multilinearEval t (boolPoint a j ++ x) * eqEval (boolPoint a j) y := by
  have hfold : ∀ r : List E, r.length = a →
      multilinearEval t (r ++ x) = multilinearEval (foldAll t r) x := fun r _ ↦ by
    rw [multilinearEval_eq_foldAll, multilinearEval_eq_foldAll, foldAll_append]
  have hlen : ∀ r : List E, r.length = a → (foldAll t r).length = 2 ^ d := fun r hr ↦
    length_foldAll r t d (by rw [hr, ht])
  have hentry : ∀ r : List E, r.length = a → ∀ i ∈ range (2 ^ d),
      (foldAll t r).getD i 0 =
        ∑ j ∈ range (2 ^ a), eqEval (boolPoint a j) r * t.getD (j + 2 ^ a * i) 0 :=
    fun r hr i hi ↦ by
      rw [getD_foldAll r t d i (by rw [hr, ht]) (mem_range.mp hi), hr]
  rw [hfold y hy, multilinearEval_eq_sum d _ x (hlen y hy) hx,
    sum_congr rfl fun i hi ↦ by rw [hentry y hy i hi]]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [hfold _ (length_boolPoint a j),
    multilinearEval_eq_sum d _ x (hlen _ (length_boolPoint a j)) hx, sum_mul]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [hentry _ (length_boolPoint a j) i hi]
  rw [sum_congr rfl fun j' hj' ↦ by
    rw [eqEval_boolPoint_boolPoint a j' j (mem_range.mp hj') (mem_range.mp hj)]]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', hj, ↓reduceIte]
  rw [eqEval_comm]
  ring

/-! ## Polynomial dependence on one coordinate -/

/-- The equality weight is affine in any one coordinate of its second point. -/
theorem polyLE_eqEval : ∀ (u a v : List E), PolyLE 1 fun X ↦ eqEval a (u ++ X :: v)
  | [], [], v => (PolyLE.const 1 1).congr fun X ↦ by simp
  | [], a₀ :: a, v =>
    ((PolyLE.affine (1 + a₀) 1).mul (PolyLE.const 0 (eqEval a v))).congr fun X ↦ by
      rw [List.nil_append, eqEval_cons]; ring
  | _ :: _, [], v => (PolyLE.const 1 1).congr fun X ↦ by simp
  | u₀ :: u, a₀ :: a, v =>
    ((polyLE_eqEval u a v).const_mul (1 + a₀ + u₀)).congr fun X ↦ by
      rw [List.cons_append, eqEval_cons]

/-- A table's extension is affine in any one coordinate. -/
theorem polyLE_multilinearEval {t : List E} (u v : List E)
    (ht : t.length = 2 ^ (u.length + 1 + v.length)) :
    PolyLE 1 fun X ↦ multilinearEval t (u ++ X :: v) := by
  refine (PolyLE.sum (range (2 ^ (u.length + 1 + v.length))) fun i _ ↦
    (polyLE_eqEval u (boolPoint (u.length + 1 + v.length) i) v).const_mul
      (t.getD i 0)).congr fun X ↦ ?_
  rw [multilinearEval_eq_sum _ t _ ht (by simp; omega)]

/-- A product of polynomial functions, along a list. -/
theorem PolyLE.listProd {ι : Type} {d : ℕ} (F : ι → E → E) :
    ∀ l : List ι, (∀ i ∈ l, PolyLE d (F i)) → PolyLE (l.length * d) fun x ↦ (l.map (F · x)).prod
  | [], _ => (PolyLE.const _ 1).congr fun x ↦ by simp
  | i :: l, h =>
    ((PolyLE.mul (h i (by simp)) (PolyLE.listProd F l fun j hj ↦ h j (by simp [hj]))).mono
      (by rw [List.length_cons]; nlinarith)).congr fun x ↦ by simp

/-! ## The trees -/

/-- Adjacent pairs multiplied: one level up a product tree. -/
def mulPairs : List E → List E
  | a :: b :: t => a * b :: mulPairs t
  | _ => []

/-- The layer `k` levels above the leaves `L`. -/
def up (k : ℕ) (L : List E) : List E := mulPairs^[k] L

theorem length_mulPairs : ∀ t : List E, (mulPairs t).length = t.length / 2
  | [] => rfl
  | [_] => by simp [mulPairs]
  | a :: b :: t => by
    simp only [mulPairs, List.length_cons, length_mulPairs t]
    omega

theorem getD_mulPairs : ∀ (t : List E) (j : ℕ), 2 * j + 1 < t.length →
    (mulPairs t).getD j 0 = t.getD (2 * j) 0 * t.getD (2 * j + 1) 0
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: t, 0, _ => by simp [mulPairs]
  | a :: b :: t, j + 1, h => by
    simp only [mulPairs, List.getD_cons_succ, List.length_cons] at h ⊢
    rw [getD_mulPairs t j (by omega), show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp

/-- Multiplying adjacent pairs keeps the product of a list of even length. -/
theorem prod_mulPairs : ∀ t : List E, Even t.length → (mulPairs t).prod = t.prod
  | [], _ => rfl
  | [_], h => by simp at h
  | a :: b :: t, h => by
    have ht : Even t.length := by
      simpa [List.length_cons, Nat.even_add_one] using h
    simp only [mulPairs, List.prod_cons, prod_mulPairs t ht, mul_assoc]

theorem up_succ (k : ℕ) (L : List E) : up (k + 1) L = mulPairs (up k L) :=
  Function.iterate_succ_apply' _ _ _

theorem up_add (a b : ℕ) (L : List E) : up (a + b) L = up a (up b L) :=
  Function.iterate_add_apply _ _ _ _

theorem length_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → (up k L).length = 2 ^ m
  | 0, m, L, h => by simpa [up] using h
  | k + 1, m, L, h => by
    rw [up_succ, length_mulPairs, length_up k (m + 1) L (by rw [h]; ring_nf), pow_succ,
      Nat.mul_div_cancel _ (by norm_num)]

/-- **A node of the tree** is the product of the leaves below it: entry `i` of the layer `k`
levels up is the product of the leaves `j + 2^k·i`. -/
theorem getD_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → ∀ i, i < 2 ^ m →
    (up k L).getD i 0 = ((List.range (2 ^ k)).map fun j ↦ L.getD (j + 2 ^ k * i) 0).prod
  | 0, m, L, _, i, _ => by simp [up]
  | k + 1, m, L, h, i, hi => by
    have hl := length_up k (m + 1) L (by rw [h]; ring_nf)
    rw [up_succ, getD_mulPairs _ i (by rw [hl, pow_succ]; omega),
      getD_up k (m + 1) L (by rw [h]; ring_nf) (2 * i) (by rw [pow_succ]; omega),
      getD_up k (m + 1) L (by rw [h]; ring_nf) (2 * i + 1) (by rw [pow_succ]; omega),
      pow_succ, mul_two, List.range_add, List.map_append, List.prod_append, List.map_map]
    congr 2
    · refine List.map_congr_left fun j _ ↦ ?_
      rw [show j + 2 ^ k * (2 * i) = j + (2 ^ k + 2 ^ k) * i by ring]
    · refine List.map_congr_left fun j _ ↦ ?_
      rw [Function.comp_apply, show j + 2 ^ k * (2 * i + 1) = 2 ^ k + j + (2 ^ k + 2 ^ k) * i by
        ring]

/-- The product of the layers is the product of the leaves. -/
theorem prod_up : ∀ (k m : ℕ) (L : List E), L.length = 2 ^ (m + k) → (up k L).prod = L.prod
  | 0, _, _, _ => rfl
  | k + 1, m, L, h => by
    have hl := length_up k (m + 1) L (by rw [h]; ring_nf)
    rw [up_succ, prod_mulPairs _ (by rw [hl, pow_succ]; exact ⟨2 ^ m, by ring⟩),
      prod_up k (m + 1) L (by rw [h]; ring_nf)]

/-- The root of a tree is the leaves' product. -/
theorem multilinearEval_up_root {D : ℕ} {L : List E} (h : L.length = 2 ^ D) :
    multilinearEval (up D L) [] = L.prod := by
  have hl := length_up D 0 L (by rw [h, zero_add])
  obtain ⟨a, ha⟩ : ∃ a, up D L = [a] := by
    match hu : up D L, hl with
    | [a], _ => exact ⟨a, rfl⟩
  rw [← prod_up D 0 L (by rw [h, zero_add]), ha]
  simp [multilinearEval]

/-! ## One step -/

/-- The children a step of `step` levels sends of the layer `C`: `C̃(j, x)` for every `j`. -/
def child (C : List E) (step : ℕ) (x : List E) : List E :=
  (List.range (2 ^ step)).map fun j ↦ multilinearEval C (boolPoint step j ++ x)

/-- The children's products, batched in the Horner order of `polyEval`: the step's polynomial
`F(x)`. -/
def stepF (C₀ C₁ C₂ : List E) (step : ℕ) (c : E) (x : List E) : E :=
  polyEval [(child C₀ step x).prod, (child C₁ step x).prod, (child C₂ step x).prod] c

/-- The running claim of the step's sumcheck after the challenges `pre`:
`Σ_b eq(p_{≥|pre|}, b) · F(pre, b)`. -/
def stepClaim (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (pre : List E) : E :=
  ∑ b ∈ range (2 ^ (p.length - pre.length)),
    eqEval (p.drop pre.length) (boolPoint (p.length - pre.length) b) *
      stepF C₀ C₁ C₂ step c (pre ++ boolPoint (p.length - pre.length) b)

/-- The children's extension at `y` is the layer's extension at `y ++ x`. -/
theorem multilinearEval_child {C : List E} {step d : ℕ} (hC : C.length = 2 ^ (step + d))
    {x y : List E} (hx : x.length = d) (hy : y.length = step) :
    multilinearEval (child C step x) y = multilinearEval C (y ++ x) := by
  rw [multilinearEval_append hC hy hx, multilinearEval_eq_sum step _ y (by simp [child]) hy]
  refine sum_congr rfl fun j hj ↦ ?_
  simp [child, List.getD_eq_getElem?_getD, mem_range.mp hj]

/-- A child at a cube point is a node of the layer. -/
theorem child_boolPoint {C : List E} {step d : ℕ} (hC : C.length = 2 ^ (step + d)) {b : ℕ}
    (hb : b < 2 ^ d) :
    child C step (boolPoint d b) =
      (List.range (2 ^ step)).map fun j ↦ C.getD (j + 2 ^ step * b) 0 := by
  refine List.map_congr_left fun j hj ↦ ?_
  have hj' := List.mem_range.mp hj
  rw [← boolPoint_add step d j b hj', multilinearEval_boolPoint hC]
  rw [pow_add]
  exact add_mul_lt hj' hb

/-- **The start of the step.** The batched values of the layers at `p` are the sumcheck's
claim. -/
theorem stepClaim_nil {C₀ C₁ C₂ : List E} {step : ℕ} {p : List E}
    (h₀ : C₀.length = 2 ^ (step + p.length)) (h₁ : C₁.length = 2 ^ (step + p.length))
    (h₂ : C₂.length = 2 ^ (step + p.length)) (c : E) :
    polyEval [multilinearEval (up step C₀) p, multilinearEval (up step C₁) p,
      multilinearEval (up step C₂) p] c = stepClaim C₀ C₁ C₂ step p c [] := by
  have hT : ∀ C : List E, C.length = 2 ^ (step + p.length) →
      multilinearEval (up step C) p =
        ∑ b ∈ range (2 ^ p.length), (child C step (boolPoint p.length b)).prod *
          eqEval (boolPoint p.length b) p := fun C hC ↦ by
    have hl := length_up step p.length C (by rw [hC, add_comm])
    rw [multilinearEval_eq_sum p.length _ p hl rfl]
    refine sum_congr rfl fun b hb ↦ ?_
    rw [getD_up step p.length C (by rw [hC, add_comm]) b (mem_range.mp hb),
      child_boolPoint hC (mem_range.mp hb)]
  rw [hT C₀ h₀, hT C₁ h₁, hT C₂ h₂, polyEval_three, stepClaim]
  simp only [List.length_nil, Nat.sub_zero, List.drop_zero, List.nil_append, stepF,
    polyEval_three, sum_mul, ← sum_add_distrib]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [eqEval_comm]
  ring

/-- **A round of the step.** The next claims at `0` and `1` split the claim as the equality-mode
round checks it, with the point's coordinate `p_k`. -/
theorem stepClaim_split (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (pre : List E)
    (hk : pre.length < p.length) :
    RoundSplit (some p[pre.length]) (stepClaim C₀ C₁ C₂ step p c pre)
      (stepClaim C₀ C₁ C₂ step p c (pre ++ [0])) (stepClaim C₀ C₁ C₂ step p c (pre ++ [1])) := by
  obtain ⟨m, hm⟩ : ∃ m, p.length - pre.length = m + 1 := ⟨p.length - pre.length - 1, by omega⟩
  have hm' : p.length - (pre.length + 1) = m := by omega
  simp only [RoundSplit, stepClaim, List.length_append, List.length_singleton, hm, hm']
  rw [pow_succ', sum_range_two_mul, List.drop_eq_getElem_cons hk, mul_sum, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [boolPoint_two_mul, boolPoint_two_mul_add_one, eqEval_cons, eqEval_cons,
    show pre ++ 0 :: boolPoint m j = pre ++ [0] ++ boolPoint m j by simp,
    show pre ++ 1 :: boolPoint m j = pre ++ [1] ++ boolPoint m j by simp]
  linear_combination (-(eqEval (p.drop (pre.length + 1)) (boolPoint m j) *
    stepF C₀ C₁ C₂ step c (pre ++ [1] ++ boolPoint m j))) * two_eq_zero_E

/-- **The degree of a round.** The next claim is a polynomial of degree `2^step` in the next
challenge. -/
theorem stepClaim_polyLE {C₀ C₁ C₂ : List E} {step : ℕ} {p : List E}
    (h₀ : C₀.length = 2 ^ (step + p.length)) (h₁ : C₁.length = 2 ^ (step + p.length))
    (h₂ : C₂.length = 2 ^ (step + p.length)) (c : E) (pre : List E)
    (hk : pre.length < p.length) :
    PolyLE (2 ^ step) fun X ↦ stepClaim C₀ C₁ C₂ step p c (pre ++ [X]) := by
  have hchild : ∀ C : List E, C.length = 2 ^ (step + p.length) → ∀ b : ℕ,
      PolyLE (2 ^ step) fun X ↦
        (child C step (pre ++ [X] ++ boolPoint (p.length - (pre.length + 1)) b)).prod := by
    intro C hC b
    have := PolyLE.listProd (d := 1) (fun j X ↦ multilinearEval C
      ((boolPoint step j ++ pre) ++ X :: boolPoint (p.length - (pre.length + 1)) b))
      (List.range (2 ^ step)) fun j _ ↦ polyLE_multilinearEval _ _ (by
        rw [hC]; simp only [List.length_append, length_boolPoint]; congr 1; omega)
    simp only [List.length_range, mul_one] at this
    refine this.congr fun X ↦ ?_
    simp [child]
  have hF : ∀ b, PolyLE (2 ^ step) fun X ↦
      stepF C₀ C₁ C₂ step c (pre ++ [X] ++ boolPoint (p.length - (pre.length + 1)) b) := by
    intro b
    refine (((hchild C₀ h₀ b).add ((hchild C₁ h₁ b).mul (PolyLE.const 0 c))).add
      ((hchild C₂ h₂ b).mul (PolyLE.const 0 (c ^ 2)))).congr fun X ↦ ?_
    simp only [stepF, polyEval_three]
  refine (PolyLE.sum (range (2 ^ (p.length - (pre.length + 1)))) fun b _ ↦
    (hF b).const_mul (eqEval (p.drop (pre.length + 1))
      (boolPoint (p.length - (pre.length + 1)) b))).congr fun X ↦ ?_
  simp only [stepClaim, List.length_append, List.length_singleton]

/-- **The end of the step.** With every coordinate bound, the claim is `F` at the challenges. -/
theorem stepClaim_self (C₀ C₁ C₂ : List E) (step : ℕ) (p : List E) (c : E) (x : List E)
    (hx : x.length = p.length) : stepClaim C₀ C₁ C₂ step p c x = stepF C₀ C₁ C₂ step c x := by
  simp [stepClaim, hx]


/-- `prodE` is the product. -/
theorem prodE_eq (l : List E) : prodE l = l.prod := by
  rw [prodE, foldl_mul_eq, one_mul]

end

end LeanVM.Protocol.EndToEnd.Complete
