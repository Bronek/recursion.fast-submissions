-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToArkLib/Whir/Ood.lean` and the out-of-domain part of
-- `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Escape.lean` (formal rev 0b850750) as `LvmWhirOod` for lvm2 (WP JB-L).
-- Changed: one module in namespace `LeanVM.Protocol.Whir.Sound`; the helpers of the count (`evens`, `odds`,
-- `evalMle_evalMleStep`, `evalMle_succ`, `eq_of_evens_eq_of_odds_eq`, `card_affine_eq_zero_le`,
-- `card_vector_eq_pow`) live in the sub-namespace `Ood` (CompPoly's `CMlPolynomialEval.evalMle_succ` is opened);
-- VCVio's `instFintypeVector` is replaced by the local `Ood.instFintypeVector` through `Ood.vectorEquivFun`
-- (`Vector F κ ≃ (Fin κ → F)`). Statements and proofs are otherwise leanVM's.
/-
  LeanVM.Protocol.Whir.Sound.Ood

  Out-of-domain separation: the number of points at which two distinct multilinear tables have
  the same extension, and at which some pair of a finite list collides; the out-of-domain value of
  a member of the next oracle's list, and the count of points that leave two members with equal
  values.
-/

import LvmWhirLanes
import LvmCpMultilinear

/-!
# Out-of-domain separation

Annex B of the leanVM specification (leanVM `127510d1`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), `lem:ood`, in count form, for CompPoly's
hypercube tables `CMlPolynomialEval F κ` and their multilinear extension `evalMle`, evaluated at
points `z : Vector F κ`.

* `card_evalMle_eq_le`: the Schwartz-Zippel count for multilinear extensions. Two distinct
  tables on `κ` variables have the same extension at at most `κ |F|^(κ-1)` points. The proof is
  an induction on `κ` through CompPoly's recursive evaluation, which interpolates the low
  coordinate first (`Ood.evalMle_evalMleStep`): at a point whose tail separates neither half the
  extension is affine in the head and vanishes once, elsewhere it can vanish everywhere.
* `card_ood_collision_le`: for a finite set `L` of tables, at most `C(|L|, 2) κ |F|^(κ-1)` points
  `z` have two distinct members with equal extensions at `z`, a union over the `C(|L|, 2)`
  unordered pairs.
* `card_ood_collision_image_le`: the same for a list decoded injectively into tables, the form the
  round-by-round analysis consumes (distinct interleaved codewords decode to distinct tables).
* `OodSep P Q z`: the members of the list of `Q` have pairwise distinct out-of-domain values
  `oodVal z` (`claimSum (eqEval z)` of their decoded messages). `card_oodSep_bad_le`: at most
  `C(listMax, 2)·κ·|E|^(κ−1)` points `z` break it (`card_ood_collision_image_le`, with the
  injectivity of decoding `decode_injOn`, `tableOf_injective`, `joinMsg_injective`, and
  `sum_eqEval_vec`: the out-of-domain claim reads the table's extension).

Points are counted in `Vector F κ` with the finite-type instance `Ood.instFintypeVector`
(through `Vector F κ ≃ (Fin κ → F)`); `Ood.card_vector_eq_pow` gives its size `|F|^κ`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset CompPoly
  CMlPolynomialEval

section

namespace Ood

/-- Vectors of length `κ` are functions on `Fin κ`. -/
def vectorEquivFun (F : Type*) (κ : ℕ) : Vector F κ ≃ (Fin κ → F) where
  toFun v j := v[j]
  invFun f := Vector.ofFn f
  left_inv v := by ext i hi; simp
  right_inv f := by funext j; simp

/-- The points of `F^κ` as vectors form a finite type (stands in for VCVio's
`instFintypeVector`). -/
instance instFintypeVector {F : Type*} [Fintype F] (κ : ℕ) : Fintype (Vector F κ) :=
  Fintype.ofEquiv _ (vectorEquivFun F κ).symm

variable {F : Type*} [CommRing F]

/-- The even-indexed half of a table on `κ + 1` variables: its restriction to coordinate `0`
equal to `0`. -/
def evens {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) : CMlPolynomialEval F κ :=
  Vector.ofFn fun j : Fin (2 ^ κ) ↦ g.get ⟨2 * j.val, by have := j.isLt; rw [pow_succ]; omega⟩

/-- The odd-indexed half of a table on `κ + 1` variables: its restriction to coordinate `0`
equal to `1`. -/
def odds {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) : CMlPolynomialEval F κ :=
  Vector.ofFn fun j : Fin (2 ^ κ) ↦ g.get ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ]; omega⟩

/-- One interpolation step is the affine combination of the two halves' extensions. -/
theorem evalMle_evalMleStep {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) (a : F)
    (w : Vector F κ) :
    evalMle (evalMleStep g a) w = (1 - a) * evalMle (evens g) w + a * evalMle (odds g) w := by
  simp only [evalMle_eq_sum, evalMleStep, evens, odds, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  ring

/-- The extension at a point is the affine combination, at its head, of the halves' extensions at
its tail. -/
theorem evalMle_succ {κ : ℕ} (g : CMlPolynomialEval F (κ + 1)) (z : Vector F (κ + 1)) :
    evalMle g z = (1 - z.head) * evalMle (evens g) z.tail + z.head * evalMle (odds g) z.tail := by
  rw [← evalMle_evalMleStep]
  rfl

omit [CommRing F] in
/-- Two tables with the same halves are equal. -/
theorem eq_of_evens_eq_of_odds_eq {κ : ℕ} {g g' : CMlPolynomialEval F (κ + 1)}
    (he : evens g = evens g') (ho : odds g = odds g') : g = g' := by
  ext i hi
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' i
  · have hj : j < 2 ^ κ := by rw [pow_succ] at hi; omega
    have := congrArg (·[j]) he
    simpa [evens, Vector.get_eq_getElem] using this
  · have hj : j < 2 ^ κ := by rw [pow_succ] at hi; omega
    have := congrArg (·[j]) ho
    simpa [odds, Vector.get_eq_getElem] using this

omit [CommRing F] in
/-- There are `|F|^κ` points. -/
theorem card_vector_eq_pow [Fintype F] (κ : ℕ) :
    Fintype.card (Vector F κ) = Fintype.card F ^ κ := by
  rw [Fintype.card_congr (vectorEquivFun F κ), Fintype.card_fun, Fintype.card_fin]

/-- An affine function `A + a (B - A)` of `a` that is not identically zero vanishes at most once. -/
theorem card_affine_eq_zero_le [IsDomain F] [Fintype F] [DecidableEq F] (A B : F)
    (h : ¬ (A = 0 ∧ B = 0)) :
    (univ.filter fun a : F ↦ (1 - a) * A + a * B = 0).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a₁ h₁ a₂ h₂ ↦ ?_
  rw [Finset.mem_filter] at h₁ h₂
  by_contra hne
  have hBA : B = A := by
    have : (a₁ - a₂) * (B - A) = 0 := by linear_combination h₁.2 - h₂.2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · exact sub_eq_zero.mp h
  apply h
  have hA : A = 0 := by rw [hBA] at h₁; linear_combination h₁.2
  exact ⟨hA, hBA.trans hA⟩

end Ood

open Ood

section Count

variable {F : Type*} [CommRing F] [IsDomain F] [Fintype F] [DecidableEq F]

/-- **Schwartz-Zippel for multilinear extensions.** Two distinct tables on `κ` variables have the
same multilinear extension at at most `κ |F|^(κ-1)` points. -/
theorem card_evalMle_eq_le : ∀ {κ : ℕ} {g g' : CMlPolynomialEval F κ}, g ≠ g' →
    (univ.filter fun z : Vector F κ ↦ evalMle g z = evalMle g' z).card ≤
      κ * Fintype.card F ^ (κ - 1)
  | 0, g, g', hne => by
    refine (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun z _ hz ↦ hne ?_)).le
    ext i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simpa [evalMle_zero, Vector.get_eq_getElem] using hz
  | κ + 1, g, g', hne => by
    set q := Fintype.card F
    -- The differences of the halves' extensions.
    let A : Vector F κ → F := fun w ↦ evalMle (evens g) w - evalMle (evens g') w
    let B : Vector F κ → F := fun w ↦ evalMle (odds g) w - evalMle (odds g') w
    -- The doubly degenerate tails are few, by induction on a separated half.
    have hdeg : (univ.filter fun w : Vector F κ ↦ A w = 0 ∧ B w = 0).card ≤
        κ * q ^ (κ - 1) := by
      by_cases he : evens g = evens g'
      · have ho : odds g ≠ odds g' := fun ho ↦ hne (eq_of_evens_eq_of_odds_eq he ho)
        refine (Finset.card_le_card fun w hw ↦ ?_).trans (card_evalMle_eq_le ho)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, B] at hw ⊢
        exact sub_eq_zero.mp hw.2
      · refine (Finset.card_le_card fun w hw ↦ ?_).trans (card_evalMle_eq_le he)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A] at hw ⊢
        exact sub_eq_zero.mp hw.1
    -- Split a point into its head and tail.
    let P : F × Vector F κ → Prop := fun p ↦ (1 - p.1) * A p.2 + p.1 * B p.2 = 0
    have hsplit : (univ.filter fun z : Vector F (κ + 1) ↦ evalMle g z = evalMle g' z).card ≤
        (univ.filter P).card := by
      refine Finset.card_le_card_of_injOn (fun z ↦ (z.head, z.tail)) (fun z hz ↦ ?_)
        (fun z₁ _ z₂ _ h ↦ ?_)
      · simp only [coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
        rw [Ood.evalMle_succ, Ood.evalMle_succ] at hz
        simp only [P, A, B]
        linear_combination hz
      · simp only [Prod.mk.injEq] at h
        ext i hi
        cases i with
        | zero => simpa [Vector.head] using h.1
        | succ i =>
          have := congrArg (·[i]) h.2
          simpa [Vector.tail, Nat.add_comm] using this
    have hfiber : (univ.filter P).card =
        ∑ w : Vector F κ, (univ.filter fun a : F ↦ (1 - a) * A w + a * B w = 0).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type_right]
      exact Finset.sum_congr rfl fun w _ ↦ (Finset.card_filter _ _).symm
    have hbound : ∀ w : Vector F κ,
        (univ.filter fun a : F ↦ (1 - a) * A w + a * B w = 0).card ≤
          1 + q * (if A w = 0 ∧ B w = 0 then 1 else 0) := by
      intro w
      split_ifs with h
      · exact (Finset.card_le_univ _).trans (by omega)
      · exact (card_affine_eq_zero_le _ _ h).trans (by omega)
    have hsum : ∑ w : Vector F κ, (1 + q * (if A w = 0 ∧ B w = 0 then 1 else 0)) =
        q ^ κ + q * (univ.filter fun w : Vector F κ ↦ A w = 0 ∧ B w = 0).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter]
      simp [card_vector_eq_pow, q]
    calc
      _ ≤ (univ.filter P).card := hsplit
      _ ≤ q ^ κ + q * (κ * q ^ (κ - 1)) := by
        rw [hfiber, ← add_le_add_iff_left 0, zero_add, zero_add]
        exact (Finset.sum_le_sum fun w _ ↦ hbound w).trans
          (hsum.le.trans (Nat.add_le_add_left (Nat.mul_le_mul_left q hdeg) _))
      _ = (κ + 1) * q ^ (κ + 1 - 1) := by
        rcases κ with _ | κ
        · simp
        · simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- **Out-of-domain separation** (Annex B, `lem:ood`, count form). For a finite set `L` of tables
on `κ` variables, at most `C(|L|, 2) κ |F|^(κ-1)` points `z` have two distinct members whose
extensions agree at `z`. -/
theorem card_ood_collision_le {κ : ℕ} (L : Finset (CMlPolynomialEval F κ))
    [DecidablePred fun z : Vector F κ ↦ ∃ g ∈ L, ∃ g' ∈ L, g ≠ g' ∧ evalMle g z = evalMle g' z] :
    (univ.filter fun z : Vector F κ ↦
        ∃ g ∈ L, ∃ g' ∈ L, g ≠ g' ∧ evalMle g z = evalMle g' z).card ≤
      L.card.choose 2 * (κ * Fintype.card F ^ (κ - 1)) := by
  classical
  let bad : Finset (CMlPolynomialEval F κ) → Finset (Vector F κ) := fun P ↦
    univ.filter fun z ↦ ∀ g ∈ P, ∀ g' ∈ P, evalMle g z = evalMle g' z
  calc
    _ ≤ ((L.powersetCard 2).biUnion bad).card := by
      refine Finset.card_le_card fun z hz ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨g, hg, g', hg', hne, heq⟩ := hz
      refine Finset.mem_biUnion.mpr ⟨{g, g'}, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.insert_subset hg (Finset.singleton_subset_iff.mpr hg'),
          Finset.card_pair hne⟩
      · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        rintro a (rfl | rfl) b (rfl | rfl) <;> simp [heq]
    _ ≤ ∑ P ∈ L.powersetCard 2, (bad P).card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ L.powersetCard 2, κ * Fintype.card F ^ (κ - 1) := by
      refine Finset.sum_le_sum fun P hP ↦ ?_
      obtain ⟨g, g', hne, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hP).2
      refine (Finset.card_le_card fun z hz ↦ ?_).trans (card_evalMle_eq_le hne)
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz g (by simp) g' (by simp)
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

/-- **Out-of-domain separation for a decoded list.** If a finite list decodes injectively into
tables on `κ` variables, at most `C(|L|, 2) κ |F|^(κ-1)` points separate two distinct members
badly, i.e. give their decoded tables equal extensions. -/
theorem card_ood_collision_image_le {X : Type*} {κ : ℕ} (L : Finset X)
    (dec : X → CMlPolynomialEval F κ) (hinj : Set.InjOn dec L)
    [DecidablePred fun z : Vector F κ ↦
      ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ evalMle (dec U) z = evalMle (dec U') z] :
    (univ.filter fun z : Vector F κ ↦
        ∃ U ∈ L, ∃ U' ∈ L, U ≠ U' ∧ evalMle (dec U) z = evalMle (dec U') z).card ≤
      L.card.choose 2 * (κ * Fintype.card F ^ (κ - 1)) := by
  classical
  rw [← Finset.card_image_of_injOn hinj]
  refine (Finset.card_le_card fun z hz ↦ ?_).trans (card_ood_collision_le (L.image dec))
  rw [Finset.mem_filter] at hz ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  obtain ⟨U, hU, U', hU', hne, heq⟩ := hz.2
  exact ⟨dec U, Finset.mem_image_of_mem _ hU, dec U', Finset.mem_image_of_mem _ hU',
    fun h ↦ hne (hinj hU hU' h), heq⟩

end Count

/-! ## Out-of-domain separation of the next list -/

/-- The out-of-domain value of a decoded member: its claim against `eq_eval(z, ·)`. -/
def oodVal {m κ : ℕ} (z : List E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) : E :=
  claimSum (eqEval z) g

/-- The members of the list of `Q` have pairwise distinct out-of-domain values at `z`. -/
def OodSep (P : LevelCode) {m : ℕ} (Q : (Fin m → Bool) → Fin P.n → E) (z : List E) : Prop :=
  ∀ V ∈ iList P.code P.thr Q, ∀ V' ∈ iList P.code P.thr Q, V ≠ V' →
    oodVal z (decode P V) ≠ oodVal z (decode P V')

/-- The out-of-domain claim against a vector point reads the extension of the table. -/
theorem sum_eqEval_vec {κ : ℕ} (v : Vector E κ) (G : (Fin κ → Bool) → E) :
    ∑ p, eqEval v.toList (bitsL p) * G p = evalMle (tableOf G) v := by
  rw [evalMle_eq_sum, ← Equiv.sum_comp (bitsEquiv κ)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have ht : (tableOf G)[bitsEquiv κ p] = G p := by
    simp [tableOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  have hl : (lagrangeBasis v)[bitsEquiv κ p] = eqEval v.toList (bitsL p) := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (bitsEquiv κ p).isLt,
      eqEval_bitsL v.toList (by simp)]
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    rw [bitsEquiv_val, testBit_bitsToNat]
    simp [List.getD_eq_getElem?_getD]
  rw [ht, hl, mul_comm]

/-- Decoding is injective on interleaved codewords. -/
theorem decode_injOn (P : LevelCode) {ρ : Type*} {V V' : ρ → Fin P.n → E}
    (hV : IsInterleavedCodeword P.code V) (hV' : IsInterleavedCodeword P.code V')
    (h : decode P V = decode P V') : V = V' := by
  funext u
  rw [← enc_decode P hV u, ← enc_decode P hV' u, h]

/-- The table of a message is injective in the message. -/
theorem tableOf_injective {κ : ℕ} : Function.Injective (tableOf (n := κ)) := by
  intro G G' h
  funext p
  have := congrArg (fun t : CMlPolynomialEval E κ ↦ t[bitsEquiv κ p]) h
  simpa [tableOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply] using this

/-- Joining is injective in the split message. -/
theorem joinMsg_injective {n m κ' : ℕ} (hn : n = m + κ') :
    Function.Injective (fun g : (Fin m → Bool) → (Fin κ' → Bool) → E ↦ joinMsg hn g) := by
  subst hn
  intro g g' h
  funext u x
  have := congrFun h (Fin.append u x)
  simpa [joinMsg] using this

open Classical in
/-- **Out-of-domain separation** (Annex B, `lem:ood`): at most `C(listMax, 2)·κ·|E|^(κ−1)` points
`z` leave two members of the list of `Q` with equal out-of-domain values. -/
theorem card_oodSep_bad_le (P : LevelCode) {m κ : ℕ} (hκ : κ = m + P.κ)
    (Q : (Fin m → Bool) → Fin P.n → E) :
    (univ.filter fun v : Vector E κ ↦ ¬ OodSep P Q v.toList).card ≤
      P.listMax.choose 2 * (κ * Fintype.card E ^ (κ - 1)) := by
  set L := iList P.code P.thr Q
  let dec : ((Fin m → Bool) → Fin P.n → E) → CMlPolynomialEval E κ :=
    fun V ↦ tableOf (joinMsg hκ (decode P V))
  have hval : ∀ V (v : Vector E κ), oodVal v.toList (decode P V) = evalMle (dec V) v := by
    intro V v
    rw [oodVal, ← sum_joinMsg hκ, sum_eqEval_vec]
  have hinj : Set.InjOn dec L := by
    intro V hV V' hV' h
    exact decode_injOn P ((mem_iList _ _ _ _).mp hV).1 ((mem_iList _ _ _ _).mp hV').1
      (joinMsg_injective hκ (tableOf_injective h))
  refine (Finset.card_le_card fun v hv ↦ ?_).trans
    ((card_ood_collision_image_le L dec hinj).trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (P.card_iList_le Q))))
  have hv' := (Finset.mem_filter.mp hv).2
  simp only [OodSep, not_forall, not_not, exists_prop] at hv'
  obtain ⟨V, hV, V', hV', hne, heq⟩ := hv'
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, V, hV, V', hV', hne, by
    rw [← hval, ← hval, heq]⟩

end
end LeanVM.Protocol.Whir.Sound
