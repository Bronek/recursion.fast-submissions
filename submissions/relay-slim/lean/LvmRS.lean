-- WP-6 (UD). Sections "Interleaved words" and "Uniqueness" are ported from leanVM
-- `formal/lean_vm/LeanVM/Protocol/ToArkLib/Whir/Interleaved.lean` (leanVM `0b850750`), with ArkLib's
-- `ReedSolomon.code`/`mem_code_iff_eval` replaced by `rsCode`/`mem_rsCode_iff_eval` below (same
-- definition and statement as ArkLib `7653a901`, `ArkLib/Data/CodingTheory/ReedSolomon.lean:42-66,208`).
-- `exists_mem_rsCode_eqOn`, `map_mem_rsCode`, `exists_sub_of_eqOn` follow flock-recursive `FRRS`
-- (`rs_interp`) and `FRProximityFold` (`rsCode_map`, `interp_F`), branch kk/base `c52529eb`.
-- The unique-decoding list bound is new.
import Mathlib.LinearAlgebra.Lagrange

/-!
# Reed–Solomon codes, interleaved words, and the unique-decoding list

Generic over a field `F`, a finite index type `ι` (the evaluation domain's positions) and an
evaluation map `domain : ι ↪ F`.

* `rsCode domain k`: the Reed–Solomon code of the polynomials of degree below `k`, an
  `F`-subspace of `ι → F` (ArkLib's `ReedSolomon.code`, inlined since ArkLib cannot be imported).
* `exists_mem_rsCode_eqOn`: any data on at most `k` positions is matched by a codeword
  (Lagrange interpolation).
* The objects of leanVM's Annex B, `def:interleaved`: interleaved words `O : ρ → ι → F`,
  `AgreeOn`, `agreeSet`, `IsInterleavedCodeword`, `IsClose`, the list `iList C A O` at agreement
  threshold `A`.
* `eq_of_mem_code_of_agreeOn`: two codewords agreeing on `k` positions are equal.
* **`card_iList_le_one`** (unique decoding): if `n + k ≤ 2 A` (`n = |ι|`), the list has at most
  one member, for every number of rows. This is the `listMax = 1` of the unique-decoding level
  code (`LvmMcaUd.codeFacts_ud`).
* `exists_sub_of_eqOn`: for a subfield embedding `φ : K →+* F` and a domain inside `K`, a codeword
  over `F` that is `K`-valued on `k` positions is the image of a codeword over `K`; so the codeword
  close to a `K`-valued word, at any threshold `A ≥ k`, is `K`-valued (`sub_of_mem_iList`).
-/

namespace LeanVM.Protocol.Whir

open Finset Polynomial

section RS

variable {F : Type*} [Field F] {ι : Type*}

/-- Evaluation at the points of `domain`, as an `F`-linear map (ArkLib `ReedSolomon.evalOnPoints`). -/
noncomputable def evalOnPoints (domain : ι ↪ F) : F[X] →ₗ[F] (ι → F) where
  toFun p x := p.eval (domain x)
  map_add' p q := by funext x; simp
  map_smul' c p := by funext x; simp

/-- **The Reed–Solomon code** `RS[F, domain, k]`: the evaluations at `domain` of the polynomials of
degree below `k` (ArkLib `ReedSolomon.code`). -/
noncomputable def rsCode (domain : ι ↪ F) (k : ℕ) : Submodule F (ι → F) :=
  (Polynomial.degreeLT F k).map (evalOnPoints domain)

/-- Membership in the code (ArkLib `ReedSolomon.mem_code_iff_eval`). -/
theorem mem_rsCode_iff_eval {k : ℕ} {domain : ι ↪ F} {f : ι → F} :
    f ∈ rsCode domain k ↔ ∃ p : F[X], p.degree < k ∧ ∀ x, p.eval (domain x) = f x :=
  Submodule.mem_map.trans <| exists_congr fun _ ↦ and_congr Polynomial.mem_degreeLT funext_iff

/-- The evaluations of a polynomial of degree below `k` form a codeword. -/
theorem eval_mem_rsCode {k : ℕ} (domain : ι ↪ F) {p : F[X]} (hp : p.degree < k) :
    (fun x ↦ p.eval (domain x)) ∈ rsCode domain k :=
  mem_rsCode_iff_eval.mpr ⟨p, hp, fun _ ↦ rfl⟩

/-- **Interpolation**: data on at most `k` positions is matched by a codeword (the Lagrange
interpolant through `(domain x, u x)`, `x ∈ S`). -/
theorem exists_mem_rsCode_eqOn [DecidableEq ι] (domain : ι ↪ F) {k : ℕ} (S : Finset ι)
    (hS : S.card ≤ k) (u : ι → F) : ∃ v ∈ rsCode domain k, ∀ x ∈ S, v x = u x := by
  have hinj : Set.InjOn (fun x ↦ domain x) S := domain.injective.injOn
  refine ⟨_, eval_mem_rsCode domain ((Lagrange.degree_interpolate_lt u hinj).trans_le
    (by exact_mod_cast hS)), fun x hx ↦ Lagrange.eval_interpolate_at_node u hinj hx⟩

end RS

/-! ## Interleaved words (leanVM `ToArkLib/Whir/Interleaved`) -/

variable {F : Type*} {ι ρ : Type*}

/-- The interleaved words `O` and `U` agree on `S`: every row of `O` equals the same row of `U`
at every coordinate of `S`. -/
def AgreeOn (O U : ρ → ι → F) (S : Finset ι) : Prop :=
  ∀ r, ∀ x ∈ S, O r x = U r x

/-- The coordinates at which all rows of `O` and `U` agree. -/
def agreeSet [Fintype ι] [Fintype ρ] [DecidableEq F] (O U : ρ → ι → F) : Finset ι :=
  univ.filter fun x ↦ ∀ r, O r x = U r x

@[simp] theorem mem_agreeSet [Fintype ι] [Fintype ρ] [DecidableEq F] (O U : ρ → ι → F) (x : ι) :
    x ∈ agreeSet O U ↔ ∀ r, O r x = U r x := by
  simp [agreeSet]

/-- Agreement on `S` is containment of `S` in the agreement set. -/
theorem agreeOn_iff_subset_agreeSet [Fintype ι] [Fintype ρ] [DecidableEq F] (O U : ρ → ι → F)
    (S : Finset ι) : AgreeOn O U S ↔ S ⊆ agreeSet O U := by
  constructor
  · intro h x hx
    exact (mem_agreeSet O U x).mpr fun r ↦ h r x hx
  · intro h r x hx
    exact (mem_agreeSet O U x).mp (h hx) r

/-- Agreement is symmetric. -/
theorem AgreeOn.symm {O U : ρ → ι → F} {S : Finset ι} (h : AgreeOn O U S) : AgreeOn U O S :=
  fun r x hx ↦ (h r x hx).symm

/-- Agreement on `S` is agreement on every subset. -/
theorem AgreeOn.mono {O U : ρ → ι → F} {S T : Finset ι} (h : AgreeOn O U S) (hTS : T ⊆ S) :
    AgreeOn O U T :=
  fun r x hx ↦ h r x (hTS hx)

/-- Agreement is transitive on a common set. -/
theorem AgreeOn.trans {O U V : ρ → ι → F} {S : Finset ι} (h₁ : AgreeOn O U S)
    (h₂ : AgreeOn U V S) : AgreeOn O V S :=
  fun r x hx ↦ (h₁ r x hx).trans (h₂ r x hx)

section Code

variable [Field F]

/-- `U` is an interleaved codeword of `C`: every row lies in `C`. -/
def IsInterleavedCodeword (C : Submodule F (ι → F)) (U : ρ → ι → F) : Prop :=
  ∀ r, U r ∈ C

end Code

/-- `U` is close to `O` at threshold `A`: they agree on some set of at least `A` coordinates. -/
def IsClose (A : ℕ) (O U : ρ → ι → F) : Prop :=
  ∃ S : Finset ι, A ≤ S.card ∧ AgreeOn O U S

/-- Closeness is witnessed by the full agreement set. -/
theorem isClose_iff_le_card_agreeSet [Fintype ι] [Fintype ρ] [DecidableEq F] (A : ℕ)
    (O U : ρ → ι → F) : IsClose A O U ↔ A ≤ (agreeSet O U).card := by
  constructor
  · rintro ⟨S, hS, hagree⟩
    exact hS.trans (card_le_card ((agreeOn_iff_subset_agreeSet O U S).mp hagree))
  · intro h
    exact ⟨agreeSet O U, h, (agreeOn_iff_subset_agreeSet O U _).mpr subset_rfl⟩

/-- A larger threshold is a stronger closeness. -/
theorem IsClose.mono {A A' : ℕ} {O U : ρ → ι → F} (h : IsClose A O U) (hA : A' ≤ A) :
    IsClose A' O U :=
  let ⟨S, hS, hagree⟩ := h
  ⟨S, hA.trans hS, hagree⟩

section List

variable [Field F] [Fintype F] [Fintype ι] [Fintype ρ]

open Classical in
/-- **The list** `Λ(O)` at agreement threshold `A`: the interleaved codewords of `C` that agree
with `O` on a common set of at least `A` coordinates. -/
noncomputable def iList (C : Submodule F (ι → F)) (A : ℕ) (O : ρ → ι → F) :
    Finset (ρ → ι → F) :=
  univ.filter fun U ↦ IsInterleavedCodeword C U ∧ IsClose A O U

@[simp] theorem mem_iList (C : Submodule F (ι → F)) (A : ℕ) (O U : ρ → ι → F) :
    U ∈ iList C A O ↔ IsInterleavedCodeword C U ∧ IsClose A O U := by
  classical
  simp [iList]

end List

/-! ## Uniqueness for Reed–Solomon codes -/

section Uniqueness

variable [Field F]

/-- **Uniqueness.** Two codewords of the Reed–Solomon code of polynomials of degree below `k`
that agree on a set of `k` coordinates are equal. -/
theorem eq_of_mem_code_of_agreeOn (domain : ι ↪ F) {k : ℕ} {u v : ι → F}
    (hu : u ∈ rsCode domain k) (hv : v ∈ rsCode domain k) (S : Finset ι)
    (hS : k ≤ S.card) (h : ∀ x ∈ S, u x = v x) : u = v := by
  obtain ⟨P, hP, hPu⟩ := mem_rsCode_iff_eval.mp hu
  obtain ⟨Q, hQ, hQv⟩ := mem_rsCode_iff_eval.mp hv
  have hk : ((k : ℕ) : WithBot ℕ) ≤ (S.card : WithBot ℕ) := by exact_mod_cast hS
  have hPQ : P = Q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq S (domain.injective.injOn)
      (hP.trans_le hk) (hQ.trans_le hk) fun x hx ↦ by rw [hPu, hQv, h x hx]
  funext x
  rw [← hPu, ← hQv, hPQ]

/-- **Interleaved uniqueness.** Two interleaved codewords of the Reed–Solomon code of degree
below `k` that agree on a common set of `k` coordinates are equal. -/
theorem eq_of_isInterleavedCodeword_of_agreeOn (domain : ι ↪ F) {k : ℕ} {U V : ρ → ι → F}
    (hU : IsInterleavedCodeword (rsCode domain k) U)
    (hV : IsInterleavedCodeword (rsCode domain k) V) (S : Finset ι)
    (hS : k ≤ S.card) (h : AgreeOn U V S) : U = V :=
  funext fun r ↦ eq_of_mem_code_of_agreeOn domain (hU r) (hV r) S hS (h r)

/-- **Distinct interleaved codewords agree on fewer than `k` coordinates** of the Reed–Solomon
code of degree below `k`. -/
theorem card_agreeSet_lt [Fintype ι] [Fintype ρ] [DecidableEq F] (domain : ι ↪ F) {k : ℕ}
    {U V : ρ → ι → F} (hU : IsInterleavedCodeword (rsCode domain k) U)
    (hV : IsInterleavedCodeword (rsCode domain k) V) (hne : U ≠ V) :
    (agreeSet U V).card < k := by
  by_contra hk
  exact hne (eq_of_isInterleavedCodeword_of_agreeOn domain hU hV _ (not_lt.mp hk)
    ((agreeOn_iff_subset_agreeSet U V _).mpr subset_rfl))

end Uniqueness

/-! ## The unique-decoding list -/

section UniqueDecoding

variable [Field F] [Fintype ι]

/-- Two sets of at least `A` coordinates each meet in at least `k` coordinates when
`|ι| + k ≤ 2 A`. -/
theorem le_card_inter_of_ud [DecidableEq ι] {k A : ℕ} (hA : Fintype.card ι + k ≤ 2 * A)
    {S T : Finset ι} (hS : A ≤ S.card) (hT : A ≤ T.card) : k ≤ (S ∩ T).card := by
  have h1 := card_union_add_card_inter S T
  have h2 : (S ∪ T).card ≤ Fintype.card ι := card_le_univ _
  omega

/-- In the unique-decoding range, a set of at least `A` coordinates has at least `k`. -/
theorem le_card_of_ud {k A : ℕ} (hA : Fintype.card ι + k ≤ 2 * A) {S : Finset ι}
    (hS : A ≤ S.card) : k ≤ S.card := by
  have : S.card ≤ Fintype.card ι := card_le_univ _
  omega

/-- **Unique decoding**: if `|ι| + k ≤ 2 A`, two interleaved codewords close to the same word at
threshold `A` are equal. -/
theorem eq_of_isClose_of_ud (domain : ι ↪ F) {k A : ℕ} (hA : Fintype.card ι + k ≤ 2 * A)
    {O U V : ρ → ι → F} (hU : IsInterleavedCodeword (rsCode domain k) U)
    (hV : IsInterleavedCodeword (rsCode domain k) V) (hOU : IsClose A O U) (hOV : IsClose A O V) :
    U = V := by
  classical
  obtain ⟨S, hS, hSU⟩ := hOU
  obtain ⟨T, hT, hTV⟩ := hOV
  exact eq_of_isInterleavedCodeword_of_agreeOn domain hU hV (S ∩ T)
    (le_card_inter_of_ud hA hS hT)
    ((hSU.mono inter_subset_left).symm.trans (hTV.mono inter_subset_right))

/-- **The unique-decoding list bound** (`listMax = 1`): if `|ι| + k ≤ 2 A`, every interleaved
word, with any number of rows, has at most one interleaved codeword of `RS[F, domain, k]` at
threshold `A`. -/
theorem card_iList_le_one [Fintype F] [Fintype ρ] (domain : ι ↪ F) {k A : ℕ}
    (hA : Fintype.card ι + k ≤ 2 * A) (O : ρ → ι → F) :
    (iList (rsCode domain k) A O).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun U hU V hV ↦ ?_
  rw [mem_iList] at hU hV
  exact eq_of_isClose_of_ud domain hA hU.1 hV.1 hU.2 hV.2

end UniqueDecoding

/-! ## Codewords over an extension that are subfield-valued -/

section Sub

variable {K : Type*} [Field K] [Field F] {ι : Type*}

/-- An `K`-codeword maps to an `F`-codeword of the same code over the image points. -/
theorem map_mem_rsCode (φ : K →+* F) {domK : ι ↪ K} {domF : ι ↪ F}
    (hdom : ∀ x, domF x = φ (domK x)) {k : ℕ} {v : ι → K} (hv : v ∈ rsCode domK k) :
    (fun x ↦ φ (v x)) ∈ rsCode domF k := by
  obtain ⟨p, hp, hpv⟩ := mem_rsCode_iff_eval.mp hv
  refine mem_rsCode_iff_eval.mpr ⟨p.map φ, by rwa [degree_map], fun x ↦ ?_⟩
  rw [hdom, eval_map, eval₂_hom, hpv]

/-- **Subfield-valued codewords** (FR `interp_F`): for `φ : K →+* F` and the domain `domF = φ ∘ domK`,
a codeword of `RS[F, domF, k]` that agrees on `k` positions with the image of a `K`-valued word is
the image of a codeword of `RS[K, domK, k]`. -/
theorem exists_sub_of_eqOn [DecidableEq ι] (φ : K →+* F) {domK : ι ↪ K} {domF : ι ↪ F}
    (hdom : ∀ x, domF x = φ (domK x)) {k : ℕ} {c : ι → F} (hc : c ∈ rsCode domF k) (w : ι → K)
    (S : Finset ι) (hS : k ≤ S.card) (hcS : ∀ x ∈ S, c x = φ (w x)) :
    ∃ c' ∈ rsCode domK k, c = fun x ↦ φ (c' x) := by
  obtain ⟨J, hJS, hJ⟩ := exists_subset_card_eq hS
  obtain ⟨c', hc', hc'J⟩ := exists_mem_rsCode_eqOn domK J hJ.le w
  refine ⟨c', hc', eq_of_mem_code_of_agreeOn domF hc (map_mem_rsCode φ hdom hc') J hJ.ge
    fun x hx ↦ ?_⟩
  rw [hcS x (hJS hx), hc'J x hx]

/-- **The close codeword of a subfield-valued word is subfield-valued**: if `O` has `K`-valued
rows (`O = φ ∘ W`) and `U` is in its list at a threshold `A ≥ k`, every row of `U` is the image of
a codeword over `K`. -/
theorem sub_of_mem_iList [Fintype F] [Fintype ι] [DecidableEq ι] {ρ : Type*} [Fintype ρ]
    (φ : K →+* F) {domK : ι ↪ K} {domF : ι ↪ F} (hdom : ∀ x, domF x = φ (domK x)) {k A : ℕ}
    (hkA : k ≤ A) (W : ρ → ι → K) {U : ρ → ι → F}
    (hU : U ∈ iList (rsCode domF k) A fun r x ↦ φ (W r x)) (r : ρ) :
    ∃ c' ∈ rsCode domK k, U r = fun x ↦ φ (c' x) := by
  obtain ⟨hcw, S, hS, hag⟩ := (mem_iList _ _ _ _).mp hU
  exact exists_sub_of_eqOn φ hdom (hcw r) (W r) S (hkA.trans hS) fun x hx ↦ (hag r x hx).symm

end Sub

end LeanVM.Protocol.Whir
