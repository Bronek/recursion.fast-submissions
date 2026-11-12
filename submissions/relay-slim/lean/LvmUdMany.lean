-- WP-6 (UD). New: the fold by `ℓ` challenges at once, as `ℓ` one-coordinate folds (leanVM's row
-- convention: `Whir/Sound/Code.lean` `consRows`, `foldN`, bit `0` first), and its counts by
-- induction on `ℓ` from the per-round counts of `LvmMcaUd`.
import LvmMcaUd

/-!
# Mutual correlated agreement for `ℓ` challenges (unique decoding)

For an interleaved word `O` with rows `Fin ℓ → Bool` (row `u` is the word `f_u`) and challenges
`α : Fin ℓ → F`, `foldAll α O` folds bit `0` at `α 0`, then bit `1` at `α 1`, and so on
(leanVM's `foldsN` on `rowsOf`, first challenge on the low bit). `foldAll_eq_sum`: it is the
eq-weighted sum `Σ_u eq(α, u) f_u`, `eq(α, u) = Π_i (u_i ? α_i : 1 − α_i)`.

Given a per-round fold-list count `M` (`∀ ρ O, |foldBad C A O| ≤ |ρ| · M`, which
`CodeFacts.card_foldBad_le` provides, `M = mcaUd n k A` in the unique-decoding range):

* `card_foldAllBad_le`: the `α ∈ F^ℓ` with `Λ(foldAll α O) ≠ foldAll α '' Λ(O)` are at most a
  `(2^ℓ − 1) · M / |F|` fraction;
* **`nonempty_iList_of_card_close`** (mutual correlated agreement): if more than that fraction of
  the `α` make `Σ_u eq(α, u) f_u` close to the code at threshold `A`, then all rows `f_u` agree
  with codewords on one common set of at least `A` coordinates;
* `card_foldAllLuck_le`: the `α` for which a column on which `O` and `U` differ agrees after the
  fold are at most an `ℓ · n / |F|` fraction (Schwartz–Zippel for multilinear columns, the
  extractor's luck); `agreeSet_foldAll_eq` off that event.

WHIR's soundness analysis does not use these: its fold challenges are separate rounds
(`LvmMcaUd`). They are the statement over `α ∈ F^ℓ` for the extractor and for comparison.
-/

namespace LeanVM.Protocol.Whir.Ud

open Finset

variable {F : Type*} [Field F] {ι M : Type*}

/-! ## Rows on `m + 1` bits, split on the low bit -/

/-- The rows of a word on `m + 1` bits, split on the low bit (leanVM `consRows`). -/
def splitLow {m : ℕ} (Q : (Fin (m + 1) → Bool) → ι → M) : Bool × (Fin m → Bool) → ι → M :=
  fun r ↦ Q (Fin.cons r.1 r.2)

/-- Rejoin split rows (leanVM `unconsRows`). -/
def joinLow {m : ℕ} (Q : Bool × (Fin m → Bool) → ι → M) : (Fin (m + 1) → Bool) → ι → M :=
  fun u ↦ Q (u 0, Fin.tail u)

theorem splitLow_joinLow {m : ℕ} (Q : Bool × (Fin m → Bool) → ι → M) :
    splitLow (joinLow Q) = Q := by
  funext r
  simp [splitLow, joinLow]

theorem joinLow_splitLow {m : ℕ} (Q : (Fin (m + 1) → Bool) → ι → M) :
    joinLow (splitLow Q) = Q := by
  funext u
  simp [splitLow, joinLow, Fin.cons_self_tail]

section Reindex

variable [Fintype F] [Fintype ι] {ρ ρ' : Type*} [Fintype ρ] [Fintype ρ']

/-- Reindexing the rows keeps list membership. -/
theorem comp_mem_iList (C : Submodule F (ι → F)) {A : ℕ} {O U : ρ → ι → F} (f : ρ' → ρ)
    (hU : U ∈ iList C A O) : (fun r ↦ U (f r)) ∈ iList C A (fun r ↦ O (f r)) := by
  rw [mem_iList] at hU ⊢
  obtain ⟨hcw, S, hS, hag⟩ := hU
  exact ⟨fun r ↦ hcw (f r), S, hS, fun r x hx ↦ hag (f r) x hx⟩

/-- The list of the split word is the split of the list. -/
theorem iList_splitLow [DecidableEq F] [DecidableEq ι] (C : Submodule F (ι → F)) (A : ℕ)
    {m : ℕ} (O : (Fin (m + 1) → Bool) → ι → F) :
    iList C A (splitLow O) = (iList C A O).image splitLow := by
  ext V
  rw [mem_image]
  constructor
  · intro hV
    refine ⟨joinLow V, ?_, splitLow_joinLow V⟩
    have := comp_mem_iList C (fun u : Fin (m + 1) → Bool ↦ (u 0, Fin.tail u)) hV
    rwa [show (fun u : Fin (m + 1) → Bool ↦ splitLow O (u 0, Fin.tail u)) = O from
      joinLow_splitLow O] at this
  · rintro ⟨U, hU, rfl⟩
    exact comp_mem_iList C (fun r : Bool × (Fin m → Bool) ↦ (Fin.cons r.1 r.2 : Fin (m + 1) → Bool)) hU

omit [Field F] [Fintype F] in
/-- The agreement set does not see the row order. -/
theorem agreeSet_splitLow [DecidableEq F] {m : ℕ} (O U : (Fin (m + 1) → Bool) → ι → F) :
    agreeSet (splitLow O) (splitLow U) = agreeSet O U := by
  ext x
  simp only [mem_agreeSet, splitLow]
  constructor
  · intro h u
    simpa [Fin.cons_self_tail] using h (u 0, Fin.tail u)
  · intro h r
    exact h _

end Reindex

/-! ## The fold by `m` challenges -/

/-- **The fold by `α ∈ F^m`**: bit `0` at `α 0` first, then the rest. The result has the single
row `Fin 0 → Bool`. -/
def foldAll : {m : ℕ} → (Fin m → F) → ((Fin m → Bool) → ι → F) → (Fin 0 → Bool) → ι → F
  | 0, _, O => O
  | _ + 1, α, O => foldAll (Fin.tail α) (fold (α 0) (splitLow O))

theorem foldAll_zero (α : Fin 0 → F) (O : (Fin 0 → Bool) → ι → F) : foldAll α O = O := rfl

theorem foldAll_succ {m : ℕ} (α : Fin (m + 1) → F) (O : (Fin (m + 1) → Bool) → ι → F) :
    foldAll α O = foldAll (Fin.tail α) (fold (α 0) (splitLow O)) := rfl

theorem foldAll_cons {m : ℕ} (s : F) (α : Fin m → F) (O : (Fin (m + 1) → Bool) → ι → F) :
    foldAll (Fin.cons s α : Fin (m + 1) → F) O = foldAll α (fold s (splitLow O)) := by
  rw [foldAll_succ, Fin.tail_cons, Fin.cons_zero]

omit [Field F] in
/-- `Fin.consEquiv` on constant fibres is `Fin.cons`. -/
theorem consEquiv_apply' {α : Type*} {m : ℕ} (p : α × (Fin m → α)) :
    (Fin.consEquiv fun _ : Fin (m + 1) ↦ α) p = Fin.cons p.1 p.2 := rfl

/-- The weight `eq(α, u) = Π_i (u_i ? α_i : 1 − α_i)`. -/
def eqW {m : ℕ} (α : Fin m → F) (u : Fin m → Bool) : F :=
  ∏ i, if u i then α i else 1 - α i

/-- **The fold is the eq-weighted sum** `Σ_u eq(α, u) O[u, x]` (Annex B, `def:interleaved`). -/
theorem foldAll_eq_sum : ∀ {m : ℕ} (α : Fin m → F) (O : (Fin m → Bool) → ι → F)
    (v : Fin 0 → Bool) (x : ι), foldAll α O v x = ∑ u, eqW α u * O u x
  | 0, α, O, v, x => by
    rw [foldAll_zero, Fintype.sum_unique]
    simp only [eqW, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    exact congrArg (O · x) (Subsingleton.elim _ _)
  | m + 1, α, O, v, x => by
    rw [foldAll_succ, foldAll_eq_sum, ← (Fin.consEquiv fun _ ↦ Bool).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    simp only [fold, splitLow, eqW, consEquiv_apply', Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Fin.tail, ite_true, Bool.false_eq_true, ite_false]
    ring

/-! ## Counts over `α ∈ F^m` -/

section Counts

variable [Fintype F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

omit [Field F] [DecidableEq F] in
/-- A count over `F × G` of a predicate on the first coordinate. -/
theorem card_filter_fst_add {G : Type*} [Fintype G] (P : F → Prop) (Q : F → G → Prop)
    [DecidablePred P] [∀ s, DecidablePred (Q s)] (R : F → G → Prop) [∀ s, DecidablePred (R s)]
    (hR : ∀ s g, R s g → P s ∨ Q s g) :
    (∑ s, (univ.filter (R s)).card) ≤
      (univ.filter P).card * Fintype.card G + ∑ s, (univ.filter (Q s)).card := by
  have h1 : ∀ s, (univ.filter (R s)).card ≤
      (if P s then Fintype.card G else 0) + (univ.filter (Q s)).card := by
    intro s
    by_cases hs : P s
    · simp only [hs, ite_true]
      exact (card_le_univ _).trans (Nat.le_add_right _ _)
    · simp only [hs, ite_false, zero_add]
      exact card_le_card fun g hg ↦ mem_filter.mpr ⟨mem_univ _,
        ((hR s g (mem_filter.mp hg).2).resolve_left hs)⟩
  refine (Finset.sum_le_sum fun s _ ↦ h1 s).trans ?_
  rw [Finset.sum_add_distrib, Finset.card_filter, Finset.sum_mul]
  gcongr with s
  split_ifs <;> simp

omit [Field F] [DecidableEq F] in
/-- A count over `Fin (m + 1) → F` as a sum over the first coordinate. -/
theorem card_filter_cons {m : ℕ} (P : (Fin (m + 1) → F) → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ s, (univ.filter fun α : Fin m → F ↦ P (Fin.cons s α)).card := by
  rw [card_filter, ← (Fin.consEquiv fun _ ↦ F).sum_comp, Fintype.sum_prod_type]
  simp only [card_filter, consEquiv_apply']
  rfl

open Classical in
/-- **The bad challenges of `m` folds**: if every word with rows `Bool × ρ` has at most `|ρ| M`
fold-bad challenges, the `α ∈ F^m` with `Λ(foldAll α O) ≠ foldAll α '' Λ(O)` are at most
`(2^m − 1) M |F|^(m−1)`. -/
theorem card_foldAllBad_le (C : Submodule F (ι → F)) (A K : ℕ)
    (hK : ∀ (ρ : Type) [Fintype ρ] (O : Bool × ρ → ι → F),
      (foldBad C A O).card ≤ Fintype.card ρ * K) :
    ∀ {m : ℕ} (O : (Fin m → Bool) → ι → F),
      (univ.filter fun α : Fin m → F ↦
          iList C A (foldAll α O) ≠ (iList C A O).image (foldAll α)).card * Fintype.card F ≤
        (2 ^ m - 1) * K * Fintype.card F ^ m
  | 0, O => by
    have : (univ.filter fun α : Fin 0 → F ↦
        iList C A (foldAll α O) ≠ (iList C A O).image (foldAll α)) = ∅ := by
      refine filter_eq_empty_iff.mpr fun α _ ↦ ?_
      simp only [foldAll_zero, ne_eq, not_not]
      exact (Finset.image_id' (s := iList C A O)).symm
    simp [this]
  | m + 1, O => by
    set q := Fintype.card F
    have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
    -- one round: a bad `cons s α` has `s` fold-bad or `α` bad for the folded word
    have hstep : ∀ s (α : Fin m → F),
        iList C A (foldAll (Fin.cons s α : Fin (m + 1) → F) O) ≠
            (iList C A O).image (foldAll (Fin.cons s α : Fin (m + 1) → F)) →
          s ∈ foldBad C A (splitLow O) ∨
            iList C A (foldAll α (fold s (splitLow O))) ≠
              (iList C A (fold s (splitLow O))).image (foldAll α) := by
      intro s α hbad
      by_contra hgood
      push Not at hgood
      obtain ⟨hs, hα⟩ := hgood
      rw [mem_foldBad, not_not, iList_splitLow] at hs
      apply hbad
      rw [foldAll_cons, hα, hs, image_image, image_image]
      exact congrArg (fun f ↦ (iList C A O).image f) (funext fun U ↦ (foldAll_cons s α U).symm)
    rw [card_filter_cons]
    have hsum := card_filter_fst_add (G := Fin m → F) (fun s ↦ s ∈ foldBad C A (splitLow O))
      (fun s α ↦ iList C A (foldAll α (fold s (splitLow O))) ≠
        (iList C A (fold s (splitLow O))).image (foldAll α)) _ hstep
    have hfb : (univ.filter fun s ↦ s ∈ foldBad C A (splitLow O)).card ≤ 2 ^ m * K := by
      rw [filter_mem_eq_inter, univ_inter, ← hcard]
      exact hK _ _
    have hih : ∀ s, (univ.filter fun α : Fin m → F ↦ iList C A (foldAll α (fold s (splitLow O))) ≠
        (iList C A (fold s (splitLow O))).image (foldAll α)).card * q ≤ (2 ^ m - 1) * K * q ^ m :=
      fun s ↦ card_foldAllBad_le C A K hK (fold s (splitLow O))
    have hG : Fintype.card (Fin m → F) = q ^ m := by simp [q]
    rw [hG] at hsum
    have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    calc (∑ s, (univ.filter fun α : Fin m → F ↦ iList C A (foldAll (Fin.cons s α : Fin (m + 1) → F) O) ≠
            (iList C A O).image (foldAll (Fin.cons s α : Fin (m + 1) → F))).card) * q
        ≤ ((univ.filter fun s ↦ s ∈ foldBad C A (splitLow O)).card * q ^ m +
            ∑ s, (univ.filter fun α : Fin m → F ↦
              iList C A (foldAll α (fold s (splitLow O))) ≠
                (iList C A (fold s (splitLow O))).image (foldAll α)).card) * q :=
          Nat.mul_le_mul_right _ hsum
      _ ≤ (2 ^ m * K * q ^ m) * q + ∑ _s : F, (2 ^ m - 1) * K * q ^ m := by
          rw [add_mul, Finset.sum_mul]
          exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hfb))
            (Finset.sum_le_sum fun s _ ↦ hih s)
      _ = (2 ^ (m + 1) - 1) * K * q ^ (m + 1) := by
          rw [Finset.sum_const, card_univ, smul_eq_mul, pow_succ, pow_succ]
          have : 2 ^ m * 2 - 1 = 2 ^ m + (2 ^ m - 1) := by omega
          rw [this]
          ring

open Classical in
/-- **Mutual correlated agreement over `α ∈ F^m`**: if more than a `(2^m − 1) M / |F|` fraction
of the challenges make `foldAll α O = Σ_u eq(α, u) O[u, ·]` close to the code at threshold `A`,
then the list of `O` is nonempty: all rows agree with codewords on one common set of at least `A`
coordinates. -/
theorem nonempty_iList_of_card_close (C : Submodule F (ι → F)) (A K : ℕ)
    (hK : ∀ (ρ : Type) [Fintype ρ] (O : Bool × ρ → ι → F),
      (foldBad C A O).card ≤ Fintype.card ρ * K)
    {m : ℕ} (O : (Fin m → Bool) → ι → F)
    (h : (2 ^ m - 1) * K * Fintype.card F ^ m <
      (univ.filter fun α : Fin m → F ↦ (iList C A (foldAll α O)).Nonempty).card *
        Fintype.card F) :
    (iList C A O).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  refine absurd ((Nat.mul_le_mul_right _ (card_le_card fun α hα ↦ ?_)).trans
    (card_foldAllBad_le C A K hK O)) (not_le.mpr h)
  rw [mem_filter] at hα ⊢
  refine ⟨mem_univ _, fun heq ↦ ?_⟩
  rw [heq, hne, image_empty] at hα
  exact not_nonempty_empty hα.2

omit [Fintype F] [DecidableEq ι] in
/-- Folding never shrinks the agreement set. -/
theorem agreeSet_subset_foldAll : ∀ {m : ℕ} (α : Fin m → F) (O U : (Fin m → Bool) → ι → F),
    agreeSet O U ⊆ agreeSet (foldAll α O) (foldAll α U)
  | 0, _, _, _ => subset_rfl
  | m + 1, α, O, U => by
    rw [foldAll_succ, foldAll_succ, ← agreeSet_splitLow]
    exact (agreeSet_subset_agreeSet_fold _ _ _).trans (agreeSet_subset_foldAll _ _ _)

open Classical in
/-- **The extractor's luck over `α ∈ F^m`**: the `α` for which some column on which `O` and `U`
differ agrees after the fold are at most `m n |F|^(m−1)`. -/
theorem card_foldAllLuck_le : ∀ {m : ℕ} (O U : (Fin m → Bool) → ι → F),
    (univ.filter fun α : Fin m → F ↦
        ¬ agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U).card * Fintype.card F ≤
      m * Fintype.card ι * Fintype.card F ^ m
  | 0, O, U => by simp [foldAll_zero]
  | m + 1, O, U => by
    set q := Fintype.card F
    have hstep : ∀ s (α : Fin m → F),
        ¬ agreeSet (foldAll (Fin.cons s α : Fin (m + 1) → F) O)
            (foldAll (Fin.cons s α : Fin (m + 1) → F) U) ⊆ agreeSet O U →
          ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆
              agreeSet (splitLow O) (splitLow U) ∨
            ¬ agreeSet (foldAll α (fold s (splitLow O))) (foldAll α (fold s (splitLow U))) ⊆
              agreeSet (fold s (splitLow O)) (fold s (splitLow U)) := by
      intro s α hbad
      by_contra hgood
      push Not at hgood
      apply hbad
      rw [foldAll_cons, foldAll_cons, ← agreeSet_splitLow]
      exact hgood.2.trans hgood.1
    rw [card_filter_cons]
    have hsum := card_filter_fst_add (G := Fin m → F)
      (fun s ↦ ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆
        agreeSet (splitLow O) (splitLow U))
      (fun s α ↦ ¬ agreeSet (foldAll α (fold s (splitLow O))) (foldAll α (fold s (splitLow U))) ⊆
        agreeSet (fold s (splitLow O)) (fold s (splitLow U))) _ hstep
    have hG : Fintype.card (Fin m → F) = q ^ m := by simp [q]
    rw [hG] at hsum
    have hl := card_foldLuck_le (splitLow O) (splitLow U)
    have hih : ∀ s, (univ.filter fun α : Fin m → F ↦
        ¬ agreeSet (foldAll α (fold s (splitLow O))) (foldAll α (fold s (splitLow U))) ⊆
          agreeSet (fold s (splitLow O)) (fold s (splitLow U))).card * q ≤
        m * Fintype.card ι * q ^ m :=
      fun s ↦ card_foldAllLuck_le (fold s (splitLow O)) (fold s (splitLow U))
    calc _ ≤ ((univ.filter fun s ↦ ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆
              agreeSet (splitLow O) (splitLow U)).card * q ^ m + ∑ s, (univ.filter fun α : Fin m → F ↦
              ¬ agreeSet (foldAll α (fold s (splitLow O))) (foldAll α (fold s (splitLow U))) ⊆
                agreeSet (fold s (splitLow O)) (fold s (splitLow U))).card) * q :=
          Nat.mul_le_mul_right _ hsum
      _ ≤ (Fintype.card ι * q ^ m) * q + ∑ _s : F, m * Fintype.card ι * q ^ m := by
          rw [add_mul, Finset.sum_mul]
          exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hl))
            (Finset.sum_le_sum fun s _ ↦ hih s)
      _ = (m + 1) * Fintype.card ι * q ^ (m + 1) := by
          rw [Finset.sum_const, card_univ, smul_eq_mul, pow_succ]
          ring

omit [Fintype F] [DecidableEq ι] in
/-- Off the luck event the agreement set of the fold is that of the word. -/
theorem agreeSet_foldAll_eq {m : ℕ} {α : Fin m → F} {O U : (Fin m → Bool) → ι → F}
    (h : agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U) :
    agreeSet (foldAll α O) (foldAll α U) = agreeSet O U :=
  Finset.Subset.antisymm h (agreeSet_subset_foldAll α O U)

omit [DecidableEq ι] in
/-- **The extractor's agreement set** (BLUEPRINT §6.2 step 5): let `U` be in the list of `O`, that
list have at most one member, `α` be neither fold-bad for `O` nor lucky for `(O, U)`. If a single
word `V` (the encoding of the final message) is in the list of `foldAll α O`, then
`V = foldAll α U`, and the columns where `foldAll α O` agrees with `V` are exactly those where
every row of `O` agrees with `U`. -/
theorem agreeSet_foldAll_of_mem (C : Submodule F (ι → F)) {A m : ℕ} {α : Fin m → F}
    {O U : (Fin m → Bool) → ι → F} {V : (Fin 0 → Bool) → ι → F}
    (hU : U ∈ iList C A O) (hone : (iList C A O).card ≤ 1)
    (hgood : iList C A (foldAll α O) = (iList C A O).image (foldAll α))
    (hluck : agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U)
    (hV : V ∈ iList C A (foldAll α O)) :
    V = foldAll α U ∧ agreeSet (foldAll α O) V = agreeSet O U := by
  rw [hgood, mem_image] at hV
  obtain ⟨U', hU', rfl⟩ := hV
  obtain rfl : U' = U := Finset.card_le_one.mp hone _ hU' _ hU
  exact ⟨rfl, agreeSet_foldAll_eq hluck⟩

end Counts

end LeanVM.Protocol.Whir.Ud
