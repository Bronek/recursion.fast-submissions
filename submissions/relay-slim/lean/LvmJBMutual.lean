-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBMutual.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBMain

/-!
# Haböck's mutual correlated agreement

Ordinary correlated agreement says the pair `(u₀, u₁)` agrees with a pair of codewords
`(v₀, v₁)` on many coordinates.  Haböck's strengthening says more: for almost every
parameter `z`, the agreement set of the *line point* `u₀ + z u₁` is not merely larger
than the correlated agreement set — it is **equal** to it.  In other words a random `z`
reveals no accidental agreements.

The inclusion `Λ ⊆ Λ_z` is immediate.  The content is the reverse, and it is the same
one-affine-root observation that drives the §4 endgame: a coordinate outside `Λ` can
produce an accidental agreement for at most one value of `z` (`eq_of_mem_pairDisagree`).
So the sets `Λ_z \ Λ` are pairwise disjoint subsets of the correlated disagreement set
`E`, and at most `|E|` parameters can fail.

Combining with §4 (`card_pairDisagree_le`, which bounds `|E|` by `e`) gives the sharp
form: **mutual correlated agreement fails for at most `e` parameters** — no separate
argument, and no loss beyond the distance bound already assumed.
-/

namespace JBAgreement

open Finset Polynomial

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The correlated agreement set `Λ`: coordinates where *both* words match. -/
def corrAgree (u₀ u₁ v₀ v₁ : ι → F) : Finset ι :=
  univ.filter fun x => u₀ x = v₀ x ∧ u₁ x = v₁ x

/-- The agreement set `Λ_z` of the line point `u₀ + z u₁` with `v₀ + z v₁`. -/
def lineAgree (u₀ u₁ v₀ v₁ : ι → F) (z : F) : Finset ι :=
  univ.filter fun x => u₀ x + z * u₁ x = v₀ x + z * v₁ x

omit [Field F] [DecidableEq ι] in
@[simp] lemma mem_corrAgree {u₀ u₁ v₀ v₁ : ι → F} {x : ι} :
    x ∈ corrAgree u₀ u₁ v₀ v₁ ↔ (u₀ x = v₀ x ∧ u₁ x = v₁ x) := by simp [corrAgree]

omit [DecidableEq ι] in
@[simp] lemma mem_lineAgree {u₀ u₁ v₀ v₁ : ι → F} {z : F} {x : ι} :
    x ∈ lineAgree u₀ u₁ v₀ v₁ z ↔ u₀ x + z * u₁ x = v₀ x + z * v₁ x := by
  simp [lineAgree]

omit [Field F] in
/-- `Λ` is the complement of the correlated disagreement set `E`. -/
lemma corrAgree_eq_compl (u₀ u₁ v₀ v₁ : ι → F) :
    corrAgree u₀ u₁ v₀ v₁ = univ \ pairDisagree u₀ u₁ v₀ v₁ := by
  ext x
  simp only [mem_corrAgree, mem_sdiff, mem_univ, true_and, mem_pairDisagree, not_or, not_not]

omit [DecidableEq ι] in
/-- Correlated agreement always implies agreement along the line. -/
lemma corrAgree_subset_lineAgree (u₀ u₁ v₀ v₁ : ι → F) (z : F) :
    corrAgree u₀ u₁ v₀ v₁ ⊆ lineAgree u₀ u₁ v₀ v₁ z := by
  intro x hx
  rw [mem_corrAgree] at hx
  rw [mem_lineAgree, hx.1, hx.2]

/-- **The count of accidental agreements.**

The parameters at which the line agreement set strictly exceeds the correlated agreement
set are at most as many as the correlated disagreement set has coordinates.

Each such parameter consumes at least one coordinate of `E`, and no coordinate can be
consumed twice: at a coordinate of `E` the agreement equation is a nontrivial affine
equation in `z`, so it has a single root. -/
theorem card_mutual_bad_le (u₀ u₁ v₀ v₁ : ι → F) (S : Finset F) :
    (S.filter fun z => lineAgree u₀ u₁ v₀ v₁ z ≠ corrAgree u₀ u₁ v₀ v₁).card
      ≤ (pairDisagree u₀ u₁ v₀ v₁).card := by
  set Bad := S.filter fun z => lineAgree u₀ u₁ v₀ v₁ z ≠ corrAgree u₀ u₁ v₀ v₁ with hBad
  set D : F → Finset ι := fun z => lineAgree u₀ u₁ v₀ v₁ z \ corrAgree u₀ u₁ v₀ v₁ with hD
  -- Each `D z` lands in the correlated disagreement set.
  have hDsub : ∀ z, D z ⊆ pairDisagree u₀ u₁ v₀ v₁ := by
    intro z x hx
    rw [hD] at hx
    simp only [mem_sdiff, mem_corrAgree, not_and_or] at hx
    rw [mem_pairDisagree]
    rcases hx.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- Distinct parameters consume distinct coordinates.
  have hdisj : ∀ z ∈ Bad, ∀ z' ∈ Bad, z ≠ z' → Disjoint (D z) (D z') := by
    intro z _ z' _ hne
    rw [Finset.disjoint_left]
    intro x hxz hxz'
    have hx : x ∈ pairDisagree u₀ u₁ v₀ v₁ := hDsub z hxz
    rw [hD, mem_sdiff, mem_lineAgree] at hxz hxz'
    exact hne (eq_of_mem_pairDisagree hx hxz.1 hxz'.1)
  -- A bad parameter really does consume a coordinate.
  have hne : ∀ z ∈ Bad, 1 ≤ (D z).card := by
    intro z hz
    rw [hBad, mem_filter] at hz
    have hss : corrAgree u₀ u₁ v₀ v₁ ⊂ lineAgree u₀ u₁ v₀ v₁ z :=
      lt_of_le_of_ne (corrAgree_subset_lineAgree u₀ u₁ v₀ v₁ z) (Ne.symm hz.2)
    obtain ⟨x, hx1, hx2⟩ := Finset.exists_of_ssubset hss
    exact Finset.card_pos.mpr ⟨x, by rw [hD, mem_sdiff]; exact ⟨hx1, hx2⟩⟩
  -- Count.
  have hbi : (Bad.biUnion D).card = ∑ z ∈ Bad, (D z).card := card_biUnion hdisj
  have hle : ∑ z ∈ Bad, (D z).card ≤ (pairDisagree u₀ u₁ v₀ v₁).card := by
    rw [← hbi]
    refine card_le_card fun x hx => ?_
    obtain ⟨z, _, hz⟩ := mem_biUnion.mp hx
    exact hDsub z hz
  calc Bad.card = ∑ _z ∈ Bad, 1 := by simp
    _ ≤ ∑ z ∈ Bad, (D z).card := sum_le_sum hne
    _ ≤ _ := hle

/-- **Mutual correlated agreement (Haböck).**

Under the hypotheses of §4 — every line point `u₀ + z u₁`, `z ∈ S`, is within distance
`e` of the corresponding point of a fixed line of codewords, and `|S| > e + 1` — the
line agreement set *equals* the correlated agreement set for all but at most `e`
parameters of `S`.

So the correlated agreement produced by the branch argument is not merely a lower bound
on what a random `z` sees: it is exactly what a random `z` sees. -/
theorem card_mutual_bad_le_of_agree {u₀ u₁ v₀ v₁ : ι → F} {e : ℕ} {S : Finset F}
    (hdis : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (fun x => v₀ x + z * v₁ x)).card ≤ e)
    (hS : e + 1 < S.card) :
    (S.filter fun z => lineAgree u₀ u₁ v₀ v₁ z ≠ corrAgree u₀ u₁ v₀ v₁).card ≤ e :=
  le_trans (card_mutual_bad_le u₀ u₁ v₀ v₁ S) (card_pairDisagree_le hdis hS)

/-- The Reed–Solomon form: for all but at most `e` parameters `z`, the coordinates on
which `u₀ + z u₁` agrees with the codeword `v₀ + z v₁` are exactly the coordinates of
correlated agreement of `(u₀, u₁)` with `(v₀, v₁)`. -/
theorem mutual_correlatedAgreement (dom : ι → F) (u₀ u₁ : ι → F) (v₀ v₁ : F[X]) (e : ℕ)
    (S : Finset F) (hS : e + 1 < S.card)
    (hagree : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x)
                (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) :
    (S.filter fun z =>
        lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z
          ≠ corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e := by
  refine card_mutual_bad_le_of_agree (e := e) (S := S) ?_ hS
  intro z hz
  have h := hagree z hz
  simpa only [RSeval_line dom v₀ v₁] using h

end JBAgreement
