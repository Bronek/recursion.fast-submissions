-- New for lvm2 (WP JB-L, J2): the extractor's facts for a level-0 word decoded at the Johnson radius
-- (JB-DES §3 option B: decoding with advice, the decoder program unchanged), the list version of
-- `LvmWhirDoom.ud_extract`; the per-member luck union.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the extractor's facts with a list)
-/

import LvmWhirDoom

/-!
# Extraction with a list (`C_rec` at the Johnson radius)

`ud_extract` takes uniqueness from the unique-decoding radius (`card_iList_le_one`): the one
candidate is the good one, and the residual is its fold. At the Johnson radius the root's word has
a list of up to `L` candidates, and the residual `f` is the advice that selects one (JB-DES §3 B,
decoding with advice; the decoder program is unchanged). The doom is restricted accordingly:

* **the restricted final doom** `FinalRDoomJ`: `f` is not the fold of any good candidate. Its
  negation is exactly what the extractor needs, and it is the end state of a WHIR invariant
  relativised to the list members that are not folds of good candidates (open, see below): no
  fold-bad or collision event appears in the extractor's statement, those stay inside the WHIR
  groups' escapes.
* **luck over the list** `FoldAllLuckL`: some list member's agreement set grows under the fold.
  `card_foldLuckL_le`: per fold round at most `L·n` challenges (`card_foldLuck_le` per member),
  the luck term `L·n/|E|` of JB-DES §2.2. Off it, the selected member's pair is not lucky
  (`foldAllLuck_of_luckL`).

`j_extract`, the list version of `ud_extract`: from `¬ FinalRDoomJ`, a good candidate `q` whose
blocks fold to `f`, agreeing with the word on at least `A` columns and, off the luck of its pair,
with `agreeSet (foldAll α W) (Enc f) = agreeSet W (Enc q)`, the set `E` computes. `decodeRec_correct`
consumes exactly these (it needs `2^κ₀ ≤ A` agreeing columns: `A₀ = 23261 ≥ 2^13` for
`codeJ13R3`). `not_finalRDoomJ_of_ud`: in the unique-decoding range `ud_extract`'s hypotheses
imply `¬ FinalRDoomJ`, so the restricted doom is never stronger than v1's.

**Open (J2):** that an accepting transcript is, except with the charged escapes, not in
`FinalRDoomJ`: the WHIR invariant relativised to tracked members (JB-L report §4).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset

section

/-- **The restricted final doom**: the residual `f` is not the fold of any good candidate of `W`. -/
def FinalRDoomJ (μ R A : ℕ) (Good : Column μ → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E) : Prop :=
  ∀ q ∈ Candidates μ R A W, Good q → f ≠ foldMsg α q

/-- **Luck over the list**: some member of the list of `O` has an agreement set that the fold by
`α` enlarges. -/
def FoldAllLuckL {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Submodule E (ι → E)) (A : ℕ)
    {m : ℕ} (α : Fin m → E) (O : (Fin m → Bool) → ι → E) : Prop :=
  ∃ U ∈ iList C A O, FoldAllLuck α O U

/-- The luck over the list contains the luck of every member. -/
theorem foldAllLuck_of_luckL {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Submodule E (ι → E)}
    {A m : ℕ} {α : Fin m → E} {O U : (Fin m → Bool) → ι → E} (hU : U ∈ iList C A O)
    (h : ¬ FoldAllLuckL C A α O) : ¬ FoldAllLuck α O U :=
  fun hl ↦ h ⟨U, hU, hl⟩

open Classical in
/-- **One round's luck over the list**: at most `L·n` challenges `s` make some member's agreement
set grow under the fold (`card_foldLuck_le` for each member). -/
theorem card_foldLuckL_le {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]
    (C : Submodule E (ι → E)) (A L : ℕ) (O : Bool × ρ → ι → E)
    (hL : (iList C A O).card ≤ L) :
    (univ.filter fun s : E ↦ ∃ U ∈ iList C A O,
        ¬ agreeSet (fold s O) (fold s U) ⊆ agreeSet O U).card ≤ L * Fintype.card ι := by
  refine (card_filter_exists_le (iList C A O) _ (N := Fintype.card ι) fun U _ ↦
    card_foldLuck_le O U).trans ?_
  exact Nat.mul_le_mul_right _ hL

/-- **The extractor's facts at the Johnson radius** (the list version of `ud_extract`): if the
residual is the fold of a good candidate (`¬ FinalRDoomJ`), that candidate `q` agrees with the word
on at least `A` columns, and off the luck of its pair the agreement set of the folded word with the
residual's encoding is the word's agreement set with `q`'s encoding. -/
theorem j_extract {μ R A : ℕ} (h64 : μ - laneBits + R ≤ 64)
    (Good : Column μ → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E) (hR : ¬ FinalRDoomJ μ R A Good W α f) :
    ∃ q ∈ Candidates μ R A W, Good q ∧ f = foldMsg α q ∧
      A ≤ (agreeSet (laneRows μ R W) (encRows μ R q)).card ∧
      (¬ FoldAllLuck α (laneRows μ R W) (encRows μ R q) →
        agreeSet (foldAll α (laneRows μ R W)) (fun _ ↦ enc (μ - laneBits) R f) =
          agreeSet (laneRows μ R W) (encRows μ R q)) := by
  classical
  simp only [FinalRDoomJ, not_forall, not_not, exists_prop] at hR
  obtain ⟨q, hq, hgood, hf⟩ := hR
  set C := rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
  have hmem : encRows μ R q ∈ iList C A (laneRows μ R W) := by
    rw [encRows_eq]; exact comp_mem_iList C (bitsEquiv laneBits) (mem_iList_of_candidate h64 hq)
  have heq : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R f) = foldAll α (encRows μ R q) := by
    rw [foldAll_encRows, hf]
  refine ⟨q, hq, hgood, hf, ?_, fun hluck ↦ ?_⟩
  · exact (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2
  · rw [heq]
    exact agreeSet_foldAll_eq (not_not.mp hluck)

/-- **The restricted doom is never stronger than v1's**: in the unique-decoding range, not doomed
at the commitment and at the final residual (`ud_extract`'s hypotheses) implies `¬ FinalRDoomJ`. -/
theorem not_finalRDoomJ_of_ud {μ R A : ℕ} (hμ : laneBits ≤ μ) (h64 : μ - laneBits + R ≤ 64)
    (hud : 2 ^ (μ - laneBits + R) + 2 ^ (μ - laneBits) ≤ 2 * A)
    (Good : Column μ → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E) (hC : ¬ CommitDoomUd μ R A Good W)
    (hF : ¬ FinalDoomUd μ R A h64 W α f) :
    ¬ FinalRDoomJ μ R A Good W α f := by
  obtain ⟨q, hq, hgood, -, hf, -⟩ := ud_extract hμ h64 hud Good W α f hC hF
  exact fun h ↦ h q hq hgood hf

end
end LeanVM.Protocol.Whir.Sound
