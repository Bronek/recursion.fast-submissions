-- New for lvm2 (X-REC2, stage S4; BLUEPRINT2 §3.2, §5): the extractor's facts for a `C_rec` with two WHIR levels.
-- Built on WP-7's `LvmWhirDoom` (`ud_extract`'s argument, `foldAll_mem_iList`, `foldAll_encRows`).
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the extractor's doom facts at two levels)

  The doom of the level-1 commitment of a two-level unique-decoding opening, and the extraction
  facts: under no commitment doom, no level-1 doom and no final doom, the root's unique good
  candidate `q` folds to the level-1 word's unique list member, whose fold is the residual.
-/

import LvmWhirDoom
import LvmWhirParams
import LvmWhirParams24

/-!
# Two levels: the level-1 doom and the extractor's facts

Setting (BLUEPRINT2 §3.2, S4): a root committed as a level-0 word `W₀` (`2^(μ−6+R)` leaves of
`2^6` `K` words; lvm's `C_rec`: `μ = 19`, `R = 2`), level-0 fold challenges `α₀ ∈ E^6`, then a
level-1 word `W₁` whose `2^ℓ₁` lanes (`E` scalars, a leaf of `3·2^ℓ₁` `K` words) are rows `Q'` of
the level-1 code `P₁` (`κ₁ = μ − 6 − ℓ₁`; lvm: `ℓ₁ = 4`, `κ₁ = 9`, `R₁ = 3`), level-1 fold
challenges `α₁ ∈ E^ℓ₁` and the final residual `f₂` (`2^κ₁` `E` scalars). WHIR glues a level-1
row family `V` to the folded root word through `joinMsg` (lane bits low): the level-0 message
of `V` is `joinMsg hκ (decode P₁ V)`.

* `MidDoomUd`: **the level-1 commitment's doom**: no member `V` of the level-1 list has a
  level-0 encoding close to the folded root word `C = foldAll α₀ (laneRows W₀)` (agreement on
  fewer than `A` columns). Created at the commitment of `W₁` (a prover move); from it the level-0
  query group catches the level-1 word except with probability `eQueryUd` (the certificate's
  `LvmCertSMid2`'s spec, the generalised `escRet_queryFrag_le_ud`).
* `FinalDoomL`: **the final residual's doom at level 1**: `Enc₁(f₂)` is not in the list of the
  level-1 rows folded by `α₁` (the part of `FinViol` that the extractor needs).
* **`ud_extract2`**: `¬ CommitDoomUd ∧ ¬ MidDoomUd ∧ ¬ FinalDoomL` ⇒ the root's unique candidate
  `q` is good; the level-1 list has a unique member `V`; `joinMsg (decode V) = foldMsg α₀ q` (the
  level-1 message is the level-0 fold of `q`); `f₂ = Σ_u eq(α₁, u) · decode V u`; both words agree
  with their codewords on at least the thresholds, and off each level's luck event the agreement
  set of the folded word with the encoding of the next message is the joint agreement set. So the
  extractor decodes level 1 first (`V`'s message on the agreement set of `foldAll α₁ Q'` with
  `Enc₁(f₂)`), then level 0 as v1 with `f₁ := joinMsg (decode V)`.
* `not_finalDoomUd_foldMsg`: the level-0 fold of a candidate is never final-doomed: v1's level-0
  decoder facts (`ud_extract`, `LvmXDecUd.decodeRec_of_ud`) apply with `f := foldMsg α₀ q`.
* `ud_extract_rec20`, `ud_extract_rec18`: the instances at lvm's `C_rec` (P20: `κ = 13, 9`,
  `R = 2, 3`; S2's P8, μ = 18: `κ = 12, 8`), with non-vacuity at P20 (`ud_extract_rec20_nonvacuous`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset

section

/-! ## The level-1 rows -/

/-- **The level-1 rows** of a word whose leaves hold `2^ℓ` `E` scalars as `K` triples (WHIR's
`laneO 1`, `extRow`): row `u` at column `v` is lane `⟨u⟩` of leaf `v`. -/
def rows1 (ℓ n : ℕ) (W : Word) : (Fin ℓ → Bool) → Fin n → E :=
  fun u v ↦ (lanesOf 1 (W v)).getD (bitsToNat u) 0

/-! ## The doom predicates -/

/-- **The level-1 commitment's doom**: every member `V` of the level-1 list of `Q'` has a level-0
encoding (`Enc₀(joinMsg (decode V))`) that agrees with the folded root word `C` on fewer than `A`
columns. -/
def MidDoomUd {κ₀ R₀ ℓ₁ : ℕ} (A : ℕ) (P₁ : LevelCode) (hκ : κ₀ = ℓ₁ + P₁.κ)
    (C : Fin (2 ^ (κ₀ + R₀)) → E) (Q' : (Fin ℓ₁ → Bool) → Fin P₁.n → E) : Prop :=
  ∀ V ∈ iList P₁.code P₁.thr Q',
    (univ.filter fun x ↦ enc κ₀ R₀ (joinMsg hκ (decode P₁ V)) x = C x).card < A

/-- **The final residual's doom at level 1**: `Enc₁(f₂)` is not in the list of the level-1 rows
folded by `α₁`. -/
def FinalDoomL {ℓ₁ : ℕ} (P₁ : LevelCode) (Q' : (Fin ℓ₁ → Bool) → Fin P₁.n → E) (α₁ : Fin ℓ₁ → E)
    (f₂ : (Fin P₁.κ → Bool) → E) : Prop :=
  (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R f₂) ∉ iList P₁.code P₁.thr (foldAll α₁ Q')

/-! ## The facts -/

/-- A candidate's level-0 fold is in the list of the folded root word. -/
theorem foldMsg_mem {μ R A : ℕ} (h64 : μ - laneBits + R ≤ 64) {W : Word} {q : Column μ}
    (hq : q ∈ Candidates μ R A W) (α : Fin laneBits → E) :
    (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R (foldMsg α q)) ∈
      iList (rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) A
        (foldAll α (laneRows μ R W)) := by
  have hmem64 := mem_iList_of_candidate h64 hq
  have hmem : encRows μ R q ∈ iList (rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) A
      (laneRows μ R W) := by
    rw [encRows_eq]; exact comp_mem_iList _ (bitsEquiv laneBits) hmem64
  rw [← foldAll_encRows]
  exact foldAll_mem_iList _ α hmem

/-- **The level-0 fold of a candidate is never final-doomed** (v1's level-0 decoder facts then
apply with `f := foldMsg α q`). -/
theorem not_finalDoomUd_foldMsg {μ R A : ℕ} (h64 : μ - laneBits + R ≤ 64) {W : Word}
    {q : Column μ} (hq : q ∈ Candidates μ R A W) (α : Fin laneBits → E) :
    ¬ FinalDoomUd μ R A h64 W α (foldMsg α q) :=
  fun hD ↦ hD (foldMsg_mem h64 hq α)

/-- **The extractor's facts at two levels** (BLUEPRINT2 §3.2, S4): not doomed at the root's
commitment, at the level-1 commitment and at the final residual, the root has exactly one
candidate `q`, it is good; the level-1 list has exactly one member `V`; `V`'s level-0 message is
the fold of `q`; the residual is the fold of `V`'s messages; both levels' agreement sets are at
least their thresholds, and off each level's luck event the extractor's agreement set (the folded
word against the encoding of the next message) is the joint one. -/
theorem ud_extract2 {μ R A ℓ₁ : ℕ} (hμ : laneBits ≤ μ) (h64 : μ - laneBits + R ≤ 64)
    (hud : 2 ^ (μ - laneBits + R) + 2 ^ (μ - laneBits) ≤ 2 * A)
    (P₁ : LevelCode) (hκ : μ - laneBits = ℓ₁ + P₁.κ) (hL : P₁.listMax ≤ 1)
    (Good : Column μ → Prop) (W₀ : Word) (α₀ : Fin laneBits → E)
    (Q' : (Fin ℓ₁ → Bool) → Fin P₁.n → E) (α₁ : Fin ℓ₁ → E) (f₂ : (Fin P₁.κ → Bool) → E)
    (hC : ¬ CommitDoomUd μ R A Good W₀)
    (hM : ¬ MidDoomUd A P₁ hκ (foldAll α₀ (laneRows μ R W₀) Fin.elim0) Q')
    (hF : ¬ FinalDoomL P₁ Q' α₁ f₂) :
    ∃ q ∈ Candidates μ R A W₀, Good q ∧ (∀ q' ∈ Candidates μ R A W₀, q' = q) ∧
      ∃ V ∈ iList P₁.code P₁.thr Q', (∀ V' ∈ iList P₁.code P₁.thr Q', V' = V) ∧
        joinMsg hκ (decode P₁ V) = foldMsg α₀ q ∧
        f₂ = ∑ u, eqW α₁ u • decode P₁ V u ∧
        P₁.thr ≤ (agreeSet Q' V).card ∧
        (¬ FoldAllLuck α₁ Q' V →
          agreeSet (foldAll α₁ Q') (fun _ ↦ enc P₁.κ P₁.R f₂) = agreeSet Q' V) ∧
        A ≤ (agreeSet (laneRows μ R W₀) (encRows μ R q)).card ∧
        (¬ FoldAllLuck α₀ (laneRows μ R W₀) (encRows μ R q) →
          agreeSet (foldAll α₀ (laneRows μ R W₀))
              (fun _ ↦ enc (μ - laneBits) R (foldMsg α₀ q)) =
            agreeSet (laneRows μ R W₀) (encRows μ R q)) := by
  classical
  set C₀ := rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
  have hn : Fintype.card (Fin (2 ^ (μ - laneBits + R))) + 2 ^ (μ - laneBits) ≤ 2 * A := by
    rwa [Fintype.card_fin]
  -- level 0: the good candidate, unique (`ud_extract`'s argument)
  simp only [CommitDoomUd, not_forall, not_not, exists_prop] at hC
  obtain ⟨q, hq, hgood⟩ := hC
  have hmem64 : encStack μ R q ∈ iList C₀ A (laneWord μ R W₀) := mem_iList_of_candidate h64 hq
  have hmem : encRows μ R q ∈ iList C₀ A (laneRows μ R W₀) := by
    rw [encRows_eq]; exact comp_mem_iList C₀ (bitsEquiv laneBits) hmem64
  have huniq : ∀ q' ∈ Candidates μ R A W₀, q' = q := fun q' hq' ↦
    encStack_injective hμ h64 (Finset.card_le_one.mp (card_iList_le_one _ hn _) _
      (mem_iList_of_candidate h64 hq') _ hmem64)
  have hfold0 := foldMsg_mem h64 hq α₀
  -- level 1: the member close to the folded root word
  simp only [MidDoomUd, not_forall, not_lt, exists_prop] at hM
  obtain ⟨V, hV, hclose⟩ := hM
  have hone : (iList P₁.code P₁.thr Q').card ≤ 1 := (P₁.card_iList_le Q').trans hL
  have hVuniq : ∀ V' ∈ iList P₁.code P₁.thr Q', V' = V := fun V' hV' ↦
    Finset.card_le_one.mp hone _ hV' _ hV
  -- its level-0 encoding is in the folded root word's list, hence the fold of `q`
  have hrow : (fun _ : Fin 0 → Bool ↦ foldAll α₀ (laneRows μ R W₀) Fin.elim0) =
      foldAll α₀ (laneRows μ R W₀) := by
    funext v; rw [Subsingleton.elim v Fin.elim0]
  have hmemV : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R (joinMsg hκ (decode P₁ V))) ∈
      iList C₀ A (foldAll α₀ (laneRows μ R W₀)) := by
    rw [← hrow, mem_iList]
    refine ⟨fun _ ↦ ?_, _, hclose, fun _ x hx ↦ ((Finset.mem_filter.mp hx).2).symm⟩
    show _ ∈ rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
    rw [← range_enc h64]; exact LinearMap.mem_range_self _ _
  have hjoin : joinMsg hκ (decode P₁ V) = foldMsg α₀ q :=
    enc_injective h64 (congrFun (Finset.card_le_one.mp (card_iList_le_one _ hn _) _ hmemV _ hfold0)
      (Fin.elim0 : Fin 0 → Bool))
  -- the residual is the fold of `V`
  have hVcw : IsInterleavedCodeword P₁.code V := ((mem_iList _ _ _ _).mp hV).1
  have hVenc : V = fun u ↦ enc P₁.κ P₁.R (decode P₁ V u) := funext fun u ↦ (enc_decode P₁ hVcw u).symm
  have hfoldV : foldAll α₁ V ∈ iList P₁.code P₁.thr (foldAll α₁ Q') := foldAll_mem_iList _ α₁ hV
  have hF' : (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R f₂) ∈ iList P₁.code P₁.thr (foldAll α₁ Q') :=
    not_not.mp hF
  have hone' : (iList P₁.code P₁.thr (foldAll α₁ Q')).card ≤ 1 :=
    (P₁.card_iList_le _).trans hL
  have heq1 : (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R f₂) = foldAll α₁ V :=
    Finset.card_le_one.mp hone' _ hF' _ hfoldV
  have hf₂ : f₂ = ∑ u, eqW α₁ u • decode P₁ V u := by
    have h2 : foldAll α₁ V = fun _ ↦ enc P₁.κ P₁.R (∑ u, eqW α₁ u • decode P₁ V u) := by
      conv_lhs => rw [hVenc]
      exact foldAll_enc α₁ _
    rw [h2] at heq1
    exact enc_injective P₁.h64 (congrFun heq1 (Fin.elim0 : Fin 0 → Bool))
  refine ⟨q, hq, hgood, huniq, V, hV, hVuniq, hjoin, hf₂, ?_, fun hluck ↦ ?_, ?_, fun hluck ↦ ?_⟩
  · exact (isClose_iff_le_card_agreeSet _ _ _).mp ((mem_iList _ _ _ _).mp hV).2
  · rw [heq1]
    exact agreeSet_foldAll_eq (not_not.mp hluck)
  · exact (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2
  · rw [← foldAll_encRows]
    exact agreeSet_foldAll_eq (not_not.mp hluck)

/-! ## lvm's `C_rec` -/

/-- **The extractor's facts for `C_rec` at P20** (S4: levels `(6, 2)`, `(4, 3)`; thresholds
`udThr 13 2`, `udThr 9 3`; `2^15` and `2^12` columns; a `2^9`-scalar residual). -/
theorem ud_extract_rec20 (Good : Column 19 → Prop) (W₀ : Word) (α₀ : Fin laneBits → E)
    (Q' : (Fin 4 → Bool) → Fin (codesRec20 1).n → E) (α₁ : Fin 4 → E)
    (f₂ : (Fin (codesRec20 1).κ → Bool) → E)
    (hC : ¬ CommitDoomUd 19 2 (udThr 13 2) Good W₀)
    (hM : ¬ MidDoomUd (udThr 13 2) (codesRec20 1) (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ)
      (foldAll α₀ (laneRows 19 2 W₀) Fin.elim0) Q')
    (hF : ¬ FinalDoomL (codesRec20 1) Q' α₁ f₂) :
    ∃ q ∈ Candidates 19 2 (udThr 13 2) W₀, Good q ∧
      (∀ q' ∈ Candidates 19 2 (udThr 13 2) W₀, q' = q) ∧
      ∃ V ∈ iList (codesRec20 1).code (codesRec20 1).thr Q',
        (∀ V' ∈ iList (codesRec20 1).code (codesRec20 1).thr Q', V' = V) ∧
        joinMsg (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ) (decode (codesRec20 1) V) =
          foldMsg α₀ q ∧
        f₂ = ∑ u, eqW α₁ u • decode (codesRec20 1) V u ∧
        (codesRec20 1).thr ≤ (agreeSet Q' V).card ∧
        (¬ FoldAllLuck α₁ Q' V →
          agreeSet (foldAll α₁ Q') (fun _ ↦ enc (codesRec20 1).κ (codesRec20 1).R f₂) =
            agreeSet Q' V) ∧
        udThr 13 2 ≤ (agreeSet (laneRows 19 2 W₀) (encRows 19 2 q)).card ∧
        (¬ FoldAllLuck α₀ (laneRows 19 2 W₀) (encRows 19 2 q) →
          agreeSet (foldAll α₀ (laneRows 19 2 W₀)) (fun _ ↦ enc (19 - laneBits) 2 (foldMsg α₀ q)) =
            agreeSet (laneRows 19 2 W₀) (encRows 19 2 q)) :=
  ud_extract2 (by norm_num) (by norm_num) (by norm_num [udThr]) (codesRec20 1) rfl le_rfl Good W₀ α₀
    Q' α₁ f₂ hC hM hF

/-- **The extractor's facts for `C_rec` at P8** (S2's P8, μ = 18; S4: levels `(6, 2)`, `(4, 3)`; `κ = 12, 8`). -/
theorem ud_extract_rec18 (Good : Column 18 → Prop) (W₀ : Word) (α₀ : Fin laneBits → E)
    (Q' : (Fin 4 → Bool) → Fin (codesRec18 1).n → E) (α₁ : Fin 4 → E)
    (f₂ : (Fin (codesRec18 1).κ → Bool) → E)
    (hC : ¬ CommitDoomUd 18 2 (udThr 12 2) Good W₀)
    (hM : ¬ MidDoomUd (udThr 12 2) (codesRec18 1) (by rfl : 18 - laneBits = 4 + (codesRec18 1).κ)
      (foldAll α₀ (laneRows 18 2 W₀) Fin.elim0) Q')
    (hF : ¬ FinalDoomL (codesRec18 1) Q' α₁ f₂) :
    ∃ q ∈ Candidates 18 2 (udThr 12 2) W₀, Good q ∧
      (∀ q' ∈ Candidates 18 2 (udThr 12 2) W₀, q' = q) ∧
      ∃ V ∈ iList (codesRec18 1).code (codesRec18 1).thr Q',
        (∀ V' ∈ iList (codesRec18 1).code (codesRec18 1).thr Q', V' = V) ∧
        joinMsg (by rfl : 18 - laneBits = 4 + (codesRec18 1).κ) (decode (codesRec18 1) V) =
          foldMsg α₀ q ∧
        f₂ = ∑ u, eqW α₁ u • decode (codesRec18 1) V u ∧
        (codesRec18 1).thr ≤ (agreeSet Q' V).card ∧
        (¬ FoldAllLuck α₁ Q' V →
          agreeSet (foldAll α₁ Q') (fun _ ↦ enc (codesRec18 1).κ (codesRec18 1).R f₂) =
            agreeSet Q' V) ∧
        udThr 12 2 ≤ (agreeSet (laneRows 18 2 W₀) (encRows 18 2 q)).card ∧
        (¬ FoldAllLuck α₀ (laneRows 18 2 W₀) (encRows 18 2 q) →
          agreeSet (foldAll α₀ (laneRows 18 2 W₀)) (fun _ ↦ enc (18 - laneBits) 2 (foldMsg α₀ q)) =
            agreeSet (laneRows 18 2 W₀) (encRows 18 2 q)) :=
  ud_extract2 (by norm_num) (by norm_num) (by norm_num [udThr]) (codesRec18 1) rfl le_rfl Good W₀ α₀
    Q' α₁ f₂ hC hM hF

/-- The zero level-1 word is in its own list. -/
theorem zero_mem_iList1 {ℓ₁ : ℕ} (P₁ : LevelCode) (hthr : P₁.thr ≤ P₁.n) :
    (0 : (Fin ℓ₁ → Bool) → Fin P₁.n → E) ∈ iList P₁.code P₁.thr 0 := by
  rw [mem_iList]
  refine ⟨fun _ ↦ Submodule.zero_mem _, univ, ?_, fun _ _ _ ↦ rfl⟩
  rw [Finset.card_univ, Fintype.card_fin]
  exact hthr

/-- The zero words are not level-1 doomed. -/
theorem not_midDoomUd_zero {κ₀ R₀ ℓ₁ A : ℕ} (P₁ : LevelCode) (hκ : κ₀ = ℓ₁ + P₁.κ)
    (hthr : P₁.thr ≤ P₁.n) (hA : A ≤ 2 ^ (κ₀ + R₀)) : ¬ MidDoomUd (R₀ := R₀) A P₁ hκ 0 0 := by
  intro hD
  have h := hD 0 (zero_mem_iList1 P₁ hthr)
  have hdec : decode P₁ (0 : (Fin ℓ₁ → Bool) → Fin P₁.n → E) = 0 := by
    have := decode_enc P₁ (fun _ : Fin ℓ₁ → Bool ↦ (0 : (Fin P₁.κ → Bool) → E))
    simp only [map_zero] at this
    exact this
  have hj : joinMsg hκ (0 : (Fin ℓ₁ → Bool) → (Fin P₁.κ → Bool) → E) = 0 := rfl
  rw [hdec, hj, map_zero, Finset.filter_true_of_mem (fun _ _ ↦ rfl), Finset.card_univ,
    Fintype.card_fin] at h
  omega

/-- The zero residual of the zero words is not final-doomed. -/
theorem not_finalDoomL_zero {ℓ₁ : ℕ} (P₁ : LevelCode) (hthr : P₁.thr ≤ P₁.n) (α₁ : Fin ℓ₁ → E) :
    ¬ FinalDoomL P₁ 0 α₁ 0 := by
  intro hD
  apply hD
  have h0 : (fun _ : Fin 0 → Bool ↦ enc P₁.κ P₁.R 0) = foldAll α₁ (0 : (Fin ℓ₁ → Bool) → Fin P₁.n → E) := by
    funext v x
    rw [map_zero, foldAll_eq_sum]
    simp
  rw [h0]
  exact foldAll_mem_iList _ α₁ (zero_mem_iList1 P₁ hthr)

/-- **Non-vacuity of `ud_extract_rec20`**: the all-zero words (root and level 1), with the zero
stack as the good candidate and the zero residual, satisfy all three hypotheses, for every
`α₀`, `α₁` (the honest instance). -/
theorem ud_extract_rec20_nonvacuous (α₀ : Fin laneBits → E) (α₁ : Fin 4 → E) :
    ¬ CommitDoomUd 19 2 (udThr 13 2) (fun q ↦ q = zeroCol 19) zeroWord ∧
      ¬ MidDoomUd (udThr 13 2) (codesRec20 1) (by rfl : 19 - laneBits = 4 + (codesRec20 1).κ)
        (foldAll α₀ (laneRows 19 2 zeroWord) Fin.elim0) 0 ∧
      ¬ FinalDoomL (codesRec20 1) 0 α₁ 0 := by
  obtain ⟨h1, -⟩ := ud_extract_rec20_l0_nonvacuous α₀
  have hrows : laneRows 19 2 zeroWord = 0 := by
    funext u v
    simp [laneRows, laneWord, laneOf, zeroWord, List.getD_eq_getElem?_getD]
  have hC : foldAll α₀ (laneRows 19 2 zeroWord) Fin.elim0 = 0 := by
    funext x
    rw [foldAll_eq_sum, hrows]
    simp
  have hthr : (codesRec20 1).thr ≤ (codesRec20 1).n := by
    show udThr 9 3 ≤ 2 ^ (9 + 3)
    simp only [udThr]; norm_num
  rw [hC]
  exact ⟨h1, not_midDoomUd_zero _ _ hthr (by simp only [udThr, laneBits]; norm_num),
    not_finalDoomL_zero _ hthr α₁⟩

end
end LeanVM.Protocol.Whir.Sound
