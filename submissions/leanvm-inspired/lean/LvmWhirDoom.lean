-- New for lvm (WP-7): the commitment-level doom of a unique-decoding root (lvm's `C_rec`) and the facts the
-- extractor (WP-13) and the certificate (WP-14) consume (BLUEPRINT §6.2 "Correctness", §7.2): not doomed after the
-- commitment and after the final residual `f`, the unique close codeword's message folds to `f`, and off the
-- luck event its agreement set is the one `E` computes. Built on WP-6's `LvmUdMany` (`foldAll`,
-- `agreeSet_foldAll_eq`) and `LvmRS` (`card_iList_le_one`), and leanVM's candidate bridge (`LvmWhirCandidates`).
/-
  LeanVM.Protocol.Whir.Sound (lvm: the extractor's doom facts)

  The doom of a committed level-0 word in the unique-decoding regime, the final residual's doom,
  and the extraction facts: under neither, the word's unique candidate satisfies the relation,
  its blocks fold to the residual, and the agreement set of the folded word with the residual's
  encoding is the word's agreement set with the candidate's encoding (off the luck event).
-/

import LvmWhirSpec
import LvmUdMany

/-!
# The commitment-level doom and the extractor's facts

Setting: a root committed as a level-0 word `W` (`2^(μ−6+R)` leaves of `2^6` `K`-words; lvm's
`C_rec`: `μ = 19`, `R = 2`), the level-0 code `RS[E, D_{μ−6,R}, 2^(μ−6)]` at a threshold `A` in
the unique-decoding range (`2^(μ−6+R) + 2^(μ−6) ≤ 2 A`, e.g. `udThr (μ−6) R`), the opening's
level-0 fold challenges `α ∈ E^6` and the final residual `f` (lvm's `C_rec` has one level, so its
residual is the fold of the root's word).

* `laneRows μ R W`: the root's lanes as rows indexed by six lane bits (`u ↦ laneWord (⟨u⟩)`), the
  word the opening folds (`rowsOf 6 (laneO 0 …)`, `rowsOf_laneO_zero`); `encRows μ R q`: the same
  for the encoding of a stack `q`.
* `CommitDoomUd μ R A Good W`: **the commitment's doom**: no candidate of `W` (a `K`-valued stack
  whose encoding agrees with `W` on `A` columns) satisfies `Good` (WP-14's relation on the decoded
  stack). Its negation is the existence of a good candidate.
* `FinalDoomUd μ R A h64 W α f`: **the final residual's doom**: the encoding of `f` is not in the
  list of the folded word `foldAll α (laneRows μ R W)` (it agrees with it on fewer than `A`
  columns). The WHIR specification's doom at the boundary after the residual, `ResC`, contains
  `FinViol` of the residual, whose negation gives `¬ FinalDoomUd` (`not_finalDoomUd`).
* `foldMsg α q`: the fold `Σ_u eq(α, u) · block_u(q)` of a stack's blocks.
* **`ud_extract`**: `¬ CommitDoomUd ∧ ¬ FinalDoomUd` ⇒ there is exactly one candidate `q`, it is
  good, `f = foldMsg α q`, `A ≤ |agreeSet (laneRows W) (encRows q)|`, and if `α` is not lucky for
  `(laneRows W, encRows q)` then `agreeSet (foldAll α (laneRows W)) (Enc f) =
  agreeSet (laneRows W) (encRows q)`: the set `E` computes from the log and `f` is the joint
  agreement set, on which every one of the 64 rows of `W` is the candidate's encoding
  (BLUEPRINT §6.2 step 5). No "not fold-bad" hypothesis is needed: with a list of at most one
  member, the folded list is the fold of the list (`foldAll_mem_iList`).
* `FoldAllLuck α O U` and `foldAllLuck_cons`: the luck event over `α ∈ E^m` splits into a first
  round's luck (`card_foldLuck_le`: at most `n` challenges) or the rest's: the per-round luck
  predicate of the certificate (`N₀/|E| = 2^-177` per round at P20, `N₀ = 2^15` columns, A13).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Protocol.Whir.Ud Finset

section

/-! ## Folding a list member -/

/-- **The fold of a list member is in the list of the fold**, for `m` challenges. -/
theorem foldAll_mem_iList {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    [DecidableEq ι] (C : Submodule F (ι → F)) {A : ℕ} :
    ∀ {m : ℕ} (α : Fin m → F) {O U : (Fin m → Bool) → ι → F}, U ∈ iList C A O →
      foldAll α U ∈ iList C A (foldAll α O)
  | 0, _, _, _, h => h
  | m + 1, α, O, U, h => by
    have h1 : splitLow U ∈ iList C A (splitLow O) := by
      rw [iList_splitLow]; exact Finset.mem_image_of_mem _ h
    rw [foldAll_succ α O, foldAll_succ α U]
    exact foldAll_mem_iList C (Fin.tail α) (fold_mem_iList C h1 (α 0))

/-- **The fold of row-wise encodings is the encoding of the folded messages** (`enc` linear). -/
theorem foldAll_enc {m κ R : ℕ} (α : Fin m → E) (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    foldAll α (fun u ↦ enc κ R (g u)) = fun _ ↦ enc κ R (∑ u, eqW α u • g u) := by
  funext v x
  rw [foldAll_eq_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]

/-- **The opening's fold rounds are WP-6's `foldAll`**: folding an integer-indexed lane oracle by
the challenges `l` (first challenge, low bit) is `foldAll` of its rows by `l`. -/
theorem rowsOf_foldsN_eq_foldAll {ι : Type*} :
    ∀ (m : ℕ) (l : List E), l.length = m → ∀ (O : ℕ → ι → E),
      rowsOf 0 (foldsN l O) = foldAll (fun i : Fin m ↦ l.getD i 0) (rowsOf m O)
  | 0, l, hl, O => by
    obtain rfl : l = [] := List.eq_nil_of_length_eq_zero hl
    rfl
  | m + 1, l, hl, O => by
    obtain ⟨s, l', rfl⟩ : ∃ s l', l = s :: l' := by
      cases l with
      | nil => simp at hl
      | cons s l' => exact ⟨s, l', rfl⟩
    have hl' : l'.length = m := by simpa using hl
    have h1 : foldsN (s :: l') O = foldsN l' (foldN s O) := rfl
    rw [h1, rowsOf_foldsN_eq_foldAll m l' hl' (foldN s O), rowsOf_foldN, foldAll_succ]
    rfl

/-! ## The level-0 rows -/

/-- The root's lanes as rows indexed by six lane bits. -/
def laneRows (μ R : ℕ) (W : Word) : (Fin laneBits → Bool) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u ↦ laneWord μ R W (bitsEquiv laneBits u)

/-- A stack's lane-wise encoding as rows indexed by six lane bits. -/
noncomputable def encRows (μ R : ℕ) (q : Column μ) :
    (Fin laneBits → Bool) → Fin (2 ^ (μ - laneBits + R)) → E :=
  fun u ↦ enc (μ - laneBits) R (blockOf q (bitsEquiv laneBits u))

/-- The fold of a stack's blocks by `α ∈ E^6`: `Σ_u eq(α, u) · block_u(q)`. -/
noncomputable def foldMsg {μ : ℕ} (α : Fin laneBits → E) (q : Column μ) :
    (Fin (μ - laneBits) → Bool) → E :=
  ∑ u, eqW α u • blockOf q (bitsEquiv laneBits u)

/-! ## The doom predicates -/

/-- **The commitment's doom** (unique decoding): no candidate of the committed word satisfies
`Good`. -/
def CommitDoomUd (μ R A : ℕ) (Good : Column μ → Prop) (W : Word) : Prop :=
  ∀ q ∈ Candidates μ R A W, ¬ Good q

/-- **The final residual's doom**: the encoding of `f` is not in the list of the root's word folded
by `α`. -/
def FinalDoomUd (μ R A : ℕ) (h64 : μ - laneBits + R ≤ 64) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E) : Prop :=
  (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R f) ∉
    iList (rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) A
      (foldAll α (laneRows μ R W))

/-- Luck over `α ∈ E^m`: a column on which `O` and `U` differ agrees after the fold. -/
def FoldAllLuck {ι : Type*} [Fintype ι] {m : ℕ} (α : Fin m → E)
    (O U : (Fin m → Bool) → ι → E) : Prop :=
  ¬ agreeSet (foldAll α O) (foldAll α U) ⊆ agreeSet O U

/-- **The luck event splits by rounds**: lucky for `cons s α` is lucky at the first round or for
`α` after it. -/
theorem foldAllLuck_cons {ι : Type*} [Fintype ι] {m : ℕ} (s : E) (α : Fin m → E)
    (O U : (Fin (m + 1) → Bool) → ι → E)
    (h : FoldAllLuck (Fin.cons s α : Fin (m + 1) → E) O U) :
    ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆
        agreeSet (splitLow O) (splitLow U) ∨
      FoldAllLuck α (fold s (splitLow O)) (fold s (splitLow U)) := by
  simp only [FoldAllLuck] at h ⊢
  by_contra hgood
  push Not at hgood
  apply h
  rw [foldAll_cons, foldAll_cons, ← agreeSet_splitLow]
  exact hgood.2.trans hgood.1

/-! ## The extractor's facts -/

/-- The encoding rows are the candidates' encoding `encStack`, reindexed by the lane bits. -/
theorem encRows_eq {μ R : ℕ} (q : Column μ) :
    encRows μ R q = fun u ↦ encStack μ R q (bitsEquiv laneBits u) := rfl

/-- The fold of the encoding rows is the encoding of the folded blocks. -/
theorem foldAll_encRows {μ R : ℕ} (α : Fin laneBits → E) (q : Column μ) :
    foldAll α (encRows μ R q) = fun _ ↦ enc (μ - laneBits) R (foldMsg α q) :=
  foldAll_enc α _

/-- **The extractor's facts** (BLUEPRINT §6.2, "Correctness"): not doomed at the commitment and
not doomed at the final residual, the committed word has exactly one candidate `q`; it is good;
its blocks fold to the residual; it agrees with the word on at least `A` columns; and off the
luck event the agreement set of the folded word with the residual's encoding is the word's
agreement set with the candidate's encoding. -/
theorem ud_extract {μ R A : ℕ} (hμ : laneBits ≤ μ) (h64 : μ - laneBits + R ≤ 64)
    (hud : 2 ^ (μ - laneBits + R) + 2 ^ (μ - laneBits) ≤ 2 * A)
    (Good : Column μ → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (μ - laneBits) → Bool) → E)
    (hC : ¬ CommitDoomUd μ R A Good W) (hF : ¬ FinalDoomUd μ R A h64 W α f) :
    ∃ q ∈ Candidates μ R A W, Good q ∧ (∀ q' ∈ Candidates μ R A W, q' = q) ∧
      f = foldMsg α q ∧ A ≤ (agreeSet (laneRows μ R W) (encRows μ R q)).card ∧
      (¬ FoldAllLuck α (laneRows μ R W) (encRows μ R q) →
        agreeSet (foldAll α (laneRows μ R W)) (fun _ ↦ enc (μ - laneBits) R f) =
          agreeSet (laneRows μ R W) (encRows μ R q)) := by
  classical
  set C := rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))
  have hn : Fintype.card (Fin (2 ^ (μ - laneBits + R))) + 2 ^ (μ - laneBits) ≤ 2 * A := by
    rwa [Fintype.card_fin]
  -- the good candidate
  simp only [CommitDoomUd, not_forall, not_not, exists_prop] at hC
  obtain ⟨q, hq, hgood⟩ := hC
  have hmem64 : encStack μ R q ∈ iList C A (laneWord μ R W) := mem_iList_of_candidate h64 hq
  have hmem : encRows μ R q ∈ iList C A (laneRows μ R W) := by
    rw [encRows_eq]; exact comp_mem_iList C (bitsEquiv laneBits) hmem64
  -- uniqueness
  have huniq : ∀ q' ∈ Candidates μ R A W, q' = q := fun q' hq' ↦
    encStack_injective hμ h64 (Finset.card_le_one.mp (card_iList_le_one _ hn _) _
      (mem_iList_of_candidate h64 hq') _ hmem64)
  -- the residual's encoding is the fold of the candidate's
  have hF' : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R f) ∈
      iList C A (foldAll α (laneRows μ R W)) := not_not.mp hF
  have hfold : foldAll α (encRows μ R q) ∈ iList C A (foldAll α (laneRows μ R W)) :=
    foldAll_mem_iList C α hmem
  have heq : (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R f) = foldAll α (encRows μ R q) :=
    Finset.card_le_one.mp (card_iList_le_one _ hn _) _ hF' _ hfold
  have hf : f = foldMsg α q := by
    rw [foldAll_encRows] at heq
    exact enc_injective h64 (congrFun heq (Fin.elim0 : Fin 0 → Bool))
  refine ⟨q, hq, hgood, huniq, hf, ?_, fun hluck ↦ ?_⟩
  · exact (isClose_iff_le_card_agreeSet A _ _).mp ((mem_iList _ _ _ _).mp hmem).2
  · rw [heq]
    exact agreeSet_foldAll_eq (not_not.mp hluck)

/-- **The level-0 extractor's facts for `C_rec` at P20** (`μ = 19`, `R = 2`, threshold `udThr 13 2`;
`2^15` columns, `2^13`-scalar level-0 fold). With S4's second level the fold `f` is not sent; it is
the level-1 word's decoded message (`LvmWhirDoom2.ud_extract_rec20`), and `¬ FinalDoomUd` holds for
it (`not_finalDoomUd_foldMsg`). -/
theorem ud_extract_rec20_l0 (Good : Column 19 → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (19 - laneBits) → Bool) → E)
    (hC : ¬ CommitDoomUd 19 2 (udThr 13 2) Good W)
    (hF : ¬ FinalDoomUd 19 2 (udThr 13 2) (by norm_num) W α f) :
    ∃ q ∈ Candidates 19 2 (udThr 13 2) W, Good q ∧
      (∀ q' ∈ Candidates 19 2 (udThr 13 2) W, q' = q) ∧ f = foldMsg α q ∧
      udThr 13 2 ≤ (agreeSet (laneRows 19 2 W) (encRows 19 2 q)).card ∧
      (¬ FoldAllLuck α (laneRows 19 2 W) (encRows 19 2 q) →
        agreeSet (foldAll α (laneRows 19 2 W)) (fun _ ↦ enc (19 - laneBits) 2 f) =
          agreeSet (laneRows 19 2 W) (encRows 19 2 q)) :=
  ud_extract (by norm_num) (by norm_num) (by norm_num [udThr]) Good W α f hC hF

/-- **The level-0 extractor's facts for `C_rec` at P8** (`μ = 17`, `R = 2`, threshold `udThr 11 2`). -/
theorem ud_extract_rec8_l0 (Good : Column 17 → Prop) (W : Word) (α : Fin laneBits → E)
    (f : (Fin (17 - laneBits) → Bool) → E)
    (hC : ¬ CommitDoomUd 17 2 (udThr 11 2) Good W)
    (hF : ¬ FinalDoomUd 17 2 (udThr 11 2) (by norm_num) W α f) :
    ∃ q ∈ Candidates 17 2 (udThr 11 2) W, Good q ∧
      (∀ q' ∈ Candidates 17 2 (udThr 11 2) W, q' = q) ∧ f = foldMsg α q ∧
      udThr 11 2 ≤ (agreeSet (laneRows 17 2 W) (encRows 17 2 q)).card ∧
      (¬ FoldAllLuck α (laneRows 17 2 W) (encRows 17 2 q) →
        agreeSet (foldAll α (laneRows 17 2 W)) (fun _ ↦ enc (17 - laneBits) 2 f) =
          agreeSet (laneRows 17 2 W) (encRows 17 2 q)) :=
  ud_extract (by norm_num) (by norm_num) (by norm_num [udThr]) Good W α f hC hF

/-- The all-zero committed word: `2^6` zero words in every leaf. -/
def zeroWord : Word := fun _ ↦ List.replicate (2 ^ laneBits) 0

/-- The zero stack. -/
def zeroCol (μ : ℕ) : Column μ := ⟨Vector.replicate _ 0⟩

/-- The zero stack's blocks are zero, for a variable height: at `μ = 19` the kernel would
evaluate the `2^19`-word `Vector.replicate` (78 s, 10 GB). -/
private theorem blockOf_zeroCol (μ : ℕ) (u : Fin (2 ^ laneBits)) : blockOf (zeroCol μ) u = 0 := by
  funext x
  simp only [blockOf, zeroCol, Vector.getD, Vector.toArray_replicate, Array.getD_eq_getD_getElem?,
    Array.getElem?_replicate]
  split_ifs <;> simp

/-- **Non-vacuity of `ud_extract_rec20_l0`**: the all-zero root word, with the zero stack as the good
candidate and the zero residual, satisfies both hypotheses (the honest instance), for every `α`. -/
theorem ud_extract_rec20_l0_nonvacuous (α : Fin laneBits → E) :
    ¬ CommitDoomUd 19 2 (udThr 13 2) (fun q ↦ q = zeroCol 19) zeroWord ∧
      ¬ FinalDoomUd 19 2 (udThr 13 2) (by norm_num) zeroWord α 0 := by
  have hA : udThr 13 2 ≤ (univ : Finset (Fin (2 ^ (19 - laneBits + 2)))).card := by
    simp only [card_univ, Fintype.card_fin, udThr, laneBits]; norm_num
  have hlane : ∀ u v, laneOf zeroWord u v = 0 := fun u v ↦ by
    simp [laneOf, zeroWord, List.getD_eq_getElem?_getD]
  have hblock : ∀ u, blockOf (zeroCol 19) u = 0 := blockOf_zeroCol 19
  refine ⟨fun hD ↦ hD (zeroCol 19) ⟨univ, hA, fun v _ u ↦ ?_⟩ rfl, fun hF ↦ hF ?_⟩
  · rw [hlane, hblock, map_zero]; rfl
  · have hrows : laneRows 19 2 zeroWord = 0 := by
      funext u v; simp [laneRows, laneWord, hlane]
    rw [mem_iList]
    refine ⟨fun _ ↦ by rw [map_zero]; exact Submodule.zero_mem _, univ, hA, fun _ x _ ↦ ?_⟩
    rw [foldAll_eq_sum, hrows, map_zero]
    simp

/-! ## From the WHIR specification's doom -/

/-- **The final residual's doom from the specification's.** On the level-0 code of a UD level
(`LevelCode.ud (μ − 6) R`), if the residual `G` does not satisfy `FinViol` against the word folded
by the level's challenges `r.2` (six of them), it satisfies the running claim and is not
final-doomed: `Enc(G)` is in the list of `foldAll α (laneRows W)`, `α = r.2`, `W` the root's word
in the view. -/
theorem not_finalDoomUd {μ R : ℕ} (h64 : μ - laneBits + R ≤ 64) (hκ : 1 ≤ μ - laneBits)
    (hR : 1 ≤ R) (r : WhirStateT × List E) (hlf : r.2.length = laneBits)
    (cs : List (ℕ × ℕ × Word)) (Φ : List E → E) (σ : E)
    (G : (Fin (μ - laneBits) → Bool) → E)
    (h : ¬ FinViol (LevelCode.ud (μ - laneBits) R h64 hκ hR)
      (foldedW 0 (LevelCode.ud (μ - laneBits) R h64 hκ hR) r cs) Φ σ G) :
    ∑ x, Φ (bitsL x) * G x = σ ∧
      ¬ FinalDoomUd μ R (udThr (μ - laneBits) R) h64 (wordOf cs 0)
        (fun i ↦ r.2.getD i 0) G := by
  simp only [FinViol, not_or, not_not] at h
  refine ⟨h.1, fun hD ↦ hD ?_⟩
  obtain ⟨-, hmem⟩ := h
  rw [show (fun _ : Fin 0 → Bool ↦ foldedW 0 (LevelCode.ud (μ - laneBits) R h64 hκ hR) r cs) =
      rowsOf 0 (foldsN r.2 (laneO 0 cs (LevelCode.ud (μ - laneBits) R h64 hκ hR).n)) from
      (rowsOf_zero (foldsN r.2 (laneO 0 cs (LevelCode.ud (μ - laneBits) R h64 hκ hR).n))).symm,
    rowsOf_foldsN_eq_foldAll laneBits r.2 hlf] at hmem
  change (fun _ : Fin 0 → Bool ↦ enc (μ - laneBits) R G) ∈
    iList (rsCode (domain (μ - laneBits) R h64) (2 ^ (μ - laneBits))) (udThr (μ - laneBits) R)
      (foldAll (fun i : Fin laneBits ↦ r.2.getD i 0)
        (rowsOf laneBits (laneO 0 cs (2 ^ (μ - laneBits + R))))) at hmem
  rwa [rowsOf_laneO_zero μ R cs] at hmem

/-- `ResC`'s bookkeeping and the negation of `ResC` give the negation of `FinViol`. -/
theorem not_finViol_of_not_resC {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P : LevelCode} {ℓ pre : ℕ}
    {r : WhirStateT × List E} {res : List E} {cs : List (ℕ × ℕ × Word)}
    (hbook : res.length = 2 ^ (μ - r.1.folds.length) ∧ FinBook μ i P ℓ pre r cs)
    (h : ¬ ResC μ ℓ₀ w i P ℓ pre r res cs) :
    ¬ FinViol P (foldedW i P r cs) (runW w ℓ₀ r.1) r.1.target (resMsg res) :=
  fun hv ↦ h ⟨hbook, hv⟩

/-- **The commitment's doom from the stacked opening's**: not in `StackedPreUd` while the
bookkeeping holds, some candidate of the root satisfies every claim. -/
theorem exists_candidate_of_not_stackedPreUd {cfg : UdConfig} {P₀ : LevelCode}
    {claims : List StackClaim} {cs : List (ℕ × ℕ × Word)} (hc : cfg.c₀ < cfg.n₀)
    (hlen : cs.length = cfg.n₀)
    (hW : ∃ W, cs[cfg.c₀]? = some (P₀.κ + P₀.R, 2 ^ laneBits, W) ∧ WellShaped (2 ^ laneBits) W)
    (h : ¬ StackedPreUd cfg P₀ claims cs) :
    ¬ CommitDoomUd cfg.μ P₀.R P₀.thr (fun q ↦ ∀ c ∈ claims, StackClaim.Holds cfg.μ c q)
      (wordOf cs cfg.c₀) := by
  intro hD
  refine h ⟨hc, hlen, hW, fun q hq ↦ ?_⟩
  have := hD q hq
  simp only [not_forall, exists_prop] at this
  exact this

end
end LeanVM.Protocol.Whir.Sound
