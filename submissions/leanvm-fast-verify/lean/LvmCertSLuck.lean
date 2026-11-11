-- WP-14 (ASM). New for lvm (O9): the certificate's luck predicate, the fold luck of `C_rec`'s
-- opening (WP-6 `card_foldLuck_le`, WP-7 `foldAllLuck_cons`), and its group bound.
import LvmCertSRes

/-!
# The luck of `P_S` (O9)

The extractor's decoder needs, besides the residual, that `C_rec`'s six fold challenges are not
lucky for the unique candidate `q` (`¬ FoldAllLuck α (laneRows W) (encRows q)`, WP-13b
`decodeRec_of_ud_ws`). Luck is read on the history:

* `afterMid mid x h`: the roots' events and the events after the middle phases returned (if they
  have); `foldChal mid x h`: the samples after the middle phases, without the first (`C_rec`'s
  batching challenge), at most six (`C_rec`'s fold challenges, once drawn); `WrOf h`: `C_rec`'s
  committed word (the roots' second commitment).
* `RoundsLuck m α O U`: some round `j < |α|` is lucky (the agreement set of the rows folded by
  `α_j` is not inside the unfolded one), the rounds' rows being `O`, `U` folded by `α_0 … α_{j-1}`.
  `FoldAllLuck` of six challenges gives `RoundsLuck` of them (`roundsLuck_of_foldAllLuck`).
* **`LuckB mid x h`**: some candidate `q` of `WrOf h` has `RoundsLuck 6 (foldChal mid x h)
  (laneRows 19 2 W) (encRows 19 2 q)`.
* **`esc_luck_le`**: from a history that is not lucky, a group becomes lucky with probability at
  most `(6 − |foldChal|) · 2^15/|E|` (one new fold challenge per group at most, `C_rec`'s candidate
  unique, WP-6's `card_foldLuck_le` per round); hence `≤ 2^-130` (`esc_luck_le_εB`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
open scoped ENNReal

/-! ## Reading the fold challenges off a history -/

/-- The challenge of a sample event. -/
def sampleOf : Ev → Option E
  | .sample c => some c
  | _ => none

/-- The roots' program. -/
abbrev rootsProg : VerifierProgram Unit := commitRootUd cfgMain20 >>= fun _ ↦ commitRootUd cfgRec20

/-- The roots' events, and the events after the middle phases returned. -/
def afterMid (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    Option (List Ev × List Ev) :=
  match rootsProg.retSplit h with
  | none => none
  | some (_, l₁, l₂) => match (mid x).retSplit l₂ with
    | none => none
    | some (_, _, l₃) => some (l₁, l₃)

/-- **The fold challenges drawn so far** (the samples after the middle phases, without `C_rec`'s
batching challenge, at most six). -/
def foldChal (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    List E :=
  match afterMid mid x h with
  | none => []
  | some (_, l₃) => ((l₃.filterMap sampleOf).drop 1).take 6

/-- The roots' events of a history (empty before the roots). -/
def rootsOf (h : List Ev) : List Ev :=
  match rootsProg.retSplit h with
  | none => []
  | some (_, l₁, _) => l₁

/-- `C_rec`'s committed word. -/
def WrOf (h : List Ev) : Word := wordOf (commits (rootsOf h)) 1

section Snoc

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

theorem retSplit_snoc_cases {α : Type} (p : VerifierProgram α) (h : List Ev) (e : Ev) :
    (∀ a l₁ l₂, p.retSplit h = some (a, l₁, l₂) → p.retSplit (h ++ [e]) = some (a, l₁, l₂ ++ [e])) ∧
      (p.retSplit h = none → ∀ a l₁ l₂, p.retSplit (h ++ [e]) = some (a, l₁, l₂) → l₂ = []) :=
  ⟨fun _ _ _ hs ↦ retSplit_append [e] hs, fun hs _ _ _ hs' ↦ (retSplit_concat hs hs').2⟩

theorem afterMid_snoc (h : List Ev) (e : Ev) :
    (∀ l₁ l₃, afterMid mid x h = some (l₁, l₃) → afterMid mid x (h ++ [e]) = some (l₁, l₃ ++ [e])) ∧
      (afterMid mid x h = none → ∀ l₁ l₃, afterMid mid x (h ++ [e]) = some (l₁, l₃) → l₃ = []) := by
  constructor
  · intro l₁ l₃ hm
    unfold afterMid at hm ⊢
    rcases hr : rootsProg.retSplit h with _ | ⟨a, m₁, m₂⟩ <;> rw [hr] at hm
    · cases hm
    · rw [(retSplit_snoc_cases _ h e).1 a m₁ m₂ hr]
      simp only at hm ⊢
      rcases hmid : (mid x).retSplit m₂ with _ | ⟨b, n₁, n₂⟩ <;> rw [hmid] at hm
      · cases hm
      · simp only [Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        rw [(retSplit_snoc_cases _ m₂ e).1 b n₁ n₂ hmid]
  · intro hm l₁ l₃ hm'
    unfold afterMid at hm hm'
    rcases hr : rootsProg.retSplit h with _ | ⟨a, m₁, m₂⟩ <;> rw [hr] at hm
    · rcases hr' : rootsProg.retSplit (h ++ [e]) with _ | ⟨a', m₁', m₂'⟩ <;> rw [hr'] at hm'
      · cases hm'
      · have := (retSplit_snoc_cases _ h e).2 hr a' m₁' m₂' hr'
        subst this
        simp only at hm'
        rcases hmid : (mid x).retSplit [] with _ | ⟨b, n₁, n₂⟩ <;> rw [hmid] at hm'
        · cases hm'
        · simp only [Option.some.injEq, Prod.mk.injEq] at hm'
          obtain ⟨rfl, rfl⟩ := hm'
          have h0 := (retSplit_eq_some_iff.1 hmid).1
          rw [eq_comm, List.append_eq_nil_iff] at h0
          exact h0.2
    · rw [(retSplit_snoc_cases _ h e).1 a m₁ m₂ hr] at hm'
      simp only at hm hm'
      rcases hmid : (mid x).retSplit m₂ with _ | ⟨b, n₁, n₂⟩ <;> rw [hmid] at hm
      · rcases hmid' : (mid x).retSplit (m₂ ++ [e]) with _ | ⟨b', n₁', n₂'⟩ <;> rw [hmid'] at hm'
        · cases hm'
        · simp only [Option.some.injEq, Prod.mk.injEq] at hm'
          obtain ⟨rfl, rfl⟩ := hm'
          exact (retSplit_snoc_cases _ m₂ e).2 hmid b' n₁' n₂' hmid'
      · cases hm

theorem rootsOf_snoc {h : List Ev} {l₁ l₃ : List Ev} (hm : afterMid mid x h = some (l₁, l₃))
    (e : Ev) : rootsOf (h ++ [e]) = rootsOf h := by
  unfold afterMid at hm
  unfold rootsOf
  rcases hr : rootsProg.retSplit h with _ | ⟨a, m₁, m₂⟩ <;> rw [hr] at hm
  · cases hm
  · rw [(retSplit_snoc_cases _ h e).1 a m₁ m₂ hr]

/-- The fold challenges do not change at an event that is not a challenge. -/
theorem foldChal_snoc_of_ne (h : List Ev) (e : Ev) (he : sampleOf e = none) :
    foldChal mid x (h ++ [e]) = foldChal mid x h := by
  unfold foldChal
  rcases hm : afterMid mid x h with _ | ⟨l₁, l₃⟩
  · rcases hm' : afterMid mid x (h ++ [e]) with _ | ⟨l₁', l₃'⟩
    · rfl
    · rw [(afterMid_snoc h e).2 hm l₁' l₃' hm']; rfl
  · rw [(afterMid_snoc h e).1 l₁ l₃ hm]
    simp [List.filterMap_append, he]

/-- The fold challenges grow at the next challenge. -/
def Grows (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  ∃ l₁ l₃, afterMid mid x h = some (l₁, l₃) ∧ l₃.filterMap sampleOf ≠ [] ∧
    (l₃.filterMap sampleOf).length < 7

open Classical in
theorem foldChal_snoc_sample (h : List Ev) (c : E) :
    foldChal mid x (h ++ [Ev.sample c]) =
      if Grows mid x h then foldChal mid x h ++ [c] else foldChal mid x h := by
  classical
  unfold foldChal
  rcases hm : afterMid mid x h with _ | ⟨l₁, l₃⟩
  · have hg : ¬ Grows mid x h := by rintro ⟨_, _, h', -⟩; rw [hm] at h'; cases h'
    rw [if_neg hg]
    rcases hm' : afterMid mid x (h ++ [Ev.sample c]) with _ | ⟨l₁', l₃'⟩
    · rfl
    · rw [(afterMid_snoc h _).2 hm l₁' l₃' hm']; rfl
  · rw [(afterMid_snoc h _).1 l₁ l₃ hm]
    dsimp only
    rw [List.filterMap_append, show [Ev.sample c].filterMap sampleOf = [c] from rfl]
    set S := l₃.filterMap sampleOf
    by_cases hS : S = []
    · have hg : ¬ Grows mid x h := by
        rintro ⟨_, _, h', h2, -⟩; rw [hm] at h'; cases h'; exact h2 hS
      rw [if_neg hg, hS]; rfl
    · by_cases hl : S.length < 7
      · have hg : Grows mid x h := ⟨l₁, l₃, hm, hS, hl⟩
        rw [if_pos hg, List.drop_append_of_le_length (by
          rcases S with _ | ⟨a, t⟩
          · exact absurd rfl hS
          · simp)]
        rw [List.take_of_length_le (by simp; omega),
          List.take_of_length_le (l := S.drop 1) (by simp; omega)]
      · have hg : ¬ Grows mid x h := by
          rintro ⟨_, _, h', -, h3⟩; rw [hm] at h'; cases h'; exact hl h3
        rw [if_neg hg, List.drop_append_of_le_length (by
          rcases S with _ | ⟨a, t⟩
          · exact absurd rfl hS
          · simp), List.take_append_of_le_length (by simp; omega)]

theorem length_foldChal_of_grows {h : List Ev} (hg : Grows mid x h) :
    (foldChal mid x h).length < 6 := by
  obtain ⟨l₁, l₃, hm, -, hl⟩ := hg
  unfold foldChal
  rw [hm]
  simp only [List.length_take, List.length_drop]
  omega

theorem afterMid_of_foldChal_ne {h : List Ev} (hne : foldChal mid x h ≠ []) :
    ∃ l₁ l₃, afterMid mid x h = some (l₁, l₃) := by
  unfold foldChal at hne
  rcases hm : afterMid mid x h with _ | ⟨l₁, l₃⟩
  · rw [hm] at hne; exact absurd rfl hne
  · exact ⟨l₁, l₃, rfl⟩

theorem afterMid_of_grows {h : List Ev} (hg : Grows mid x h) : ∃ l₁ l₃, afterMid mid x h = some (l₁, l₃) := by
  obtain ⟨l₁, l₃, hm, -⟩ := hg
  exact ⟨l₁, l₃, hm⟩

end Snoc

/-! ## Luck by rounds -/

section Rounds

variable {ι : Type} [Fintype ι]

/-- **Luck by rounds**: some round `j < |α|` is lucky, on the rows folded by the earlier rounds. -/
def RoundsLuck : (m : ℕ) → List E → ((Fin m → Bool) → ι → E) → ((Fin m → Bool) → ι → E) → Prop
  | 0, _, _, _ => False
  | _ + 1, [], _, _ => False
  | _ + 1, s :: α, O, U =>
    ¬ agreeSet (fold s (splitLow O)) (fold s (splitLow U)) ⊆ agreeSet (splitLow O) (splitLow U) ∨
      RoundsLuck _ α (fold s (splitLow O)) (fold s (splitLow U))

theorem roundsLuck_nil : ∀ (m : ℕ) (O U : (Fin m → Bool) → ι → E), ¬ RoundsLuck m [] O U
  | 0, _, _ => id
  | _ + 1, _, _ => id

/-- **Luck of all folds gives luck by rounds** (WP-7 `foldAllLuck_cons`). -/
theorem roundsLuck_of_foldAllLuck :
    ∀ (m : ℕ) (α : List E) (O U : (Fin m → Bool) → ι → E), α.length = m →
      FoldAllLuck (fun i : Fin m ↦ α.getD i 0) O U → RoundsLuck m α O U
  | 0, _, O, U, _, h => h (by rw [foldAll_zero, foldAll_zero])
  | m + 1, [], _, _, hl, _ => absurd hl (by simp)
  | m + 1, s :: α, O, U, hl, h => by
    have he : (fun i : Fin (m + 1) ↦ (s :: α).getD i 0) =
        (Fin.cons s (fun i : Fin m ↦ α.getD i 0) : Fin (m + 1) → E) := by
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
      · simp
    rw [he] at h
    rcases foldAllLuck_cons s _ O U h with h1 | h2
    · exact .inl h1
    · exact .inr (roundsLuck_of_foldAllLuck m α _ _ (by simpa using hl) h2)

open Classical in
/-- **A new round is lucky at at most `|ι|` challenges** (WP-6 `card_foldLuck_le`). -/
theorem card_roundsLuck_snoc :
    ∀ (m : ℕ) (α : List E) (O U : (Fin m → Bool) → ι → E), α.length < m →
      ¬ RoundsLuck m α O U →
      (Finset.univ.filter fun c ↦ RoundsLuck m (α ++ [c]) O U).card ≤ Fintype.card ι
  | 0, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | m + 1, [], O, U, _, _ => by
    refine le_trans (Finset.card_le_card fun c hc ↦ ?_) (card_foldLuck_le (splitLow O) (splitLow U))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.nil_append, RoundsLuck] at hc ⊢
    exact hc.resolve_right (roundsLuck_nil m _ _)
  | m + 1, s :: α, O, U, hl, hn => by
    simp only [RoundsLuck, not_or] at hn
    refine le_trans (Finset.card_le_card fun c hc ↦ ?_)
      (card_roundsLuck_snoc m α _ _ (by simpa using hl) hn.2)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.cons_append, RoundsLuck] at hc ⊢
    exact hc.resolve_left hn.1

end Rounds

/-! ## The luck predicate -/

/-- **The luck of `P_S`**: some candidate of `C_rec`'s word is lucky in the fold rounds drawn. -/
def LuckB (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  ∃ q ∈ Candidates 19 2 thrRec (WrOf h),
    RoundsLuck LeanVM.Protocol.EndToEnd.laneBits (foldChal mid x h) (laneRows 19 2 (WrOf h)) (encRows 19 2 q)

section Luck

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

theorem not_luckB_of_foldChal_nil {h : List Ev} (hn : foldChal mid x h = []) : ¬ LuckB mid x h := by
  rintro ⟨q, -, hq⟩
  rw [hn] at hq
  exact roundsLuck_nil _ _ _ hq

/-- Luck does not change where the fold challenges and `C_rec`'s word do not. -/
theorem luckB_snoc_iff {h : List Ev} {e : Ev} (hf : foldChal mid x (h ++ [e]) = foldChal mid x h) :
    LuckB mid x (h ++ [e]) ↔ LuckB mid x h := by
  by_cases hn : foldChal mid x h = []
  · exact ⟨fun h' ↦ absurd h' (not_luckB_of_foldChal_nil (hf.trans hn)),
      fun h' ↦ absurd h' (not_luckB_of_foldChal_nil hn)⟩
  · obtain ⟨l₁, l₃, hm⟩ := afterMid_of_foldChal_ne hn
    unfold LuckB WrOf
    rw [rootsOf_snoc hm e, hf]

/-- **A prover move or an opening keeps luck out.** -/
theorem not_luckB_snoc {h : List Ev} {e : Ev} (he : sampleOf e = none) (hB : ¬ LuckB mid x h) :
    ¬ LuckB mid x (h ++ [e]) :=
  fun h' ↦ hB ((luckB_snoc_iff (foldChal_snoc_of_ne h e he)).1 h')

theorem LuckB_nil : ¬ LuckB mid x [] := by
  apply not_luckB_of_foldChal_nil
  unfold foldChal afterMid
  have : rootsProg.retSplit [] = none := by
    simp [rootsProg, commitRootUd, cfgMain20, VerifierProgram.readCommitment, VerifierProgram.bind,
      retSplit]
  rw [this]

/-- Candidates are at most one in the unique-decoding regime (WP-7 `ud_extract`'s argument). -/
theorem cands_unique {μ R A : ℕ} (hμ : LeanVM.Protocol.EndToEnd.laneBits ≤ μ)
    (h64 : μ - LeanVM.Protocol.EndToEnd.laneBits + R ≤ 64)
    (hud : 2 ^ (μ - LeanVM.Protocol.EndToEnd.laneBits + R) + 2 ^ (μ - LeanVM.Protocol.EndToEnd.laneBits) ≤ 2 * A)
    (W : Word) {q q' : Column μ} (hq : q ∈ Candidates μ R A W) (hq' : q' ∈ Candidates μ R A W) :
    q = q' := by
  have hn : Fintype.card (Fin (2 ^ (μ - LeanVM.Protocol.EndToEnd.laneBits + R))) +
      2 ^ (μ - LeanVM.Protocol.EndToEnd.laneBits) ≤ 2 * A := by rwa [Fintype.card_fin]
  exact encStack_injective hμ h64 (Finset.card_le_one.mp (card_iList_le_one _ hn _) _
    (mem_iList_of_candidate h64 hq) _ (mem_iList_of_candidate h64 hq'))

/-- `C_rec`'s candidates are at most one (unique decoding). -/
theorem cands_rec_unique (W : Word) {q q' : Column 19} (hq : q ∈ Candidates 19 2 thrRec W)
    (hq' : q' ∈ Candidates 19 2 thrRec W) : q = q' :=
  cands_unique (by norm_num) (by norm_num) (by rw [thrRec_eq]; norm_num [udThr]) W hq hq'

/-- `C_main`'s candidates are at most one (unique decoding). -/
theorem cands_main_unique (W : Word) {q q' : Column 26} (hq : q ∈ Candidates 26 1 thrMain W)
    (hq' : q' ∈ Candidates 26 1 thrMain W) : q = q' :=
  cands_unique (by norm_num) (by norm_num) (by norm_num [thrMain, codesMain20, LevelCode.ud, udThr])
    W hq hq'

/-- **The candidate pairs are at most one** (review fact; `kgSpec`'s `L₀ = 1`). -/
theorem candPairs_ncard_le_one (h : List Ev) : (candPairs h).ncard ≤ 1 := by
  have hs : (candPairs h).Subsingleton := fun p hp p' hp' ↦
    Prod.ext (cands_main_unique _ hp.1 hp'.1) (cands_rec_unique _ hp.2 hp'.2)
  rw [Set.ncard_def]
  have := Set.encard_le_one_iff_subsingleton.2 hs
  exact ENat.toNat_le_of_le_coe this

/-- The per-round luck bound, `2^15 / |E|`. -/
noncomputable def δL : ℝ≥0∞ := (2 ^ 15 : ℝ≥0∞) / Fintype.card E

theorem esc_le_one (D : List Ev → Prop) : ∀ (p : VerifierProgram Bool) (h : List Ev), esc D h p ≤ 1
  | .ret true, h => by classical simp only [esc]; split_ifs <;> simp
  | .ret false, _ => by simp [esc]
  | .fail, _ => by simp [esc]
  | .read k, h => by classical simp only [esc]; split_ifs <;> simp
  | .grind b k, h => by classical simp only [esc]; split_ifs <;> simp
  | .commit ht w k, h => by classical simp only [esc]; split_ifs <;> simp
  | .sample k, h => by
    simp only [esc]
    exact avg_le_one _ fun c ↦ esc_le_one D (k c) _
  | .query i ps k, h => by
    simp only [esc]
    split
    · exact esc_le_one D _ _
    · exact zero_le_one

open Classical in
/-- **The luck's group bound**: from a history that is not lucky, the next group becomes lucky
with probability at most `(6 − |foldChal|) · 2^15/|E|`. -/
theorem esc_luck_le : ∀ (p : VerifierProgram Bool) (h : List Ev), ¬ LuckB mid x h →
    esc (fun h' ↦ ¬ LuckB mid x h') h p ≤ ((6 - (foldChal mid x h).length : ℕ) : ℝ≥0∞) * δL
  | .ret true, h, hB => by simp [esc, hB]
  | .ret false, _, _ => by simp [esc]
  | .fail, _, _ => by simp [esc]
  | .read k, h, hB => by simp [esc, hB]
  | .grind b k, h, hB => by simp [esc, hB]
  | .commit ht w k, h, hB => by simp [esc, hB]
  | .query i ps k, h, hB => by
    simp only [esc]
    split
    · rename_i rows _
      have hf := foldChal_snoc_of_ne (mid := mid) (x := x) h (Ev.query rows) rfl
      rw [← hf]
      exact esc_luck_le _ _ (not_luckB_snoc rfl hB)
    · exact zero_le
  | .sample k, h, hB => by
    simp only [esc]
    by_cases hg : Grows mid x h
    · have hlt := length_foldChal_of_grows hg
      obtain ⟨l₁, l₃, hm⟩ := afterMid_of_grows hg
      set n := (foldChal mid x h).length
      set bad := Finset.univ.filter fun c : E ↦ LuckB mid x (h ++ [Ev.sample c])
      have hbad : bad.card ≤ 2 ^ 15 := by
        by_cases hc : ∃ q, q ∈ Candidates 19 2 thrRec (WrOf h)
        · obtain ⟨q, hq⟩ := hc
          have hnq : ¬ RoundsLuck LeanVM.Protocol.EndToEnd.laneBits (foldChal mid x h) (laneRows 19 2 (WrOf h))
              (encRows 19 2 q) := fun h' ↦ hB ⟨q, hq, h'⟩
          refine le_trans (Finset.card_le_card fun c hc ↦ ?_)
            ((card_roundsLuck_snoc LeanVM.Protocol.EndToEnd.laneBits _ _ _ hlt hnq).trans (by norm_num))
          simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
          obtain ⟨q', hq', hl⟩ := hc
          unfold WrOf at hq' hl
          rw [rootsOf_snoc hm, foldChal_snoc_sample, if_pos hg] at hl
          rw [rootsOf_snoc hm] at hq'
          rwa [cands_rec_unique _ hq' hq] at hl
        · push Not at hc
          refine le_trans (Finset.card_le_card (t := ∅) fun c hc' ↦ ?_) (by simp)
          simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
          obtain ⟨q', hq', -⟩ := hc'
          unfold WrOf at hq'
          rw [rootsOf_snoc hm] at hq'
          exact absurd hq' (hc q')
      have hstep : ∀ c, esc (fun h' ↦ ¬ LuckB mid x h') (h ++ [Ev.sample c]) (k c) ≤
          (if c ∈ bad then 1 else 0) + ((5 - n : ℕ) : ℝ≥0∞) * δL := by
        intro c
        by_cases hc : c ∈ bad
        · rw [if_pos hc]; exact (esc_le_one _ _ _).trans le_self_add
        · rw [if_neg hc, zero_add]
          have hB' : ¬ LuckB mid x (h ++ [Ev.sample c]) := by simpa [bad] using hc
          have := esc_luck_le (k c) _ hB'
          rwa [foldChal_snoc_sample, if_pos hg, List.length_append, List.length_singleton,
            show 6 - (n + 1) = 5 - n by omega] at this
      calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c, esc (fun h' ↦ ¬ LuckB mid x h') (h ++ [Ev.sample c]) (k c)
          ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, ((if c ∈ bad then 1 else 0) + ((5 - n : ℕ) : ℝ≥0∞) * δL) := by
            gcongr with c; exact hstep c
        _ = (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card + ((5 - n : ℕ) : ℝ≥0∞) * δL := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add,
              ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul, Finset.sum_ite_mem,
              Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ δL + ((5 - n : ℕ) : ℝ≥0∞) * δL := by
            gcongr
            rw [δL, ENNReal.div_eq_inv_mul]
            gcongr
            exact_mod_cast hbad
        _ = ((6 - n : ℕ) : ℝ≥0∞) * δL := by
            rw [show 6 - n = (5 - n) + 1 by omega, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
              add_comm]
    · have hf : ∀ c, foldChal mid x (h ++ [Ev.sample c]) = foldChal mid x h := fun c ↦ by
        rw [foldChal_snoc_sample, if_neg hg]
      calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c, esc (fun h' ↦ ¬ LuckB mid x h') (h ++ [Ev.sample c]) (k c)
          ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ _c : E, ((6 - (foldChal mid x h).length : ℕ) : ℝ≥0∞) * δL := by
            gcongr with c
            have hB' : ¬ LuckB mid x (h ++ [Ev.sample c]) :=
              fun h' ↦ hB ((luckB_snoc_iff (hf c)).1 h')
            have := esc_luck_le (k c) _ hB'
            rwa [hf c] at this
        _ = _ := Spec.avg_const _

/-- The luck bound: `6 · 2^15 / |E| ≤ 2^-130`. -/
theorem six_δL_le : (6 : ℝ≥0∞) * δL ≤ (2 : ℝ≥0∞)⁻¹ ^ 130 := by
  rw [δL, card_E_ennreal, ← mul_div_assoc, ← two_pow_cast 192,
    show (6 : ℝ≥0∞) * 2 ^ 15 = ((6 * 2 ^ 15 : ℕ) : ℝ≥0∞) by push_cast; ring]
  exact natCast_div_le_inv_pow (by positivity) (by norm_num)

end Luck

end Lvm.ASM
