-- WP-14 (ASM). New for lvm (O9): the certificate's luck predicate, the fold luck of `C_rec`'s
-- opening (WP-6 `card_foldLuck_le`, WP-7 `foldAllLuck_cons`), and its group bound.
import LvmCertSRes
import LvmWhirDoom2

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
* `LuckB0 mid x h`: some candidate `q` of `WrOf h` has `RoundsLuck 6 (foldChal mid x h)
  (laneRows 19 2 W) (encRows 19 2 q)`.
* lvm2 S4, level 1: `rec1Of` (the first commitment after the middle phases: `C_rec`'s level-1
  oracle, and the events after it), `foldChal1` (the samples after it, minus the level-0 query
  group's 24 positions and `λ`, at most four), `W1L` (its word); `LuckB1`: some member `V` of the
  level-1 list of `rows1 W1L` has `RoundsLuck 4 foldChal1 (rows1 W1L) V`.
* **`LuckB = LuckB0 ∨ LuckB1`**; **`esc_luck_le`**: from a history that is not lucky, a group
  becomes lucky with probability at most `((6 − |foldChal|) + (4 − |foldChal1|)) · 2^15/|E|` (WP-6's
  `card_foldLuck_le` per round, unique candidate and unique level-1 member); hence `≤ 2^-132`
  (`ten_δL_le`).
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
abbrev rootsProg : VerifierProgram Unit := commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G

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

/-- **The level-0 luck of `P_S`**: some candidate of `C_rec`'s root word is lucky in the level-0
fold rounds drawn. -/
def LuckB0 (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  ∃ q ∈ Candidates 19 2 thrRec (WrOf h),
    RoundsLuck LeanVM.Protocol.EndToEnd.laneBits (foldChal mid x h) (laneRows 19 2 (WrOf h)) (encRows 19 2 q)

section Luck

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

theorem not_luckB0_of_foldChal_nil {h : List Ev} (hn : foldChal mid x h = []) : ¬ LuckB0 mid x h := by
  rintro ⟨q, -, hq⟩
  rw [hn] at hq
  exact roundsLuck_nil _ _ _ hq

/-- Luck does not change where the fold challenges and `C_rec`'s word do not. -/
theorem luckB0_snoc_iff {h : List Ev} {e : Ev} (hf : foldChal mid x (h ++ [e]) = foldChal mid x h) :
    LuckB0 mid x (h ++ [e]) ↔ LuckB0 mid x h := by
  by_cases hn : foldChal mid x h = []
  · exact ⟨fun h' ↦ absurd h' (not_luckB0_of_foldChal_nil (hf.trans hn)),
      fun h' ↦ absurd h' (not_luckB0_of_foldChal_nil hn)⟩
  · obtain ⟨l₁, l₃, hm⟩ := afterMid_of_foldChal_ne hn
    unfold LuckB0 WrOf
    rw [rootsOf_snoc hm e, hf]

/-- **A prover move or an opening keeps luck out.** -/
theorem not_luckB0_snoc {h : List Ev} {e : Ev} (he : sampleOf e = none) (hB : ¬ LuckB0 mid x h) :
    ¬ LuckB0 mid x (h ++ [e]) :=
  fun h' ↦ hB ((luckB0_snoc_iff (foldChal_snoc_of_ne h e he)).1 h')

theorem LuckB0_nil : ¬ LuckB0 mid x [] := by
  apply not_luckB0_of_foldChal_nil
  unfold foldChal afterMid
  have : rootsProg.retSplit [] = none := by
    simp [rootsProg, commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.bind,
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

/-- **The candidate pairs are at most `98`** (lvm2 JB-VQP, J1: `C_main`'s root at the Johnson threshold
has at most `98` candidates, `candidates_main24J_ncard_le`; `C_rec`'s is unique; `kgSpec`'s
`L₀ = 98`). -/
theorem candPairs_ncard_le (h : List Ev) : (candPairs h).ncard ≤ 98 := by
  refine (Set.ncard_le_ncard_of_injOn Prod.fst (fun p hp ↦ hp.1) (fun p hp p' hp' he ↦
    Prod.ext he (cands_rec_unique _ hp.2 hp'.2)) (Set.toFinite _)).trans ?_
  exact candidates_main24J_ncard_le _

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

/-! ## The level-1 luck (lvm2, S4) -/

/-- The first commitment of a list of events: its word and the events after it. -/
def splitCommit : List Ev → Option (Word × List Ev)
  | [] => none
  | Ev.commit _ _ W :: rest => some (W, rest)
  | _ :: rest => splitCommit rest

theorem splitCommit_snoc (l : List Ev) (e : Ev) :
    (∀ W b, splitCommit l = some (W, b) → splitCommit (l ++ [e]) = some (W, b ++ [e])) ∧
      (splitCommit l = none → ∀ W b, splitCommit (l ++ [e]) = some (W, b) → b = []) := by
  induction l with
  | nil =>
    refine ⟨fun W b h ↦ by simp [splitCommit] at h, fun _ W b h ↦ ?_⟩
    cases e <;> simp [splitCommit] at h
    first | exact h.2 | exact h.2.symm
  | cons e' l ih =>
    cases e' with
    | commit ht w W' =>
      refine ⟨fun W b h ↦ ?_, fun h ↦ by simp [splitCommit] at h⟩
      simp only [splitCommit, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | _ => simpa [splitCommit] using ih

/-- **`C_rec`'s level-1 oracle as the luck reads it**: the first commitment after the middle phases,
and the events after it. -/
def rec1Of (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    Option (Word × List Ev) :=
  match afterMid mid x h with
  | none => none
  | some (_, l₃) => splitCommit l₃

theorem rec1Of_snoc (h : List Ev) (e : Ev) :
    (∀ W b, rec1Of mid x h = some (W, b) → rec1Of mid x (h ++ [e]) = some (W, b ++ [e])) ∧
      (rec1Of mid x h = none → ∀ W b, rec1Of mid x (h ++ [e]) = some (W, b) → b = []) := by
  constructor
  · intro W b hr
    unfold rec1Of at hr ⊢
    rcases hm : afterMid mid x h with _ | ⟨l₁, l₃⟩ <;> rw [hm] at hr
    · cases hr
    · rw [(afterMid_snoc h e).1 l₁ l₃ hm]
      exact (splitCommit_snoc l₃ e).1 W b hr
  · intro hr W b hr'
    unfold rec1Of at hr hr'
    rcases hm : afterMid mid x h with _ | ⟨l₁, l₃⟩ <;> rw [hm] at hr
    · rcases hm' : afterMid mid x (h ++ [e]) with _ | ⟨l₁', l₃'⟩ <;> rw [hm'] at hr'
      · cases hr'
      · rw [(afterMid_snoc h e).2 hm l₁' l₃' hm'] at hr'
        simp [splitCommit] at hr'
    · rw [(afterMid_snoc h e).1 l₁ l₃ hm] at hr'
      exact (splitCommit_snoc l₃ e).2 hr W b hr'

/-- **The level-1 fold challenges drawn so far**: the samples after `C_rec`'s level-1 commitment,
without the level-0 query group's `24` position challenges and its `λ`, at most four. -/
def foldChal1 (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    List E :=
  match rec1Of mid x h with
  | none => []
  | some (_, b) => ((b.filterMap sampleOf).drop 25).take 4

/-- **`C_rec`'s level-1 word as the luck reads it** (the empty word before it is committed). -/
def W1L (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Word :=
  match rec1Of mid x h with
  | none => fun _ ↦ []
  | some (W, _) => W

theorem foldChal1_snoc_of_ne (h : List Ev) (e : Ev) (he : sampleOf e = none) :
    foldChal1 mid x (h ++ [e]) = foldChal1 mid x h := by
  unfold foldChal1
  rcases hr : rec1Of mid x h with _ | ⟨W, b⟩
  · rcases hr' : rec1Of mid x (h ++ [e]) with _ | ⟨W', b'⟩
    · rfl
    · rw [(rec1Of_snoc h e).2 hr W' b' hr']; rfl
  · rw [(rec1Of_snoc h e).1 W b hr]
    simp [List.filterMap_append, he]

/-- The level-1 fold challenges grow at the next challenge. -/
def Grows1 (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  ∃ W b, rec1Of mid x h = some (W, b) ∧ 25 ≤ (b.filterMap sampleOf).length ∧
    (b.filterMap sampleOf).length < 29

open Classical in
theorem foldChal1_snoc_sample (h : List Ev) (c : E) :
    foldChal1 mid x (h ++ [Ev.sample c]) =
      if Grows1 mid x h then foldChal1 mid x h ++ [c] else foldChal1 mid x h := by
  unfold foldChal1
  rcases hr : rec1Of mid x h with _ | ⟨W, b⟩
  · have hg : ¬ Grows1 mid x h := by rintro ⟨_, _, h', -⟩; rw [hr] at h'; cases h'
    rw [if_neg hg]
    rcases hr' : rec1Of mid x (h ++ [Ev.sample c]) with _ | ⟨W', b'⟩
    · rfl
    · rw [(rec1Of_snoc h _).2 hr W' b' hr']; rfl
  · rw [(rec1Of_snoc h _).1 W b hr]
    dsimp only
    rw [List.filterMap_append, show [Ev.sample c].filterMap sampleOf = [c] from rfl]
    set S := b.filterMap sampleOf
    by_cases h1 : 25 ≤ S.length
    · by_cases h2 : S.length < 29
      · have hg : Grows1 mid x h := ⟨W, b, hr, h1, h2⟩
        rw [if_pos hg, List.drop_append_of_le_length h1,
          List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
      · have hg : ¬ Grows1 mid x h := by
          rintro ⟨_, _, h', -, h3⟩; rw [hr] at h'; cases h'; exact h2 h3
        rw [if_neg hg, List.drop_append_of_le_length h1,
          List.take_append_of_le_length (by simp; omega)]
    · have hg : ¬ Grows1 mid x h := by
        rintro ⟨_, _, h', h3, -⟩; rw [hr] at h'; cases h'; exact h1 h3
      rw [if_neg hg, List.drop_eq_nil_of_le (by simp; omega),
        List.drop_eq_nil_of_le (by omega)]

theorem length_foldChal1_le (h : List Ev) : (foldChal1 mid x h).length ≤ 4 := by
  unfold foldChal1
  split
  · simp
  · simp

theorem length_foldChal1_of_grows1 {h : List Ev} (hg : Grows1 mid x h) :
    (foldChal1 mid x h).length < 4 := by
  obtain ⟨W, b, hr, -, hl⟩ := hg
  unfold foldChal1
  rw [hr]
  simp only [List.length_take, List.length_drop]
  omega

theorem W1L_of_rec1Of {h : List Ev} {W : Word} {b : List Ev} (hr : rec1Of mid x h = some (W, b)) :
    W1L mid x h = W := by
  unfold W1L; rw [hr]

theorem rec1Of_of_foldChal1_ne {h : List Ev} (hne : foldChal1 mid x h ≠ []) :
    ∃ W b, rec1Of mid x h = some (W, b) := by
  unfold foldChal1 at hne
  rcases hr : rec1Of mid x h with _ | ⟨W, b⟩
  · rw [hr] at hne; exact absurd rfl hne
  · exact ⟨W, b, rfl⟩

/-- **The level-1 luck of `P_S`**: some member of the list of `C_rec`'s level-1 word is lucky in the
level-1 fold rounds drawn. -/
def LuckB1 (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  ∃ V ∈ iList (codesRec20 1).code (codesRec20 1).thr (rows1 4 (codesRec20 1).n (W1L mid x h)),
    RoundsLuck 4 (foldChal1 mid x h) (rows1 4 (codesRec20 1).n (W1L mid x h)) V

theorem not_luckB1_of_nil {h : List Ev} (hn : foldChal1 mid x h = []) : ¬ LuckB1 mid x h := by
  rintro ⟨V, -, hV⟩
  rw [hn] at hV
  exact roundsLuck_nil _ _ _ hV

/-- Level-1 luck does not change where its challenges and its word do not. -/
theorem luckB1_snoc_iff {h : List Ev} {e : Ev}
    (hf : foldChal1 mid x (h ++ [e]) = foldChal1 mid x h) :
    LuckB1 mid x (h ++ [e]) ↔ LuckB1 mid x h := by
  by_cases hn : foldChal1 mid x h = []
  · exact ⟨fun h' ↦ absurd h' (not_luckB1_of_nil (hf.trans hn)),
      fun h' ↦ absurd h' (not_luckB1_of_nil hn)⟩
  · obtain ⟨W, b, hr⟩ := rec1Of_of_foldChal1_ne hn
    unfold LuckB1
    rw [W1L_of_rec1Of ((rec1Of_snoc h e).1 W b hr), W1L_of_rec1Of hr, hf]

theorem not_luckB1_snoc {h : List Ev} {e : Ev} (he : sampleOf e = none) (hB : ¬ LuckB1 mid x h) :
    ¬ LuckB1 mid x (h ++ [e]) :=
  fun h' ↦ hB ((luckB1_snoc_iff (foldChal1_snoc_of_ne h e he)).1 h')

theorem foldChal1_nil : foldChal1 mid x [] = [] := by
  unfold foldChal1 rec1Of afterMid
  have : rootsProg.retSplit [] = none := by
    simp [rootsProg, commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.bind,
      retSplit]
  rw [this]

/-! ## The luck predicate -/

/-- **The luck of `P_S`** (lvm2, S4): level-0 luck (`C_rec`'s root candidate in the six level-0
fold rounds) or level-1 luck (a member of the level-1 list in the four level-1 fold rounds). -/
def LuckB (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) : Prop :=
  LuckB0 mid x h ∨ LuckB1 mid x h

/-- **A prover move or an opening keeps luck out.** -/
theorem not_luckB_snoc {h : List Ev} {e : Ev} (he : sampleOf e = none) (hB : ¬ LuckB mid x h) :
    ¬ LuckB mid x (h ++ [e]) := by
  rintro (h' | h')
  · exact not_luckB0_snoc he (fun h0 ↦ hB (.inl h0)) h'
  · exact not_luckB1_snoc he (fun h1 ↦ hB (.inr h1)) h'

theorem LuckB_nil : ¬ LuckB mid x [] := by
  rintro (h' | h')
  · exact LuckB0_nil h'
  · exact not_luckB1_of_nil foldChal1_nil h'

/-! ## The group bound -/

open Classical in
theorem length_foldChal_snoc (h : List Ev) (c : E) :
    (foldChal mid x (h ++ [Ev.sample c])).length =
      (foldChal mid x h).length + if Grows mid x h then 1 else 0 := by
  rw [foldChal_snoc_sample]; split_ifs <;> simp

open Classical in
theorem length_foldChal1_snoc (h : List Ev) (c : E) :
    (foldChal1 mid x (h ++ [Ev.sample c])).length =
      (foldChal1 mid x h).length + if Grows1 mid x h then 1 else 0 := by
  rw [foldChal1_snoc_sample]; split_ifs <;> simp

theorem length_foldChal_le (h : List Ev) : (foldChal mid x h).length ≤ 6 := by
  unfold foldChal
  split
  · simp
  · simp

open Classical in
theorem length_foldChal_add_le (h : List Ev) :
    (foldChal mid x h).length + (if Grows mid x h then 1 else 0) ≤ 6 := by
  split_ifs with hg
  · exact length_foldChal_of_grows hg
  · simpa using length_foldChal_le h

open Classical in
theorem length_foldChal1_add_le (h : List Ev) :
    (foldChal1 mid x h).length + (if Grows1 mid x h then 1 else 0) ≤ 4 := by
  split_ifs with hg
  · exact length_foldChal1_of_grows1 hg
  · simpa using length_foldChal1_le h

open Classical in
/-- The challenges at which the level-0 luck starts: at most `2^15`, and none unless the level-0
challenges grow. -/
theorem card_bad0_le {h : List Ev} (hB : ¬ LuckB0 mid x h) :
    (Finset.univ.filter fun c : E ↦ LuckB0 mid x (h ++ [Ev.sample c])).card ≤
      (if Grows mid x h then 1 else 0) * 2 ^ 15 := by
  by_cases hg : Grows mid x h
  · rw [if_pos hg, one_mul]
    have hlt := length_foldChal_of_grows hg
    obtain ⟨l₁, l₃, hm⟩ := afterMid_of_grows hg
    by_cases hc : ∃ q, q ∈ Candidates 19 2 thrRec (WrOf h)
    · obtain ⟨q, hq⟩ := hc
      have hnq : ¬ RoundsLuck LeanVM.Protocol.EndToEnd.laneBits (foldChal mid x h)
          (laneRows 19 2 (WrOf h)) (encRows 19 2 q) := fun h' ↦ hB ⟨q, hq, h'⟩
      refine le_trans (Finset.card_le_card fun c hc ↦ ?_)
        ((card_roundsLuck_snoc LeanVM.Protocol.EndToEnd.laneBits _ _ _ hlt hnq).trans (by norm_num))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      obtain ⟨q', hq', hl⟩ := hc
      unfold WrOf at hq' hl
      rw [rootsOf_snoc hm, foldChal_snoc_sample, if_pos hg] at hl
      rw [rootsOf_snoc hm] at hq'
      rwa [cands_rec_unique _ hq' hq] at hl
    · push Not at hc
      refine le_trans (Finset.card_le_card (t := ∅) fun c hc' ↦ ?_) (by simp)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
      obtain ⟨q', hq', -⟩ := hc'
      unfold WrOf at hq'
      rw [rootsOf_snoc hm] at hq'
      exact absurd hq' (hc q')
  · rw [if_neg hg, zero_mul]
    refine le_trans (Finset.card_le_card (t := ∅) fun c hc' ↦ ?_) (by simp)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    exact absurd ((luckB0_snoc_iff (by rw [foldChal_snoc_sample, if_neg hg])).1 hc') hB

open Classical in
/-- A new round makes a list of at most `m` members lucky at at most `m·|ι|` challenges (`m = 1`
in unique decoding; generic for a Johnson level-1 code). -/
theorem card_luck_snoc_le {ι : Type} [Fintype ι] {k m : ℕ} (L : Finset ((Fin k → Bool) → ι → E))
    (hL : L.card ≤ m) (O : (Fin k → Bool) → ι → E) (α : List E) (hα : α.length < k)
    (hn : ¬ ∃ V ∈ L, RoundsLuck k α O V) :
    (Finset.univ.filter fun c : E ↦ ∃ V ∈ L, RoundsLuck k (α ++ [c]) O V).card ≤
      m * Fintype.card ι :=
  (card_filter_exists_le L (fun V c ↦ RoundsLuck k (α ++ [c]) O V) fun V hV ↦
    card_roundsLuck_snoc k α O V hα fun h' ↦ hn ⟨V, hV, h'⟩).trans (Nat.mul_le_mul_right _ hL)

open Classical in
/-- The challenges at which the level-1 luck starts: at most `2^12 ≤ 2^15`, and none unless the
level-1 challenges grow. -/
theorem card_bad1_le {h : List Ev} (hB : ¬ LuckB1 mid x h) :
    (Finset.univ.filter fun c : E ↦ LuckB1 mid x (h ++ [Ev.sample c])).card ≤
      (if Grows1 mid x h then 1 else 0) * 2 ^ 15 := by
  by_cases hg : Grows1 mid x h
  · rw [if_pos hg, one_mul]
    have hlt := length_foldChal1_of_grows1 hg
    obtain ⟨W, b, hr, -⟩ := id hg
    have hW1 : ∀ c, W1L mid x (h ++ [Ev.sample c]) = W1L mid x h := fun c ↦ by
      rw [W1L_of_rec1Of ((rec1Of_snoc h _).1 W b hr), W1L_of_rec1Of hr]
    have key : ∀ c, LuckB1 mid x (h ++ [Ev.sample c]) ↔
        ∃ V ∈ iList (codesRec20 1).code (codesRec20 1).thr (rows1 4 (codesRec20 1).n (W1L mid x h)),
          RoundsLuck 4 (foldChal1 mid x h ++ [c]) (rows1 4 (codesRec20 1).n (W1L mid x h)) V := by
      intro c; unfold LuckB1; rw [hW1 c, foldChal1_snoc_sample, if_pos hg]
    simp only [key]
    refine (card_luck_snoc_le (m := 1) _ ((codesRec20 1).card_iList_le _) _ _ hlt hB).trans ?_
    rw [one_mul, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by norm_num) (by decide)
  · rw [if_neg hg, zero_mul]
    refine le_trans (Finset.card_le_card (t := ∅) fun c hc' ↦ ?_) (by simp)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    exact absurd ((luckB1_snoc_iff (by rw [foldChal1_snoc_sample, if_neg hg])).1 hc') hB

open Classical in
/-- **The luck's group bound**: from a history that is not lucky, the next group becomes lucky
with probability at most `((6 − |foldChal|) + (4 − |foldChal1|)) · 2^15/|E|`. -/
theorem esc_luck_le : ∀ (p : VerifierProgram Bool) (h : List Ev), ¬ LuckB mid x h →
    esc (fun h' ↦ ¬ LuckB mid x h') h p ≤
      (((6 - (foldChal mid x h).length) + (4 - (foldChal1 mid x h).length) : ℕ) : ℝ≥0∞) * δL
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
      have hf1 := foldChal1_snoc_of_ne (mid := mid) (x := x) h (Ev.query rows) rfl
      rw [← hf, ← hf1]
      exact esc_luck_le _ _ (not_luckB_snoc rfl hB)
    · exact zero_le
  | .sample k, h, hB => by
    simp only [esc]
    have hB0 : ¬ LuckB0 mid x h := fun h' ↦ hB (.inl h')
    have hB1 : ¬ LuckB1 mid x h := fun h' ↦ hB (.inr h')
    set n0 := (foldChal mid x h).length
    set n1 := (foldChal1 mid x h).length
    set k0 : ℕ := if Grows mid x h then 1 else 0
    set k1 : ℕ := if Grows1 mid x h then 1 else 0
    have hle0 : n0 + k0 ≤ 6 := length_foldChal_add_le h
    have hle1 : n1 + k1 ≤ 4 := length_foldChal1_add_le h
    set N' : ℕ := (6 - (n0 + k0)) + (4 - (n1 + k1))
    set bad := Finset.univ.filter fun c : E ↦ LuckB mid x (h ++ [Ev.sample c])
    have hbad : bad.card ≤ (k0 + k1) * 2 ^ 15 := by
      refine (Finset.card_le_card (t := (Finset.univ.filter fun c : E ↦
          LuckB0 mid x (h ++ [Ev.sample c])) ∪ (Finset.univ.filter fun c : E ↦
          LuckB1 mid x (h ++ [Ev.sample c]))) fun c hc ↦ ?_).trans
        ((Finset.card_union_le _ _).trans ?_)
      · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hc ⊢
        exact hc
      · rw [add_mul]
        exact add_le_add (card_bad0_le hB0) (card_bad1_le hB1)
    have hstep : ∀ c, esc (fun h' ↦ ¬ LuckB mid x h') (h ++ [Ev.sample c]) (k c) ≤
        (if c ∈ bad then 1 else 0) + (N' : ℝ≥0∞) * δL := by
      intro c
      by_cases hc : c ∈ bad
      · rw [if_pos hc]; exact (esc_le_one _ _ _).trans le_self_add
      · rw [if_neg hc, zero_add]
        have hB' : ¬ LuckB mid x (h ++ [Ev.sample c]) := by simpa [bad] using hc
        have := esc_luck_le (k c) _ hB'
        rwa [length_foldChal_snoc, length_foldChal1_snoc] at this
    have hK : (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card ≤ ((k0 + k1 : ℕ) : ℝ≥0∞) * δL := by
      calc (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card
          ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * (((k0 + k1) * 2 ^ 15 : ℕ) : ℝ≥0∞) := by
            gcongr
        _ = ((k0 + k1 : ℕ) : ℝ≥0∞) * δL := by
            rw [δL, ENNReal.div_eq_inv_mul]; push_cast; ring
    calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c, esc (fun h' ↦ ¬ LuckB mid x h') (h ++ [Ev.sample c]) (k c)
        ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, ((if c ∈ bad then 1 else 0) + (N' : ℝ≥0∞) * δL) := by
          gcongr with c; exact hstep c
      _ = (Fintype.card E : ℝ≥0∞)⁻¹ * bad.card + (N' : ℝ≥0∞) * δL := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_add,
            ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul, Finset.sum_ite_mem,
            Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ((k0 + k1 : ℕ) : ℝ≥0∞) * δL + (N' : ℝ≥0∞) * δL := by gcongr
      _ = (((6 - n0) + (4 - n1) : ℕ) : ℝ≥0∞) * δL := by
          rw [← add_mul, ← Nat.cast_add, show k0 + k1 + N' = (6 - n0) + (4 - n1) by omega]

/-- The luck bound: `10 · 2^15 / |E| ≤ 2^-132` (within S2J's exact budget's margin). -/
theorem ten_δL_le : (10 : ℝ≥0∞) * δL ≤ (2 : ℝ≥0∞)⁻¹ ^ 132 := by
  rw [δL, card_E_ennreal, ← mul_div_assoc, ← two_pow_cast 192,
    show (10 : ℝ≥0∞) * 2 ^ 15 = ((10 * 2 ^ 15 : ℕ) : ℝ≥0∞) by push_cast; ring]
  exact natCast_div_le_inv_pow (by positivity) (by norm_num)

end Luck

end Lvm.ASM
