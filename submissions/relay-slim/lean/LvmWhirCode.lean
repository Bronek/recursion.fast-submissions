-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Code.lean` (formal rev 40f877dc) as `LvmWhirCode` for
-- lvm (WP-7). Edited by hand: `LevelCode` (leanVM lines 58-97) no longer fixes ArkLib's Johnson radius; it carries the
-- threshold `thr`, the list bound `listMax`, the MCA count `mcaMax` and their proofs as one field
-- `facts : CodeFacts …` (WP-6, `LvmMcaUd`). `card_iList_le`, `card_foldBad_le`, `two_pow_le_thr` keep their
-- statements (for row types in `Type`) and are projections of `facts`. `LevelCode.ud` is the unique-decoding
-- instance (WP-6 `codeFacts_udLevel`). `η`, `hagr` and the Johnson computations are gone. Everything after
-- `LevelCode` is leanVM's (`ReedSolomon.code` is LvmRS's `rsCode`). The same generalisation is leanerVM's per-level
-- `ListBound`/`McaBound` (`LeanerVM/Protocol/Whir/Lanes.lean`, `listBound_unique` in `Exact.lean`); not reused: its words
-- and messages are other types (`LW`, `Msgs`) and its `McaBound` instance is at exact agreement only, while WP-6's
-- `codeFacts_udLevel` gives both bounds at the unique-decoding threshold on leanVM's `iList`/`foldBad`.
/-
  LeanVM.Protocol.Whir.Sound.Code

  The code of a WHIR level at an agreement threshold with a list bound and an MCA count, its lists,
  the decoding of list members to messages, lane oracles indexed by integers, and the fold step of
  the round-by-round soundness: a fold challenge keeps every list member violating the running
  claim except at `2·L + 2^m·E_mca` challenges.
-/


import LvmWhirSumcheck
import LvmNovelBasis
import LvmMcaUd

/-!
# The code of a level and the fold step

Annex B of the leanVM specification (leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`,
`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), proof of Theorem `thm:rbr`, "Fold
challenge": level `i` uses the novel-basis Reed-Solomon code `C_i = RS[E, D_{κ,R}, 2^κ]`
(`enc κ R`, `range_enc`) on `n = 2^(κ+R)` points. leanVM runs the analysis at ArkLib's Johnson
radius; here the radius is a parameter of the level, with its facts.

* `LevelCode`: the parameters `κ, R` (`1 ≤ κ`, `1 ≤ R`, `κ + R ≤ 64`), an agreement threshold
  `thr`, a list bound `listMax`, a per-row-pair MCA count `mcaMax`, and `facts : CodeFacts …`
  (`LvmMcaUd`): codewords agreeing on `2^κ` points are equal, `2^κ ≤ thr`, every list at `thr`
  has at most `listMax` members, every word on `Bool × ρ` rows has at most `|ρ|·mcaMax` fold-bad
  challenges. `LevelCode.card_iList_le`, `LevelCode.card_foldBad_le`, `LevelCode.two_pow_le_thr`
  are its projections.
* `LevelCode.ud`: **the unique-decoding level** (lvm BLUEPRINT §3.2, A13): `thr = udThr κ R =
  2^(κ+R−1) + 2^(κ−1)`, `listMax = 1`, `mcaMax = udMca κ R = 2^κ (n − thr) + n`.
* `decode`: the message of a codeword row (`enc` is injective), `Viol`: every member of the list
  of a word violates a claim, the invariant `A(i, j)` of the design note.
* Lane oracles are indexed by integers, `O : ℕ → Fin n → E` (lane `j` of column `v`), read on `m`
  lane bits by `rowsOf m O`. One fold binds the low lane bit: `foldN s O j = (1 − s) O(2j) +
  s O(2j+1)`, the order of the verifier's `eq_kernel` (first challenge, low bit).
* `card_foldStep_bad_le`: **the fold step.** If every member of the list of `rowsOf (m+1) O`
  violates `(Φ, σ)` and the prover's quadratic has `h(0) + h(1) = σ`, at most
  `2·listMax + 2^m·mcaMax` challenges `s` leave a member of the list of `rowsOf m (foldN s O)`
  satisfying `(Φ(s, ·), h(s))`. The two terms are the bad events `B₁` (sumcheck, two points per
  member) and `B₂` (the fold-list count `card_foldBad_le`, one pair of rows per lane of the folded
  word) of the Annex.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset

section

/-! ## The code of a level -/

/-- The code of a level: message variables `κ`, rate `2^-R`, an agreement threshold `thr`, a list
bound `listMax` and an MCA count `mcaMax` with their proofs (leanVM: ArkLib's Johnson bounds at a
slack `η`). -/
structure LevelCode where
  /-- The message variables. -/
  κ : ℕ
  /-- The log inverse rate. -/
  R : ℕ
  /-- The domain fits in `K`. -/
  h64 : κ + R ≤ 64
  /-- At least one message variable. -/
  hκ : 1 ≤ κ
  /-- Rate at most `1/2`. -/
  hR : 1 ≤ R
  /-- The agreement threshold `A`. -/
  thr : ℕ
  /-- The list bound `L`. -/
  listMax : ℕ
  /-- The MCA count per pair of rows. -/
  mcaMax : ℕ
  /-- The code facts at `thr` (`LvmMcaUd.CodeFacts`). -/
  facts : CodeFacts (rsCode (domain κ R h64) (2 ^ κ)) (2 ^ κ) thr listMax mcaMax

namespace LevelCode

variable (P : LevelCode)

/-- The block length `n = 2^(κ+R)`. -/
abbrev n : ℕ := 2 ^ (P.κ + P.R)

/-- The degree bound `D = 2^κ − 1`. -/
abbrev D : ℕ := 2 ^ P.κ - 1

/-- The code `RS[E, D_{κ,R}, 2^κ]`, the range of `enc κ R`. -/
noncomputable abbrev code : Submodule E (Fin P.n → E) :=
  rsCode (domain P.κ P.R P.h64) (2 ^ P.κ)

theorem two_pow_κ_eq : 2 ^ P.κ = P.D + 1 := (Nat.sub_add_cancel Nat.one_le_two_pow).symm

theorem one_le_D : 1 ≤ P.D := by
  have : 2 ≤ 2 ^ P.κ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ P.κ := Nat.pow_le_pow_right (by norm_num) P.hκ
  simp only [D]; omega

theorem D_le : P.D ≤ P.n - 2 := by
  have : 2 * 2 ^ P.κ ≤ 2 ^ (P.κ + P.R) := by
    rw [pow_add, mul_comm]
    exact Nat.mul_le_mul_left _ (by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ P.R := Nat.pow_le_pow_right (by norm_num) P.hR)
  have := P.one_le_D
  simp only [D, n] at *; omega

theorem D_lt_n : P.D < P.n := by
  have := P.D_le; have := P.one_le_D; omega

/-- **The list bound** (projection of `facts`). -/
theorem card_iList_le {ρ : Type} [Fintype ρ] (O : ρ → Fin P.n → E) :
    (iList P.code P.thr O).card ≤ P.listMax :=
  P.facts.card_iList_le ρ O

/-- **The fold-list count**: at most `|ρ|·mcaMax` challenges create new list members (projection
of `facts`). -/
theorem card_foldBad_le {ρ : Type} [Fintype ρ] (O : Bool × ρ → Fin P.n → E) :
    (foldBad P.code P.thr O).card ≤ Fintype.card ρ * P.mcaMax :=
  P.facts.card_foldBad_le ρ O

/-- The threshold is at least the dimension: `2^κ ≤ thr` (projection of `facts`). -/
theorem two_pow_le_thr : 2 ^ P.κ ≤ P.thr := P.facts.k_le_thr

/-- **The unique-decoding level** (WP-6 `codeFacts_udLevel`): threshold `udThr κ R`, list bound
`1`, MCA count `udMca κ R`. -/
noncomputable def ud (κ R : ℕ) (h64 : κ + R ≤ 64) (hκ : 1 ≤ κ) (hR : 1 ≤ R) : LevelCode where
  κ := κ
  R := R
  h64 := h64
  hκ := hκ
  hR := hR
  thr := udThr κ R
  listMax := 1
  mcaMax := udMca κ R
  facts := codeFacts_udLevel hκ (domain κ R h64)

@[simp] theorem ud_κ (κ R h64 hκ hR) : (ud κ R h64 hκ hR).κ = κ := rfl
@[simp] theorem ud_R (κ R h64 hκ hR) : (ud κ R h64 hκ hR).R = R := rfl
@[simp] theorem ud_thr (κ R h64 hκ hR) : (ud κ R h64 hκ hR).thr = udThr κ R := rfl
@[simp] theorem ud_listMax (κ R h64 hκ hR) : (ud κ R h64 hκ hR).listMax = 1 := rfl
@[simp] theorem ud_mcaMax (κ R h64 hκ hR) : (ud κ R h64 hκ hR).mcaMax = udMca κ R := rfl

end LevelCode

/-! ## Decoding -/

variable (P : LevelCode)

open Classical in
/-- The message of a codeword row: the unique `g` with `enc g = V u` (zero off the code). -/
noncomputable def decode {ρ : Type*} (V : ρ → Fin P.n → E) : ρ → (Fin P.κ → Bool) → E :=
  fun u ↦ if h : ∃ g, enc P.κ P.R g = V u then h.choose else 0

theorem enc_decode {ρ : Type*} {V : ρ → Fin P.n → E} (hV : IsInterleavedCodeword P.code V)
    (u : ρ) : enc P.κ P.R (decode P V u) = V u := by
  have hex : ∃ g, enc P.κ P.R g = V u := by
    have : V u ∈ rsCode (domain P.κ P.R P.h64) (2 ^ P.κ) := hV u
    rw [← range_enc P.h64] at this
    exact this
  simp only [decode, hex, dite_true]
  exact hex.choose_spec

/-- Decoding an encoded word gives the messages back. -/
theorem decode_enc {ρ : Type*} (g : ρ → (Fin P.κ → Bool) → E) :
    decode P (fun u ↦ enc P.κ P.R (g u)) = g := by
  funext u
  have hcw : IsInterleavedCodeword P.code fun u ↦ enc P.κ P.R (g u) := fun u ↦ by
    show _ ∈ rsCode (domain P.κ P.R P.h64) (2 ^ P.κ)
    rw [← range_enc P.h64]; exact LinearMap.mem_range_self _ _
  exact enc_injective P.h64 (enc_decode P hcw u)

/-- Every member of the list of `O` violates the claim `(Φ, σ)`. -/
def Viol {m : ℕ} (O : (Fin m → Bool) → Fin P.n → E) (Φ : List E → E) (σ : E) : Prop :=
  ∀ V ∈ iList P.code P.thr O, claimSum Φ (decode P V) ≠ σ

/-! ## Lane oracles -/

/-- An integer-indexed lane oracle on `m` lane bits: lane `⟨u⟩` (bit `0` low). -/
def rowsOf (m : ℕ) {ι : Type*} (O : ℕ → ι → E) : (Fin m → Bool) → ι → E :=
  fun u ↦ O (bitsToNat u)

/-- One fold of an integer-indexed lane oracle on the low lane bit. -/
def foldN {ι : Type*} (s : E) (O : ℕ → ι → E) : ℕ → ι → E :=
  fun j x ↦ (1 - s) * O (2 * j) x + s * O (2 * j + 1) x

/-- The folds of a level, first challenge first. -/
def foldsN {ι : Type*} (s : List E) (O : ℕ → ι → E) : ℕ → ι → E :=
  s.foldl (fun O c ↦ foldN c O) O

theorem bitsToNat_cons {m : ℕ} (b : Bool) (u : Fin m → Bool) :
    bitsToNat (Fin.cons b u : Fin (m + 1) → Bool) = b.toNat + 2 * bitsToNat u := by
  simp only [bitsToNat, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
    mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The rows of an interleaved word on `m + 1` lane bits, split on the low bit. -/
def consRows {m : ℕ} {ι M : Type*} (Q : (Fin (m + 1) → Bool) → ι → M) :
    Bool × (Fin m → Bool) → ι → M :=
  fun r ↦ Q (Fin.cons r.1 r.2)

/-- Rejoin split rows. -/
def unconsRows {m : ℕ} {ι M : Type*} (Q : Bool × (Fin m → Bool) → ι → M) :
    (Fin (m + 1) → Bool) → ι → M :=
  fun u ↦ Q (u 0, Fin.tail u)

theorem consRows_unconsRows {m : ℕ} {ι M : Type*} (Q : Bool × (Fin m → Bool) → ι → M) :
    consRows (unconsRows Q) = Q := by
  funext r
  simp [consRows, unconsRows]

/-- Folding the integer-indexed oracle is folding its split rows. -/
theorem rowsOf_foldN {m : ℕ} {ι : Type*} (s : E) (O : ℕ → ι → E) :
    rowsOf m (foldN s O) = fold s (consRows (rowsOf (m + 1) O)) := by
  funext u x
  simp [rowsOf, foldN, fold, consRows, bitsToNat_cons, add_comm]

/-- Lists are invariant under splitting the rows. -/
theorem consRows_mem_iList {m : ℕ} {ι : Type*} [Fintype ι] (C : Submodule E (ι → E)) (A : ℕ)
    {Q V : (Fin (m + 1) → Bool) → ι → E} :
    consRows V ∈ iList C A (consRows Q) ↔ V ∈ iList C A Q := by
  simp only [mem_iList, IsInterleavedCodeword, IsClose, AgreeOn, consRows]
  constructor
  · rintro ⟨hcw, S, hS, hag⟩
    refine ⟨fun u ↦ by simpa using hcw (u 0, Fin.tail u), S, hS, fun u x hx ↦ ?_⟩
    simpa using hag (u 0, Fin.tail u) x hx
  · rintro ⟨hcw, S, hS, hag⟩
    exact ⟨fun r ↦ hcw _, S, hS, fun r x hx ↦ hag _ x hx⟩

/-- The decoded fold of a codeword is the fold of its messages. -/
theorem decode_fold {m : ℕ} {V : (Fin (m + 1) → Bool) → Fin P.n → E}
    (hV : IsInterleavedCodeword P.code V) (s : E) :
    decode P (fold s (consRows V)) = foldRows s (decode P V) := by
  have hcw : IsInterleavedCodeword P.code (fold s (consRows V)) :=
    isInterleavedCodeword_fold _ (fun r ↦ hV _) s
  funext u
  apply enc_injective P.h64
  have hf : foldRows s (decode P V) u =
      (1 - s) • decode P V (Fin.cons false u) + s • decode P V (Fin.cons true u) := by
    funext x; simp [foldRows]
  rw [enc_decode P hcw u, hf, map_add, map_smul, map_smul, enc_decode P hV, enc_decode P hV,
    fold_apply_eq_smul]
  rfl

/-! ## The fold step -/

open Classical in
/-- **The fold step** (Annex B, proof of `thm:rbr`, "Fold challenge"): if every member of the list
of `rowsOf (m+1) O` violates `(Φ, σ)` and the prover's quadratic `[c₀, c₁, c₂]` has
`h(0) + h(1) = σ`, at most `2·listMax + 2^m·mcaMax` challenges `s` leave a member of the list of
`rowsOf m (foldN s O)` satisfying `(Φ(s, ·), h(s))`. -/
theorem card_foldStep_bad_le {m : ℕ} (Φ : List E → E) (hΦ : IsMultiaffine (m + 1 + P.κ) Φ)
    (O : ℕ → Fin P.n → E) (σ c₀ c₁ c₂ : E)
    (hσ : polyEval [c₀, c₁, c₂] 0 + polyEval [c₀, c₁, c₂] 1 = σ)
    (hviol : Viol P (rowsOf (m + 1) O) Φ σ) :
    (univ.filter fun s ↦
        ¬ Viol P (rowsOf m (foldN s O)) (fun r ↦ Φ (s :: r)) (polyEval [c₀, c₁, c₂] s)).card ≤
      2 * P.listMax + 2 ^ m * P.mcaMax := by
  classical
  set Q := rowsOf (m + 1) O
  set L := iList P.code P.thr Q
  let B₁ : Finset E := univ.filter fun s ↦
    ∃ V ∈ L, polyEval [c₀, c₁, c₂] s = claimSum (fun r ↦ Φ (s :: r)) (foldRows s (decode P V))
  have hB₁ : B₁.card ≤ 2 * P.listMax := by
    refine (card_filter_exists_le L _ (N := 2) fun V hV ↦
      card_sumcheck_bad_le Φ hΦ (decode P V) σ c₀ c₁ c₂ hσ (hviol V hV)).trans ?_
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ (P.card_iList_le Q)
  have hB₂ : (foldBad P.code P.thr (consRows Q)).card ≤ 2 ^ m * P.mcaMax := by
    have := P.card_foldBad_le (consRows Q)
    simpa using this
  refine (Finset.card_le_card fun s hs ↦ ?_).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add hB₁ hB₂))
  rw [Finset.mem_union]
  by_contra hgood
  push Not at hgood
  obtain ⟨hs₁, hs₂⟩ := hgood
  refine (Finset.mem_filter.mp hs).2 fun V' hV' ↦ ?_
  rw [rowsOf_foldN] at hV'
  have hlist := not_not.mp ((not_congr (mem_foldBad _ _ _ s)).mp hs₂)
  rw [hlist] at hV'
  obtain ⟨W', hW', rfl⟩ := Finset.mem_image.mp hV'
  rw [← consRows_unconsRows W', consRows_mem_iList] at hW'
  rw [← consRows_unconsRows W', decode_fold P ((mem_iList _ _ _ _).mp hW').1]
  intro heq
  exact hs₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, hW', heq.symm⟩)

end
end LeanVM.Protocol.Whir.Sound
