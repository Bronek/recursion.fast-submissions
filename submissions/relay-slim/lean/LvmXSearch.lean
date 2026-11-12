-- adapted from rf-k/submissions/flock-recursive/lean/FRXSearch.lean@kk/base (namespace FR.X → Lvm.X).
-- Port of FR's search branch (FR BLUEPRINT B-15) for lvm (WP-13a).
import RecursionFast.Contract.Certificate

/-!
# The extractor's search branch (B-15)

Outside the contract's `Computes` domain the extractor need not be efficient, but the badge
compiles the whole submission, so it must still be a computable function. B-15's answer is a
total search of the **finite** witness space of `Rel acc c`, tested by the decidable `Rel`.

**The space is finite** under the contract's types: a leaf witness has `n ≤ chainCap`; a node
witness has two digests and two signed proofs, and `Submission.acc` bounds each: the proof below
`2^64` bytes, the trace at most `S.qV ≤ 2^16` entries (the certificate's cap) of queries of at most
`queryCap` bytes, and `SigOk` fixes the signature's shape (`idx < 2^16`, 133 chain values, 16
path digests). `SFits`/`WFits` name these bounds; `sFits_of_acc` derives them from `acc`.

**Finders.** A `Finder α` takes a test `k : α → Option Wit` and returns the first `some` that
`k` gives over a fixed enumeration of `α`'s candidates. They are built from `fRet` (one
candidate), `fBind` (dependent pairs), `fOr` (union) and `fNat` (the numbers below `n`), and
never materialise a list of candidates, so no large closed term exists in the compiled code.
* `Finder.Sound`: every result is the test's result on some candidate.
* `Finder.Covers F a`: if the test succeeds on `a`, `F` returns something.

**The search.** `search A vk c` runs `fWit` with the test `relDec (A vk) c`.
* **`search_sound`**: its result is a witness of `Rel (A vk) c`.
* **`search_spec`**: if a witness within the bounds exists, the search returns one;
  `search_spec_acc` for an `A` that implies the bounds (the contract's `acc`, `sFits_of_acc`).
* `search_none`: no witness, `none`.

Its running time is astronomical, and irrelevant: on the domain `E` is the program's denotation
(`FRXExt`), and the search is only ever reasoned about.

Controls: `search_acceptAll` (positive: an accept-everything `acc` and a node statement give a
witness), `search_rejectAll_node` (negative: an `acc` rejecting everything gives no node
witness), and two kernel-evaluated toy runs of `fNat` (`toy_found`, `toy_none`).
-/

namespace Lvm.X
open RecursionFast

/-! ## Finders -/

/-- **A finder over `α`**: given a test, the first `some` it gives over a fixed enumeration of
candidates in `α`, or `none`. -/
abbrev Finder (α : Type) : Type := (α → Option Wit) → Option Wit

/-- Every result of the finder is the test's result on some candidate. -/
def Finder.Sound {α : Type} (F : Finder α) : Prop := ∀ k w, F k = some w → ∃ a, k a = some w

/-- `a` is a candidate of `F`: whenever the test succeeds on `a`, `F` returns a result. -/
def Finder.Covers {α : Type} (F : Finder α) (a : α) : Prop := ∀ k, (k a).isSome → (F k).isSome

/-- The one candidate `a`. -/
def fRet {α : Type} (a : α) : Finder α := fun k => k a

/-- The candidates of `G a`, for each candidate `a` of `F`. -/
def fBind {α β : Type} (F : Finder α) (G : α → Finder β) : Finder β := fun k => F fun a => G a k

/-- The candidates of `F`, then those of `G`. -/
def fOr {α : Type} (F G : Finder α) : Finder α := fun k => (F k).or (G k)

/-- The numbers below `n`, in increasing order. -/
def fNat : ℕ → Finder ℕ
  | 0, _ => none
  | n + 1, k => (fNat n k).or (k n)

/-- The lists of exactly `n` candidates of `F`. -/
def fListN {α : Type} (F : Finder α) : ℕ → Finder (List α)
  | 0, k => k []
  | n + 1, k => F fun a => fListN F n fun l => k (a :: l)

/-- The lists of at most `N` candidates of `F`. -/
def fListLe {α : Type} (F : Finder α) (N : ℕ) : Finder (List α) := fBind (fNat (N + 1)) (fListN F)

section Rules
variable {α β : Type}

theorem sound_fRet (a : α) : (fRet a).Sound := fun _ _ h => ⟨a, h⟩

theorem covers_fRet (a : α) : (fRet a).Covers a := fun _ h => h

theorem sound_fBind {F : Finder α} {G : α → Finder β} (hF : F.Sound) (hG : ∀ a, (G a).Sound) :
    (fBind F G).Sound := fun k w h => by
  obtain ⟨a, ha⟩ := hF _ w h
  exact hG a k w ha

theorem covers_fBind {F : Finder α} {G : α → Finder β} {a : α} {b : β} (hF : F.Covers a)
    (hG : (G a).Covers b) : (fBind F G).Covers b := fun k hk => hF (fun a => G a k) (hG k hk)

theorem sound_fOr {F G : Finder α} (hF : F.Sound) (hG : G.Sound) : (fOr F G).Sound :=
  fun k w h => by
    unfold fOr at h
    cases hf : F k with
    | none => rw [hf, Option.none_or] at h; exact hG k w h
    | some v => rw [hf, Option.some_or] at h; exact hF k w (hf.trans h)

theorem covers_fOr_left {F G : Finder α} {a : α} (hF : F.Covers a) : (fOr F G).Covers a :=
  fun k hk => by
    have := hF k hk
    unfold fOr; cases hf : F k <;> simp_all

theorem covers_fOr_right {F G : Finder α} {a : α} (hG : G.Covers a) : (fOr F G).Covers a :=
  fun k hk => by
    have := hG k hk
    unfold fOr; cases F k <;> simp_all

theorem sound_fNat : ∀ n, (fNat n).Sound
  | 0 => fun _ _ h => by cases h
  | n + 1 => fun k w h => by
    simp only [fNat] at h
    cases hf : fNat n k with
    | none => rw [hf, Option.none_or] at h; exact ⟨n, h⟩
    | some v => rw [hf, Option.some_or] at h; exact sound_fNat n k w (hf.trans h)

theorem covers_fNat : ∀ {n a : ℕ}, a < n → (fNat n).Covers a
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, h => fun k hk => by
    simp only [fNat]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · simp [Option.isSome_or, covers_fNat h k hk]
    · simp [Option.isSome_or, hk]

theorem sound_fListN {F : Finder α} (hF : F.Sound) : ∀ n, (fListN F n).Sound
  | 0 => fun k w h => ⟨[], h⟩
  | n + 1 => fun k w h => by
    obtain ⟨a, ha⟩ := hF _ w h
    obtain ⟨l, hl⟩ := sound_fListN hF n _ w ha
    exact ⟨a :: l, hl⟩

theorem covers_fListN {F : Finder α} : ∀ {l : List α}, (∀ a ∈ l, F.Covers a) →
    (fListN F l.length).Covers l
  | [], _ => fun _ h => h
  | a :: _, h => fun k hk =>
    h a (List.mem_cons_self ..) _
      (covers_fListN (fun b hb => h b (List.mem_cons_of_mem _ hb)) (fun l' => k (a :: l')) hk)

theorem sound_fListLe {F : Finder α} (hF : F.Sound) (N : ℕ) : (fListLe F N).Sound :=
  sound_fBind (sound_fNat _) (sound_fListN hF)

theorem covers_fListLe {F : Finder α} {N : ℕ} {l : List α} (hl : l.length ≤ N)
    (h : ∀ a ∈ l, F.Covers a) : (fListLe F N).Covers l :=
  covers_fBind (covers_fNat (by omega)) (covers_fListN h)

end Rules

/-! ## The witness space -/

/-- The bytes. -/
def fByte : Finder UInt8 := fBind (fNat 256) fun i => fRet i.toUInt8

/-- The byte strings of fewer than `N` bytes. -/
def fBytesLt (N : ℕ) : Finder ByteArray :=
  fBind (fNat N) fun n => fBind (fListN fByte n) fun l => fRet ⟨l.toArray⟩

/-- The digests. -/
def fDigest : Finder Digest :=
  fBind (fListN fByte 32) fun l => fRet (Vector.ofFn fun i => l.getD i 0)

/-- A trace entry: a query of at most `queryCap` bytes and a digest. -/
def fEntry : Finder (ByteArray × Digest) :=
  fBind (fBytesLt (queryCap + 1)) fun q => fBind fDigest fun a => fRet (q, a)

/-- The certificate's cap on the verifier's queries, so on an accepted trace's length: `2^16`. -/
def qMax : ℕ := 2 ^ 16

/-- The traces of at most `qMax` entries. -/
def fTrace : Finder Trace := fListLe fEntry qMax

/-- The signatures of `SigOk`'s shape: an index below `2^16`, 133 chain values, 16 path digests. -/
def fSig : Finder Sig :=
  fBind (fNat (2 ^ sigHeight)) fun i => fBind (fListN fDigest wotsLen) fun o =>
    fBind (fListN fDigest sigHeight) fun p => fRet ⟨i, o, p⟩

/-- The signed proofs within `acc`'s bounds. -/
def fSigned : Finder Signed :=
  fBind (fBytesLt (2 ^ 64)) fun π => fBind fTrace fun tr => fBind fSig fun σ => fRet ⟨π, tr, σ⟩

/-- **The witness space**: the leaves of at most `chainCap` steps, then the nodes whose signed
proofs are within `acc`'s bounds. -/
def fWit : Finder Wit :=
  fOr (fBind fDigest fun s => fBind (fNat (chainCap + 1)) fun n => fRet (.leaf s n))
    (fBind fDigest fun c₁ => fBind fDigest fun c₂ => fBind fSigned fun p₁ =>
      fBind fSigned fun p₂ => fRet (.node c₁ c₂ p₁ p₂))

/-- **A signed proof within `acc`'s bounds** (the contract's `Submission.acc` and `SigOk`, with the
certificate's cap `qV ≤ 2^16`). -/
def SFits (p : Signed) : Prop :=
  p.π.size < 2 ^ 64 ∧ p.tr.length ≤ qMax ∧ (∀ e ∈ p.tr, e.1.size ≤ queryCap) ∧
    p.σ.idx < 2 ^ sigHeight ∧ p.σ.ots.length = wotsLen ∧ p.σ.path.length = sigHeight

/-- **A witness within the bounds**: a leaf of at most `chainCap` steps, or a node whose two signed
proofs are within `acc`'s bounds. -/
def WFits : Wit → Prop
  | .leaf _ n => n ≤ chainCap
  | .node _ _ p₁ p₂ => SFits p₁ ∧ SFits p₂

theorem covers_byte (b : UInt8) : fByte.Covers b :=
  covers_fBind (covers_fNat b.toNat_lt) (by rw [Nat.toUInt8, UInt8.ofNat_toNat]; exact covers_fRet b)

theorem covers_bytesLt {N : ℕ} {b : ByteArray} (h : b.size < N) : (fBytesLt N).Covers b := by
  have hl : b.data.toList.length = b.size := by rw [Array.length_toList]; rfl
  refine covers_fBind (covers_fNat h) ?_
  rw [← hl]
  refine covers_fBind (covers_fListN fun a _ => covers_byte a) ?_
  rw [show (⟨b.data.toList.toArray⟩ : ByteArray) = b by rw [Array.toArray_toList]]
  exact covers_fRet b

theorem covers_digest (d : Digest) : fDigest.Covers d := by
  refine covers_fBind (a := d.toList) ?_ ?_
  · have := covers_fListN (F := fByte) (l := d.toList) fun a _ => covers_byte a
    rwa [Vector.length_toList] at this
  · rw [show (Vector.ofFn fun i : Fin 32 => d.toList.getD i 0) = d by
      ext i hi; simp [List.getD_eq_getElem?_getD]]
    exact covers_fRet d

theorem covers_signed {p : Signed} (h : SFits p) : fSigned.Covers p := by
  obtain ⟨π, tr, i, o, q⟩ := p
  obtain ⟨hπ, htr, hq, hi, ho, hp⟩ := h
  refine covers_fBind (covers_bytesLt hπ) (covers_fBind (covers_fListLe htr fun e he => ?_)
    (covers_fBind (covers_fBind (covers_fNat hi) (covers_fBind (ho ▸ covers_fListN fun a _ =>
      covers_digest a) (covers_fBind (hp ▸ covers_fListN fun a _ => covers_digest a)
        (covers_fRet _)))) (covers_fRet _)))
  exact covers_fBind (covers_bytesLt (Nat.lt_succ_of_le (hq e he)))
    (covers_fBind (covers_digest e.2) (covers_fRet _))

theorem covers_wit {w : Wit} (h : WFits w) : fWit.Covers w := by
  cases w with
  | leaf s n =>
    exact covers_fOr_left (covers_fBind (covers_digest s)
      (covers_fBind (covers_fNat (Nat.lt_succ_of_le h)) (covers_fRet _)))
  | node c₁ c₂ p₁ p₂ =>
    exact covers_fOr_right (covers_fBind (covers_digest c₁) (covers_fBind (covers_digest c₂)
      (covers_fBind (covers_signed h.1) (covers_fBind (covers_signed h.2) (covers_fRet _)))))

theorem sound_byte : fByte.Sound := sound_fBind (sound_fNat _) fun _ => sound_fRet _

theorem sound_digest : fDigest.Sound := sound_fBind (sound_fListN sound_byte _) fun _ => sound_fRet _

theorem sound_wit : fWit.Sound := by
  have hB : ∀ N, (fBytesLt N).Sound := fun N =>
    sound_fBind (sound_fNat _) fun _ => sound_fBind (sound_fListN sound_byte _) fun _ => sound_fRet _
  have hS : fSigned.Sound := sound_fBind (hB _) fun _ => sound_fBind (sound_fListLe
    (sound_fBind (hB _) fun _ => sound_fBind sound_digest fun _ => sound_fRet _) _) fun _ =>
      sound_fBind (sound_fBind (sound_fNat _) fun _ => sound_fBind (sound_fListN sound_digest _)
        fun _ => sound_fBind (sound_fListN sound_digest _) fun _ => sound_fRet _) fun _ => sound_fRet _
  exact sound_fOr (sound_fBind sound_digest fun _ => sound_fBind (sound_fNat _) fun _ => sound_fRet _)
    (sound_fBind sound_digest fun _ => sound_fBind sound_digest fun _ => sound_fBind hS fun _ =>
      sound_fBind hS fun _ => sound_fRet _)

/-! ## The search -/

/-- **`Rel acc c` decided** (the leaf's chain and statement, or the node's statement and the two
`acc` checks). -/
def relDec (acc : Digest → Signed → Bool) (c : Digest) : Wit → Bool
  | .leaf s n => decide (n ≤ chainCap) && decide (c = leafStmt (chainEnd s n) n)
  | .node c₁ c₂ p₁ p₂ => acc c₁ p₁ && acc c₂ p₂ && decide (c = nodeStmt c₁ c₂)

theorem relDec_iff {acc : Digest → Signed → Bool} {c : Digest} {w : Wit} :
    relDec acc c w = true ↔ Rel acc c w := by
  cases w <;> simp [relDec, Rel, and_comm]

/-- **The search** (B-15's `E_search`): the first witness of `Rel (A vk) c` in the witness space.
Total and computable; never run (its time is that of the space). -/
def search (A : Digest → Digest → Signed → Bool) (vk c : Digest) : Option Wit :=
  fWit fun w => if relDec (A vk) c w then some w else none

variable {A : Digest → Digest → Signed → Bool} {vk c : Digest}

/-- **The search returns only witnesses.** -/
theorem search_sound {w : Wit} (h : search A vk c = some w) : Rel (A vk) c w := by
  obtain ⟨a, ha⟩ := sound_wit _ w h
  by_cases hr : relDec (A vk) c a = true
  · rw [if_pos hr] at ha
    cases ha
    exact relDec_iff.1 hr
  · rw [if_neg hr] at ha; cases ha

/-- **`search_spec`**: if a witness of `Rel (A vk) c` within the bounds exists, the search returns
a witness. -/
theorem search_spec (h : ∃ w, WFits w ∧ Rel (A vk) c w) :
    ∃ w, search A vk c = some w ∧ Rel (A vk) c w := by
  obtain ⟨w, hw, hR⟩ := h
  have := covers_wit hw (fun w => if relDec (A vk) c w then some w else none)
    (by rw [if_pos (relDec_iff.2 hR)]; rfl)
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 this
  exact ⟨w', hw', search_sound hw'⟩

/-- **No witness, no result.** -/
theorem search_none (h : ∀ w, ¬ Rel (A vk) c w) : search A vk c = none := by
  cases hs : search A vk c with
  | none => rfl
  | some w => exact absurd (search_sound hs) (h w)

/-- **`acc` implies the bounds**: a signed proof the contract's `acc` accepts is within them, for
a verifier asking at most `qMax` queries. -/
theorem sFits_of_acc {S : Submission} (hq : S.qV ≤ qMax) {vk c : Digest} {p : Signed}
    (h : S.acc vk c p = true) : SFits p := by
  simp only [Submission.acc, SigOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hπ, ht⟩, hq'⟩, ⟨⟨hi, ho⟩, hp⟩, -⟩, -⟩ := h
  exact ⟨hπ, ht.trans hq, hq', hi, ho, hp⟩

/-- A witness of `Rel acc c` is within the bounds when `acc` implies them. -/
theorem wFits_of_rel {acc : Digest → Signed → Bool} (hA : ∀ c p, acc c p = true → SFits p)
    {w : Wit} (h : Rel acc c w) : WFits w := by
  cases w with
  | leaf s n => exact h.1
  | node c₁ c₂ p₁ p₂ => exact ⟨hA _ _ h.2.1, hA _ _ h.2.2⟩

/-- **`search_spec` for an `acc` that implies the bounds** (the contract's, `sFits_of_acc`). -/
theorem search_spec_acc (hA : ∀ c p, A vk c p = true → SFits p) (h : ∃ w, Rel (A vk) c w) :
    ∃ w, search A vk c = some w ∧ Rel (A vk) c w :=
  search_spec (h.elim fun w hw => ⟨w, wFits_of_rel hA hw, hw⟩)

/-! ## Controls -/

/-- A signed proof within the bounds: the empty proof and trace, a signature of `SigOk`'s shape. -/
def signed₀ (d : Digest) : Signed := ⟨ByteArray.empty, [], ⟨0, List.replicate wotsLen d,
  List.replicate sigHeight d⟩⟩

theorem sFits_signed₀ (d : Digest) : SFits (signed₀ d) := by
  refine ⟨by simp [signed₀], by simp [signed₀], by simp [signed₀], by simp [signed₀, sigHeight],
    by simp [signed₀], by simp [signed₀]⟩

/-- **Positive control**: with an `acc` accepting everything, the search finds a witness of a
node statement. -/
theorem search_acceptAll (vk d : Digest) :
    ∃ w, search (fun _ _ _ => true) vk (nodeStmt d d) = some w ∧
      Rel (fun _ _ => true) (nodeStmt d d) w :=
  search_spec ⟨.node d d (signed₀ d) (signed₀ d), ⟨sFits_signed₀ d, sFits_signed₀ d⟩,
    rfl, rfl, rfl⟩

/-- **Negative control**: with an `acc` rejecting everything, the search returns no node
witness. -/
theorem search_rejectAll_node (vk c c₁ c₂ : Digest) (p₁ p₂ : Signed) :
    search (fun _ _ _ => false) vk c ≠ some (.node c₁ c₂ p₁ p₂) := fun h =>
  Bool.false_ne_true (search_sound h).2.1

/-- A toy test: the leaf `(d, n)` for `n = m`. -/
def toyTest (d : Digest) (m n : ℕ) : Option Wit := if n = m then some (.leaf d n) else none

/-- Kernel-evaluated control (positive): `fNat 3` finds the candidate `1`. -/
theorem toy_found (d : Digest) : fNat 3 (toyTest d 1) = some (.leaf d 1) := rfl

/-- Kernel-evaluated control (negative): `fNat 3` has no candidate `5`. -/
theorem toy_none (d : Digest) : fNat 3 (toyTest d 5) = none := rfl

end Lvm.X
