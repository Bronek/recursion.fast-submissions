-- new for lvm (WP-9b): kernel-cheap Boolean checks of the lvm instance's layout facts (`LayOk`,
-- `GrpOk`, `InOk`, the tables' shape) and their soundness: structured per table, group and array
-- (offsets laid end to end), never per pair of rows.
import LvmM3Loop
import LvmM3Fid

/-!
# Boolean layout checks

The layout facts of `LvmM3Inst`/`LvmM3Loop` quantify over rows (`GrpOk.disj`/`cover`, `InOk.inj`
over pairs of rows: about `2^36` pairs for P20's stream lanes). Each is implied by a check that
walks the structure once:

* **`tilesB`**: blocks lie end to end from a start to an end (each block starts where the previous
  one ends). It gives: every block inside `[c, N)` (`tiles_mem`), earlier blocks end before later
  ones start (`tiles_pairwise`), every point of `[c, N)` inside a block (`tiles_cover`).
* **`grpOkB`**: each group's members tile its rows `[0, 2^τ)` in list order, each member a piece of
  the group's shape at an offset its height divides, and the members' piece indices, sorted, are
  `0, …, (number of pieces) − 1` (every piece in exactly one place). `grpOk_of_B : grpOkB Q groups = true →
  GrpOk Q groups`.
* **`inOkB`** (`LvmM3CheckIn`): the input arrays tile the input cells.
* **`layOkB`**: every committed column is an aligned block inside its commitment (`LayOk`).
* **`tabsOkB`**: every table reads or seeds (`AllSc`), has a column, and its count columns are
  inside its width (`loop_bus`'s `hin`).

Cost: linear in the members, arrays, columns and reads, plus one sort of the piece indices.
-/

namespace Lvm.M3

open Lvm.Loop

/-! ## Blocks end to end -/

section Tiles

variable {α : Type} (b s : α → ℕ)

/-- **Blocks end to end**: block `a` spans `[b a, b a + s a)`; the blocks of `l` start at `c`, each
where the previous one ends, and the last ends at `N`. -/
def tilesB : List α → ℕ → ℕ → Bool
  | [], c, N => c == N
  | a :: l, c, N => b a == c && tilesB l (c + s a) N

variable {b s}

theorem tiles_cons {a : α} {l : List α} {c N : ℕ} (h : tilesB b s (a :: l) c N = true) :
    b a = c ∧ tilesB b s l (c + s a) N = true := by
  simp only [tilesB, Bool.and_eq_true, beq_iff_eq] at h; exact h

theorem tiles_le : ∀ {l : List α} {c N : ℕ}, tilesB b s l c N = true → c ≤ N
  | [], c, N, h => by simp only [tilesB, beq_iff_eq] at h; omega
  | a :: l, c, N, h => by
    have := tiles_le (tiles_cons h).2; omega

/-- Every block lies inside `[c, N)`. -/
theorem tiles_mem : ∀ {l : List α} {c N : ℕ}, tilesB b s l c N = true →
    ∀ a ∈ l, c ≤ b a ∧ b a + s a ≤ N
  | [], _, _, _, a, ha => by simp at ha
  | a' :: l, c, N, h, a, ha => by
    obtain ⟨h1, h2⟩ := tiles_cons h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨h1.ge, by rw [h1]; exact tiles_le h2⟩
    · have := tiles_mem h2 a ha; omega

/-- Earlier blocks end before later ones start. -/
theorem tiles_pairwise : ∀ {l : List α} {c N : ℕ}, tilesB b s l c N = true →
    l.Pairwise fun a a' ↦ b a + s a ≤ b a'
  | [], _, _, _ => List.Pairwise.nil
  | a :: l, c, N, h => by
    obtain ⟨h1, h2⟩ := tiles_cons h
    refine List.Pairwise.cons (fun a' ha' ↦ ?_) (tiles_pairwise h2)
    have := (tiles_mem h2 a' ha').1; omega

/-- Every point of `[c, N)` lies in a block. -/
theorem tiles_cover : ∀ {l : List α} {c N : ℕ}, tilesB b s l c N = true →
    ∀ e, c ≤ e → e < N → ∃ a ∈ l, b a ≤ e ∧ e < b a + s a
  | [], c, N, h, e, h1, h2 => by simp only [tilesB, beq_iff_eq] at h; omega
  | a :: l, c, N, h, e, h1, h2 => by
    obtain ⟨ha, hl⟩ := tiles_cons h
    by_cases he : e < c + s a
    · exact ⟨a, List.mem_cons_self .., by omega, by omega⟩
    · obtain ⟨a', ha', h3⟩ := tiles_cover hl e (by omega) h2
      exact ⟨a', List.mem_cons_of_mem _ ha', h3⟩

/-- A tiling depends on the sizes of its blocks only. -/
theorem tilesB_congr {s' : α → ℕ} : ∀ {l : List α} {c N : ℕ}, (∀ a ∈ l, s a = s' a) →
    tilesB b s l c N = tilesB b s' l c N
  | [], _, _, _ => rfl
  | a :: l, c, N, h => by
    simp only [tilesB, h a List.mem_cons_self,
      tilesB_congr (l := l) fun a' ha' ↦ h a' (List.mem_cons_of_mem _ ha')]

/-- Two blocks of a tiling holding the same point are the same block. -/
theorem tiles_unique {l : List α} {c N : ℕ} (h : tilesB b s l c N = true) {a a' : α}
    (ha : a ∈ l) (ha' : a' ∈ l) {y : ℕ} (hy : b a ≤ y ∧ y < b a + s a)
    (hy' : b a' ≤ y ∧ y < b a' + s a') : a = a' := by
  have hp := List.pairwise_iff_getElem.mp (tiles_pairwise h)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem ha'
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
  · have := hp i i' hi hi' hlt; omega
  · rfl
  · have := hp i' i hi' hi hlt; omega

end Tiles

/-! ## Kernel-cheap lookups and permutations -/

/-- A binary trie keyed by `ℕ` (Braun order: `0` the root, odd `n` in the left subtrie at `n / 2`,
even `n ≥ 2` in the right one at `n / 2 − 1`): `O(log n)` lookups the kernel reduces quickly. -/
inductive NTrie (α : Type) where
  | nil : NTrie α
  | node (v : Option α) (l r : NTrie α) : NTrie α

namespace NTrie

variable {α : Type}

/-- The entry at key `n`. -/
def get? : NTrie α → ℕ → Option α
  | .nil, _ => none
  | .node v l r, n => if n = 0 then v else if n % 2 = 1 then l.get? (n / 2) else r.get? (n / 2 - 1)

/-- The root's entry and subtries. -/
def parts : NTrie α → Option α × NTrie α × NTrie α
  | .nil => (none, .nil, .nil)
  | .node v l r => (v, l, r)

/-- Set key `n` to `a` (`f` bounds the depth: keys `n + 1 < 2^f`). -/
def ins (a : α) : ℕ → NTrie α → ℕ → NTrie α
  | 0, t, _ => t
  | f + 1, t, n =>
    if n = 0 then .node (some a) t.parts.2.1 t.parts.2.2
    else if n % 2 = 1 then .node t.parts.1 (ins a f t.parts.2.1 (n / 2)) t.parts.2.2
    else .node t.parts.1 t.parts.2.1 (ins a f t.parts.2.2 (n / 2 - 1))

theorem get?_parts (t : NTrie α) (n : ℕ) :
    t.get? n = (NTrie.node t.parts.1 t.parts.2.1 t.parts.2.2).get? n := by
  cases t <;> simp [get?, parts]

theorem get?_ins (a : α) : ∀ (f : ℕ) (t : NTrie α) (n m : ℕ), n + 1 < 2 ^ f →
    (t.ins a f n).get? m = if m = n then some a else t.get? m
  | 0, _, n, _, h => by simp at h
  | f + 1, t, n, m, h => by
    rw [get?_parts t m]
    simp only [ins]
    by_cases hn : n = 0
    · subst hn; by_cases hm : m = 0 <;> simp [get?, hm]
    by_cases hp : n % 2 = 1
    · simp only [hn, hp, if_false, if_true, get?]
      have hf : n / 2 + 1 < 2 ^ f := by rw [pow_succ] at h; omega
      by_cases hm : m = 0
      · subst hm; simp only [get?, if_true]; rw [if_neg (fun h' : 0 = n ↦ hn h'.symm)]
      by_cases hq : m % 2 = 1
      · rw [get?_ins a f _ _ _ hf]; simp only [hm, hq, if_false, if_true]
        by_cases he : m / 2 = n / 2
        · have : m = n := by omega
          simp [he, this]
        · have : m ≠ n := fun h' ↦ he (by rw [h'])
          simp [he, this]
      · have : m ≠ n := by omega
        simp [hm, hq, this]
    · simp only [hn, hp, if_false, get?]
      have hf : n / 2 - 1 + 1 < 2 ^ f := by rw [pow_succ] at h; omega
      by_cases hm : m = 0
      · subst hm; simp only [get?, if_true]; rw [if_neg (fun h' : 0 = n ↦ hn h'.symm)]
      by_cases hq : m % 2 = 1
      · have : m ≠ n := by omega
        simp [hm, hq, this]
      · rw [get?_ins a f _ _ _ hf]; simp only [hm, hq, if_false]
        by_cases he : m / 2 - 1 = n / 2 - 1
        · have : m = n := by omega
          simp [he, this]
        · have : m ≠ n := fun h' ↦ he (by rw [h'])
          simp [he, this]

/-- The trie of a list from key `k` on. -/
def ofListFrom : List α → ℕ → NTrie α → NTrie α
  | [], _, t => t
  | a :: l, k, t => ofListFrom l (k + 1) (t.ins a 64 k)

/-- The trie of a list: entry `n` at key `n`. -/
def ofList (l : List α) : NTrie α := ofListFrom l 0 .nil

theorem get?_ofListFrom : ∀ (l : List α) (k : ℕ) (t : NTrie α), k + l.length < 2 ^ 64 →
    ∀ m, (ofListFrom l k t).get? m = if k ≤ m ∧ m < k + l.length then l[m - k]? else t.get? m
  | [], k, t, _, m => by simp [ofListFrom]
  | a :: l, k, t, h, m => by
    simp only [ofListFrom, List.length_cons] at h ⊢
    rw [get?_ofListFrom l (k + 1) _ (by omega), get?_ins a 64 t k m (by omega)]
    by_cases h1 : k + 1 ≤ m ∧ m < k + 1 + l.length
    · rw [if_pos h1, if_pos ⟨by omega, by omega⟩,
        show m - k = (m - (k + 1)) + 1 by omega, List.getElem?_cons_succ]
    · rw [if_neg h1]
      by_cases hm : m = k
      · subst hm; simp
      · rw [if_neg hm, if_neg (by omega)]

theorem get?_ofList (l : List α) (h : l.length < 2 ^ 64) (n : ℕ) : (ofList l).get? n = l[n]? := by
  rw [ofList, get?_ofListFrom l 0 .nil (by omega)]
  by_cases hn : n < l.length
  · simp [hn]
  · rw [if_neg (by omega), List.getElem?_eq_none (by omega)]; rfl

end NTrie

/-- Mark each index of `l` in the bitmask `m`: `none` if one is out of range or repeats. -/
def markAll (N : ℕ) : List ℕ → ℕ → Option ℕ
  | [], m => some m
  | n :: l, m => if n < N ∧ m.testBit n = false then markAll N l (m ||| 1 <<< n) else none

theorem testBit_one_shl (n i : ℕ) : (1 <<< n).testBit i = decide (i = n) := by
  simp only [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_decide]; exact eq_comm

/-- What `markAll` checks: the indices are in range, new, distinct, and the result marks them. -/
theorem markAll_spec (N : ℕ) : ∀ (l : List ℕ) (m m' : ℕ), markAll N l m = some m' →
    l.Nodup ∧ (∀ x ∈ l, m.testBit x = false) ∧ ∀ i, m'.testBit i = (m.testBit i || decide (i ∈ l))
  | [], m, m', h => by simp only [markAll, Option.some.injEq] at h; subst h; simp
  | n :: l, m, m', h => by
    simp only [markAll] at h
    split at h
    · rename_i hc
      obtain ⟨hnd, hnew, hbits⟩ := markAll_spec N l _ m' h
      have hn : n ∉ l := fun hn ↦ by
        have := hnew n hn; simp [Nat.testBit_or, testBit_one_shl] at this
      refine ⟨List.nodup_cons.mpr ⟨hn, hnd⟩, fun x hx ↦ ?_, fun i ↦ ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hc.2
        · have := hnew x hx; simp only [Nat.testBit_or, Bool.or_eq_false_iff] at this; exact this.1
      · rw [hbits i, Nat.testBit_or, testBit_one_shl]
        by_cases hi : i = n <;> simp [hi]
    · simp at h

/-- **A permutation of `0, …, N − 1`, by bitmask**: marking every index of `l` from `0` gives
`2^N − 1` exactly when `l` lists each index below `N` once. -/
theorem nodup_mem_of_markAll {N : ℕ} {l : List ℕ} (h : markAll N l 0 = some (2 ^ N - 1)) :
    l.Nodup ∧ ∀ n < N, n ∈ l := by
  obtain ⟨hnd, -, hbits⟩ := markAll_spec N l 0 _ h
  refine ⟨hnd, fun n hn ↦ ?_⟩
  have := hbits n
  rw [Nat.testBit_two_pow_sub_one, Nat.zero_testBit, Bool.false_or] at this
  simpa [hn] using this

/-! ## Groups -/

/-- What the groups' check needs of a piece: its shape and log-height. -/
def pinfo (Q : Program) (p : Piece) : Loop.Shape × ℕ := (p.shape, Q.height p)

/-- **The groups' check on the pieces' shapes and log-heights** `info` (one entry per piece): each
group's members tile `[0, 2^τ)` in list order, each a piece of the group's shape at an offset its
height divides; the members' piece indices mark every piece once (`markAll`, a bitmask). Lookups
go through a trie (`NTrie`, `O(log n)`): list lookups and an insertion sort cost the kernel tens of
seconds at ~700 pieces. -/
def grpOkCore (info : List (Loop.Shape × ℕ)) (groups : List Grp) : Bool :=
  let tr := NTrie.ofList info
  groups.all (fun g ↦ tilesB (·.2) (fun m ↦ 2 ^ ((tr.get? m.1).getD default).2) g.mem 0 (2 ^ g.τ) &&
    g.mem.all fun m ↦ match tr.get? m.1 with
      | some sh => decide (sh.1 = g.σ) && m.2 % 2 ^ sh.2 == 0
      | none => false) &&
  decide (info.length < 2 ^ 64) &&
  markAll info.length (groups.flatMap fun g ↦ g.mem.map (·.1)) 0 == some (2 ^ info.length - 1)

/-- **The groups' Boolean check** of a program. For a large program, decide
`Q.pieces.map (pinfo Q) = info` once (the cost of `Q.pieces` in the kernel) and `grpOkCore info
groups` on literals (`grpOk_of_core`). -/
def grpOkB (Q : Program) (groups : List Grp) : Bool := grpOkCore (Q.pieces.map (pinfo Q)) groups

/-- The member `m`'s height. -/
def memSize (Q : Program) (m : ℕ × ℕ) : ℕ := 2 ^ Q.height (Q.pieces.getD m.1 default)

theorem holds_iff (Q : Program) (m : ℕ × ℕ) (y : ℕ) :
    Grp.Holds Q m y = true ↔ m.2 ≤ y ∧ y < m.2 + memSize Q m := by
  simp [Grp.Holds, memSize]

theorem memSize_eq (Q : Program) {m : ℕ × ℕ} (h : m.1 < Q.pieces.length) :
    2 ^ (((Q.pieces.map (pinfo Q))[m.1]?).getD default).2 = memSize Q m := by
  simp [memSize, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, pinfo]

/-- **The groups' check gives `GrpOk`.** -/
theorem grpOk_of_B {Q : Program} {groups : List Grp} (h : grpOkB Q groups = true) :
    GrpOk Q groups := by
  simp only [grpOkB, grpOkCore, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.length_map] at h
  obtain ⟨⟨hg1, hlen⟩, hmark⟩ := h
  have hget : ∀ n, (NTrie.ofList (Q.pieces.map (pinfo Q))).get? n = (Q.pieces.map (pinfo Q))[n]? :=
    fun n ↦ NTrie.get?_ofList _ (by simpa using hlen) n
  simp only [hget] at hg1
  have hg0 := hg1
  have hg : ∀ g ∈ groups, tilesB (·.2) (memSize Q) g.mem 0 (2 ^ g.τ) = true ∧
      ∀ m ∈ g.mem, (match (Q.pieces.map (pinfo Q))[m.1]? with
        | some sh => decide (sh.1 = g.σ) && m.2 % 2 ^ sh.2 == 0
        | none => false) = true := by
    intro g hgm
    obtain ⟨ht, hall⟩ := hg0 g hgm
    refine ⟨?_, hall⟩
    rw [← ht]
    refine (tilesB_congr fun m hm ↦ (memSize_eq Q ?_).symm)
    have := hall m hm
    rcases Nat.lt_or_ge m.1 Q.pieces.length with h | h
    · exact h
    · rw [List.getElem?_eq_none (by simpa using h)] at this; simp at this
  obtain ⟨hnd, hall'⟩ := nodup_mem_of_markAll hmark
  refine ⟨fun g hgm m hm ↦ ?_, fun g hgm m hm m' hm' y h1 h2 ↦ ?_, fun g hgm y hy ↦ ?_,
    fun n hn ↦ ?_, fun i i' hi hi' n off off' h1 h2 ↦ ?_, fun g hgm ↦ ?_⟩
  · obtain ⟨ht, hall⟩ := hg g hgm
    have hmm := hall m hm
    rw [List.getElem?_map] at hmm
    cases hp : Q.pieces[m.1]? with
    | none => simp [hp] at hmm
    | some p =>
      simp only [hp, Option.map_some, pinfo, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hmm
      have hpd : Q.pieces.getD m.1 default = p := by simp [List.getD_eq_getElem?_getD, hp]
      have hin := (tiles_mem ht m hm).2
      simp only [memSize, hpd] at hin
      exact ⟨p, rfl, hmm.1, hin, Nat.dvd_of_mod_eq_zero hmm.2⟩
  · obtain ⟨ht, -⟩ := hg g hgm
    exact tiles_unique ht hm hm' ((holds_iff Q m y).mp h1) ((holds_iff Q m' y).mp h2)
  · obtain ⟨ht, -⟩ := hg g hgm
    obtain ⟨m, hm, hy'⟩ := tiles_cover ht y (Nat.zero_le _) hy
    exact ⟨m, hm, (holds_iff Q m y).mpr hy'⟩
  · have hmem : n ∈ groups.flatMap fun g ↦ g.mem.map (·.1) := hall' n hn
    obtain ⟨g, hgm, hn'⟩ := List.mem_flatMap.mp hmem
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hgm
    exact ⟨i, hi, m.2, hm⟩
  · -- one place: the piece index appears once in the concatenation
    have hpw := (List.nodup_flatMap.mp hnd).2
    rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
    · have hd := List.pairwise_iff_getElem.mp hpw i i' hi hi' hlt
      exact absurd (List.mem_map_of_mem (f := (·.1)) h2) (hd (List.mem_map_of_mem (f := (·.1)) h1))
    · refine ⟨rfl, ?_⟩
      have hnd1 := (List.nodup_flatMap.mp hnd).1 _ (List.getElem_mem hi)
      obtain ⟨k, hk, hke⟩ := List.getElem_of_mem h1
      obtain ⟨k', hk', hke'⟩ := List.getElem_of_mem h2
      have hkk : k = k' := by
        have e1 : (groups[i].mem.map (·.1))[k]'(by simpa using hk) = n := by simp [hke]
        have e2 : (groups[i].mem.map (·.1))[k']'(by simpa using hk') = n := by simp [hke']
        exact (List.Nodup.getElem_inj_iff hnd1).mp (e1.trans e2.symm)
      subst hkk
      have := hke.symm.trans hke'
      simp only [Prod.mk.injEq] at this
      exact this.2
    · have hd := List.pairwise_iff_getElem.mp hpw i' i hi' hi hlt
      exact absurd (List.mem_map_of_mem (f := (·.1)) h1) (hd (List.mem_map_of_mem (f := (·.1)) h2))
  · -- members strictly increase in offset (each block has at least one row)
    obtain ⟨ht, -⟩ := hg g hgm
    exact (tiles_pairwise ht).imp fun {m m'} hle heq ↦ by
      subst heq; have : 0 < memSize Q m := Nat.two_pow_pos _; omega

/-- **The groups' check on literals**: the pieces' information, decided once, and the check on it. -/
theorem grpOk_of_core {Q : Program} {groups : List Grp} {info : List (Loop.Shape × ℕ)}
    (hinfo : Q.pieces.map (pinfo Q) = info) (h : grpOkCore info groups = true) : GrpOk Q groups :=
  grpOk_of_B (by rw [grpOkB, hinfo]; exact h)

/-! ## Committed columns aligned -/

/-- A column's alignment, as a Boolean. -/
def colOkB (L : Lay) (τ : ℕ) : ColSrc → Bool
  | .com rec off => off % 2 ^ τ == 0 && decide (off + 2 ^ τ ≤ 2 ^ (if rec then L.nuRec else L.nuMain)) &&
      decide (L.nuRec ≤ L.nuMain)
  | .fix _ _ => true

/-- **The layout's Boolean check**: every committed column is an aligned block inside its
commitment. -/
def layOkB (L : Lay) (tabs : List Tab) : Bool := tabs.all fun t ↦ t.cols.all (colOkB L t.τ)

/-- **The layout's check gives `LayOk`.** -/
theorem layOk_of_B {L : Lay} {tabs : List Tab} (h : layOkB L tabs = true) : LayOk L tabs := by
  intro t ht i hi
  simp only [layOkB, List.all_eq_true] at h
  have hc := h t ht _ (List.getElem_mem hi)
  unfold Aligned
  rw [List.getElem?_eq_getElem hi]
  revert hc
  cases t.cols[i] with
  | com rec off =>
    simp only [colOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨Nat.dvd_of_mod_eq_zero h1, h2, h3⟩
  | fix f ev => exact fun _ ↦ trivial

/-! ## The tables' shape -/

/-- **The tables' Boolean check**: every table reads or seeds, has a column, its read-count
columns are inside its width, and every key has at most 13 value limbs (the fingerprint's 16
coordinates: separator, address, count, values; `LvmM3FidBus.KeysOk`). -/
def tabsOkB (tabs : List Tab) : Bool :=
  tabs.all fun t ↦ (!t.reads.isEmpty || !t.seeds.isEmpty) && decide (0 < t.w) &&
    t.reads.all (fun r ↦ decide (r.2 < t.w)) &&
    t.reads.all (fun r ↦ decide (r.1.val.length ≤ 13)) && t.seeds.all fun s ↦ decide (s.1.val.length ≤ 13)

theorem allSc_of_B {tabs : List Tab} (h : tabsOkB tabs = true) : AllSc tabs := by
  intro t ht
  simp only [tabsOkB, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff] at h
  exact (h t ht).1.1.1.1

theorem width_pos_of_B {tabs : List Tab} (h : tabsOkB tabs = true) : ∀ t ∈ tabs, 0 < t.w := by
  intro t ht
  simp only [tabsOkB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h t ht).1.1.1.2

theorem counts_of_B {tabs : List Tab} (h : tabsOkB tabs = true) : ∀ t ∈ tabs, ∀ r ∈ t.reads, r.2 < t.w := by
  intro t ht r hr
  simp only [tabsOkB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h t ht).1.1.2 r hr

/-- The keys' limb counts (`LvmM3FidBus.KeysOk`, unfolded). -/
theorem keys_of_B {tabs : List Tab} (h : tabsOkB tabs = true) :
    ∀ t ∈ tabs, (∀ r ∈ t.reads, r.1.val.length ≤ 13) ∧ ∀ s ∈ t.seeds, s.1.val.length ≤ 13 := by
  intro t ht
  simp only [tabsOkB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(h t ht).1.2, (h t ht).2⟩

end Lvm.M3
