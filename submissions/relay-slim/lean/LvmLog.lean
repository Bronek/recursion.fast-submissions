-- WP-5 (FS). New for lvm (BLUEPRINT §7.3, A8). After FR's `FRLog` (`Bad`, `bad_step_le`), with
-- every 32-byte window of every query as the referenced digests.
import LvmCompile

/-!
# The bad events of a log

A digest a query *references* is any of its 32-byte windows (`InWins`), for a query of at most
`queryCap` bytes (no verifier asks a longer one). This covers, at once, a Fiat–Shamir state (the
window at offset `0`), a cap node absorbed in a message (BLUEPRINT A8), and the two children of a
Merkle node query.

* **`Bad L`**: a repeated query, a collision (two entries, one answer), or a **window hit**: an
  answer equal to a window of a query asked before it or by the same entry.
* **`bad_step_le`**: on a log with no bad event, at most `|L| + (|L| + 1)·2^20` of the `2^256`
  answers to a fresh query make it bad; **`bad_step_frac`**: at most `badCount = 2^96 + 2^116`
  below `logCap` (a per-query charge of `badCount / 2^256 < 2^-139`).
* `not_bad_of_append`: a prefix of a log without bad events has none.
-/

namespace Lvm.FS

open LeanVM.Parameters LeanVM.Protocol.Compile RecursionFast
open scoped NNReal

/-- `v` is a 32-byte window of the query `q`, of at most `queryCap` bytes. -/
def InWins (v : Digest) (q : ByteArray) : Prop :=
  q.size ≤ queryCap ∧ ∃ k, k + 32 ≤ q.size ∧ v = win q k

/-- *Window hit*: an answer equal to a window of a query asked before it or by the same entry. -/
def WinHit (L : Log) : Prop :=
  ∃ i j : ℕ, ∃ (hij : i ≤ j) (hj : j < L.length), InWins L[j].2 (L[i]'(by omega)).1

/-- **The bad events of a log**: a repeated query, a collision, a window hit. -/
def Bad (L : Log) : Prop := ¬ (L.map Prod.fst).Nodup ∨ ¬ (L.map Prod.snd).Nodup ∨ WinHit L

/-- The bad-answer count below `logCap`. -/
def badCount : ℕ := 2 ^ 96 + 2 ^ 116

theorem not_bad_nil : ¬ Bad [] := by
  rintro (h | h | ⟨i, j, -, hj, -⟩)
  · exact h List.nodup_nil
  · exact h List.nodup_nil
  · simp at hj

/-- A prefix of a log without bad events has none. -/
theorem not_bad_of_append {L L₂ : Log} (h : ¬ Bad (L ++ L₂)) : ¬ Bad L := by
  rintro (h1 | h2 | ⟨i, j, hij, hj, hm⟩)
  · exact h (Or.inl fun hn => h1 (by rw [List.map_append] at hn; exact hn.of_append_left))
  · exact h (Or.inr (Or.inl fun hn => h2 (by rw [List.map_append] at hn; exact hn.of_append_left)))
  · refine h (Or.inr (Or.inr ⟨i, j, hij, by simp; omega, ?_⟩))
    rwa [List.getElem_append_left hj, List.getElem_append_left (by omega)]

/-- The windows of a query, as a finite set. -/
def winsF (q : ByteArray) : Finset Digest :=
  if q.size ≤ queryCap then (Finset.range (q.size - 31)).image (win q) else ∅

theorem mem_winsF {v : Digest} {q : ByteArray} : v ∈ winsF q ↔ InWins v q := by
  unfold winsF InWins
  split_ifs with h
  · simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨h, k, by omega, rfl⟩
    · rintro ⟨-, k, hk, rfl⟩; exact ⟨k, by omega, rfl⟩
  · simp only [Finset.notMem_empty, false_iff]
    rintro ⟨h', -⟩; exact h h'

theorem card_winsF_le (q : ByteArray) : (winsF q).card ≤ 2 ^ 20 := by
  unfold winsF
  split_ifs with h
  · refine Finset.card_image_le.trans ?_
    simp only [Finset.card_range]; unfold queryCap at h; omega
  · simp

set_option linter.constructorNameAsVariable false in
open Classical in
/-- **The bad answers of a fresh query**: at most `|L| + (|L| + 1)·2^20`. -/
theorem bad_step_le {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst) :
    (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card ≤
      L.length + (L.length + 1) * 2 ^ 20 := by
  set A := (L.map Prod.snd).toFinset
  set B := L.toFinset.biUnion fun e => winsF e.1
  set B' := winsF q
  have hA : A.card ≤ L.length := (List.toFinset_card_le _).trans (by simp)
  have hB : B.card ≤ L.length * 2 ^ 20 :=
    (Finset.card_biUnion_le_card_mul _ _ _ fun e _ => card_winsF_le _).trans
      (Nat.mul_le_mul_right _ (List.toFinset_card_le L))
  have hB' : B'.card ≤ 2 ^ 20 := card_winsF_le q
  have hn1 : (L.map Prod.fst).Nodup := by by_contra h; exact hb (Or.inl h)
  have hn2 : (L.map Prod.snd).Nodup := by by_contra h; exact hb (Or.inr (Or.inl h))
  have hw : ¬ WinHit L := fun h => hb (Or.inr (Or.inr h))
  have hsub : (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])) ⊆ A ∪ B ∪ B' := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_union]
    rcases ha with h1 | h2 | ⟨i, j, hij, hj, hm⟩
    · exfalso
      apply h1
      rw [List.map_append, List.nodup_append]
      refine ⟨hn1, by simp, ?_⟩
      intro x hx y hy hxy
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy; subst hxy
      exact hq hx
    · left; left
      by_contra hA'
      apply h2
      rw [List.map_append, List.nodup_append]
      refine ⟨hn2, by simp, ?_⟩
      intro x hx y hy hxy
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
      subst hy; subst hxy
      exact hA' (List.mem_toFinset.mpr hx)
    · have hlen : (L ++ [(q, a)]).length = L.length + 1 := by simp
      rw [hlen] at hj
      by_cases hjL : j < L.length
      · refine absurd ⟨i, j, hij, hjL, ?_⟩ hw
        rwa [List.getElem_append_left hjL, List.getElem_append_left (by omega)] at hm
      · have hj' : j = L.length := by omega
        subst hj'
        rw [List.getElem_concat_length rfl] at hm
        by_cases hiL : i < L.length
        · rw [List.getElem_append_left hiL] at hm
          left; right
          exact Finset.mem_biUnion.mpr ⟨L[i], List.mem_toFinset.mpr (List.getElem_mem hiL),
            mem_winsF.mpr hm⟩
        · have hi' : i = L.length := by omega
          subst hi'
          rw [List.getElem_concat_length rfl] at hm
          right
          exact mem_winsF.mpr hm
  calc (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card
      ≤ (A ∪ B ∪ B').card := Finset.card_le_card hsub
    _ ≤ A.card + B.card + B'.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ L.length + (L.length + 1) * 2 ^ 20 := by nlinarith

open Classical in
/-- **`bad_step_frac`**: below `logCap`, at most `badCount` answers are bad. -/
theorem bad_step_frac {L : Log} {q : ByteArray} (hb : ¬ Bad L) (hq : q ∉ L.map Prod.fst)
    (hl : L.length < logCap) :
    (Finset.univ.filter fun a : Digest => Bad (L ++ [(q, a)])).card ≤ badCount :=
  (bad_step_le hb hq).trans (by unfold logCap at hl; unfold badCount; nlinarith)

/-- The hash term is below `2^-139`. -/
theorem badCount_div_le : (badCount : ℝ≥0) / 2 ^ 256 ≤ (2 : ℝ≥0)⁻¹ ^ 139 := by
  unfold badCount
  rw [div_le_iff₀ (by positivity)]
  norm_num

end Lvm.FS
