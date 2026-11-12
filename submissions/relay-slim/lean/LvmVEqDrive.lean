-- New for lvm (WP-14a): V_S's driver (LvmDriver.driveItems) over the schedule's atoms, and two
-- facts of an accepting driver run: its next Fiat–Shamir query (lookahead) and its body cursor's
-- growth (monotonicity).
import LvmVEqShape

/-!
# The driver over atoms

`driveAtoms p π as s k`: `driveItems` with every item cut into its atoms (`LvmVEqShape.atomsOf`):
`driveItems p π its s k = driveAtoms p π (atomsOf p its) s k` (`driveItems_eq`).

On an accepting run (`(driveAtoms p π as s k).runSeq tr = some true`):
* **lookahead** (`drive_next`): if the atoms reach a Fiat–Shamir query before an opening, the
  trace's next entry is that query, `st ‖ π[pend, off + pendA as)` (`pendA`: the bytes the atoms
  read before it);
* **monotonicity** (`drive_mono`): the continuation is reached at a state whose body cursor is at
  least the current one plus the bytes the next atoms read (`pendA`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm

section Drive

variable (p : Params) (π : ByteArray)

/-- **The driver over atoms.** -/
def driveAtoms : List Atom → DSt → (DSt → OProg Bool) → OProg Bool
  | [], s, k => k s
  | .rd :: as, s, k => driveAtoms as { s with off := s.off + eBytes } k
  | .cap c r :: as, s, k =>
    driveAtoms as { s with caps := (r, s.off) :: s.caps, off := s.off + nodeBytes * 2 ^ c } k
  | .sm :: as, s, k => fsQuery π s fun s _ => driveAtoms as s k
  | .pclr :: as, s, k => driveAtoms as { s with pos := [] } k
  | .ps h n :: as, s, k =>
    fsQuery π s fun s a => driveAtoms as { s with pos := s.pos ++ chunk h n (answerBits a) } k
  | .op r :: as, s, k =>
    match capOffset s r with
    | none => .ret false
    | some capOff =>
      if (p.level r).row ≤ queryCap then
        openLoop π (p.level r) capOff s.pos s fun s => driveAtoms as { s with pend := s.off } k
      else .ret false

theorem driveAtoms_reads (as : List Atom) (k : DSt → OProg Bool) :
    ∀ (m : ℕ) (s : DSt), driveAtoms p π (List.replicate m .rd ++ as) s k =
      driveAtoms p π as { s with off := s.off + eBytes * m } k
  | 0, s => by simp
  | m + 1, s => by
    rw [List.replicate_succ, List.cons_append, driveAtoms, driveAtoms_reads as k m]
    congr 2
    simp only [eBytes]; ring

theorem driveAtoms_pos (h : ℕ) (as : List Atom) (k : DSt → OProg Bool) :
    ∀ (n rem : ℕ) (s : DSt), posLoop π h n rem s (fun s ↦ driveAtoms p π as s k) =
      driveAtoms p π (posAtoms h n rem ++ as) s k
  | 0, rem, s => rfl
  | n + 1, rem, s => by
    simp only [posLoop, posAtoms, List.cons_append, driveAtoms, chunk]
    congr 1; funext s' a
    exact driveAtoms_pos h as k n _ _

/-- **`driveItems` is the driver over the atoms.** -/
theorem driveItems_eq : ∀ (its : List Item) (s : DSt) (k : DSt → OProg Bool),
    driveItems p π its s k = driveAtoms p π (atomsOf p its) s k
  | [], s, k => rfl
  | .read m :: its, s, k => by
    rw [atomsOf_cons, itemAtoms, driveAtoms_reads, driveItems, driveItems_eq its]
  | .cap c r :: its, s, k => by
    rw [atomsOf_cons, itemAtoms, driveItems, driveItems_eq its]; rfl
  | .sample :: its, s, k => by
    rw [atomsOf_cons, itemAtoms, driveItems]
    simp only [List.cons_append, List.nil_append, driveAtoms]
    congr 1; funext s' a; exact driveItems_eq its s' k
  | .positions r :: its, s, k => by
    rw [atomsOf_cons, itemAtoms, driveItems, List.cons_append, driveAtoms, ← driveAtoms_pos]
    congr 1; funext s'; exact driveItems_eq its s' k
  | .opening r :: its, s, k => by
    rw [atomsOf_cons, itemAtoms]
    simp only [driveItems, List.cons_append, List.nil_append, driveAtoms]
    cases capOffset s r with
    | none => rfl
    | some capOff =>
      simp only
      split
      · congr 1; funext s'; exact driveItems_eq its _ k
      · rfl

end Drive

/-! ## Lookahead and monotonicity -/

/-- The bytes the atoms read before the next query (a sample, a positions sample, an opening). -/
def pendA : List Atom → ℕ
  | .rd :: as => eBytes + pendA as
  | .cap c _ :: as => nodeBytes * 2 ^ c + pendA as
  | .pclr :: as => pendA as
  | _ => 0

/-- The atoms reach a Fiat–Shamir query (`sm` or `ps`) before an opening or their end. -/
def NextFS : List Atom → Prop
  | .rd :: as => NextFS as
  | .cap _ _ :: as => NextFS as
  | .pclr :: as => NextFS as
  | .sm :: _ => True
  | .ps _ _ :: _ => True
  | _ => False

theorem runSeq_query_cons {q : ByteArray} {k : Digest → OProg Bool} {tr : Trace}
    (h : (OProg.query q k).runSeq tr = some true) :
    ∃ a rest, tr = (q, a) :: rest ∧ (k a).runSeq rest = some true := by
  match tr, h with
  | (q', a) :: rest, h =>
    simp only [OProg.runSeq] at h
    by_cases hq : q' = q
    · subst hq; rw [if_pos rfl] at h; exact ⟨a, rest, rfl, h⟩
    · rw [if_neg hq] at h; exact absurd h (by simp)

/-- **Lookahead**: an accepting run's next entry is the next Fiat–Shamir query. -/
theorem drive_next (p : Params) (π : ByteArray) :
    ∀ (as : List Atom) (s : DSt) (k : DSt → OProg Bool) (tr : Trace), NextFS as →
      (driveAtoms p π as s k).runSeq tr = some true →
      ∃ a rest, tr = (digestBytes s.st ++ π.extract s.pend (s.off + pendA as), a) :: rest
  | .rd :: as, s, k, tr, hn, h => by
    obtain ⟨a, rest, e⟩ := drive_next p π as _ k tr hn h
    exact ⟨a, rest, by rw [e]; simp only [pendA, Nat.add_assoc]⟩
  | .cap c r :: as, s, k, tr, hn, h => by
    obtain ⟨a, rest, e⟩ := drive_next p π as _ k tr hn h
    exact ⟨a, rest, by rw [e]; simp only [pendA, Nat.add_assoc]⟩
  | .pclr :: as, s, k, tr, hn, h => drive_next p π as { s with pos := [] } k tr hn h
  | .sm :: as, s, k, tr, _, h => by
    obtain ⟨a, rest, e, -⟩ := runSeq_query_cons h
    exact ⟨a, rest, by simp [e, pendA]⟩
  | .ps hh n :: as, s, k, tr, _, h => by
    obtain ⟨a, rest, e, -⟩ := runSeq_query_cons h
    exact ⟨a, rest, by simp [e, pendA]⟩

/-! ## What an accepting run consumes -/

theorem ask_run {q : ByteArray} {s : DSt} {k : DSt → Digest → OProg Bool} {tr : Trace}
    (h : (ask q s k).runSeq tr = some true) :
    ∃ a rest, tr = (q, a) :: rest ∧ (k { s with log := (q, a) :: s.log } a).runSeq rest = some true := by
  obtain ⟨a, rest, e, h'⟩ := runSeq_query_cons h
  exact ⟨a, rest, e, h'⟩

theorem drop_succ_cons {e : ByteArray × Digest} {rest : Trace} (n : ℕ) :
    (e :: rest).drop (n + 1) = rest.drop n := rfl

theorem take_succ_cons {e : ByteArray × Digest} {rest : Trace} (n : ℕ) :
    ((e :: rest).take (n + 1)).reverse = (rest.take n).reverse ++ [e] := by simp

/-- Logs compose. -/
theorem log_comp {A : Trace} {n₁ n₂ : ℕ} {L₀ L₁ L₂ : Trace} (h₁ : L₁ = (A.take n₁).reverse ++ L₀)
    (h₂ : L₂ = ((A.drop n₁).take n₂).reverse ++ L₁) : L₂ = (A.take (n₁ + n₂)).reverse ++ L₀ := by
  rw [h₂, h₁, List.take_add, List.reverse_append, List.append_assoc]

/-- A log after one more entry. -/
theorem log_cons {e : ByteArray × Digest} {rest : Trace} {n : ℕ} {L₀ L : Trace}
    (h : L = (rest.take n).reverse ++ e :: L₀) : L = ((e :: rest).take (n + 1)).reverse ++ L₀ := by
  rw [h, take_succ_cons, List.append_assoc]; rfl

/-- A Merkle climb: `j` node queries, each 32 body bytes. -/
theorem climb_run (π : ByteArray) (q : ℕ) : ∀ (j lvl : ℕ) (cur : Digest) (s : DSt)
    (k : DSt → Digest → OProg Bool) (tr : Trace), (climb π q j lvl cur s k).runSeq tr = some true →
    ∃ s' d n, (k s' d).runSeq (tr.drop n) = some true ∧ s'.log = (tr.take n).reverse ++ s.log ∧
      s'.off = s.off + nodeBytes * j ∧ n ≤ tr.length
  | 0, lvl, cur, s, k, tr, h => ⟨s, cur, 0, h, by simp, by simp, by simp⟩
  | j + 1, lvl, cur, s, k, tr, h => by
    rw [climb] at h
    obtain ⟨a, rest, rfl, h'⟩ := ask_run h
    obtain ⟨s', d, n, h1, h2, h3, h4⟩ := climb_run π q j (lvl + 1) a _ k rest h'
    refine ⟨s', d, n + 1, h1, ?_, ?_, by simp; omega⟩
    · exact log_cons h2
    · rw [h3]; simp only [nodeBytes]; ring

/-- An opening: per position a leaf query and a climb. -/
theorem openLoop_run (π : ByteArray) (L : Level) (capOff : ℕ) : ∀ (ps : List ℕ) (s : DSt)
    (k : DSt → OProg Bool) (tr : Trace), (openLoop π L capOff ps s k).runSeq tr = some true →
    ∃ s' n, (k s').runSeq (tr.drop n) = some true ∧ s'.log = (tr.take n).reverse ++ s.log ∧
      s.off ≤ s'.off ∧ n ≤ tr.length
  | [], s, k, tr, h => ⟨s, 0, h, by simp, le_rfl, by simp⟩
  | q :: qs, s, k, tr, h => by
    obtain ⟨a, rest, rfl, h'⟩ := ask_run h
    obtain ⟨s1, d, n1, h1, h2, h3, h4⟩ := climb_run π q L.path 0 a _ _ rest h'
    split at h1
    · obtain ⟨s', n, h5, h6, h7, h8⟩ := openLoop_run π L capOff qs s1 k _ h1
      refine ⟨s', n1 + 1 + n, ?_, ?_, ?_, ?_⟩
      · rw [show n1 + 1 + n = (n1 + n) + 1 by omega, drop_succ_cons, ← List.drop_drop]; exact h5
      · have := log_comp (A := rest) (n₁ := n1) (n₂ := n) (L₀ := (_, a) :: s.log) h2 h6
        rw [show n1 + 1 + n = (n1 + n) + 1 by omega]
        exact log_cons this
      · have : s1.off = s.off + L.row + nodeBytes * L.path := h3
        omega
      · have := List.length_drop (l := rest) (i := n1); simp only [List.length_cons]; omega
    · exfalso
      rcases hd : rest.drop n1 with _ | ⟨e, l⟩ <;> rw [hd] at h1 <;> simp [OProg.runSeq] at h1

theorem runSeq_ret_true {b : Bool} {l : Trace} (h : (OProg.ret b : OProg Bool).runSeq l = some true) :
    l = [] ∧ b = true := by
  rcases l with _ | ⟨e, l⟩
  · simp only [OProg.runSeq, Option.some.injEq] at h; exact ⟨rfl, h⟩
  · simp [OProg.runSeq] at h

/-- **An accepting driver run**: it reaches its continuation at a state that logged the entries it
consumed and whose body cursor moved past the bytes the next atoms read. -/
theorem drive_run (p : Params) (π : ByteArray) : ∀ (as : List Atom) (s : DSt) (k : DSt → OProg Bool)
    (tr : Trace), (driveAtoms p π as s k).runSeq tr = some true →
    ∃ s' n, (k s').runSeq (tr.drop n) = some true ∧ s'.log = (tr.take n).reverse ++ s.log ∧
      s.off + pendA as ≤ s'.off ∧ n ≤ tr.length
  | [], s, k, tr, h => ⟨s, 0, h, by simp, by simp [pendA], by simp⟩
  | .rd :: as, s, k, tr, h => by
    obtain ⟨s', n, h1, h2, h3, h4⟩ := drive_run p π as _ k tr h
    exact ⟨s', n, h1, h2, by simp only [pendA] at h3 ⊢; omega, h4⟩
  | .cap c r :: as, s, k, tr, h => by
    obtain ⟨s', n, h1, h2, h3, h4⟩ := drive_run p π as _ k tr h
    exact ⟨s', n, h1, h2, by simp only [pendA] at h3 ⊢; omega, h4⟩
  | .pclr :: as, s, k, tr, h => by
    obtain ⟨s', n, h1, h2, h3, h4⟩ := drive_run p π as { s with pos := [] } k tr h
    exact ⟨s', n, h1, h2, by simpa [pendA] using h3, h4⟩
  | .sm :: as, s, k, tr, h => by
    rw [driveAtoms, fsQuery] at h
    obtain ⟨a, rest, rfl, h'⟩ := ask_run h
    obtain ⟨s', n, h1, h2, h3, h4⟩ := drive_run p π as _ k rest h'
    exact ⟨s', n + 1, h1, log_cons h2, by simp only [pendA] at h3 ⊢; omega, by simp; omega⟩
  | .ps hh m :: as, s, k, tr, h => by
    rw [driveAtoms, fsQuery] at h
    obtain ⟨a, rest, rfl, h'⟩ := ask_run h
    obtain ⟨s', n, h1, h2, h3, h4⟩ := drive_run p π as _ k rest h'
    exact ⟨s', n + 1, h1, log_cons h2, by simp only [pendA] at h3 ⊢; omega, by simp; omega⟩
  | .op r :: as, s, k, tr, h => by
    simp only [driveAtoms] at h
    split at h
    · exact absurd (runSeq_ret_true h).2 (by simp)
    · split at h
      · obtain ⟨s1, n1, h1, h2, h3, h4⟩ := openLoop_run π _ _ _ _ _ tr h
        obtain ⟨s', n, h5, h6, h7, h8⟩ := drive_run p π as _ k _ h1
        refine ⟨s', n1 + n, by rw [← List.drop_drop]; exact h5, log_comp h2 h6, ?_, ?_⟩
        · simp only [pendA] at h7 ⊢; omega
        · have := List.length_drop (l := tr) (i := n1); omega
      · exact absurd (runSeq_ret_true h).2 (by simp)

end Lvm.VEq
