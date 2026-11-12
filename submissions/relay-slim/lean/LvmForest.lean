-- WP-5 (FS). New for lvm (BLUEPRINT §7.3). The transcript forest follows FR's `FRLog`
-- (`predIdx`, `back`, `pathOf`) and leanerVM's `ChainLog`/`DecodeChain` in spirit; the reading of a
-- node is the interactive program's, not a fixed item list.
import LvmLog
import Mathlib.Logic.Relation

/-!
# The transcript forest of a log

**Reading a message** (`Step`, `Steps`): from an interactive state `PS` (program, history, the
group's start `hb`, the commitments), a Fiat–Shamir message is read the way the compiled verifier
reads the proof body: a `read` takes 24 bytes (`E` scalar), a `commit` its cap (the word read by
`W`, in the forest `W = wordOf L`), and an opening (`query`) is answered from the history's words
without consuming bytes. A move sets the group's start to the history after it.

**Nodes** (`IsNode L j I`): the entries of `L` that are Fiat–Shamir queries of some transcript,
with their interactive state `I` right after the challenge their answer gives:
* a *seed*: `L[j] = (a₀ ‖ enc x, _)` where an earlier entry is `(q₀, a₀)`; state `P x` at `[]`;
* a *child*: `L[j] = (a ‖ msg, a')` where an earlier node `i` answered `a`, and `msg` reads from
  `i`'s state up to a challenge, with nothing left; state: that challenge `chal a'` taken.
Abandoned branches (several children of one node) are nodes too; the forest is the whole log's.

* `Opens`: openings only (the steps of an empty message).
* **`isNode_unique`**: without bad events a node has one state.
* **`isNode_append`**: without bad events in `L ++ L₂`, the nodes of `L` and their states are
  those of `L ++ L₂` below `|L|` (the first-preimage words are stable, `wordOf_append`).
* **`isNode_new`**: the nodes at a fresh entry are seeds or children of nodes of the old log, read
  with the old log's words.
* **`openAll_rows`** (Merkle): an opening the compiled verifier accepts on the log reads the rows
  of the log's word (no collision suffices).
-/

namespace Lvm.FS

open LeanVM.Parameters LeanVM.Protocol.Compile RecursionFast
open scoped NNReal

/-- An interactive state: program, history, group start, commitments. -/
structure PS where
  p : VerifierProgram Bool
  h : List Ev
  hb : List Ev
  caps : List CapI

namespace Scheme

variable (S : Scheme)

/-- **One step of reading a message** (words of commitments by `W`). -/
inductive Step (W : CapI → Word) : PS × Bytes → PS × Bytes → Prop
  | read {k : E → VerifierProgram Bool} {h hb : List Ev} {caps : List CapI} {msg : Bytes} :
      24 ≤ msg.length →
      Step W (⟨.read k, h, hb, caps⟩, msg)
        (⟨k (S.decE (msg.take 24)), h ++ [.read (S.decE (msg.take 24))],
          h ++ [.read (S.decE (msg.take 24))], caps⟩, msg.drop 24)
  | commit {ht w : ℕ} {k : VerifierProgram Bool} {h hb : List Ev} {caps : List CapI} {msg : Bytes} :
      S.capBytes ht w ≤ msg.length →
      Step W (⟨.commit ht w k, h, hb, caps⟩, msg)
        (⟨k, h ++ [.commit ht w (W (S.capI ht w msg))], h ++ [.commit ht w (W (S.capI ht w msg))],
          caps ++ [S.capI ht w msg]⟩, msg.drop (S.capBytes ht w))
  | «open» {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram Bool} {h hb : List Ev}
      {caps : List CapI} {msg : Bytes} {rows : List (List K)} :
      answer h i ps = some rows →
      Step W (⟨.query i ps k, h, hb, caps⟩, msg) (⟨k rows, h ++ [.query rows], hb, caps⟩, msg)

/-- Reading a message: steps. -/
abbrev Steps (W : CapI → Word) : PS × Bytes → PS × Bytes → Prop :=
  Relation.ReflTransGen (S.Step W)

end Scheme

/-- One opening on a (program, history) pair. -/
inductive OpenStep : VerifierProgram Bool × List Ev → VerifierProgram Bool × List Ev → Prop
  | mk {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram Bool} {h : List Ev}
      {rows : List (List K)} :
      answer h i ps = some rows → OpenStep (.query i ps k, h) (k rows, h ++ [.query rows])

/-- Openings only. -/
abbrev Opens : VerifierProgram Bool × List Ev → VerifierProgram Bool × List Ev → Prop :=
  Relation.ReflTransGen OpenStep

namespace Scheme

variable (S : Scheme)

/-- **A node's state**: its statement and the interactive state after its challenge. -/
structure NI where
  x : S.Stmt
  st : PS

/-- The seed node of a statement. -/
def seedNI (x : S.Stmt) : S.NI := ⟨x, ⟨S.P x, [], [], []⟩⟩

/-- The child state: the challenge of the answer `a` taken at `sample k`. -/
def childNI (x : S.Stmt) (k : E → VerifierProgram Bool) (hs hb : List Ev) (caps : List CapI)
    (a : Digest) : S.NI :=
  ⟨x, ⟨k (S.chal a), hs ++ [.sample (S.chal a)], hb, caps⟩⟩

/-- **The nodes of a log** and their states. -/
inductive IsNode (L : Log) : ℕ → S.NI → Prop
  | seed {r j : ℕ} {a₀ st : Digest} (x : S.Stmt) : r < j → L[r]? = some (toQ S.q0, a₀) →
      L[j]? = some (S.seedQ a₀ x, st) → 32 + (S.enc x).length ≤ queryCap →
      IsNode L j (S.seedNI x)
  | child {i j : ℕ} {I : S.NI} {qi : ByteArray} {ai a : Digest} {msg : Bytes}
      {k : E → VerifierProgram Bool} {hs hb : List Ev} {caps : List CapI} :
      IsNode L i I → i < j → L[i]? = some (qi, ai) →
      L[j]? = some (toQ (ai.toList ++ msg), a) → 32 + msg.length ≤ queryCap →
      S.Steps (S.wordOf L) (I.st, msg) (⟨.sample k, hs, hb, caps⟩, []) →
      IsNode L j (S.childNI I.x k hs hb caps a)

/-- The node continues its group: openings reach a challenge (its continuation query is its own
answer, the empty message). -/
def Cont (I : S.NI) : Prop := ∃ k hs, Opens (I.st.p, I.st.h) (.sample k, hs)

/-- **A seed query** of the old log: `q = a₀ ‖ enc x` after `(q₀, a₀)`. -/
def SeedQ (L : Log) (q : ByteArray) (x : S.Stmt) : Prop :=
  ∃ (r : ℕ) (a₀ : Digest), L[r]? = some (toQ S.q0, a₀) ∧ q = S.seedQ a₀ x ∧ 32 + (S.enc x).length ≤ queryCap

/-- **A child query** of a node `i` of the old log, read with the old log's words. -/
def ChildQ (L : Log) (q : ByteArray) (i : ℕ) (I : S.NI) (msg : Bytes)
    (k : E → VerifierProgram Bool) (hs hb : List Ev) (caps : List CapI) : Prop :=
  S.IsNode L i I ∧ (∃ (qi : ByteArray) (ai : Digest), L[i]? = some (qi, ai) ∧ q = toQ (ai.toList ++ msg)) ∧
    32 + msg.length ≤ queryCap ∧ S.Steps (S.wordOf L) (I.st, msg) (⟨.sample k, hs, hb, caps⟩, [])

/-! ## Log helpers -/

/-- Indices of a log with no collision are determined by answers. -/
theorem idx_eq_of_snd {L : Log} (hn : (L.map Prod.snd).Nodup) {i j : ℕ}
    {e e' : ByteArray × Digest} (hi : L[i]? = some e) (hj : L[j]? = some e') (h : e.2 = e'.2) :
    i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
  have := (List.Nodup.getElem_inj_iff hn (hi := by simpa using hi') (hj := by simpa using hj')).mp
    (by simpa using h)
  exact this

/-- Indices of a log with no repeated query are determined by queries. -/
theorem idx_eq_of_fst {L : Log} (hn : (L.map Prod.fst).Nodup) {i j : ℕ}
    {e e' : ByteArray × Digest} (hi : L[i]? = some e) (hj : L[j]? = some e') (h : e.1 = e'.1) :
    i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj_iff hn (hi := by simpa using hi') (hj := by simpa using hj')).mp
    (by simpa using h)

theorem nodup_fst_of_not_bad {L : Log} (hb : ¬ Bad L) : (L.map Prod.fst).Nodup := by
  by_contra h; exact hb (Or.inl h)

theorem nodup_snd_of_not_bad {L : Log} (hb : ¬ Bad L) : (L.map Prod.snd).Nodup := by
  by_contra h; exact hb (Or.inr (Or.inl h))

/-- A window hit between an earlier-or-equal entry and a later one is bad. -/
theorem not_inWins_of_not_bad {L : Log} (hb : ¬ Bad L) {i j : ℕ} (hij : i ≤ j)
    {e e' : ByteArray × Digest} (hi : L[i]? = some e) (hj : L[j]? = some e') :
    ¬ InWins e'.2 e.1 := by
  intro hw
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  exact hb (Or.inr (Or.inr ⟨i, j, hij, hj', hw⟩))

/-- No answer of a later block is a window of a query of the earlier block. -/
theorem noWin_append {L L₂ : Log} (hb : ¬ Bad (L ++ L₂)) :
    ∀ e' ∈ L₂, ∀ e ∈ L, ¬ InWins e'.2 e.1 := by
  intro e' he' e he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he'
  have hiL : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjL : j < L₂.length := (List.getElem?_eq_some_iff.mp hj).1
  refine not_inWins_of_not_bad hb (i := i) (j := L.length + j) (by omega) ?_ ?_
  · rw [List.getElem?_append_left hiL]; exact hi
  · rw [List.getElem?_append_right (by omega)]; simpa using hj

/-- The first entry answering `v` is not changed by entries that do not answer `v`. -/
theorem findA_append {L L₂ : Log} {v : Digest} (h : ∀ e' ∈ L₂, e'.2 ≠ v) :
    findA (L ++ L₂) v = findA L v := by
  unfold findA
  rw [List.find?_append]
  cases hf : L.find? (fun e => decide (e.2 = v)) with
  | some e => rfl
  | none =>
    simp only [Option.none_or]
    exact List.find?_eq_none.mpr fun x hx => by simpa using h x hx

theorem findA_mem {L : Log} {v : Digest} {e : ByteArray × Digest} (h : findA L v = some e) :
    e ∈ L ∧ e.2 = v :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- With no collision, the first entry answering an entry's answer is the entry. -/
theorem findA_of_mem {L : Log} (hn : (L.map Prod.snd).Nodup) {e : ByteArray × Digest}
    (he : e ∈ L) : findA L e.2 = some e := by
  cases hf : findA L e.2 with
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf e he
    simp at this
  | some e' =>
    obtain ⟨he', h2⟩ := findA_mem hf
    rw [List.inj_on_of_nodup_map hn he' he h2]

/-- A 64-byte query's halves are windows of it. -/
theorem inWins_half {q : ByteArray} (hq : q.size = 64) (c : Prop) [Decidable c] :
    InWins (if c then win q 0 else win q 32) q := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact ⟨by rw [hq]; unfold queryCap; norm_num, 0, by omega, rfl⟩
  · rw [ite_eq_right hc]; exact ⟨by rw [hq]; unfold queryCap; norm_num, 32, by omega, rfl⟩

theorem descend_cases {L : Log} : ∀ (n : ℕ) (v : Digest) (q : ℕ) (d : Digest),
    descend L n v q = some d → d = v ∨ ∃ e ∈ L, InWins d e.1 := by
  intro n
  induction n with
  | zero => intro v q d h; rw [descend, Option.some.injEq] at h; exact Or.inl h.symm
  | succ n ih =>
    intro v q d h
    rw [descend] at h
    cases hf : findA L v with
    | none => rw [hf, Option.bind_none] at h; exact absurd h (by simp)
    | some e =>
      rw [hf, Option.bind_some] at h
      by_cases h64 : e.1.size = 64
      · rw [ite_eq_left h64] at h
        rcases ih _ q d h with rfl | hw
        · exact Or.inr ⟨e, (findA_mem hf).1, inWins_half h64 _⟩
        · exact Or.inr hw
      · rw [ite_eq_right h64] at h; exact absurd h (by simp)

/-- **Stability of the descent.** -/
theorem descend_append {L L₂ : Log} (hL : ∀ e' ∈ L₂, ∀ e ∈ L, ¬ InWins e'.2 e.1) :
    ∀ (n : ℕ) (v : Digest) (q : ℕ), (∀ e' ∈ L₂, e'.2 ≠ v) →
      descend (L ++ L₂) n v q = descend L n v q := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro v q hv
    rw [descend, descend, findA_append hv]
    cases hf : findA L v with
    | none => rfl
    | some e =>
      rw [Option.bind_some, Option.bind_some]
      by_cases h64 : e.1.size = 64
      · rw [ite_eq_left h64, ite_eq_left h64]
        apply ih
        intro e' he' heq
        apply hL e' he' e (findA_mem hf).1
        rw [heq]; exact inWins_half h64 _
      · rw [ite_eq_right h64, ite_eq_right h64]

/-- **Stability of the first-preimage words** (general form). -/
theorem wordOf_append' {L L₂ : Log} (hL : ∀ e' ∈ L₂, ∀ e ∈ L, ¬ InWins e'.2 e.1) (ci : CapI)
    (hci : ∀ v ∈ ci.cap, ∀ e' ∈ L₂, e'.2 ≠ v) : S.wordOf (L ++ L₂) ci = S.wordOf L ci := by
  funext p
  unfold wordOf leafBytes
  congr 1
  cases hv : ci.cap[p % 2 ^ ci.ht / 2 ^ (ci.ht - ci.lv)]? with
  | none => rfl
  | some v =>
    simp only [Option.bind_some]
    have hv' : ∀ e' ∈ L₂, e'.2 ≠ v := hci v (List.mem_of_getElem? hv)
    rw [descend_append hL _ v _ hv']
    cases hd : descend L (ci.ht - ci.lv) v (p % 2 ^ ci.ht) with
    | none => rfl
    | some d =>
      simp only [Option.bind_some]
      rw [findA_append]
      intro e' he' heq
      rcases descend_cases _ _ _ _ hd with rfl | ⟨e, he, hw⟩
      · exact hv' e' he' heq
      · exact hL e' he' e he (heq ▸ hw)

/-- **The first-preimage words are stable**: without bad events in `L ++ L₂`, the word under caps
whose nodes are windows of queries of `L` is the same in both logs. -/
theorem wordOf_append {L L₂ : Log} (hb : ¬ Bad (L ++ L₂)) (ci : CapI)
    (hci : ∀ v ∈ ci.cap, ∃ e ∈ L, InWins v e.1) : S.wordOf (L ++ L₂) ci = S.wordOf L ci :=
  S.wordOf_append' (noWin_append hb) ci fun v hv e' he' heq => by
    obtain ⟨e, he, hw⟩ := hci v hv
    exact noWin_append hb e' he' e he (heq ▸ hw)

/-! ## Reading messages -/

/-- `v` is a 32-byte window of the byte string `m`. -/
def InMsg (v : Digest) (m : Bytes) : Prop := ∃ k, k + 32 ≤ m.length ∧ v = dg (m.drop k)

theorem dg_take_drop (b : Bytes) (n i : ℕ) (h : 32 * i + 32 ≤ n) :
    dg ((b.take n).drop (32 * i)) = dg (b.drop (32 * i)) := by
  unfold dg
  congr 1
  funext j
  have hj := j.isLt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
    List.getElem?_drop, List.getElem?_take, ite_eq_left (show 32 * i + j.val < n by omega)]

/-- The cap nodes of a commitment read from `m` are windows of `m`. -/
theorem capI_inMsg {ht w : ℕ} {m : Bytes} (hm : S.capBytes ht w ≤ m.length) :
    ∀ v ∈ (S.capI ht w m).cap, InMsg v m := by
  intro v hv
  simp only [capI, digestsOf, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  have h1 : 32 * i + 32 ≤ S.capBytes ht w := by
    unfold capBytes; have := Nat.succ_le_of_lt hi; omega
  exact ⟨32 * i, by omega, dg_take_drop m _ i h1⟩

theorem inMsg_drop {v : Digest} {m : Bytes} {d : ℕ} (h : InMsg v (m.drop d)) : InMsg v m := by
  obtain ⟨k, hk, rfl⟩ := h
  refine ⟨d + k, by simp at hk; omega, ?_⟩
  rw [List.drop_drop]

/-- Reading consumes a prefix: every message on the way is a suffix. -/
theorem steps_suffix {W : CapI → Word} {m₀ : Bytes} {x y : PS × Bytes} (h : S.Steps W x y)
    (hx : ∃ d, x.2 = m₀.drop d) : ∃ d, y.2 = m₀.drop d := by
  induction h with
  | refl => exact hx
  | tail _ hst ih =>
    obtain ⟨d, hd⟩ := ih
    cases hst with
    | read hl => exact ⟨d + 24, by simp only at hd ⊢; rw [hd, List.drop_drop]⟩
    | commit hl => exact ⟨d + S.capBytes _ _, by simp only at hd ⊢; rw [hd, List.drop_drop]⟩
    | «open» hr => exact ⟨d, hd⟩

/-- **Words agreeing on the caps a message holds read it the same way.** -/
theorem steps_congrW {W W' : CapI → Word} {m₀ : Bytes}
    (hW : ∀ ci, (∀ v ∈ ci.cap, InMsg v m₀) → W ci = W' ci) {x y : PS × Bytes}
    (h : S.Steps W x y) (hx : ∃ d, x.2 = m₀.drop d) : S.Steps W' x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
    refine Relation.ReflTransGen.tail ih ?_
    obtain ⟨d, hd⟩ := S.steps_suffix hxy hx
    cases hyz with
    | read hl => exact Step.read hl
    | commit hl =>
      rename_i ht w k h hb caps msg
      simp only at hd
      have heq : W (S.capI ht w msg) = W' (S.capI ht w msg) := by
        apply hW
        intro v hv
        have := S.capI_inMsg hl v hv
        rw [hd] at this
        exact inMsg_drop this
      rw [heq]; exact Step.commit hl
    | «open» hr => exact Step.open hr

theorem steps_congrW' {W W' : CapI → Word} {m₀ : Bytes}
    (hW : ∀ ci, (∀ v ∈ ci.cap, InMsg v m₀) → W ci = W' ci) {s t : PS} {m' : Bytes}
    (h : S.Steps W (s, m₀) (t, m')) : S.Steps W' (s, m₀) (t, m') :=
  S.steps_congrW hW h ⟨0, by simp⟩

/-- An empty message reads openings only. -/
theorem steps_nil_iff (W : CapI → Word) (s t : PS) :
    S.Steps W (s, []) (t, []) ↔ Opens (s.p, s.h) (t.p, t.h) ∧ t.hb = s.hb ∧ t.caps = s.caps := by
  constructor
  · intro h
    have key : ∀ y : PS × Bytes, S.Steps W (s, []) y →
        y.2 = [] ∧ Opens (s.p, s.h) (y.1.p, y.1.h) ∧ y.1.hb = s.hb ∧ y.1.caps = s.caps := by
      intro y hy
      induction hy with
      | refl => exact ⟨rfl, Relation.ReflTransGen.refl, rfl, rfl⟩
      | tail _ hst ih =>
        obtain ⟨hm, ho, hhb, hc⟩ := ih
        cases hst with
        | read hl => simp only at hm; subst hm; simp at hl
        | commit hl =>
          simp only at hm; subst hm
          simp only [List.length_nil] at hl; unfold capBytes at hl; simp at hl
        | «open» hr => exact ⟨hm, ho.tail (OpenStep.mk hr), hhb, hc⟩
    obtain ⟨-, h1, h2, h3⟩ := key _ h
    exact ⟨h1, h2, h3⟩
  · rintro ⟨ho, hhb, hc⟩
    obtain ⟨tp, th, thb, tc⟩ := t
    simp only at hhb hc ho
    subst hhb hc
    have key : ∀ y : VerifierProgram Bool × List Ev, Opens (s.p, s.h) y →
        S.Steps W (s, []) (⟨y.1, y.2, s.hb, s.caps⟩, []) := by
      intro y hy
      induction hy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hst ih =>
        cases hst with
        | mk hr => exact ih.tail (Step.open hr)
    exact key _ ho

/-- One reading step is deterministic. -/
theorem step_det {W : CapI → Word} {x y z : PS × Bytes} (h₁ : S.Step W x y) (h₂ : S.Step W x z) :
    y = z := by
  cases h₁ <;> cases h₂ <;> simp_all

/-- A challenge state has no reading step. -/
theorem not_step_sample {W : CapI → Word} {k : E → VerifierProgram Bool} {h hb : List Ev}
    {caps : List CapI} {m : Bytes} {y : PS × Bytes} :
    ¬ S.Step W (⟨.sample k, h, hb, caps⟩, m) y := by
  intro hs; cases hs

/-- **Reading to a challenge is deterministic.** -/
theorem steps_sample_unique {W : CapI → Word} {x : PS × Bytes} {k k' : E → VerifierProgram Bool}
    {h h' hb hb' : List Ev} {caps caps' : List CapI} {m m' : Bytes}
    (h₁ : S.Steps W x (⟨.sample k, h, hb, caps⟩, m))
    (h₂ : S.Steps W x (⟨.sample k', h', hb', caps'⟩, m')) :
    k = k' ∧ h = h' ∧ hb = hb' ∧ caps = caps' ∧ m = m' := by
  have hru : Relator.RightUnique (S.Step W) := fun _ _ _ a b => S.step_det a b
  rcases Relation.ReflTransGen.total_of_right_unique hru h₁ h₂ with h3 | h3
  · rcases h3.cases_head with h4 | ⟨_, h5, -⟩
    · simp only [Prod.mk.injEq, PS.mk.injEq, VerifierProgram.sample.injEq] at h4
      exact ⟨h4.1.1, h4.1.2.1, h4.1.2.2.1, h4.1.2.2.2, h4.2⟩
    · exact absurd h5 S.not_step_sample
  · rcases h3.cases_head with h4 | ⟨_, h5, -⟩
    · simp only [Prod.mk.injEq, PS.mk.injEq, VerifierProgram.sample.injEq] at h4
      exact ⟨h4.1.1.symm, h4.1.2.1.symm, h4.1.2.2.1.symm, h4.1.2.2.2.symm, h4.2.symm⟩
    · exact absurd h5 S.not_step_sample

/-! ## The forest -/

theorem seedQ_size (a₀ : Digest) (x : S.Stmt) : (S.seedQ a₀ x).size = 32 + (S.enc x).length := by
  simp [seedQ]

/-- A node's query has at least the 32 bytes of its state. -/
theorem isNode_size {L : Log} {j : ℕ} {I : S.NI} (h : S.IsNode L j I) :
    ∃ e, L[j]? = some e ∧ 32 ≤ e.1.size := by
  cases h with
  | seed x hr h0 hq hcap => exact ⟨_, hq, by rw [S.seedQ_size]; omega⟩
  | child hI hij hi hq hcap hs => exact ⟨_, hq, by simp⟩

theorem toQ_append_inj {a a' : Digest} {m m' : Bytes} (h : toQ (a.toList ++ m) = toQ (a'.toList ++ m')) :
    a = a' ∧ m = m' := by
  have h' := congrArg qb h
  simp only [qb_toQ] at h'
  obtain ⟨h1, h2⟩ := List.append_inj h' (by simp)
  exact ⟨Vector.toList_inj.mp h1, h2⟩

/-- Without bad events a node has one state. -/
theorem isNode_unique {L : Log} (hb : ¬ Bad L) {j : ℕ} {I I' : S.NI} :
    S.IsNode L j I → S.IsNode L j I' → I = I' := by
  intro h
  induction h generalizing I' with
  | seed x hr h0 hq hcap =>
    intro h'
    cases h' with
    | seed x' hr' h0' hq' hcap' =>
      have hrr := idx_eq_of_fst (nodup_fst_of_not_bad hb) h0 h0' rfl
      subst hrr
      rw [h0] at h0'
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h0'
      subst h0'
      rw [hq] at hq'
      simp only [Option.some.injEq, Prod.mk.injEq] at hq'
      have := (toQ_append_inj hq'.1).2
      rw [S.enc_inj this]
    | child hI' hij' hi' hq' hcap' hs' =>
      exfalso
      rw [hq] at hq'
      simp only [Option.some.injEq, Prod.mk.injEq] at hq'
      have ha := (toQ_append_inj hq'.1).1
      have hri := idx_eq_of_snd (nodup_snd_of_not_bad hb) h0 hi' ha
      subst hri
      obtain ⟨e, he, hsz⟩ := S.isNode_size hI'
      rw [h0] at he
      simp only [Option.some.injEq] at he
      subst he
      simp only [size_toQ] at hsz
      have := S.q0_short
      omega
  | child hI hij hi hq hcap hs ih =>
    intro h'
    cases h' with
    | seed x' hr' h0' hq' hcap' =>
      exfalso
      rw [hq] at hq'
      simp only [Option.some.injEq, Prod.mk.injEq] at hq'
      have ha := (toQ_append_inj hq'.1).1
      have hri := idx_eq_of_snd (nodup_snd_of_not_bad hb) hi h0' ha
      subst hri
      obtain ⟨e, he, hsz⟩ := S.isNode_size hI
      rw [h0'] at he
      simp only [Option.some.injEq] at he
      subst he
      simp only [size_toQ] at hsz
      have := S.q0_short
      omega
    | child hI' hij' hi' hq' hcap' hs' =>
      rw [hq] at hq'
      simp only [Option.some.injEq, Prod.mk.injEq] at hq'
      obtain ⟨ha, hm⟩ := toQ_append_inj hq'.1
      have hii := idx_eq_of_snd (nodup_snd_of_not_bad hb) hi hi' ha
      subst hii
      have hII := ih hI'
      subst hII hm
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := S.steps_sample_unique hs hs'
      rw [hq'.2]

/-- The caps a node's message holds are windows of the node's query. -/
theorem inWins_of_inMsg {a : Digest} {m : Bytes} (hcap : 32 + m.length ≤ queryCap) {v : Digest}
    (h : InMsg v m) : InWins v (toQ (a.toList ++ m)) := by
  obtain ⟨k, hk, rfl⟩ := h
  have hs : (toQ (a.toList ++ m)).size = 32 + m.length := by
    rw [size_toQ, List.length_append, Vector.length_toList]
  refine ⟨by rw [hs]; exact hcap, 32 + k, by rw [hs]; omega, ?_⟩
  unfold win
  rw [qb_toQ, List.drop_append,
    List.drop_eq_nil_of_le (show a.toList.length ≤ 32 + k by rw [Vector.length_toList]; omega),
    List.nil_append, Vector.length_toList, show 32 + k - 32 = k by omega]

theorem isNode_append_aux {L L₂ : Log} {j : ℕ} {I : S.NI}
    (hW : ∀ (a : Digest) (m : Bytes) (e : ByteArray × Digest), e ∈ L →
      e.1 = toQ (a.toList ++ m) → 32 + m.length ≤ queryCap →
      ∀ ci, (∀ v ∈ ci.cap, InMsg v m) → S.wordOf L ci = S.wordOf (L ++ L₂) ci) :
    S.IsNode (L ++ L₂) j I → j < L.length → S.IsNode L j I := by
  intro h
  induction h with
  | seed x hr h0 hq hcap =>
    intro hj
    rw [List.getElem?_append_left (by omega)] at h0
    rw [List.getElem?_append_left hj] at hq
    exact IsNode.seed x hr h0 hq hcap
  | child hI hij hi hq hcap hs ih =>
    intro hj
    have hi' := hi
    rw [List.getElem?_append_left (by omega)] at hi'
    rw [List.getElem?_append_left hj] at hq
    refine IsNode.child (ih (by omega)) hij hi' hq hcap ?_
    exact S.steps_congrW' (fun ci hci =>
      (hW _ _ _ (List.mem_of_getElem? hq) rfl hcap ci hci).symm) hs

theorem isNode_append_aux' {L L₂ : Log} {j : ℕ} {I : S.NI}
    (hW : ∀ (a : Digest) (m : Bytes) (e : ByteArray × Digest), e ∈ L →
      e.1 = toQ (a.toList ++ m) → 32 + m.length ≤ queryCap →
      ∀ ci, (∀ v ∈ ci.cap, InMsg v m) → S.wordOf L ci = S.wordOf (L ++ L₂) ci) :
    S.IsNode L j I → S.IsNode (L ++ L₂) j I := by
  intro h
  induction h with
  | @seed r j a₀ st x hr h0 hq hcap =>
    have hj : j < L.length := (List.getElem?_eq_some_iff.mp hq).1
    have h0' : (L ++ L₂)[r]? = some (toQ S.q0, a₀) := by
      rw [List.getElem?_append_left (by omega)]; exact h0
    have hq' : (L ++ L₂)[j]? = some (S.seedQ a₀ x, st) := by
      rw [List.getElem?_append_left hj]; exact hq
    exact IsNode.seed x hr h0' hq' hcap
  | @child i j I qi ai a msg k hs' hb' caps hI hij hi hq hcap hs ih =>
    have hj : j < L.length := (List.getElem?_eq_some_iff.mp hq).1
    have hi' : (L ++ L₂)[i]? = some (qi, ai) := by
      rw [List.getElem?_append_left (by omega)]; exact hi
    have hq' : (L ++ L₂)[j]? = some (toQ (ai.toList ++ msg), a) := by
      rw [List.getElem?_append_left hj]; exact hq
    exact IsNode.child ih hij hi' hq' hcap (S.steps_congrW' (fun ci hci =>
        hW _ _ _ (List.mem_of_getElem? hq) rfl hcap ci hci) hs)

/-- **The nodes are stable**: below `|L|`, the nodes of `L ++ L₂` are those of `L`. -/
theorem isNode_append {L L₂ : Log} (hb : ¬ Bad (L ++ L₂)) {j : ℕ} (hj : j < L.length) (I : S.NI) :
    S.IsNode (L ++ L₂) j I ↔ S.IsNode L j I := by
  have hW : ∀ (a : Digest) (m : Bytes) (e : ByteArray × Digest), e ∈ L →
      e.1 = toQ (a.toList ++ m) → 32 + m.length ≤ queryCap →
      ∀ ci, (∀ v ∈ ci.cap, InMsg v m) → S.wordOf L ci = S.wordOf (L ++ L₂) ci := by
    intro a m e he heq hcap ci hci
    refine (S.wordOf_append hb ci fun v hv => ⟨e, he, ?_⟩).symm
    rw [heq]; exact inWins_of_inMsg hcap (hci v hv)
  exact ⟨fun h => S.isNode_append_aux hW h hj, S.isNode_append_aux' hW⟩

/-- **The nodes at a fresh entry**: a seed or a child of an old node, with old words. -/
theorem isNode_new {L : Log} {q : ByteArray} {a : Digest} (hb : ¬ Bad (L ++ [(q, a)])) (I : S.NI) :
    S.IsNode (L ++ [(q, a)]) L.length I ↔
      (∃ x, S.SeedQ L q x ∧ I = S.seedNI x) ∨
      (∃ i I₀ msg k hs hb' caps, S.ChildQ L q i I₀ msg k hs hb' caps ∧
        I = S.childNI I₀.x k hs hb' caps a) := by
  have hself : ¬ InWins a q := by
    have := not_inWins_of_not_bad hb (i := L.length) (j := L.length) le_rfl
      List.getElem?_concat_length List.getElem?_concat_length
    simpa using this
  have hW : ∀ (m : Bytes), (∃ ai : Digest, q = toQ (ai.toList ++ m)) → 32 + m.length ≤ queryCap →
      ∀ ci, (∀ v ∈ ci.cap, InMsg v m) → S.wordOf L ci = S.wordOf (L ++ [(q, a)]) ci := by
    rintro m ⟨ai, rfl⟩ hcap ci hci
    refine (S.wordOf_append' (noWin_append hb) ci fun v hv e' he' heq => ?_).symm
    simp only [List.mem_singleton] at he'
    subst he'
    simp only at heq
    apply hself
    rw [heq]
    exact inWins_of_inMsg hcap (hci v hv)
  constructor
  · intro h
    cases h with
    | seed x hr h0 hq hcap =>
      left
      rw [List.getElem?_append_left hr] at h0
      rw [List.getElem?_concat_length] at hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      exact ⟨x, ⟨_, _, h0, hq.1, hcap⟩, rfl⟩
    | child hI hij hi hq hcap hs =>
      right
      rw [List.getElem?_concat_length] at hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨hq1, rfl⟩ := hq
      have hi' := hi
      rw [List.getElem?_append_left hij] at hi'
      refine ⟨_, _, _, _, _, _, _, ⟨(S.isNode_append hb hij _).mp hI, ⟨_, _, hi', hq1⟩, hcap,
        S.steps_congrW' (fun ci hci => (hW _ ⟨_, hq1⟩ hcap ci hci).symm) hs⟩, rfl⟩
  · rintro (⟨x, ⟨r, a₀, h0, rfl, hcap⟩, rfl⟩ | ⟨i, I₀, msg, k, hs, hb', caps,
      ⟨hI, ⟨qi, ai, hi, rfl⟩, hcap, hst⟩, rfl⟩)
    · have hr : r < L.length := (List.getElem?_eq_some_iff.mp h0).1
      exact IsNode.seed x hr (by rw [List.getElem?_append_left hr]; exact h0)
        List.getElem?_concat_length hcap
    · have hi' : i < L.length := (List.getElem?_eq_some_iff.mp hi).1
      exact IsNode.child ((S.isNode_append hb hi' _).mpr hI) hi'
        (by rw [List.getElem?_append_left hi']; exact hi) List.getElem?_concat_length hcap
        (S.steps_congrW' (fun ci hci => hW _ ⟨_, rfl⟩ hcap ci hci) hst)

/-! ## Merkle openings read the log's word -/

/-- One level of descent, at the bottom. -/
def stepDown (L : Log) (d : Digest) (b : ℕ) : Option Digest :=
  (findA L d).bind fun e => if e.1.size = 64 then some (if b = 0 then win e.1 0 else win e.1 32)
    else none

/-- Peel the bottom level of a descent. -/
theorem descend_succ_bottom (L : Log) : ∀ (n : ℕ) (v : Digest) (q : ℕ),
    descend L (n + 1) v q = (descend L n v (q / 2)).bind fun d => stepDown L d (q % 2) := by
  intro n
  induction n with
  | zero =>
    intro v q
    simp only [descend, Option.bind_some, stepDown, pow_zero, Nat.div_one]
  | succ n ih =>
    intro v q
    have hdiv : q / 2 / 2 ^ n = q / 2 ^ (n + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    conv_lhs => rw [descend]
    conv_rhs => rw [descend]
    rw [hdiv]
    cases findA L v with
    | none => rfl
    | some e =>
      rw [Option.bind_some, Option.bind_some]
      by_cases h64 : e.1.size = 64
      · rw [ite_eq_left h64, ite_eq_left h64, ih]
      · rw [ite_eq_right h64, ite_eq_right h64]; rfl

theorem dg_toList_append (d : Digest) (s : Bytes) : dg (d.toList ++ s) = d := by
  unfold dg
  ext i hi
  simp only [Vector.getElem_ofFn, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem dg_toList (d : Digest) : dg d.toList = d := by
  have := dg_toList_append d []
  rwa [List.append_nil] at this

theorem dg_drop_append (d : Digest) (s : Bytes) (hs : s.length = 32) :
    dg ((s ++ d.toList).drop 32) = d := by
  rw [List.drop_left' hs, dg_toList]

/-- **The verifier's climb is the log's descent** (no collision). -/
theorem climb_descend {L : Log} (hc : (L.map Prod.snd).Nodup) : ∀ (n : ℕ) (d : Digest) (q : ℕ)
    (body : Bytes) (top : Digest) (rest : Bytes),
    (climb n d q body).runLog L = some (some (top, rest)) → descend L n top q = some d := by
  intro n
  induction n with
  | zero =>
    intro d q body top rest h
    rw [climb, OProg.runLog, Option.some.injEq, Option.some.injEq, Prod.mk.injEq] at h
    rw [descend, h.1]
  | succ n ih =>
    intro d q body top rest h
    rw [climb] at h
    by_cases hl : body.length < 32
    · rw [ite_eq_left hl] at h; exact absurd h (by simp [OProg.runLog])
    · rw [ite_eq_right hl, OProg.runLog] at h
      cases hf : L.find? (fun e => decide (e.1 = toQ (if q % 2 = 0 then d.toList ++ body.take 32
          else body.take 32 ++ d.toList))) with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some e =>
        rw [hf, Option.bind_some] at h
        have he : e ∈ L := List.mem_of_find?_eq_some hf
        have heq : e.1 = toQ (if q % 2 = 0 then d.toList ++ body.take 32
            else body.take 32 ++ d.toList) := by simpa using List.find?_some hf
        have h1 := ih e.2 (q / 2) _ top rest h
        rw [descend_succ_bottom, h1, Option.bind_some]
        have hlen : (body.take 32).length = 32 := by simp; omega
        have hsz : e.1.size = 64 := by
          rw [heq, size_toQ]
          by_cases hq : q % 2 = 0
          · rw [ite_eq_left hq, List.length_append, Vector.length_toList, hlen]
          · rw [ite_eq_right hq, List.length_append, Vector.length_toList, hlen]
        rw [stepDown, findA_of_mem hc he, Option.bind_some, ite_eq_left hsz]
        congr 1
        by_cases hq : q % 2 = 0
        · rw [ite_eq_left hq]; unfold win; rw [heq, ite_eq_left hq, qb_toQ, List.drop_zero]
          exact dg_toList_append d _
        · rw [ite_eq_right hq]; unfold win; rw [heq, ite_eq_right hq, qb_toQ]
          exact dg_drop_append d _ hlen

/-- **Merkle openings read the log's word**: one position. -/
theorem openOne_row {L : Log} (hc : (L.map Prod.snd).Nodup) (ci : CapI) (p : ℕ)
    (body rest : Bytes) (row : List K)
    (h : (S.openOne ci p body).runLog L = some (some (row, rest))) :
    row = S.wordOf L ci (p % 2 ^ ci.ht) := by
  rw [openOne] at h
  by_cases hl : body.length < 8 * ci.wd
  · rw [ite_eq_left hl] at h; exact absurd h (by simp [OProg.runLog])
  · rw [ite_eq_right hl, OProg.runLog] at h
    cases hf : L.find? (fun e => decide (e.1 = toQ (body.take (8 * ci.wd)))) with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some e =>
      rw [hf, Option.bind_some, OProgFacts.runLog_bind] at h
      have he : e ∈ L := List.mem_of_find?_eq_some hf
      have heq : e.1 = toQ (body.take (8 * ci.wd)) := by simpa using List.find?_some hf
      cases hcl : (climb (ci.ht - ci.lv) e.2 (p % 2 ^ ci.ht) (body.drop (8 * ci.wd))).runLog L with
      | none => rw [hcl] at h; exact absurd h (by simp)
      | some r =>
        rw [hcl, Option.bind_some] at h
        rcases r with _ | ⟨top, rest'⟩
        · exact absurd h (by simp [OProg.runLog])
        · simp only [OProg.runLog] at h
          by_cases hcap : ci.cap[p % 2 ^ ci.ht / 2 ^ (ci.ht - ci.lv)]? = some top
          · rw [ite_eq_left hcap, Option.some.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            have hd := climb_descend hc _ _ _ _ _ _ hcl
            unfold wordOf leafBytes
            rw [Nat.mod_mod, hcap, Option.bind_some, hd, Option.bind_some, findA_of_mem hc he,
              Option.map_some, Option.getD_some, heq, qb_toQ]
          · rw [ite_eq_right hcap] at h; exact absurd h (by simp)

/-- **Merkle openings read the log's word**: an opening the compiled verifier accepts on a log
with no collision gives, at each position, the row the log's word holds there. -/
theorem openAll_rows {L : Log} (hc : (L.map Prod.snd).Nodup) (ci : CapI) : ∀ (ps : List ℕ)
    (body rest : Bytes) (rows : List (List K)),
    (S.openAll ci ps body).runLog L = some (some (rows, rest)) →
    rows = ps.map fun p => S.wordOf L ci (p % 2 ^ ci.ht) := by
  intro ps
  induction ps with
  | nil =>
    intro body rest rows h
    simp only [openAll, OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.1]
  | cons p ps ih =>
    intro body rest rows h
    simp only [openAll] at h
    rw [OProgFacts.runLog_bind] at h
    cases h1 : (S.openOne ci p body).runLog L with
    | none => simp [h1] at h
    | some r =>
      rw [h1, Option.bind_some] at h
      rcases r with _ | ⟨row, rest₁⟩
      · simp [OProg.runLog] at h
      · simp only at h
        rw [OProgFacts.runLog_bind] at h
        cases h2 : (S.openAll ci ps rest₁).runLog L with
        | none => simp [h2] at h
        | some r' =>
          rw [h2, Option.bind_some] at h
          rcases r' with _ | ⟨rs, rest₂⟩
          · simp [OProg.runLog] at h
          · simp only [OProg.runLog, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            rw [List.map_cons, S.openOne_row hc ci p body rest₁ row h1, ih rest₁ rest₂ rs h2]

end Scheme

end Lvm.FS
