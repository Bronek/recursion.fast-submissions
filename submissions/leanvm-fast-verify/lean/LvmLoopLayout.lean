import LvmLoopTable
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# LoopIR layout facts

The arithmetic of the dense allocation: loop indices and their flattening, the read bound
`maxExcess`, the instance list (membership, closed-form clocks, the clock chain the interpreter
follows), and the program check read back per instance. Proof-help lemmas for `LvmLoopInterp` and
`LvmLoopSound`; nothing here is load-bearing on its own.
-/

namespace Lvm.Loop

/-! ## Loop indices -/

/-- A loop index lies in the box of `dims`. -/
def InBox : List Nat → List Nat → Prop
  | [], [] => True
  | d :: ds, j :: js => j < 2 ^ d ∧ InBox ds js
  | _, _ => False

theorem unflat_inBox : ∀ (ds : List Nat) (n : Nat), InBox ds (unflat ds n)
  | [], _ => trivial
  | d :: ds, n => ⟨Nat.mod_lt _ (Nat.two_pow_pos d), unflat_inBox ds _⟩

theorem flat_unflat : ∀ (ds : List Nat) (n : Nat), flat ds (unflat ds n) = n % 2 ^ ds.sum
  | [], n => by simp [flat, unflat, Nat.mod_one]
  | d :: ds, n => by
    simp only [unflat, flat, flat_unflat ds, List.sum_cons, Nat.pow_add]
    rw [Nat.mod_mul]

theorem flat_unflat_of_lt (ds : List Nat) {n : Nat} (h : n < 2 ^ ds.sum) :
    flat ds (unflat ds n) = n := by
  rw [flat_unflat, Nat.mod_eq_of_lt h]

/-- **The read bound**: on the box, `dot s j ≤ maxExcess s D w + w · flat D j`. -/
theorem dot_le_maxExcess : ∀ (s D j : List Nat) (w : Nat), InBox D j →
    dot s j ≤ maxExcess s D w + w * flat D j
  | [], _, _, _, _ => by simp [dot]
  | _ :: _, [], [], _, _ => by simp [dot]
  | _ :: _, [], _ :: _, _, h => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim
  | s :: ss, d :: ds, j :: js, w, ⟨hj, h⟩ => by
    have ih := dot_le_maxExcess ss ds js (w * 2 ^ d) h
    simp only [dot, maxExcess, flat]
    have hj' : j ≤ 2 ^ d - 1 := by omega
    have h1 : s * j ≤ (s - w) * (2 ^ d - 1) + w * j := by
      calc s * j ≤ ((s - w) + w) * j := Nat.mul_le_mul_right _ (by omega)
        _ = (s - w) * j + w * j := by ring
        _ ≤ (s - w) * (2 ^ d - 1) + w * j := by
          have := Nat.mul_le_mul_left (s - w) hj'
          omega
    have h2 : w * (j + 2 ^ d * flat ds js) = w * j + w * 2 ^ d * flat ds js := by ring
    rw [h2]
    omega

/-! ## Template instances -/

/-- Writes of memory `τ` among the rows. -/
def rowsW (τ : Ty) (rs : List Row) : Nat := (rs.map (Row.w τ)).sum

theorem mem_tplInsts {b jf : Nat} {j : List Nat} :
    ∀ (rs : List Row) (t k e : Nat) (i : Inst), i ∈ tplInsts b jf j t k e rs ↔
      ∃ m < rs.length, i = ⟨b, jf, j, t + m, rs.getD m default, k + rowsW .K (rs.take m),
        e + rowsW .E (rs.take m)⟩
  | [], _, _, _, _ => by simp [tplInsts]
  | r :: rs, t, k, e, i => by
    simp only [tplInsts, List.mem_cons, mem_tplInsts rs]
    constructor
    · rintro (h | ⟨m, hm, rfl⟩)
      · exact ⟨0, by simp, by simp [h, rowsW]⟩
      · refine ⟨m + 1, by simp; omega, ?_⟩
        simp [rowsW, List.take_succ_cons, Nat.add_assoc, Nat.add_comm 1 m]
    · rintro ⟨m, hm, rfl⟩
      cases m with
      | zero => left; simp [rowsW]
      | succ m =>
        right
        refine ⟨m, by simpa using hm, ?_⟩
        simp [rowsW, List.take_succ_cons, Nat.add_assoc, Nat.add_comm 1 m]

/-- The rank is the writes of the first rows. -/
theorem Block.rank_eq (B : Block) (τ : Ty) (t : Nat) : B.rank τ t = rowsW τ (B.tpl.take t) := rfl

namespace Program

variable (Q : Program)

theorem blk_eq {b : Nat} (hb : b < Q.blocks.length) : Q.blk b = Q.blocks[b] := by
  simp [blk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]

theorem mem_blockInsts (b : Nat) (i : Inst) :
    i ∈ Q.blockInsts b (Q.blk b) ↔
      ∃ jf < (Q.blk b).size, ∃ t < (Q.blk b).tpl.length, i = Q.inst b jf t := by
  simp only [blockInsts, List.mem_flatMap, List.mem_range, mem_tplInsts, inst]
  constructor
  · rintro ⟨jf, hjf, m, hm, rfl⟩
    exact ⟨jf, hjf, m, hm, by simp [Block.rank_eq, Nat.add_assoc]⟩
  · rintro ⟨jf, hjf, t, ht, rfl⟩
    exact ⟨jf, hjf, t, ht, by simp [Block.rank_eq, Nat.add_assoc]⟩

/-- **Membership in the instance list**: exactly the closed-form instances of valid triples. -/
theorem mem_insts (i : Inst) :
    i ∈ Q.insts ↔ ∃ b < Q.blocks.length, ∃ jf < (Q.blk b).size, ∃ t < (Q.blk b).tpl.length,
      i = Q.inst b jf t := by
  simp only [insts, List.mem_flatMap, List.mem_range, mem_blockInsts]

end Program

/-! ## The clock chain -/

/-- The clocks of a list of instances start at `k`, `e` and advance by each instance's writes. -/
def Chain : Nat → Nat → List Inst → Prop
  | _, _, [] => True
  | k, e, i :: L => i.ck = k ∧ i.ce = e ∧ Chain (k + i.row.w .K) (e + i.row.w .E) L

/-- Writes of memory `τ` among instances. -/
def instW (τ : Ty) (L : List Inst) : Nat := (L.map fun i => i.row.w τ).sum

theorem chain_append : ∀ (L₁ L₂ : List Inst) (k e : Nat),
    Chain k e (L₁ ++ L₂) ↔ Chain k e L₁ ∧ Chain (k + instW .K L₁) (e + instW .E L₁) L₂
  | [], L₂, k, e => by simp [Chain, instW]
  | i :: L₁, L₂, k, e => by
    simp only [List.cons_append, Chain, chain_append L₁ L₂, instW, List.map_cons, List.sum_cons,
      Nat.add_assoc, and_assoc]

theorem chain_tplInsts {b jf : Nat} {j : List Nat} :
    ∀ (rs : List Row) (t k e : Nat), Chain k e (tplInsts b jf j t k e rs) ∧
      instW .K (tplInsts b jf j t k e rs) = rowsW .K rs ∧
      instW .E (tplInsts b jf j t k e rs) = rowsW .E rs
  | [], _, _, _ => by simp [tplInsts, Chain, instW, rowsW]
  | r :: rs, t, k, e => by
    obtain ⟨h1, h2, h3⟩ := chain_tplInsts rs (t + 1) (k + r.w .K) (e + r.w .E)
    refine ⟨⟨rfl, rfl, h1⟩, ?_, ?_⟩
    · simp only [tplInsts, instW, List.map_cons, List.sum_cons, rowsW] at h2 ⊢; rw [h2]
    · simp only [tplInsts, instW, List.map_cons, List.sum_cons, rowsW] at h3 ⊢; rw [h3]

theorem Block.tw_eq (B : Block) (τ : Ty) : B.tw τ = rowsW τ B.tpl := rfl

theorem chain_range_flatMap (f : Nat → List Inst) (cK cE : Nat) (k e : Nat)
    (hf : ∀ n, Chain (k + cK * n) (e + cE * n) (f n) ∧ instW .K (f n) = cK ∧ instW .E (f n) = cE) :
    ∀ n, Chain k e ((List.range n).flatMap f) ∧ instW .K ((List.range n).flatMap f) = cK * n ∧
      instW .E ((List.range n).flatMap f) = cE * n
  | 0 => by simp [Chain, instW]
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := chain_range_flatMap f cK cE k e hf n
    obtain ⟨g1, g2, g3⟩ := hf n
    have hW : ∀ τ, instW τ ((List.range n).flatMap f ++ f n) =
        instW τ ((List.range n).flatMap f) + instW τ (f n) := by
      intro τ; simp [instW, List.map_append, List.sum_append]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, chain_append, hW, hW, h2, h3,
      g2, g3]
    exact ⟨⟨h1, by simpa [h2, h3] using g1⟩, by ring, by ring⟩

namespace Program

variable (Q : Program)

theorem chain_blockInsts (b : Nat) :
    Chain (Q.start .K b) (Q.start .E b) (Q.blockInsts b (Q.blk b)) ∧
      instW .K (Q.blockInsts b (Q.blk b)) = (Q.blk b).tw .K * (Q.blk b).size ∧
      instW .E (Q.blockInsts b (Q.blk b)) = (Q.blk b).tw .E * (Q.blk b).size := by
  have := chain_range_flatMap (fun jf => tplInsts b jf (unflat (Q.blk b).dims jf) 0
      (Q.start .K b + (Q.blk b).tw .K * jf) (Q.start .E b + (Q.blk b).tw .E * jf) (Q.blk b).tpl)
    ((Q.blk b).tw .K) ((Q.blk b).tw .E) (Q.start .K b) (Q.start .E b) (fun n => by
      obtain ⟨h1, h2, h3⟩ := chain_tplInsts (b := b) (jf := n) (j := unflat (Q.blk b).dims n)
        (Q.blk b).tpl 0 (Q.start .K b + (Q.blk b).tw .K * n) (Q.start .E b + (Q.blk b).tw .E * n)
      exact ⟨h1, h2, h3⟩) (Q.blk b).size
  exact this

theorem start_succ (τ : Ty) {b : Nat} (hb : b < Q.blocks.length) :
    Q.start τ (b + 1) = Q.start τ b + (Q.blk b).tw τ * (Q.blk b).size := by
  simp only [start, List.take_add_one, List.getElem?_eq_getElem hb, Option.toList_some, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Q.blk_eq hb]
  omega

theorem chain_insts_prefix : ∀ n, n ≤ Q.blocks.length →
    Chain Q.nInK Q.nInE ((List.range n).flatMap fun b => Q.blockInsts b (Q.blk b)) ∧
      Q.nInK + instW .K ((List.range n).flatMap fun b => Q.blockInsts b (Q.blk b)) = Q.start .K n ∧
      Q.nInE + instW .E ((List.range n).flatMap fun b => Q.blockInsts b (Q.blk b)) = Q.start .E n
  | 0, _ => by simp [Chain, instW, start, nIn]
  | n + 1, hn => by
    obtain ⟨h1, h2, h3⟩ := chain_insts_prefix n (by omega)
    obtain ⟨g1, g2, g3⟩ := Q.chain_blockInsts n
    have hW : ∀ τ, instW τ ((List.range n).flatMap (fun b => Q.blockInsts b (Q.blk b)) ++
        Q.blockInsts n (Q.blk n)) = instW τ ((List.range n).flatMap fun b => Q.blockInsts b (Q.blk b)) +
          instW τ (Q.blockInsts n (Q.blk n)) := by
      intro τ; simp [instW, List.map_append, List.sum_append]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, chain_append, hW, hW,
      Q.start_succ .K (by omega), Q.start_succ .E (by omega), ← h2, ← h3, g2, g3]
    refine ⟨⟨h1, ?_⟩, by ring, by ring⟩
    rw [h2, h3]; exact g1

/-- **The interpreter's clock chain**: the instances' clocks are the counts of cells defined before
them, from the inputs to `cells`. -/
theorem chain_insts : Chain Q.nInK Q.nInE Q.insts ∧ Q.nInK + instW .K Q.insts = Q.cells .K ∧
    Q.nInE + instW .E Q.insts = Q.cells .E :=
  Q.chain_insts_prefix Q.blocks.length le_rfl

end Program

theorem chain_clock_le : ∀ (L : List Inst) (k e : Nat), Chain k e L → ∀ i ∈ L,
    k ≤ i.ck ∧ e ≤ i.ce ∧ i.ck + i.row.w .K ≤ k + instW .K L ∧ i.ce + i.row.w .E ≤ e + instW .E L
  | [], _, _, _, _, h => by simp at h
  | j :: L, k, e, ⟨hk, he, hc⟩, i, hi => by
    simp only [instW, List.map_cons, List.sum_cons] at *
    rcases List.mem_cons.mp hi with rfl | hi
    · subst hk he; omega
    · have := chain_clock_le L _ _ hc i hi
      simp only [instW] at this
      omega

/-! ## The program check, per instance -/

namespace Program

variable (Q : Program)

theorem inst_clock (b jf t : Nat) (τ : Ty) :
    (Q.inst b jf t).clock τ = Q.start τ b + (Q.blk b).tw τ * jf + (Q.blk b).rank τ t := by
  cases τ <;> rfl

theorem rowOk_of_wf (hwf : Q.wf = true) {b t : Nat} (hb : b < Q.blocks.length)
    (ht : t < (Q.blk b).tpl.length) :
    Q.rowOk b (Q.blk b) t ((Q.blk b).tpl.getD t default) = true := by
  simp only [wf, List.all_eq_true, List.mem_range] at hwf
  exact hwf b hb t ht

/-- The program check gives, per instance: the row is well typed, every operand reads a cell defined
before it, and a `readd`'s region is defined before it. -/
theorem inst_ok (hwf : Q.wf = true) {b jf t : Nat} (hb : b < Q.blocks.length)
    (hjf : jf < (Q.blk b).size) (ht : t < (Q.blk b).tpl.length) :
    (Q.inst b jf t).row.typeOk = true ∧
      (∀ a ∈ (Q.inst b jf t).row.args, a.at (Q.inst b jf t).j < (Q.inst b jf t).clock a.ty) ∧
      (∀ lo m, (Q.inst b jf t).row.op = .readd lo m →
        lo + 2 ^ m ≤ (Q.inst b jf t).clock (Q.inst b jf t).row.ty) := by
  have h := Q.rowOk_of_wf hwf hb ht
  simp only [rowOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun a ha => ?_, fun lo m hop => ?_⟩
  · have hb2 := h2 a ha
    have hd := dot_le_maxExcess a.strides (Q.blk b).dims (unflat (Q.blk b).dims jf)
      ((Q.blk b).tw a.ty) (unflat_inBox _ _)
    rw [flat_unflat_of_lt _ hjf] at hd
    rw [inst_clock]
    simp only [Addr.at, inst]
    omega
  · simp only [inst] at hop
    rw [hop] at h3
    simp only [decide_eq_true_eq] at h3
    rw [inst_clock]; simp only [inst]; omega

end Program

end Lvm.Loop
