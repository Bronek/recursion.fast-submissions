-- New for lvm (AC-Q). Searched for reusable straight-line chains: QA2's `dotG`/`pows`/`eqTab`
-- (`LvmQWhirBatch`, loops over affine cells, reused for the `eq` tables), Q_sig's `Ok`/`seqAll`
-- helpers (`LvmQSigHdr`, reused), FR's `FRVIR*` (R1CS, no LoopIR). The glue chains below (a dot
-- product over arbitrary cells, Horner, the line point, gated `E` equalities) had no counterpart.
import LvmQWhirBatch
import LvmQSumcheckCore
import LvmQSigHdr

/-!
# Q_acc's building blocks (BLUEPRINT §12.5)

Straight-line gadgets over `E` cells, each with a pointer-generic spec (QL's frame form):

* `ldE q`: the `E` scalar of stream lanes `q, q+1, q+2` (`ldE_feAt`: `F`'s `feAt Σ (8q)` on
  streamed cells); `ldEs qs`: one per entry.
* `macChain l acc`: `acc + Σ a·b` over the cell pairs `l` (one `muladd` row each).
* `horner cs t z`: `polyEval cs t` (`F`'s Horner, constant first; `z` holds `0`).
* `linePt a b t`: `a + t·(a + b)` (the accumulator's line, characteristic 2).
* `assertEqE a b g`: `g·(a + b) = 0` (`a = b` when the gate `g` is `1`).
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

variable {c : Ctx} {M : Mem}

/-! ## Stream scalars -/

/-- The `E` scalar at stream lanes `q, q + 1, q + 2`. -/
def ldE (q : Nat) : BM Cell := loadE (kc q) (kc (q + 1)) (kc (q + 2))

theorem ldE_cell (q : Nat) (p : Ptr) : (ldE q p).1 = ec p.e := rfl

theorem ldE_val {q : Nat} {p : Ptr} (h : SegsHold c M p (ldE q p).2) :
    (ldE q p).1.val M = FE.ofK (M.k q) + FE.y * FE.ofK (M.k (q + 1)) + FE.y * FE.y * FE.ofK (M.k (q + 2)) :=
  loadE_spec h

/-- **A loaded stream scalar is `F`'s scalar** at byte `8q`. -/
theorem ldE_feAt {sig : ByteArray} {T q : Nat} {p : Ptr} (hS : Streamed M sig T) (hq : q + 2 < T)
    (h : SegsHold c M p (ldE q p).2) : (ldE q p).1.val M = feAt sig (8 * q) := by
  rw [ldE_val h]; exact load_feAt hS hq

/-- The scalars at the lanes `qs`, in order. -/
def ldEs (qs : List Nat) : BM (List Cell) := seqAll (qs.map ldE)

theorem ldEs_length : ∀ (qs : List Nat) (p : Ptr), (ldEs qs p).1.length = qs.length
  | [], _ => rfl
  | q :: qs, p => by
    simp only [ldEs, List.map_cons, seqAll_cons_apply, List.length_cons] at *
    rw [show (seqAll (qs.map ldE) _).1.length = qs.length from ldEs_length qs _]

theorem ldEs_spec {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) :
    ∀ (qs : List Nat) (p : Ptr), (∀ q ∈ qs, q + 2 < T) → SegsHold c M p (ldEs qs p).2 →
      ∀ i < qs.length, ((ldEs qs p).1.getD i default).ty = .E ∧
        ((ldEs qs p).1.getD i default).val M = feAt sig (8 * qs.getD i 0)
  | [], _, _, _, i, hi => absurd hi (by simp)
  | q :: qs, p, hq, h, i, hi => by
    simp only [ldEs, List.map_cons, seqAll_cons_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      exact ⟨rfl, ldE_feAt hS (hq q (by simp)) h.1⟩
    | succ i =>
      simp only [List.getD_cons_succ]
      exact ldEs_spec hS qs _ (fun q' h' => hq q' (by simp [h'])) h.2.1 i (by simpa using hi)

theorem ldEs_cells : ∀ (qs : List Nat) (p : Ptr) (i : Nat), i < qs.length →
    (ldEs qs p).1.getD i default = ec (p.e + i)
  | [], _, i, hi => absurd hi (by simp)
  | q :: qs, p, i, hi => by
    simp only [ldEs, List.map_cons, seqAll_cons_apply]
    cases i with
    | zero => simp [ldE_cell]
    | succ i =>
      simp only [List.getD_cons_succ]
      rw [show (seqAll (qs.map ldE) _).1.getD i default = _ from ldEs_cells qs _ i (by simpa using hi)]
      simp [ldE, loadE, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes, Ptr.at]
      omega

/-- The scalars at the lanes `qs` at consecutive `E` cells; their first cell. -/
def ldEsB (qs : List Nat) : BM Nat := do
  let p ← getPtr
  let _ ← ldEs qs
  pure p.e

theorem ldEsB_spec {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) {qs : List Nat} {p : Ptr}
    (hq : ∀ q ∈ qs, q + 2 < T) (h : SegsHold c M p (ldEsB qs p).2) :
    ∀ i < qs.length, M.e ((ldEsB qs p).1 + i) = feAt sig (8 * qs.getD i 0) := by
  simp only [ldEsB, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil, Ptr.adv_nil] at h ⊢
  intro i hi
  have := (ldEs_spec hS qs p hq h i hi).2
  rwa [ldEs_cells qs p i hi] at this

/-- `ldEsB` on any `K` cells: the scalar of three consecutive cells. -/
theorem ldEsB_val {qs : List Nat} {p : Ptr} (h : SegsHold c M p (ldEsB qs p).2) :
    ∀ i < qs.length, M.e ((ldEsB qs p).1 + i) =
      ⟨M.k (qs.getD i 0), M.k (qs.getD i 0 + 1), M.k (qs.getD i 0 + 2)⟩ := by
  have key : ∀ (qs : List Nat) (p : Ptr), SegsHold c M p (ldEs qs p).2 → ∀ i < qs.length,
      ((ldEs qs p).1.getD i default).val M =
        ⟨M.k (qs.getD i 0), M.k (qs.getD i 0 + 1), M.k (qs.getD i 0 + 2)⟩ := by
    intro qs
    induction qs with
    | nil => intro p _ i hi; exact absurd hi (by simp)
    | cons q qs ih =>
      intro p h i hi
      simp only [ldEs, List.map_cons, seqAll_cons_apply] at h ⊢
      rw [segsHold_append, segsHold_append] at h
      cases i with
      | zero => simp only [List.getD_cons_zero]; rw [ldE_val h.1, FE_mk_eq]
      | succ i => simpa [ldEs] using ih _ h.2.1 i (by simpa using hi)
  simp only [ldEsB, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil, Ptr.adv_nil] at h ⊢
  intro i hi
  have := key qs p h i hi
  rwa [ldEs_cells qs p i hi] at this

/-! ## A dot product with `K` cells -/

/-- **`Σ_{i<n} x_i · y_i`**, `x_i` at the `E` cells `xb + xs·i`, `y_i` at the `K` cells `yb + ys·i`
(QA2's `dotG` with a `K` operand: a `2^a`-term running `muladd`, one difference row stopping at
`n`). -/
def dotGK (a n xb xs yb ys : Nat) : BM Cell := do
  let p ← getPtr
  let s ← loop [a] [⟨.muladd, .E, [.abs ⟨.E, xb, [xs]⟩, .abs ⟨.K, yb, [ys]⟩, .prev 0]⟩]
  add (s.cell 0 (n - 1)) (ec (p.e - 1))

theorem dotGK_spec {p : Ptr} {a n xb xs yb ys : Nat} (h : SegsHold c M p (dotGK a n xb xs yb ys p).2)
    (hp : 1 ≤ p.e) (hn : 1 ≤ n) (hna : n ≤ 2 ^ a) :
    (dotGK a n xb xs yb ys p).1.val M =
      ∑ i ∈ Finset.range n, M.e (xb + xs * i) * FE.ofK (M.k (yb + ys * i)) := by
  simp only [dotGK, bind_apply, getPtr, pure_apply, List.nil_append, Ptr.adv_nil] at h ⊢
  rw [segsHold_append] at h
  have hs := lin_spec h.2
  simp only [add] at hs ⊢
  rw [hs]
  have hstep : ∀ x < 2 ^ a, M.e (p.e + 1 * x) =
      M.e (xb + xs * x) * FE.ofK (M.k (yb + ys * x)) + M.e (p.e - 1 + 1 * x) := by
    intro x hx
    have hjf : x < 2 ^ [a].sum := by simpa using hx
    have hu : unflat [a] x = [x] := by simp [unflat, Nat.mod_eq_of_lt hx]
    have r := loop_rel h.1 (jf := x) (t := 0) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Opd.val_abs] at r
    rw [Opd.val_prev M _ hjf] at r
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, Loop.dot, hu, Mem.rd_E, Mem.rd_K] at r
    simp only [Nat.one_mul]
    rw [r]
  have hpre := prefix_cells M.e p.e 1 (2 ^ a) hp _ hstep
  have hl := hpre n hna
  simp only [Nat.one_mul] at hl
  have hc : (LoopOut.cell ⟨p, [a], [⟨.muladd, .E, [.abs ⟨.E, xb, [xs]⟩, .abs ⟨.K, yb, [ys]⟩,
      .prev 0]⟩]⟩ 0 (n - 1)).val M = M.e (p.e - 1 + n) := by
    simp [LoopOut.cell_val, lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Mem.rd_E]
    congr 1; omega
  simp only [loop_apply] at hc ⊢
  rw [hc, hl, ofK_one, ofK_zero, one_mul, add_zero, Cell.val_E, add_right_comm,
    CharTwo.add_self_eq_zero, zero_add]

/-! ## Constants -/

/-- The `E` constants `0` and `1` (`x + x + k'`, from any `K` cell `x`), at `p.e`, `p.e + 1`. -/
def consts (x : Nat) : BM (Cell × Cell) := do
  let z ← const .E 0 (kc x)
  let o ← const .E 1 (kc x)
  pure (z, o)

theorem consts_spec {x : Nat} {p : Ptr} (h : SegsHold c M p (consts x p).2) :
    (consts x p).1.1 = ec p.e ∧ (consts x p).1.2 = ec (p.e + 1) ∧
      M.e p.e = 0 ∧ M.e (p.e + 1) = 1 := by
  simp only [consts, bind_apply, pure_apply, List.append_nil] at h ⊢
  rw [segsHold_append] at h
  have h1 := lin_spec h.1
  have h2 := lin_spec h.2
  have hp : (p.adv (const .E 0 (kc x) p).2).e = p.e + 1 := by
    simp [const, lin, rowRes, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
  refine ⟨rfl, by simp [const, lin, rowRes, Ptr.at, Ptr.adv, segsW, Seg.w, Row.w, Row.writes], ?_, ?_⟩
  · have : (const .E 0 (kc x) p).1.val M = M.e p.e := rfl
    rw [← this]; simp only [const] at h1 ⊢; rw [h1, ofK_one, one_mul, CharTwo.add_self_eq_zero, ofK_zero,
      add_zero]
  · have : (const .E 1 (kc x) (p.adv (const .E 0 (kc x) p).2)).1.val M = M.e (p.e + 1) := by
      simp [const, lin, rowRes, Ptr.at, Cell.val, Mem.rd_E, Ptr.adv, segsW, Seg.w, Row.w, Row.writes]
    rw [← this]; simp only [const] at h2 ⊢; rw [h2, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add]

/-! ## Dot products over cell pairs -/

/-- `acc + Σ a·b` over the pairs, one `E` `muladd` row per pair. -/
def macChain : List (Cell × Cell) → Cell → BM Cell
  | [], acc => pure acc
  | ab :: l, acc => do
    let acc' ← mulAdd .E ab.1 ab.2 acc
    macChain l acc'

theorem macChain_spec : ∀ (l : List (Cell × Cell)) (acc : Cell) (p : Ptr),
    SegsHold c M p (macChain l acc p).2 →
      (macChain l acc p).1.val M = acc.val M + (l.map fun ab => ab.1.val M * ab.2.val M).sum
  | [], acc, p, _ => by simp [macChain, pure_apply]
  | ab :: l, acc, p, h => by
    simp only [macChain, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [macChain_spec l _ _ h.2, mulAdd_spec h.1, List.map_cons, List.sum_cons]
    ring

/-! ## Horner and the line -/

/-- `polyEval cs t` (constant first): `z` (a cell holding `0`) for no coefficient, else
`horner rest · t + c₀`. -/
def horner : List Cell → Cell → Cell → BM Cell
  | [], _, z => pure z
  | c₀ :: cs, t, z => do
    let r ← horner cs t z
    mulAdd .E r t c₀

theorem horner_spec (t z : Cell) (hz : z.val M = 0) : ∀ (cs : List Cell) (p : Ptr),
    SegsHold c M p (horner cs t z p).2 →
      (horner cs t z p).1.val M = polyEval (cs.map (Cell.val M)) (t.val M)
  | [], p, _ => by simp [horner, pure_apply, polyEval, hz]
  | c₀ :: cs, p, h => by
    simp only [horner, bind_apply] at h ⊢
    rw [segsHold_append] at h
    rw [mulAdd_spec h.2, horner_spec t z hz cs p h.1]
    simp [polyEval]

/-- `a + t·(a + b)`: the point of the line through `a` (at `0`) and `b` (at `1`) at `t`. -/
def linePt (a b t : Cell) : BM Cell := do
  let s ← add a b
  mulAdd .E t s a

theorem linePt_spec {a b t : Cell} {p : Ptr} (h : SegsHold c M p (linePt a b t p).2) :
    (linePt a b t p).1.val M = a.val M + t.val M * (a.val M + b.val M) := by
  simp only [linePt, bind_apply] at h ⊢
  rw [segsHold_append] at h
  rw [mulAdd_spec h.2, add, lin_spec h.1, ofK_one, ofK_zero, one_mul, add_zero]
  ring

/-- The line point of every coordinate pair, in order. -/
def linePts (ab : List (Cell × Cell)) (t : Cell) : BM (List Cell) :=
  seqAll (ab.map fun x => linePt x.1 x.2 t)

theorem linePts_spec (t : Cell) : ∀ (ab : List (Cell × Cell)) (p : Ptr),
    SegsHold c M p (linePts ab t p).2 → (linePts ab t p).1.length = ab.length ∧
      ∀ i < ab.length, ((linePts ab t p).1.getD i default).val M =
        (ab.getD i default).1.val M + t.val M * ((ab.getD i default).1.val M + (ab.getD i default).2.val M)
  | [], _, _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | x :: ab, p, h => by
    simp only [linePts, List.map_cons, seqAll_cons_apply] at h ⊢
    rw [segsHold_append, segsHold_append] at h
    obtain ⟨ih1, ih2⟩ := linePts_spec t ab _ h.2.1
    refine ⟨by simpa [linePts] using ih1, fun i hi => ?_⟩
    cases i with
    | zero => simpa using linePt_spec h.1
    | succ i => simpa [linePts] using ih2 i (by simpa using hi)

/-! ## Gated equalities -/

/-- Assert `g·(a + b) = 0`. -/
def assertEqE (a b g : Cell) : BM Unit := assertEq a b g

theorem assertEqE_spec {a b g : Cell} {p : Ptr} (h : Ok c M (assertEqE a b g) p) (hg : g.val M = 1) :
    a.val M = b.val M := by
  obtain ⟨h1, h2⟩ := h
  simp only [assertEqE, assertEq, bind_apply] at h1 h2
  rw [segsHold_append] at h1
  rw [segsAssert_append] at h2
  have hs := lin_spec h1.1
  have ha := assert0_spec h2.2
  simp only [add] at hs ha
  rw [hg, one_mul] at ha
  have : (lin (jn a.ty b.ty) 1 0 a b p).1.val M = 0 := ha
  rw [hs, ofK_one, ofK_zero, one_mul, add_zero] at this
  exact (CharTwo.add_eq_zero (R := FE)).mp this

/-- Assert `a_i = b_i` for every pair. -/
def assertEqs (ab : List (Cell × Cell)) (g : Cell) : BM (List Unit) :=
  seqAll (ab.map fun x => assertEqE x.1 x.2 g)

theorem assertEqs_spec {g : Cell} (hg : g.val M = 1) : ∀ (ab : List (Cell × Cell)) (p : Ptr),
    Ok c M (assertEqs ab g) p → ∀ x ∈ ab, x.1.val M = x.2.val M
  | [], _, _, x, hx => absurd hx (by simp)
  | y :: ab, p, h, x, hx => by
    obtain ⟨h1, h2⟩ := h
    simp only [assertEqs, List.map_cons, seqAll_cons_apply] at h1 h2
    rw [segsHold_append, segsHold_append] at h1
    rw [segsAssert_append, segsAssert_append] at h2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact assertEqE_spec ⟨h1.1, h2.1⟩ hg
    · exact assertEqs_spec hg ab _ ⟨h1.2.1, h2.2.1⟩ x hx

end Lvm.QAcc
