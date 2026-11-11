import LvmQWhirBatch

/-!
# QA2: self-evaluation of the glue as a builder gadget (BLUEPRINT §4.5, D10; WP-10 `LvmSelfEval`)

The child's verifier needs, at its table-sumcheck point, the extension of every fixed column of
every piece. Structured columns have closed forms (WP-10 `pieceEval_eq`); the glue's columns (the
pieces of blocks without loop dimension: the builder's straight-line rows) are evaluated by the
program itself (`fixmul`, whose multiplier is the glue matrix `fixMat`).

**`selfEval dc dx r`** (WP-10's `eqLevel`×dx + `fixPro` + `fixBlock`, written with the builder):
* the `eq` table of the point `r_0 … r_{dx−1}` (`eqTab`, `2^(dx+1)` rows);
* `2^dc` zero cells (the accumulators' iteration −1);
* one `fixmul` loop of dims `[dc, dx]` (column inner, row outer):
  `acc[c, x] = F_c(x) · eq[x] + acc[c, x − 1]`, `F_c(x) = fm [c, x]`.

**`selfEval_spec`**: the last accumulator of column `c` is `mle r (x ↦ fm [c, x])`: in a program
(`ctxOf Q`) the extension of glue column `c` zero-extended to `2^dx` rows (WP-10 `fixmul_mle`, here
for the builder). Its multiplier column is a combination of the accumulators (WP-10 `mle_fixF`), its
other columns are structured, and its straight-line rows (the `eq` table's `1 + r_i`) are glue
themselves: **the program is a fixed point as soon as its glue fits**, i.e. `glueFits Q dc dx`
(decidable on the final program).

Cost: `12·2^(dc+dx)` (fixmul) `+ 16·(2^(dx+1) − 2) + 12·dx` (eq table) `+ 12·2^dc` (zeros).

**The configuration that closes exactly is `dx = 0`** (`selfEval0_spec`). The table sumcheck evaluates a
piece of height `2^h` at `point.take h`, and the `fixmul` piece's own multiplier column has extension
`mle r'_{<dc} (c ↦ mle r'_{[dc, dc+dx)} F_c)` (WP-10 `mle_fixF`): with `dx > 0` the glue pieces need
`F_c` at `r'_{<h}` but the `fixmul` column needs it at `r'_{[dc, dc+dx)}` (WP-10's `fixMat` takes the
column from loop dimension 0), and pieces shorter than `2^dx` pick up `Π_{h≤i<dx}(1 − r_i)`. With
`dx = 0` every glue piece has height 1 (one row per shape per glue run; the builder's `group` must
split a run at a repeated shape), its fixed values are its constants, the accumulators are exactly
`F_c(0)`, and the `fixmul` column's extension at `r'_{<dc}` is `Σ_c eq(r', c)·acc_c` (`eqTab` +
`dotG`). Then **the fixed point closes iff `glueFits Q dc 0`**. `dx > 0` needs a WP-10 change (a
column offset in `fixMat` and one block per height class, or `fixMat` indexed row-first).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm Lvm.Loop

/-- **The self-evaluation gadget**: the base of the last accumulator row (`2^dc` cells). -/
def selfEval (dc dx : Nat) (r : Nat → Cell) (one z : Cell) : BM Nat := do
  let eb ← eqTab r z one false dx
  let _ ← loop [dc] [⟨.lin 0 0, .E, [z.opd, z.opd]⟩]
  let p ← getPtr
  let _ ← loop [dc, dx] [⟨.fixmul, .E, [.abs ⟨.E, eb, [0, 1]⟩, .abs ⟨.E, p.e - 2 ^ dc, [1, 2 ^ dc]⟩]⟩]
  pure (p.e + 2 ^ dc * (2 ^ dx - 1))

/-- **The fixed point closes** for a program whose glue has at most `2^dc` columns, each of a
piece of at most `2^dx` rows (WP-10 `toy_fit`'s condition). -/
def glueFits (Q : Program) (dc dx : Nat) : Bool :=
  decide (Q.glueCols.length ≤ 2 ^ dc) && Q.glueCols.all fun pc => decide (Q.height pc.1 ≤ dx)

variable {c : Ctx} {M : Mem}

/-- **The accumulators are the extensions of the glue columns** at `r`. -/
theorem selfEval_spec {dc dx : Nat} {r : Nat → Cell} {one z : Cell} {p : Ptr}
    (h : SegsHold c M p (selfEval dc dx r one z p).2) (hz : z.val M = 0) (hzE : z.ty = .E)
    (hr : ∀ i, (r i).ty = .E) (hone : M.e one.n = 1) {col : Nat} (hcol : col < 2 ^ dc) :
    M.e ((selfEval dc dx r one z p).1 + col) =
      mle ((List.range dx).map fun i => (r i).val M) (fun x => FE.ofK (c.fm [col, x])) := by
  simp only [selfEval, bind_apply, getPtr, pure_apply, List.nil_append, List.append_nil,
    Ptr.adv_nil] at h ⊢
  rw [segsHold_append, segsHold_append] at h
  obtain ⟨he, hzs, hf⟩ := h
  have heq := eqTab_spec r z one false dx he hz hr hone
  set eb := (eqTab r z one false dx p).1
  set p₁ := p.adv (eqTab r z one false dx p).2
  set p₂ := p₁.adv (loop [dc] [⟨.lin 0 0, .E, [z.opd, z.opd]⟩] p₁).2
  have hp₂ : p₂.e = p₁.e + 2 ^ dc := by
    simp only [p₂, loop_adv, ltw]; simp [LRow.w, Row.w, Row.writes]
  -- the zero cells
  have hzero : ∀ c' < 2 ^ dc, M.e (p₁.e + c') = 0 := by
    intro c' hc'
    have hjf : c' < 2 ^ [dc].sum := by simpa using hc'
    have r0 := loop_rel hzs (jf := c') (t := 0) hjf (by simp)
    simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
      LoopOut.cell_val, Cell.opd, Opd.val_abs] at r0
    simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, Mem.rd_E, Cell.addr] at r0
    have hzv : M.rd z.ty z.n = 0 := hz
    rw [r0, hzv]; simp [ofK_zero]
  -- the accumulator recursion, summed
  have hacc : ∀ x < 2 ^ dx, M.e (p₂.e + (col + 2 ^ dc * x)) =
      ∑ x' ∈ Finset.range (x + 1), FE.ofK (c.fm [col, x']) * M.e (eb + x') := by
    intro x hx
    induction x with
    | zero =>
      have hjf : col + 2 ^ dc * 0 < 2 ^ [dc, dx].sum := by
        simp; exact lt_of_lt_of_le hcol (Nat.pow_le_pow_right (by norm_num) (by omega))
      have r0 := loop_rel hf (jf := col + 2 ^ dc * 0) (t := 0) hjf (by simp)
      simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
        LoopOut.cell_val, Opd.val_abs] at r0
      rw [unflat_two hcol hx] at r0
      simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, Mem.rd_E] at r0
      simp only [Nat.mul_zero, Nat.add_zero] at r0 ⊢
      rw [r0, show p₂.e - 2 ^ dc + col = p₁.e + col by omega, hzero col hcol, add_zero]
      simp
    | succ x ih =>
      have hjf : col + 2 ^ dc * (x + 1) < 2 ^ [dc, dx].sum := by
        simp only [List.sum_cons, List.sum_nil, Nat.add_zero, pow_add]
        calc col + 2 ^ dc * (x + 1) < 2 ^ dc * (x + 2) := by rw [Nat.mul_succ (2 ^ dc) (x + 1)]; omega
          _ ≤ 2 ^ dc * 2 ^ dx := Nat.mul_le_mul_left _ hx
      have r0 := loop_rel hf (jf := col + 2 ^ dc * (x + 1)) (t := 0) hjf (by simp)
      simp only [LRel, List.getD_cons_zero, List.getD_cons_succ, LoopOut.arg, loop_apply,
        LoopOut.cell_val, Opd.val_abs] at r0
      rw [unflat_two hcol hx] at r0
      simp [lrank, ltw, LRow.w, Row.w, Row.writes, Ptr.at, Addr.at, dot, Mem.rd_E] at r0
      rw [Finset.sum_range_succ, ← ih (by omega), r0]
      have e1 : p₂.e - 2 ^ dc + (col + 2 ^ dc * (x + 1)) = p₂.e + (col + 2 ^ dc * x) := by
        rw [Nat.mul_succ]; omega
      rw [e1]; ring
  rw [show p₂.e + 2 ^ dc * (2 ^ dx - 1) + col = p₂.e + (col + 2 ^ dc * (2 ^ dx - 1)) by ring,
    hacc (2 ^ dx - 1) (by have := Nat.two_pow_pos dx; omega),
    show 2 ^ dx - 1 + 1 = 2 ^ dx by have := Nat.two_pow_pos dx; omega, mle_eq_sum]
  simp only [List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [heq x (Finset.mem_range.mp hx), mul_comm]
  congr 2

/-- **`dx = 0`**: the accumulator of glue column `c` is its single value `F_c(0)`. -/
theorem selfEval0_spec {dc : Nat} {r : Nat → Cell} {one z : Cell} {p : Ptr}
    (h : SegsHold c M p (selfEval dc 0 r one z p).2) (hz : z.val M = 0) (hzE : z.ty = .E)
    (hr : ∀ i, (r i).ty = .E) (hone : M.e one.n = 1) {col : Nat} (hcol : col < 2 ^ dc) :
    M.e ((selfEval dc 0 r one z p).1 + col) = FE.ofK (c.fm [col, 0]) := by
  rw [selfEval_spec h hz hzE hr hone hcol]
  simp [mle]

end Lvm.Loop.Build
