-- New for lvm (WP-11b-QL): the one-pass program check of `LvmQBuild` implies WP-10's `Program.wf`.
import LvmQBuildSem

/-!
# The fast program check

`Program.wf` recomputes `Q.start` per row (`O(rows · blocks)`), which is slow under `decide` on a
large program. `segsOk` (in `LvmQBuild`) walks the segments once with the running pointer.
**`toProgram_wf`**: `segsOk ⟨nK, nE⟩ (m ⟨nK, nE⟩).2 = true → (toProgram nK nE m).wf = true`.
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-- Every block of `bs` passes the check at its pointer. -/
def BlocksOk : Ptr → List Block → Prop
  | _, [] => True
  | p, B :: bs => blockOkAt p B = true ∧ BlocksOk (p.advBs [B]) bs

theorem blocksOk_iff : ∀ (p : Ptr) (bs : List Block),
    BlocksOk p bs ↔ ∀ b < bs.length, blockOkAt (p.advBs (bs.take b)) (bs.getD b default) = true
  | p, [] => by simp [BlocksOk]
  | p, B :: bs => by
    simp only [BlocksOk, blocksOk_iff _ bs, List.length_cons]
    constructor
    · rintro ⟨h0, h⟩ b hb
      rcases b with _ | b
      · simpa [Ptr.advBs] using h0
      · have := h b (by omega)
        simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this
    · intro h
      refine ⟨by simpa [Ptr.advBs] using h 0 (by omega), fun b hb => ?_⟩
      have := h (b + 1) (by omega)
      simpa [List.take_succ_cons, Ptr.advBs_cons p B (bs.take b)] using this

theorem ptr_at_start (Q : Program) (b : Nat) (τ : Ty) :
    (⟨Q.start .K b, Q.start .E b⟩ : Ptr).at τ = Q.start τ b := by cases τ <;> rfl

theorem rowOk_eq (Q : Program) (b : Nat) (B : Block) (t : Nat) (r : Row) :
    Q.rowOk b B t r = rowOkC (fun τ => (⟨Q.start .K b, Q.start .E b⟩ : Ptr).at τ + B.rank τ t)
      B.dims B.tw r := by
  simp only [ptr_at_start]; rfl

/-- **The block-wise check implies `wf`.** -/
theorem wf_of_blocksOk (Q : Program) (h : BlocksOk ⟨Q.nInK, Q.nInE⟩ Q.blocks) : Q.wf = true := by
  rw [blocksOk_iff] at h
  simp only [Program.wf, List.all_eq_true, List.mem_range]
  intro b hb t ht
  have := h b hb
  rw [← start_ptr] at this
  simp only [blockOkAt, List.all_eq_true, List.mem_range] at this
  rw [rowOk_eq]
  exact this t (by simpa [Program.blk] using ht)

theorem maxExcess_nil (s : List Nat) (w : Nat) : maxExcess s [] w = 0 := by cases s <;> rfl

/-- On a block without dimensions the row check does not read the writes per iteration. -/
theorem rowOkC_nil (cl : Ty → Nat) (tw tw' : Ty → Nat) (r : Row) :
    rowOkC cl [] tw r = rowOkC cl [] tw' r := by
  simp only [rowOkC, maxExcess_nil]

theorem glueOk_iff : ∀ (p : Ptr) (rs : List Row),
    blockOkAt p ⟨[], rs⟩ = true ↔ segsOk p (rs.map .row) = true
  | p, [] => by simp [blockOkAt, segsOk]
  | p, r :: rs => by
    have ih := glueOk_iff (p.adv [.row r]) rs
    simp only [List.map_cons, segsOk, Bool.and_eq_true, ← ih, blockOkAt, List.all_eq_true,
      List.mem_range, List.length_cons]
    have hcl : ∀ t, (fun τ => p.at τ + Block.rank ⟨[], r :: rs⟩ τ (t + 1)) =
        fun τ => (p.adv [.row r]).at τ + Block.rank ⟨[], rs⟩ τ t := by
      intro t; funext τ
      rw [rank_glue_succ]
      cases τ <;> simp [Ptr.at, Ptr.adv, segsW, Seg.w] <;> omega
    have hcl0 : (fun τ => p.at τ + Block.rank ⟨[], r :: rs⟩ τ 0) = p.at := by
      funext τ; simp [Block.rank]
    constructor
    · intro h
      refine ⟨?_, fun t ht => ?_⟩
      · have := h 0 (by omega)
        rwa [hcl0, rowOkC_nil _ _ (fun _ => 0)] at this
      · have := h (t + 1) (by omega)
        rw [hcl t, rowOkC_nil _ _ (Block.tw ⟨[], rs⟩)] at this
        exact this
    · rintro ⟨h0, h⟩ t ht
      rcases t with _ | t
      · rw [hcl0, rowOkC_nil _ _ (fun _ => 0)]; exact h0
      · rw [hcl t, rowOkC_nil _ _ (Block.tw ⟨[], rs⟩)]
        exact h t (by simpa using ht)

theorem blocksOk_glueB (p : Ptr) (rs : List Row) (bs : List Block) :
    BlocksOk p (glueB rs bs) ↔ segsOk p (rs.map .row) = true ∧ BlocksOk (p.adv (rs.map .row)) bs := by
  unfold glueB
  rcases rs with _ | ⟨r, rs⟩
  · simp [segsOk]
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, BlocksOk, glueOk_iff, advBs_glue]

theorem segsOk_append : ∀ (p : Ptr) (δ₁ δ₂ : List Seg),
    segsOk p (δ₁ ++ δ₂) = true ↔ segsOk p δ₁ = true ∧ segsOk (p.adv δ₁) δ₂ = true
  | p, [], δ₂ => by simp [segsOk]
  | p, .row r :: δ₁, δ₂ => by
    simp only [List.cons_append, segsOk, Bool.and_eq_true]
    rw [segsOk_append _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]
  | p, .blk B :: δ₁, δ₂ => by
    simp only [List.cons_append, segsOk, Bool.and_eq_true]
    rw [segsOk_append _ δ₁ δ₂, ← Ptr.adv_cons, and_assoc]

theorem groupAux_ok : ∀ (p : Ptr) (δ : List Seg),
    segsOk p δ = true ↔ segsOk p ((groupAux δ).1.map .row) = true ∧
      BlocksOk (p.adv ((groupAux δ).1.map .row)) (groupAux δ).2
  | p, [] => by simp [segsOk, BlocksOk, groupAux]
  | p, .row r :: δ => by
    rw [groupAux_row]
    split
    · simp only [segsOk, List.map_cons, List.map_nil, Bool.and_eq_true, Bool.and_true]
      rw [groupAux_ok _ δ, blocksOk_glueB]
    · simp only [segsOk, List.map_cons, Bool.and_eq_true]
      rw [groupAux_ok _ δ, Ptr.adv_cons p (.row r) ((groupAux δ).1.map .row), and_assoc]
  | p, .blk B :: δ => by
    rw [groupAux_blk]
    simp only [segsOk, List.map_nil, Ptr.adv_nil, BlocksOk, Bool.and_eq_true, true_and]
    rw [groupAux_ok _ δ, blocksOk_glueB, advBs_blk]

/-- **The one-pass check implies the program check** of the gadget's program. -/
theorem toProgram_wf {α : Type} (nK nE : Nat) (m : BM α)
    (h : segsOk ⟨nK, nE⟩ (m ⟨nK, nE⟩).2 = true) : (toProgram nK nE m).wf = true := by
  apply wf_of_blocksOk
  show BlocksOk ⟨nK, nE⟩ (group (m ⟨nK, nE⟩).2)
  rw [group_eq, blocksOk_glueB]
  exact (groupAux_ok _ _).mp h

end Lvm.Loop.Build
