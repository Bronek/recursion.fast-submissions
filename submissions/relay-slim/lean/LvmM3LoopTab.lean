-- new for lvm (WP-9): the LoopIR pieces (WP-10, `LvmLoopTable`) and the input arrays as lvm M3 tables
-- (`LvmM3Tab`), Mathlib-free: the native verifier and the prover's table dump build them from the program.
import LvmM3Tab
import LvmLoopTable

/-!
# The LoopIR tables as lvm M3 tables (data)

`pieceTab`: a LoopIR piece's table (columns = the shape's committed columns placed by `pl`, then its
fixed columns `Q.fval`; constraints, reads and seed = WP-10's with variables renamed to column indices).
`InArr.tab`: an input array's table. `lvmTabs`: pieces, then input arrays, then auxiliary tables.
Degree at most two is proved (`constraints_d2`). The instance and the bus bridge are `LvmM3Loop`.
-/

namespace Lvm.M3

open Lvm.Loop

/-! ## `Poly2` as `CPoly` -/

/-- A LoopIR polynomial with its variables renamed to column indices. -/
def ofPoly2 (idx : Var → Nat) (P : Poly2) : CPoly := P.map fun m ↦ (m.coef, m.vars.map idx)

/-- Every monomial of a LoopIR polynomial has at most two variables. -/
def D2 (P : Poly2) : Prop := ∀ m ∈ P, m.vars.length ≤ 2

theorem d2_ofPoly2 {idx : Var → Nat} {P : Poly2} (h : D2 P) : (ofPoly2 idx P).Deg2 := by
  intro m hm
  obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
  simpa using h m' hm'

theorem d2_append {P R : Poly2} (hP : D2 P) (hR : D2 R) : D2 (P ++ R) := fun m hm ↦ by
  rcases List.mem_append.mp hm with h | h
  · exact hP m h
  · exact hR m h

theorem d2_var (u : Var) : D2 (Poly2.var u) := fun m hm ↦ by
  simp [Poly2.var] at hm; subst hm; simp

theorem d2_prodPoly (u w : Nat → Var) (la lb l : Nat) : D2 (prodPoly u w la lb l) := fun m hm ↦ by
  simp only [prodPoly, List.mem_map] at hm
  obtain ⟨_, -, rfl⟩ := hm; simp

theorem d2_limbPoly (u : Nat → Var) (n l : Nat) : D2 (limbPoly u n l) := by
  unfold limbPoly; split
  · exact d2_var _
  · intro m hm; simp at hm

theorem d2_limbFix (c : FCol) (u : Nat → Var) (n l : Nat) : D2 (limbFix c u n l) := by
  unfold limbFix; split
  · intro m hm; simp at hm; subst hm; simp
  · intro m hm; simp at hm

/-- **WP-10's constraints have degree at most two** (fixed columns counted as variables). -/
theorem constraints_d2 (σ : Loop.Shape) : ∀ C ∈ σ.constraints, D2 C := by
  intro C hC
  unfold Loop.Shape.constraints at hC
  split at hC <;> simp only [List.mem_map, List.mem_range] at hC <;> obtain ⟨l, -, rfl⟩ := hC
  · exact d2_append (d2_append (d2_var _) (d2_prodPoly _ _ _ _ _)) (d2_limbPoly _ _ _)
  · refine d2_append (d2_append (d2_append (d2_var _) (d2_limbPoly _ _ _)) (d2_limbFix _ _ _ _)) ?_
    split
    · exact d2_var _
    · intro m hm; simp at hm
  · exact d2_prodPoly _ _ _ _ _
  · exact d2_append (d2_var _) (d2_var _)
  · exact d2_append (d2_append (d2_var _) (d2_limbFix _ _ _ _)) (d2_limbPoly _ _ _)

/-- `eq_kernel(point)` over `FE` (first coordinate the lowest bit). -/
def eqKernel' (point : List FE) : List FE :=
  point.foldl (fun out r ↦ out.map (· * (1 - r)) ++ out.map (· * r)) [1]

/-- `eq(bits of s, z)`: the selector weight of the coordinates `z` at the index `s`. -/
def eqSel (s : Nat) (z : List FE) : FE :=
  (z.zipIdx.map fun (r, i) ↦ if (s >>> i) % 2 = 1 then r else 1 - r).foldl (· * ·) 1

/-! ## The tables -/

/-- The variables of a shape's table: its committed columns, then its fixed columns. -/
def shapeVars (σ : Loop.Shape) : List Var := σ.committed ++ σ.fcols.map Var.fix

/-- The column index of a variable (the width if it is not a column). -/
def vidx (σ : Loop.Shape) (u : Var) : Nat := (shapeVars σ).idxOf u

/-- The key of a flush, renamed. -/
def keyOf (σ : Loop.Shape) (f : Flush) : Key := ⟨f.sep, ofPoly2 (vidx σ) f.addr, f.val.map (ofPoly2 (vidx σ))⟩

/-- The count column of a flush whose count is one variable (`Poly2.var`). -/
def cntOf (σ : Loop.Shape) (f : Flush) : Nat :=
  match f.cnt with
  | [⟨_, [u]⟩] => vidx σ u
  | _ => 0

theorem d2_val (σ : Loop.Shape) (o : Nat) : ∀ P ∈ σ.argVals o, D2 P := by
  intro P hP; simp only [Loop.Shape.argVals, List.mem_map] at hP
  obtain ⟨_, -, rfl⟩ := hP; exact d2_var _

theorem d2_resVals (σ : Loop.Shape) : ∀ P ∈ σ.resVals, D2 P := by
  intro P hP; simp only [Loop.Shape.resVals, List.mem_map] at hP
  obtain ⟨_, -, rfl⟩ := hP; exact d2_var _

theorem keyOf_read_deg (σ : Loop.Shape) : ∀ f ∈ σ.readFlushes, (keyOf σ f).Deg2 := by
  intro f hf
  simp only [Loop.Shape.readFlushes, List.mem_append, List.mem_map, List.mem_range] at hf
  rcases hf with ⟨o, -, rfl⟩ | hf
  · refine ⟨d2_ofPoly2 (d2_var _), fun P hP ↦ ?_⟩
    obtain ⟨P', hP', rfl⟩ := List.mem_map.mp hP
    exact d2_ofPoly2 (d2_val σ o P' hP')
  · split at hf
    · simp only [List.mem_singleton] at hf; subst hf
      refine ⟨d2_ofPoly2 (d2_var _), fun P hP ↦ ?_⟩
      obtain ⟨P', hP', rfl⟩ := List.mem_map.mp hP
      exact d2_ofPoly2 (d2_resVals σ P' hP')
    · simp at hf

/-- The table of `2^τ` rows of LoopIR rows of shape `σ`: committed columns placed by `pl`, fixed
column `c` given by `fx c` (cells) and `fe c` (closed form). -/
def shapeTab (σ : Loop.Shape) (τ : Nat) (fx : FCol → Nat → FK) (fe : FCol → List FE → FE)
    (pl : Var → Bool × Nat) : Tab where
  τ := τ
  cols := (shapeVars σ).map fun u ↦ match u with
    | .fix c => .fix (fx c) (fe c)
    | u => .com (pl u).1 (pl u).2
  cons := σ.constraints.map (ofPoly2 (vidx σ))
  reads := σ.readFlushes.map fun f ↦ (keyOf σ f, cntOf σ f)
  seeds := if σ.writes then [(keyOf σ σ.seedFlush, vidx σ .fin)] else []
  deg := by
    refine ⟨fun C hC ↦ ?_, fun r hr ↦ ?_, fun s hs ↦ ?_⟩
    · obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
      exact d2_ofPoly2 (constraints_d2 _ C' hC')
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hr
      exact keyOf_read_deg _ f hf
    · split at hs
      · simp only [List.mem_singleton] at hs; subst hs
        refine ⟨d2_ofPoly2 (d2_var _), fun P hP ↦ ?_⟩
        obtain ⟨P', hP', rfl⟩ := List.mem_map.mp hP
        exact d2_ofPoly2 (d2_resVals _ P' hP')
      · simp at hs

/-- A **group**: LoopIR pieces of one shape `σ` stacked in one table of `2^τ` rows, each piece
`n` at row offset `off` (`mem`). WP-9 groups each shape's pieces by the binary decomposition of the
shape's total rows (largest first, aligned): no padding row. -/
structure Grp where
  /-- The shape of every member. -/
  σ : Loop.Shape
  /-- Log-height. -/
  τ : Nat
  /-- The members: piece index, row offset. -/
  mem : List (Nat × Nat)
  deriving Inhabited

/-- Member `m = (n, off)` holds row `y`. -/
def Grp.Holds (Q : Program) (m : Nat × Nat) (y : Nat) : Bool :=
  m.2 ≤ y && y < m.2 + 2 ^ Q.height (Q.pieces.getD m.1 default)

/-- The member holding row `y`, and the piece's row there. -/
def Grp.at (Q : Program) (g : Grp) (y : Nat) : Option (Nat × Nat) :=
  (g.mem.find? fun m ↦ Grp.Holds Q m y).map fun m ↦ (m.1, y - m.2)

/-- Fixed column `c` of a group at row `y`: its member's. -/
def grpFix (Q : Program) (g : Grp) (c : FCol) (y : Nat) : FK :=
  match g.at Q y with
  | some (n, x) => Q.fval (Q.pieces.getD n default) c x
  | none => 0

/-- `F̃` of a `fixmul` piece at `r` (loop dimensions `[dc, dx]`, column index fastest):
`Σ_c eq(r_c, c)·G̃_c(r_x)`, `G_c` the glue matrix's column `c` (the basic fixed column of a glue
piece of height `2^h`) on `2^dx` rows: `0` past `2^h` when `h ≤ dx` (the factor `Π (1 - r_x)` above
`h`), truncated to `2^dx` rows when `h > dx` (the piece's closed form at `r_x` padded with zeros).
Exact for every glue height (`LvmM3FidFix.fixFEval_eq`). -/
def fixFEval (Q : Program) (p : Piece) (r : List FE) : FE :=
  let dims := (Q.blk p.blk).dims
  let dc := dims.getD 0 0
  let dx := dims.getD 1 0
  let rc := r.take dc
  let rx := (r.drop dc).take dx
  let ec := eqKernel' rc
  ((Q.glueCols.zipIdx).map fun ((gp, gc), c) ↦
    let h := Q.height gp
    ec.getD c 0 * Q.pieceEval gp gc (rx.take h ++ List.replicate (h - rx.length) 0) *
      ((rx.drop h).map (1 - ·)).foldl (· * ·) 1).foldl (· + ·) 0

/-- A piece's fixed column's closed form (`pieceEval`; `fixFEval` for `F`). -/
def pieceFixEval (Q : Program) (p : Piece) (c : FCol) (r : List FE) : FE :=
  match c with
  | .F => fixFEval Q p r
  | c => Q.pieceEval p c r

/-- A group's fixed column's closed form: `Σ_m eq(sel_m, r_{≥h_m})·(piece m's at r_{<h_m})`. -/
def grpEval (Q : Program) (g : Grp) (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let p := Q.pieces.getD n default
    let h := Q.height p
    eqSel (off >>> h) (r.drop h) * pieceFixEval Q p c (r.take h)).foldl (· + ·) 0

/-- The table of a group. -/
def grpTab (Q : Program) (pl : Var → Bool × Nat) (g : Grp) : Tab :=
  shapeTab g.σ g.τ (grpFix Q g) (grpEval Q g) pl

/-- An input array: rows `x < 2^τ` seed the input cells `base + stride·x` of memory `ty` with the
value columns `val` (placements, one per limb); `fin` places the finalize-count column. A *public*
array (`pub = some (f, e)`, BLUEPRINT A19's `PUB`, for `K` arrays): its value column is not
committed but derived, cell `x` is `f x` (the statement's public values) and `e` evaluates its
extension (from π's header); `val` then only fixes the limb count. -/
structure InArr where
  /-- The memory. -/
  ty : Loop.Ty
  /-- Log-height. -/
  τ : Nat
  /-- The first cell. -/
  base : Nat
  /-- The cell step per row. -/
  stride : Nat
  /-- The value columns' placements (`ty.limbs` of them). -/
  val : List (Bool × Nat)
  /-- The finalize-count column's placement. -/
  fin : Bool × Nat
  /-- A public array's values and their extension's closed form (`none`: committed values). -/
  pub : Option ((Nat → FK) × (List FE → FE)) := none
  deriving Inhabited

/-- The value columns of an input array: the committed placements, or (public array) the derived
column, one per limb. -/
def InArr.vcols (a : InArr) : List ColSrc :=
  match a.pub with
  | some fe => a.val.map fun _ ↦ ColSrc.fix fe.1 fe.2
  | none => a.val.map fun pl ↦ ColSrc.com pl.1 pl.2

@[simp] theorem InArr.length_vcols (a : InArr) : a.vcols.length = a.val.length := by
  unfold InArr.vcols; split <;> simp

/-- The table of an input array: value columns (`vcols`), the finalize count, the fixed address
column. -/
def InArr.tab (a : InArr) : Tab where
  τ := a.τ
  cols := a.vcols ++
    [.com a.fin.1 a.fin.2, .fix (fun x ↦ FK.x ^ (a.base + a.stride * x))
      (fun r ↦ FE.ofK (FK.x ^ a.base) * powEval r (FK.x ^ a.stride))]
  cons := []
  reads := []
  seeds := [(⟨sep a.ty, CPoly.var (a.val.length + 1), (List.range a.val.length).map CPoly.var⟩,
    a.val.length)]
  deg := by
    refine ⟨fun C hC ↦ by simp at hC, fun r hr ↦ by simp at hr, fun s hs ↦ ?_⟩
    simp only [List.mem_singleton] at hs; subst hs
    have hv : ∀ i, CPoly.Deg2 (CPoly.var i) := fun i m hm ↦ by
      simp [CPoly.var] at hm; subst hm; simp
    refine ⟨hv _, fun P hP ↦ ?_⟩
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hP; exact hv _

/-- **The tables of the lvm instance**: the groups of `Q`'s pieces (group `i` placed by `pl i`), the
input arrays, the auxiliary tables. -/
def lvmTabs (Q : Program) (pl : Nat → Var → Bool × Nat) (groups : List Grp) (arrs : List InArr)
    (aux : List Tab) : List Tab :=
  (List.range groups.length).map (fun i ↦ grpTab Q (pl i) (groups.getD i default)) ++
    arrs.map InArr.tab ++ aux

end Lvm.M3
