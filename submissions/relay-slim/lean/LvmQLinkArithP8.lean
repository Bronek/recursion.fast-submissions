import LvmQLinkArithKS

/-!
# QA1 links: the `P8` instance (smoke check of `ksLink_sound`)

The `KS` link's template check (`SLok`) is discharged by evaluation at `P8`'s sizes (lvm2 S2: `ksLog = 14`,
`recRowsLog = 13`, `spongeBlocks P8` from `sizes_P8`). S2 has no `CH` link.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

theorem spongeBlocks_P8 : spongeBlocks P8 = 3247 := by
  rw [spongeBlocks, sizes_P8.2.2.2.2.2.2.2.1]

/-! ## The template check does not read addresses -/

/-- An operand with its address forgotten. -/
def Src.shape : Src → Src
  | .ext _ => .ext default
  | s => s

/-- An instruction with its addresses forgotten. -/
def Ins.shape (i : Ins) : Ins := ⟨i.op, i.ty, i.args.map Src.shape⟩

theorem getD_map_shape (ins : List Ins) (k : Nat) :
    (ins.map Ins.shape).getD k default = (ins.getD k default).shape := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ins[k]? <;> rfl

theorem locOk_shape (ins : List Ins) (k : Nat) (i : Ins) :
    i.shape.locOk (ins.map Ins.shape) k = i.locOk ins k := by
  simp only [Ins.locOk, Ins.shape, List.all_map, getD_map_shape, List.length_map]
  congr 1
  congr 1
  funext s
  cases s <;> rfl

/-- **`SLok` of a template is that of its shape.** -/
theorem SLok_shape (ins : List Ins) : SLok (ins.map Ins.shape) = SLok ins := by
  simp only [SLok, List.length_map, getD_map_shape, locOk_shape]

/-! ## Combinators commute with forgetting addresses -/

/-- Two operand lists with the same shape. -/
def SameShape (xs ys : List Src) : Prop := xs.map Src.shape = ys.map Src.shape

theorem shape_loc (k : Nat) : (Src.loc k).shape = .loc k := rfl

theorem map_cellSrc_shape (l : List Cell) : (l.map cellSrc).map Src.shape = List.replicate l.length (.ext default) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]; rfl

theorem shape_mulI (a b d : Src) : (mulI a b d).shape = mulI a.shape b.shape d.shape := rfl
theorem shape_linI (k k' : FK) (a b : Src) : (linI k k' a b).shape = linI k k' a.shape b.shape := rfl
theorem shape_addI (a b : Src) : (addI a b).shape = addI a.shape b.shape := rfl
theorem shape_shape (s : Src) : s.shape.shape = s.shape := by cases s <;> rfl

theorem dotIns_shape : ∀ (n : Nat) (s : Src) (ps : List (Src × Src)),
    (dotIns n s ps).map Ins.shape = (dotIns n s.shape (ps.map fun ab => (ab.1.shape, ab.2.shape))).map Ins.shape
  | _, _, [] => rfl
  | n, s, (a, b) :: ps => by
    simp only [dotIns, List.map_cons, shape_mulI, shape_shape, dotIns_shape (n + 1) (.loc n) ps]
    rfl

theorem mulChainIns_shape (z : Src) : ∀ (n : Nat) (s : Src) (cs : List Src),
    (mulChainIns z n s cs).map Ins.shape = (mulChainIns z n s.shape (cs.map Src.shape)).map Ins.shape
  | _, _, [] => rfl
  | n, s, c :: cs => by
    simp only [mulChainIns, List.map_cons, shape_mulI, shape_shape, mulChainIns_shape z (n + 1) (.loc n) cs]
    rfl

theorem shiftRecE_shape (n : Nat) : ∀ (xs ys : List Src) (E0 : Src),
    (shiftRecE n (xs.map Src.shape) (ys.map Src.shape) E0.shape).shape = (shiftRecE n xs ys E0).shape
  | _ :: _, _ :: _, _ => by simp [shiftRecE]
  | [], _, _ => by simp [shiftRecE, shape_shape]
  | _ :: _, [], _ => by simp [shiftRecE, shape_shape]

theorem shiftRecS_shape (n : Nat) : ∀ (xs ys : List Src) (S0 : Src),
    (shiftRecS n (xs.map Src.shape) (ys.map Src.shape) S0.shape).shape = (shiftRecS n xs ys S0).shape
  | _ :: _, _ :: _, _ => by simp [shiftRecS]
  | [], _, _ => by simp [shiftRecS, shape_shape]
  | _ :: _, [], _ => by simp [shiftRecS, shape_shape]

theorem shiftRecIns_shape (z : Src) (n : Nat) : ∀ (xs ys : List Src) (E0 S0 : Src),
    (shiftRecIns z n xs ys E0 S0).map Ins.shape =
      (shiftRecIns z.shape n (xs.map Src.shape) (ys.map Src.shape) E0.shape S0.shape).map Ins.shape
  | x0 :: x, y0 :: y, E0, S0 => by
    simp only [List.map_cons, shiftRecIns, List.map_append, shiftRecIns_shape z n x y E0 S0, List.length_map]
    congr 1
    simp only [shiftLevel, List.map_cons, List.map_nil, shape_mulI, shape_linI, shape_shape, shape_loc,
      shiftRecE_shape, shiftRecS_shape]
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem preRecOut_shape (n : Nat) : ∀ (xs ys : List Src) (base : Src × Src × Src),
    preRecOut n (xs.map Src.shape) (ys.map Src.shape) (base.1.shape, base.2.1.shape, base.2.2.shape) =
      ((preRecOut n xs ys base).1.shape, (preRecOut n xs ys base).2.1.shape, (preRecOut n xs ys base).2.2.shape)
  | _ :: _, _ :: _, _ => by simp [preRecOut, shape_loc]
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl

theorem preRecIns_shape (z : Src) (n : Nat) : ∀ (xs ys : List Src) (H : Nat) (base : Src × Src × Src),
    (preRecIns z n xs ys H base).map Ins.shape =
      (preRecIns z.shape n (xs.map Src.shape) (ys.map Src.shape) H
        (base.1.shape, base.2.1.shape, base.2.2.shape)).map Ins.shape
  | x0 :: x, y0 :: y, H, base => by
    simp only [List.map_cons, preRecIns, List.map_append, preRecIns_shape z n x y (H / 2) base, List.length_map,
      preRecOut_shape]
    congr 1
    simp only [preLevel, List.map_cons, List.map_nil, shape_mulI, shape_linI, shape_addI, shape_shape, shape_loc]
    split <;> simp [shape_mulI, shape_shape, shape_loc]
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl

theorem eqLevelIns_shape (z : Src) (n : Nat) (olds : List Src) (r : Src) :
    (eqLevelIns z n olds r).map Ins.shape = (eqLevelIns z.shape n (olds.map Src.shape) r.shape).map Ins.shape := by
  simp only [eqLevelIns, List.map_cons, shape_linI, shape_shape, List.length_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  simp only [Function.comp_def]
  split
  · rename_i h; simp only [shape_mulI, shape_shape, shape_loc]
    rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, shape_shape]
  · rename_i h; simp only [shape_mulI, shape_shape]
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, shape_shape]

theorem eqLevelOut_shape (n m : Nat) : (eqLevelOut n m).map Src.shape = eqLevelOut n m := by
  unfold eqLevelOut; rw [List.map_map]; rfl

theorem eqTabGo_shape (z : Src) : ∀ (rs : List Src) (n : Nat) (olds : List Src),
    (eqTabGo z n olds rs).map Ins.shape = (eqTabGo z.shape n (olds.map Src.shape) (rs.map Src.shape)).map Ins.shape
  | [], _, _ => rfl
  | r :: rs, n, olds => by
    simp only [eqTabGo, List.map_cons, List.map_append, List.length_map]
    rw [eqLevelIns_shape, eqTabGo_shape z rs, eqLevelOut_shape]

theorem shape_cellSrc (c : Cell) : (cellSrc c).shape = .ext default := rfl

theorem shape_ins_mk (op : Op) (ty : Ty) (args : List Src) :
    (⟨op, ty, args⟩ : Ins).shape = ⟨op, ty, args.map Src.shape⟩ := rfl

theorem shape_getD_mapCellSrc {α : Type} (f : α → Cell) (l : List α) (i : Nat) :
    ((l.map fun x => cellSrc (f x)).getD i default).shape = .ext default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem eqTabOut_len : ∀ (n : Nat) (olds rs rs' : List Src), rs.length = rs'.length →
    eqTabOut n olds rs = eqTabOut n olds rs'
  | _, _, [], [], _ => rfl
  | n, olds, _ :: rs, _ :: rs', h => by
    simp only [eqTabOut]; exact eqTabOut_len _ _ rs rs' (by simpa using h)
  | _, _, [], _ :: _, h => by simp at h
  | _, _, _ :: _, [], h => by simp at h

theorem eMus_any (c₀ c₁ : Cell) : eMus [c₀, c₁] = eMus [default, default] := by
  funext m; unfold eMus
  rw [eqTabOut_len 66 [.loc 65] ([c₀, c₁].map cellSrc) ([default, default].map cellSrc) (by simp)]

theorem shape_getD_cellSrc (l : List Cell) (i : Nat) : ((l.map cellSrc).getD i default).shape = .ext default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> rfl

theorem loadsAt_shape (q s N : Nat) : (loadsAt q s N).map Ins.shape = (loadsAt 0 0 N).map Ins.shape := by
  simp only [loadsAt, List.map_map]; rfl

/-- A placeholder loop output (only its shape matters to `SLok`). -/
def defOut : LoopOut := ⟨⟨0, 0⟩, [], []⟩

theorem okE_P8 (Q : Nat) (gate : Cell) (sh : LoopOut) :
    SLok (ksGlueE 14 Q (ksQV 14 Q) 3246 (2 ^ 13 + 399 + 31) (2 ^ 13 + 399) (rho'C sh 14) (sh.cell 2 13)
      (sh.cell 5 (14 - 1)) gate) = true := by
  rw [← SLok_shape]
  simp only [ksGlueE, List.map_append]
  rw [loadsAt_shape, loadsAt_shape (q := ksQV 14 Q), preRecIns_shape, preRecIns_shape (n := 13 * 14 + 6),
    preRecIns_shape (n := 25 * 14 + 6), mulChainIns_shape]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def, shape_cellSrc, shape_mulI, shape_linI, shape_addI, shape_loc, shape_shape, shape_getD_cellSrc, rhoC, rho'C, eZC, eLC, preP, List.length_map, List.length_range, shape_ins_mk, shape_getD_mapCellSrc, eMus_any]
  decide +kernel

/-- **`P8`'s `KS` link circuit is sound.** -/
theorem ksLink_sound_P8 {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)} {tfv : Pub → List FE → List FE}
    {tfs : Pub → List (List FE × List FE) → List FE} {tpc : Pub → List (List FE × List FE) → Bool}
    {c : Ctx} {M : Mem} {ptr : Ptr} {sig : ByteArray} {T P Q : Nat} (rk : List FE) (pub : Pub)
    (gate : Cell) (hPQ : P + 40 = 8 * Q) (hS : Streamed M sig T) (hT : ksQV 14 Q + 3 * 4 + 3 ≤ T)
    (hg : gate.val M = 1) (h : SegsHold c M ptr (ksLinkGadget P8 4 Q gate ptr).2)
    (hA : SegsAssert M ptr (ksLinkGadget P8 4 Q gate ptr).2) :
    (ksLink0 P8 (ksLinkView P8 (M3.ofParts P8 bf tb tcl tfv tfs tpc) (feAt sig) P rk pub)).1 = true :=
  ksLink_sound P8 4 rk pub gate (by decide) (by decide) (by decide) hPQ (by rw [spongeBlocks_P8]; decide)
    (by rw [spongeBlocks_P8]; decide) (by decide)
    (fun sh => by rw [spongeBlocks_P8]; exact okE_P8 Q gate sh) hS hT hg h hA

end Lvm.Q1
