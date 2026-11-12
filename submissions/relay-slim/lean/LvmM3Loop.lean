-- new for lvm (WP-9): the LoopIR tables (WP-10, `LvmLoopTable`) as tables of the lvm M3 instance
-- (`LvmM3Inst`), and the bus hypotheses of WP-10's `loopir_sound` (`LvmLoopSound.lean:348`) from
-- `M3Holds` through `mem_lookup` (`LvmBusIMem`).
import LvmBusIMem
import LvmLoopSound
import LvmM3LoopTab

/-!
# The LoopIR tables in the M3 instance, and the bus bridge to `loopir_sound`

**Tables.** `lvmTabs Q pl groups arrs aux` lists the tables of the lvm instance: one per LoopIR piece
(`pieceTab`, piece `n` is table `n`), one per input array (`InArr.tab`), then auxiliary tables
(`BITS`; they read, they seed nothing). A piece's columns are its shape's committed columns,
placed by `pl n`, then its fixed columns (derived: `Q.fval`); its constraints, reads and seed are
WP-10's (`Shape.constraints`, `readFlushes`, `seedFlush`/`finFlush`) with variables renamed to
column indices. An input array of type `τ` seeds, at row `x`, the input cell `base + stride·x`
of memory `τ` with its value columns (one or three limbs); its address column is fixed.

**The witness on the stack** (`witOf`, `inKOf`, `inEOf`): piece `n`'s committed value of a
variable at row `x` is its column's cell; input cell `e` is the value of the input array row that
seeds it (`0` if none does).

**The bridge** (`loop_bus`): `M3Holds` of the instance (its `Balanced` and `CountsNonzero`
clauses), the input arrays' layout facts (`InOk`), count columns inside the widths and fewer than
`2^64 - 1` reads give WP-10's `hbus` verbatim; `loop_ginj` gives its `hinj` when the program has at
most `2^64 - 1` cells of each memory; `inKOf_size`/`inEOf_size` its `hsz`.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval
open Lvm.Loop

theorem toBF64_prodK (l : List FK) : FK.toBF64 (prodK l) = (l.map FK.toBF64).prod := by
  induction l with
  | nil => simp [prodK]
  | cons a l ih => simp [prodK, ih]

/-- Evaluating the renamed polynomial at a row is evaluating the LoopIR polynomial at the
variables' values, when the row holds them. -/
theorem evalB_ofPoly2 (u : ℕ → K) (v : Var → FK) (idx : Var → ℕ) (P : Poly2)
    (h : ∀ m ∈ P, ∀ y ∈ m.vars, u (idx y) = FK.toBF64 (v y)) :
    CPoly.evalB u (ofPoly2 idx P) = FK.toBF64 (P.ev v) := by
  induction P with
  | nil => simp [ofPoly2, CPoly.evalB, Poly2.ev]
  | cons m P ih =>
    have ih' := ih fun m' hm' ↦ h m' (List.mem_cons_of_mem _ hm')
    simp only [ofPoly2, CPoly.evalB, List.map_cons, List.sum_cons] at ih' ⊢
    simp only [Poly2.ev, List.foldr_cons] at ih' ⊢
    rw [ih', FK.toBF64_add, FK.toBF64_mul, toBF64_prodK, List.map_map, List.map_map]
    congr 2
    exact congrArg List.prod (List.map_congr_left (f := u ∘ idx) (g := FK.toBF64 ∘ v)
      fun y hy ↦ h m (List.mem_cons_self ..) y hy)

/-! ## Facts the instance needs -/

/-- The input arrays' facts: limb counts, cells below the input counts, one seed per cell, every
input cell seeded. -/
structure InOk (Q : Program) (arrs : List InArr) : Prop where
  /-- One value column per limb. -/
  limbs : ∀ a ∈ arrs, a.val.length = a.ty.limbs
  /-- The seeded cells are input cells. -/
  lt : ∀ a ∈ arrs, ∀ x < 2 ^ a.τ, a.base + a.stride * x < Q.nIn a.ty
  /-- No cell is seeded twice. -/
  inj : ∀ (i i' : Fin arrs.length) (x x' : ℕ), x < 2 ^ (arrs.get i).τ → x' < 2 ^ (arrs.get i').τ →
    (arrs.get i).ty = (arrs.get i').ty →
    (arrs.get i).base + (arrs.get i).stride * x = (arrs.get i').base + (arrs.get i').stride * x' →
    i = i' ∧ x = x'
  /-- Every input cell is seeded (the inputs cover `[0, nIn τ)`; replay reads every input). -/
  cover : ∀ τ : Loop.Ty, ∀ e < Q.nIn τ, ∃ a ∈ arrs, a.ty = τ ∧ ∃ x < 2 ^ a.τ, a.base + a.stride * x = e

section Bridge

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **The lvm M3 instance.** -/
noncomputable abbrev lvmInst : M3Instance := inst L (lvmTabs Q pl groups arrs aux) hτ

theorem lvmTabs_length :
    (lvmTabs Q pl groups arrs aux).length = groups.length + arrs.length + aux.length := by
  simp [lvmTabs]; omega

theorem get_grp {i : ℕ} (hi : i < groups.length) (h : i < (lvmTabs Q pl groups arrs aux).length) :
    (lvmTabs Q pl groups arrs aux).get ⟨i, h⟩ = grpTab Q (pl i) groups[i] := by
  simp only [List.get_eq_getElem, lvmTabs]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
  simp [List.getElem?_eq_getElem hi]

theorem get_arr {k : ℕ} (hk : k < arrs.length) (h : groups.length + k < (lvmTabs Q pl groups arrs aux).length) :
    (lvmTabs Q pl groups arrs aux).get ⟨groups.length + k, h⟩ = arrs[k].tab := by
  simp only [List.get_eq_getElem, lvmTabs]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
  simp

theorem get_aux {k : ℕ} (hk : k < aux.length)
    (h : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length) :
    (lvmTabs Q pl groups arrs aux).get ⟨groups.length + arrs.length + k, h⟩ = aux[k] := by
  simp only [List.get_eq_getElem, lvmTabs]
  rw [List.getElem_append_right (by simp)]
  simp

/-- The value of a fixed column at a row is its function's. -/
theorem row_fixed (q : Column L.μ) (j : Fin (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get j).τ)) (i : Fin ((lvmTabs Q pl groups arrs aux).get j).w)
    {f : ℕ → FK} (hf : ((lvmTabs Q pl groups arrs aux).get j).fixedOf i = some f) :
    (lvmInst Q pl groups arrs aux L hτ).row q j x i = FK.toBF64 (f x) := by
  simp only [M3Instance.row, M3Instance.column, inst, hf, Option.map_some, Option.elim_some,
    fixedColumn, Vector.get_ofFn]

/-- Where piece `n` sits: its group and row offset (the first member naming it). -/
def loc (groups : List Grp) (n : ℕ) : Option (ℕ × ℕ) :=
  (List.range groups.length).findSome? fun i ↦
    ((groups.getD i default).mem.find? fun m ↦ m.1 == n).map fun m ↦ (i, m.2)

/-- **The LoopIR witness on the stack**: piece `n`'s committed variable `u` at row `x` is its
column's cell in its group's table, at the piece's offset (`0` past the tables). -/
noncomputable def witOf (q : Column L.μ) : Witness := fun n x u ↦
  match loc groups n with
  | some (i, off) =>
    if h : i < (lvmTabs Q pl groups arrs aux).length then
      if hx : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ then
        if hi : vidx (Q.pieces.getD n default).shape u < ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).w then
          FK.ofBF64 ((lvmInst Q pl groups arrs aux L hτ).row q ⟨i, h⟩ ⟨off + x, hx⟩ ⟨_, hi⟩)
        else 0
      else 0
    else 0
  | none => 0

/-- The input array row seeding cell `e` of memory `τ`, if any: the first array that does. -/
def findIn (τ : Loop.Ty) (e : ℕ) : Option (ℕ × ℕ) :=
  (List.range arrs.length).findSome? fun k ↦
    ((List.range (2 ^ (arrs.getD k default).τ)).find? fun x ↦
      (arrs.getD k default).ty = τ ∧
        (arrs.getD k default).base + (arrs.getD k default).stride * x = e).map (k, ·)

/-- Limb `l` of the input array row `(k, x)` read off the stack (`0` outside). -/
noncomputable def inVal (q : Column L.μ) (k x l : ℕ) : FK :=
  if h : groups.length + k < (lvmTabs Q pl groups arrs aux).length then
    if hx : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, h⟩).τ then
      if hl : l < ((lvmTabs Q pl groups arrs aux).get ⟨_, h⟩).w then
        FK.ofBF64 ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, h⟩ ⟨x, hx⟩ ⟨l, hl⟩)
      else 0
    else 0
  else 0

/-- **The `K` inputs on the stack.** -/
noncomputable def inKOf (q : Column L.μ) : Array FK :=
  Array.ofFn (n := Q.nInK) fun e ↦
    match findIn arrs .K e with
    | some (k, x) => inVal Q pl groups arrs aux L hτ q k x 0
    | none => 0

/-- **The `E` inputs on the stack.** -/
noncomputable def inEOf (q : Column L.μ) : Array FE :=
  Array.ofFn (n := Q.nInE) fun e ↦
    match findIn arrs .E e with
    | some (k, x) => ⟨inVal Q pl groups arrs aux L hτ q k x 0, inVal Q pl groups arrs aux L hτ q k x 1,
        inVal Q pl groups arrs aux L hτ q k x 2⟩
    | none => 0

theorem inKOf_size (q : Column L.μ) : (inKOf Q pl groups arrs aux L hτ q).size = Q.nInK := by
  simp [inKOf]

theorem inEOf_size (q : Column L.μ) : (inEOf Q pl groups arrs aux L hτ q).size = Q.nInE := by
  simp [inEOf]

end Bridge

/-! ## `g`-power injectivity -/

/-- **WP-10's `hinj`**: `g`-powers are injective below `N ≤ 2^64 - 1`. -/
theorem loop_ginj {N : ℕ} (hN : N ≤ 2 ^ 64 - 1) : GInj N :=
  fun _ _ ha hb h ↦ FK.FKx_pow_inj (by omega) (by omega) h

/-! ## Messages as tuples -/

/-- A LoopIR message as sixteen coordinates: separator, address, count, value limbs, zeros. -/
def encT (m : Loop.Msg) : Vector K 16 := Vector.ofFn fun k ↦
  if k.val = 0 then FK.toBF64 m.sep else if k.val = 1 then FK.toBF64 m.addr
  else if k.val = 2 then FK.toBF64 m.cnt else FK.toBF64 (m.val.getD (k.val - 3) 0)

/-- A message of memory `τ`: its separator and its limb count. -/
def Shaped (m : Loop.Msg) : Prop := ∃ τ : Loop.Ty, m.sep = sep τ ∧ m.val.length = τ.limbs

theorem sep_ne : sep Loop.Ty.K ≠ sep Loop.Ty.E := by
  intro h
  have := FK.FKx_pow_inj (a := 3) (b := 4) (by norm_num) (by norm_num) h
  omega

theorem sep_inj' {τ τ' : Loop.Ty} (h : sep τ = sep τ') : τ = τ' := by
  cases τ <;> cases τ' <;> first | rfl | exact absurd h sep_ne | exact absurd h.symm sep_ne

theorem keyT_coord {t t' : Vector K 16} (h : keyT t = keyT t') (k : ℕ) (hk : k < 16) (hk2 : k ≠ 2) :
    t[k] = t'[k] := by
  have := congrArg (·[k]) h
  simpa [keyT, hk2] using this

/-- **Equal tuple keys are equal message keys**, for shaped messages. -/
theorem key_of_keyT {m m' : Loop.Msg} (hm : Shaped m) (hm' : Shaped m')
    (h : keyT (encT m) = keyT (encT m')) : m.key = m'.key := by
  obtain ⟨τ, hs, hl⟩ := hm
  obtain ⟨τ', hs', hl'⟩ := hm'
  have h0 := keyT_coord h 0 (by norm_num) (by norm_num)
  have h1 := keyT_coord h 1 (by norm_num) (by norm_num)
  simp only [encT, Vector.getElem_ofFn] at h0 h1
  simp only [if_true, show ¬ (1 = 0) from by decide, if_false] at h0 h1
  have hsep : m.sep = m'.sep := FK.toBF64_injective h0
  have hτ : τ = τ' := sep_inj' (hs.symm.trans (hsep.trans hs'))
  subst hτ
  have hlen : m.val.length = m'.val.length := hl.trans hl'.symm
  have hlim : τ.limbs ≤ 3 := by cases τ <;> simp [Loop.Ty.limbs]
  have hval : m.val = m'.val := by
    apply List.ext_getElem hlen
    intro l hl1 hl2
    have hc := keyT_coord h (l + 3) (by omega) (by omega)
    simp only [encT, Vector.getElem_ofFn, show l + 3 ≠ 0 from by omega,
      show l + 3 ≠ 1 from by omega, show l + 3 ≠ 2 from by omega, if_false,
      Nat.add_sub_cancel] at hc
    have := FK.toBF64_injective hc
    rwa [List.getD_eq_getElem _ _ hl1, List.getD_eq_getElem _ _ hl2] at this
  simp only [Loop.Msg.key, hsep, FK.toBF64_injective h1, hval]

/-- The key of an evaluated table message is the key of a LoopIR message, when the separators,
addresses and value limbs agree. -/
theorem keyT_vec_eq {w : ℕ} (r : Fin w → K) (k : Key) (cnt : CPoly) (m : Loop.Msg)
    (hs : k.sep = m.sep) (ha : CPoly.evalB (CPoly.ext r) k.addr = FK.toBF64 m.addr)
    (hl : k.val.length = m.val.length)
    (hv : ∀ l (h1 : l < k.val.length) (h2 : l < m.val.length),
      CPoly.evalB (CPoly.ext r) k.val[l] = FK.toBF64 m.val[l]) :
    keyT (evalV r (k.vec w cnt)) = keyT (encT m) := by
  apply Vector.ext; intro i hi
  simp only [keyT, Vector.getElem_ofFn, Fin.getElem_fin, evalV, Vector.getElem_map, Key.vec, encT]
  by_cases h2 : i = 2
  · simp [h2]
  by_cases h0 : i = 0
  · subst h0; simp [hs]
  by_cases h1 : i = 1
  · subst h1; simp [CPoly.eval_toMv, ha]
  simp only [h0, h1, h2, if_false, CPoly.eval_toMv]
  rcases Nat.lt_or_ge (i - 3) k.val.length with h | h
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (hl ▸ h), hv _ h (hl ▸ h)]
  · rw [List.getD_eq_default _ _ h, List.getD_eq_default _ _ (hl ▸ h)]
    simp [CPoly.evalB]

/-! ## Fixed variables of the flushes are columns -/

/-- The fixed variables of a polynomial are among the shape's columns. -/
def FixIn (σ : Loop.Shape) (P : Poly2) : Prop :=
  ∀ m ∈ P, ∀ y ∈ m.vars, ∀ c, y = .fix c → y ∈ shapeVars σ

theorem fixIn_var_nonfix (σ : Loop.Shape) (u : Var) (hu : ∀ c, u ≠ .fix c) : FixIn σ (Poly2.var u) := by
  intro m hm y hy c hc
  simp [Poly2.var] at hm; subst hm; simp at hy; subst hy; exact absurd hc (hu c)

theorem fixIn_var_fix (σ : Loop.Shape) (c : FCol) (hc : c ∈ σ.fcols) : FixIn σ (Poly2.var (.fix c)) := by
  intro m hm y hy c' _
  simp [Poly2.var] at hm; subst hm; simp at hy; subst hy
  exact List.mem_append_right _ (List.mem_map_of_mem hc)

theorem read_fixIn (σ : Loop.Shape) (f : Flush) (hf : f ∈ σ.readFlushes) :
    FixIn σ f.addr ∧ ∀ P ∈ f.val, FixIn σ P := by
  simp only [Loop.Shape.readFlushes, List.mem_append, List.mem_map, List.mem_range] at hf
  rcases hf with ⟨o, ho, rfl⟩ | hf
  · refine ⟨fixIn_var_fix σ _ ?_, fun P hP ↦ ?_⟩
    · simp [Loop.Shape.fcols, ho]
    · simp only [Loop.Shape.argVals, List.mem_map] at hP
      obtain ⟨l, -, rfl⟩ := hP
      exact fixIn_var_nonfix σ _ (fun c h ↦ by cases h)
  · split at hf
    · simp only [List.mem_singleton] at hf; subst hf
      refine ⟨fixIn_var_nonfix σ _ (fun c h ↦ by cases h), fun P hP ↦ ?_⟩
      simp only [Loop.Shape.resVals, List.mem_map] at hP
      obtain ⟨l, -, rfl⟩ := hP
      exact fixIn_var_nonfix σ _ (fun c h ↦ by cases h)
    · simp at hf

theorem seed_fixIn (σ : Loop.Shape) (hw : σ.writes = true) :
    FixIn σ σ.seedFlush.addr ∧ ∀ P ∈ σ.seedFlush.val, FixIn σ P := by
  refine ⟨fixIn_var_fix σ _ (by simp [Loop.Shape.fcols, hw]), fun P hP ↦ ?_⟩
  simp only [Loop.Shape.seedFlush, Loop.Shape.resVals, List.mem_map] at hP
  obtain ⟨l, -, rfl⟩ := hP
  exact fixIn_var_nonfix σ _ (fun c h ↦ by cases h)

theorem read_shaped (σ : Loop.Shape) (f : Flush) (hf : f ∈ σ.readFlushes) (v : Var → FK) :
    Shaped (f.msg v) := by
  simp only [Loop.Shape.readFlushes, List.mem_append, List.mem_map, List.mem_range] at hf
  rcases hf with ⟨o, -, rfl⟩ | hf
  · exact ⟨σ.args.getD o .K, rfl, by simp [Flush.msg, Loop.Shape.argVals, Loop.Shape.argLimbs]⟩
  · split at hf
    · simp only [List.mem_singleton] at hf; subst hf
      exact ⟨σ.ty, rfl, by simp [Flush.msg, Loop.Shape.resVals]⟩
    · simp at hf

theorem seed_shaped (σ : Loop.Shape) (v : Var → FK) : Shaped (σ.seedFlush.msg v) :=
  ⟨σ.ty, rfl, by simp [Flush.msg, Loop.Shape.seedFlush, Loop.Shape.resVals]⟩

section Bridge2

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr) (aux : List Tab) (L : Lay)
  (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The groups' facts: members are pieces of the group's shape inside its rows, members are
disjoint and cover the rows, every piece is in exactly one group, at one offset. -/
structure GrpOk (Q : Program) (groups : List Grp) : Prop where
  /-- A member is a piece of the group's shape, inside the group's rows. -/
  mem : ∀ g ∈ groups, ∀ m ∈ g.mem, ∃ p, Q.pieces[m.1]? = some p ∧ p.shape = g.σ ∧
    m.2 + 2 ^ Q.height p ≤ 2 ^ g.τ ∧ 2 ^ Q.height p ∣ m.2
  /-- One member holds a row. -/
  disj : ∀ g ∈ groups, ∀ m ∈ g.mem, ∀ m' ∈ g.mem, ∀ y, Grp.Holds Q m y = true →
    Grp.Holds Q m' y = true → m = m'
  /-- Every row of a group is a member's. -/
  cover : ∀ g ∈ groups, ∀ y < 2 ^ g.τ, ∃ m ∈ g.mem, Grp.Holds Q m y = true
  /-- Every piece is a member. -/
  all : ∀ n < Q.pieces.length, ∃ i, ∃ h : i < groups.length, ∃ off, (n, off) ∈ groups[i].mem
  /-- At one place. -/
  uniq : ∀ i i' (h : i < groups.length) (h' : i' < groups.length) n off off',
    (n, off) ∈ groups[i].mem → (n, off') ∈ groups[i'].mem → i = i' ∧ off = off'
  /-- No member is listed twice (a group's fixed columns sum over its members). -/
  nodup : ∀ g ∈ groups, g.mem.Nodup

theorem loc_eq (hg : GrpOk Q groups) {i n off : ℕ} (hi : i < groups.length)
    (hm : (n, off) ∈ groups[i].mem) : loc groups n = some (i, off) := by
  have hgd : ∀ i' (h : i' < groups.length), groups.getD i' default = groups[i'] := fun i' h ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  have hsome : (loc groups n).isSome := by
    unfold loc
    rw [List.findSome?_isSome_iff]
    refine ⟨i, List.mem_range.mpr hi, ?_⟩
    rw [Option.isSome_map, List.find?_isSome, hgd i hi]
    exact ⟨_, hm, by simp⟩
  obtain ⟨⟨i1, off1⟩, hres⟩ := Option.isSome_iff_exists.mp hsome
  rw [hres]
  unfold loc at hres
  obtain ⟨i1', hi1, hF⟩ := List.exists_of_findSome?_eq_some hres
  obtain ⟨m, hfind, heq⟩ := Option.map_eq_some_iff.mp hF
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hi1l : i1' < groups.length := List.mem_range.mp hi1
  have hpr := List.find?_some hfind
  have hmm := List.mem_of_find?_eq_some hfind
  rw [hgd i1' hi1l] at hmm
  simp only [beq_iff_eq] at hpr
  obtain ⟨m1, m2⟩ := m
  simp only at hpr; subst hpr
  obtain ⟨h1, h2⟩ := hg.uniq i1' i hi1l hi _ _ _ hmm hm
  rw [h1, h2]

theorem at_eq (hg : GrpOk Q groups) {g : Grp} (hgm : g ∈ groups) {n off y : ℕ}
    (hm : (n, off) ∈ g.mem) (hy : Grp.Holds Q (n, off) y = true) : g.at Q y = some (n, y - off) := by
  have hsome : (g.mem.find? fun m ↦ Grp.Holds Q m y).isSome := by
    rw [List.find?_isSome]; exact ⟨_, hm, hy⟩
  obtain ⟨m, hm'⟩ := Option.isSome_iff_exists.mp hsome
  have := hg.disj g hgm m (List.mem_of_find?_eq_some hm') _ hm y
    (List.find?_some (p := fun m ↦ Grp.Holds Q m y) hm') hy
  subst this
  simp [Grp.at, hm']

/-- **A group row on the stack holds the witness's values**: at row `off + x` of the table of the
group holding piece `n` at `off`, at the column of a variable, the row holds the variable's value
under `witOf` (fixed variables: when they are columns). -/
theorem ext_row_grp (hg : GrpOk Q groups) (q : Column L.μ) {i n off x : ℕ} {p : Piece}
    (hi : i < groups.length) (hm : (n, off) ∈ groups[i].mem) (hp : Q.pieces[n]? = some p)
    (hx : x < 2 ^ Q.height p) (h : i < (lvmTabs Q pl groups arrs aux).length)
    (hy : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ) (u : Var)
    (hu : ∀ c, u = .fix c → u ∈ shapeVars p.shape) :
    CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨i, h⟩ ⟨off + x, hy⟩) (vidx p.shape u) =
      FK.toBF64 (Q.rowVal (witOf Q pl groups arrs aux L hτ q) n p x u) := by
  have hget := get_grp Q pl groups arrs aux hi h
  obtain ⟨p', hp', hσ, -, -⟩ := hg.mem _ (List.getElem_mem hi) _ hm
  simp only at hp'
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  have hw : ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).w = (shapeVars p.shape).length := by
    rw [hget, hσ]; simp [grpTab, shapeTab, Tab.w]
  by_cases hfix : ∃ c, u = .fix c
  · obtain ⟨c, rfl⟩ := hfix
    have hmem := hu c rfl
    have hil : vidx p.shape (.fix c) < ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).w := by
      rw [hw]; exact List.idxOf_lt_length_of_mem hmem
    have hfx : ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).fixedOf (vidx p.shape (.fix c)) =
        some (grpFix Q groups[i] c) := by
      rw [hget]
      simp only [Tab.fixedOf, grpTab, shapeTab, List.getElem?_map, vidx, ← hσ]
      rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hmem),
        List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)]
      rfl
    simp only [CPoly.ext, dif_pos hil]
    rw [row_fixed Q pl groups arrs aux L hτ q ⟨i, h⟩ ⟨off + x, hy⟩ ⟨_, hil⟩ hfx]
    have hpd : Q.pieces.getD n default = p := by simp [List.getD_eq_getElem?_getD, hp]
    have hholds : Grp.Holds Q (n, off) (off + x) = true := by
      simp [Grp.Holds, hp, hx]
    simp only [grpFix, at_eq Q groups hg (List.getElem_mem hi) hm hholds, hpd,
      Nat.add_sub_cancel_left]
    rfl
  · have hrv : Q.rowVal (witOf Q pl groups arrs aux L hτ q) n p x u =
        witOf Q pl groups arrs aux L hτ q n x u := by
      cases u <;> first | rfl | exact absurd ⟨_, rfl⟩ hfix
    rw [hrv]
    have hgd : Q.pieces.getD n default = p := by simp [List.getD_eq_getElem?_getD, hp]
    simp only [witOf, loc_eq Q groups hg hi hm, dif_pos h, dif_pos hy, CPoly.ext, hgd]
    split <;> simp

/-- Under `InOk`, the first array row seeding cell `base + stride·x` of array `k`'s memory is
`(k, x)`. -/
theorem findIn_eq (hok : InOk Q arrs) {k x : ℕ} (hk : k < arrs.length) (hx : x < 2 ^ arrs[k].τ) :
    findIn arrs arrs[k].ty (arrs[k].base + arrs[k].stride * x) = some (k, x) := by
  have hgd : ∀ k' (h : k' < arrs.length), arrs.getD k' default = arrs[k'] := fun k' h ↦ by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  have hsome : (findIn arrs arrs[k].ty (arrs[k].base + arrs[k].stride * x)).isSome := by
    unfold findIn
    rw [List.findSome?_isSome_iff]
    refine ⟨k, List.mem_range.mpr hk, ?_⟩
    rw [Option.isSome_map, List.find?_isSome]
    exact ⟨x, List.mem_range.mpr (by rw [hgd k hk]; exact hx),
      by simp [List.getElem?_eq_getElem hk]⟩
  obtain ⟨⟨k1, x1⟩, hres⟩ := Option.isSome_iff_exists.mp hsome
  rw [hres]
  unfold findIn at hres
  obtain ⟨k1', hk1, hF⟩ := List.exists_of_findSome?_eq_some hres
  obtain ⟨x1', hfind, heq⟩ := Option.map_eq_some_iff.mp hF
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hk1l : k1' < arrs.length := List.mem_range.mp hk1
  have hpr := List.find?_some hfind
  have hxm := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
  simp only [hgd k1' hk1l, decide_eq_true_eq] at hpr hxm
  obtain ⟨h1, h2⟩ := (hok.inj ⟨k1', hk1l⟩ ⟨k, hk⟩ x1' x hxm hx hpr.1 hpr.2)
  simp only [Fin.mk.injEq] at h1
  rw [h1, h2]

/-- **A public array's value is its input cell** (BLUEPRINT A19's `PUB`): for every stack, the `K`
input cell `base + stride·x` of a public `K` array is the public value `f x`. -/
theorem inKOf_pub (hok : InOk Q arrs) (q : Column L.μ) {k : ℕ} (hk : k < arrs.length)
    (hty : arrs[k].ty = .K) {f : ℕ → FK} {e : List FE → FE} (hpub : arrs[k].pub = some (f, e))
    {x : ℕ} (hx : x < 2 ^ arrs[k].τ) :
    (inKOf Q pl groups arrs aux L hτ q).getD (arrs[k].base + arrs[k].stride * x) 0 = f x := by
  have hmem : arrs[k] ∈ arrs := List.getElem_mem hk
  have hlt : arrs[k].base + arrs[k].stride * x < Q.nInK := by
    have := hok.lt _ hmem x hx; rwa [hty] at this
  have hfind := findIn_eq Q arrs hok hk hx
  rw [hty] at hfind
  have hj : groups.length + k < (lvmTabs Q pl groups arrs aux).length := by
    rw [lvmTabs_length]; omega
  have hget := get_arr Q pl groups arrs aux hk hj
  have hlim : arrs[k].val.length = 1 := by have := hok.limbs _ hmem; rw [hty] at this; exact this
  have hτeq : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ = arrs[k].τ := by rw [hget]; rfl
  have hxt : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ := by rw [hτeq]; exact hx
  have hw : 0 < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by
    rw [hget]; simp [InArr.tab, Tab.w]
  have hfx : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).fixedOf 0 = some f := by
    rw [hget]
    obtain ⟨v, hv⟩ : ∃ v, arrs[k].val = [v] := List.length_eq_one_iff.mp hlim
    simp [Tab.fixedOf, InArr.tab, InArr.vcols, hpub, hv]
  simp only [inKOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hlt, Option.getD_some,
    hfind, inVal, dif_pos hj, dif_pos hxt, dif_pos hw]
  rw [row_fixed Q pl groups arrs aux L hτ q ⟨_, hj⟩ ⟨x, hxt⟩ ⟨0, hw⟩ hfx, FK.ofBF64_toBF64]

theorem evalB_var (u : ℕ → K) (i : ℕ) : CPoly.evalB u (CPoly.var i) = u i := by
  simp [CPoly.evalB, CPoly.var]

/-- The seed of an input array row has the key of an input seed of the LoopIR program (the case of
`loop_bus` for the input arrays, in continuation form). -/
theorem inputKey (q : Column L.μ) (hok : InOk Q arrs) {k : ℕ} (hk : k < arrs.length)
    (hj : groups.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x' : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨groups.length + k, hj⟩).τ)) (sd : Key × ℕ)
    (hsd : sd = (⟨sep arrs[k].ty, CPoly.var (arrs[k].val.length + 1),
      (List.range arrs[k].val.length).map CPoly.var⟩, arrs[k].val.length))
    (hget : (lvmTabs Q pl groups arrs aux).get ⟨groups.length + k, hj⟩ = arrs[k].tab) (goal : Prop)
    (hfin : ∀ m' : Loop.Msg, Shaped m' → m' ∈ Q.seedMsgs (witOf Q pl groups arrs aux L hτ q)
      (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q) →
      keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x')
        (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).seedVec sd)) = keyT (encT m') → goal) : goal := by
  subst hsd
  have hτeq : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ = arrs[k].τ := by rw [hget]; rfl
  have hxa : x'.val < 2 ^ arrs[k].τ := lt_of_lt_of_eq x'.isLt (by rw [hτeq])
  have hw : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w = arrs[k].val.length + 2 := by
    rw [hget]; simp [InArr.tab, Tab.w]
  have hmem : arrs[k] ∈ arrs := List.getElem_mem hk
  have hlim := hok.limbs _ hmem
  have hlt := hok.lt _ hmem x'.val hxa
  have hfind := findIn_eq Q arrs hok hk hxa
  -- the address column
  have hcol : (arrs[k].tab.cols)[arrs[k].val.length + 1]? =
      some (.fix (fun x ↦ FK.x ^ (arrs[k].base + arrs[k].stride * x))
        (fun r ↦ FE.ofK (FK.x ^ arrs[k].base) * powEval r (FK.x ^ arrs[k].stride))) := by
    simp only [InArr.tab]
    rw [List.getElem?_append_right (by simp)]
    simp
  have haddr : CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x') (arrs[k].val.length + 1) =
      FK.toBF64 (FK.x ^ (arrs[k].base + arrs[k].stride * x'.val)) := by
    have hi : arrs[k].val.length + 1 < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by rw [hw]; omega
    have hfx : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).fixedOf (arrs[k].val.length + 1) =
        some (fun x ↦ FK.x ^ (arrs[k].base + arrs[k].stride * x)) := by
      rw [hget]; simp only [Tab.fixedOf, hcol]
    simp only [CPoly.ext, dif_pos hi]
    exact row_fixed Q pl groups arrs aux L hτ q ⟨_, hj⟩ x' ⟨_, hi⟩ hfx
  -- the value columns
  have hval : ∀ l (hl : l < arrs[k].val.length),
      FK.toBF64 (inVal Q pl groups arrs aux L hτ q k x'.val l) =
        CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x') l := by
    intro l hl
    have hi : l < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by rw [hw]; omega
    simp only [inVal, dif_pos hj, dif_pos x'.isLt, dif_pos hi, CPoly.ext, FK.toBF64_ofBF64]
  -- the seed's key
  have hkey : ∀ m' : Loop.Msg, m'.sep = sep arrs[k].ty →
      m'.addr = FK.x ^ (arrs[k].base + arrs[k].stride * x'.val) →
      m'.val.length = arrs[k].val.length →
      (∀ l (hl : l < arrs[k].val.length) (h2 : l < m'.val.length),
        FK.toBF64 m'.val[l] = CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x') l) →
      keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x')
        (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).seedVec
          (⟨sep arrs[k].ty, CPoly.var (arrs[k].val.length + 1),
            (List.range arrs[k].val.length).map CPoly.var⟩, arrs[k].val.length))) =
        keyT (encT m') := by
    intro m' h1 h2 h3 h4
    refine keyT_vec_eq _ _ _ _ h1.symm ?_ (by simpa using h3.symm) ?_
    · rw [evalB_var, haddr, h2]
    · intro l h1' h2'
      simp only [List.getElem_map, List.getElem_range, evalB_var]
      have hl : l < arrs[k].val.length := by simpa using h1'
      exact (h4 l hl h2').symm
  cases hty : arrs[k].ty with
  | K =>
    rw [hty] at hfind hlt hlim
    refine hfin ⟨sep .K, FK.x ^ (arrs[k].base + arrs[k].stride * x'.val), 1,
      [(inKOf Q pl groups arrs aux L hτ q).getD (arrs[k].base + arrs[k].stride * x'.val) 0]⟩
      ⟨.K, rfl, rfl⟩ ?_ (hkey _ (by rw [hty]) rfl (by simp only [List.length_singleton]; exact hlim.symm) ?_)
    · simp only [Program.seedMsgs, Program.inputSeeds, List.mem_append, List.mem_map,
        List.mem_range]
      exact Or.inl (Or.inl ⟨_, hlt, rfl⟩)
    · intro l hl h2
      have hl0 : l = 0 := by simp at h2; omega
      subst hl0
      have hltK : arrs[k].base + arrs[k].stride * x'.val < Q.nInK := hlt
      simp only [List.getElem_cons_zero, inKOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
        dif_pos hltK, Option.getD_some, hfind]
      exact hval 0 hl
  | E =>
    rw [hty] at hfind hlt hlim
    refine hfin ⟨sep .E, FK.x ^ (arrs[k].base + arrs[k].stride * x'.val), 1,
      limbsOf .E ((inEOf Q pl groups arrs aux L hτ q).getD (arrs[k].base + arrs[k].stride * x'.val) 0)⟩
      ⟨.E, rfl, rfl⟩ ?_ (hkey _ (by rw [hty]) rfl (by simp only [limbsOf]; exact hlim.symm) ?_)
    · simp only [Program.seedMsgs, Program.inputSeeds, List.mem_append, List.mem_map,
        List.mem_range]
      exact Or.inl (Or.inr ⟨_, hlt, rfl⟩)
    · intro l hl h2
      have hltE : arrs[k].base + arrs[k].stride * x'.val < Q.nInE := hlt
      simp only [inEOf, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hltE,
        Option.getD_some, hfind, limbsOf, List.getElem_cons_zero, List.getElem_cons_succ] at h2 ⊢
      have : l < 3 := by simpa using h2
      interval_cases l
      · exact hval 0 hl
      · exact hval 1 hl
      · exact hval 2 hl

/-- The key of an evaluated group flush is the LoopIR message's. -/
theorem grp_key (hg : GrpOk Q groups) (q : Column L.μ) {i n off x : ℕ} {p : Piece}
    (hi : i < groups.length) (hm : (n, off) ∈ groups[i].mem)
    (hp : Q.pieces[n]? = some p) (hx : x < 2 ^ Q.height p)
    (h : i < (lvmTabs Q pl groups arrs aux).length)
    (hy : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ)
    (f : Flush) (hfix : FixIn p.shape f.addr ∧ ∀ P ∈ f.val, FixIn p.shape P) (cnt : CPoly) :
    keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨i, h⟩ ⟨off + x, hy⟩)
        ((keyOf p.shape f).vec ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).w cnt)) =
      keyT (encT (f.msg (Q.rowVal (witOf Q pl groups arrs aux L hτ q) n p x))) := by
  have hrow := ext_row_grp Q pl groups arrs aux L hτ hg q hi hm hp hx h hy
  refine keyT_vec_eq _ _ _ _ rfl ?_ (by simp [keyOf, Flush.msg]) ?_
  · exact evalB_ofPoly2 _ _ _ _ fun m hm y hy ↦ hrow y fun c hc ↦ hfix.1 m hm y hy c hc
  · intro l h1 h2
    simp only [keyOf, Flush.msg, List.getElem_map]
    have hl : l < f.val.length := by simpa [keyOf] using h1
    exact evalB_ofPoly2 _ _ _ _ fun m hm y hy ↦ hrow y fun c hc ↦
      hfix.2 _ (List.getElem_mem hl) m hm y hy c hc

/-- **Every seed of the instance is a LoopIR seed**: a group's result seed, or an input array's
input seed (auxiliary tables seed nothing), with the witness and the inputs read off the stack. -/
theorem seed_key (hg : GrpOk Q groups) (hok : InOk Q arrs) (haux : ∀ t ∈ aux, t.seeds = [])
    (q : Column L.μ) {s : Vector K 16} (hs : s ∈ seedTuples L (lvmTabs Q pl groups arrs aux) hτ q) :
    ∃ m' : Loop.Msg, Shaped m' ∧ m' ∈ Q.seedMsgs (witOf Q pl groups arrs aux L hτ q)
      (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q) ∧
      keyT s = keyT (encT m') := by
  set W := witOf Q pl groups arrs aux L hτ q with hW
  simp only [seedTuples, partT, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨⟨jv, hj⟩, -, v, ⟨sd, hsd, rfl⟩, x', -, rfl⟩ := hs
  have hfin : ∀ m' : Loop.Msg, Shaped m' → m' ∈ Q.seedMsgs W (inKOf Q pl groups arrs aux L hτ q)
      (inEOf Q pl groups arrs aux L hτ q) →
      keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨jv, hj⟩ x')
        (((lvmTabs Q pl groups arrs aux).get ⟨jv, hj⟩).seedVec sd)) = keyT (encT m') →
      ∃ m' : Loop.Msg, Shaped m' ∧ m' ∈ Q.seedMsgs W (inKOf Q pl groups arrs aux L hτ q)
        (inEOf Q pl groups arrs aux L hτ q) ∧
        keyT (evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨jv, hj⟩ x')
          (((lvmTabs Q pl groups arrs aux).get ⟨jv, hj⟩).seedVec sd)) = keyT (encT m') :=
    fun m' h1 h2 h3 ↦ ⟨m', h1, h2, h3⟩
  rcases (by omega : jv < groups.length ∨
      (groups.length ≤ jv ∧ jv < groups.length + arrs.length) ∨
      groups.length + arrs.length ≤ jv) with hjp | ⟨hj1, hj2⟩ | hj3
  · -- a group's result seed: the member holding the row
    have hget' := get_grp Q pl groups arrs aux hjp hj
    have hτj : ((lvmTabs Q pl groups arrs aux).get ⟨jv, hj⟩).τ = groups[jv].τ := by
      rw [hget']; rfl
    obtain ⟨⟨n', off'⟩, hm', hhold⟩ := hg.cover _ (List.getElem_mem hjp) x'.val
      (lt_of_lt_of_eq x'.isLt (by rw [hτj]))
    obtain ⟨p', hp', hσ', -, -⟩ := hg.mem _ (List.getElem_mem hjp) _ hm'
    simp only at hp'
    have hpd : Q.pieces.getD n' default = p' := by simp [List.getD_eq_getElem?_getD, hp']
    simp only [Grp.Holds, hpd, Bool.and_eq_true, decide_eq_true_eq] at hhold
    have hx' : x'.val - off' < 2 ^ Q.height p' := by omega
    rw [hget'] at hsd
    simp only [grpTab, shapeTab, ← hσ'] at hsd
    split at hsd
    · rename_i hwr
      simp only [List.mem_singleton] at hsd
      subst hsd
      refine hfin (p'.shape.seedFlush.msg (Q.rowVal W n' p' (x'.val - off')))
        (seed_shaped _ _) ?_ ?_
      · simp only [Program.seedMsgs, List.mem_append, List.mem_flatMap]
        refine Or.inr ⟨(n', p', x'.val - off'), (Q.mem_prows).mpr ⟨hp', hx'⟩, ?_⟩
        simp [hwr]
      · have hy' : off' + (x'.val - off') < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨jv, hj⟩).τ := by
          have := x'.isLt; omega
        have hxe : (⟨off' + (x'.val - off'), hy'⟩ : Fin _) = x' := Fin.ext (by simp; omega)
        have := grp_key Q pl groups arrs aux L hτ hg q hjp hm' hp' hx' hj hy' _ (seed_fixIn _ hwr) (CPoly.const 1)
        rw [hxe] at this
        exact this
    · simp at hsd
  · -- an input array's seed
    obtain ⟨k, rfl⟩ : ∃ k, jv = groups.length + k := ⟨jv - groups.length, by omega⟩
    have hk : k < arrs.length := by omega
    have hget' := get_arr Q pl groups arrs aux hk hj
    have hsd' := hsd
    rw [hget'] at hsd'
    simp only [InArr.tab, List.mem_singleton] at hsd'
    exact inputKey Q pl groups arrs aux L hτ q hok hk hj x' sd hsd' hget' _ hfin
  · -- an auxiliary table seeds nothing
    obtain ⟨k, rfl⟩ : ∃ k, jv = groups.length + arrs.length + k :=
      ⟨jv - groups.length - arrs.length, by omega⟩
    have hk : k < aux.length := by rw [lvmTabs_length] at hj; omega
    rw [get_aux Q pl groups arrs aux hk hj, haux _ (List.getElem_mem hk)] at hsd
    simp at hsd

/-- **The bus hypothesis of `loopir_sound`, verbatim.** On the lvm instance, `M3Holds` (its
balance and nonzero-count clauses), the input arrays' facts, auxiliary tables that seed nothing,
count columns inside their tables and fewer than `2^64 - 1` reads: every read of the LoopIR
pieces, with the witness and the inputs read off the stack, has the key of a seed. -/
theorem loop_bus (hg : GrpOk Q groups) (hok : InOk Q arrs) (haux : ∀ t ∈ aux, t.seeds = [])
    (hin : ∀ t ∈ lvmTabs Q pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w)
    (hlen : nReads (lvmTabs Q pl groups arrs aux) < 2 ^ 64 - 1) (q : Column L.μ)
    (hM : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q) :
    ∀ m ∈ Q.readMsgs (witOf Q pl groups arrs aux L hτ q),
      m.key ∈ (Q.seedMsgs (witOf Q pl groups arrs aux L hτ q) (inKOf Q pl groups arrs aux L hτ q)
        (inEOf Q pl groups arrs aux L hτ q)).map Loop.Msg.key := by
  set W := witOf Q pl groups arrs aux L hτ q with hW
  intro m hm
  simp only [Program.readMsgs, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨⟨n, p, x⟩, hpx, f, hf, rfl⟩ := hm
  obtain ⟨hp, hxh⟩ := (Q.mem_prows).mp hpx
  have hnp : n < Q.pieces.length := (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨i, hi, off, hmem⟩ := hg.all n hnp
  obtain ⟨p', hp', hσ, hfit, -⟩ := hg.mem _ (List.getElem_mem hi) _ hmem
  simp only at hp' hfit
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  have h : i < (lvmTabs Q pl groups arrs aux).length := by rw [lvmTabs_length]; omega
  have hget := get_grp Q pl groups arrs aux hi h
  have hτi : ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ = groups[i].τ := by
    rw [hget]; rfl
  have hy : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ := by
    rw [hτi]; omega
  have hrd : (keyOf p.shape f, cntOf p.shape f) ∈ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).reads := by
    rw [hget]; simp only [grpTab, shapeTab, ← hσ]; exact List.mem_map_of_mem hf
  have hu : evalV ((lvmInst Q pl groups arrs aux L hτ).row q ⟨i, h⟩ ⟨off + x, hy⟩)
      (((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).readVec (keyOf p.shape f, cntOf p.shape f)) ∈
      readTuples L (lvmTabs Q pl groups arrs aux) hτ q := by
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
    refine ⟨⟨i, h⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, ⟨off + x, hy⟩, ?_, rfl⟩
    simp [M3Instance.executed, inst]
  have hkey := grp_key Q pl groups arrs aux L hτ hg q hi hmem hp hxh h hy f (read_fixIn _ f hf) (CPoly.var (cntOf p.shape f))
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L (lvmTabs Q pl groups arrs aux) hτ q hM.2.1
    hM.2.2.1 hin hlen _ hu)
  obtain ⟨m', hsh, hm', he⟩ := seed_key Q pl groups arrs aux L hτ hg hok haux q hs
  rw [key_of_keyT (read_shaped _ f hf (Q.rowVal W n p x)) hsh (hkey.symm.trans (hks.symm.trans he))]
  exact List.mem_map_of_mem hm'

/-! ## The constraints: `loopir_sound`'s `hcons` -/

theorem fixIn_append {σ : Loop.Shape} {P R : Poly2} (hP : FixIn σ P) (hR : FixIn σ R) :
    FixIn σ (P ++ R) := fun m hm ↦ by
  rcases List.mem_append.mp hm with h | h
  · exact hP m h
  · exact hR m h

theorem fixIn_nil (σ : Loop.Shape) : FixIn σ [] := fun m hm ↦ by simp at hm

theorem fixIn_prod (σ : Loop.Shape) (la lb l : ℕ) :
    FixIn σ (prodPoly (Var.arg 0) (Var.arg 1) la lb l) := by
  intro m hm y hy c hc
  simp only [prodPoly, List.mem_map] at hm
  obtain ⟨_, -, rfl⟩ := hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> cases hc

theorem fixIn_limb (σ : Loop.Shape) (o n l : ℕ) : FixIn σ (limbPoly (Var.arg o) n l) := by
  unfold limbPoly; split
  · exact fixIn_var_nonfix σ _ (fun c h ↦ by cases h)
  · exact fixIn_nil σ

theorem fixIn_limbFix (σ : Loop.Shape) (c : FCol) (hc : c ∈ σ.fcols) (o n l : ℕ) :
    FixIn σ (limbFix c (Var.arg o) n l) := by
  unfold limbFix; split
  · intro m hm y hy c' hc'
    simp only [List.mem_singleton] at hm; subst hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact List.mem_append_right _ (List.mem_map_of_mem hc)
    · cases hc'
  · exact fixIn_nil σ

/-- The fixed variables of WP-10's constraints are columns of the shape's table. -/
theorem constraints_fixIn (σ : Loop.Shape) : ∀ C ∈ σ.constraints, FixIn σ C := by
  intro C hC
  have nf : ∀ l, FixIn σ (Poly2.var (.res l)) := fun l ↦ fixIn_var_nonfix σ _ (fun c h ↦ by cases h)
  unfold Loop.Shape.constraints at hC
  split at hC <;> rename_i hk <;> simp only [List.mem_map, List.mem_range] at hC <;>
    obtain ⟨l, -, rfl⟩ := hC
  · exact fixIn_append (fixIn_append (nf l) (fixIn_prod _ _ _ _)) (fixIn_limb _ _ _ _)
  · have hk' : ∀ c ∈ [FCol.k, FCol.k'], c ∈ σ.fcols := fun c hc ↦ by
      simp only [Loop.Shape.fcols, hk, if_true, List.mem_append]
      exact Or.inl (Or.inr hc)
    refine fixIn_append (fixIn_append (fixIn_append (nf l) (fixIn_limb _ _ _ _))
      (fixIn_limbFix σ .k (hk' _ (by simp)) _ _ _)) ?_
    split
    · exact fixIn_var_fix σ .k' (hk' _ (by simp))
    · exact fixIn_nil σ
  · exact fixIn_prod _ _ _ _
  · exact fixIn_append (nf l) (fixIn_var_nonfix σ _ (fun c h ↦ by cases h))
  · have hF : FCol.F ∈ σ.fcols := by simp [Loop.Shape.fcols, hk]
    exact fixIn_append (fixIn_append (nf l) (fixIn_limbFix σ .F hF _ _ _)) (fixIn_limb _ _ _ _)

/-- **The constraint hypothesis of `loopir_sound`, verbatim.** On the lvm instance, the clause
`ConstraintsVanish` of `M3Holds` gives every LoopIR constraint at every piece row, with the witness
read off the stack. -/
theorem loop_cons (hg : GrpOk Q groups) (q : Column L.μ)
    (hM : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q) :
    Q.ConstraintsHold (witOf Q pl groups arrs aux L hτ q) := by
  intro ⟨n, p, x⟩ hpx C hC
  obtain ⟨hp, hxh⟩ := (Q.mem_prows).mp hpx
  simp only at hC ⊢
  have hnp : n < Q.pieces.length := (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨i, hi, off, hmem⟩ := hg.all n hnp
  obtain ⟨p', hp', hσ, hfit, -⟩ := hg.mem _ (List.getElem_mem hi) _ hmem
  simp only at hp' hfit
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  have h : i < (lvmTabs Q pl groups arrs aux).length := by rw [lvmTabs_length]; omega
  have hget := get_grp Q pl groups arrs aux hi h
  have hτi : ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ = groups[i].τ := by rw [hget]; rfl
  have hy : off + x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).τ := by rw [hτi]; omega
  have hcm : ofPoly2 (vidx p.shape) C ∈ ((lvmTabs Q pl groups arrs aux).get ⟨i, h⟩).cons := by
    rw [hget]; simp only [grpTab, shapeTab, ← hσ]; exact List.mem_map_of_mem hC
  have hz := hM.1 ⟨i, h⟩ _ (List.mem_map_of_mem hcm) ⟨off + x, hy⟩
  rw [CPoly.eval_toMv] at hz
  have hrow := ext_row_grp Q pl groups arrs aux L hτ hg q hi hmem hp hxh h hy
  rw [evalB_ofPoly2 _ _ _ _ fun m hm y hy' ↦ hrow y fun c hc ↦
    constraints_fixIn _ C hC m hm y hy' c hc] at hz
  exact FK.toBF64_injective (hz.trans FK.toBF64_zero.symm)

end Bridge2

/-! ## Non-vacuity -/

/-- The empty program's instance: no table. -/
def emptyProgram : Program := ⟨0, 0, [], []⟩

/-- **Non-vacuity of `loop_bus`'s hypotheses**: on the empty program's instance, `M3Holds`, `GrpOk`
and `InOk` hold of every stack. -/
theorem empty_hyps (L : Lay) (q : Column L.μ) :
    M3Holds (lvmInst emptyProgram (fun _ _ ↦ (false, 0)) [] [] [] L (by simp [lvmTabs])) () q ∧
      GrpOk emptyProgram [] ∧ InOk emptyProgram [] := by
  have hj : ∀ j : Fin (lvmTabs emptyProgram (fun _ _ ↦ (false, 0)) [] [] []).length, False := by
    intro j; have := j.isLt; simp [lvmTabs, emptyProgram, Program.pieces] at this
  refine ⟨⟨fun j ↦ (hj j).elim, ?_, fun j ↦ (hj j).elim, fun l hl ↦ by simp at hl,
    fun r hr ↦ by simp at hr⟩, ⟨by simp, by simp, by simp,
      fun n hn ↦ by simp [emptyProgram, Program.pieces] at hn, by simp, by simp⟩,
    ⟨by simp, by simp, fun i ↦ i.elim0, fun τ e he ↦ by cases τ <;> simp [emptyProgram, Program.nIn] at he⟩⟩
  have hnil : ∀ sd, (lvmInst emptyProgram (fun _ _ ↦ (false, 0)) [] [] [] L
      (by simp [lvmTabs])).flushTuples q sd = [] := by
    intro sd
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    simp only [M3Instance.flushTuples, List.mem_flatMap] at hx
    obtain ⟨j, -, -⟩ := hx
    have := j.isLt
    simp [lvmTabs, emptyProgram, Program.pieces] at this
  unfold M3Instance.Balanced M3Instance.tuples
  rw [hnil, hnil]
  simp [M3Instance.boundaryTuples]

end Lvm.M3
