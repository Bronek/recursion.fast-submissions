-- new for lvm (WP-9b): the verifier program's table phase for the lvm instance on `E` (the program
-- objects `lbusTableSpec` is stated at): the tables, the layout, the bus result (`busFinalV`, the
-- `E` transcription of the native `LvmDecideM3Real.busFinalR`, list for list), the global column
-- numbering, and the fixed-column check (`tableCheckVB`, the program's version of `tableCheckR`).
import LvmM3Phase
import LvmLoopTable

/-!
# The lvm table phase's program objects

leanVM's `busTableSpec` (`LvmM3Phase.lvmBusTableSpec`) is stated for a list of verifier tables,
a layout and a bus result computed from what the bus phase read. For the lvm instance
`inst L tabs hτ` they are:

* `vTables tabs`: table `j` has opcode `j`, the table's width in columns, and its constraints
  evaluated at the row's values (`CPoly.evalV`); `vLayout tabs`: only the log-heights;
* `busFinalV tabs` (`busResV` on an `LBus`): the leaf decomposition, as the native
  `busFinalR` computes it (the same lists in the same order, over `E`): each side's blocks in the
  protocol's order (`sideBlocksV`), stacked largest first (`stackBlocksV`), weighted by
  `eq_above` of their placement (`blockWeightV`), bucketed by table (each table's blocks in
  reverse order, as the native fold prepends them); the totals `v + 1 + Σ_b w_b`;
* `colOfL tabs`: the protocol's column `⟨j, i⟩` is global column `6 + Σ_{j' < j} w_{j'} + i`, the
  number the table phase's claims carry (`globalColumnBases`);
* `tableCheckVB tabs claims`: every claim on a fixed column has its closed form's value
  (`fixedEvalV`, the native evaluator through `FE.toExt3`).

`AllSc tabs`: every table reads or seeds (every lvm table does: LoopIR pieces, input arrays,
`BITS`), so every table is a sumcheck table and the native decision's filter is the identity.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier

/-! ## Polynomials over `E` -/

/-- An `FK` coefficient as an element of `E`. -/
def kE (c : FK) : E := ofK (FK.toBF64 c)

/-- The value of a `CPoly` at a row of `E` values (the native `CPoly.evalE` over `E`). -/
def CPoly.evalV (v : ℕ → E) (P : CPoly) : E :=
  (P.map fun m ↦ kE m.1 * (m.2.map v).foldl (· * ·) 1).foldl (· + ·) 0

/-! ## Tables and layout -/

/-- Every table reads or seeds: every table is a sumcheck table. -/
def AllSc (tabs : List Tab) : Prop := ∀ t ∈ tabs, t.reads ≠ [] ∨ t.seeds ≠ []

/-- The verifier table of lvm table `t`, numbered `j`. -/
def vTable (j : ℕ) (t : Tab) : Table where
  opcode := j
  columns := List.replicate t.w ""
  flushes := {}
  constraints ev := t.cons.map (CPoly.evalV fun i ↦ ev.getD i 0)
  padding := []

/-- The verifier tables of the lvm tables, in order. -/
def vTables (tabs : List Tab) : List Table := tabs.zipIdx.map fun (t, j) ↦ vTable j t

@[simp] theorem length_vTables (tabs : List Tab) : (vTables tabs).length = tabs.length := by
  simp [vTables]

/-- The verifier layout: the table phase reads only the log-heights. -/
def vLayout (tabs : List Tab) : Layout where
  logMemory := 0
  logBytecode := 0
  bytecode := []
  push := []
  pull := []
  count := []
  placements := []
  stackLog := 0
  tableLogHeights := tabs.map (·.τ)

/-- **The global column numbering**: column `i` of table `j` is the table phase's claim number
(`globalColumnBases`). -/
noncomputable def colOfL (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) :
    (inst L tabs hτ).ColumnId → ℕ :=
  fun c ↦ (globalColumnBases (vTables tabs)).getD c.1.val 0 + c.2.val

/-- The (empty) boundary values of the lvm instance. -/
noncomputable def vals0 (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) :
    Vector E (inst L tabs hτ).busClaims :=
  Vector.cast (busClaims_zero L tabs hτ).symm #v[]

/-! ## The bus result (the native `busFinalR` over `E`) -/

/-- `w·P` as a form. -/
def cpolyFormV (w : E) (P : CPoly) : Form := ⟨P.map fun m ↦ (m.2, w * kE m.1)⟩

/-- The sum of forms (terms concatenated). -/
def formSumV (fs : List Form) : Form := ⟨fs.flatMap (·.terms)⟩

/-- The leaf form of a message `⟨sep, addr, cnt, val⟩` at unit weight:
`β + Σ_i eq(α, i)·coord_i`. -/
def leafFormV (eqα : List E) (β : E) (k : Key) (cnt : CPoly) : Form :=
  formSumV ([Form.const (β + eqα.getD 0 0 * kE k.sep), cpolyFormV (eqα.getD 1 0) k.addr,
    cpolyFormV (eqα.getD 2 0) cnt] ++ k.val.zipIdx.map fun (P, l) ↦ cpolyFormV (eqα.getD (3 + l) 0) P)

/-- A block of a bus side: its table, its log-height, its form at unit weight. -/
structure VBlock where
  /-- The table. -/
  tab : ℕ
  /-- The log-height. -/
  κ : ℕ
  /-- The form at unit weight. -/
  form : Form

/-- The blocks of the three sides, in the protocol's order (`Bus.sideSources`, `countSources`). -/
def sideBlocksV (tabs : List Tab) (eqα : List E) (β : E) : List (List VBlock) :=
  let ts := tabs.zipIdx
  [ts.flatMap fun (t, j) ↦
      t.reads.map (fun r ↦ ⟨j, t.τ, leafFormV eqα β r.1 [(FK.x, [r.2])]⟩) ++
        t.seeds.map (fun s ↦ ⟨j, t.τ, leafFormV eqα β s.1 (CPoly.const 1)⟩),
   ts.flatMap fun (t, j) ↦
      t.reads.map (fun r ↦ ⟨j, t.τ, leafFormV eqα β r.1 (CPoly.var r.2)⟩) ++
        t.seeds.map (fun s ↦ ⟨j, t.τ, leafFormV eqα β s.1 (CPoly.var s.2)⟩),
   ts.flatMap fun (t, j) ↦ t.counts.map fun c ↦ ⟨j, t.τ, Form.col c.val⟩]

/-- The blocks stacked largest first (stable), with their offsets. -/
def stackBlocksV (bs : List VBlock) : List (VBlock × ℕ) :=
  let sorted := bs.mergeSort fun a b ↦ decide (b.κ ≤ a.κ)
  (sorted.foldl (fun (acc : List (VBlock × ℕ) × ℕ) b ↦ (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
    ([], 0)).1

/-- Block weight of a block at offset `off`: `eq_above` of its placement. -/
def blockWeightV (ζ : List E) (κ off : ℕ) : E := ({ variableCount := κ, index := off } : Placement).eqAbove ζ

/-- The sides' blocks with their weights at `ζ`. -/
def sidesV (tabs : List Tab) (alphas : List E) (β : E) (ζ : List E) : List (List (VBlock × E)) :=
  (sideBlocksV tabs (eqKernel alphas) β).map fun bs ↦
    (stackBlocksV bs).map fun (b, off) ↦ (b, blockWeightV ζ b.κ off)

/-- Table `j`'s terms on a side: its blocks' weighted terms, the last block first (the native
fold prepends). -/
def bucketV (s : List (VBlock × E)) (j : ℕ) : List (List ℕ × E) :=
  ((s.filter fun bw ↦ bw.1.tab == j).reverse).flatMap fun bw ↦
    bw.1.form.terms.map fun t ↦ (t.1, bw.2 * t.2)

/-- **The bus leaf decomposition** of the lvm tables over `E`: no framework claim, the GKR point,
each table's three forms, each side's total `v + 1 + Σ_b w_b`. -/
def busFinalV (tabs : List Tab) (alphas : List E) (β : E) (ζ values : List E) : BusResult :=
  let sides := sidesV tabs alphas β ζ
  ⟨[], ζ, (List.range tabs.length).map (fun j ↦ sides.map fun s ↦ (⟨bucketV s j⟩ : Form)),
    (List.range 3).map fun k ↦ values.getD k 0 + 1 + sumE ((sides.getD k []).map (·.2))⟩

/-- The bus result of what the lvm bus phase read. -/
def busResV (tabs : List Tab) (b : LBus) : BusResult := busFinalV tabs b.alphas b.beta b.point b.values

/-! ## The fixed-column check -/

/-- The table and local column of global column `n` (the first table whose block holds it). -/
def colLoc (tabs : List Tab) (n : ℕ) : Option (ℕ × ℕ) :=
  ((List.range tabs.length).find? fun j ↦
      decide ((globalColumnBases (vTables tabs)).getD j 0 ≤ n ∧
        n < (globalColumnBases (vTables tabs)).getD j 0 + ((tabs[j]?.map (·.w)).getD 0))).map
    fun j ↦ (j, n - (globalColumnBases (vTables tabs)).getD j 0)

/-- The closed form over `E` of global column `n`, if it is a fixed column (the native evaluator
through `FE.toExt3`). -/
def fixedEvalV (tabs : List Tab) (n : ℕ) : Option (List E → E) :=
  (colLoc tabs n).bind fun ji ↦
    match tabs[ji.1]?.bind fun t ↦ t.cols[ji.2]? with
    | some (.fix _ ev) => some fun pt ↦ FE.toExt3 (ev (pt.map FE.ofExt3))
    | _ => none

/-- **The fixed-column check** of the table phase's claims: every claim on a fixed column has the
closed form's value at its point. -/
def tableCheckVB (tabs : List Tab) (claims : List ColumnClaim) : Bool :=
  claims.all fun c ↦ match fixedEvalV tabs c.column with
    | some ev => decide (c.value = ev c.point)
    | none => true

/-- **Every fixed column's closed form is its cells' multilinear extension** (native, at every
point of the table's height). -/
def FixOk (tabs : List Tab) : Prop :=
  ∀ t ∈ tabs, ∀ f ev, ColSrc.fix f ev ∈ t.cols → ∀ r : List FE, r.length = t.τ →
    ev r = Loop.mle r fun x ↦ FE.ofK (f x)

end Lvm.M3
