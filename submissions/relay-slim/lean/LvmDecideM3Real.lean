-- new for lvm (WP-9; frozen into WP-11a's interface by INT-2): the native verifier's M3 decision from
-- the lvm tables (`LvmM3Tab`). The leaf decomposition transcribes the protocol's `Bus.busOut` (WP-2's
-- port of leanVM `Protocol/Bus.lean`: sources, stable largest-first stacking, selector weights,
-- `flushForm`, `countForm`, `total`) for an instance with no boundary block and no padding row.
import LvmM3Tab
import LvmDecideV0
import LvmLoopMleFast

/-!
# The native M3 decision of the lvm instance

**Bus** (`busFinalR`). From `α`, `β`, the grand product's point `ζ` and its three values, side by
side (push, pull, count): the side's blocks in the protocol's order (each table's read pushes then
seed pushes; read pulls then finalize pulls; count columns), stably sorted largest first and stacked
at aligned offsets in `2^μ`; block `b`'s selector weight `w_b = eq(sel_b, ζ_{≥κ_b})`; on its table,
a flush block adds `w_b·(β + Σ_i eq(α, i)·coord_i)` to the side's form (characteristic two), a count
block `w_b·X_c`; the side's total is `v + 1 + Σ_b w_b` (no boundary block, no padding row). The bus
phase ends with one scalar that must be zero (`LvmM3Phase.lvmBusProg`): `leafdecReads = 1`.

**Tables** (`nativeTable`). Every column of a sumcheck table is an evaluation the prover sends,
committed and fixed alike (leanVM's derived columns); the constraints are the table's `CPoly`s at the
evaluations. **Claims** (`tableClaimsR`): each committed column's value at the table's point, on its
commitment. **Fixed columns** (A23, BLUEPRINT §12): `fixColsR` lists every fixed column but `PUB`'s
value column (`PUB` = sumcheck table `Params.pubTab`, its column 0); their sent evaluations
(`fixSentR`) are batched into the accumulator and their closed forms (`fixValsR`) are evaluated once,
at the folded point (`PhiC`, `LvmDecide`); `PUB`'s value column is checked against the header lanes
(`pubCheckR`). INT-2's per-column check `tableCheckR` stays defined (WP-9b's lemmas use it) but `V`
no longer runs it.

**`V_S`** (INT-2). `M3.real p tabs` is WP-11a's interface (`LvmDecideM3`) filled with these and the
layout and links of `M3.ofParts`; `V_S` is `VS p (M3.real p tabs)` (`LvmVerifierS.VSL`), `tabs` being
`fun pub => LvmM3LoopTab.lvmTabs Q pl groups (arrsOf pub) aux` of the final program (`fitsR` on its
shapes, which do not depend on `pub`). **`fitsR p tabs`** is the size
condition the record must meet for the tables (`Params.busDepth`, `leafdecReads = 1`, `tableRounds`,
`tableEvals`; the values are frozen in `LvmParams` from WP-9's size model).
-/

set_option autoImplicit false

namespace Lvm.M3

open Lvm DM

/-! ## Forms -/

/-- `w·P` as a native form. -/
def cpolyForm (w : FE) (P : CPoly) : Form := ⟨P.map fun m => (m.2, w * FE.ofK m.1)⟩

/-- The sum of forms (terms concatenated). -/
def formSum (fs : List Form) : Form := ⟨fs.flatMap (·.terms)⟩

/-- The leaf form of a message `⟨sep, addr, cnt, val⟩` at unit weight: `β + Σ_i eq(α, i)·coord_i`. -/
def leafForm (eqα : List FE) (β : FE) (k : Key) (cnt : CPoly) : Form :=
  formSum ([Form.const (β + eqα.getD 0 0 * FE.ofK k.sep), cpolyForm (eqα.getD 1 0) k.addr,
    cpolyForm (eqα.getD 2 0) cnt] ++ k.val.zipIdx.map fun (P, l) => cpolyForm (eqα.getD (3 + l) 0) P)

/-- A block of a bus side: its table, its log-height, its form at unit weight. -/
structure NBlock where
  /-- The table. -/
  tab : Nat
  /-- The log-height. -/
  κ : Nat
  /-- The form at unit weight. -/
  form : Form

/-- The blocks of the three sides, in the protocol's order (`Bus.sideSources`, `countSources`). -/
def sideBlocks (tabs : List Tab) (eqα : List FE) (β : FE) : List (List NBlock) :=
  let ts := tabs.zipIdx
  [ts.flatMap fun (t, j) =>
      t.reads.map (fun r => ⟨j, t.τ, leafForm eqα β r.1 [(FK.x, [r.2])]⟩) ++
        t.seeds.map (fun s => ⟨j, t.τ, leafForm eqα β s.1 (CPoly.const 1)⟩),
   ts.flatMap fun (t, j) =>
      t.reads.map (fun r => ⟨j, t.τ, leafForm eqα β r.1 (CPoly.var r.2)⟩) ++
        t.seeds.map (fun s => ⟨j, t.τ, leafForm eqα β s.1 (CPoly.var s.2)⟩),
   ts.flatMap fun (t, j) => t.counts.map fun c => ⟨j, t.τ, Form.col c.val⟩]

/-- The blocks stacked largest first (stable), with their offsets. -/
def stackBlocks (bs : List NBlock) : List (NBlock × Nat) :=
  let sorted := bs.mergeSort fun a b => decide (b.κ ≤ a.κ)
  (sorted.foldl (fun (acc : List (NBlock × Nat) × Nat) b => (acc.1 ++ [(b, acc.2)], acc.2 + 2 ^ b.κ))
    ([], 0)).1

/-- Block weight `eq(sel_b, ζ_{≥κ})` of a block at offset `off`. -/
def blockWeight (ζ : List FE) (κ off : Nat) : FE :=
  eqEval (selectorPoint (off >>> κ) (ζ.length - κ)) (ζ.drop κ)

/-- **The bus leaf decomposition** of the lvm tables (each block's weight computed once, the
blocks bucketed by table in one pass). -/
def busFinalR (tabs : List Tab) (i : BusIn) : BusOut :=
  let eqα := eqKernel i.alphas
  let sides := (sideBlocks tabs eqα i.beta).map fun bs =>
    (stackBlocks bs).map fun (b, off) => (b, blockWeight i.point b.κ off)
  let bucket (s : List (NBlock × FE)) : Array (List (List Nat × FE)) :=
    s.foldl (fun acc (b, w) => acc.modify b.tab fun ts =>
      b.form.terms.map (fun t => (t.1, w * t.2)) ++ ts) (Array.replicate tabs.length [])
  let bs := sides.map bucket
  let forms := (List.range tabs.length).map fun j => bs.map fun a => (⟨a.getD j []⟩ : Form)
  let totals := (List.range 3).map fun k =>
    i.values.getD k 0 + 1 + sumE ((sides.getD k []).map (·.2))
  ⟨i.values.length == 3 && i.leafdec == [0], [], forms, totals⟩

/-! ## Tables, claims, fixed columns -/

/-- The native table of an lvm table: every column an evaluation, the constraints at them. -/
def nativeTable (t : Tab) : TableSpec :=
  ⟨t.τ, t.w, t.cons.length, fun _ evals => t.cons.map (CPoly.evalE (fun i => evals.getD i 0))⟩

/-- The committed columns' claims of the tables' evaluations, on their commitments. -/
def tableClaimsR (tabs : List Tab) (evs : List (List FE × List FE)) : List (Com × BlockClaim) :=
  (tabs.zip evs).flatMap fun (t, (pt, ev)) =>
    t.cols.zipIdx.filterMap fun (c, i) => match c with
      | .com rec off => some (if rec then .crec else .main, BlockClaim.point ⟨t.τ, off⟩ pt (ev.getD i 0))
      | .fix _ _ => none

/-- The fixed columns' values are their closed forms at the tables' points. -/
def tableCheckR (tabs : List Tab) (evs : List (List FE × List FE)) : Bool :=
  (tabs.zip evs).all fun (t, (pt, ev)) =>
    t.cols.zipIdx.all fun (c, i) => match c with
      | .com _ _ => true
      | .fix _ e => ev.getD i 0 == e pt

/-- A column of `Φ` (A23): its table's index and log-height, its column index, its closed form. -/
structure FixCol where
  /-- The table's index among the sumcheck tables. -/
  tab : Nat
  /-- The table's log-height. -/
  τ : Nat
  /-- The column's index in the table. -/
  col : Nat
  /-- The closed form of the column's extension (`ColSrc.fix`'s `ev`). -/
  ev : List FE → FE

/-- **`fixCols`** (BLUEPRINT §12.2): every fixed column of `tabs`, in table order then column order,
except column 0 of table `pubTab` (`PUB`'s value column). -/
def fixColsR (tabs : List Tab) (pubTab : Nat) : List FixCol :=
  tabs.zipIdx.flatMap fun (t, j) =>
    t.cols.zipIdx.filterMap fun (c, i) => match c with
      | .com _ _ => none
      | .fix _ e => if j == pubTab && i == 0 then none else some ⟨j, t.τ, i, e⟩

/-- **The closed forms of `fixCols`** at `p ∈ E^tableRounds`: column `k` at `p.take τ_k`. -/
def fixValsR (tabs : List Tab) (pubTab : Nat) (p : List FE) : List FE :=
  (fixColsR tabs pubTab).map fun c => c.ev (p.take c.τ)

/-- **The sent evaluations of `fixCols`**, from the tables' evaluations `(point, values)`. -/
def fixSentR (tabs : List Tab) (pubTab : Nat) (evs : List (List FE × List FE)) : List FE :=
  (fixColsR tabs pubTab).map fun c => (evs.getD c.tab default).2.getD c.col 0

/-- **`PUB`'s check**: the sent evaluation of column 0 of table `pubTab` is the extension of the
header lanes at that table's point (`pubEval`, BLUEPRINT §12.4 step 1). -/
def pubCheckR (pubTab : Nat) (pub : Pub) (evs : List (List FE × List FE)) : Bool :=
  let e := evs.getD pubTab default
  e.2.getD 0 0 == pubEval pub.hdrLanes e.1

/-- The tables of the table sumcheck: those with a constraint, a read or a seed. -/
def sumcheckTabs (tabs : List Tab) : List Tab :=
  tabs.filter fun t => !t.cons.isEmpty || !t.reads.isEmpty || !t.seeds.isEmpty

/-- **The real M3 instance** of the tables `tabs pub` (the public values enter only fixed columns'
closed forms, WP-9b's PUB array): WP-9's bus leaf decomposition, native tables, column claims, and
A23's `fixCols` (closed forms, sent evaluations) and `PUB` check on the sumcheck tables, with
`M3.ofParts`'s layout and links. -/
def real (p : Params) (tabs : Pub → List Tab) : M3 :=
  M3.ofParts p (fun i => busFinalR (sumcheckTabs (tabs i.pub)) i)
    (fun pub => (sumcheckTabs (tabs pub)).map nativeTable)
    (fun pub => tableClaimsR (sumcheckTabs (tabs pub)))
    (fun pub => fixValsR (sumcheckTabs (tabs pub)) p.pubTab)
    (fun pub => fixSentR (sumcheckTabs (tabs pub)) p.pubTab)
    (fun pub => pubCheckR p.pubTab pub)

/-- **`Φ` is the same polynomial in every proof** (A23): the closed forms of `fixCols` do not
depend on the header. A property of the final tables (only `PUB`'s value column reads the header);
the node-level assembly proves it for `M3.tabsP20` (owner AC-N). -/
def FixStatic (p : Params) (tabs : Pub → List Tab) : Prop :=
  ∀ pub pub', ((fixColsR (sumcheckTabs (tabs pub)) p.pubTab).map fun c => (c.tab, c.τ, c.col)) =
      (fixColsR (sumcheckTabs (tabs pub')) p.pubTab).map (fun c => (c.tab, c.τ, c.col)) ∧
    fixValsR (sumcheckTabs (tabs pub)) p.pubTab = fixValsR (sumcheckTabs (tabs pub')) p.pubTab

@[simp] theorem length_fixValsR (tabs : List Tab) (pubTab : Nat) (p : List FE) :
    (fixValsR tabs pubTab p).length = (fixColsR tabs pubTab).length := by simp [fixValsR]

@[simp] theorem length_fixSentR (tabs : List Tab) (pubTab : Nat) (evs : List (List FE × List FE)) :
    (fixSentR tabs pubTab evs).length = (fixColsR tabs pubTab).length := by simp [fixSentR]

/-- Column 0 of a table is fixed (`PUB`'s value column is). -/
def col0Fix (t : Tab) : Bool := match t.cols.head? with
  | some (.fix _ _) => true
  | _ => false

/-- The push side's leaves: one per row of every read and every seed of every sumcheck table. -/
def pushLeavesR (tabs : List Tab) : Nat :=
  ((sumcheckTabs tabs).map fun t => (t.reads.length + t.seeds.length) * 2 ^ t.τ).sum

/-- Every committed column is an aligned block inside its commitment (`LvmM3Inst.Aligned`, as a Bool:
`2^τ ∣ off`, `off + 2^τ ≤ 2^ν`). -/
def colsFitB (p : Params) (tabs : List Tab) : Bool :=
  decide (p.nuRec ≤ p.nuMain) && tabs.all fun t => t.cols.all fun c => match c with
    | .com rec off => off % 2 ^ t.τ == 0 && decide (off + 2 ^ t.τ ≤ 2 ^ (if rec then p.nuRec else p.nuMain))
    | .fix _ _ => true

/-- **The record fits the tables** (the conditions V_S's reading and WP-9's phase specs need that are
decidable on the data): one leaf-decomposition scalar; the bus depth `⌈log₂⌉` of the push leaves, in
`[1, 22]` (`abError_le`; the pull side has as many leaves and the count side at most as many,
`leafCount_pull_eq`, `leafCount_count_le`, so no side's stacking passes `2^busDepth`); the table
rounds the tallest sumcheck table; the evaluations the widths' sum (the schedule reads them in one
item, `tableTerms` table by table); every table at most `nuMain + 1` high (`inst`'s `hτ`); every
constrained table reads or seeds (`inst_conditions`'s `hcon`); the committed columns aligned
(`colsFitB`; WP-9b's `layOkB` on a `Lay` is the same check); A23: `tableRounds ≤ accVars`,
`fixCols` has at most `2^accLog` columns, `pubTab` is a sumcheck table high enough for the
header's `pubLanes` whose column 0 is fixed. Not decidable here, owed by the final assembly (WP-14a): each fixed column's closed form
is its cells' extension (`pieceEval_eq`; `fixFEval`, `grpEval` vs `grpFix` with aligned, disjoint
members). -/
def fitsR (p : Params) (tabs : List Tab) : Bool :=
  let st := sumcheckTabs tabs
  p.leafdecReads == 1 && p.busDepth == log2Ceil (pushLeavesR tabs) && decide (1 ≤ p.busDepth) &&
    decide (p.busDepth ≤ 22) && p.tableRounds == (st.map (·.τ)).foldl max 0 &&
    p.tableEvals == (st.map (·.w)).sum && tabs.all (fun t => decide (t.τ ≤ p.nuMain + 1)) &&
    tabs.all (fun t => t.cons.isEmpty || !t.reads.isEmpty || !t.seeds.isEmpty) && colsFitB p tabs &&
    decide (p.tableRounds ≤ accVars) && decide ((fixColsR st p.pubTab).length ≤ 2 ^ p.accLog) &&
    decide (p.pubTab < st.length) && decide (pubLanes ≤ 2 ^ ((st.map (·.τ)).getD p.pubTab 0)) &&
    (st.map col0Fix).getD p.pubTab false

end Lvm.M3
