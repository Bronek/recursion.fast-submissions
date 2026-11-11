-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/TablePhase.lean` (formal rev 40f877dc) as `LvmFrontTablePhase` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.TablePhase

  The verifier program's table sumcheck specified on the oracle protocol's relations: from the bus
  seam at what the bus phase read to the table seam at the protocol's output, given the algebraic
  identities between the program's computations and the protocol's verdicts.
-/


import LvmClaims
import LvmBTableClaims
import LvmFrontBusPhase
import LvmFrontTableArk
import LvmFrontTableTerms

/-! lvm (WP-2): over a table list `tables` (the source's are at leanISA's `tables`): `nCons`,
`cpsOf`, `fpsOf`, `rowsOf`, `TableFid`, `TableSumcheckPost`, `tableSumcheckSpec`, `tablePhaseSpec`
take it, and the last two the hypothesis `htw : ∀ t ∈ tables, 0 < t.width` (leanISA's
`tables_width_pos`, decided there, is not a fact of an arbitrary list). -/

/-!
# The table sumcheck on doom

`tablePhase layout bus` (`crates/verifier/src/lib.rs:242-266` and `bus.rs:218-259`) is the oracle
protocol's `tableSumcheck` (`LeanVM.Protocol.TableSumcheck`) on the wire: the batching challenge
`ξ`, the plain sumcheck of four coefficients per round (one left out on the wire), the evaluations
of every table's columns, and the final check. Its doom is stated on the protocol's relations at the
protocol's statement `(input, busOut …)` of what the bus phase read (`BusWit`):

* `ξ`: from the bus seam to the sumcheck's input relation, charged `L₀ · (B + 2) / |E|`
  (`xi_escape`);
* the rounds: `wireSumcheckSpec` on the protocol's family, each charged `L₀ · 3 / |E|`;
* the evaluations and the check: the protocol's last message and its check (`finalValues_keep`),
  to the table seam at `tableOut`.

The program computes the target, the final check's value and the claims its own way. The four
identities that make them the protocol's are `TableFid` (the number of rounds is `τ_max`; the
target is the protocol's batched claim; the final check's value is the protocol's formula; every
claim of the protocol's output is among the program's, through a column numbering `colOf`); they
are statements about the instance and the layout only, discharged for leanISA separately.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.TableSumcheck
open CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

section

/-! ## The program's quantities -/

variable (tables : List Table)

/-- The number of constraints, `Σ n_constraints`. -/
def nCons : ℕ := (tables.map Table.nConstraints).sum

/-- The constraint powers of `ξ`. -/
def cpsOf (ξ : E) : List E := (powers ξ (nCons tables + 3)).take (nCons tables)

/-- The form powers of `ξ`. -/
def fpsOf (ξ : E) : List E := (powers ξ (nCons tables + 3)).drop (nCons tables)

/-- The rows of the final loop at the point `point` (the challenges reversed). -/
def rowsOf (layout : Verifier.Layout) (bus : BusResult) (point : List E) :
    List (Table × ℕ × List Form × E) :=
  List.zip tables (List.zip layout.tableLogHeights
    (List.zip bus.forms (Verifier.tableWeights layout.tableLogHeights bus.point point)))

/-- Every row of the final loop is of a table of positive width, when every table is (lvm: the
source's `tables_width_pos`, a fact of leanISA's tables, is this hypothesis). -/
theorem rowsOf_width_pos (htw : ∀ t ∈ tables, 0 < t.width) (layout : Verifier.Layout)
    (bus : BusResult) (point : List E) :
    ∀ r ∈ rowsOf tables layout bus point, 0 < r.1.width := fun _ hr ↦
  htw _ (List.of_mem_zip hr).1

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (layout : Verifier.Layout)

/-- The protocol's statement after the bus phase, on what it read. -/
noncomputable def busStmt (w : BusWit) : I.Stmt × BusOut I := (input, Bus.busOut hI (w.layer I input) (w.vals I))

/-- The sumcheck's statement after its rounds. -/
noncomputable def tableStmt (w : BusWit) (ξ : E) (ch : List E) (claim : E) :
    SumcheckRound.Stmt (Data I) E I.τmax :=
  ((busStmt I hI input w, ξ), (vecOf I.τmax ch, claim))

/-- **The program's computations are the protocol's**: the identities between the table phase's
target, final check and claims and the protocol's batched claim, formula and output claims, at
what the bus phase read. `colOf` numbers the protocol's columns as the program does. -/
structure TableFid (colOf : I.ColumnId → ℕ) (w : BusWit) : Prop where
  /-- The rounds: `max` of the heights is `τ_max`. -/
  rounds : layout.tableLogHeights.foldl max 0 = I.τmax
  /-- The target is the protocol's batched claim. -/
  target : ∀ ξ, dot (fpsOf tables ξ) (w.result tables layout).totals =
    powerBatch (claimed I (busStmt I hI input w)) ξ
  /-- The final check's value is the protocol's formula. -/
  formula : ∀ ξ (ch : List E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf tables layout (w.result tables layout) ch.reverse) evs →
    (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse (rowsOf tables layout (w.result tables layout) ch.reverse) evs
      0 0 []).1 = formula I (busStmt I hI input w, ξ) (vecOf I.τmax ch).reverse
        (vecOf I.tableColumns evs.flatten)
  /-- The protocol's output claims are among the program's. -/
  claims : ∀ ξ (ch : List E) (claim : E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf tables layout (w.result tables layout) ch.reverse) evs →
    ∀ c ∈ (tableOut I (tableStmt I hI input w ξ ch claim)
      (vecOf I.tableColumns evs.flatten)).2.columns.toList,
      (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
        (w.result tables layout).claims ++ (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
          (rowsOf tables layout (w.result tables layout) ch.reverse) evs 0 0 []).2

/-- **The table seam on the wire**: the protocol's output at what was read is doomed, its input
statement is `input`, its claims are among the program's, and it is the table sumcheck's output
(`tableOut`) at some final statement and values: its claims are the bus phase's and one per column
of every sumcheck table at the point's low coordinates. -/
def TablePost (colOf : I.ColumnId → ℕ) (claims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ (W : Word) (tout : I.Stmt × TableOut I), firstWord h = some W ∧
    RelDoom (cands W) (Seam.table I) tout ∧ tout.1 = input ∧
    (∀ c ∈ tout.2.columns.toList, (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
      claims) ∧
    ∃ (st : SumcheckRound.Stmt (Data I) E I.τmax) (v : Vector E I.tableColumns),
      tout = tableOut I st v

variable {εmax : ℝ≥0∞}

/-- What the table sumcheck's rounds and final values give: the evaluations read, the claims
the program makes of them, and the table seam's doom at the protocol's output. -/
def TableSumcheckPost (w : BusWit) (ξ : E) (claims' : List Verifier.ColumnClaim) (h : List Ev) :
    Prop :=
  ∃ ch claim evs, ReadShape (rowsOf tables layout (w.result tables layout) ch.reverse) evs ∧
    ch.length = I.τmax ∧
    claims' = (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
      (rowsOf tables layout (w.result tables layout) ch.reverse) evs 0 0 []).2 ∧
    HDoom cands (Seam.table I) (tableOut I (tableStmt I hI input w ξ ch claim)
      (vecOf I.tableColumns evs.flatten)) h

/-- **The table sumcheck's rounds and final values** (`table_sumcheck`, `bus.rs:218-259`),
from doom on the sumcheck's input relation after `ξ`: the plain sumcheck, each round charged
`L₀ · 3 / |E|`, then the evaluations and the final check. -/
noncomputable def tableSumcheckSpec (colOf : I.ColumnId → ℕ) (w : BusWit)
    (fid : TableFid tables I hI input layout colOf w) (htw : ∀ t ∈ tables, 0 < t.width)
    (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) (ξ : E) :
    Spec (Verifier.tableSumcheckClaims tables layout.tableLogHeights (w.result tables layout).forms (cpsOf tables ξ)
        (fpsOf tables ξ) (w.result tables layout).point (dot (fpsOf tables ξ) (w.result tables layout).totals))
      (HDoom cands (SumcheckRound.rel (tableFamily I) 0)
        ((busStmt I hI input w, ξ), (#v[], dot (fpsOf tables ξ) (w.result tables layout).totals)))
      (TableSumcheckPost tables I hI cands input layout w ξ) εmax
      (sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T) T :=
  let s := busStmt I hI input w
  let bus := w.result tables layout
  let n := layout.tableLogHeights.foldl max 0
  (wireSumcheckSpec (T := T) (tableFamily I) cands (tableFamily_consistent I hd)
    (tableFamily_sound I) hfin hcard (by norm_num) he (s, ξ) (List.replicate n none) 0 #v[]
    (dot (fpsOf tables ξ) bus.totals) (by simp [n, fid.rounds]) (fun k hk ↦ by
      have hk' : k < I.τmax := by simpa [n, fid.rounds] using hk
      simp [tableFamily, Sumcheck.familyInv, Sumcheck.domain, Sumcheck.unitWeights, wireDomain,
        hk'])).bind' fun ⟨ch, claim⟩ ↦
    let P := SumcheckPost (tableFamily I) cands (s, ξ) I.τmax #v[] (ch, claim)
    let rows := rowsOf tables layout bus ch.reverse
    ((tableTermsSpec tables hT P (fun _ _ hp ↦ ⟨hp.1, hp.2.append _⟩) (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
      rows (rowsOf_width_pos tables htw layout bus _) 0 0 []).mono (fun _ hp ↦ hp) (fun _ _ hp ↦ hp) le_rfl
      (rowsLead_le _ _) le_rfl).bind' fun ⟨final, claims⟩ ↦
    (Spec.require (c := final = claim) (Post := fun _ h ↦ ∃ evs, ReadShape rows evs ∧
        ch.length = I.τmax ∧
        claims = (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse rows evs 0 0 []).2 ∧
        HDoom cands (Seam.table I) (tableOut I (tableStmt I hI input w ξ ch claim)
          (vecOf I.tableColumns evs.flatten)) h)
      (fun _ hp hc ↦ by
        obtain ⟨evs, hs, heq, hlen, W, hW, hR⟩ := hp
        have hl : ch.length = I.τmax := by simpa using hlen
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        simp only at hfst hsnd
        refine ⟨evs, hs, hl, hsnd, W, hW, finalValues_keep I hR _ ?_⟩
        rw [Sumcheck.finalCheck, decide_eq_true_eq]
        show formula I (s, ξ) (vecOf I.τmax ch).reverse (vecOf I.tableColumns evs.flatten) = claim
        rw [← fid.formula ξ ch evs hl hs, ← hfst, hc])).bind' fun _ ↦
    (Spec.ret (Post := TableSumcheckPost tables I hI cands input layout w ξ) claims).mono
      (fun _ ⟨evs, hs, hl, hc, hD⟩ ↦ ⟨ch, claim, evs, hs, hl, hc, hD⟩) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl

open Classical in
/-- **The table sumcheck** (`tablePhase`, `lib.rs:242-266`, `bus.rs:218-259`) after the bus phase
read `w`: from the bus seam at `w` to the table seam on the wire. `ξ` is charged
`L₀ · (B + 2) / |E|`, each round `L₀ · 3 / |E|`. -/
noncomputable def tablePhaseSpec (colOf : I.ColumnId → ℕ) (w : BusWit)
    (fid : TableFid tables I hI input layout colOf w) (htw : ∀ t ∈ tables, 0 < t.width)
    (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) :
    Spec (tablePhaseClaims tables layout (w.result tables layout)) (BusAt I hI cands input w)
      (TablePost I cands input colOf) εmax
      (xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T)
      T :=
  let s := busStmt I hI input w
  (Spec.sampleE (xiError I L₀) (Post := fun ξ h ↦ HDoom cands
      (SumcheckRound.rel (tableFamily I) 0)
      ((s, ξ), (#v[], dot (fpsOf tables ξ) (w.result tables layout).totals)) h)
    (fun h₀ hp ↦ by
      obtain ⟨-, -, -, W, hW, hR⟩ := hp
      refine le_trans ?_ (xi_escape I (hfin W) (hcard W) s hR)
      gcongr with ξ _
      intro hD
      refine ⟨W, firstWord_append hW _, ?_⟩
      rw [fid.target ξ, tableFamily_rel_zero]
      exact hD)).bind' fun ξ ↦
  (tableSumcheckSpec tables I hI cands input layout colOf w fid htw hd hfin hcard he hT ξ).bind'
    fun tableClaims ↦
  (Spec.ret (Post := TablePost I cands input colOf) ((w.result tables layout).claims ++ tableClaims)).mono
    (fun _ hp ↦ by
      obtain ⟨ch, claim, evs, hs, hl, rfl, W, hW, hR⟩ := hp
      exact ⟨W, _, hW, hR, rfl, fid.claims ξ ch claim evs hl hs, _, _, rfl⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl
    le_rfl

end
end LeanVM.Protocol.EndToEnd.Front
