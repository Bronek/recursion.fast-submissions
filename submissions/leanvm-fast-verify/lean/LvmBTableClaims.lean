-- New for lvm (WP-2): the table-phase part of leanVM `formal/lean_vm/LeanVM/Protocol/Verifier/Claims.lean`
-- (`tableTermsClaims`, `tableSumcheckClaims`, `tablePhaseClaims`, lines 41-81) and of
-- `formal/Statement/LeanVmVerifier.lean` (`tableWidths`, `globalColumnBases`, lines 961-967), at
-- formal rev 40f877dc, over a table list `tables` (the source's are at leanISA's `tables`, cut from
-- `LvmVCore`). Group B's copy of these seam declarations, for `LvmFrontTableTerms`/`TablePhase`.
import LvmVCore

/-!
# The table phase in claim-list form, over a table list

leanVM's `Verifier.Claims` writes the table phase of `verify_execution`
(`crates/verifier/src/lib.rs:242-266`, `bus.rs:215-259`) with the tables' column claims as one
list: `tableTermsClaims` reads each table's evaluations and collects a claim per column,
numbered from the table's first global column (`globalColumnBases`), `tableSumcheckClaims` is
`tableSumcheck` returning those claims, and `tablePhaseClaims` draws `ξ`, batches, and prepends
the bus phase's claims. The source fixes the table list to leanISA's instruction tables; here it is
the argument `tables`, the list `verifyBusBalance tables` and `tableSumcheck tables` take in
`LvmVCore`. The framework's six global columns before the tables' (`globalColumnCount`) are kept
as the constant they are in the verifier.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Compile

section

variable (tables : List Table)

/-- `TABLE_WIDTHS` (`layout.rs:471-478`), of the table list. -/
def tableWidths : List ℕ := tables.map Table.width

/-- `GLOBAL_COLUMN_BASES`: each table's first global column (`layout.rs:479-487`), of the table
list. -/
def globalColumnBases : List ℕ :=
  (List.range tables.length).map fun t ↦ globalColumnCount + ((tableWidths tables).take t).sum

/-- `tableTerms`, collecting the column claims of the evaluations. -/
def tableTermsClaims (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → ℕ → E → List ColumnClaim → VerifierProgram (E × List
        ColumnClaim)
  | [], _, final, claims => return (final, claims)
  | (table, height, forms, weight) :: rest, cursor, final, claims => do
    let evaluations ← VerifierProgram.readScalars table.width
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let claims := claims ++ evaluations.zipIdx.map fun (value, column) ↦
      ⟨(globalColumnBases tables).getD table.opcode 0 + column, point.take height, value⟩
    tableTermsClaims constraintPowers formPowers point rest (cursor + table.nConstraints) final
      claims

/-- `tableSumcheck`, returning the tables' column claims. -/
def tableSumcheckClaims (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    VerifierProgram (List ColumnClaim) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheck target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := List.zip tables (List.zip heights (List.zip busForms weights))
  let (final, claims) ← tableTermsClaims tables constraintPowers formPowers point rows 0 0 []
  VerifierProgram.require (final = claim)
  return claims

/-- `tablePhase`, returning the bus's and the tables' column claims. -/
def tablePhaseClaims (layout : Layout) (bus : BusResult) : VerifierProgram (List ColumnClaim) := do
  let xi ← VerifierProgram.sampleChallenge
  let nConstraints := (tables.map Table.nConstraints).sum
  let xiPowers := powers xi (nConstraints + 3)
  let constraintPowers := xiPowers.take nConstraints
  let formPowers := xiPowers.drop nConstraints
  let target := dot formPowers bus.totals
  let tableClaims ← tableSumcheckClaims tables layout.tableLogHeights bus.forms constraintPowers
    formPowers bus.point target
  return bus.claims ++ tableClaims

end
end LeanVM.Protocol.Verifier
