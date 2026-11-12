import LvmDecideBase

/-!
# The decision `F`: sumcheck rounds, the grand-product GKR, the table sumcheck

Ported from leanVM `formal/Statement/LeanVmVerifier.lean` on the reader `DM` (`LvmDecideBase`):

* `sumcheckRoundPoly`, `sumcheck` (`:1143-1164`; `transcript.rs:188-233`): a round polynomial
  of `count` coefficients is sent with one left out, which the running claim fixes (plain mode:
  `q(0) + q(1) = claim` fixes `c₁`; equality mode with `eq_factor = r`:
  `(1 + r) q(0) + r q(1) = claim` fixes `c₀`);
* `gkrStep`, `gkrLayers`, `verifyGkrGrandProducts` (`:1176-1218`; `bus.rs:14-51`): the push,
  pull and count trees batched, two levels a step, one when the remaining depth is odd;
* `tableWeights`, `tableTerms`, `tableSumcheck` (`:1315-1352`; `bus.rs:215-259`), generic over
  the tables (`TableSpec`): leanVM's six instruction tables are replaced by the M3 instance's
  tables (LoopIR blocks and `BITS`, WP-9/WP-10), whose constraints also read the table's point
  (the fixed columns' values there, the self-evaluation of BLUEPRINT §4.5).

Deviation: `require` records a failed check and goes on (LvmDecideBase), where leanVM fails.
-/

set_option autoImplicit false

namespace Lvm

open DM

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`: the round polynomial's
coefficients, constant first (`LeanVmVerifier.lean:1146-1153`). -/
def sumcheckRoundPoly (count : Nat) (claim : FE) : Option FE → DM (List FE)
  | none => do
    let constant ← readE
    let tail ← readEs (count - 2)
    pure (constant :: (claim + sumE tail) :: tail)
  | some eqFactor => do
    let tail ← readEs (count - 1)
    pure ((claim + eqFactor * sumE tail) :: tail)

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry; the challenges and the
final claim (`LeanVmVerifier.lean:1158-1164`). -/
def sumcheck (claim : FE) (count : Nat) : List (Option FE) → DM (List FE × FE)
  | [] => pure ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← sampleE
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    pure (challenge :: point, final)

/-! ## The grand-product GKR (`LeanVmVerifier.lean:1176-1218`) -/

/-- The push, pull and count trees' values at `point`. -/
structure GkrState where
  /-- The three trees' values. -/
  values : List FE
  /-- Their point. -/
  point : List FE

/-- One step of `step` levels (`bus.rs:21-47`). -/
def gkrStep (step : Nat) (state : GkrState) : DM GkrState := do
  let combiner ← sampleE
  let claim := polyEval state.values combiner
  let (x, claim) ← sumcheck claim (2 ^ step + 1) (state.point.map some)
  let child0 ← readEs (2 ^ step)
  let child1 ← readEs (2 ^ step)
  let child2 ← readEs (2 ^ step)
  let children := [child0, child1, child2]
  let products := children.map prodE
  require (claim == polyEval products combiner)
  let y ← samples step
  let values := children.map (multilinearEval · y)
  pure ⟨values, y ++ x⟩

/-- The `while layer > 0` loop (`bus.rs`; `LeanVmVerifier.lean:1199-1210`). -/
def gkrLayers : Nat → GkrState → DM GkrState
  | 0, s => pure s
  | 1, s => gkrStep 1 s
  | n + 2, s =>
    if n % 2 = 1 then do
      let s ← gkrStep 1 s
      gkrLayers (n + 1) s
    else do
      let s ← gkrStep 2 s
      gkrLayers n s

/-- `verify_gkr_grand_products(depth)`: the count root, the point, the three trees' values
(`bus.rs:14-51`). -/
def verifyGkrGrandProducts (depth : Nat) : DM (FE × List FE × List FE) := do
  let shared ← readE
  let count ← readE
  let s ← gkrLayers depth ⟨[shared, shared, count], []⟩
  pure (count, s.point, s.values)

/-! ## The table sumcheck (`LeanVmVerifier.lean:1315-1352`) -/

/-- A table of the M3 instance, as the table sumcheck sees it. -/
structure TableSpec where
  /-- Its log-height. -/
  logHeight : Nat
  /-- Its columns (the evaluations the prover sends). -/
  width : Nat
  /-- Its constraint count. -/
  nConstraints : Nat
  /-- Its constraints at the table's point, from the columns' values there (the fixed columns'
  values at the point are the table's own business: LoopIR self-evaluation). -/
  constraints : List FE → List FE → List FE

/-- The tables' weights at the point (`bus.rs:231-237`). -/
def tableWeights (heights : List Nat) (equalityPoint point : List FE) : List FE :=
  point.zipIdx.foldl (fun weights (challenge, coord) =>
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    List.zipWith (fun weight height => weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ => 1)

/-- The per-table loops of `table_sumcheck` (`bus.rs:239-257`). -/
def tableTerms (constraintPowers formPowers point : List FE) :
    List (TableSpec × List Form × FE) → Nat → FE → DM (FE × List (List FE × List FE))
  | [], _, final => pure (final, [])
  | (table, forms, weight) :: rest, cursor, final => do
    let evaluations ← readEs table.width
    let tpoint := point.take table.logHeight
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints tpoint evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.value (evaluations.getD · 0))))
    let (final, rows) ← tableTerms constraintPowers formPowers point rest
      (cursor + table.nConstraints) final
    pure (final, (tpoint, evaluations) :: rows)

/-- `table_sumcheck(…)` (`bus.rs:218-259`): each table's point and its columns' values there.
`rounds` is the schedule's (`Params.tableRounds`); leanVM takes the tallest table's height. -/
def tableSumcheck (rounds : Nat) (tables : List TableSpec) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List FE) (target : FE) :
    DM (List (List FE × List FE)) := do
  let (challenges, claim) ← sumcheck target 4 (List.replicate rounds none)
  let point := challenges.reverse
  let weights := tableWeights (tables.map (·.logHeight)) equalityPoint point
  let rows := List.zip tables (List.zip busForms weights)
  let (final, evaluations) ← tableTerms constraintPowers formPowers point rows 0 0
  require (final == claim)
  pure evaluations

end Lvm
