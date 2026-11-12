-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/ToArkLib/GrandProduct.lean` (formal rev 40f877dc) as `LvmGrandProduct` for lvm (WP-2).
/-
  LeanVM.Protocol.ToArkLib.GrandProduct

  The batched grand-product argument as a typed component: from the roots of several product
  trees to one evaluation claim per tree at one shared point, layer by layer, at the slot
  `Typed.gkrSlot`. Definition and completeness. Candidate for ArkLib.
-/


import LvmSumcheckRound
import LvmCpProductTree
import LvmCpPartialSum
import LvmCpPowerBatching
import Mathlib.Algebra.Polynomial.BigOperators

/-! lvm (WP-2): the ArkLib-typed components and their typed completeness (`lambdaStep`,
`lambdaComplete`, `sendChildren`, `childrenComplete`, `interpPrefix`, `interpPrefixComplete`,
`interpolate`, `interpolateComplete`, `layerStep`, `layerStepComplete`, `layerSteps`,
`layerStepsComplete`, `odd`, `oddComplete`, `gkr`, `gkrComplete`), built on `ToArkLib.Typed.*`
outside lvm's imports, are cut. Kept: the statements and relations, the layer's sumcheck family
and its honesty, the combiner's, descendants' and combination challenges' next statements and
checks, and the facts the typed completeness proofs composed (`lambdaNext_mem_rel`,
`combineCheck_children`, `interpDone_mem`, `layerRel_subset_relOut`, `relIn_iff_layerRel_zero`),
made public here. The round polynomial `roundPolyRaw` is restated on Mathlib's `Polynomial`
(leanVM: CompPoly's `CPolynomial`, outside lvm's imports), so `roundPoly` is noncomputable. The
verifier lvm runs is `LvmVCore`'s `gkrStep`/`gkrLayers`. -/

/-!
# The grand product by GKR

`nside` product trees of `2 ^ μ` leaves each. The leaves are tables computed from the public data
and the oracles' contents (`leaves`); nobody sends them. The input statement is the public data
and one claimed root per tree, and the input relation (`Gkr.relIn`) says each root is the product
of its tree's leaves. The output statement is the public data, a point `ζ` of `μ` coordinates and
one value per tree, and the output relation (`Gkr.relOut`) says each value is the multilinear
extension of its tree's leaves at `ζ`. In between, the statement at layer `m` (`LayerStmt`) is a
point of `m` coordinates and one value per tree, the extension of the tree's level on `m`
variables (`layerRel`). A step (`layerStep`) goes `ρ` levels down, from layer `m` to `m + ρ`, at
the slot `Typed.stepSlot F nside ρ m`:

* the combiner (`lambdaStep`, one challenge, batching by powers, `Typed.batch`): the verifier
  draws `λ`, and the claims become one, `Σ_s value_s · λ^s` (`powerBatch`), the sum of the layer
  identity `Σ_s Ṽ_s(r) · λ^s = Σ_x eq(r, x) Σ_s λ^s ∏_c Ṽ'_s(c, x)` over the level `ρ` below;
* the normalized sumcheck on that identity (`m` rounds of `SumcheckRound.round` on
  `SumcheckRound.normalizedWeights`): the message is the cofactor of `eq(r, ·)` (`roundPoly`), a
  sum of products of `2 ^ ρ` affine factors, so of degree `2 ^ ρ`, sent as its `2 ^ ρ + 1`
  coefficients;
* the descendants (`sendChildren`, one message): the prover sends, per tree, the `2 ^ ρ` values of
  the level below at the descendants of the sumcheck's point `c`, and the verifier checks that
  their combined products are the sumcheck's final claim (`combineCheck`);
* the combination challenges (`interpolate`, `ρ` challenges `u`, one round each, lowest first):
  the new point is `(u, c)` and each tree's new value is the extension of its descendants'
  values at `u`.

`gkr` reads the roots as the statement at layer `0`, takes one binary step first when `μ` is odd
(`Gkr.odd`) and steps of radix four after (`Gkr.layerSteps`), each step opening with its
combiner; its slot is `Typed.gkrSlot F nside μ`, so that a protocol's slot that appends it takes
it, and its errors are `Typed.gkrErrors`, which its knowledge soundness is stated at.
`gkrComplete` is its completeness, composed from its parts' through `Typed.Complete.append` on the
layer identities of `LeanVM.Protocol.ToCompPoly.ProductTree`.

*Riders* are further tables computed from the public data and the oracles, each on at most `μ`
variables. The input relation asks each to be zero; the output relation asks each extension to
vanish at the low coordinates of `ζ` (`lowPoint`). They are for a protocol that reuses `ζ` as a
zerocheck point; no definition reads them. A rider on no variable is one value: it states a
condition on the public data and the oracles, carried unchanged from the input relation to the
output relation, which no challenge can make true. The oracles pass through untouched, and there
is no witness.

Written from the mathematics of the product-tree argument. The deployed verifier draws each
layer's combiner at the start of the layer, as here (`verify_gkr_grand_products`,
`crates/verifier/src/bus.rs:20-48` at leanVM `40f877dc`).

## Relation to ArkLib pull request 818

ArkLib's pull request 818 formalizes GKR for layered circuits of addition and multiplication
gates: a sumcheck over the `2k` variables of the two children's indices against the wiring
predicates, and Thaler's line restriction. It is another protocol, whose shapes correspond:
`LayerStmt` and `layerRel` to its `GKRStatement` and `Materialized.layerRel`, `layerStep` and
`layerSteps` to its `gkrLayer` and `gkrReduction` (with `Typed.Def.append` for
`seqCompose`), `sendChildren` with `interpolate` to its `Combine` (interpolation for the line).
This module goes when ArkLib carries a product-tree GKR with round-by-round knowledge soundness.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval
open scoped Polynomial

section

namespace Gkr

variable {F : Type} [Field F]
  {X : Type} {ι : Type} {O : ι → Type}

/-! ## Statements and relations -/

/-- The statement at a layer: the public data, the point, and one claimed value per tree. -/
abbrev LayerStmt (X F : Type) (nside m : ℕ) : Type := X × (Vector F m × (Fin nside → F))

/-- The public data of a step's sumcheck: the layer statement it started from and the
combiner. -/
abbrev LayerX (X F : Type) (nside m : ℕ) : Type := LayerStmt X F nside m × F

/-- What a step's sumcheck reads: its public data, the oracles' contents, no witness. -/
abbrev LayerCtx (X F : Type) {ι : Type} (O : ι → Type) (nside m : ℕ) : Type :=
  SumcheckRound.Ctx (LayerX X F nside m) O Unit

/-- The public data of the protocol, in a step's context. -/
abbrev dataOf {nside m : ℕ} (ctx : LayerCtx X F O nside m) : X := ctx.1.1.1.1

/-- The oracles' contents, in a step's context. -/
abbrev oraclesOf {nside m : ℕ} (ctx : LayerCtx X F O nside m) : ∀ i, O i := ctx.1.2

/-- The point the layer started from. -/
abbrev pointOf {nside m : ℕ} (ctx : LayerCtx X F O nside m) : Vector F m := ctx.1.1.1.2.1

/-- The combiner of the layer. -/
abbrev combinerOf {nside m : ℕ} (ctx : LayerCtx X F O nside m) : F := ctx.1.1.2

/-- The low `τ` coordinates of a point. -/
def lowPoint {μ : ℕ} (ζ : Vector F μ) (τ : Fin (μ + 1)) : Vector F τ :=
  Vector.ofFn fun i ↦ ζ[i.val]'(by have := i.isLt; have := τ.isLt; omega)

variable (nside μ : ℕ) (leaves : X → (∀ i, O i) → Fin nside → CMlPolynomialEval F μ)
  (riders : X → (∀ i, O i) → List (Σ τ : Fin (μ + 1), CMlPolynomialEval F τ))

/-- Every rider table is zero. -/
def RidersZero (x : X) (o : ∀ i, O i) : Prop :=
  ∀ r ∈ riders x o, ∀ i : Fin (2 ^ (r.1 : ℕ)), r.2[i] = 0

/-- The input relation: every rider table is zero, and every tree's claimed root is the product
of its leaves. -/
def relIn : Set (((X × (Fin nside → F)) × ∀ i, O i) × Unit) :=
  {p | RidersZero μ riders p.1.1.1 p.1.2 ∧
    ∀ s, p.1.1.2 s = ∏ i : Fin (2 ^ μ), (leaves p.1.1.1 p.1.2 s)[i]}

/-- The relation at layer `m`: every rider table is zero, and every tree's claimed value is the
extension of its level on `m` variables at the point. -/
def layerRel (m : ℕ) : Set ((LayerStmt X F nside m × ∀ i, O i) × Unit) :=
  {p | RidersZero μ riders p.1.1.1 p.1.2 ∧
    ∀ s, evalMle (layerTable (leaves p.1.1.1 p.1.2 s) m) p.1.1.2.1 = p.1.1.2.2 s}

/-- The output relation: every tree's claimed value is the extension of its leaves at the point,
and every rider's extension vanishes at the point's low coordinates. -/
def relOut : Set ((LayerStmt X F nside μ × ∀ i, O i) × Unit) :=
  {p | (∀ s, evalMle (leaves p.1.1.1 p.1.2 s) p.1.1.2.1 = p.1.1.2.2 s) ∧
    ∀ r ∈ riders p.1.1.1 p.1.2, evalMle r.2 (lowPoint p.1.1.2.1 r.1) = 0}

/-! ## The layer's sumcheck -/

section Layer

variable (ρ m : ℕ)

/-- The trees' levels `ρ` below the step's layer. -/
def below (ctx : LayerCtx X F O nside m) (s : Fin nside) : CMlPolynomialEval F (m + ρ) :=
  layerTable (leaves (dataOf ctx) (oraclesOf ctx) s) (m + ρ)

/-- The summand of the layer's sumcheck at a point `y`: the combination, by the powers of the
combiner, of the products of the descendants of `y` in each tree. -/
def summand (ctx : LayerCtx X F O nside m) (y : Vector F m) : F :=
  ∑ s, combinerOf ctx ^ s.val *
    ∏ c : Fin (2 ^ ρ), evalMle (below nside μ leaves ρ m ctx s) (childPoint ρ c y)

/-- The value of a descendant's extension with the round's variable fixed to `z`. -/
def descendant (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) (x' : Fin (2 ^ (m - (j + 1)))) (s : Fin nside) (c : Fin (2 ^ ρ)) (z : F) :
    F :=
  evalMle (below nside μ leaves ρ m ctx s) (childPoint ρ c (fixLow hj (cv.push z) (boolVec x')))

/-- The honest round polynomial at round `j` (lvm: on Mathlib's `Polynomial`): the eq-weighted sum,
over the coordinates not yet bound, of the combined products of the descendants' values, each
affine in the variable of the round. -/
noncomputable def roundPolyRaw (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) : F[X] :=
  ∑ x' : Fin (2 ^ (m - (j + 1))), Polynomial.C (lagrangeBasis ((pointOf ctx).drop (j + 1)))[x'] *
    ∑ s, Polynomial.C (combinerOf ctx ^ s.val) *
      ∏ c : Fin (2 ^ ρ), (Polynomial.C (descendant nside μ leaves ρ m ctx hj cv x' s c 0) +
        Polynomial.X * Polynomial.C (descendant nside μ leaves ρ m ctx hj cv x' s c 1 -
          descendant nside μ leaves ρ m ctx hj cv x' s c 0))

/-- The honest round polynomial has degree at most `2 ^ ρ`: a sum of products of `2 ^ ρ` affine
factors. -/
theorem degree_roundPolyRaw_le (ctx : LayerCtx X F O nside m) {j : ℕ}
    (hj : j < m) (cv : Vector F j) :
    (roundPolyRaw nside μ leaves ρ m ctx hj cv).degree ≤ (2 ^ ρ : ℕ) := by
  refine Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr ?_)
  rw [roundPolyRaw]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x' _ ↦ ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ ↦ ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun c _ ↦ ?_).trans (by simp)
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  refine (Polynomial.natDegree_mul_le).trans ?_
  simp

/-- The honest round polynomial as a message, its `2 ^ ρ + 1` coefficients; the zero polynomial
past the last round. -/
noncomputable def roundPoly (ctx : LayerCtx X F O nside m) (j : ℕ) (cv : Vector F j) :
    SumcheckRound.Message F (2 ^ ρ) :=
  if h : j < m then SumcheckRound.ofPolynomial _ (roundPolyRaw nside μ leaves ρ m ctx h cv)
  else SumcheckRound.ofPolynomial _ 0

/-- The verifier's domain at round `j`: the normalized round's, against the layer's point. -/
def weights : SumcheckRound.Weights F (LayerX X F nside m) :=
  SumcheckRound.normalizedWeights fun x ↦ x.1.2.1

/-- The family of claims of the layer's sumcheck: the eq-weighted running sums of the summand,
the honest polynomials, the normalized domain, and the riders' condition. -/
noncomputable def family : SumcheckRound.Family F (LayerX X F nside m) O Unit (2 ^ ρ) where
  claim := fun ctx j cv ↦ partialSum (summand nside μ leaves ρ m ctx) (pointOf ctx) j cv
  poly := roundPoly nside μ leaves ρ m
  weight := weights nside m
  inv := fun ctx _ _ ↦ RidersZero μ riders (dataOf ctx) (oraclesOf ctx)

/-- The honest polynomial's value at `x` is the running sum with one more coordinate fixed to
`x`: each descendant's value is affine in the round's variable. -/
private theorem roundPoly_eval (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) (x : F) :
    SumcheckRound.evaluate (2 ^ ρ) (roundPoly nside μ leaves ρ m ctx j cv) x =
      partialSum (summand nside μ leaves ρ m ctx) (pointOf ctx) (j + 1) (cv.push x) := by
  rw [roundPoly, dite_eq_left hj,
    SumcheckRound.evaluate_ofPolynomial _ _ (degree_roundPolyRaw_le nside μ leaves ρ m ctx hj cv),
    roundPolyRaw, Polynomial.eval_finsetSum, partialSum, dite_eq_left (Nat.succ_le_of_lt hj),
    evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x' _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum, mul_comm]
  simp only [Fin.getElem_fin, restrictTable, Vector.getElem_ofFn, summand, Fin.eta]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_C]
  unfold descendant
  have key : ∀ z : F,
      evalMle (below nside μ leaves ρ m ctx s)
          (childPoint ρ c (fixLow hj (cv.push z) (boolVec x'))) =
        evalMle (below nside μ leaves ρ m ctx s)
          ((childPoint ρ c (fixLow hj (cv.push 0) (boolVec x'))).set (ρ + j) z (by omega)) := by
    intro z
    rw [fixLow_push_set hj cv (boolVec x') z, childPoint_set]
  rw [key x, key 1, evalMle_set (below nside μ leaves ρ m ctx s) _ (k := ρ + j) (by omega) x,
    ← key 0]
  ring

/-- The honest polynomial passes the verifier's check: its weighted values at `0` and `1` are the
running sum before the round. -/
private theorem roundPoly_check (ctx : LayerCtx X F O nside m) {j : ℕ} (hj : j < m)
    (cv : Vector F j) :
    SumcheckRound.weightedSum (2 ^ ρ) (weights nside m ctx.1.1 j)
        (roundPoly nside μ leaves ρ m ctx j cv) =
      partialSum (summand nside μ leaves ρ m ctx) (pointOf ctx) j cv := by
  simp only [weights, SumcheckRound.normalizedWeights, hj, ↓reduceDIte,
    SumcheckRound.weightedSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [roundPoly_eval nside μ leaves ρ m ctx hj cv 0, roundPoly_eval nside μ leaves ρ m ctx hj cv 1,
    partialSum_split _ _ hj]

/-- The layer's family is honest. -/
theorem family_honest : (family nside μ leaves riders ρ m).Honest m where
  check := fun ctx _ c hj ↦ roundPoly_check nside μ leaves ρ m ctx hj c
  next := fun ctx _ c x hj ↦ roundPoly_eval nside μ leaves ρ m ctx hj c x
  inv_push := fun _ _ _ _ _ h ↦ h

/-! ## The combiner -/

/-- The statement after the combiner: the layer statement with the combiner, no challenge yet,
and the combined claim `Σ_s value_s · λ^s`. -/
def lambdaNext (s : LayerStmt X F nside m) (l : F) : SumcheckRound.Stmt (LayerX X F nside m) F 0 :=
  ((s, l), (#v[], powerBatch s.2.2 l))

variable [DecidableEq F]

omit [DecidableEq F] in
/-- On a Boolean point, the summand is the combination of the trees' levels at the layer: the
descendants' product is the node's value. -/
theorem summand_boolVec (hm : m + ρ ≤ μ) (ctx : LayerCtx X F O nside m) (x : Fin (2 ^ m)) :
    summand nside μ leaves ρ m ctx (boolVec x) =
      ∑ s, combinerOf ctx ^ s.val * (layerTable (leaves (dataOf ctx) (oraclesOf ctx) s) m)[x] := by
  unfold summand
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  rw [layerTable_contractPow _ ρ hm, contractPow_getElem]
  exact Finset.prod_congr rfl fun c _ ↦ evalMle_childPoint_boolVec ρ _ c x

omit [DecidableEq F] in
/-- The family's first claim is the combination, by the powers of the combiner, of the trees'
levels at the layer's point. -/
theorem partialSum_summand_zero (hm : m + ρ ≤ μ) (s : LayerStmt X F nside m) (o : ∀ i, O i)
    (l : F) :
    partialSum (summand nside μ leaves ρ m (((s, l), o), ())) s.2.1 0 #v[] =
      powerBatch (fun t ↦ evalMle (layerTable (leaves s.1 o t) m) s.2.1) l := by
  rw [partialSum_zero]
  have htab : (Vector.ofFn fun y ↦ summand nside μ leaves ρ m (((s, l), o), ()) (boolVec y)) =
      Vector.ofFn fun y ↦ ∑ t, l ^ t.val * (layerTable (leaves s.1 o t) m)[y] :=
    Vector.ext fun y hy ↦ by
      simp only [Vector.getElem_ofFn]
      exact summand_boolVec nside μ leaves ρ m hm _ ⟨y, hy⟩
  rw [htab, evalMle_ofFn_sum, powerBatch]
  exact Finset.sum_congr rfl fun t _ ↦ mul_comm _ _

omit [DecidableEq F] in
/-- From the layer relation, the combined claim at any challenge is the running sum of the
summand with nothing fixed, and the riders' condition carries over. -/
theorem lambdaNext_mem_rel (hm : m + ρ ≤ μ) (s : LayerStmt X F nside m) (o : ∀ i, O i)
    (l : F)
    (h : ((s, o), ()) ∈ layerRel nside μ leaves riders m) :
    ((lambdaNext nside m s l, o), ()) ∈ SumcheckRound.rel (family nside μ leaves riders ρ m) 0 := by
  obtain ⟨hz, hval⟩ := h
  refine ⟨hz, ?_⟩
  change (lambdaNext nside m s l).2.2 =
    partialSum (summand nside μ leaves ρ m (((s, l), o), ())) s.2.1 0 #v[]
  rw [partialSum_summand_zero nside μ leaves ρ m hm s o l]
  show powerBatch s.2.2 l = _
  exact congrArg (powerBatch · l) (funext fun t ↦ (hval t).symm)

/-! ## The descendants -/

/-- The statement after the descendants' message, with `i` combination challenges drawn: the
public data, the sumcheck's point, the values per tree, and the challenges. -/
abbrev InterpStmt (X F : Type) (nside m ρ i : ℕ) : Type :=
  (X × (Vector F m × (Fin nside → CMlPolynomialEval F ρ))) × Vector F i

/-- The honest values of the trees at the point `c`: each tree's level below at the descendants
of `c`. -/
def children (x : X) (o : ∀ i, O i) (c : Vector F m) (s : Fin nside) : CMlPolynomialEval F ρ :=
  Vector.ofFn fun b ↦ evalMle (layerTable (leaves x o s) (m + ρ)) (childPoint ρ b c)

/-- The verifier's check: the final claim is the combination, by the powers of the combiner, of
the products of each tree's values. -/
def combineCheck (s : SumcheckRound.Stmt (LayerX X F nside m) F m)
    (ch : Fin nside → CMlPolynomialEval F ρ) : Bool :=
  decide (s.2.2 = powerBatch (fun t ↦ ∏ c : Fin (2 ^ ρ), (ch t)[c]) s.1.2)

/-- The statement after the message: the public data, the sumcheck's point, the values. -/
def childNext (s : SumcheckRound.Stmt (LayerX X F nside m) F m)
    (ch : Fin nside → CMlPolynomialEval F ρ) : InterpStmt X F nside m ρ 0 :=
  ((s.1.1.1, (s.2.1, ch)), #v[])

/-- The relation after the descendants' message, with `i` combination challenges drawn: every
rider table is zero, and the trees' values are the honest ones at the sumcheck's point. -/
def childRel (i : ℕ) : Set ((InterpStmt X F nside m ρ i × ∀ j, O j) × Unit) :=
  {p | RidersZero μ riders p.1.1.1.1 p.1.2 ∧
    p.1.1.1.2.2 = children nside μ leaves ρ m p.1.1.1.1 p.1.2 p.1.1.1.2.1}

/-- From the sumcheck's final relation, the honest values pass the check: the final claim is the
summand at the point, the combination of the descendants' products. -/
theorem combineCheck_children (s : SumcheckRound.Stmt (LayerX X F nside m) F m)
    (o : ∀ i, O i)
    (h : ((s, o), ()) ∈ SumcheckRound.rel (family nside μ leaves riders ρ m) m) :
    combineCheck nside ρ m s (children nside μ leaves ρ m s.1.1.1 o s.2.1) = true := by
  obtain ⟨-, hclaim⟩ := h
  rw [combineCheck, decide_eq_true_eq, hclaim]
  change partialSum (summand nside μ leaves ρ m ((s.1, o), ())) s.1.1.2.1 m s.2.1 = _
  rw [partialSum_self, powerBatch]
  unfold summand
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  simp [children, below]

/-! ## The combination challenges -/

/-- The statement after one more combination challenge: the challenge appended. -/
def interpNext {i : ℕ} (s : InterpStmt X F nside m ρ i) (u : F) :
    InterpStmt X F nside m ρ (i + 1) :=
  (s.1, s.2.push u)

/-- The layer statement once the `ρ` combination challenges `u` are drawn: the point `(u, c)`,
and each tree's values interpolated at `u`. -/
def interpDone (s : InterpStmt X F nside m ρ ρ) : LayerStmt X F nside (m + ρ) :=
  (s.1.1, (Vector.cast (Nat.add_comm ρ m) (s.2 ++ s.1.2.1), fun t ↦ evalMle (s.1.2.2 t) s.2))

omit [DecidableEq F] in
/-- The values interpolated at `u` are the level below at the new point `(u, c)`. -/
theorem interpDone_mem (s : InterpStmt X F nside m ρ ρ) (o : ∀ i, O i)
    (hin : ((s, o), ()) ∈ childRel nside μ leaves riders ρ m ρ) :
    ((interpDone nside ρ m s, o), ()) ∈ layerRel nside μ leaves riders (m + ρ) := by
  obtain ⟨hz, hch⟩ := hin
  refine ⟨hz, fun t ↦ ?_⟩
  show _ = evalMle (s.1.2.2 t) s.2
  rw [hch]
  exact evalMle_cast_append ρ _ s.2 s.1.2.1

end Layer

/-! ## The whole argument -/

/-- The relation at the leaves gives the output relation: the level on `μ` variables is the
leaves, and a zero table has a zero extension everywhere. -/
theorem layerRel_subset_relOut :
    layerRel nside μ leaves riders μ ⊆ relOut nside μ leaves riders := by
  intro p ⟨hz, hval⟩
  refine ⟨fun t ↦ by rw [← hval t, layerTable_self], fun r hr ↦ ?_⟩
  rw [evalMle_eq_sum]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [hz r hr i, zero_mul]

/-- The roots as the statement at layer `0`, whose point is empty. -/
def rootStmt (s : X × (Fin nside → F)) : LayerStmt X F nside 0 := (s.1, (#v[], s.2))

/-- Roots are the products of their leaves exactly when, read as the statement at layer `0`,
they are the trees' values there. -/
theorem relIn_iff_layerRel_zero (s : X × (Fin nside → F)) (o : ∀ i, O i) :
    ((s, o), ()) ∈ relIn nside μ leaves riders ↔
      ((rootStmt nside s, o), ()) ∈ layerRel nside μ leaves riders 0 := by
  refine and_congr Iff.rfl (forall_congr' fun t ↦ ?_)
  show s.2 t = ∏ i : Fin (2 ^ μ), (leaves s.1 o t)[i] ↔
    evalMle (layerTable (leaves s.1 o t) 0) #v[] = s.2 t
  constructor
  · intro h
    rw [evalMle_zero, h, ← layerTable_zero_getElem]
    rfl
  · intro h
    rw [evalMle_zero] at h
    rw [← h, ← layerTable_zero_getElem]
    rfl

end Gkr

end
end LeanVM.Protocol
