-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Claims.lean` (formal rev 40f877dc),
-- with, from `Protocol/Verifier/Claims.lean`, `ColumnClaim.stackClaim` (lines 36-39) and the
-- `AllRet` machinery (lines 109-187), and, from `Statement/LeanVmVerifier.lean`, `ringSwitchClaim`
-- (lines 1974-1978), as `LvmClaims` for lvm (WP-2). The rest of `Verifier/Claims` (the claim-list
-- form of the leanISA verifier, `buildLayout_ok`, ...) is leanISA-specific and not ported.
import LvmVCore
import LvmProtoField

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.Compile

section


/-- A column claim as a claim on the stack, at its column's placement. -/
def ColumnClaim.stackClaim (c : ColumnClaim) (layout : Layout) : StackClaim :=
  let point := (layout.placement c.column).stackPoint c.point layout.stackLog
  (fun x ↦ eqEval point x, c.value)

/-- Step 7's ring-switching claim on the stack: supported on `q_keccak`'s region, its weight
carries the placement's selector (`lib.rs:305-311`). -/
def ringSwitchClaim (layout : Layout) (target : E) (weight : List E → E) : StackClaim :=
  let qkeccakPlacement := layout.placement qkeccak
  (fun x ↦ qkeccakPlacement.eqAbove x * weight (x.take qkeccakPlacement.variableCount), target)

/-! ## Every value a program returns -/

namespace Claims

/-- Every value a program can return satisfies `P`, whatever it reads and samples: an inductive
predicate, so that elaboration does not unfold it along a program. -/
inductive AllRetI {α : Type} (P : α → Prop) : VerifierProgram α → Prop
  | ret {a : α} : P a → AllRetI P (.ret a)
  | fail : AllRetI P .fail
  | read {k : E → VerifierProgram α} : (∀ x, AllRetI P (k x)) → AllRetI P (.read k)
  | sample {k : E → VerifierProgram α} : (∀ c, AllRetI P (k c)) → AllRetI P (.sample k)
  | grind {b : ℕ} {k : VerifierProgram α} : AllRetI P k → AllRetI P (.grind b k)
  | commit {h w : ℕ} {k : VerifierProgram α} : AllRetI P k → AllRetI P (.commit h w k)
  | query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} :
      (∀ r, AllRetI P (k r)) → AllRetI P (.query i ps k)

/-- Every value `p` can return satisfies `P`. -/
abbrev AllRet {α : Type} (p : VerifierProgram α) (P : α → Prop) : Prop := AllRetI P p

theorem allRet_of_forall {α : Type} {P : α → Prop} (h : ∀ a, P a) : ∀ p : VerifierProgram α,
    AllRet p P
  | .ret a => .ret (h a)
  | .fail => .fail
  | .read k => .read fun x ↦ allRet_of_forall h (k x)
  | .sample k => .sample fun c ↦ allRet_of_forall h (k c)
  | .grind _ k => .grind (allRet_of_forall h k)
  | .commit _ _ k => .commit (allRet_of_forall h k)
  | .query _ _ k => .query fun r ↦ allRet_of_forall h (k r)

theorem allRet_true {α : Type} (p : VerifierProgram α) : AllRet p fun _ ↦ True :=
  allRet_of_forall (fun _ ↦ trivial) p

theorem AllRet.mono {α : Type} {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) {p : VerifierProgram α}
    (hp : AllRet p P) : AllRet p Q := by
  induction hp with
  | ret h => exact .ret (hPQ _ h)
  | fail => exact .fail
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

theorem AllRet.bind {α β : Type} {Q : α → Prop} {P : β → Prop} {f : α → VerifierProgram β}
    (hf : ∀ a, Q a → AllRet (f a) P) (p : VerifierProgram α) (hp : AllRet p Q) : AllRet (p.bind f)
        P := by
  induction hp with
  | ret h => exact hf _ h
  | fail => exact .fail
  | read _ ih => exact .read ih
  | sample _ ih => exact .sample ih
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query ih

/-- Two continuations that agree on every value a program returns make one program. -/
theorem bind_congr {α β : Type} {Q : α → Prop} {f g : α → VerifierProgram β} (h : ∀ a, Q a → f
    a = g a)
    (p : VerifierProgram α) (hp : AllRet p Q) : p.bind f = p.bind g := by
  induction hp with
  | ret hq => exact h _ hq
  | fail => rfl
  | read _ ih => exact congrArg VerifierProgram.read (funext ih)
  | sample _ ih => exact congrArg VerifierProgram.sample (funext ih)
  | grind _ ih => exact congrArg (VerifierProgram.grind _) ih
  | commit _ ih => exact congrArg (VerifierProgram.commit _ _) ih
  | query _ ih => exact congrArg (VerifierProgram.query _ _) (funext ih)

theorem allRet_readN : ∀ n : ℕ, AllRet (VerifierProgram.readScalars n) fun xs ↦ xs.length = n
  | 0 => .ret rfl
  | n + 1 => .read fun x ↦
    AllRet.bind (fun xs hxs ↦ .ret (by show (x :: xs).length = n + 1; simp [hxs])) _
      (allRet_readN n)

theorem allRet_liftOption {α : Type} (o : Option α) : AllRet (liftOption o) fun a ↦ o = some a := by
  cases o with
  | none => exact .fail
  | some a => exact .ret rfl

end Claims

end

end LeanVM.Protocol.Verifier

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Protocol.Verifier

section

/-- The cube point of index `x` on `μ` coordinates, bit `0` first, with coordinates `0`/`1`
in `E`. -/
def boolPoint (μ x : ℕ) : List E :=
  (List.range μ).map fun i ↦ if x.testBit i then 1 else 0

/-- The meaning of a stack claim: the weight's values on the cube, paired with the stack, give
the value. -/
def StackClaim.Holds (μ : ℕ) (c : StackClaim) (q : Column μ) : Prop :=
  ∑ x : Fin (2 ^ μ), c.1 (boolPoint μ x) * ofK (q.values.getD x 0) = c.2

/-- A weight function is the multilinear extension of its values on the cube: at every point of
`μ` coordinates it is `Σ_x w(x) · eq(x, point)`. -/
def IsMultilinearFn (μ : ℕ) (w : List E → E) : Prop :=
  ∀ point : List E, point.length = μ →
    w point = ∑ x : Fin (2 ^ μ), w (boolPoint μ x) * eqEval (boolPoint μ x) point

/-- Every column claim of a list holds of the stack, each placed on the stack by the layout. -/
def ColumnClaimsHold (layout : Layout) (cs : List ColumnClaim) (q : Column layout.stackLog) :
    Prop :=
  ∀ c ∈ cs, StackClaim.Holds layout.stackLog (c.stackClaim layout) q

/-- Every claim of the list holds of the stack `q`, by a reading `H` of a claim (for leanISA,
`Front.WireHolds`: the `KECCAK` output lanes read as the derived columns they claim, every other
column on the stack). -/
def ClaimsHoldBy {layout : Layout} (H : ColumnClaim → Column layout.stackLog → Prop)
    (cs : List ColumnClaim) (q : Column layout.stackLog) : Prop :=
  ∀ c ∈ cs, H c q

end
end LeanVM.Protocol.EndToEnd
