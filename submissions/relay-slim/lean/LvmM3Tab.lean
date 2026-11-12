-- new for lvm (WP-9): the lvm M3 tables as computable data (no Mathlib), shared by the instance
-- (`LvmM3Inst`) and the native verifier's decision (`LvmDecideM3Real`).
import LvmFieldE

/-!
# lvm M3 tables as data

`CPoly` (monomial lists over column indices, coefficients in `Lvm.FK`), `Key` (separator, address,
value limbs), `ColSrc` (committed at an offset of `C_main`/`C_rec`, or fixed with its closed-form
extension), `Tab` (log-height, columns, constraints, reads with their count columns, seeds with their
finalize columns, degree at most two). Mathlib-free: the native verifier builds and evaluates these.
The `M3Instance` they define is `LvmM3Inst.inst`.
-/

namespace Lvm.M3

/-- A polynomial in a table's columns: monomials, each a coefficient and the column indices it
multiplies. -/
abbrev CPoly := List (FK × List Nat)

namespace CPoly

/-- The column `i`. -/
def var (i : Nat) : CPoly := [(1, [i])]

/-- The constant `c`. -/
def const (c : FK) : CPoly := [(c, [])]

/-- The value at a row of `FE` values (the native verifier's). -/
def evalE (v : Nat → FE) (P : CPoly) : FE := (P.map fun m => FE.ofK m.1 * (m.2.map v).foldl (· * ·) 1).foldl (· + ·) 0

/-- Every monomial has at most two columns. -/
def Deg2 (P : CPoly) : Prop := ∀ m ∈ P, m.2.length ≤ 2

end CPoly

/-! ## Messages -/

/-- What a read or a seed names: the memory's separator, the address, the value limbs. -/
structure Key where
  /-- The domain separator (`g^3` for `K` cells, `g^4` for `E` cells). -/
  sep : FK
  /-- The address. -/
  addr : CPoly
  /-- The value limbs (one or three). -/
  val : List CPoly

/-- The polynomials of a key have degree at most two. -/
def Key.Deg2 (k : Key) : Prop := k.addr.Deg2 ∧ ∀ P ∈ k.val, P.Deg2

/-! ## Tables -/

/-- A column: committed (an aligned block of `C_main`, or of `C_rec` when `rec`), or fixed (cell
`x` is `f x`; `ev` evaluates its multilinear extension, for the native verifier). -/
inductive ColSrc where
  | com (rec : Bool) (off : Nat)
  | fix (f : Nat → FK) (ev : List FE → FE)

/-- An lvm table. -/
structure Tab where
  /-- Log-height. -/
  τ : Nat
  /-- The columns. -/
  cols : List ColSrc
  /-- The constraints, each vanishing on every row. -/
  cons : List CPoly
  /-- The reads: a key and the read-count column. -/
  reads : List (Key × Nat)
  /-- The seeds: a key and the finalize-count column. -/
  seeds : List (Key × Nat)
  /-- Constraints and keys have degree at most two. -/
  deg : (∀ C ∈ cons, C.Deg2) ∧ (∀ r ∈ reads, r.1.Deg2) ∧ ∀ s ∈ seeds, s.1.Deg2

namespace Tab

variable (t : Tab)

/-- The width. -/
abbrev w : Nat := t.cols.length

/-- The read-count columns, those inside the width. -/
def counts : List (Fin t.w) :=
  t.reads.filterMap fun r ↦ if h : r.2 < t.w then some ⟨r.2, h⟩ else none

/-- The fixed column `i`, if column `i` is fixed. -/
def fixedOf (i : Nat) : Option (Nat → FK) :=
  match t.cols[i]? with
  | some (.fix f _) => some f
  | _ => none

end Tab

end Lvm.M3
