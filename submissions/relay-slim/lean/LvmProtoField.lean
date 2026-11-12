-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Field.lean` (formal rev 40f877dc) as `LvmProtoField` for lvm (WP-2).
import LvmFieldFacts
import LvmInnerProduct
import LvmMlBasic

/-!
# Fields for the proof system

leanVM's columns take values in `K` and its challenges in `E`, the cubic extension of `K`. This
module keeps, of leanVM's `LeanVM.Protocol.Field`:

* `Column n`, the value table of a `K`-multilinear on `n` variables;
* the equivalences `finEquivK : Fin (2^64) ≃ K` and `limbsEquiv : Vector K 3 ≃ E`;
* `card_E`: `Fintype.card E = 2^192`, the one cardinality fact every error bound rewrites with;
* `answer_eqWeight`: pairing the equality kernel with a column evaluates its extension.

lvm cut (WP-2): leanVM's VCVio `SampleableType` samplers and ArkLib's `OracleInterface` instance
on `Column`. Uniform sampling is stated directly as sums over `Fintype E` (`card_E`), and the
inner-product oracle is `Weight.pair` (`LvmInnerProduct`).
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly

section

/-! ## Columns -/

/-- A column of height `2^n`: the values of a `K`-multilinear on the cube, low bit first. A
structure rather than an abbreviation so that its oracle interface below does not overlap
ArkLib's position-query interface on `Vector`. -/
structure Column (n : ℕ) where
  /-- The value table, CompPoly's hypercube representation. -/
  values : CMlPolynomialEval K n

/-! ## Sampling -/

/-- `K` as the `2^64` bit patterns, the `BitVec` view of `Fin (2^64)`. -/
def finEquivK : Fin (2 ^ 64) ≃ K where
  toFun := fun i ↦ BF64.ofBitVec (BitVec.ofFin i)
  invFun := fun x ↦ x.toBitVec.toFin
  left_inv _ := rfl
  right_inv _ := rfl

/-- `E` as its three limbs, CompPoly's carrier view. -/
def limbsEquiv : Vector K 3 ≃ E where
  toFun := fun v ↦ CompPoly.Extension.Ext.ofVector (P := BF64.ext3Params) v
  invFun := fun x ↦ CompPoly.Extension.Ext.coeffs (P := BF64.ext3Params) x
  left_inv _ := rfl
  right_inv _ := rfl

/-- `|E| = 2^192`: the size of the challenge space in every error bound. -/
theorem card_E : Fintype.card E = 2 ^ 192 := BF64.card_ext3

/-! ## The inner-product oracle -/

/-- The answer to the equality kernel at `p` is the column's extension at `p`. -/
theorem answer_eqWeight {n : ℕ} (q : Column n) (p : Vector E n) :
    (eqWeight p).pair (algebraMap K E) q.values =
      CMlPolynomialEval.eval₂Mle q.values (algebraMap K E) p :=
  Weight.pair_eqWeight (algebraMap K E) p q.values

end
end LeanVM.Protocol
