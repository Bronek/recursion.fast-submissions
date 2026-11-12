import LvmDecideKeccak
import LvmKeccakRmfeLit

/-!
# QA1: the RMFE constants as literals (`rmfeProject`, `rmfeEmbed`, kernel-checked)

Values of `ref/loopir.py` (`RMFE_PROJECT`, `RMFE_EMBED`, leanVM `keccak.rs:25-46`), equal to
`F`'s computed lists. `F`'s `rmfe` (`LvmDecideKeccak`) and the verifier language's
(`Verifier.rmfe`, `LvmVCore`) have the same definition: `rmfe_eq_V` proves them equal piece by
piece, without evaluating either, so the kernel evaluates `rmfe` once, in
`KeccakGkr.rmfeProject_eq` (`LvmKeccakRmfeLit`), and `rmfeProject_eq`, `rmfeEmbed_eq` here (and
`Lvm.VEq.rmfeProject_eq`, `rmfeEmbed_eq`) are read off it.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm LeanVM.Protocol

/-- `RMFE_PROJECT` as a literal. -/
def projLit : List Nat := [0x1, 0x7fffffffffff, 0x274e9d3a74e9, 0x1d3a74e9d3a7, 0x65cb972e5cb9, 0x5cb972e5cb97,
  0x6690aec7cd21, 0x5d8f9a42bb1f, 0x73485763e690, 0x3750967c6ea1, 0x12cf8dd4259f,
  0x1ba84b3e3750, 0x0ad0c9f715a1, 0x064fb8ad0c9f, 0x456864fb8ad0, 0x400000000000]

/-- `RMFE_EMBED` as a literal. -/
def embedLit : List Nat := [0x40c50b, 0x7f79f2, 0x4b4e0a, 0x72740c, 0x5357da, 0x1d1c9e, 0x04be6e, 0x785246,
  0x097cdc, 0x109e7e, 0x1f1454, 0x213cfc, 0x4cfcc8, 0x775770, 0x187386, 0x818a16]

/-! ## `F`'s embedding is the verifier language's, piece by piece -/

theorem bitLength_eq_V : Lvm.bitLength = Verifier.bitLength := rfl

theorem productBits_eq_V : Lvm.productBits = Verifier.productBits := rfl

theorem rmfeFactors_eq_V : Lvm.rmfeFactors = Verifier.rmfeFactors := rfl

theorem carrylessAux_eq_V : Lvm.carrylessAux = Verifier.carrylessAux := by
  funext fuel a b out
  induction fuel generalizing a b out with
  | zero => rfl
  | succ n ih => simp only [Lvm.carrylessAux, Verifier.carrylessAux, ih]

theorem carryless_eq_V : Lvm.carryless = Verifier.carryless := by
  funext a b; simp only [Lvm.carryless, Verifier.carryless, carrylessAux_eq_V]

theorem carrylessDivmodAux_eq_V : Lvm.carrylessDivmodAux = Verifier.carrylessDivmodAux := by
  funext fuel f q a
  induction fuel generalizing q a with
  | zero => rfl
  | succ n ih => simp only [Lvm.carrylessDivmodAux, Verifier.carrylessDivmodAux, ih, bitLength_eq_V]

theorem carrylessDivmod_eq_V : Lvm.carrylessDivmod = Verifier.carrylessDivmod := by
  funext a f
  simp only [Lvm.carrylessDivmod, Verifier.carrylessDivmod, carrylessDivmodAux_eq_V, bitLength_eq_V]

theorem bitParity_eq_V : Lvm.bitParity = Verifier.bitParity := by
  funext n; simp only [Lvm.bitParity, Verifier.bitParity, bitLength_eq_V]

theorem rmfeModulus_eq_V : Lvm.rmfeModulus = Verifier.rmfeModulus := by
  unfold Lvm.rmfeModulus Verifier.rmfeModulus; rw [rmfeFactors_eq_V, carryless_eq_V]; rfl

theorem rmfeFactor_eq_V : Lvm.rmfeFactor = Verifier.rmfeFactor := by
  funext m f b
  simp only [Lvm.rmfeFactor, Verifier.rmfeFactor, carryless_eq_V, carrylessDivmod_eq_V, bitParity_eq_V,
    productBits_eq_V, bitLength_eq_V]

/-- `F`'s `rmfe` is `Verifier.rmfe`. -/
theorem rmfe_eq_V : Lvm.rmfe = Verifier.rmfe := by
  unfold Lvm.rmfe Verifier.rmfe; rw [rmfeFactor_eq_V, rmfeModulus_eq_V, rmfeFactors_eq_V, productBits_eq_V]

/-! ## The literals -/

theorem rmfeProject_eq : rmfeProject = projLit :=
  (congrArg Prod.snd rmfe_eq_V).trans KeccakGkr.rmfeProject_eq

theorem rmfeEmbed_eq : rmfeEmbed = embedLit :=
  (congrArg Prod.fst rmfe_eq_V).trans KeccakGkr.rmfeEmbed_eq

end Lvm.Q1
