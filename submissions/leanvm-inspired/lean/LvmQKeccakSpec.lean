import LvmDecideKeccak

/-!
# QA1: the structured forms the circuit computes for the Keccak GKR verifier

`F` (`LvmDecideKeccak`, leanVM's verifier) materialises a claim's `1600` position weights: after a
layer they are `Lᵀ(w)` (`keccakLinearTranspose`) of the product weights
`w(64ℓ + z) = eq(a, z)·B(ℓ)` (`a` the layer's six slice challenges, `B` its 25 batched lane weights),
and the next layer reads them in three places: the iota term (lane `0`), the final check
(`Σ_ℓ eq_L(ℓ) Σ_z eq_Z(z) W(64ℓ + z)`) and, after the last layer, the input opening
(`Σ_z W(64ℓ + z)·slice_z`). The circuit never writes the `1600` weights (WP-0: that would cost
≈ 9 k rows per layer); it keeps `(a, B)` and evaluates these through the guest's structured forms
(leanVM `crates/rec_aggregation/guests/lean_ethereum.py:2570-2700`, `keccak_shifts_eq`,
`keccak_form`), defined here:

* `rotSum u A s = Σ_{z<64} u(z)·A((z + s) mod 64)`: a slice vector against `A` rotated by `s`;
* `laneForm B R ℓ`: `Σ_z u(z)·Lᵀ(w)(64ℓ + z)` in terms of `R = rotSum u A` (θ's transpose is the
  lane plus two column sums, `ρπ` moves lanes and rotates slices): three groups of `B·R`;
* `lowTab`, `highTab`, `shiftLH`: `rotSum (eq b) (eq a) r` through the split `r = r_l + 8 r_h`
  (the guest's `keccak_shifts_eq`): two 8-entry tables for the low three bits by carry, one
  8-entry table for the high three, `shift(r) = L₀(r_l)·H(r_h) + L₁(r_l)·H(r_h + 1)`.

The equalities with `F`'s materialised forms are in `LvmQEqKeccakAlg`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm

/-- `eq(a, z)`: entry `z` of `F`'s `eqKernel a` (first coordinate the lowest bit). -/
def eqAt (a : List FE) (z : Nat) : FE := (eqKernel a).getD z 0

/-- The product weights `w(64ℓ + z) = A(z)·B(ℓ)` on the `1600` positions. -/
def prodW (A : Nat → FE) (B : List FE) : List FE :=
  (List.range keccakBits).map fun j => A (j % 64) * B.getD (j / 64) 0

/-- `Σ_{z<64} u(z)·A((z + s) mod 64)`. -/
def rotSum (u A : Nat → FE) (s : Nat) : FE := sumE ((List.range 64).map fun z => u z * A ((z + s) % 64))

/-- The rotation of lane `ℓ` (`keccakRho`). -/
def rho (l : Nat) : Nat := keccakRho.getD l 0

/-- **Lane `ℓ`'s form**: `Σ_z u(z)·Lᵀ(w)(64ℓ + z)` from `R = rotSum u A`: the lane itself, the
column `x + 1` at the same slice, the column `x − 1` one slice up (`x = ℓ mod 5`). -/
def laneForm (B : List FE) (R : Nat → FE) (l : Nat) : FE :=
  B.getD (keccakPi l) 0 * R (rho l) +
  sumE ((List.range 5).map fun y =>
    B.getD (keccakPi ((l % 5 + 1) % 5 + 5 * y)) 0 * R (rho ((l % 5 + 1) % 5 + 5 * y))) +
  sumE ((List.range 5).map fun y =>
    B.getD (keccakPi ((l % 5 + 4) % 5 + 5 * y)) 0 * R ((rho ((l % 5 + 4) % 5 + 5 * y) + 1) % 64))

/-- **The final check's weight** in the guest's grouping (`keccak_form`): `Σ_ℓ f(ℓ)·laneForm`,
the column sums shared. -/
def kForm (B : List FE) (R : Nat → FE) (f : List FE) : FE :=
  let moved (l : Nat) : FE := B.getD (keccakPi l) 0 * R (rho l)
  let movedN (l : Nat) : FE := B.getD (keccakPi l) 0 * R ((rho l + 1) % 64)
  let col (x : Nat) : FE := sumE ((List.range 5).map fun y => moved (x + 5 * y))
  let colN (x : Nat) : FE := sumE ((List.range 5).map fun y => movedN (x + 5 * y))
  let fcol (x : Nat) : FE := sumE ((List.range 5).map fun y => f.getD (x + 5 * y) 0)
  sumE ((List.range 25).map fun l => f.getD l 0 * moved l) +
    sumE ((List.range 5).map fun x => fcol x * (col ((x + 1) % 5) + colN ((x + 4) % 5)))

/-- `F`'s final-check weight on materialised weights `W`: `Σ_{ℓ<25} f(ℓ) Σ_{z<64} e(z)·W(64ℓ + z)`. -/
def weightedF (f e W : List FE) : FE :=
  sumE ((List.range 25).map fun l => f.getD l 0 * sumE ((List.range 64).map fun z => e.getD z 0 * W.getD (64 * l + z) 0))

/-! ## The rotated `eq` sum through two 8-entry tables (`keccak_shifts_eq`) -/

/-- `L_c(r_l) = Σ_{z<8, carry(z + r_l) = c} eq(b_lo, z)·eq(a_lo, (z + r_l) mod 8)`. -/
def lowTab (a b : List FE) (c rl : Nat) : FE :=
  sumE ((List.range 8).map fun z =>
    if (z + rl) / 8 = c then eqAt (b.take 3) z * eqAt (a.take 3) ((z + rl) % 8) else 0)

/-- `H(k) = Σ_{z<8} eq(b_hi, z)·eq(a_hi, (z + k) mod 8)`. -/
def highTab (a b : List FE) (k : Nat) : FE :=
  sumE ((List.range 8).map fun z => eqAt (b.drop 3) z * eqAt (a.drop 3) ((z + k) % 8))

/-- **`shift(r)` from the tables**: `L₀(r mod 8)·H(r / 8) + L₁(r mod 8)·H(r / 8 + 1)`. -/
def shiftLH (a b : List FE) (r : Nat) : FE :=
  lowTab a b 0 (r % 8) * highTab a b (r / 8) + lowTab a b 1 (r % 8) * highTab a b ((r / 8 + 1) % 8)

/-! ## The iota term -/

/-- The bit positions a round constant can use: `2^i − 1`, `i < 7`. -/
def iotaPos (i : Nat) : Nat := 2 ^ i - 1

/-- `flip_i`: the weight of slice `2^i − 1` of lane `0`, `Σ_z [z = 2^i−1]·Lᵀ(w)(z)`, as a lane form. -/
def flipForm (B : List FE) (A : Nat → FE) (i : Nat) : FE :=
  laneForm B (fun s => A ((iotaPos i + s) % 64)) 0

/-- Bit `2^i − 1` of a round constant, as `0` or `1`. -/
def rcBit (rc : UInt64) (i : Nat) : FE := if rc.toNat.testBit (iotaPos i) then 1 else 0

/-- `F`'s iota sum on a weight vector `W`: `Σ_{z ∈ bits(rc)} W(z)`. -/
def iotaF (rc : UInt64) (W : List FE) : FE :=
  sumE ((List.range 64).filterMap fun z => if rc.toNat.testBit z then some (W.getD z 0) else none)

end Lvm.Q1
