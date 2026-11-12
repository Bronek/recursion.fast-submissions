-- Ported from `rf-pcs` `submissions/spartan-srom/lean/SpartanSromFieldExtCorrect.lean` (branch v4/flock-pcs, last changed at
-- f07d028c), renamed `SpartanSrom.F` → `Lvm.FK`, `SpartanSrom.EF` → `Lvm.FE`. Spartan-srom's file was ported from
-- v3 `spartan-chain` to the v4 contract.
import LvmFieldE
import LvmFieldKCorrect
import CompPoly.Fields.Binary.BF64.Ext3

/-!
# `FE` agrees with CompPoly's `BF64.Ext3`

`toExt3 : FE → BF64.Ext3` sends `⟨c₀, c₁, c₂⟩` to the coefficient vector
`#v[toBF64 c₀, toBF64 c₁, toBF64 c₂]`. It is a bijection (`equivExt3`) that commutes with every
operation, and `FE` is a field through it.

## Main statements

* `toExt3_add`, `toExt3_mul`, `toExt3_sq`, `toExt3_inv`: the operations are `Ext3`'s.
* `ringEquivExt3 : FE ≃+* BF64.Ext3`.
* `instField`: `FE` is a field, with computable operations.
* `card_FE`: every enumeration of `FE` has `2 ^ 192` elements.
* `toBytes_eq`: the encoding is the three `ByteCodec BF64` encodings concatenated, which is
  CompPoly's `ByteCodec (Ext P)` (`CompPoly.Fields.Extension.Bytes`, outside the import
  allowlist, so stated here through `BF64`'s codec).

## How the product is proved

Every `Ext3` element is `c₀ + c₁ g + c₂ g^2` with `g = BF64.ext3Gen` and `g^3 = g + 1`
(`toExt3_eq`, CompPoly's `ext3Gen_pow_three`). Each law is then a polynomial identity in the
coefficients modulo `g^3 = g + 1` and `2 = 0`, closed by `linear_combination` and the
characteristic-two normalisation `ring_nf; simp only [ofNat_char_two]; norm_num`. The inverse is `w * det⁻¹` with `x * w = det`
(`mul_adj`); `det ≠ 0` for `x ≠ 0` because `det` is multiplicative (`norm_mul`) and `x` has an
inverse in the field `Ext3`.
-/

namespace Lvm.FE

open CompPoly.Extension FK

/-- A numeral in characteristic two is its parity. -/
private theorem ofNat_char_two {R : Type*} [CommRing R] [CharP R 2] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : R) = ((n % 2 : ℕ) : R) := by
  rw [← CharP.cast_eq_mod R 2 n]; rfl

/-! ## The map to `Ext3` -/

/-- The `Ext3` element with the same coefficients. -/
def toExt3 (x : FE) : BF64.Ext3 := Ext.ofVector #v[toBF64 x.c₀, toBF64 x.c₁, toBF64 x.c₂]

/-- The `FE` element with the same coefficients. -/
def ofExt3 (z : BF64.Ext3) : FE :=
  ⟨ofBF64 (Ext.coeff z ⟨0, by decide⟩), ofBF64 (Ext.coeff z ⟨1, by decide⟩),
    ofBF64 (Ext.coeff z ⟨2, by decide⟩)⟩

@[simp] theorem ofExt3_toExt3 (x : FE) : ofExt3 (toExt3 x) = x := rfl

@[simp] theorem toExt3_ofExt3 (z : BF64.Ext3) : toExt3 (ofExt3 z) = z := by
  ext ⟨i, hi⟩
  change i < 3 at hi
  interval_cases i <;> rfl

/-- `FE` and `Ext3` are in bijection by their common coefficients. -/
def equivExt3 : FE ≃ BF64.Ext3 where
  toFun := toExt3
  invFun := ofExt3
  left_inv := ofExt3_toExt3
  right_inv := toExt3_ofExt3

theorem toExt3_injective : Function.Injective toExt3 := equivExt3.injective

theorem toExt3_inj {x y : FE} : toExt3 x = toExt3 y ↔ x = y := toExt3_injective.eq_iff

/-! ## Coordinates in the basis `1, g, g^2` (proof helpers) -/

local notation "C" => algebraMap BF64 BF64.Ext3
local notation "g" => BF64.ext3Gen

/-- Every element is `c₀ + c₁ g + c₂ g^2`. -/
theorem toExt3_eq (x : FE) :
    toExt3 x = C (toBF64 x.c₀) + C (toBF64 x.c₁) * g + C (toBF64 x.c₂) * g ^ 2 := by
  apply Ext.toQuot_injective
  simp only [Ext.algebraMap_eq_ofBase, Ext.toQuot_add, Ext.toQuot_mul, Ext.toQuot_pow,
    Ext.toQuot_ofBase, BF64.toQuot_ext3Gen]
  rw [Ext.toQuot]
  change (∑ i : Fin 3, _) = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  have h0 : Ext.coeff (toExt3 x) (0 : Fin 3) = toBF64 x.c₀ := rfl
  have h1 : Ext.coeff (toExt3 x) (Fin.succ (0 : Fin 2)) = toBF64 x.c₁ := rfl
  have h2 : Ext.coeff (toExt3 x) (Fin.succ (Fin.succ (0 : Fin 1))) = toBF64 x.c₂ := rfl
  rw [h0, h1, h2]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one, zero_add, pow_one]
  ring

private theorem g_cube : g ^ 3 = g + 1 := BF64.ext3Gen_pow_three


/-! ## Coefficients of the operations (proof helpers) -/

@[simp] private theorem c_zero : (0 : FE).c₀ = 0 ∧ (0 : FE).c₁ = 0 ∧ (0 : FE).c₂ = 0 :=
  ⟨rfl, rfl, rfl⟩

@[simp] private theorem c_one : (1 : FE).c₀ = 1 ∧ (1 : FE).c₁ = 0 ∧ (1 : FE).c₂ = 0 :=
  ⟨rfl, rfl, rfl⟩

private theorem add_def (x y : FE) : x + y = ⟨x.c₀ + y.c₀, x.c₁ + y.c₁, x.c₂ + y.c₂⟩ := rfl

private theorem mul_def (x y : FE) : x * y =
    ⟨x.c₀ * y.c₀ + (x.c₁ + x.c₂) * (y.c₁ + y.c₂) + x.c₁ * y.c₁ + x.c₂ * y.c₂,
      (x.c₀ + x.c₁) * (y.c₀ + y.c₁) + x.c₀ * y.c₀ + (x.c₁ + x.c₂) * (y.c₁ + y.c₂),
      (x.c₀ + x.c₂) * (y.c₀ + y.c₂) + x.c₀ * y.c₀ + x.c₁ * y.c₁⟩ := rfl

/-! ## The operations are `Ext3`'s -/

@[simp] theorem toExt3_zero : toExt3 0 = 0 := by
  rw [toExt3_eq]
  change C (toBF64 0) + C (toBF64 0) * g + C (toBF64 0) * g ^ 2 = 0
  simp

@[simp] theorem toExt3_one : toExt3 1 = 1 := by
  rw [toExt3_eq]
  change C (toBF64 1) + C (toBF64 0) * g + C (toBF64 0) * g ^ 2 = 1
  simp

/-- **Addition is `Ext3`'s.** -/
@[simp] theorem toExt3_add (x y : FE) : toExt3 (x + y) = toExt3 x + toExt3 y := by
  rw [toExt3_eq, toExt3_eq x, toExt3_eq y, add_def]
  simp only [toBF64_add, map_add]
  ring

@[simp] theorem toExt3_neg (x : FE) : toExt3 (-x) = -toExt3 x := by
  change toExt3 x = _
  rw [eq_neg_iff_add_eq_zero, ← toExt3_add]
  rw [← toExt3_zero]
  congr 1
  rw [add_def]
  cases x
  simp only [CharTwo.add_self_eq_zero]
  rfl

/-- **Multiplication is `Ext3`'s.** -/
@[simp] theorem toExt3_mul (x y : FE) : toExt3 (x * y) = toExt3 x * toExt3 y := by
  rw [toExt3_eq, toExt3_eq x, toExt3_eq y, mul_def]
  simp only [toBF64_add, toBF64_mul, map_add, map_mul]
  linear_combination (norm := (ring_nf; simp only [ofNat_char_two]; norm_num))
    (C (toBF64 x.c₁) * C (toBF64 y.c₂) + C (toBF64 x.c₂) * C (toBF64 y.c₁) +
      C (toBF64 x.c₂) * C (toBF64 y.c₂) * g) * g_cube

@[simp] theorem toExt3_sub (x y : FE) : toExt3 (x - y) = toExt3 x - toExt3 y := by
  change toExt3 (x + y) = _
  rw [toExt3_add, sub_eq_add_neg, ← toExt3_neg]
  rfl

/-- **Squaring is `Ext3`'s.** -/
@[simp] theorem toExt3_sq (x : FE) : toExt3 (sq x) = toExt3 x * toExt3 x := by
  rw [toExt3_eq, toExt3_eq x]
  change C (toBF64 (FK.sq x.c₀)) + C (toBF64 (FK.sq x.c₂)) * g +
    C (toBF64 (FK.sq x.c₁ + FK.sq x.c₂)) * g ^ 2 = _
  simp only [toBF64_add, toBF64_sq, map_add, map_mul]
  linear_combination (norm := (ring_nf; simp only [ofNat_char_two]; norm_num))
    (C (toBF64 x.c₁) * C (toBF64 x.c₂) * 2 + C (toBF64 x.c₂) * C (toBF64 x.c₂) * g) * g_cube

/-- Multiplication by a base field element is the `algebraMap` product. -/
@[simp] theorem toExt3_smulBase (c : FK) (x : FE) :
    toExt3 (smulBase c x) = C (toBF64 c) * toExt3 x := by
  rw [toExt3_eq, toExt3_eq x]
  change C (toBF64 (c * x.c₀)) + C (toBF64 (c * x.c₁)) * g + C (toBF64 (c * x.c₂)) * g ^ 2 = _
  simp only [toBF64_mul, map_mul]
  ring

/-- The base field embedding. -/
@[simp] theorem toExt3_ofK (c : FK) : toExt3 (ofK c) = C (toBF64 c) := by
  rw [toExt3_eq]
  change C (toBF64 c) + C (toBF64 0) * g + C (toBF64 0) * g ^ 2 = _
  simp

/-! ## The inverse -/

/-- The determinant of `x`, as a `BF64` polynomial in the coefficients. -/
private theorem toBF64_normOf (x : FE) : toBF64 (normOf x (adj x)) =
    toBF64 x.c₀ * (toBF64 x.c₀ * toBF64 x.c₀ + toBF64 x.c₁ * toBF64 x.c₁ +
      toBF64 x.c₂ * toBF64 x.c₂ + toBF64 x.c₁ * toBF64 x.c₂) +
    toBF64 x.c₂ * (toBF64 x.c₀ * toBF64 x.c₁ + toBF64 x.c₂ * toBF64 x.c₂) +
    toBF64 x.c₁ * (toBF64 x.c₁ * toBF64 x.c₁ + toBF64 x.c₀ * toBF64 x.c₂ +
      toBF64 x.c₂ * toBF64 x.c₂) := by
  simp only [normOf, adj, toBF64_add, toBF64_mul, toBF64_sq]

/-- **The adjugate column**: `x * adj x` is the base field element `normOf x (adj x)`. -/
theorem mul_adj (x : FE) : toExt3 x * toExt3 (adj x) = C (toBF64 (normOf x (adj x))) := by
  rw [toBF64_normOf, toExt3_eq, toExt3_eq (adj x)]
  change _ * (C (toBF64 (FK.sq x.c₀ + FK.sq x.c₁ + FK.sq x.c₂ + x.c₁ * x.c₂)) +
    C (toBF64 (x.c₀ * x.c₁ + FK.sq x.c₂)) * g +
    C (toBF64 (FK.sq x.c₁ + x.c₀ * x.c₂ + FK.sq x.c₂)) * g ^ 2) = _
  simp only [toBF64_add, toBF64_mul, toBF64_sq, map_add, map_mul]
  set a0 := C (toBF64 x.c₀)
  set a1 := C (toBF64 x.c₁)
  set a2 := C (toBF64 x.c₂)
  linear_combination (norm := (ring_nf; simp only [ofNat_char_two]; norm_num))
    (a1 * (a1 * a1 + a0 * a2 + a2 * a2) + a2 * (a0 * a1 + a2 * a2) +
      a2 * (a1 * a1 + a0 * a2 + a2 * a2) * g) * g_cube

/-- The determinant is multiplicative. -/
private theorem norm_mul (x y : FE) :
    toBF64 (normOf (x * y) (adj (x * y))) =
      toBF64 (normOf x (adj x)) * toBF64 (normOf y (adj y)) := by
  simp only [toBF64_normOf, mul_def, toBF64_add, toBF64_mul]
  ring_nf
  simp only [ofNat_char_two]
  norm_num

/-- The determinant of a nonzero element is nonzero. -/
private theorem norm_ne_zero {x : FE} (hx : x ≠ 0) : toBF64 (normOf x (adj x)) ≠ 0 := by
  have hX : toExt3 x ≠ 0 := fun h => hx (toExt3_injective (h.trans toExt3_zero.symm))
  set y := ofExt3 (toExt3 x)⁻¹
  have hxy : x * y = 1 := toExt3_injective (by
    rw [toExt3_mul, toExt3_ofExt3, mul_inv_cancel₀ hX, toExt3_one])
  have h1 : toBF64 (normOf (1 : FE) (adj 1)) = 1 := by
    rw [toBF64_normOf]
    simp only [c_one, toBF64_one, toBF64_zero]
    ring
  intro h
  have := norm_mul x y
  rw [hxy, h1, h, zero_mul] at this
  exact one_ne_zero this

/-- **The inverse is `Ext3`'s.** -/
@[simp] theorem toExt3_inv (x : FE) : toExt3 x⁻¹ = (toExt3 x)⁻¹ := by
  change toExt3 (smulBase (normOf x (adj x))⁻¹ (adj x)) = _
  rw [toExt3_smulBase, toBF64_inv]
  by_cases hx : x = 0
  · subst hx
    have : toBF64 (normOf (0 : FE) (adj 0)) = 0 := by
      rw [toBF64_normOf]
      simp only [c_zero, toBF64_zero]
      ring
    rw [this, inv_zero, map_zero, zero_mul, toExt3_zero, inv_zero]
  · refine eq_inv_of_mul_eq_one_right ?_
    rw [mul_left_comm, mul_adj, ← map_mul, inv_mul_cancel₀ (norm_ne_zero hx), map_one]

/-! ## The field structure, transported from `Ext3` -/

instance : SMul ℕ FE := ⟨nsmulRec⟩
instance : SMul ℤ FE := ⟨zsmulRec nsmulRec⟩
instance : NatCast FE := ⟨fun n => ofK (n : FK)⟩
instance : IntCast FE := ⟨fun n => ofK (n : FK)⟩

@[simp] theorem toExt3_natCast (n : ℕ) : toExt3 (n : FE) = (n : BF64.Ext3) := by
  change toExt3 (ofK (n : FK)) = _
  rw [toExt3_ofK, toBF64_natCast, map_natCast]

@[simp] theorem toExt3_intCast (n : ℤ) : toExt3 (n : FE) = (n : BF64.Ext3) := by
  change toExt3 (ofK (n : FK)) = _
  rw [toExt3_ofK, toBF64_intCast, map_intCast]

theorem toExt3_nsmul (n : ℕ) (x : FE) : toExt3 (n • x) = n • toExt3 x := by
  change toExt3 (nsmulRec n x) = _
  induction n with
  | zero => simp [nsmulRec]
  | succ n ih => rw [nsmulRec, toExt3_add, ih, succ_nsmul]

theorem toExt3_zsmul (n : ℤ) (x : FE) : toExt3 (n • x) = n • toExt3 x := by
  rcases n with n | n
  · exact (toExt3_nsmul n x).trans (natCast_zsmul _ _).symm
  · change toExt3 (-(nsmulRec (n + 1) x)) = _
    rw [toExt3_neg, negSucc_zsmul]
    exact congrArg _ (toExt3_nsmul (n + 1) x)

theorem toExt3_powGo (k : ℕ) (b : FE) (e : ℕ) (acc : FE) (he : e ≤ k) :
    toExt3 (powGo k b e acc) = toExt3 acc * toExt3 b ^ e := by
  induction k generalizing b e acc with
  | zero => obtain rfl : e = 0 := by omega
            simp [powGo]
  | succ k ih =>
    rw [powGo]
    split_ifs with h0 ho
    · simp [h0]
    · rw [ih _ _ _ (by omega)]; simp only [toExt3_mul, toExt3_sq]
      conv_rhs => rw [show e = 2 * (e / 2) + 1 by omega, pow_succ, pow_mul, _root_.sq]
      ring
    · rw [ih _ _ _ (by omega), toExt3_sq]
      conv_rhs => rw [show e = 2 * (e / 2) by omega, pow_mul, _root_.sq]

theorem toExt3_npow (x : FE) (n : ℕ) : toExt3 (x ^ n) = toExt3 x ^ n := by
  change toExt3 (powGo n x n 1) = _
  rw [toExt3_powGo n x n 1 le_rfl, toExt3_one, one_mul]

instance instCommRing : CommRing FE where
  add_assoc a b c := toExt3_injective (by simp only [toExt3_add, add_assoc])
  zero_add a := toExt3_injective (by simp only [toExt3_add, toExt3_zero, zero_add])
  add_zero a := toExt3_injective (by simp only [toExt3_add, toExt3_zero, add_zero])
  add_comm a b := toExt3_injective (by simp only [toExt3_add, add_comm])
  neg_add_cancel a :=
    toExt3_injective (by simp only [toExt3_add, toExt3_neg, toExt3_zero, neg_add_cancel])
  sub_eq_add_neg a b :=
    toExt3_injective (by simp only [toExt3_sub, toExt3_add, toExt3_neg, sub_eq_add_neg])
  nsmul n a := n • a
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  zsmul n a := n • a
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl
  left_distrib a b c := toExt3_injective (by simp only [toExt3_mul, toExt3_add, mul_add])
  right_distrib a b c := toExt3_injective (by simp only [toExt3_mul, toExt3_add, add_mul])
  zero_mul a := toExt3_injective (by simp only [toExt3_mul, toExt3_zero, zero_mul])
  mul_zero a := toExt3_injective (by simp only [toExt3_mul, toExt3_zero, mul_zero])
  mul_assoc a b c := toExt3_injective (by simp only [toExt3_mul, mul_assoc])
  one_mul a := toExt3_injective (by simp only [toExt3_mul, toExt3_one, one_mul])
  mul_one a := toExt3_injective (by simp only [toExt3_mul, toExt3_one, mul_one])
  mul_comm a b := toExt3_injective (by simp only [toExt3_mul, mul_comm])
  npow n a := a ^ n
  npow_zero a := toExt3_injective (by simp only [toExt3_npow, toExt3_one, pow_zero])
  npow_succ n a := toExt3_injective (by simp only [toExt3_npow, toExt3_mul, pow_succ])
  natCast n := (n : FE)
  natCast_zero := toExt3_injective (by simp only [toExt3_natCast, toExt3_zero, Nat.cast_zero])
  natCast_succ n := toExt3_injective
    (by simp only [toExt3_natCast, toExt3_add, toExt3_one, Nat.cast_succ])
  intCast n := (n : FE)
  intCast_ofNat n := toExt3_injective (by simp only [toExt3_intCast, toExt3_natCast,
    Int.cast_natCast])
  intCast_negSucc n := toExt3_injective (by simp only [toExt3_intCast, toExt3_neg,
    toExt3_natCast, Int.cast_negSucc])

instance : Div FE := ⟨fun x y => x * y⁻¹⟩

private theorem mul_inv_cancel_ (x : FE) (h : x ≠ 0) : x * x⁻¹ = 1 := by
  apply toExt3_injective
  rw [toExt3_mul, toExt3_inv, toExt3_one]
  have hX : toExt3 x ≠ 0 := fun h' => h (toExt3_injective (h'.trans toExt3_zero.symm))
  exact Ext.mul_inv_cancel' hX

private theorem inv_zero_ : (0 : FE)⁻¹ = 0 := by
  apply toExt3_injective
  rw [toExt3_inv, toExt3_zero, inv_zero]

/-- **`FE` is a field**, with the word-level operations. -/
instance instField : Field FE where
  inv := inv
  div x y := x * y⁻¹
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := mul_inv_cancel_
  inv_zero := inv_zero_
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- `toExt3` as a ring isomorphism. -/
def ringEquivExt3 : FE ≃+* BF64.Ext3 where
  toEquiv := equivExt3
  map_mul' := toExt3_mul
  map_add' := toExt3_add

@[simp] theorem ringEquivExt3_apply (x : FE) : ringEquivExt3 x = toExt3 x := rfl

@[simp] theorem toExt3_div (x y : FE) : toExt3 (x / y) = toExt3 x / toExt3 y := by
  change toExt3 (x * y⁻¹) = _
  rw [toExt3_mul, toExt3_inv, div_eq_mul_inv]

/-- `ofK` is the embedding of `FK` into `FE`, `algebraMap` on the `CompPoly` side. -/
def ofKRingHom : FK →+* FE where
  toFun := ofK
  map_one' := rfl
  map_mul' a b := toExt3_injective (by simp only [toExt3_ofK, toExt3_mul, toBF64_mul, map_mul])
  map_zero' := rfl
  map_add' a b := toExt3_injective (by simp only [toExt3_ofK, toExt3_add, toBF64_add, map_add])

/-- `FE` is an `FK`-algebra by `ofK`. -/
instance instAlgebra : Algebra FK FE := ofKRingHom.toAlgebra

theorem algebraMap_eq_ofK (c : FK) : algebraMap FK FE c = ofK c := rfl

theorem smulBase_eq_mul (c : FK) (x : FE) : smulBase c x = ofK c * x :=
  toExt3_injective (by rw [toExt3_smulBase, toExt3_mul, toExt3_ofK])

instance : CharP FE 2 where
  cast_eq_zero_iff n := by
    rw [← toExt3_inj, toExt3_natCast, toExt3_zero]
    exact CharP.cast_eq_zero_iff BF64.Ext3 2 n

/-! ## Cardinality -/

instance : Finite FE := Finite.of_equiv BF64.Ext3 equivExt3.symm

/-- `FE` has `2 ^ 192` elements. -/
theorem nat_card_FE : Nat.card FE = 2 ^ 192 := by
  rw [Nat.card_congr equivExt3, BF64.nat_card_ext3]

/-- An enumeration of `FE`, for statements that need one; noncomputable on purpose, as for
`FK`. -/
noncomputable instance : Fintype FE := Fintype.ofFinite FE

/-- Every enumeration of `FE` has `2 ^ 192` elements. -/
theorem card_FE [Fintype FE] : Fintype.card FE = 2 ^ 192 := by
  rw [← Nat.card_eq_fintype_card, nat_card_FE]

/-! ## Frobenius powers and the bases `1, y^(2^k), y^(2^(k+1))` -/

theorem sq_eq_mul (x : FE) : sq x = x * x :=
  toExt3_injective (by rw [toExt3_sq, toExt3_mul])

/-- `frob k` is the `2 ^ k`-th power. -/
theorem frob_eq_pow (k : ℕ) (x : FE) : frob k x = x ^ (2 ^ k) := by
  induction k generalizing x with
  | zero => simp [frob]
  | succ k ih => rw [frob, ih, sq_eq_mul, ← _root_.sq, ← pow_mul, pow_succ, mul_comm]

@[simp] theorem y_c : y.c₀ = 0 ∧ y.c₁ = 1 ∧ y.c₂ = 0 := ⟨rfl, rfl, rfl⟩

/-- `y` is the adjoined root: it maps to CompPoly's `ext3Gen`. -/
theorem toExt3_y : toExt3 y = BF64.ext3Gen := by
  rw [toExt3_eq]
  simp only [y_c, toBF64_zero, toBF64_one, map_zero, map_one, zero_add, one_mul, zero_mul,
    add_zero]

theorem frob_add (m n : ℕ) (x : FE) : frob (m + n) x = frob m (frob n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, frob, ih, frob]

/-- `y` lies in `GF(8)`: `y^(2^3) = y`, so its Frobenius powers have period three. -/
theorem frob_three_y : frob 3 y = y := by decide +kernel

theorem frob_y_mod (k : ℕ) : frob k y = frob (k % 3) y := by
  conv_lhs => rw [← Nat.mod_add_div k 3, frob_add]
  congr 1
  induction k / 3 with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, Nat.add_comm, frob_add, ih, frob_three_y]

/-- The determinant of the `FK`-coordinates of `1, u, v` (as columns), expanded. -/
def det3 (u v : FE) : FK := u.c₁ * v.c₂ - u.c₂ * v.c₁

theorem det_coords (u v : FE) :
    Matrix.det !![(1 : FE).c₀, u.c₀, v.c₀; (1 : FE).c₁, u.c₁, v.c₁; (1 : FE).c₂, u.c₂, v.c₂] =
      det3 u v := by
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, c_one, det3]
  ring

/-- **For every `k < 64`, `1, y^(2^k), y^(2^(k+1))` is an `FK`-basis of `FE`**: the determinant of
their `FK`-coordinates is nonzero. Kernel-decided on the word arithmetic. -/
theorem ybasis : ∀ k < 64,
    Matrix.det !![(1 : FE).c₀, (y ^ 2 ^ k).c₀, (y ^ 2 ^ (k + 1)).c₀;
      (1 : FE).c₁, (y ^ 2 ^ k).c₁, (y ^ 2 ^ (k + 1)).c₁;
      (1 : FE).c₂, (y ^ 2 ^ k).c₂, (y ^ 2 ^ (k + 1)).c₂] ≠ 0 := by
  intro k _
  rw [det_coords, ← frob_eq_pow, ← frob_eq_pow, frob_y_mod, frob_y_mod (k + 1)]
  have h3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have e : (k + 1) % 3 = (k % 3 + 1) % 3 := by omega
  rw [e]
  generalize k % 3 = j at h3 ⊢
  interval_cases j <;> decide +kernel

/-! ## Bytes -/

/-- **The encoding is the three `BF64` encodings concatenated**, CompPoly's `ByteCodec (Ext P)`
for `Ext3`. -/
theorem toBytes_eq (x : FE) : (toBytes x).toList =
    (CompPoly.ByteCodec.toBytes (toBF64 x.c₀)).toList ++
      (CompPoly.ByteCodec.toBytes (toBF64 x.c₁)).toList ++
        (CompPoly.ByteCodec.toBytes (toBF64 x.c₂)).toList := by
  simp only [toBytes, Vector.toList_append, ← FK.toBytes_eq]

private theorem slice0 (u v w : Vector UInt8 8) :
    (Vector.ofFn fun i : Fin 8 => ((u ++ v) ++ w)[i.1]) = u := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  rw [Vector.getElem_append_left (by omega), Vector.getElem_append_left (by omega)]

private theorem slice1 (u v w : Vector UInt8 8) :
    (Vector.ofFn fun i : Fin 8 => ((u ++ v) ++ w)[8 + i.1]) = v := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  rw [Vector.getElem_append_left (by omega), Vector.getElem_append_right (by omega) (by omega)]
  congr 1; omega

private theorem slice2 (u v w : Vector UInt8 8) :
    (Vector.ofFn fun i : Fin 8 => ((u ++ v) ++ w)[16 + i.1]) = w := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  rw [Vector.getElem_append_right (by omega) (by omega)]
  congr 1; omega

/-- Decoding inverts encoding. -/
@[simp] theorem ofBytes_toBytes (x : FE) : ofBytes (toBytes x) = x := by
  simp only [FE.ofBytes, FE.toBytes, slice0, slice1, slice2, FK.ofBytes_toBytes]

/-- **The decoding is CompPoly's**, coefficient by coefficient: each eight-byte slice is read by
`CanonicalNat.ofBytesModOrder`, as CompPoly's entrywise `Ext` decoder does. -/
theorem toExt3_ofBytes (v : Vector UInt8 24) : toExt3 (ofBytes v) = Ext.ofVector
    #v[CompPoly.CanonicalNat.ofBytesModOrder (Vector.ofFn fun i : Fin 8 => v[i.1]),
      CompPoly.CanonicalNat.ofBytesModOrder (Vector.ofFn fun i : Fin 8 => v[8 + i.1]),
      CompPoly.CanonicalNat.ofBytesModOrder (Vector.ofFn fun i : Fin 8 => v[16 + i.1])] := by
  have h0 : toBF64 (ofBytes v).c₀ = CompPoly.CanonicalNat.ofBytesModOrder
      (Vector.ofFn fun i : Fin 8 => v[i.1]) := FK.ofBytes_eq _
  have h1 : toBF64 (ofBytes v).c₁ = CompPoly.CanonicalNat.ofBytesModOrder
      (Vector.ofFn fun i : Fin 8 => v[8 + i.1]) := FK.ofBytes_eq _
  have h2 : toBF64 (ofBytes v).c₂ = CompPoly.CanonicalNat.ofBytesModOrder
      (Vector.ofFn fun i : Fin 8 => v[16 + i.1]) := FK.ofBytes_eq _
  change Ext.ofVector (P := BF64.ext3Params)
    #v[toBF64 (ofBytes v).c₀, toBF64 (ofBytes v).c₁, toBF64 (ofBytes v).c₂] = _
  rw [h0, h1, h2]

/-- Encoding inverts decoding: every 24-byte string is an encoding. -/
@[simp] theorem toBytes_ofBytes (v : Vector UInt8 24) : toBytes (ofBytes v) = v := by
  apply Vector.ext
  intro i hi
  simp only [toBytes, ofBytes, FK.toBytes_ofBytes]
  by_cases h8 : i < 8
  · rw [Vector.getElem_append_left (by omega), Vector.getElem_append_left h8, Vector.getElem_ofFn]
  · by_cases h16 : i < 16
    · rw [Vector.getElem_append_left (by omega),
        Vector.getElem_append_right (by omega) (by omega), Vector.getElem_ofFn]
      congr 1; dsimp only; omega
    · rw [Vector.getElem_append_right (by omega) (by omega), Vector.getElem_ofFn]
      congr 1; dsimp only; omega

end Lvm.FE
