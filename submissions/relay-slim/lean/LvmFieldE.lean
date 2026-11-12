-- Ported from `rf-pcs` `submissions/spartan-srom/lean/SpartanSromFieldExt.lean` (branch v4/flock-pcs, last changed at
-- f07d028c), renamed `SpartanSrom.F` → `Lvm.FK`, `SpartanSrom.EF` → `Lvm.FE`. Spartan-srom's file was ported from
-- v3 `spartan-chain` to the v4 contract.
import LvmFieldK

/-!
# `GF(2^192)` as a cubic extension of `FK`

`FE` is `FK[y] / (y^3 + y + 1)` with coefficients `c₀ + c₁ y + c₂ y^2`: the modulus, the
coefficient order and the byte layout of CompPoly's `BF64.Ext3` (`ext3Params`, lower
coefficients `#v[1, 1, 0]`, CompPoly `572f997`). The operations are written out for degree three:

* addition is coefficientwise;
* multiplication is three-term Karatsuba (six `FK` products) followed by the reduction
  `y^3 = y + 1`, `y^4 = y^2 + y`;
* squaring is three `FK` squarings, since squaring is additive in characteristic two;
* inversion is the adjugate of the multiplication matrix: `x * w = det` for an explicit `w`
  quadratic in the coefficients, so `x⁻¹ = w * det⁻¹`, one inversion in `FK`;
* bytes are the three coefficient encodings concatenated (CompPoly's `ByteCodec (Ext P)`).

The agreement with `Ext3` is in `LvmFieldCorrect`.
-/

namespace Lvm

/-- An element `c₀ + c₁ y + c₂ y^2` of `FK[y] / (y^3 + y + 1)`. -/
structure FE where
  /-- The constant coefficient. -/
  c₀ : FK
  /-- The coefficient of `y`. -/
  c₁ : FK
  /-- The coefficient of `y^2`. -/
  c₂ : FK
  deriving DecidableEq, Inhabited, Hashable

namespace FE

instance : BEq FE := ⟨fun x y => x.c₀ == y.c₀ && x.c₁ == y.c₁ && x.c₂ == y.c₂⟩

instance : Repr FE := ⟨fun x _ => repr (x.c₀, x.c₁, x.c₂)⟩

instance : Zero FE := ⟨⟨0, 0, 0⟩⟩
instance : One FE := ⟨⟨1, 0, 0⟩⟩

/-- The base field element `c` as `c + 0 y + 0 y^2`. -/
@[inline] def ofK (c : FK) : FE := ⟨c, 0, 0⟩

/-- Coefficientwise addition; it is also subtraction and negation is the identity. -/
@[inline] def add (x y : FE) : FE := ⟨x.c₀ + y.c₀, x.c₁ + y.c₁, x.c₂ + y.c₂⟩

instance : Add FE := ⟨add⟩
instance : Sub FE := ⟨add⟩
instance : Neg FE := ⟨fun x => x⟩

/-- Multiplication: Karatsuba over the three coefficients, then `y^3 = y + 1`. With
`d_k = ∑_{i + j = k} x_i y_j` the unreduced product, the result is
`(d0 + d3) + (d1 + d3 + d4) y + (d2 + d4) y^2`. -/
def mul (x y : FE) : FE :=
  let m0 := x.c₀ * y.c₀
  let m1 := x.c₁ * y.c₁
  let m2 := x.c₂ * y.c₂
  let m01 := (x.c₀ + x.c₁) * (y.c₀ + y.c₁)
  let m02 := (x.c₀ + x.c₂) * (y.c₀ + y.c₂)
  let m12 := (x.c₁ + x.c₂) * (y.c₁ + y.c₂)
  ⟨m0 + m12 + m1 + m2, m01 + m0 + m12, m02 + m0 + m1⟩

instance : Mul FE := ⟨mul⟩

/-- Multiplication by a base field element: three `FK` products. -/
@[inline] def smulBase (c : FK) (x : FE) : FE := ⟨c * x.c₀, c * x.c₁, c * x.c₂⟩

/-- Squaring: `(c₀ + c₁ y + c₂ y^2)^2 = c₀^2 + c₁^2 y^2 + c₂^2 (y^2 + y)`. -/
def sq (x : FE) : FE :=
  let s2 := FK.sq x.c₂
  ⟨FK.sq x.c₀, s2, FK.sq x.c₁ + s2⟩

/-- The adjugate column `w` of `x`: `x * w` is the base field element `normOf x`. -/
@[inline] def adj (x : FE) : FE :=
  let s1 := FK.sq x.c₁
  let s2 := FK.sq x.c₂
  ⟨FK.sq x.c₀ + s1 + s2 + x.c₁ * x.c₂, x.c₀ * x.c₁ + s2, s1 + x.c₀ * x.c₂ + s2⟩

/-- The determinant of multiplication by `x`, its norm to `FK`. -/
@[inline] def normOf (x : FE) (w : FE) : FK := x.c₀ * w.c₀ + x.c₂ * w.c₁ + x.c₁ * w.c₂

/-- The inverse, `adj x * (normOf x)⁻¹`, with `0⁻¹ = 0`. -/
def inv (x : FE) : FE :=
  let w := adj x
  smulBase (normOf x w)⁻¹ w

instance : Inv FE := ⟨inv⟩

/-- Square-and-multiply: `powGo k b e acc = acc * b ^ e` whenever `e ≤ k`. The fuel `k` makes the
recursion structural on a natural number, so the kernel evaluates powers by peeling literals
(Mathlib's `npowBinRec` recurses through `Nat.binaryRec`, which the kernel unfolds slowly). -/
def powGo : Nat → FE → Nat → FE → FE
  | 0, _, _, acc => acc
  | k + 1, b, e, acc =>
    if e = 0 then acc else powGo k (sq b) (e / 2) (if e % 2 = 1 then acc * b else acc)

/-- Powers by repeated squaring. -/
instance : Pow FE Nat := ⟨fun a n => powGo n a n 1⟩

/-- The generator `y` of `FE` over `FK`, a root of `y^3 + y + 1`. -/
def y : FE := ⟨0, 1, 0⟩

/-- The Frobenius power `x ^ (2 ^ k)`, by `k` squarings. -/
def frob : Nat → FE → FE
  | 0, x => x
  | k + 1, x => frob k (sq x)

/-- The three coefficient encodings concatenated, CompPoly's `ByteCodec Ext3` layout. -/
def toBytes (x : FE) : Vector UInt8 24 :=
  (x.c₀.toBytes ++ x.c₁.toBytes) ++ x.c₂.toBytes

/-- Decode three coefficients of eight bytes each; every byte string decodes. -/
def ofBytes (v : Vector UInt8 24) : FE :=
  ⟨FK.ofBytes (Vector.ofFn fun i : Fin 8 => v[i.1]),
    FK.ofBytes (Vector.ofFn fun i : Fin 8 => v[8 + i.1]),
    FK.ofBytes (Vector.ofFn fun i : Fin 8 => v[16 + i.1])⟩

end FE

end Lvm
