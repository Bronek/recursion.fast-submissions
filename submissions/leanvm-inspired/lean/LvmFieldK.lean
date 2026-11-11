-- Ported from `rf-k` `submissions/flock-recursive/lean/FRFieldBase.lean` (branch kk/base at 8bff272b),
-- renamed `FR.B64` → `Lvm.FK`; `beta`, `mulBeta` (FR's GF(2^128) constant) dropped. FR's file is a copy of
-- spartan-srom's `SpartanSromFieldBase.lean` with the 64 × 64 product factored out as `clmul64`.

/-!
# `GF(2^64)` on machine words

`FK` is `GF(2)[x] / (x^64 + x^4 + x^3 + x + 1)` stored in one `UInt64`, bit `i` the coefficient of
`x^i`: the polynomial basis and bit order of CompPoly's `BF64` (`CompPoly.Fields.Binary.BF64`,
CompPoly `572f997`). `BF64` stores a `BitVec 64`, whose compiled code is `Nat` arithmetic; `FK`
stores the same bits in a `UInt64`, so its compiled code is word arithmetic.

* Addition is `xor`.
* Multiplication is a carry-less product giving 128 bits in two words, followed by a fold of the
  high word by `x^64 = x^4 + x^3 + x + 1` (`reduce`). The product is Karatsuba over the 32-bit
  halves: three products of words below `2^32` (`clmul32`), each sixteen integer products of the
  operands split into the four classes of bit positions modulo 4, whose column sums (at most 8)
  never carry into the next position of the same class. v3's 64-step shift-and-add loop
  (`mulLoop`) is kept as the reference; the product is equal to it (`mul_eq_mulLoop`).
* Squaring spreads the bits of the input (bit `i` to bit `2 i`, by five mask-and-shift steps) and
  reduces.
* Inversion is CompPoly's Itoh-Tsujii addition chain, with `0⁻¹ = 0`.
* Bytes are the eight little-endian bytes of the word, CompPoly's `ByteCodec BF64`.

The agreement with `BF64` is in `LvmFieldKCorrect`.
-/

namespace Lvm

/-- An element of `GF(2^64)`: bit `i` of `val` is the coefficient of `x^i`. -/
structure FK where
  /-- The polynomial-basis word. -/
  val : UInt64
  deriving DecidableEq, Inhabited, Hashable

namespace FK

instance : BEq FK := ⟨fun a b => a.val == b.val⟩

/-- `==` is equality (review S-A-m1). -/
instance : LawfulBEq FK where
  eq_of_beq {a b} h := by
    cases a; cases b
    exact congrArg FK.mk (eq_of_beq (α := UInt64) h)
  rfl {a} := beq_self_eq_true (α := UInt64) a.val

instance : Repr FK := ⟨fun a _ => repr a.val⟩

/-- Zero. -/
instance : Zero FK := ⟨⟨0⟩⟩
/-- One: the constant polynomial. -/
instance : One FK := ⟨⟨1⟩⟩

/-- Addition, subtraction and negation are coefficientwise `xor` in characteristic two. -/
@[inline] def add (a b : FK) : FK := ⟨a.val ^^^ b.val⟩

instance : Add FK := ⟨add⟩
instance : Sub FK := ⟨add⟩
instance : Neg FK := ⟨fun a => a⟩

/-! ## Multiplication -/

/-- The state of the shift-and-add product: the multiplier bits `a` still to read, the
multiplicand times the current power of `x` as the 128-bit `(bl, bh)`, and the 128-bit
accumulator `(lo, hi)`. -/
structure MulState where
  /-- The multiplier, shifted so that its bit `0` is the next bit to read. -/
  a : UInt64
  /-- The low word of the shifted multiplicand. -/
  bl : UInt64
  /-- The high word of the shifted multiplicand. -/
  bh : UInt64
  /-- The low word of the accumulator. -/
  lo : UInt64
  /-- The high word of the accumulator. -/
  hi : UInt64

/-- One bit of the product: add the multiplicand to the accumulator if bit `0` of `a` is set
(branch-free, by the mask `0 - (a &&& 1)`), then shift `a` right and the multiplicand left. -/
@[inline] def mulStep (s : MulState) : MulState :=
  let m := (0 : UInt64) - (s.a &&& 1)
  ⟨s.a >>> 1, s.bl <<< 1, (s.bh <<< 1) ^^^ (s.bl >>> 63), s.lo ^^^ (s.bl &&& m),
    s.hi ^^^ (s.bh &&& m)⟩

/-- Reduce the 128-bit value `hi * x^64 + lo` modulo `x^64 + x^4 + x^3 + x + 1`.

`hi * x^64 = hi * (x^4 + x^3 + x + 1)`, whose bits above 63 are the word
`c = (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)`, below `2^4`; folding `c` once more stays below
`2^8`. Both folds are one multiplication of `d = hi ^^^ c` by `x^4 + x^3 + x + 1`, truncated. -/
@[inline] def reduce (lo hi : UInt64) : UInt64 :=
  let d := hi ^^^ (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  lo ^^^ d ^^^ (d <<< 1) ^^^ (d <<< 3) ^^^ (d <<< 4)

/-- The carry-less product loop, four bits per round (`n` rounds), ending in `reduce` (v3's
multiplication, `16` rounds; kept as the reference of `mul`). The state is passed as five words,
so the compiled loop allocates nothing. -/
def mulLoop : Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, _, lo, hi => reduce lo hi
  | n + 1, a, bl, bh, lo, hi =>
    let s := mulStep (mulStep (mulStep (mulStep ⟨a, bl, bh, lo, hi⟩)))
    mulLoop n s.a s.bl s.bh s.lo s.hi

/-- The carry-less product of two words below `2^32` (a word below `2^63`): the operands split
into the bits at positions `≡ r (mod 4)`, `r < 4`; the integer product of the class-`r` part of
`x` and the class-`s` part of `y` has, at the positions of class `r + s`, the carry-less product's
bits (each column adds at most eight bits, so its sum fits in the four positions up to the next
one of its class). -/
@[inline] def clmul32 (x y : UInt64) : UInt64 :=
  let x0 := x &&& 0x11111111
  let x1 := x &&& 0x22222222
  let x2 := x &&& 0x44444444
  let x3 := x &&& 0x88888888
  let y0 := y &&& 0x11111111
  let y1 := y &&& 0x22222222
  let y2 := y &&& 0x44444444
  let y3 := y &&& 0x88888888
  (((x0 * y0) ^^^ (x1 * y3) ^^^ (x2 * y2) ^^^ (x3 * y1)) &&& 0x1111111111111111) |||
    (((x0 * y1) ^^^ (x1 * y0) ^^^ (x2 * y3) ^^^ (x3 * y2)) &&& 0x2222222222222222) |||
    (((x0 * y2) ^^^ (x1 * y1) ^^^ (x2 * y0) ^^^ (x3 * y3)) &&& 0x4444444444444444) |||
    (((x0 * y3) ^^^ (x1 * y2) ^^^ (x2 * y1) ^^^ (x3 * y0)) &&& 0x8888888888888888)

/-- A 128-bit value as two words, `lo + x^64 hi`. -/
structure U128 where
  /-- The low word. -/
  lo : UInt64
  /-- The high word. -/
  hi : UInt64

/-- The carry-less product of two words, `lo + x^64 hi`: Karatsuba over their 32-bit halves
(three `clmul32`), unreduced. -/
@[inline] def clmul64 (a b : UInt64) : U128 :=
  let a0 := a &&& 0xFFFFFFFF
  let a1 := a >>> 32
  let b0 := b &&& 0xFFFFFFFF
  let b1 := b >>> 32
  let p0 := clmul32 a0 b0
  let p2 := clmul32 a1 b1
  let pm := clmul32 (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p2
  ⟨p0 ^^^ (pm <<< 32), p2 ^^^ (pm >>> 32)⟩

/-- Multiplication: the carry-less product of the words (`clmul64`), reduced. -/
def mul (a b : FK) : FK :=
  let p := clmul64 a.val b.val
  ⟨reduce p.lo p.hi⟩

instance : Mul FK := ⟨mul⟩

/-- Spread the low 32 bits of `x`: bit `i` goes to bit `2 i`, the other bits are `0`. -/
@[inline] def spread (x : UInt64) : UInt64 :=
  let x := x &&& 0x00000000FFFFFFFF
  let x := (x ||| (x <<< 16)) &&& 0x0000FFFF0000FFFF
  let x := (x ||| (x <<< 8)) &&& 0x00FF00FF00FF00FF
  let x := (x ||| (x <<< 4)) &&& 0x0F0F0F0F0F0F0F0F
  let x := (x ||| (x <<< 2)) &&& 0x3333333333333333
  (x ||| (x <<< 1)) &&& 0x5555555555555555

/-- Squaring: in characteristic two the carry-less square spreads the bits, so the low word
spreads the low half of `a` and the high word the high half. -/
@[inline] def sq (a : FK) : FK := ⟨reduce (spread a.val) (spread (a.val >>> 32))⟩

/-- The Frobenius power `a ^ (2 ^ k)`, by `k` squarings. -/
def frob : Nat → FK → FK
  | 0, a => a
  | k + 1, a => frob k (sq a)

/-- The multiplicative inverse by CompPoly's Itoh-Tsujii chain (`BF64.invItohTsujii`):
`a⁻¹ = (a ^ (2 ^ 63 - 1)) ^ 2`, with `a ^ (2 ^ k - 1)` along `1, 2, 3, 6, 7, 14, 15, 30, 31, 62,
63`, and `0⁻¹ = 0`. -/
def inv (a : FK) : FK :=
  if a.val = 0 then 0 else
    let u1 := a
    let u2 := frob 1 u1 * u1
    let u3 := frob 1 u2 * u1
    let u6 := frob 3 u3 * u3
    let u7 := frob 1 u6 * u1
    let u14 := frob 7 u7 * u7
    let u15 := frob 1 u14 * u1
    let u30 := frob 15 u15 * u15
    let u31 := frob 1 u30 * u1
    let u62 := frob 31 u31 * u31
    let u63 := frob 1 u62 * u1
    sq u63

instance : Inv FK := ⟨inv⟩

/-- Square-and-multiply: `powGo k b e acc = acc * b ^ e` whenever `e ≤ k`. The fuel `k` makes the
recursion structural on a natural number, so the kernel evaluates powers by peeling literals
(Mathlib's `npowBinRec` recurses through `Nat.binaryRec`, which the kernel unfolds slowly). -/
def powGo : Nat → FK → Nat → FK → FK
  | 0, _, _, acc => acc
  | k + 1, b, e, acc =>
    if e = 0 then acc else powGo k (sq b) (e / 2) (if e % 2 = 1 then acc * b else acc)

/-- Powers by repeated squaring. -/
instance : Pow FK Nat := ⟨fun a n => powGo n a n 1⟩

/-- The element with the given polynomial-basis word. -/
@[inline] def ofUInt64 (w : UInt64) : FK := ⟨w⟩

/-- The polynomial-basis word of an element. -/
@[inline] def toUInt64 (a : FK) : UInt64 := a.val

/-- The generator `x` of `FK` over `GF(2)`, the class of `x` modulo the modulus. -/
def x : FK := ⟨2⟩

/-! ## Bytes -/

/-- The eight little-endian bytes of the word, CompPoly's `ByteCodec BF64` encoding. -/
def toBytes (a : FK) : Vector UInt8 8 :=
  #v[a.val.toUInt8, (a.val >>> 8).toUInt8, (a.val >>> 16).toUInt8, (a.val >>> 24).toUInt8,
    (a.val >>> 32).toUInt8, (a.val >>> 40).toUInt8, (a.val >>> 48).toUInt8,
    (a.val >>> 56).toUInt8]

/-- The element with the given eight little-endian bytes; every byte string decodes. The shifted
bytes do not overlap, so `+` is `|||` here. -/
def ofBytes (v : Vector UInt8 8) : FK :=
  ⟨v[0].toUInt64 + (v[1].toUInt64 <<< 8) + (v[2].toUInt64 <<< 16) + (v[3].toUInt64 <<< 24) +
    (v[4].toUInt64 <<< 32) + (v[5].toUInt64 <<< 40) + (v[6].toUInt64 <<< 48) +
    (v[7].toUInt64 <<< 56)⟩

end FK

end Lvm
