-- From relay-echo (#12), `lean/FastProofChainWords.lean` (Apache-2.0), unchanged except the module names of
-- its imports.
/-
  Little-endian byte packing (`pack8`), for the chain statements of `FastSpec.lean`
  (`xorBlock_chain`, `toH4_outBytes`, `ofH4_toH4`) and the word reader of `FastSpecParse.lean`
  (`u64At_toNat`): a word's eight bytes pack back into the word, shifts by whole bytes move the
  packed bytes, and byte `i` of a packed word is its `i`-th input. Every byte and word stays
  symbolic.
-/
import WlFastDefs
import Mathlib.Tactic.IntervalCases

namespace RecursionFast.FastCheck.ChainProof
open RecursionFast Keccak

/-- Eight bytes packed into one little-endian word. -/
def pack8 (a b c d e f g h : UInt8) : UInt64 :=
  a.toUInt64 ||| b.toUInt64 <<< 8 ||| c.toUInt64 <<< 16 ||| d.toUInt64 <<< 24 |||
  e.toUInt64 <<< 32 ||| f.toUInt64 <<< 40 ||| g.toUInt64 <<< 48 ||| h.toUInt64 <<< 56

/-- Reading all eight bytes of a word and packing them recovers the word. -/
theorem pack8_bytes (w : UInt64) :
    pack8 (w >>> 0).toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8
      (w >>> 32).toUInt8 (w >>> 40).toUInt8 (w >>> 48).toUInt8 (w >>> 56).toUInt8 = w := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- Shifting a packed word left by one byte drops its last byte and puts a zero byte first. -/
theorem pack8_shl (a b c d e f g h : UInt8) :
    pack8 a b c d e f g h <<< 8 = pack8 0 a b c d e f g := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64,
    BitVec.getLsbD_or, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- Shifting a packed word right by seven bytes leaves its last byte. -/
theorem pack8_shr (a b c d e f g h : UInt8) :
    pack8 a b c d e f g h >>> 56 = h.toUInt64 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [pack8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt8.toBitVec_toUInt64, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

/-- Extracting byte `i` of a packed word recovers the corresponding input byte. -/
theorem byte_pack8 (a b c d e f g h : UInt8) (i : Nat) (hi : i < 8) :
    ((pack8 a b c d e f g h) >>> (8 * i).toUInt64).toUInt8 = (#v[a,b,c,d,e,f,g,h])[i] := by
  interval_cases i <;> apply UInt8.toBitVec_inj.mp <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  all_goals
    simp only [pack8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth]
    interval_cases j <;> simp

/-! `byte_pack8` at each of the eight byte positions, as rewrite rules. -/

theorem byte_pack8_0 (a b c d e f g h : UInt8) :
    ((pack8 a b c d e f g h) >>> 0).toUInt8 = a :=
  byte_pack8 a b c d e f g h 0 (by decide)

theorem byte_pack8_1 (a b c d e f g h : UInt8) :
    ((pack8 a b c d e f g h) >>> 8).toUInt8 = b :=
  byte_pack8 a b c d e f g h 1 (by decide)

theorem byte_pack8_2 (a b c d e f g h : UInt8) :
    ((pack8 a b c d e f g h) >>> 16).toUInt8 = c :=
  byte_pack8 a b c d e f g h 2 (by decide)

theorem byte_pack8_3 (a b c d e f g h : UInt8) :
    ((pack8 a b c d e f g h) >>> 24).toUInt8 = d :=
  byte_pack8 a b c d e f g h 3 (by decide)

theorem byte_pack8_4 (a b c d e f g h : UInt8) :
    ((pack8 a b c d e f g h) >>> 32).toUInt8 = e :=
  byte_pack8 a b c d e f g h 4 (by decide)

theorem byte_pack8_5 (a b c d e f g h : UInt8) :
    ((pack8 a b c d e f g h) >>> 40).toUInt8 = f :=
  byte_pack8 a b c d e f g h 5 (by decide)

theorem byte_pack8_6 (a b c d e f g h : UInt8) :
    ((pack8 a b c d e f g h) >>> 48).toUInt8 = g :=
  byte_pack8 a b c d e f g h 6 (by decide)

theorem byte_pack8_7 (a b c d e f g h : UInt8) :
    ((pack8 a b c d e f g h) >>> 56).toUInt8 = h :=
  byte_pack8 a b c d e f g h 7 (by decide)

end RecursionFast.FastCheck.ChainProof
