-- From relay-echo (#12), `lean/FastProofParseBytes.lean` (Apache-2.0), unchanged except the module names of
-- its imports.
/-
  Byte-level lemmas for the statements of `FastSpecParse.lean`: the library's `wordsBytes` as
  `List.flatMap` rewrites, the bytes of packed words and of a number's word, and where a field
  sits in a byte array `pre ++ mid ++ post`.

  `ParseProof.packed_bytes` and `ParseProof.word_to_bytes` are the statements
  `wordsBytes_packBytes` and `wordBytes_toWord` of `FastSpecParse.lean`, under other names:
  `FastSpecParse.lean` imports this module, so they are proved here first and the statements
  there are proved from them.
-/
import WlFastChainWords

namespace RecursionFast.FastCheck
open RecursionFast

/-- `wordsBytes` of an append is the append of `wordsBytes`. -/
theorem wordsBytes_append' (a b : List Word) :
    wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b := List.flatMap_append

/-- `wordsBytes` of a cons: the word's bytes, then the rest's. -/
theorem wordsBytes_cons' (w : Word) (ws : List Word) :
    wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws := List.flatMap_cons

/-- `wordsBytes` of no word is no byte. -/
theorem wordsBytes_nil' : wordsBytes [] = [] := rfl

namespace ParseProof

/-- The bytes of packed words are the bytes, then zeros up to a multiple of 8. -/
theorem packed_bytes (l : List UInt8) :
    wordsBytes (packBytes l) = l ++ List.replicate ((8 - l.length % 8) % 8) 0 := by
  apply List.ext_getElem
  · simp only [wordsBytes_length, packBytes_length, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    rw [← List.getD_eq_getElem _ 0 hi, ← wordByte_eq_getD, wordByte_packBytes]
    by_cases h : i < l.length
    · rw [List.getElem_append_left h, List.getD_eq_getElem _ _ h]
    · rw [List.getD_eq_default _ _ (by omega), List.getElem_append_right (by omega)]
      simp

/-- A digest's 32 bytes, packed into words, give its bytes back. -/
theorem wordsBytes_digest (d : Digest) : wordsBytes (packBytes d.toList) = d.toList := by
  rw [packed_bytes]
  simp

/-- A list of digests, packed digest by digest, gives its bytes back. -/
theorem wordsBytes_digests (ds : List Digest) :
    wordsBytes (ds.flatMap fun d => packBytes d.toList) = ds.flatMap Vector.toList := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [List.flatMap_cons, wordsBytes_append', wordsBytes_digest, ih]

/-- Byte lists of one length with the same little-endian value are equal. -/
theorem ofLE_inj {a b : List UInt8} (hlen : a.length = b.length)
    (h : ofLE a = ofLE b) : a = b := by
  apply List.ext_getElem hlen
  intro i ha hb
  apply UInt8.toNat_inj.mp
  simpa [List.getD_eq_getElem, ha, hb] using
    (ofLE_div_mod a i).symm.trans ((congrArg (fun n => n / 256 ^ i % 256) h).trans
      (ofLE_div_mod b i))

/-- The bytes of a number's word are the 8 little-endian bytes of the number. -/
theorem word_to_bytes (n : ℕ) : wordBytes (toWord n) = enc64 n := by
  apply ofLE_inj (by rw [wordBytes_length, enc64_length])
  rw [ofLE_wordBytes, ofLE_enc64]
  rfl

/-- The 8 little-endian bytes of a word's value are its bytes, low byte first. -/
theorem enc64_u64 (w : UInt64) : enc64 w.toNat =
    [(w >>> 0).toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8,
     (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8, (w >>> 56).toUInt8] := by
  apply List.ext_getElem (by simp [enc64_length])
  intro i hi hj
  have hi8 : i < 8 := by simpa [enc64_length] using hi
  interval_cases i <;> apply UInt8.toNat_inj.mp <;>
    simp [enc64, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- The value of a packed word is the little-endian value of its 8 bytes. -/
theorem pack8_toNat (a b c d e f g h : UInt8) :
    (ChainProof.pack8 a b c d e f g h).toNat = ofLE [a, b, c, d, e, f, g, h] := by
  have hb := enc64_u64 (ChainProof.pack8 a b c d e f g h)
  simp only [ChainProof.byte_pack8_0, ChainProof.byte_pack8_1, ChainProof.byte_pack8_2,
    ChainProof.byte_pack8_3, ChainProof.byte_pack8_4, ChainProof.byte_pack8_5,
    ChainProof.byte_pack8_6, ChainProof.byte_pack8_7] at hb
  have he := congrArg ofLE hb
  rw [ofLE_enc64, Nat.mod_eq_of_lt (UInt64.toNat_lt _)] at he
  exact he

/-- The middle part of `pre ++ mid ++ post`, by index and length. -/
theorem slice_mid {b : ByteArray} {pre mid post : List UInt8}
    (hb : b.data.toList = pre ++ mid ++ post) :
    (b.data.toList.drop pre.length).take mid.length = mid := by
  rw [hb, List.append_assoc, List.drop_left, List.take_left]

/-- Byte `j` of the middle part, read at index `pre.length + j`. -/
theorem get_mid {b : ByteArray} {pre mid post : List UInt8}
    (hb : b.data.toList = pre ++ mid ++ post) (j : ℕ) (hj : j < mid.length)
    (h : pre.length + j < b.size) : b[pre.length + j] = mid[j] := by
  simp only [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList, hb,
    List.append_assoc]
  rw [List.getElem_append_right (by omega)]
  simpa using List.getElem_append_left (bs := post) hj

/-- `ByteArray.extract` of the middle part is that part. -/
theorem extract_mid {b x : ByteArray} {pre post : List UInt8}
    (hb : b.data.toList = pre ++ x.data.toList ++ post) :
    b.extract pre.length (pre.length + x.size) = x := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  simpa using slice_mid hb

/-- `digestAt` reads a digest in the middle part back. -/
theorem digestAt_mid {b : ByteArray} {pre post : List UInt8} (d : Digest)
    (hb : b.data.toList = pre ++ d.toList ++ post) (h : pre.length + 32 ≤ b.size) :
    digestAt b pre.length h = d := by
  apply Vector.ext
  intro j hj
  simp only [digestAt, Vector.getElem_ofFn]
  exact (get_mid hb j (by simpa using hj) (by omega)).trans (by rfl)

/-- A list of digests has 32 bytes per digest. -/
theorem digests_length (ds : List Digest) : (ds.flatMap Vector.toList).length = 32 * ds.length := by
  simp [List.length_flatMap, Nat.mul_comm]

/-- `digestsAt` reads a list of digests in the middle part back. -/
theorem digestsAt_mid {b : ByteArray} {pre post : List UInt8} (ds : List Digest)
    (hb : b.data.toList = pre ++ ds.flatMap Vector.toList ++ post)
    (h : pre.length + 32 * ds.length ≤ b.size) :
    digestsAt b pre.length ds.length h = ds := by
  induction ds generalizing pre with
  | nil => rfl
  | cons d ds ih =>
    have hb1 : b.data.toList = pre ++ d.toList ++ (ds.flatMap Vector.toList ++ post) := by
      simpa [List.append_assoc] using hb
    have hb2 : b.data.toList = (pre ++ d.toList) ++ ds.flatMap Vector.toList ++ post := by
      simpa [List.append_assoc] using hb
    simp only [List.length_cons, digestsAt, digestAt_mid d hb1]
    have he := ih hb2 (by
      simp only [List.length_append, Vector.length_toList]
      simp only [List.length_cons] at h
      omega)
    simpa using he

end ParseProof
end RecursionFast.FastCheck
