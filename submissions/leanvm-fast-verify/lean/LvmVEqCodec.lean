-- New for lvm (WP-14a, H0): V_S's stream readers (`kAt`, `feAt`, `u64At`, `answerBits`, LvmDecideBase /
-- LvmDriver) are the compiled verifier's byte decoders (`Lvm.FS.kOfBytes`, `eOfBytes`, `chalOf`,
-- `rowOf`, LvmCompileCodec / LvmCompile) through `FK.toBF64`, `FE.toExt3`.
import LvmDecideBase
import LvmDriver
import LvmCompileCodec
import LvmFieldCorrect
import LvmVCore

/-!
# The native stream readers are the compiled verifier's byte decoders

`sb sig o n` is the byte window `[o, o + n)` of `sig` (fewer at the end). A word past the end of
`sig` reads `0` on both sides (`ByteArray.get!` and `List.getD _ _ 0`), so no size hypotheses.

* `toBF64_kAt`: the native word at `o` is `kOfBytes` of the window `[o, o + 8)`;
* `toExt3_feAt`, `toExt3_feAt_chal`: the native scalar at `o` is `eOfBytes` of `[o, o + 24)`, and
  `chalOf` of the digest at `o`;
* `rowOf_sb`: entry `j` of a row read by `rowOf kOfBytes` is the native word at `o + 8 j`;
* `eToNat_toExt3`, `answerBits_eq`: the challenge bits agree.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters

/-- Bytes `[o, o + n)` of a byte array (fewer at the end). -/
def sb (sig : ByteArray) (o n : ℕ) : List UInt8 := (sig.data.toList.drop o).take n

/-! ## Bytes of windows and digests -/

theorem getD_sb (sig : ByteArray) (o n i : ℕ) (hi : i < n) : (sb sig o n).getD i 0 = sig.get! (o + i) := by
  obtain ⟨d⟩ := sig
  simp only [sb, ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true, List.getElem?_drop, Array.getElem?_toList]
  rfl

theorem getD_digestAt (sig : ByteArray) (o i : ℕ) (hi : i < 32) :
    (digestAt sig o).toList.getD i 0 = sig.get! (o + i) := by
  simp [digestAt, List.getD_eq_getElem?_getD, hi]

theorem get!_digestBytes (a : RecursionFast.Digest) (i : ℕ) :
    (digestBytes a).get! i = a.toList.getD i 0 := by
  obtain ⟨⟨l⟩, hl⟩ := a
  simp [digestBytes, ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    List.getD_eq_getElem?_getD]
  rfl

/-! ## Words as numbers -/

/-- `s ||| a·2^k = s + a·2^k` when `s < 2^k`. -/
private theorem or_mul_pow (s a k P : ℕ) (hP : P = 2 ^ k) (hs : s < P) : s ||| a * P = s + a * P := by
  subst hP
  rw [← Nat.shiftLeft_eq, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hs, Nat.add_comm]

/-- The native lane at `o` is the little-endian number of the bytes `o, …, o + 7`. -/
theorem toNat_laneAt (b : ByteArray) (o : ℕ) :
    (laneAt b o).toNat = ∑ i : Fin 8, (b.get! (o + i)).toNat * 256 ^ (i : ℕ) := by
  simp only [laneAt, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Fin.sum_univ_eight]
  have h0 := (b.get! (o + 0)).toNat_lt; have h1 := (b.get! (o + 1)).toNat_lt
  have h2 := (b.get! (o + 2)).toNat_lt; have h3 := (b.get! (o + 3)).toNat_lt
  have h4 := (b.get! (o + 4)).toNat_lt; have h5 := (b.get! (o + 5)).toNat_lt
  have h6 := (b.get! (o + 6)).toNat_lt; have h7 := (b.get! (o + 7)).toNat_lt
  generalize (b.get! (o + 0)).toNat = x0 at *
  generalize (b.get! (o + 1)).toNat = x1 at *
  generalize (b.get! (o + 2)).toNat = x2 at *
  generalize (b.get! (o + 3)).toNat = x3 at *
  generalize (b.get! (o + 4)).toNat = x4 at *
  generalize (b.get! (o + 5)).toNat = x5 at *
  generalize (b.get! (o + 6)).toNat = x6 at *
  generalize (b.get! (o + 7)).toNat = x7 at *
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    Nat.shiftLeft_eq] at *
  norm_num at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [or_mul_pow _ _ 8 256 rfl (by omega), or_mul_pow _ _ 16 65536 rfl (by omega),
    or_mul_pow _ _ 24 16777216 rfl (by omega), or_mul_pow _ _ 32 4294967296 rfl (by omega),
    or_mul_pow _ _ 40 1099511627776 rfl (by omega), or_mul_pow _ _ 48 281474976710656 rfl (by omega),
    or_mul_pow _ _ 56 72057594037927936 rfl (by omega)]

/-- `kOfBytes` reads the little-endian number of the first eight bytes. -/
theorem toNat_kOfBytes (l : List UInt8) :
    (Lvm.FS.kOfBytes l).toBitVec.toNat = ∑ i : Fin 8, (l.getD i 0).toNat * 256 ^ (i : ℕ) := by
  simp only [Lvm.FS.kOfBytes, BF64.toBitVec_ofBitVec, BitVec.toNat_ofFin, Fin.val_cast,
    finFunctionFinEquiv_apply]
  rfl

theorem getD_drop_bytes (l : List UInt8) (m i : ℕ) : (l.drop m).getD i 0 = l.getD (m + i) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-! ## The readers -/

/-- The native word at `o` is `kOfBytes` of any byte list that agrees with `sig` on `[o, o + 8)`. -/
theorem toBF64_kAt_of (sig : ByteArray) (o : ℕ) (l : List UInt8)
    (h : ∀ i < 8, l.getD i 0 = sig.get! (o + i)) : FK.toBF64 (kAt sig o) = Lvm.FS.kOfBytes l := by
  apply BF64.ext
  apply BitVec.eq_of_toNat_eq
  rw [toNat_kOfBytes]
  change (laneAt sig o).toNat = _
  rw [toNat_laneAt]
  exact Finset.sum_congr rfl fun i _ => by rw [h i i.isLt]

/-- The native scalar at `o` is `eOfBytes` of any byte list that agrees with `sig` on
`[o, o + 24)`. -/
theorem toExt3_feAt_of (sig : ByteArray) (o : ℕ) (l : List UInt8)
    (h : ∀ i < 24, l.getD i 0 = sig.get! (o + i)) : FE.toExt3 (feAt sig o) = Lvm.FS.eOfBytes l := by
  have hk : ∀ j < 3, FK.toBF64 (kAt sig (o + 8 * j)) = Lvm.FS.kOfBytes (l.drop (8 * j)) :=
    fun j hj => toBF64_kAt_of _ _ _ fun i hi => by
      rw [getD_drop_bytes, h _ (by omega), Nat.add_assoc]
  apply CompPoly.Extension.Ext.ext
  intro i
  refine Eq.trans ?_ (congrFun (Equiv.apply_symm_apply (CompPoly.Extension.Ext.equivFn BF64.ext3Params)
    (fun j : Fin BF64.ext3Params.d => Lvm.FS.kOfBytes (l.drop (8 * j.val)))) i).symm
  obtain ⟨j, hj⟩ := i
  change j < 3 at hj
  interval_cases j
  · exact hk 0 (by omega)
  · exact hk 1 (by omega)
  · exact hk 2 (by omega)

theorem toBF64_kAt (sig : ByteArray) (o : ℕ) : FK.toBF64 (kAt sig o) = Lvm.FS.kOfBytes (sb sig o 8) :=
  toBF64_kAt_of _ _ _ fun i hi => getD_sb sig o 8 i hi

theorem toExt3_feAt (sig : ByteArray) (o : ℕ) : FE.toExt3 (feAt sig o) = Lvm.FS.eOfBytes (sb sig o 24) :=
  toExt3_feAt_of _ _ _ fun i hi => getD_sb sig o 24 i hi

theorem toExt3_feAt_chal (sig : ByteArray) (o : ℕ) :
    FE.toExt3 (feAt sig o) = Lvm.FS.chalOf (digestAt sig o) :=
  toExt3_feAt_of _ _ _ fun i hi => getD_digestAt sig o i (by omega)

theorem eToNat_toExt3 (x : FE) : LeanVM.Protocol.Verifier.eToNat (FE.toExt3 x) = Lvm.eToNat x := rfl

theorem answerBits_eq (a : RecursionFast.Digest) :
    answerBits a = LeanVM.Protocol.Verifier.eToNat (Lvm.FS.chalOf a) := by
  have h := toExt3_feAt_of (digestBytes a) 0 a.toList fun i _ => by rw [Nat.zero_add, get!_digestBytes]
  rw [Lvm.FS.chalOf, ← h, eToNat_toExt3]
  rfl

/-- **A row's entries**: entry `j < wd` of the row `rowOf kOfBytes wd` of the window
`[o, o + 8 wd)` is the native word at `o + 8 j`. -/
theorem rowOf_sb (sig : ByteArray) (o wd j : ℕ) (hj : j < wd) :
    (Lvm.FS.rowOf Lvm.FS.kOfBytes wd (sb sig o (8 * wd))).getD j 0 = FK.toBF64 (kAt sig (o + 8 * j)) := by
  rw [toBF64_kAt_of sig (o + 8 * j) (((sb sig o (8 * wd)).drop (8 * j)).take 8) fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hi, ← List.getD_eq_getElem?_getD, getD_drop_bytes,
      getD_sb _ _ _ _ (by omega), Nat.add_assoc]]
  simp only [Lvm.FS.rowOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some]

end Lvm.VEq
