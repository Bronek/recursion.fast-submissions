-- WP-5 (FS). New for lvm (BLUEPRINT §2.2): the byte decoders of the compiled verifier and the
-- uniformity of challenges.
import LvmCompile
import Mathlib.Algebra.BigOperators.Fin

/-!
# Byte decoders and uniform challenges

* `kOfBytes b`: the first 8 bytes of `b`, little-endian, as the bit pattern of a `K` word.
* `eOfBytes b`: the first 24 bytes as three `K` limbs (limb `j` = bytes `8j … 8j+7`).
* `chalOf a`: the challenge of an answer, lanes 0–2 of the digest as an `E` element (BLUEPRINT
  §2.2).
* **`chalOf_sum`**: every challenge has exactly `2^64` answers (the last 8 bytes are free), so the
  average over uniform digests of a function of the challenge is its average over `E`.
-/

namespace Lvm.FS

open LeanVM.Parameters LeanVM.Protocol.Compile RecursionFast
open scoped NNReal

/-- 8 bytes, little-endian, as a `K` word. -/
def kOfBytes (b : Bytes) : K :=
  BF64.ofBitVec (BitVec.ofFin (Fin.cast (by norm_num [UInt8.size])
    (finFunctionFinEquiv (fun i : Fin 8 => (b.getD i 0).toFin))))

/-- 24 bytes as an `E` scalar, limb `j` from bytes `8j … 8j+7`. -/
def eOfBytes (b : Bytes) : E :=
  (CompPoly.Extension.Ext.equivFn BF64.ext3Params).symm fun j => kOfBytes (b.drop (8 * j.val))

/-- The challenge of an answer: lanes 0–2 as an `E` element. -/
def chalOf (a : Digest) : E := eOfBytes a.toList

/-- Equal words from `kOfBytes` have equal first eight bytes. -/
theorem getD_of_kOfBytes_eq {b b' : Bytes} (h : kOfBytes b = kOfBytes b') (i : Fin 8) :
    b.getD i 0 = b'.getD i 0 := by
  unfold kOfBytes at h
  have h1 := congrArg BF64.toBitVec h
  simp only [BF64.toBitVec_ofBitVec] at h1
  simp only [BitVec.ofFin.injEq, Fin.cast_inj, EmbeddingLike.apply_eq_iff_eq] at h1
  exact UInt8.toFin_inj.mp (congrFun h1 i)

/-- Byte `i` after the first `m` bytes of a digest. -/
theorem getD_drop_toList (a : Digest) (m i : ℕ) (h : m + i < 32) :
    (a.toList.drop m).getD i 0 = a[m + i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The challenge and the last eight bytes determine the digest. -/
theorem chalOf_injective : Function.Injective fun a : Digest =>
    (chalOf a, fun i : Fin 8 => (a[24 + (i : ℕ)]'(by omega)).toFin) := by
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  obtain ⟨h1, h2⟩ := hab
  have h3 := (CompPoly.Extension.Ext.equivFn BF64.ext3Params).symm.injective h1
  apply Vector.ext
  intro k hk
  by_cases hk24 : k < 24
  · have hj := congrFun h3 ⟨k / 8, by simp; omega⟩
    have := getD_of_kOfBytes_eq hj ⟨k % 8, by omega⟩
    simp only at this
    rw [getD_drop_toList _ _ _ (by omega), getD_drop_toList _ _ _ (by omega)] at this
    simpa [Nat.div_add_mod] using this
  · have := congrFun h2 ⟨k - 24, by omega⟩
    simp only at this
    have := UInt8.toFin_inj.mp this
    simpa [show 24 + (k - 24) = k by omega] using this

/-- **Uniform answers give uniform challenges.** -/
theorem chalOf_sum (f : E → ℝ≥0) : ∑ a : Digest, f (chalOf a) = 2 ^ 64 * ∑ c : E, f c := by
  have hbij : Function.Bijective fun a : Digest =>
      (chalOf a, fun i : Fin 8 => (a[24 + (i : ℕ)]'(by omega)).toFin) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨chalOf_injective, ?_⟩
    simp [Fintype.card_prod, BF64.card_ext3, UInt8.size]
  rw [Fintype.sum_bijective _ hbij (fun a => f (chalOf a)) (fun p => f p.1) (fun _ => rfl),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Finset.mul_sum]
  norm_num

end Lvm.FS
