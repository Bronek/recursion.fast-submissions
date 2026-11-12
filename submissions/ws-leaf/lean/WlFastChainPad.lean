-- From relay-echo (#12), `lean/FastProofChainPad.lean` (Apache-2.0), unchanged except the module names of
-- its imports.
/-
  The padded message of a chain step, byte by byte, for `xorBlock_chain` (`FastSpec.lean`): the
  tag `0x43`, the digest, `0x01`, zeros, and `0x80` at byte 135, one block of 136 bytes.
-/
import WlFastDefs

namespace RecursionFast.FastCheck.ChainProof
open RecursionFast Keccak

/-- The chain message occupies one block: tag, digest, padding byte, zeros, final high bit. -/
theorem pad_chain_data (d : Digest) :
    (padB (pushDigest ((ByteArray.emptyWithCapacity 33).push tagChain) d)).data =
      (((#[tagChain] ++ d.toArray).push 1) ++ Array.replicate 101 0).push 128 := by
  simp [padB, pushDigest, ByteArray.size, rate]

/-- Each byte of the padded chain message, including the zero value beyond the block. -/
theorem byteAt_chain (d : Digest) (i : Nat) :
    byteAt (padB (pushDigest ((ByteArray.emptyWithCapacity 33).push tagChain) d)) i =
      if i = 0 then 0x43 else
      if h : i < 33 then (d[i - 1]'(by omega)).toUInt64 else
      if i = 33 then 1 else
      if i = 135 then 128 else 0 := by
  simp only [byteAt, ByteArray.size, ByteArray.getElem_eq_getElem_data, pad_chain_data]
  simp only [Array.size_push, Array.size_append, Array.size_replicate, Array.size_singleton,
    Vector.size_toArray]
  by_cases h0 : i = 0
  · subst i
    simp [tagChain]
  · by_cases h33 : i < 33
    · simp [h0, h33, Array.getElem_push, Array.getElem_append,
        show i < 136 by omega, show i - 1 < 33 by omega, show i - 1 < 32 by omega,
        show ¬i < 1 by omega]
    · by_cases he33 : i = 33
      · subst i
        simp [Array.getElem_push]
      · by_cases h135 : i = 135
        · subst i
          simp [Array.getElem_push]
        · by_cases h136 : i < 136
          · simp [h0, h33, he33, h135, h136, Array.getElem_push, Array.getElem_append,
              show ¬i - 1 < 33 by omega, show i - 1 - 33 < 101 by omega]
          · simp [h0, h33, he33, h135, h136]

end RecursionFast.FastCheck.ChainProof
