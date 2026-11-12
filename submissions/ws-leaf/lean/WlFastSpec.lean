-- From relay-echo (#12), `lean/FastSpec.lean` (Apache-2.0), unchanged except the module names of
-- its imports.
/-
  The statements that tie the compiled verifier of `FastDefs.lean` to the library's.

  * **L1** `permF_eq`: the permutation `permF` is `Keccak.keccakFF`, from the statements of
    `FastSpecPerm.lean`.
  * **L2** `toH4_chainStepF` (the crux): one library chain step, read as words, is `stepH4`. It
    rests on `padB_chain_size` (the padded message is one block), `xorBlock_chain` (that block,
    XORed into the zero state, is `blockH4`: the tag shifts the digest by one byte) and
    `toH4_outBytes` (the output's words are lanes 0 to 3).
  * **L3** `chainEndH4_toH4` (the chain loop that `check'` runs is the library's chain, read as
    words, one step at a time by `chainEndH4_succ` of `FastSpecLoop.lean`) and `ofH4_toH4` (the
    round trip), so `chainEnd_lanes`.
  * **L5** `check'_eq`: the decision is the library's, so `V'_eq`.
-/
import WlFastDefs
import WlFastChainWords
import WlFastChainPad
import WlFastSpecParse
import WlFastSpecPerm
import WlFastSpecLoop

namespace RecursionFast.FastCheck
open RecursionFast Keccak

/-! ## L1: the permutation -/

/-- **L1.** `permF` is the library's word-level permutation. -/
theorem permF_eq (s : S25) : permF s = keccakFF s := by
  simp only [permF, roundsC_foldl, roundC_complL, foldl_roundC_complL, complL_complL,
    keccakFF_split]

/-! ## L2: one chain step -/

/-- The padded message of a chain step (`tagChain ‖ d`, 33 bytes) is one block. -/
theorem padB_chain_size (d : Digest) :
    (padB (pushDigest ((ByteArray.emptyWithCapacity 33).push tagChain) d)).size = rate := by
  obtain ⟨a, ha⟩ := d
  simp [padB, pushDigest, ByteArray.size, ha, rate]

/-- That block XORed into the zero state is `blockH4` of the digest's words. -/
theorem xorBlock_chain (d : Digest) :
    xorBlock zeroS (padB (pushDigest ((ByteArray.emptyWithCapacity 33).push tagChain) d)) 0 =
      blockH4 (toH4 d) := by
  simp only [blockH4, toH4, ← ChainProof.pack8.eq_1, ChainProof.pack8_shl, ChainProof.pack8_shr]
  simp [xorBlock, zeroS, laneAt, ChainProof.byteAt_chain, ChainProof.pack8, UInt64.or_assoc,
    show (1 : UInt64) <<< 8 = 256 from rfl,
    show (128 : UInt64) <<< 56 = 0x8000000000000000 from rfl]

/-- The words of the output bytes are lanes 0 to 3. -/
theorem toH4_outBytes (s : S25) : toH4 (outBytes s) = ⟨s.a0, s.a1, s.a2, s.a3⟩ := by
  change H4.mk _ _ _ _ = _
  congr 1 <;> exact ChainProof.pack8_bytes _

/-- **L2.** One step of the library's chain, read as words, is `stepH4` of the words. -/
theorem toH4_chainStepF (d : Digest) : toH4 (chainStepF d) = stepH4 (toH4 d) := by
  simp only [chainStepF, digestB, padB_chain_size, show rate / rate = 1 from rfl,
    loopB, xorBlock_chain, toH4_outBytes, stepH4, permF_eq]

/-! ## L3: the chain -/

/-- **L3.** The chain in words is the library's chain, read as words. -/
theorem chainEndH4_toH4 (s : Digest) (n : ℕ) : chainEndH4 (toH4 s) n = toH4 (chainEndF s n) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [chainEndH4_succ, ← toH4_chainStepF, ih, chainEndF]

/-- **L3.** A digest's words give the digest back. -/
theorem ofH4_toH4 (d : Digest) : ofH4 (toH4 d) = d := by
  simp only [ofH4, toH4, ← ChainProof.pack8.eq_1, ChainProof.byte_pack8_0,
    ChainProof.byte_pack8_1, ChainProof.byte_pack8_2, ChainProof.byte_pack8_3,
    ChainProof.byte_pack8_4, ChainProof.byte_pack8_5, ChainProof.byte_pack8_6,
    ChainProof.byte_pack8_7]
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-- The leaf's chain end as `check'` computes it is the library's. -/
theorem chainEnd_lanes (s : Digest) (n : ℕ) : ofH4 (chainEndH4 (toH4 s) n) = chainEndF s n := by
  rw [chainEndH4_toH4, ofH4_toH4]

/-! ## L5: the decision -/

/-- **L5.** The decision is the library's: by strong induction on the proof's size, from
`encodeB_eq` (L5a) and `parseB_encode` (L5b) in `FastSpecParse.lean`, `chainEnd_lanes` and
`WitnessSending.check_iff`. -/
theorem check'_eq : check' = WitnessSending.check := by
  have child_acc (vk c : Digest) (p : Signed) :
      (decide (p.π.size < 2 ^ 64) && decide (p.tr.length ≤ 0) &&
        decide (∀ e ∈ p.tr, e.1.size ≤ queryCap) &&
        SigOkF vk (traceDigestF p.tr) p.σ && (p.tr.isEmpty && WitnessSending.check vk c p.π)) =
      WitnessSending.submission.acc vk c p := by
    rw [WitnessSending.acc_eq, SigOkF_eq, traceDigestF_eq]
  funext vk c π
  induction h : π.size using Nat.strong_induction_on generalizing c π with
  | _ k ih =>
    subst h
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h1
      rw [check'] at h1
      split at h1
      · next s n hp =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨⟨he, hn⟩, hc⟩ := h1
        rw [encodeB_eq] at he
        have hfit : (Wit.leaf s n).Fits := lt_of_le_of_lt hn (by decide)
        rw [WitnessSending.check_eq, ← he, WitnessSending.decode_encode _ hfit]
        simp only [decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
        rw [chainEnd_lanes, leafStmtF_eq, chainEndF_eq] at hc
        exact ⟨hn, hc⟩
      · next c₁ c₂ p₁ p₂ hp =>
        split at h1
        · next hs =>
          split at h1
          · next he =>
            rw [ih _ hs.1 c₁ p₁.π rfl, ih _ hs.2 c₂ p₂.π rfl, child_acc, child_acc] at h1
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
            obtain ⟨⟨hc, ha₁⟩, ha₂⟩ := h1
            rw [encodeB_eq] at he
            have hfit : (Wit.node c₁ c₂ p₁ p₂).Fits :=
              ⟨WitnessSending.fits_of_acc ha₁, WitnessSending.fits_of_acc ha₂⟩
            rw [WitnessSending.check_eq, ← he, WitnessSending.decode_encode _ hfit]
            simp only [ite_true, Bool.and_eq_true, decide_eq_true_eq]
            rw [nodeStmtF_eq] at hc
            exact ⟨⟨hc, ha₁⟩, ha₂⟩
          · cases h1
        · cases h1
      · cases h1
    · intro h2
      obtain ⟨w, -, he, hR⟩ := (WitnessSending.check_iff vk c π).mp h2
      have hfit := WitnessSending.fits_of_rel hR
      subst he
      rw [check', parseB_encode w hfit]
      cases w with
      | leaf s n =>
        simp only [encodeB_eq, decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
        rw [chainEnd_lanes, leafStmtF_eq, chainEndF_eq]
        exact hR
      | node c₁ c₂ p₁ p₂ =>
        have hs := WitnessSending.size_child_lt c₁ c₂ p₁ p₂
        dsimp only
        rw [dite_eq_left hs, ite_eq_left (by rw [encodeB_eq]), ih _ hs.1 c₁ p₁.π rfl,
          ih _ hs.2 c₂ p₂.π rfl, child_acc, child_acc]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [nodeStmtF_eq]
        exact ⟨⟨hR.1, hR.2.1⟩, hR.2.2⟩

/-- **The verifier is the library's.** -/
theorem V'_eq : V' = WitnessSending.V := by
  funext vk c π
  simp only [V', WitnessSending.V, check'_eq]

end RecursionFast.FastCheck
