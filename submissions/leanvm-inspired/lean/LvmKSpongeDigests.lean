-- Copied from flock-recursive `FRKeccakDigests.lean` (stage K2-LS) for lvm (WP-8) as `LvmKSpongeDigests`; namespace FR.KSponge → Lvm.KSponge.
import LvmKSponge

/-!
# The contract's digests from chains of permutation blocks

What the node hashes in-circuit (K0-DES §3.4), each as "blocks that are `BlockPerm`s of their input
XOR their rate bytes, with these bytes ⇒ the contract's digest". The bytes are stated pointwise, as
the block kinds pin them (tags, `padAt`) and as the slots carry them (digests, `enc64` words).

One block from the zero state (`absorb_one`; the kinds `chain`, `w43`, `hash41`, `hash65`):
* `chainStep_block` (33 B), `wotsStep_block` (43 B), `leafStmt_block` (41 B),
  `nodeStmt_block`, `sigNode_block` (65 B).

Streams (`absorb_sound`, `absorb_whole`):
* `traceDigest_whole`: `q` whole blocks carrying `0x54 ‖ traceBytes tr` (`136 q` bytes) and a final
  pad block give `traceDigest tr`; `traceDigest_272` is the node's case `q = 2k` (streams of
  `272 k` bytes, the pad block even);
* `wotsLeaf_stream`: 32 blocks carrying `0x4B ‖ enc64 j ‖ end₀ ‖ … ‖ end₁₃₂` (4,265 B, the last block
  `tail 49`) give `wotsLeaf j ends`; `wotsLeaf_bytes` gives the stream from the per-end bytes
  (end `i` byte `k` at stream offset `9 + 32 i + k`); `padOk_iff_tail` the tail block's pins.

The digest-level selections (`wots_chain_sound`, `sigRoot_bits`, `wots_sound` in `FRWots`) are
hash-agnostic and take these digests as they are.
-/

namespace Lvm
namespace KSponge
open RecursionFast RecursionFast.Keccak

/-! ## Byte access helpers -/

theorem getD_app (l₁ l₂ : List UInt8) (q : ℕ) :
    (l₁ ++ l₂).getD q 0 = if q < l₁.length then l₁.getD q 0 else l₂.getD (q - l₁.length) 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by assumption)]
  · rw [List.getElem?_append_right (by omega)]

theorem getElem_eq_getD (l : List UInt8) {p : ℕ} (h : p < l.length) : l[p] = l.getD p 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_cons0 (a : UInt8) (l : List UInt8) (q : ℕ) :
    (a :: l).getD q 0 = if q = 0 then a else l.getD (q - 1) 0 := by
  cases q <;> simp

theorem digest_getD (d : Digest) {k : ℕ} (hk : k < 32) : d.toList.getD k 0 = d[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem enc64_getD (n : ℕ) {k : ℕ} (hk : k < 8) : (enc64 n).getD k 0 = (n / 256 ^ k).toUInt8 := by
  rw [enc64, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [hk, dite_true, Option.getD_some]

@[simp] theorem enc64_length (n : ℕ) : (enc64 n).length = 8 := by simp [enc64]

/-- The padding bytes of a one-block message (`L < 135`): `0x01` at `L`, `0x80` at byte 135. -/
theorem padAt_short {L q : ℕ} (hL : L < rate - 1) (hq : q < rate) :
    padAt L q = if q = L then 0x01 else if q = rate - 1 then 0x80 else 0 := by
  unfold padAt
  have r : rate = 136 := rfl
  generalize rate = R at *
  subst r
  rw [Nat.mod_eq_of_lt (show L < 136 by omega), Nat.mod_eq_of_lt hq]
  by_cases h : q = L
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_right (by omega)]
  · rw [ite_eq_right h, ite_eq_right h]

/-! ## One block -/

/-- **A chain step block** (kind `chain`): rate bytes `tagChain ‖ d ‖ pad` from the zero state
output `chainStep d`. -/
theorem chainStep_block (d : Digest) (m : ℕ → UInt8) (sOut : State)
    (h0 : m 0 = tagChain) (hd : ∀ k (hk : k < 32), m (1 + k) = d[k])
    (hpad : ∀ q, 33 ≤ q → q < rate → m q = padAt 33 q)
    (hperm : BlockPerm (xorMsg zeroSt m) sOut) : stDigest sOut = chainStep d := by
  refine absorb_one _ (by simp [rate]) m sOut (fun q hq => ?_) (by simpa using hpad) hperm
  simp only [List.length_cons, Vector.length_toList] at hq
  rw [getD_cons0]
  split
  · subst_vars; exact h0
  · rw [digest_getD _ (by omega), ← hd _ (by omega)]; congr 1; omega

/-- **A WOTS chain step block** (kind `w43 i s`): rate bytes
`tagWots ‖ enc64 j ‖ i ‖ s ‖ x ‖ pad` from the zero state output `wotsStep j i s x`. -/
theorem wotsStep_block (j i s : ℕ) (x : Digest) (m : ℕ → UInt8) (sOut : State)
    (h0 : m 0 = tagWots) (hj : ∀ k < 8, m (1 + k) = (j / 256 ^ k).toUInt8)
    (hi : m 9 = i.toUInt8) (hs : m 10 = s.toUInt8) (hx : ∀ k (hk : k < 32), m (11 + k) = x[k])
    (hpad : ∀ q, 43 ≤ q → q < rate → m q = padAt 43 q)
    (hperm : BlockPerm (xorMsg zeroSt m) sOut) : stDigest sOut = wotsStep j i s x := by
  refine absorb_one _ (by simp [rate]) m sOut (fun q hq => ?_) (by simpa using hpad) hperm
  simp only [List.length_cons, List.length_append, enc64_length, Vector.length_toList,
    List.length_nil] at hq
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [getD_cons0]
  by_cases q0 : q = 0
  · subst q0; simpa using h0
  rw [ite_eq_right q0, getD_app, enc64_length]
  by_cases q9 : q - 1 < 8
  · rw [ite_eq_left q9, enc64_getD _ q9, ← hj _ q9]
    congr 1; omega
  rw [ite_eq_right q9, getD_cons0]
  by_cases q9' : q - 1 - 8 = 0
  · rw [ite_eq_left q9', show q = 9 by omega, hi]
  rw [ite_eq_right q9', getD_cons0]
  by_cases q10 : q - 1 - 8 - 1 = 0
  · rw [ite_eq_left q10, show q = 10 by omega, hs]
  rw [ite_eq_right q10, digest_getD _ (by omega), ← hx _ (by omega)]
  congr 1; omega

/-- **A leaf statement block** (kind `hash41`): rate bytes `tagLeaf ‖ h ‖ enc64 n ‖ pad` from the
zero state output `leafStmt h n`. -/
theorem leafStmt_block (h : Digest) (n : ℕ) (m : ℕ → UInt8) (sOut : State)
    (h0 : m 0 = tagLeaf) (hh : ∀ k (hk : k < 32), m (1 + k) = h[k])
    (hn : ∀ k < 8, m (33 + k) = (n / 256 ^ k).toUInt8)
    (hpad : ∀ q, 41 ≤ q → q < rate → m q = padAt 41 q)
    (hperm : BlockPerm (xorMsg zeroSt m) sOut) : stDigest sOut = leafStmt h n := by
  refine absorb_one _ (by simp [rate]) m sOut (fun q hq => ?_) (by simpa using hpad) hperm
  simp only [List.length_cons, List.length_append, enc64_length, Vector.length_toList] at hq
  rw [List.cons_append, getD_cons0]
  by_cases q0 : q = 0
  · subst q0; simpa using h0
  rw [ite_eq_right q0, getD_app, Vector.length_toList]
  by_cases q33 : q - 1 < 32
  · rw [ite_eq_left q33, digest_getD _ q33, ← hh _ q33]
    congr 1; omega
  rw [ite_eq_right q33, enc64_getD _ (by omega), ← hn _ (by omega)]
  congr 1; omega

/-- Two digests after a tag (`nodeStmt`, `sigNode`). -/
theorem two_block (tag : UInt8) (l r : Digest) (m : ℕ → UInt8) (sOut : State)
    (h0 : m 0 = tag) (hl : ∀ k (hk : k < 32), m (1 + k) = l[k]) (hr : ∀ k (hk : k < 32), m (33 + k) = r[k])
    (hpad : ∀ q, 65 ≤ q → q < rate → m q = padAt 65 q)
    (hperm : BlockPerm (xorMsg zeroSt m) sOut) :
    stDigest sOut = keccakDigest (tag :: l.toList ++ r.toList) := by
  refine absorb_one _ (by simp [rate]) m sOut (fun q hq => ?_) (by simpa using hpad) hperm
  simp only [List.length_cons, List.length_append, Vector.length_toList] at hq
  rw [List.cons_append, getD_cons0]
  by_cases q0 : q = 0
  · subst q0; simpa using h0
  rw [ite_eq_right q0, getD_app, Vector.length_toList]
  by_cases q33 : q - 1 < 32
  · rw [ite_eq_left q33, digest_getD _ q33, ← hl _ q33]
    congr 1; omega
  rw [ite_eq_right q33, digest_getD _ (by omega), ← hr _ (by omega)]
  congr 1; omega

/-- **A node statement block** (kind `hash65 tagNode`): `tagNode ‖ c₁ ‖ c₂ ‖ pad` ⇒
`nodeStmt c₁ c₂`. -/
theorem nodeStmt_block (c₁ c₂ : Digest) (m : ℕ → UInt8) (sOut : State)
    (h0 : m 0 = tagNode) (h₁ : ∀ k (hk : k < 32), m (1 + k) = c₁[k]) (h₂ : ∀ k (hk : k < 32), m (33 + k) = c₂[k])
    (hpad : ∀ q, 65 ≤ q → q < rate → m q = padAt 65 q)
    (hperm : BlockPerm (xorMsg zeroSt m) sOut) : stDigest sOut = nodeStmt c₁ c₂ :=
  two_block _ _ _ m sOut h0 h₁ h₂ hpad hperm

/-- **A signature Merkle node block** (kind `hash65 tagSigNode`): `tagSigNode ‖ l ‖ r ‖ pad` ⇒
`sigNode l r`. -/
theorem sigNode_block (l r : Digest) (m : ℕ → UInt8) (sOut : State)
    (h0 : m 0 = tagSigNode) (hl : ∀ k (hk : k < 32), m (1 + k) = l[k]) (hr : ∀ k (hk : k < 32), m (33 + k) = r[k])
    (hpad : ∀ q, 65 ≤ q → q < rate → m q = padAt 65 q)
    (hperm : BlockPerm (xorMsg zeroSt m) sOut) : stDigest sOut = sigNode l r :=
  two_block _ _ _ m sOut h0 hl hr hpad hperm

/-! ## The trace digest -/

/-- **The trace digest over whole blocks** (K0-DES §3.3): `q > 0` main blocks carrying
`0x54 ‖ traceBytes tr` (`136 q` bytes) and a final pad block linked from the last give
`traceDigest tr` at the final block's output. -/
theorem traceDigest_whole (q : ℕ) (hq : 0 < q) (m : ℕ → ℕ → UInt8) (sIn sOut : ℕ → State)
    (fIn fOut : State) (mF : ℕ → UInt8)
    (hstart : sIn 0 = zeroSt)
    (hperm : ∀ i < q, BlockPerm (xorMsg (sIn i) (m i)) (sOut i))
    (hlink : ∀ i, i + 1 < q → sIn (i + 1) = sOut i)
    (hfin : fIn = sOut (q - 1)) (hmF : ∀ j < rate, mF j = padBlk j)
    (hpermF : BlockPerm (xorMsg fIn mF) fOut)
    (tr : Trace) (htr : streamOf m (rate * q) = tagTrace :: traceBytes tr) :
    stDigest fOut = traceDigest tr := by
  rw [absorb_whole q hq m sIn sOut fIn fOut mF hstart hperm hlink hfin hmF hpermF, htr,
    traceDigest]

/-- **The node's trace stream** (K0-DES §3.3: every stream has `272 k` bytes, `k > 0`): `2k` main
blocks and the pad block (index `2k`, even: `traceDigest_bits` reads it in window A). -/
theorem traceDigest_272 (k : ℕ) (hk : 0 < k) (m : ℕ → ℕ → UInt8) (sIn sOut : ℕ → State)
    (fIn fOut : State) (mF : ℕ → UInt8)
    (hstart : sIn 0 = zeroSt)
    (hperm : ∀ i < 2 * k, BlockPerm (xorMsg (sIn i) (m i)) (sOut i))
    (hlink : ∀ i, i + 1 < 2 * k → sIn (i + 1) = sOut i)
    (hfin : fIn = sOut (2 * k - 1)) (hmF : ∀ j < rate, mF j = padBlk j)
    (hpermF : BlockPerm (xorMsg fIn mF) fOut)
    (tr : Trace) (htr : streamOf m (272 * k) = tagTrace :: traceBytes tr) :
    stDigest fOut = traceDigest tr :=
  traceDigest_whole (2 * k) (by omega) m sIn sOut fIn fOut mF hstart hperm hlink hfin hmF hpermF
    tr (by rw [show rate * (2 * k) = 272 * k by simp only [rate]; omega]; exact htr)

/-! ## The WOTS key leaf -/

/-- The tail block's pins: `PadOk m L` is the last block's bytes from `L mod 136` on. -/
theorem padOk_iff_tail (m : ℕ → ℕ → UInt8) (L : ℕ) :
    PadOk m L ↔ ∀ j, L % rate ≤ j → j < rate → m (L / rate) j = padAt L (rate * (L / rate) + j) := by
  have r : rate = 136 := rfl
  constructor
  · intro h j h1 h2
    have := h (rate * (L / rate) + j) (by rw [r] at *; omega) (by simp only [nBlk, r] at *; omega)
    rwa [show (rate * (L / rate) + j) / rate = L / rate by rw [r] at *; omega,
      show (rate * (L / rate) + j) % rate = j by rw [r] at *; omega] at this
  · intro h p h1 h2
    simp only [nBlk] at h2
    have := h (p % rate) (by rw [r] at *; omega) (Nat.mod_lt _ (by decide))
    rwa [show L / rate = p / rate by rw [r] at *; omega,
      show rate * (p / rate) + p % rate = p by rw [r] at *; omega] at this

/-- **The WOTS key leaf** (32 blocks, 4,265 bytes, the last block the `tail 49` kind). -/
theorem wotsLeaf_stream (j : ℕ) (ends : List Digest)
    (m : ℕ → ℕ → UInt8) (sIn sOut : ℕ → State)
    (hstart : sIn 0 = zeroSt)
    (hperm : ∀ i < 32, BlockPerm (xorMsg (sIn i) (m i)) (sOut i))
    (hlink : ∀ i, i + 1 < 32 → sIn (i + 1) = sOut i)
    (hpad : PadOk m 4265)
    (hmsg : streamOf m 4265 = tagWotsLeaf :: enc64 j ++ ends.flatMap Vector.toList) :
    stDigest (sOut 31) = wotsLeaf j ends := by
  have := absorb_sound 4265 m sIn sOut hstart (fun i hi => hperm i (by simpa [nBlk, rate] using hi))
    (fun i hi => hlink i (by simpa [nBlk, rate] using hi)) hpad
  rw [hmsg] at this
  exact this

theorem flatMap_digest_getD (ends : List Digest) {i k : ℕ} (hi : i < ends.length) (hk : k < 32) :
    (ends.flatMap Vector.toList).getD (32 * i + k) 0 = (ends[i])[k] := by
  induction ends generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    rw [List.flatMap_cons, getD_app, Vector.length_toList]
    cases i with
    | zero => simp [hk]
    | succ i =>
      rw [ite_eq_right (by omega), show 32 * (i + 1) + k - 32 = 32 * i + k by omega,
        ih (by simpa using hi)]
      simp

theorem flatMap_digest_length (ends : List Digest) :
    (ends.flatMap Vector.toList).length = 32 * ends.length := by
  induction ends with
  | nil => simp
  | cons e es ih => simp [List.length_flatMap] at ih ⊢; omega

/-- **The key leaf's bytes**, pointwise: stream byte 0 is the tag, bytes `1 … 8` are `enc64 j`, and
byte `k` of end `i` is at offset `9 + 32 i + k` (the mirrors' `133` ends, K0-DES §3.4). -/
theorem wotsLeaf_bytes (j : ℕ) (ends : List Digest) (hlen : ends.length = wotsLen)
    (m : ℕ → ℕ → UInt8) (h0 : m 0 0 = tagWotsLeaf)
    (hj : ∀ k < 8, m ((1 + k) / rate) ((1 + k) % rate) = (j / 256 ^ k).toUInt8)
    (he : ∀ i (hi : i < wotsLen), ∀ k (hk : k < 32),
      m ((9 + 32 * i + k) / rate) ((9 + 32 * i + k) % rate) = (ends[i]'(hlen ▸ hi))[k]) :
    streamOf m 4265 = tagWotsLeaf :: enc64 j ++ ends.flatMap Vector.toList := by
  have hl := flatMap_digest_length ends
  rw [hlen] at hl
  apply List.ext_getElem
  · rw [streamOf_length]; simp [hl, wotsLen]
  intro p h1 h2
  rw [getElem_eq_getD, getElem_eq_getD]
  rw [streamOf_length] at h1
  rw [streamOf_getD _ _ h1, List.cons_append, getD_cons0]
  by_cases p0 : p = 0
  · subst p0; simpa using h0
  rw [ite_eq_right p0, getD_app, enc64_length]
  by_cases p9 : p - 1 < 8
  · rw [ite_eq_left p9, enc64_getD _ p9, ← hj _ p9]
    congr 2 <;> omega
  rw [ite_eq_right p9]
  have hi : (p - 9) / 32 < wotsLen := by simp only [wotsLen]; omega
  rw [show p - 1 - 8 = 32 * ((p - 9) / 32) + (p - 9) % 32 by omega,
    flatMap_digest_getD _ (by rw [hlen]; exact hi) (Nat.mod_lt _ (by decide)),
    ← he _ hi _ (Nat.mod_lt _ (by decide))]
  congr 2 <;> omega

end KSponge
end Lvm
