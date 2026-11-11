-- New for lvm (WP-8): the sponge table `KS` and the contract digests it proves (BLUEPRINT §4.2, §11 A2, A6).
-- The sponge layer is K2-LS (`LvmKSponge*`, copied from flock-recursive `FRKeccak{Sponge,Digests,Bits}`).
import LvmKeccakCandidate
import LvmKSpongeDigests
import LvmKSpongeBits
import LvmKSpongePerm

/-!
# The sponge table `KS`

`KS` is a 64-slot block `ks` of `K` words on `hk` row variables (`hk = ksLog`, `2^15` rows): slots
`0 … 24` hold row `i`'s permutation input `in_i` (`inState hk ks 0 i`). Its output lanes `Y i l`
(lanes 0–13 in slots 50–63, lanes 14–24 elsewhere in `C_main`), its message lanes `msg i l`
(`l < 17`: `C_rec`'s stream columns `M_l` below `2^14`, `C_main`'s `X_l` above) and the structured
continuation flag `cont i` are given as functions.

* `SpongeRel`: what `KS`'s constraints give: the Keccak GKR with all 25 lanes tied
  (`Y_i = keccakF(in_i)`), and the sponge link `in_i[l] = cont_i·Y_{i−1}[l] + [l < 17]·Msg_l[i]`.
* **`row_perm`**: row `i` is a K2-LS `BlockPerm` of its predecessor's output (or the zero state)
  with its message bytes absorbed (`msgBytes i`: the 136 little-endian bytes of `msg i 0 … 16`).
* **`sponge_segment`**: rows `a … a + nBlk L − 1` with `cont a = 0`, `cont = 1` inside and the
  padding pinned give `keccakDigest` of the `L` bytes they carry (`absorb_sound`).
* Instances: **`traceDigest_of_KS`** (the trace sponge, rows `0 … B − 1`), **`wotsLeaf_of_KS`** (32
  rows), and one-row hashes **`oneRow_perm`** for `wotsStep_block`, `sigNode_block`,
  `leafStmt_block`, `nodeStmt_block` (`LvmKSpongeDigests`), with `wotsStep_of_KS`, `sigNode_of_KS`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakGkr Lvm.KSponge

variable (hk : ℕ) (ks : ℕ → K) (Y msg : ℕ → ℕ → K) (cont : ℕ → Bool)

/-- **What `KS`'s constraints give.** -/
structure SpongeRel : Prop where
  /-- The Keccak GKR, all 25 lanes tied to `Y` (A6): `Y_i = keccakF(in_i)`. -/
  out : ∀ i < 2 ^ hk, ∀ l < 25, Y i l = laneWord (keccakF1600 (inState hk ks 0 i)) l
  /-- The sponge link (every row): `in_i[l] = cont_i·Y_{i−1}[l] + [l < 17]·Msg_l[i]`. -/
  link : ∀ i < 2 ^ hk, ∀ l < 25,
    ks (i + 2 ^ hk * l) = (if cont i then Y (i - 1) l else 0) + (if l < 17 then msg i l else 0)
  /-- Row 0 starts a sponge. -/
  cont0 : cont 0 = false

theorem lane_ofLane (w : UInt64) : K.lane (K.ofLane w) = w := rfl

/-- Row `i`'s output as a state. -/
def yState (i : ℕ) : RecursionFast.Keccak.State := Vector.ofFn fun l : Fin 25 ↦ K.lane (Y i l)

/-- Row `i`'s 136 message bytes: byte `q` is byte `q % 8` of lane `q / 8`, little-endian. -/
def msgBytes (i q : ℕ) : UInt8 := (K.lane (msg i (q / 8)) >>> (8 * (q % 8)).toUInt64).toUInt8

/-- The state a row absorbs into: its predecessor's output if it continues a sponge. -/
def prevState (i : ℕ) : RecursionFast.Keccak.State := if cont i then yState Y (i - 1) else zeroSt

theorem msgBytes_bit (i q : ℕ) {t : ℕ} (ht : t < 8) :
    (msgBytes msg i q).toBitVec.getLsbD t = (msg i (q / 8)).toBitVec.getLsbD (8 * (q % 8) + t) := by
  have hn : q % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [msgBytes, K.lane]
  generalize q % 8 = n at hn ⊢
  generalize (msg i (q / 8)).toBitVec = v
  simp only [UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt64.toBitVec_shiftRight]
  interval_cases n <;> simp [ht]

/-- **Row `i` is one permutation block** of the sponge. -/
theorem row_perm (H : SpongeRel hk ks Y msg cont) {i : ℕ} (hi : i < 2 ^ hk) :
    BlockPerm (xorMsg (prevState Y cont i) (msgBytes msg i)) (yState Y i) := by
  have hin : inState hk ks 0 i = xorMsg (prevState Y cont i) (msgBytes msg i) := by
    refine state_ext fun k hk' ↦ ?_
    rw [xorMsg_bit _ _ hk']
    have hl : k / 64 < 25 := by omega
    simp only [stBit, hk', dite_true, inState, Vector.getElem_ofFn, K.lane, Nat.mul_zero,
      Nat.zero_add]
    rw [H.link i hi _ hl, LvmKeccakWords_toBitVec_add, BitVec.getLsbD_xor]
    congr 1
    · unfold prevState
      split
      · simp [yState, K.lane]
      · simp [zeroSt]
    · rw [msgBytes_bit _ _ _ (Nat.mod_lt _ (by decide)),
        show k / 8 / 8 = k / 64 by omega, show 8 * (k / 8 % 8) + k % 8 = k % 64 by omega]
      by_cases h17 : k / 64 < 17
      · rw [if_pos h17, decide_eq_true (show k < 1088 by omega), Bool.true_and]
      · rw [if_neg h17, decide_eq_false (show ¬ k < 1088 by omega), Bool.false_and,
          BF64.toBitVec_zero, BitVec.getLsbD_zero]
  have hout : yState Y i = keccakF1600 (inState hk ks 0 i) := by
    refine Vector.ext fun l hl ↦ ?_
    simp only [yState, Vector.getElem_ofFn]
    rw [H.out i hi l hl, laneWord, lane_ofLane, LeanVM.Protocol.KeccakGkr.lane_eq _ hl]
  rw [BlockPerm, hout, keccakF1600_eq, hin]
where
  LvmKeccakWords_toBitVec_add (a b : K) : (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

/-- **A sponge segment of `KS`**: rows `a … a + nBlk L − 1`, the first starting a sponge and the
others continuing it, with the padding of the `L` bytes they carry pinned, output the contract's
Keccak-256 of those bytes. -/
theorem sponge_segment (H : SpongeRel hk ks Y msg cont) (a L : ℕ) (ha : a + nBlk L ≤ 2 ^ hk)
    (hfirst : cont a = false) (hin : ∀ i, 0 < i → i < nBlk L → cont (a + i) = true)
    (hpad : PadOk (fun i ↦ msgBytes msg (a + i)) L) :
    stDigest (yState Y (a + (nBlk L - 1))) =
      RecursionFast.keccakDigest (streamOf (fun i ↦ msgBytes msg (a + i)) L) := by
  refine absorb_sound L (fun i ↦ msgBytes msg (a + i)) (fun i ↦ prevState Y cont (a + i))
    (fun i ↦ yState Y (a + i)) (by simp [prevState, hfirst]) (fun i hi ↦ ?_) (fun i hi ↦ ?_) hpad
  · exact row_perm hk ks Y msg cont H (by omega)
  · simp only [prevState, hin (i + 1) (by omega) hi, ite_true,
      show a + (i + 1) - 1 = a + i by omega]

/-- **The trace digest** (BLUEPRINT §4.2): rows `0 … nBlk L − 1` carrying the stream
`0x54 ‖ traceBytes tr` (`L` bytes, padding pinned) output `traceDigest tr`. -/
theorem traceDigest_of_KS (H : SpongeRel hk ks Y msg cont) (L : ℕ) (hL : nBlk L ≤ 2 ^ hk)
    (hin : ∀ i, 0 < i → i < nBlk L → cont i = true) (hpad : PadOk (msgBytes msg) L)
    (tr : RecursionFast.Trace)
    (hstream : streamOf (msgBytes msg) L = RecursionFast.tagTrace :: RecursionFast.traceBytes tr) :
    stDigest (yState Y (nBlk L - 1)) = RecursionFast.traceDigest tr := by
  have h := sponge_segment hk ks Y msg cont H 0 L (by omega) H.cont0
    (fun i h1 h2 ↦ by simpa using hin i h1 h2) (by simpa using hpad)
  simp only [Nat.zero_add] at h
  rw [h, show (fun i ↦ msgBytes msg i) = msgBytes msg from rfl, hstream, RecursionFast.traceDigest]

/-- **The WOTS key leaf**: 32 rows from `a` carrying `0x4B ‖ enc64 j ‖ end₀ ‖ … ‖ end₁₃₂`
(4,265 bytes, padding pinned) output `wotsLeaf j ends`. -/
theorem wotsLeaf_of_KS (H : SpongeRel hk ks Y msg cont) (a : ℕ) (ha : a + 32 ≤ 2 ^ hk)
    (hfirst : cont a = false) (hin : ∀ i, 0 < i → i < 32 → cont (a + i) = true)
    (hpad : PadOk (fun i ↦ msgBytes msg (a + i)) 4265) (j : ℕ) (ends : List RecursionFast.Digest)
    (hmsg : streamOf (fun i ↦ msgBytes msg (a + i)) 4265 =
      RecursionFast.tagWotsLeaf :: RecursionFast.enc64 j ++ ends.flatMap Vector.toList) :
    stDigest (yState Y (a + 31)) = RecursionFast.wotsLeaf j ends := by
  have h := sponge_segment hk ks Y msg cont H a 4265 (by simpa [nBlk, RecursionFast.Keccak.rate] using ha)
    hfirst (fun i h1 h2 ↦ hin i h1 (by simpa [nBlk, RecursionFast.Keccak.rate] using h2)) hpad
  rw [show nBlk 4265 - 1 = 31 by simp [nBlk, RecursionFast.Keccak.rate], hmsg] at h
  exact h

/-- **A row that starts a sponge** is one block from the zero state (the one-block hashes:
`wotsStep_block`, `sigNode_block`, `leafStmt_block`, `nodeStmt_block`, `chainStep_block`). -/
theorem oneRow_perm (H : SpongeRel hk ks Y msg cont) {i : ℕ} (hi : i < 2 ^ hk)
    (hc : cont i = false) : BlockPerm (xorMsg zeroSt (msgBytes msg i)) (yState Y i) := by
  have := row_perm hk ks Y msg cont H hi
  simpa [prevState, hc] using this

/-- **A WOTS chain step row** (`wotsStep`, 43 bytes). -/
theorem wotsStep_of_KS (H : SpongeRel hk ks Y msg cont) {i : ℕ} (hi : i < 2 ^ hk)
    (hc : cont i = false) (j c s : ℕ) (x : RecursionFast.Digest)
    (h0 : msgBytes msg i 0 = RecursionFast.tagWots)
    (hj : ∀ k < 8, msgBytes msg i (1 + k) = (j / 256 ^ k).toUInt8)
    (hci : msgBytes msg i 9 = c.toUInt8) (hs : msgBytes msg i 10 = s.toUInt8)
    (hx : ∀ k (hk : k < 32), msgBytes msg i (11 + k) = x[k])
    (hpad : ∀ q, 43 ≤ q → q < RecursionFast.Keccak.rate → msgBytes msg i q = padAt 43 q) :
    stDigest (yState Y i) = RecursionFast.wotsStep j c s x :=
  wotsStep_block j c s x _ _ h0 hj hci hs hx hpad (oneRow_perm hk ks Y msg cont H hi hc)

/-- **A signature Merkle node row** (`sigNode`, 65 bytes). -/
theorem sigNode_of_KS (H : SpongeRel hk ks Y msg cont) {i : ℕ} (hi : i < 2 ^ hk)
    (hc : cont i = false) (l r : RecursionFast.Digest)
    (h0 : msgBytes msg i 0 = RecursionFast.tagSigNode)
    (hl : ∀ k (hk : k < 32), msgBytes msg i (1 + k) = l[k])
    (hr : ∀ k (hk : k < 32), msgBytes msg i (33 + k) = r[k])
    (hpad : ∀ q, 65 ≤ q → q < RecursionFast.Keccak.rate → msgBytes msg i q = padAt 65 q) :
    stDigest (yState Y i) = RecursionFast.sigNode l r :=
  sigNode_block l r _ _ h0 hl hr hpad (oneRow_perm hk ks Y msg cont H hi hc)

end Lvm.KG
