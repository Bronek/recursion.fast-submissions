-- New for lvm (WP-8): the chain table `CH` and `chain_of_CH` (BLUEPRINT §4.1, §11 A1, A6, A9).
import LvmKeccakCandidate
import LvmKSpongeDigests
import LvmKSpongeBits
import LvmKSpongePerm

/-!
# The chain table `CH` and the chain it proves

`CH` is a 64-slot block of `K` words on `h` row variables (`h = logN`, `2^20` rows at `P20`): word
`x + 2^h · slot` is slot `slot` of row `x`. Slots `0 … 24` hold the permutation input `in_x`
(`inState h col 0 x`, leanVM's reading), `25 … 49` the middle state, and `ys … ys + 3` (`ys = 52`
in `M3.v0`) the output lanes `Y_x[0..3]`.

* `pad43Bit y`, `pad43St y`: the first sponge block of `0x43 ‖ d` as a state, from the 256 bits `y` of
  `d` (bit `64 m + q` = bit `q` of lane `m`): `0x43` in bits `0 … 7`, `d` in bits `8 … 263`, the
  padding `0x01` at bit `264` (byte 33) and `0x80` at bit `1087` (byte 135). It is V_S's `pad43`.
* **`chainStep_pad43`**: `chainStep d = stDigest (keccakF (pad43St (digestBits d)))` (one block).
* `ChainRel`: what the table's constraints give (the Keccak GKR: `Y = keccakF(in)` on lanes 0–3 of
  every row; the link: `in_{x+1} = Pad43(Y_x)` for every `x + 1 < 2^h`, A9; the boundaries
  `in_0 = Pad43(s)` and `Y_{n−1} = hd`, A1).
* **`chain_of_CH`**: `1 ≤ n ≤ 2^h → ChainRel … → chainEnd s n = hd`, by induction on the rows.
* `LinkBits`, `ConstLanes`: the link as the shift sumcheck states it (lanes `0 … 7` bitwise, lanes
  `8 … 24` constant words); **`link_of_bits`**: together they are `ChainRel.link`.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakGkr Lvm.KSponge

/-! ## `Pad43` bitwise -/

/-- Bit `j < 1600` of the first sponge block of `0x43 ‖ d`, from the 256 bits `y` of `d`. -/
def pad43Bit (y : ℕ → Bool) (j : ℕ) : Bool :=
  if j < 8 then (0x43 : ℕ).testBit j
  else if j < 264 then y (j - 8)
  else j = 264 ∨ j = 1087

/-- The first sponge block of `0x43 ‖ d` as a state. -/
def pad43St (y : ℕ → Bool) : RecursionFast.Keccak.State := ofBits (pad43Bit y)

/-- The 256 bits of a digest: bit `j` is bit `j % 8` of byte `j / 8` (`false` past 256). -/
def digestBits (d : RecursionFast.Digest) (j : ℕ) : Bool :=
  if hj : j < 256 then (d[j / 8]'(by omega)).toBitVec.getLsbD (j % 8) else false

/-- The constant words of `Pad43` on lanes `8 … 24`: `0x80` in the top byte of lane 16. -/
def padConstLane (l : ℕ) : UInt64 := if l = 16 then (0x80 : UInt64) <<< 56 else 0

theorem pad43Bit_congr {y y' : ℕ → Bool} (h : ∀ j < 256, y j = y' j) (j : ℕ) :
    pad43Bit y j = pad43Bit y' j := by
  unfold pad43Bit
  split_ifs with h1 h2
  · rfl
  · exact h _ (by omega)
  · rfl

theorem pad43St_congr {y y' : ℕ → Bool} (h : ∀ j < 256, y j = y' j) : pad43St y = pad43St y' := by
  unfold pad43St
  rw [show pad43Bit y = pad43Bit y' from funext (pad43Bit_congr h)]

/-- `Pad43` is the zero state with its bytes absorbed (all its bits are in the rate). -/
theorem pad43St_eq_xorMsg (y : ℕ → Bool) :
    pad43St y = xorMsg zeroSt (msgOfBits (pad43Bit y)) := by
  have hz : ofBits (fun _ ↦ false) = zeroSt :=
    state_ext fun k hk ↦ by rw [stBit_ofBits _ hk, stBit_zeroSt]
  rw [← hz, pad43St]
  refine ofBits_eq_xorMsg fun k hk ↦ ?_
  simp only [Bool.false_xor]
  by_cases h : k < 1088
  · simp [h]
  · simp only [h, decide_false, Bool.false_and]
    unfold pad43Bit
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    simp only [decide_eq_false_iff_not, not_or]
    omega

theorem uint8_ext {a b : UInt8} (h : ∀ t < 8, a.toBitVec.getLsbD t = b.toBitVec.getLsbD t) : a = b :=
  UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq h)

/-- **A chain step is one permutation of `Pad43`.** -/
theorem chainStep_pad43 (d : RecursionFast.Digest) :
    RecursionFast.chainStep d =
      stDigest (RecursionFast.Keccak.keccakF (pad43St (digestBits d))) := by
  symm
  refine chainStep_block d (msgOfBits (pad43Bit (digestBits d))) _ ?_ ?_ ?_ ?_
  · refine uint8_ext fun t ht ↦ ?_
    rw [msgOfBits_bit _ _ ht]
    simp only [pad43Bit, Nat.mul_zero, Nat.zero_add, ht, ite_true]
    interval_cases t <;> decide
  · intro k hk
    refine uint8_ext fun t ht ↦ ?_
    rw [msgOfBits_bit _ _ ht]
    simp only [pad43Bit, digestBits]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), dite_eq_left (by omega)]
    simp only [show (8 * (1 + k) + t - 8) / 8 = k by omega, show (8 * (1 + k) + t - 8) % 8 = t by omega]
  · intro q h1 h2
    simp only [RecursionFast.Keccak.rate] at h2
    refine uint8_ext fun t ht ↦ ?_
    rw [msgOfBits_bit _ _ ht]
    simp only [pad43Bit, padAt, RecursionFast.Keccak.rate]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    by_cases hq : q = 33
    · subst hq
      simp only [ite_true]
      interval_cases t <;> decide
    · simp only [hq, ite_false]
      by_cases hl : q = 135
      · subst hl
        simp only [ite_true]
        interval_cases t <;> decide
      · have hl' : ¬ q % 136 = 136 - 1 := by omega
        have : ¬ (8 * q + t = 264 ∨ 8 * q + t = 1087) := by omega
        simp [hl', this]
  · rw [BlockPerm, ← pad43St_eq_xorMsg]

/-! ## The table -/

variable (h ys : ℕ) (col : ℕ → K)

/-- The 256 bits of row `x`'s output lanes `Y_x[0..3]` (slots `ys … ys + 3`). -/
def yBits (x j : ℕ) : Bool := (col (x + 2 ^ h * (ys + j / 64))).toBitVec.getLsbD (j % 64)

/-- **What `CH`'s constraints give** for a chain from `s` of `n` steps ending in `hd`. -/
structure ChainRel (s : RecursionFast.Digest) (n : ℕ) (hd : RecursionFast.Digest) : Prop where
  /-- The Keccak GKR (with the caller's lanes 0–3 tied to `Y`): `Y_x = keccakF(in_x)`, lanes 0–3. -/
  out : ∀ x < 2 ^ h, ∀ m < 4,
    col (x + 2 ^ h * (ys + m)) = laneWord (keccakF1600 (inState h col 0 x)) m
  /-- The link (every row but the last, A9): `in_{x+1} = Pad43(Y_x)`. -/
  link : ∀ x, x + 1 < 2 ^ h → inState h col 0 (x + 1) = pad43St (yBits h ys col x)
  /-- The start (25 word claims at row 0): `in_0 = Pad43(s)`. -/
  first : inState h col 0 0 = pad43St (digestBits s)
  /-- The end (4 word claims at row `n − 1`): `Y_{n−1} = hd`. -/
  last : ∀ m < 4, col (n - 1 + 2 ^ h * (ys + m)) =
    K.ofLane (RecursionFast.Keccak.blockLane hd.toArray m)

/-- State bit `k` of a row's input is the bit of its slot `k / 64`. -/
theorem stBit_inState (x : ℕ) {k : ℕ} (hk : k < 1600) :
    stBit (inState h col 0 x) k = (col (x + 2 ^ h * (k / 64))).toBitVec.getLsbD (k % 64) := by
  simp only [stBit, hk, dite_true, inState, Vector.getElem_ofFn, K.lane, Nat.mul_zero,
    Nat.zero_add]

/-- The contract's state bit is leanVM's `sbit`. -/
theorem stBit_eq_sbit (a : RecursionFast.Keccak.State) {k : ℕ} (hk : k < 1600) :
    stBit a k = sbit a k := by
  rw [stBit, dite_eq_left hk, sbit, lane_eq _ (by omega)]

theorem keccakF1600_eq' (a : RecursionFast.Keccak.State) :
    keccakF1600 a = RecursionFast.Keccak.keccakF a := keccakF1600_eq a

/-- The output bits of a row are the digest bits of its permutation. -/
theorem yBits_eq {x : ℕ}
    (hout : ∀ m < 4, col (x + 2 ^ h * (ys + m)) = laneWord (keccakF1600 (inState h col 0 x)) m)
    {j : ℕ} (hj : j < 256) :
    yBits h ys col x j =
      digestBits (stDigest (RecursionFast.Keccak.keccakF (inState h col 0 x))) j := by
  rw [yBits, hout _ (by omega), digestBits, dite_eq_left hj,
    stDigest_bit _ (by omega) (Nat.mod_lt _ (by decide)), keccakF1600_eq',
    show 8 * (j / 8) + j % 8 = j from Nat.div_add_mod j 8, stBit, dite_eq_left (by omega), laneWord,
    K.ofLane, lane_eq _ (by omega)]
  rfl

/-- **`chain_of_CH`**: a table satisfying `ChainRel` proves the chain. -/
theorem chain_of_CH {s hd : RecursionFast.Digest} {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ 2 ^ h)
    (H : ChainRel h ys col s n hd) : RecursionFast.chainEnd s n = hd := by
  let Yd : ℕ → RecursionFast.Digest :=
    fun x ↦ stDigest (RecursionFast.Keccak.keccakF (inState h col 0 x))
  have step : ∀ x < n, Yd x = RecursionFast.chainEnd s (x + 1) := by
    intro x
    induction x with
    | zero =>
      intro _
      simp only [Yd, H.first, ← chainStep_pad43]
      rfl
    | succ x ih =>
      intro _
      have hl := H.link x (by omega)
      have hy : pad43St (yBits h ys col x) = pad43St (digestBits (Yd x)) :=
        pad43St_congr fun j hj ↦ yBits_eq h ys col (H.out x (by omega)) hj
      have ih' : Yd x = RecursionFast.chainEnd s (x + 1) := ih (by omega)
      show stDigest (RecursionFast.Keccak.keccakF (inState h col 0 (x + 1))) = _
      rw [hl, hy, ← chainStep_pad43, ih', RecursionFast.chainEnd, RecursionFast.chainEnd,
        Function.iterate_succ_apply' _ (x + 1)]
  have hs := step (n - 1) (by omega)
  rw [Nat.sub_add_cancel hn] at hs
  rw [← hs]
  refine digest_ext fun e he t ht ↦ ?_
  have hlast := H.last (e / 8) (by omega)
  rw [H.out _ (by omega) _ (by omega), laneWord] at hlast
  have hw := congrArg (fun a : K ↦ a.toBitVec.getLsbD (8 * (e % 8) + t)) hlast
  simp only [K.ofLane, BF64.toBitVec_ofBitVec] at hw
  rw [stDigest_bit _ he ht, ← keccakF1600_eq', stBit_eq_sbit _ (by omega), sbit,
    show (8 * e + t) / 64 = e / 8 by omega, show (8 * e + t) % 64 = 8 * (e % 8) + t by omega,
    hw, blockLane_bit _ _ (by omega),
    show 8 * (e / 8) + (8 * (e % 8) + t) / 8 = e by omega,
    show (8 * (e % 8) + t) % 8 = t by omega]
  simp [Array.getD, he]

/-! ## The link as the shift sumcheck states it -/

/-- The link on lanes `0 … 7`, bit by bit (rows `x + 1 < 2^h`). -/
def LinkBits : Prop :=
  ∀ x, x + 1 < 2 ^ h → ∀ l < 8, ∀ p < 64,
    (col (x + 1 + 2 ^ h * l)).toBitVec.getLsbD p = pad43Bit (yBits h ys col x) (64 * l + p)

/-- The constant lanes `8 … 24` of `Pad43` on every row. -/
def ConstLanes : Prop :=
  ∀ x < 2 ^ h, ∀ l, 8 ≤ l → l < 25 → col (x + 2 ^ h * l) = K.ofLane (padConstLane l)

/-- **The link from its two parts**: lanes `0 … 7` bitwise and lanes `8 … 24` constant. -/
theorem link_of_bits (hb : LinkBits h ys col) (hc : ConstLanes h col) :
    ∀ x, x + 1 < 2 ^ h → inState h col 0 (x + 1) = pad43St (yBits h ys col x) := by
  intro x hx
  refine state_ext fun k hk ↦ ?_
  rw [stBit_inState h col _ hk, pad43St, stBit_ofBits _ hk]
  by_cases hl : k / 64 < 8
  · have := hb x hx (k / 64) hl (k % 64) (Nat.mod_lt _ (by decide))
    rwa [show 64 * (k / 64) + k % 64 = k from Nat.div_add_mod k 64] at this
  · rw [hc (x + 1) hx (k / 64) (by omega) (by omega)]
    have hp : pad43Bit (yBits h ys col x) k = decide (k = 1087) := by
      unfold pad43Bit
      rw [ite_eq_right (show ¬ k < 8 by omega), ite_eq_right (show ¬ k < 264 by omega)]
      by_cases h1087 : k = 1087
      · simp [h1087]
      · simp [h1087]; omega
    rw [hp]
    have hk' : k % 64 < 64 := Nat.mod_lt _ (by decide)
    by_cases h16 : k / 64 = 16
    · have e : (k = 1087) ↔ k % 64 = 63 := by omega
      simp only [padConstLane, h16, ite_true, K.ofLane, BF64.toBitVec_ofBitVec, e]
      generalize k % 64 = z at hk' ⊢
      interval_cases z <;> decide
    · have e : ¬ k = 1087 := by omega
      simp [padConstLane, h16, e, K.ofLane]

end Lvm.KG
