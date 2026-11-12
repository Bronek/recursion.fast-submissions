import LvmBits
import LvmKSponge

/-!
# The message lanes of the signature hashes (byte layouts of the unaligned prefixes)

New for lvm (WP-12). The circuit writes each Keccak message as 17 lanes per block (`K` words); the
sponge reads byte `q` of a message as byte `q mod 8` of lane `q / 8` (`laneByte`). This module
proves, per hash kind, that lanes built from byte-shifted parts (the `BITS` outputs `shl`/`shr`)
and constants carry exactly the contract's bytes, in the form the K2-LS block lemmas
(`LvmKSpongeDigests`: `wotsStep_block`, `two_block`, `leafStmt_block`, `wotsLeaf_bytes`) take.

* `byte_shift`, `lane_shift_byte`: a lane `(A >>> (64 − 8r)) ^^^ (B <<< 8r)` holds the byte stream of
  the words `…, A, B, …` moved up by `r` bytes.
* `wotsStep_lanes` (43 B, `0x57 ‖ enc64 j ‖ i ‖ s ‖ x`: an 11-byte prefix, `x` moved by 3 bytes),
  `two_lanes` (65 B, `tag ‖ a ‖ b`: `sigNode`, `nodeStmt`), `leafStmt_lanes` (41 B,
  `0x4C ‖ h ‖ enc64 n`), `wotsLeaf_lanes` (4,265 B over 32 blocks, `0x4B ‖ enc64 j ‖ ends`).
-/

set_option autoImplicit false

namespace Lvm.Wots

open RecursionFast RecursionFast.Keccak Lvm.Bits Lvm.KSponge

/-- Byte `q` of a lane sequence. -/
def laneByte (lane : ℕ → UInt64) (q : ℕ) : UInt8 := byteW (lane (q / 8)) (q % 8)

/-- The digest whose byte `k` is byte `k mod 8` of word `k / 8`. -/
def digOfW (w : ℕ → UInt64) : Digest := Vector.ofFn fun k : Fin 32 => byteW (w (k / 8)) (k % 8)

theorem digOfW_get (w : ℕ → UInt64) {k : ℕ} (hk : k < 32) :
    (digOfW w)[k] = byteW (w (k / 8)) (k % 8) := by
  simp [digOfW]

/-- Byte `k` of a word is the `k`-th little-endian byte of its number. -/
theorem byteW_toNat (w : UInt64) {k : ℕ} (hk : k < 8) : byteW w k = (w.toNat / 256 ^ k).toUInt8 := by
  apply UInt8.toNat_inj.mp
  have h64 : 8 * k % 64 = 8 * k := Nat.mod_eq_of_lt (by omega)
  have h8 : (8 * k) % 2 ^ 64 = 8 * k := Nat.mod_eq_of_lt (by omega)
  simp [byteW, Nat.shiftRight_eq_div_pow, h64, pow_mul]

/-- **A byte-shifted lane** (`0 < r < 8`): byte `t` of `(A >>> (64 − 8r)) ^^^ (B <<< 8r)` is byte
`t + 8 − r` of `A` below `r`, else byte `t − r` of `B`. -/
theorem byte_shift {r : ℕ} (hr0 : 0 < r) (hr : r < 8) (A B : UInt64) {t : ℕ} (ht : t < 8) :
    byteW ((A >>> (64 - 8 * r).toUInt64) ^^^ (B <<< (8 * r).toUInt64)) t =
      if t < r then byteW A (t + 8 - r) else byteW B (t - r) := by
  rw [byteW_xor _ _ ht, show 64 - 8 * r = 8 * (8 - r) by omega, byteW_shr8 _ (by omega) ht,
    byteW_shl8 _ hr ht]
  split_ifs <;> first | (exfalso; omega) | simp only [UInt8.xor_zero, UInt8.zero_xor]
  congr 1; omega

/-- Byte `t` of lane `l`. -/
theorem laneByte_8 (lane : ℕ → UInt64) (l : ℕ) {t : ℕ} (ht : t < 8) :
    laneByte lane (8 * l + t) = byteW (lane l) t := by
  unfold laneByte; rw [show (8 * l + t) / 8 = l by omega, show (8 * l + t) % 8 = t by omega]

/-- **The stream form**: a lane `l ≥ 1` of the shifted words `X` holds the bytes of `X` at offset
`8l + t − r`. -/
theorem lane_shift_byte {r : ℕ} (hr0 : 0 < r) (hr : r < 8) (X lane : ℕ → UInt64) {l : ℕ} (hl : 1 ≤ l)
    (h : lane l = (X (l - 1) >>> (64 - 8 * r).toUInt64) ^^^ (X l <<< (8 * r).toUInt64)) {t : ℕ}
    (ht : t < 8) : laneByte lane (8 * l + t) = laneByte X (8 * l + t - r) := by
  rw [laneByte_8 _ _ ht, h, byte_shift hr0 hr _ _ ht]
  by_cases h : t < r
  · simp only [h, ↓reduceIte]
    rw [show 8 * l + t - r = 8 * (l - 1) + (t + 8 - r) by omega,
      laneByte_8 _ _ (by omega)]
  · simp only [h, ↓reduceIte]
    rw [show 8 * l + t - r = 8 * l + (t - r) by omega,
      laneByte_8 _ _ (by omega)]

/-! ## Helpers for the message layouts -/

/-- Dropping the first lane. -/
theorem laneByte_add8 (lane : ℕ → UInt64) (q : ℕ) :
    laneByte lane (8 + q) = laneByte (fun l => lane (l + 1)) q := by
  unfold laneByte; rw [show (8 + q) / 8 = q / 8 + 1 by omega, show (8 + q) % 8 = q % 8 by omega]

theorem byteW_one {t : ℕ} (ht : t < 8) : byteW 1 t = if t = 0 then 1 else 0 := by
  interval_cases t <;> decide

theorem byteW_top {t : ℕ} (ht : t < 8) :
    byteW 0x8000000000000000 t = if t = 7 then 0x80 else 0 := by
  interval_cases t <;> decide

/-- High bytes of a small word vanish. -/
theorem byteW_small (w : UInt64) {n k : ℕ} (hk : k < 8) (hw : w.toNat < 256 ^ n) (hnk : n ≤ k) :
    byteW w k = 0 := by
  rw [byteW_toNat w hk, Nat.div_eq_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hnk))]
  rfl

theorem padAt_self {L : ℕ} (h : L % 136 ≠ 135) : padAt L L = 1 := by
  unfold padAt; simp [Keccak.rate, h]

theorem padAt_mid {L q : ℕ} (h1 : q ≠ L) (h2 : q % 136 ≠ 135) : padAt L q = 0 := by
  unfold padAt; simp [Keccak.rate, h1, h2]

theorem padAt_end {L q : ℕ} (h1 : q ≠ L) (h2 : q % 136 = 135) : padAt L q = 0x80 := by
  unfold padAt; simp [Keccak.rate, h1, h2]

/-- **A byte stream moved up by `r` bytes**: lane 0 is a constant `c` (bytes below `r`) and
`W 0 <<< 8r`, lanes `1 … n` the shifted words. -/
theorem stream_byte {r : ℕ} (hr0 : 0 < r) (hr : r < 8) (W lane : ℕ → UInt64) (c : UInt64) (n : ℕ)
    (h0 : lane 0 = c ^^^ (W 0 <<< (8 * r).toUInt64)) (hc : ∀ t, r ≤ t → t < 8 → byteW c t = 0)
    (hl : ∀ l, 1 ≤ l → l ≤ n →
      lane l = (W (l - 1) >>> (64 - 8 * r).toUInt64) ^^^ (W l <<< (8 * r).toUInt64))
    {k : ℕ} (hk : r + k < 8 * (n + 1)) : laneByte lane (r + k) = laneByte W k := by
  obtain ⟨l, t, ht, hq⟩ : ∃ l t, t < 8 ∧ r + k = 8 * l + t :=
    ⟨_, _, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod _ _).symm⟩
  rw [hq]
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · rw [laneByte_8 _ _ ht, h0, byteW_xor _ _ ht, hc _ (by omega) ht, byteW_shl8 _ hr ht]
    simp only [show r ≤ t by omega, ↓reduceIte, UInt8.zero_xor]
    rw [show k = 8 * 0 + k by omega, laneByte_8 _ _ (by omega)]
    congr 1; omega
  · rw [lane_shift_byte hr0 hr W lane hl1 (hl _ hl1 (by omega)) ht]; congr 1; omega

/-- **The padded tail of a block**: the stream's terminator `1` at `L`, zero lanes `l0 … l1 − 1`,
the top bit in lane `l1`, all in the block ending at lane `l1`. -/
theorem pad_all (lane : ℕ → UInt64) {L l0 l1 : ℕ} (hL : L < 8 * l0) (hl01 : l0 ≤ l1)
    (hblk : (8 * l1 + 8) % 136 = 0) (hL0 : 8 * l1 + 8 ≤ L + 136)
    (hfirst : ∀ q, L ≤ q → q < 8 * l0 → laneByte lane q = if q = L then 1 else 0)
    (hz : ∀ l, l0 ≤ l → l < l1 → lane l = 0) (htop : lane l1 = 0x8000000000000000) :
    ∀ q, L ≤ q → q < 8 * l1 + 8 → laneByte lane q = padAt L q := by
  intro q h1 h2
  by_cases hq : q < 8 * l0
  · rw [hfirst q h1 hq]
    split_ifs with he
    · subst he; exact (padAt_self (by omega)).symm
    · exact (padAt_mid he (by omega)).symm
  · unfold laneByte
    by_cases hl : q / 8 < l1
    · rw [hz _ (by omega) hl, byteW_zero, padAt_mid (by omega) (by omega)]
    · rw [show q / 8 = l1 by omega, htop, byteW_top (Nat.mod_lt _ (by norm_num))]
      split_ifs with h7
      · exact (padAt_end (by omega) (by omega)).symm
      · exact (padAt_mid (by omega) (by omega)).symm

/-- **`wotsStep`'s lanes** (`tagWots ‖ enc64 j ‖ i ‖ s ‖ x ‖ pad`, 43 bytes): the index `j < 2^16`
moved by one byte, the constants `i`, `s` at bytes 9 and 10, the four lanes of `x` moved by three
bytes, the padding. Conclusions: exactly the hypotheses of `wotsStep_block`. -/
theorem wotsStep_lanes (jw : UInt64) (hj : jw.toNat < 2 ^ 16) (i s : ℕ) (hi : i < 256)
    (hs : s < 256) (x lane : ℕ → UInt64)
    (h0 : lane 0 = (jw <<< (8 : ℕ).toUInt64) ^^^ 0x57)
    (h1 : lane 1 = ((i.toUInt64 <<< (8 : ℕ).toUInt64) ^^^ (s.toUInt64 <<< (16 : ℕ).toUInt64)) ^^^
      (x 0 <<< (24 : ℕ).toUInt64))
    (hx : ∀ k, 1 ≤ k → k < 4 → lane (k + 1) = (x (k - 1) >>> (40 : ℕ).toUInt64) ^^^ (x k <<< (24 : ℕ).toUInt64))
    (h5 : lane 5 = (x 3 >>> (40 : ℕ).toUInt64) ^^^ 0x1000000)
    (hz : ∀ l, 6 ≤ l → l < 16 → lane l = 0) (h16 : lane 16 = 0x8000000000000000) :
    laneByte lane 0 = tagWots ∧ (∀ k < 8, laneByte lane (1 + k) = (jw.toNat / 256 ^ k).toUInt8) ∧
      laneByte lane 9 = i.toUInt8 ∧ laneByte lane 10 = s.toUInt8 ∧
      (∀ k (hk : k < 32), laneByte lane (11 + k) = (digOfW x)[k]) ∧
      (∀ q, 43 ≤ q → q < rate → laneByte lane q = padAt 43 q) := by
  have hrate : rate = 136 := rfl
  obtain ⟨W, hWx, hW4⟩ : ∃ W : ℕ → UInt64, (∀ j < 4, W j = x j) ∧ W 4 = 1 :=
    ⟨fun j => if j < 4 then x j else 1, fun j hj => by simp [hj], rfl⟩
  have hiN : i.toUInt64.toNat = i := by simp; omega
  have hsN : s.toUInt64.toNat = s := by simp; omega
  have hi0 : ∀ t, 1 ≤ t → t < 8 → byteW i.toUInt64 t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by omega) h1
  have hs0 : ∀ t, 1 ≤ t → t < 8 → byteW s.toUInt64 t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by omega) h1
  have hc : ∀ t < 8, byteW ((i.toUInt64 <<< (8 : ℕ).toUInt64) ^^^ (s.toUInt64 <<< (16 : ℕ).toUInt64)) t
      = (if 1 ≤ t then byteW i.toUInt64 (t - 1) else 0) ^^^
        (if 2 ≤ t then byteW s.toUInt64 (t - 2) else 0) := fun t ht => by
    rw [byteW_xor _ _ ht]
    exact congrArg₂ _ (byteW_shl8 _ (s := 1) (by norm_num) ht) (byteW_shl8 _ (s := 2) (by norm_num) ht)
  have hb0 : ∀ t < 8, byteW (lane 0) t =
      (if 1 ≤ t then byteW jw (t - 1) else 0) ^^^ byteW (0x57 : UInt64) t := fun t ht => by
    rw [h0, byteW_xor _ _ ht]
    exact congrArg (· ^^^ _) (byteW_shl8 _ (s := 1) (by norm_num) ht)
  have hb1 : ∀ t < 8, byteW (lane 1) t =
      ((if 1 ≤ t then byteW i.toUInt64 (t - 1) else 0) ^^^
        (if 2 ≤ t then byteW s.toUInt64 (t - 2) else 0)) ^^^
        (if 3 ≤ t then byteW (x 0) (t - 3) else 0) := fun t ht => by
    rw [h1, byteW_xor _ _ ht, hc t ht]
    exact congrArg (_ ^^^ ·) (byteW_shl8 _ (s := 3) (by norm_num) ht)
  have hS : ∀ k, 3 + k < 40 → laneByte lane (8 + (3 + k)) = laneByte W k := fun k hk => by
    rw [laneByte_add8]
    refine stream_byte (by norm_num) (by norm_num) W (fun l => lane (l + 1))
      ((i.toUInt64 <<< (8 : ℕ).toUInt64) ^^^ (s.toUInt64 <<< (16 : ℕ).toUInt64)) 4
      (by show lane 1 = _; rw [h1, hWx 0 (by norm_num)]) (fun t h1 h2 => ?_) (fun l h1 h2 => ?_) hk
    · rw [hc t h2]
      simp only [show 1 ≤ t by omega, show 2 ≤ t by omega, ↓reduceIte, hi0 (t - 1) (by omega) (by omega),
        hs0 (t - 2) (by omega) (by omega), UInt8.xor_zero]
    · show lane (l + 1) = _
      rcases Nat.lt_or_ge l 4 with h4 | h4
      · rw [hx l h1 h4, hWx _ (by omega), hWx _ h4]
      · obtain rfl : l = 4 := by omega
        rw [show (4 : ℕ) - 1 = 3 from rfl, h5, hWx 3 (by norm_num), hW4]; rfl
  refine ⟨?_, fun k hk => ?_, ?_, ?_, fun k hk => ?_, fun q hq1 hq2 => ?_⟩
  · show byteW (lane 0) 0 = _
    rw [hb0 0 (by norm_num)]; simp [tagWots]; decide
  · rcases Nat.lt_or_ge k 7 with h7 | h7
    · rw [show 1 + k = 8 * 0 + (1 + k) by omega, laneByte_8 _ _ (by omega), hb0 _ (by omega),
        byteW_small (0x57 : UInt64) (n := 1) (by omega) (by decide) (by omega)]
      simp only [show 1 ≤ 1 + k by omega, ↓reduceIte, UInt8.xor_zero, Nat.add_sub_cancel_left]
      exact byteW_toNat _ (by omega)
    · obtain rfl : k = 7 := by omega
      rw [Nat.div_eq_of_lt (by omega)]
      show byteW (lane 1) 0 = _
      rw [hb1 0 (by norm_num)]; simp
  · show byteW (lane 1) 1 = _
    rw [hb1 1 (by norm_num), byteW_toNat i.toUInt64 (k := 1 - 1) (by norm_num), hiN]
    simp
  · show byteW (lane 1) 2 = _
    rw [hb1 2 (by norm_num), hi0 (2 - 1) (by norm_num) (by norm_num),
      byteW_toNat s.toUInt64 (k := 2 - 2) (by norm_num), hsN]
    simp
  · rw [show 11 + k = 8 + (3 + k) by omega, hS k (by omega), digOfW_get x hk]
    unfold laneByte; rw [hWx _ (by omega)]
  · refine pad_all lane (l0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun q h1 h2 => ?_) hz h16 q hq1 (by omega)
    rw [show q = 8 + (3 + (q - 11)) by omega, hS _ (by omega)]
    unfold laneByte
    rw [show (q - 11) / 8 = 4 by omega, hW4, byteW_one (Nat.mod_lt _ (by norm_num))]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **Two digests after a tag** (65 bytes: `sigNode`, `nodeStmt`): conclusions are the hypotheses
of `two_block`. -/
theorem two_lanes (tag : UInt8) (a b lane : ℕ → UInt64)
    (h0 : lane 0 = (a 0 <<< (8 : ℕ).toUInt64) ^^^ tag.toUInt64)
    (ha : ∀ k, 1 ≤ k → k < 4 → lane k = (a (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (a k <<< (8 : ℕ).toUInt64))
    (h4 : lane 4 = (a 3 >>> (56 : ℕ).toUInt64) ^^^ (b 0 <<< (8 : ℕ).toUInt64))
    (hb : ∀ k, 1 ≤ k → k < 4 →
      lane (4 + k) = (b (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (b k <<< (8 : ℕ).toUInt64))
    (h8 : lane 8 = (b 3 >>> (56 : ℕ).toUInt64) ^^^ 0x100)
    (hz : ∀ l, 9 ≤ l → l < 16 → lane l = 0) (h16 : lane 16 = 0x8000000000000000) :
    laneByte lane 0 = tag ∧ (∀ k (hk : k < 32), laneByte lane (1 + k) = (digOfW a)[k]) ∧
      (∀ k (hk : k < 32), laneByte lane (33 + k) = (digOfW b)[k]) ∧
      (∀ q, 65 ≤ q → q < rate → laneByte lane q = padAt 65 q) := by
  have hrate : rate = 136 := rfl
  obtain ⟨W, hWa, hWb, hW8⟩ : ∃ W : ℕ → UInt64, (∀ j < 4, W j = a j) ∧
      (∀ j, 4 ≤ j → j < 8 → W j = b (j - 4)) ∧ W 8 = 1 :=
    ⟨fun j => if j < 4 then a j else if j < 8 then b (j - 4) else 1,
      fun j hj => by simp [hj], fun j h1 h2 => by simp [h2, show ¬ j < 4 by omega], rfl⟩
  have hc : ∀ t, 1 ≤ t → t < 8 → byteW tag.toUInt64 t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by have := tag.toNat_lt; simp; omega) h1
  have hS : ∀ k, 1 + k < 72 → laneByte lane (1 + k) = laneByte W k := fun k hk => by
    refine stream_byte (by norm_num) (by norm_num) W lane tag.toUInt64 8
      (by rw [h0, hWa 0 (by norm_num), UInt64.xor_comm]) hc (fun l h1 h2 => ?_) hk
    rcases (show l < 4 ∨ l = 4 ∨ (4 < l ∧ l < 8) ∨ l = 8 by omega) with h | h | h | h
    · rw [ha l h1 h, hWa _ (by omega), hWa _ h]
    · subst h
      rw [show (4 : ℕ) - 1 = 3 from rfl, h4, hWa 3 (by norm_num), hWb 4 (by norm_num) (by norm_num)]
    · have := hb (l - 4) (by omega) (by omega)
      rw [show 4 + (l - 4) = l by omega] at this
      rw [this, hWb _ (by omega) (by omega), hWb _ (by omega) (by omega),
        show l - 1 - 4 = l - 4 - 1 by omega]
    · subst h
      rw [show (8 : ℕ) - 1 = 7 from rfl, h8, hWb 7 (by norm_num) (by norm_num), hW8]; rfl
  refine ⟨?_, fun k hk => ?_, fun k hk => ?_, fun q hq1 hq2 => ?_⟩
  · show byteW (lane 0) 0 = _
    rw [h0, byteW_xor _ _ (by norm_num), show (8 : ℕ) = 8 * 1 from rfl,
      byteW_shl8 _ (by norm_num) (by norm_num), byteW_toNat tag.toUInt64 (k := 0) (by norm_num)]
    simp
  · rw [hS k (by omega), digOfW_get a hk]
    unfold laneByte; rw [hWa _ (by omega)]
  · rw [show 33 + k = 1 + (32 + k) by omega, hS _ (by omega), digOfW_get b hk]
    unfold laneByte
    rw [hWb _ (by omega) (by omega), show (32 + k) / 8 - 4 = k / 8 by omega,
      show (32 + k) % 8 = k % 8 by omega]
  · refine pad_all lane (l0 := 9) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun q h1 h2 => ?_) hz h16 q hq1 (by omega)
    rw [show q = 1 + (q - 1) by omega, hS _ (by omega)]
    unfold laneByte
    rw [show (q - 1) / 8 = 8 by omega, hW8, byteW_one (Nat.mod_lt _ (by norm_num))]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **`leafStmt`'s lanes** (`tagLeaf ‖ h ‖ enc64 n ‖ pad`, 41 bytes): conclusions are the
hypotheses of `leafStmt_block`. -/
theorem leafStmt_lanes (h : ℕ → UInt64) (nw : UInt64) (lane : ℕ → UInt64)
    (h0 : lane 0 = (h 0 <<< (8 : ℕ).toUInt64) ^^^ 0x4C)
    (hh : ∀ k, 1 ≤ k → k < 4 → lane k = (h (k - 1) >>> (56 : ℕ).toUInt64) ^^^ (h k <<< (8 : ℕ).toUInt64))
    (h4 : lane 4 = (h 3 >>> (56 : ℕ).toUInt64) ^^^ (nw <<< (8 : ℕ).toUInt64))
    (h5 : lane 5 = (nw >>> (56 : ℕ).toUInt64) ^^^ 0x100)
    (hz : ∀ l, 6 ≤ l → l < 16 → lane l = 0) (h16 : lane 16 = 0x8000000000000000) :
    laneByte lane 0 = tagLeaf ∧ (∀ k (hk : k < 32), laneByte lane (1 + k) = (digOfW h)[k]) ∧
      (∀ k < 8, laneByte lane (33 + k) = (nw.toNat / 256 ^ k).toUInt8) ∧
      (∀ q, 41 ≤ q → q < rate → laneByte lane q = padAt 41 q) := by
  have hrate : rate = 136 := rfl
  obtain ⟨W, hWh, hW4, hW5⟩ : ∃ W : ℕ → UInt64, (∀ j < 4, W j = h j) ∧ W 4 = nw ∧ W 5 = 1 :=
    ⟨fun j => if j < 4 then h j else if j = 4 then nw else 1, fun j hj => by simp [hj], rfl, rfl⟩
  have hc : ∀ t, 1 ≤ t → t < 8 → byteW (0x4C : UInt64) t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by decide) h1
  have hS : ∀ k, 1 + k < 48 → laneByte lane (1 + k) = laneByte W k := fun k hk => by
    refine stream_byte (by norm_num) (by norm_num) W lane 0x4C 5
      (by rw [h0, hWh 0 (by norm_num), UInt64.xor_comm]) hc (fun l h1 h2 => ?_) hk
    rcases (show l < 4 ∨ l = 4 ∨ l = 5 by omega) with hl | hl | hl
    · rw [hh l h1 hl, hWh _ (by omega), hWh _ hl]
    · subst hl
      rw [show (4 : ℕ) - 1 = 3 from rfl, h4, hWh 3 (by norm_num), hW4]
    · subst hl
      rw [show (5 : ℕ) - 1 = 4 from rfl, h5, hW4, hW5]; rfl
  refine ⟨?_, fun k hk => ?_, fun k hk => ?_, fun q hq1 hq2 => ?_⟩
  · show byteW (lane 0) 0 = _
    rw [h0, byteW_xor _ _ (by norm_num), show (8 : ℕ) = 8 * 1 from rfl,
      byteW_shl8 _ (by norm_num) (by norm_num)]
    simp [tagLeaf]; decide
  · rw [hS k (by omega), digOfW_get h hk]
    unfold laneByte; rw [hWh _ (by omega)]
  · rw [show 33 + k = 1 + (32 + k) by omega, hS _ (by omega)]
    unfold laneByte
    rw [show (32 + k) / 8 = 4 by omega, hW4, show (32 + k) % 8 = k by omega, byteW_toNat _ hk]
  · refine pad_all lane (l0 := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun q h1 h2 => ?_) hz h16 q hq1 (by omega)
    rw [show q = 1 + (q - 1) by omega, hS _ (by omega)]
    unfold laneByte
    rw [show (q - 1) / 8 = 5 by omega, hW5, byteW_one (Nat.mod_lt _ (by norm_num))]
    split_ifs <;> first | rfl | (exfalso; omega)

/-- **The WOTS key leaf's lanes** (`tagWotsLeaf ‖ enc64 j ‖ end₀ ‖ … ‖ end₁₃₂ ‖ pad`, 4,265 bytes,
544 lanes = 32 blocks): the index `j < 2^16` and the 532 end lanes `E` moved by one byte. The
blocked byte map `m u q = laneByte lane (136 u + q)` meets the hypotheses of `wotsLeaf_bytes` and
`PadOk`. -/
theorem wotsLeaf_lanes (jw : UInt64) (hj : jw.toNat < 2 ^ 16) (E lane : ℕ → UInt64)
    (h0 : lane 0 = (jw <<< (8 : ℕ).toUInt64) ^^^ 0x4B) (h1 : lane 1 = E 0 <<< (8 : ℕ).toUInt64)
    (hE : ∀ m, 2 ≤ m → m ≤ 532 →
      lane m = (E (m - 2) >>> (56 : ℕ).toUInt64) ^^^ (E (m - 1) <<< (8 : ℕ).toUInt64))
    (h533 : lane 533 = (E 531 >>> (56 : ℕ).toUInt64) ^^^ 0x100)
    (hz : ∀ l, 534 ≤ l → l < 543 → lane l = 0) (h543 : lane 543 = 0x8000000000000000) :
    let mb : ℕ → ℕ → UInt8 := fun u q => laneByte lane (rate * u + q)
    mb 0 0 = tagWotsLeaf ∧
      (∀ k < 8, mb ((1 + k) / rate) ((1 + k) % rate) = (jw.toNat / 256 ^ k).toUInt8) ∧
      (∀ i < 133, ∀ k < 32, mb ((9 + 32 * i + k) / rate) ((9 + 32 * i + k) % rate) =
        byteW (E (4 * i + k / 8)) (k % 8)) ∧
      PadOk mb 4265 := by
  have hrate : rate = 136 := rfl
  intro mb
  have hmb : ∀ p, mb (p / rate) (p % rate) = laneByte lane p := fun p => by
    show laneByte lane (rate * (p / rate) + p % rate) = _
    rw [Nat.div_add_mod]
  obtain ⟨W, hW0, hWE, hW533⟩ : ∃ W : ℕ → UInt64, W 0 = jw ∧
      (∀ j, 1 ≤ j → j ≤ 532 → W j = E (j - 1)) ∧ W 533 = 1 :=
    ⟨fun j => if j = 0 then jw else if j ≤ 532 then E (j - 1) else 1, rfl,
      fun j h1 h2 => by simp [h2, show j ≠ 0 by omega], rfl⟩
  have hjs : jw >>> (56 : ℕ).toUInt64 = 0 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, UInt64.toNat_zero]
    exact Nat.div_eq_of_lt (lt_of_lt_of_le hj (by simp))
  have hc : ∀ t, 1 ≤ t → t < 8 → byteW (0x4B : UInt64) t = 0 := fun t h1 h2 =>
    byteW_small _ (n := 1) h2 (by decide) h1
  have hS : ∀ k, 1 + k < 8 * 534 → laneByte lane (1 + k) = laneByte W k := fun k hk => by
    refine stream_byte (by norm_num) (by norm_num) W lane 0x4B 533
      (by rw [h0, hW0, UInt64.xor_comm]) hc (fun l hl1 hl2 => ?_) hk
    rcases (show l = 1 ∨ (2 ≤ l ∧ l ≤ 532) ∨ l = 533 by omega) with hl | hl | hl
    · subst hl
      rw [show (1 : ℕ) - 1 = 0 from rfl, h1, hW0, hWE 1 (by norm_num) (by norm_num)]
      show _ = (jw >>> (56 : ℕ).toUInt64) ^^^ _
      rw [hjs, UInt64.zero_xor]
    · rw [hE l hl.1 hl.2, hWE _ (by omega) (by omega), hWE _ (by omega) (by omega),
        show l - 1 - 1 = l - 2 by omega]
    · subst hl
      rw [show (533 : ℕ) - 1 = 532 from rfl, h533, hWE 532 (by norm_num) (by norm_num), hW533]; rfl
  refine ⟨?_, fun k hk => ?_, fun i hi k hk => ?_, fun p hp1 hp2 => ?_⟩
  · show laneByte lane (rate * 0 + 0) = _
    show byteW (lane 0) 0 = _
    rw [h0, byteW_xor _ _ (by norm_num), show (8 : ℕ) = 8 * 1 from rfl,
      byteW_shl8 _ (by norm_num) (by norm_num)]
    simp [tagWotsLeaf]; decide
  · rw [hmb, hS k (by omega)]
    unfold laneByte
    rw [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, hW0, byteW_toNat _ hk]
  · rw [hmb, show 9 + 32 * i + k = 1 + (8 + 32 * i + k) by omega, hS _ (by omega)]
    unfold laneByte
    rw [hWE _ (by omega) (by omega), show (8 + 32 * i + k) / 8 - 1 = 4 * i + k / 8 by omega,
      show (8 + 32 * i + k) % 8 = k % 8 by omega]
  · have hn : rate * nBlk 4265 = 4352 := by decide
    rw [hmb]
    refine pad_all lane (l0 := 534) (l1 := 543) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (fun q h1 h2 => ?_) hz h543 p hp1 (by omega)
    rw [show q = 1 + (q - 1) by omega, hS _ (by omega)]
    unfold laneByte
    rw [show (q - 1) / 8 = 533 by omega, hW533, byteW_one (Nat.mod_lt _ (by norm_num))]
    split_ifs <;> first | rfl | (exfalso; omega)

end Lvm.Wots
