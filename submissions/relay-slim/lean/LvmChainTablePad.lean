-- New for lvm (WP-8): V_S's `pad43` lane formulas (`LvmDecide`) are the lanes of `pad43St` (`LvmChainTable`).
import LvmChainTable

/-!
# `Pad43` on lanes

V_S states the boundary claim `in_0 = Pad43(s)` as 25 word claims whose values are its `pad43`
(`LvmDecide`): from the four little-endian lanes `w` of `s`, lane 0 is `0x43 ||| w₀ << 8`, lanes
`1 … 3` are `w_{l−1} >> 56 ||| w_l << 8`, lane 4 is `w₃ >> 56 ||| 0x01 << 8`, lane 16 is `0x80 << 56`,
and the others are zero. **`lane_pad43St`** proves these are the lanes of `pad43St (digestBits s)`, the
state `ChainRel.first` speaks of. (`pad43Lane` is that formula on `UInt64`; V_S's version is the
same on `FK` words.)
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakGkr Lvm.KSponge

/-- V_S's `pad43` on 64-bit lanes, from the four lanes `w` of the digest. -/
def pad43Lane (w : ℕ → UInt64) (l : ℕ) : UInt64 :=
  if l = 0 then (0x43 : UInt64) ||| (w 0 <<< 8)
  else if l < 4 then (w (l - 1) >>> 56) ||| (w l <<< 8)
  else if l = 4 then (w 3 >>> 56) ||| ((0x01 : UInt64) <<< 8)
  else if l = 16 then (0x80 : UInt64) <<< 56 else 0

theorem shl8_bit (x : UInt64) {z : ℕ} (hz : z < 64) :
    (x <<< (8 : UInt64)).toBitVec.getLsbD z = (decide (8 ≤ z) && x.toBitVec.getLsbD (z - 8)) := by
  simp only [UInt64.toBitVec_shiftLeft, BitVec.getLsbD_shiftLeft]
  by_cases h : 8 ≤ z
  · simp [h, hz, show ¬ z < 8 by omega, BitVec.getLsbD_eq_getElem (show z - 8 < 64 by omega)]
  · simp [h, show z < 8 by omega]

theorem shr56_bit (x : UInt64) {z : ℕ} (hz : z < 64) :
    (x >>> (56 : UInt64)).toBitVec.getLsbD z = x.toBitVec.getLsbD (56 + z) := by
  simp [UInt64.toBitVec_shiftRight, hz]

theorem bit_ge (x : UInt64) {z : ℕ} (hz : 64 ≤ z) : x.toBitVec.getLsbD z = false :=
  BitVec.getLsbD_of_ge _ _ hz

theorem c43_bit : ∀ z < 64, (0x43 : UInt64).toBitVec.getLsbD z = (0x43 : ℕ).testBit z := by decide

theorem c01_bit : ∀ z < 64, ((0x01 : UInt64) <<< (8 : UInt64)).toBitVec.getLsbD z = decide (z = 8) := by
  decide

theorem c80_bit : ∀ z < 64, ((0x80 : UInt64) <<< (56 : UInt64)).toBitVec.getLsbD z = decide (z = 63) := by
  decide

theorem testBit43_ge {z : ℕ} (hz : 8 ≤ z) : (0x43 : ℕ).testBit z = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hz))

/-- A digest bit is the bit of its little-endian lane. -/
theorem digestBits_lane (d : RecursionFast.Digest) {j : ℕ} (hj : j < 256) :
    digestBits d j =
      (RecursionFast.Keccak.blockLane d.toArray (j / 64)).toBitVec.getLsbD (j % 64) := by
  rw [blockLane_bit _ _ (Nat.mod_lt _ (by decide)), digestBits, dite_eq_left hj,
    show 8 * (j / 64) + j % 64 / 8 = j / 8 by omega, show j % 64 % 8 = j % 8 by omega]
  simp [Array.getD, show j / 8 < 32 by omega]

/-- **V_S's `pad43` lanes are `pad43St`'s.** -/
theorem lane_pad43St (d : RecursionFast.Digest) {l : ℕ} (hl : l < 25) :
    Keccak.lane (pad43St (digestBits d)) l =
      pad43Lane (fun m ↦ RecursionFast.Keccak.blockLane d.toArray m) l := by
  refine UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun z hz ↦ ?_)
  have hb := stBit_ofBits (pad43Bit (digestBits d)) (show 64 * l + z < 1600 by omega)
  rw [← pad43St, stBit_eq_sbit _ (by omega), sbit, show (64 * l + z) / 64 = l by omega,
    show (64 * l + z) % 64 = z by omega] at hb
  rw [hb, pad43Lane]
  have hw : ∀ j < 256, digestBits d j =
      (RecursionFast.Keccak.blockLane d.toArray (j / 64)).toBitVec.getLsbD (j % 64) :=
    fun j hj ↦ digestBits_lane d hj
  unfold pad43Bit
  by_cases h0 : l = 0
  · subst h0
    simp only [ite_true, UInt64.toBitVec_or, BitVec.getLsbD_or, c43_bit z hz, shl8_bit _ hz]
    by_cases h8 : z < 8
    · simp [h8, show ¬ 8 ≤ z by omega]
    · rw [if_neg (show ¬ 64 * 0 + z < 8 by omega), if_pos (show 64 * 0 + z < 264 by omega),
        hw _ (by omega), testBit43_ge (by omega)]
      rw [show (64 * 0 + z - 8) / 64 = 0 by omega, show (64 * 0 + z - 8) % 64 = z - 8 by omega]
      simp [show 8 ≤ z by omega]
  rw [if_neg h0]
  by_cases h4 : l < 4
  · rw [if_pos h4, if_neg (show ¬ 64 * l + z < 8 by omega), if_pos (show 64 * l + z < 264 by omega),
      hw _ (by omega)]
    simp only [UInt64.toBitVec_or, BitVec.getLsbD_or, shr56_bit _ hz, shl8_bit _ hz]
    by_cases h8 : z < 8
    · rw [show (64 * l + z - 8) / 64 = l - 1 by omega, show (64 * l + z - 8) % 64 = 56 + z by omega]
      simp [show ¬ 8 ≤ z by omega]
    · rw [bit_ge _ (show 64 ≤ 56 + z by omega)]
      rw [show (64 * l + z - 8) / 64 = l by omega, show (64 * l + z - 8) % 64 = z - 8 by omega]
      simp [show 8 ≤ z by omega]
  rw [if_neg h4]
  by_cases h4' : l = 4
  · subst h4'
    rw [if_pos rfl, if_neg (show ¬ 64 * 4 + z < 8 by omega)]
    simp only [UInt64.toBitVec_or, BitVec.getLsbD_or, shr56_bit _ hz, c01_bit z hz]
    by_cases h8 : z < 8
    · rw [if_pos (show 64 * 4 + z < 264 by omega), hw _ (by omega)]
      rw [show (64 * 4 + z - 8) / 64 = 3 by omega, show (64 * 4 + z - 8) % 64 = 56 + z by omega]
      simp [show z ≠ 8 by omega]
    · rw [if_neg (show ¬ 64 * 4 + z < 264 by omega), bit_ge _ (show 64 ≤ 56 + z by omega)]
      have e : (64 * 4 + z = 264 ∨ 64 * 4 + z = 1087) ↔ z = 8 := by omega
      simp [e]
  rw [if_neg h4', if_neg (show ¬ 64 * l + z < 8 by omega), if_neg (show ¬ 64 * l + z < 264 by omega)]
  by_cases h16 : l = 16
  · subst h16
    rw [if_pos rfl, c80_bit z hz]
    have e : (64 * 16 + z = 264 ∨ 64 * 16 + z = 1087) ↔ z = 63 := by omega
    simp [e]
  · rw [if_neg h16]
    have e : ¬ (64 * l + z = 264 ∨ 64 * l + z = 1087) := by omega
    simp [e]

end Lvm.KG
