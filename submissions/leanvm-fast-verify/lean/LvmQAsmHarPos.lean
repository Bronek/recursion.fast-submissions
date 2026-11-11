-- New for lvm (HAR-POS): `F`'s WHIR positions read from `Σ' = sigma p ws` are Q_link's `posL`
-- values (`qsAt_posL`), from `qsAt_getD` (LvmQAsmArith2Whir), `kAt_sigma` (LvmQAsmHarBase) and
-- `posL_eq` (LvmQLinkBridge).
import LvmQAsmArith2Whir

/-!
# `F`'s positions are Q_link's `posL`

`F`'s `j`-th position of level `L` reads bits `(j mod 8)·h …` of a positions answer as one 192-bit
number (`eToNat`, three lanes, lane `0` lowest). When that answer is entry `e`'s (lanes `ansLane p e`,
`+1`, `+2` of `Σ'`), the number is `lw₀ + 2^64 lw₁ + 2^128 lw₂` (`kAt_sigma`), whose bit `n < 192`
is `ansBit p ws e n` (`testBit_limbs`); `posL_eq` then gives `posL`.
-/

set_option autoImplicit false

namespace Lvm.Har

open RecursionFast Lvm Lvm.QLink

theorem kToNat_laneK (ws : List Word) (i : Nat) : kToNat (laneK ws i) = lw ws i := rfl

theorem lw_lt (ws : List Word) (i : Nat) : lw ws i < 2 ^ 64 := (ws.getD i 0).isLt

/-- Bit `n < 192` of three 64-bit limbs (limb `0` lowest) is bit `n mod 64` of limb `⌊n/64⌋`. -/
theorem testBit_limbs (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 64) (a n : Nat) (hn : n < 192) :
    (f a + 2 ^ 64 * f (a + 1) + 2 ^ 128 * f (a + 2)).testBit n = (f (a + n / 64)).testBit (n % 64) := by
  have e : f a + 2 ^ 64 * f (a + 1) + 2 ^ 128 * f (a + 2) =
      2 ^ 64 * (2 ^ 64 * f (a + 2) + f (a + 1)) + f a := by
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num]; ring
  rw [e, Nat.testBit_two_pow_mul_add _ (hf a)]
  by_cases h0 : n < 64
  · simp only [h0, ↓reduceIte, Nat.div_eq_of_lt h0, Nat.mod_eq_of_lt h0, Nat.add_zero]
  simp only [h0, ↓reduceIte, Nat.testBit_two_pow_mul_add _ (hf (a + 1))]
  by_cases h1 : n - 64 < 64
  · simp only [h1, ↓reduceIte, show n / 64 = 1 by omega, show n % 64 = n - 64 by omega]
  · simp only [h1, ↓reduceIte, show n / 64 = 2 by omega, show n % 64 = n - 64 - 64 by omega]

/-- **`F`'s `j`-th position of level `L`, read from `Σ'`, is Q_link's `posL`** when the positions
answer it reads (at `P + 72 ⌊j/8⌋ + 40`) is entry `e`'s answer (`hP`) inside the hashed bytes. -/
theorem qsAt_posL (p : Params) (ws : List Word) (P : Nat) (L : Level) (e j : Nat) (hj : j < L.t)
    (hP : P + 72 * (j / 8) + 40 = 8 * ansLane p e)
    (hb : (j % 8) * L.height + L.height ≤ 192)
    (hlen : 8 * ansLane p e + 24 ≤ hashedLen p) (hws : ansLane p e + 3 ≤ ws.length) :
    (qsAt (sigma p ws) P L).getD j 0 = posL p ws e ((j % 8) * L.height) L.height := by
  rw [qsAt_getD _ P L j hj, hP]
  have hfe : eToNat (feAt (sigma p ws) (8 * ansLane p e)) =
      lw ws (ansLane p e) + 2 ^ 64 * lw ws (ansLane p e + 1) + 2 ^ 128 * lw ws (ansLane p e + 2) := by
    unfold eToNat feAt
    rw [show 8 * ansLane p e + 8 = 8 * (ansLane p e + 1) by omega,
      show 8 * ansLane p e + 16 = 8 * (ansLane p e + 2) by omega,
      kAt_sigma p ws _ (by omega) (by omega), kAt_sigma p ws _ (by omega) (by omega),
      kAt_sigma p ws _ (by omega) (by omega)]
    rfl
  rw [hfe]
  refine (posL_eq p ws _ e _ _ fun n _ h2 => ?_).symm
  rw [testBit_limbs (lw ws) (lw_lt ws) _ n (by omega)]
  rfl

end Lvm.Har
