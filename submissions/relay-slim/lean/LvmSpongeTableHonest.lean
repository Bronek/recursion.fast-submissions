-- New for lvm (WP-8): non-vacuity of `SpongeRel`: for any message rows and any `cont` with `cont 0 = 0`, the
-- honest sponge table meets it.
import LvmSpongeTable

/-!
# The honest `KS` table

`honSt msg cont i`: the honest input state of row `i`: the previous row's output, or the zero
state when `cont i = 0`, with row `i`'s message bytes absorbed. `honKs` holds its lanes in slots
`0 … 24`; `honY` the permutation's output. **`spongeRel_honest`**: `SpongeRel` holds for them, so the
hypotheses of `traceDigest_of_KS` and the other digest theorems are satisfiable.
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakGkr Lvm.KSponge

theorem idx_div' (h : ℕ) {x t : ℕ} (hx : x < 2 ^ h) : (x + 2 ^ h * t) / 2 ^ h = t := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos h), Nat.div_eq_of_lt hx, zero_add]

theorem idx_mod' (h : ℕ) {x t : ℕ} (hx : x < 2 ^ h) : (x + 2 ^ h * t) % 2 ^ h = x := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

variable (msg : ℕ → ℕ → K) (cont : ℕ → Bool)

/-- The honest output of row `i`. -/
def honOut : ℕ → RecursionFast.Keccak.State
  | 0 => RecursionFast.Keccak.keccakF (xorMsg zeroSt (msgBytes msg 0))
  | i + 1 => RecursionFast.Keccak.keccakF
      (xorMsg (if cont (i + 1) then honOut i else zeroSt) (msgBytes msg (i + 1)))

/-- The honest input of row `i`. -/
def honSt (i : ℕ) : RecursionFast.Keccak.State :=
  xorMsg (if cont i then honOut msg cont (i - 1) else zeroSt) (msgBytes msg i)

/-- The honest block: the input lanes in slots `0 … 24`. -/
def honKs (hk : ℕ) (w : ℕ) : K :=
  if w / 2 ^ hk < 25 then K.ofLane (Keccak.lane (honSt msg cont (w % 2 ^ hk)) (w / 2 ^ hk)) else 0

/-- The honest output lanes. -/
def honY (i l : ℕ) : K := K.ofLane (Keccak.lane (honOut msg cont i) l)

theorem honOut_eq (h0 : cont 0 = false) (i : ℕ) :
    honOut msg cont i = RecursionFast.Keccak.keccakF (honSt msg cont i) := by
  cases i with
  | zero => simp [honOut, honSt, h0]
  | succ i => simp [honOut, honSt]

/-- A row's message lane is the little-endian word of its message bytes. -/
theorem blockLane_msgBytes (i : ℕ) {l : ℕ} (hl : l < 17) :
    RecursionFast.Keccak.blockLane (rateArr (msgBytes msg i)) l = K.lane (msg i l) := by
  refine UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun z hz ↦ ?_)
  rw [blockLane_bit _ _ hz, rateArr_getD, if_pos (by simp only [RecursionFast.Keccak.rate]; omega),
    msgBytes_bit _ _ _ (Nat.mod_lt _ (by decide)), show (8 * l + z / 8) / 8 = l by omega,
    show 8 * ((8 * l + z / 8) % 8) + z % 8 = z by omega]
  rfl

theorem blockLane_msgBytes_ge (i : ℕ) {l : ℕ} (hl : 17 ≤ l) :
    RecursionFast.Keccak.blockLane (rateArr (msgBytes msg i)) l = 0 := by
  refine UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun z hz ↦ ?_)
  rw [blockLane_bit _ _ hz, rateArr_getD, if_neg (by simp only [RecursionFast.Keccak.rate]; omega)]
  simp

/-- **Non-vacuity of `SpongeRel`.** -/
theorem spongeRel_honest (hk : ℕ) (h0 : cont 0 = false) :
    SpongeRel hk (honKs msg cont hk) (honY msg cont) msg cont where
  out i hi l hl := by
    have hin : inState hk (honKs msg cont hk) 0 i = honSt msg cont i := by
      refine Vector.ext fun l' hl' ↦ ?_
      simp only [inState, Vector.getElem_ofFn, Nat.mul_zero, Nat.zero_add, honKs,
        idx_div' hk hi, idx_mod' hk hi, if_pos hl', K.lane, K.ofLane, BF64.toBitVec_ofBitVec,
        LeanVM.Protocol.KeccakGkr.lane_eq _ hl']
    rw [honY, hin, laneWord, keccakF1600_eq, honOut_eq msg cont h0]
  link i hi l hl := by
    rw [honKs, idx_div' hk hi, idx_mod' hk hi, if_pos hl, honSt]
    apply BF64.ext
    simp only [K.ofLane, BF64.toBitVec_ofBitVec, LvmKeccakWords_toBitVec_add]
    rw [LeanVM.Protocol.KeccakGkr.lane_eq _ hl]
    simp only [xorMsg, Vector.getElem_ofFn, UInt64.toBitVec_xor]
    congr 1
    · split <;> simp [honY, K.ofLane, zeroSt, LeanVM.Protocol.KeccakGkr.lane_eq _ hl]
    · split_ifs with h17
      · rw [blockLane_msgBytes msg i h17]; rfl
      · rw [blockLane_msgBytes_ge msg i (by omega)]; rfl
  cont0 := h0
where
  LvmKeccakWords_toBitVec_add (a b : K) : (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

end Lvm.KG
