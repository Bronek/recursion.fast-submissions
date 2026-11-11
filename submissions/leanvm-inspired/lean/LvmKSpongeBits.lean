-- Copied from flock-recursive `FRKeccakBits.lean` lines 1-127 and `digest_ext` (stage K2-LS) for lvm (WP-8) as `LvmKSpongeBits`; namespace FR.KSponge → Lvm.KSponge; the block `Layout` part is not copied.
import LvmKSponge
import Batteries.Data.BitVec

/-!
# Lanes, bytes and bits: the contract's `State` as the circuit sees it

The contract's state is 25 `UInt64` lanes, lane `i = x + 5y`, a lane the little-endian word of 8
state bytes (`Contract/Hash/Keccak.lean`). The circuit sees **state bit `k < 1600`**: bit `k % 64`
of lane `k / 64`, i.e. bit `k % 8` of state byte `k / 8` (`kblock.py`: "lane x + 5y, bit z
little-endian", state bit `i = 64 (x + 5y) + z`). A rate byte `j < 136` is message bits
`8 j … 8 j + 7`, absorbed into state bits `8 j … 8 j + 7` (`xorMsg_bit`).

* `stBit a k`, `ofBits g` (the state with bit `k` = `g k`), `stBit_ofBits`, `state_ext`;
* `blockLane_bit`, **`xorMsg_bit`**: bit `k` of `xorMsg a m` is `stBit a k ⊕ [k < 1088] ∧ bit k%8 of m (k/8)`;
* `msgOfBits`, `stDigest_bit`: digest byte `e` bit `t` is state bit `8 e + t`.
-/

namespace Lvm
namespace KSponge
open RecursionFast RecursionFast.Keccak

/-! ## State bits -/

/-- **State bit `k`**: bit `k % 64` of lane `k / 64` (`false` past 1600). -/
def stBit (a : State) (k : ℕ) : Bool :=
  if h : k < 1600 then (a[k / 64]'(by omega)).toBitVec.getLsbD (k % 64) else false

/-- The state whose bit `k` is `g k`. -/
def ofBits (g : ℕ → Bool) : State :=
  Vector.ofFn fun i : Fin 25 => ⟨BitVec.ofFnLE fun z : Fin 64 => g (64 * i + z)⟩

theorem stBit_ofBits (g : ℕ → Bool) {k : ℕ} (hk : k < 1600) : stBit (ofBits g) k = g k := by
  simp only [stBit, hk, dite_true, ofBits, Vector.getElem_ofFn, BitVec.getLsbD_ofFnLE,
    Nat.mod_lt _ (show 0 < 64 by decide)]
  congr 1
  omega

/-- Two states are equal when their 1600 bits are. -/
theorem state_ext {a a' : State} (h : ∀ k < 1600, stBit a k = stBit a' k) : a = a' := by
  refine Vector.ext fun i hi => UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun z hz => ?_)
  have := h (64 * i + z) (by omega)
  simp only [stBit, show 64 * i + z < 1600 by omega, dite_true,
    show (64 * i + z) / 64 = i by omega, show (64 * i + z) % 64 = z by omega] at this
  exact this

theorem stBit_zeroSt {k : ℕ} : stBit zeroSt k = false := by
  unfold stBit zeroSt
  split <;> simp

/-! ## Rate bytes into lanes -/

/-- Bit `z` of lane `i` of a block is bit `z % 8` of its byte `8 i + z / 8` (little-endian). -/
theorem blockLane_bit (arr : Array UInt8) (i : ℕ) {z : ℕ} (hz : z < 64) :
    (blockLane arr i).toBitVec.getLsbD z = (arr.getD (8 * i + z / 8) 0).toBitVec.getLsbD (z % 8) := by
  rw [blockLane_unfold]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64,
    BitVec.getLsbD_or, BitVec.getLsbD_zero, BitVec.ofNat_eq_ofNat,
    BitVec.zero_umod, BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod,
    BitVec.shiftLeft_zero, UInt64.toBitVec_ofNat, BitVec.reduceMod, Bool.false_or]
  interval_cases z <;> simp only [Nat.reduceLT, BitVec.getLsbD_eq_getElem,
    BitVec.getElem_setWidth, Nat.reduceLeDiff, BitVec.getLsbD_of_ge, Bool.or_self,
    Nat.reduceMod, BitVec.getElem_shiftLeft, decide_false, Bool.not_false, Nat.reduceSub,
    Bool.true_and, Bool.false_or, decide_true, Bool.not_true, Nat.sub_eq_zero_of_le, Nat.ofNat_pos,
    Bool.false_and, Bool.or_false, Nat.reduceDiv, Nat.add_zero]

/-- **Absorbing, bit by bit**: state bit `k` of `xorMsg a m` is `stBit a k`, XORed for `k < 1088`
with bit `k % 8` of rate byte `k / 8`. -/
theorem xorMsg_bit (a : State) (m : ℕ → UInt8) {k : ℕ} (hk : k < 1600) :
    stBit (xorMsg a m) k =
      (stBit a k ^^ (decide (k < 1088) && (m (k / 8)).toBitVec.getLsbD (k % 8))) := by
  simp only [stBit, hk, dite_true, xorMsg, Vector.getElem_ofFn, UInt64.toBitVec_xor,
    BitVec.getLsbD_xor]
  congr 1
  rw [blockLane_bit _ _ (Nat.mod_lt _ (by decide)), rateArr_getD,
    show 8 * (k / 64) + k % 64 / 8 = k / 8 by omega, show k % 64 % 8 = k % 8 by omega]
  by_cases h : k < 1088
  · rw [ite_eq_left (by simp only [rate]; omega)]; simp [h]
  · rw [ite_eq_right (by simp only [rate]; omega)]; simp [h]

/-- The bytes whose bit `8 j + t` is `g (8 j + t)`. -/
def msgOfBits (g : ℕ → Bool) : ℕ → UInt8 :=
  fun j => ⟨BitVec.ofFnLE fun t : Fin 8 => g (8 * j + t)⟩

theorem msgOfBits_bit (g : ℕ → Bool) (j : ℕ) {t : ℕ} (ht : t < 8) :
    (msgOfBits g j).toBitVec.getLsbD t = g (8 * j + t) := by
  simp [msgOfBits, ht]

/-- A state given bitwise as `g₀ ⊕ [k < 1088] g₁` is `g₀`'s state with `g₁`'s bytes absorbed. -/
theorem ofBits_eq_xorMsg {g g₀ g₁ : ℕ → Bool}
    (h : ∀ k < 1600, g k = (g₀ k ^^ (decide (k < 1088) && g₁ k))) :
    ofBits g = xorMsg (ofBits g₀) (msgOfBits g₁) := by
  refine state_ext fun k hk => ?_
  rw [xorMsg_bit _ _ hk, stBit_ofBits _ hk, stBit_ofBits _ hk, h k hk,
    msgOfBits_bit _ _ (Nat.mod_lt _ (by decide)), show 8 * (k / 8) + k % 8 = k by omega]

theorem xorMsg_zero (a : State) : xorMsg a (fun _ => 0) = a :=
  state_ext fun k hk => by rw [xorMsg_bit _ _ hk]; simp

/-! ## The digest of a state -/

theorem stDigest_eq_outBytes (a : State) : stDigest a = outBytes (S25.ofVec a) := by
  rw [outBytes_eq, S25.toVec_ofVec]; rfl

/-- Digest byte `e` is byte `e % 8` of lane `e / 8`. -/
theorem stDigest_getElem (a : State) {e : ℕ} (he : e < 32) :
    (stDigest a)[e] = (a[e / 8]'(by omega) >>> (8 * (e % 8)).toUInt64).toUInt8 := by
  rw [stDigest_eq_outBytes]
  interval_cases e <;> rfl

/-- **Digest byte `e` bit `t` is state bit `8 e + t`.** -/
theorem stDigest_bit (a : State) {e t : ℕ} (he : e < 32) (ht : t < 8) :
    (stDigest a)[e].toBitVec.getLsbD t = stBit a (8 * e + t) := by
  rw [stDigest_getElem _ he, stBit, dite_eq_left (show 8 * e + t < 1600 by omega)]
  simp only [show (8 * e + t) / 64 = e / 8 by omega, show (8 * e + t) % 64 = 8 * (e % 8) + t by omega]
  have hn : e % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize e % 8 = n at hn ⊢
  simp only [UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth, UInt64.toBitVec_shiftRight]
  interval_cases n <;> simp [ht]

/-- Two digests are equal when their bits are. -/
theorem digest_ext {d d' : Digest}
    (h : ∀ e (he : e < 32), ∀ t < 8, d[e].toBitVec.getLsbD t = d'[e].toBitVec.getLsbD t) :
    d = d' :=
  Vector.ext fun e he => UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun t ht => h e he t ht)

end KSponge
end Lvm
