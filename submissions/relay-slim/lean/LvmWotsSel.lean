-- adapted from rf-k/submissions/flock-recursive/lean/FRWots.lean@8bff272b (the digest-level
-- selections `wots_chain_sound`, `sigRoot_bits`, `wots_sound`, verbatim; namespace renamed);
-- the digit-from-bits and checksum lemmas are new (WP-12).
import LvmBits
import RecursionFast.Contract.Signature
import Mathlib.Tactic.IntervalCases

/-!
# WOTS at the digest level: chains, path, digits, checksum

* From FR (`FRWots`, hash-agnostic, verbatim): **`wots_chain_sound`** (three steps whose inputs
  are selected by `[d < s − 1]` give the contract's chain from the signed value at position `d`),
  **`sigRoot_bits`** (the path walk with the index's bits is `sigRoot`), **`wots_sound`** (chain
  ends, the leaf of those ends and a walk reaching `vk` give `SigOk vk m σ`).
* New: **`msgDigit_bits`**: digit `i < 128` of a digest is bit `2i` plus twice bit `2i + 1` of the
  digest read as 256 little-endian bits; **`checksum_bits`**: if `x^{Σ (3 − dᵢ)}` equals
  `x^{Σ_k 2^k c_k}` for ten Boolean `c_k` (and powers of `x` are injective below `2^10`), the five
  checksum digits of `wotsDigits` are the bit pairs `c_{2t} + 2 c_{2t+1}`.
-/

set_option autoImplicit false

namespace Lvm.Wots
open RecursionFast

/-- **One chain** (§4.2): steps `s = 1, 2, 3` from position `s − 1`; step `s`'s input is the
previous step's output when `d < s − 1`, else the signed value `ots`; the end is step 3's output
when `d < 3`, else `ots`. The end is the contract's chain from `ots` at position `d` to `3`. -/
theorem wots_chain_sound {j i d : ℕ} (hd : d ≤ 3) {ots e : Digest} {a out : ℕ → Digest}
    (hstep : ∀ s, 1 ≤ s → s ≤ 3 → out s = wotsStep j i (s - 1) (a s))
    (hsel : ∀ s, 1 ≤ s → s ≤ 3 → a s = if d + 1 < s then out (s - 1) else ots)
    (hend : e = if d < 3 then out 3 else ots) :
    e = wotsChain j i d (3 - d) ots := by
  have o1 := hstep 1 le_rfl (by omega); have o2 := hstep 2 (by omega) (by omega)
  have o3 := hstep 3 (by omega) le_rfl
  have a1 := hsel 1 le_rfl (by omega); have a2 := hsel 2 (by omega) (by omega)
  have a3 := hsel 3 (by omega) le_rfl
  interval_cases d <;> simp_all [wotsChain]

/-- **The path walk** (§4.2): `cur (t + 1) = sigNode l r` with `(l, r)` ordered by bit `t` of the
index is the contract's `sigRoot`. -/
theorem sigRoot_bits (cur : ℕ → Digest) : ∀ (path : List Digest) (j t0 : ℕ),
    (∀ t (ht : t < path.length), cur (t0 + t + 1) =
      if j / 2 ^ t % 2 = 0 then sigNode (cur (t0 + t)) path[t] else sigNode path[t] (cur (t0 + t))) →
    sigRoot j (cur t0) path = cur (t0 + path.length)
  | [], _, _, _ => rfl
  | s :: p, j, t0, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero, List.getElem_cons_zero] at h0
    rw [sigRoot, ← h0, sigRoot_bits cur p (j / 2) (t0 + 1) fun t ht => ?_]
    · simp [Nat.add_assoc, Nat.add_comm 1]
    · have := h (t + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul] at this
      rw [show t0 + 1 + t + 1 = t0 + (t + 1) + 1 by omega, this,
        show t0 + (t + 1) = t0 + 1 + t by omega, Nat.div_div_eq_div_mul, Nat.mul_comm,
        ← Nat.div_div_eq_div_mul]

theorem msgDigits_length (m : Digest) : (msgDigits m).length = 128 := by
  simp [msgDigits, List.length_flatMap]

theorem wotsDigits_length (m : Digest) : (wotsDigits m).length = wotsLen := by
  simp [wotsDigits, msgDigits_length, wotsLen]

/-- **`wots_sound`** (§4.2): chain ends that are the contract's chains from the signed values at
the message's digits, the leaf of those ends, and a walk along the path with the index's bits that
reaches `vk`, give the contract's `SigOk`. -/
theorem wots_sound {vk m : Digest} {σ : Sig} (hidx : σ.idx < 2 ^ sigHeight)
    (hots : σ.ots.length = wotsLen) (hpath : σ.path.length = sigHeight) {ends : List Digest}
    (hlen : ends.length = wotsLen)
    (hends : ∀ i (hi : i < wotsLen), ends[i]'(hlen ▸ hi) =
      wotsChain σ.idx i ((wotsDigits m)[i]'(by rw [wotsDigits_length]; exact hi))
        (3 - (wotsDigits m)[i]'(by rw [wotsDigits_length]; exact hi)) (σ.ots[i]'(hots ▸ hi)))
    {cur : ℕ → Digest} (hleaf : cur 0 = wotsLeaf σ.idx ends)
    (hwalk : ∀ t (ht : t < σ.path.length), cur (t + 1) = if σ.idx / 2 ^ t % 2 = 0
      then sigNode (cur t) σ.path[t] else sigNode σ.path[t] (cur t))
    (hroot : cur sigHeight = vk) : SigOk vk m σ = true := by
  have hE : wotsEnds σ.idx m σ.ots = ends := by
    apply List.ext_getElem (by simp [wotsEnds, wotsDigits_length, hots, hlen])
    intro i h1 h2
    simp only [wotsEnds, List.getElem_mapIdx, List.getElem_zip]
    exact (hends i (hlen ▸ h2)).symm
  have hr := sigRoot_bits cur σ.path σ.idx 0 fun t ht => by simpa using hwalk t ht
  simp only [SigOk, hidx, hots, hpath, decide_true, Bool.true_and, decide_eq_true_eq, hE,
    ← hleaf, hr, Nat.zero_add, hroot]

/-! ## Digits from bits (new) -/

theorem flatMap4_getElem {α β : Type} (f : α → List β) (hf : ∀ a, (f a).length = 4) :
    ∀ (l : List α) (q r : ℕ) (hq : q < l.length) (hr : r < 4) (h : 4 * q + r < (l.flatMap f).length),
      (l.flatMap f)[4 * q + r] = (f l[q])[r]'(by rw [hf]; exact hr)
  | [], _, _, hq, _, _ => absurd hq (by simp)
  | a :: l, q, r, hq, hr, h => by
    simp only [List.flatMap_cons] at h ⊢
    cases q with
    | zero =>
      rw [List.getElem_append_left (by rw [hf]; omega)]; simp
    | succ q =>
      rw [List.getElem_append_right (by rw [hf]; omega)]
      have := flatMap4_getElem f hf l q r (by simpa using hq) hr
        (by simp only [List.length_append, hf] at h; omega)
      simp only [hf, show 4 * (q + 1) + r - 4 = 4 * q + r by omega, this, List.getElem_cons_succ]

theorem msgDigits_getElem (m : Digest) {i : ℕ} (hi : i < 128) :
    (msgDigits m)[i]'(by rw [msgDigits_length]; exact hi) = m[i / 4].toNat / 4 ^ (i % 4) % 4 := by
  have h := flatMap4_getElem (fun b : UInt8 => (List.range 4).map fun t => b.toNat / 4 ^ t % 4)
    (by simp) m.toList (i / 4) (i % 4) (by simp; omega) (Nat.mod_lt _ (by norm_num))
    (by rw [show 4 * (i / 4) + i % 4 = i by omega]; simpa [msgDigits_length, msgDigits] using hi)
  simp only [show 4 * (i / 4) + i % 4 = i by omega] at h
  simp only [msgDigits, h, List.getElem_map, List.getElem_range, Vector.getElem_toList]

/-- A base-4 digit of a number is two of its bits. -/
theorem div_four_pow_mod (n u : ℕ) :
    n / 4 ^ u % 4 = (n.testBit (2 * u)).toNat + 2 * (n.testBit (2 * u + 1)).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    show 4 ^ u = 2 ^ (2 * u) by rw [pow_mul]; norm_num, pow_succ, ← Nat.div_div_eq_div_mul]
  generalize n / 2 ^ (2 * u) = q
  rcases Nat.mod_two_eq_zero_or_one q with h | h <;>
  rcases Nat.mod_two_eq_zero_or_one (q / 2) with h' | h' <;> simp [h, h'] <;> omega

theorem testBit_byte (b : UInt8) (j : ℕ) : b.toNat.testBit j = Bits.bbit b j := rfl

/-- **Digit `i` of a message from its bits**: with byte `k` of `m` the byte `k % 8` of lane
`k / 8` of `w`, digit `i < 128` is bit `2i` plus twice bit `2i + 1` of the lanes. -/
theorem msgDigit_bits (m : Digest) (w : ℕ → UInt64)
    (hm : ∀ k (hk : k < 32), m[k] = Bits.byteW (w (k / 8)) (k % 8)) {i : ℕ} (hi : i < 128) :
    (msgDigits m)[i]'(by rw [msgDigits_length]; exact hi) =
      (Bits.ubit (w (i / 32)) (2 * i % 64)).toNat + 2 * (Bits.ubit (w (i / 32)) (2 * i % 64 + 1)).toNat := by
  rw [msgDigits_getElem m hi, hm _ (by omega), div_four_pow_mod, testBit_byte, testBit_byte,
    Bits.bbit_byteW _ (by omega) (by omega), Bits.bbit_byteW _ (by omega) (by omega)]
  rw [show i / 4 / 8 = i / 32 by omega, show 8 * (i / 4 % 8) + 2 * (i % 4) = 2 * i % 64 by omega,
    show 8 * (i / 4 % 8) + (2 * (i % 4) + 1) = 2 * i % 64 + 1 by omega]

/-! ## The checksum (new) -/

/-- `Σ_k 2^k c_k` over the first `n` Boolean `c`. -/
def bitsVal (c : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if c n then 2 ^ n else 0) + bitsVal c n

theorem bitsVal_lt (c : ℕ → Bool) : ∀ n, bitsVal c n < 2 ^ n
  | 0 => by simp [bitsVal]
  | n + 1 => by
    have := bitsVal_lt c n
    rw [bitsVal, pow_succ]; split <;> omega

theorem bitsVal_testBit (c : ℕ → Bool) : ∀ n, ∀ k < n, (bitsVal c n).testBit k = c k
  | 0, k, hk => absurd hk (by omega)
  | n + 1, k, hk => by
    have hlt := bitsVal_lt c n
    rw [bitsVal]
    rcases Nat.lt_or_ge k n with h | h
    · rw [← bitsVal_testBit c n k h]
      split
      · exact Nat.testBit_two_pow_add_gt h _
      · rw [Nat.zero_add]
    · obtain rfl : k = n := by omega
      split
      · rename_i hc; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, hc]; rfl
      · rename_i hc; rw [Nat.zero_add, Nat.testBit_lt_two_pow hlt]; simpa using hc

/-- **The checksum digits from bits**: if the checksum `C = Σ (3 − dᵢ)` of the message digits
equals `Σ_k 2^k c_k` over ten bits, the checksum digit `t < 5` is `c_{2t} + 2 c_{2t+1}`. -/
theorem checksum_digit (m : Digest) (c : ℕ → Bool)
    (hC : ((msgDigits m).map (3 - ·)).sum = bitsVal c 10) {t : ℕ} (ht : t < 5) :
    (wotsDigits m)[128 + t]'(by rw [wotsDigits_length]; simp [wotsLen]; omega) =
      (c (2 * t)).toNat + 2 * (c (2 * t + 1)).toNat := by
  simp only [wotsDigits]
  rw [List.getElem_append_right (by rw [msgDigits_length]; omega)]
  simp only [msgDigits_length, List.getElem_map, List.getElem_range,
    show 128 + t - 128 = t by omega, hC, div_four_pow_mod]
  rw [bitsVal_testBit c 10 _ (by omega), bitsVal_testBit c 10 _ (by omega)]

theorem msgDigits_le (m : Digest) : ∀ d ∈ msgDigits m, d ≤ 3 := by
  intro d hd
  simp only [msgDigits, List.mem_flatMap, List.mem_map, List.mem_range] at hd
  obtain ⟨b, -, t, -, rfl⟩ := hd
  omega

theorem checksum_le (m : Digest) : ((msgDigits m).map (3 - ·)).sum ≤ 384 := by
  have : ∀ l : List ℕ, ((l.map (3 - ·)).sum ≤ 3 * l.length) := by
    intro l; induction l with
    | nil => simp
    | cons a l ih => simp [List.sum_cons]; omega
  have := this (msgDigits m)
  rw [msgDigits_length] at this; omega

/-- Powers of `x` with exponents `3 − d` multiply to `x^{Σ (3 − d)}`. -/
theorem prod_pow_sum (l : List ℕ) :
    (l.map fun d => FK.x ^ (3 - d)).prod = FK.x ^ (l.map (3 - ·)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, List.sum_cons, ih, pow_add]

/-- **The checksum equation**: from `x^{Σ (3 − dᵢ)} = x^{Σ 2^k c_k}` with exponents below the
injectivity bound. -/
theorem checksum_of_pow (m : Digest) (c : ℕ → Bool)
    (hinj : ∀ a b, a < 1024 → b < 1024 → FK.x ^ a = FK.x ^ b → a = b)
    (h : FK.x ^ ((msgDigits m).map (3 - ·)).sum = FK.x ^ bitsVal c 10) :
    ((msgDigits m).map (3 - ·)).sum = bitsVal c 10 :=
  hinj _ _ (by have := checksum_le m; omega) (by have := bitsVal_lt c 10; simpa using this) h

end Lvm.Wots
