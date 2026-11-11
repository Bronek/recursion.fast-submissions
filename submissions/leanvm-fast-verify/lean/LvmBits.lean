import LvmFieldKCorrect

/-!
# `BITS`: bit decomposition of `K` words and their byte-shifted parts (BLUEPRINT §4.3)

New for lvm (WP-12). Searched for reuse: FR's bit tables are BLAKE-era `GF(2^128)` element
layouts (`FRNodeRows4WotsB`, `bitsB4_bit`), FR `FRKeccakBits` / lvm `LvmKSpongeBits` work on the
Keccak state bits, and `LvmKeccakBits` on the GKR's bit slices; none states a word's bits in
`GF(2^64)` as a table row. The byte-extensionality helper follows FR `FRNodeRows4WotsB.byte_ext`.

A `K` element `w` is the word `w.val : UInt64`, bit `z` the coefficient of `x^z`.

* **The row.** Committed: `w` and 64 bit columns `β_z`. Constraints (degree 2):
  `β_z·β_z + β_z = 0` (so `β_z ∈ {0, 1}`) and `w + Σ_z x^z·β_z = 0`.
* **Derived outputs** (not committed: linear forms in the bit columns, written to the bus as
  cells): `shl k` = `w <<< k`, `shr k` = `w >>> k`, `bit z` = bit `z` (`0` or `1`); each is
  `Σ_z coef z · β_z` (`BOut.coef`). The byte shifts the unaligned prefixes need are `shl 8`/`shr 56`
  (1- and 9-byte prefixes) and `shl 24`/`shr 40` (the 11-byte `wotsStep` prefix).
* **`row_sound`**: the constraints force the bits to be `w`'s and every output to be its word
  function: `out o = ⟨o.word w.val⟩`.
* Bytes: `byteW w t` (byte `t` of a word, little-endian) with `byteW_xor`, `byteW_shl8`,
  `byteW_shr8`, the lemmas the message layouts of `LvmWotsMsg` use.
-/

set_option autoImplicit false

namespace Lvm.Bits

open Lvm

/-! ## Bits of words -/

/-- Bit `i` of a word. -/
def ubit (w : UInt64) (i : Nat) : Bool := w.toBitVec.getLsbD i

theorem u64_ext {a b : UInt64} (h : ∀ i < 64, ubit a i = ubit b i) : a = b :=
  UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq h)

theorem ubit_ge (a : UInt64) {i : Nat} (hi : 64 ≤ i) : ubit a i = false :=
  BitVec.getLsbD_of_ge _ _ hi

theorem ubit_xor (a b : UInt64) (i : Nat) : ubit (a ^^^ b) i = (ubit a i ^^ ubit b i) := by
  simp [ubit]

theorem ubit_and (a b : UInt64) (i : Nat) : ubit (a &&& b) i = (ubit a i && ubit b i) := by
  simp [ubit]

theorem ubit_or (a b : UInt64) (i : Nat) : ubit (a ||| b) i = (ubit a i || ubit b i) := by
  simp [ubit]

theorem ubit_zero (i : Nat) : ubit 0 i = false := by simp [ubit]

theorem ubit_val_zero (i : Nat) : ubit (0 : FK).val i = false := ubit_zero i

theorem ubit_one (i : Nat) : ubit 1 i = decide (i = 0) := by
  simp only [ubit, UInt64.toBitVec_one, BitVec.getLsbD_one]; by_cases h : i = 0 <;> simp [h]

theorem toBitVec_mod64 {k : Nat} (hk : k < 64) : (k.toUInt64).toBitVec % 64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem ubit_shl (a : UInt64) {k : Nat} (hk : k < 64) (i : Nat) :
    ubit (a <<< k.toUInt64) i = (decide (i < 64) && decide (k ≤ i) && ubit a (i - k)) := by
  simp only [ubit, UInt64.toBitVec_shiftLeft, toBitVec_mod64 hk, BitVec.shiftLeft_eq',
    BitVec.getLsbD_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  by_cases h : i < k
  · simp [h, show ¬ k ≤ i by omega]
  · simp [h, show k ≤ i by omega]

theorem ubit_shr (a : UInt64) {k : Nat} (hk : k < 64) (i : Nat) :
    ubit (a >>> k.toUInt64) i = ubit a (k + i) := by
  simp only [ubit, UInt64.toBitVec_shiftRight, toBitVec_mod64 hk, BitVec.ushiftRight_eq',
    BitVec.getLsbD_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]

theorem ubit_one_shl {k : Nat} (hk : k < 64) (i : Nat) :
    ubit ((1 : UInt64) <<< k.toUInt64) i = decide (i = k) := by
  rw [ubit_shl _ hk]
  by_cases h : i = k
  · subst h; simp [ubit, hk]
  · by_cases h2 : k ≤ i
    · have : ubit 1 (i - k) = false := by
        simp only [ubit, UInt64.toBitVec_one, BitVec.getLsbD_one]; simp; omega
      simp [this, h]
    · simp [h2, h]

/-! ## Bytes of words -/

/-- Byte `t` of a word (little-endian). -/
def byteW (w : UInt64) (t : Nat) : UInt8 := (w >>> (8 * t).toUInt64).toUInt8

/-- Bit `j` of a byte. -/
def bbit (b : UInt8) (j : Nat) : Bool := b.toBitVec.getLsbD j

theorem byte_ext {a b : UInt8} (h : ∀ j < 8, bbit a j = bbit b j) : a = b :=
  UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq h)

theorem bbit_byteW (w : UInt64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    bbit (byteW w t) j = ubit w (8 * t + j) := by
  simp only [bbit, byteW, UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth]
  rw [show (decide (j < 8)) = true by simp [hj], Bool.true_and]
  exact ubit_shr w (by omega) j

theorem byteW_xor (a b : UInt64) {t : Nat} (ht : t < 8) :
    byteW (a ^^^ b) t = byteW a t ^^^ byteW b t :=
  byte_ext fun j hj => by
    rw [bbit_byteW _ ht hj, ubit_xor]
    simp only [bbit, UInt8.toBitVec_xor, BitVec.getLsbD_xor]
    rw [← bbit, ← bbit, bbit_byteW _ ht hj, bbit_byteW _ ht hj]

theorem byteW_zero (t : Nat) : byteW 0 t = 0 := by simp [byteW]

/-- Shifting left by `s` bytes moves byte `t − s` to byte `t`. -/
theorem byteW_shl8 (a : UInt64) {s t : Nat} (hs : s < 8) (ht : t < 8) :
    byteW (a <<< (8 * s).toUInt64) t = if s ≤ t then byteW a (t - s) else 0 :=
  byte_ext fun j hj => by
    rw [bbit_byteW _ ht hj, ubit_shl _ (by omega)]
    split
    · rw [bbit_byteW _ (by omega) hj]
      simp [show 8 * t + j < 64 by omega, show 8 * s ≤ 8 * t + j by omega,
        show 8 * t + j - 8 * s = 8 * (t - s) + j by omega]
    · simp [bbit, show ¬ 8 * s ≤ 8 * t + j by omega]

/-- Shifting right by `s` bytes moves byte `t + s` to byte `t`. -/
theorem byteW_shr8 (a : UInt64) {s t : Nat} (hs : s < 8) (ht : t < 8) :
    byteW (a >>> (8 * s).toUInt64) t = if t + s < 8 then byteW a (t + s) else 0 :=
  byte_ext fun j hj => by
    rw [bbit_byteW _ ht hj, ubit_shr _ (by omega)]
    split
    · rw [bbit_byteW _ (by omega) hj]; congr 1; omega
    · rw [ubit_ge _ (by omega)]; simp [bbit]

/-! ## `K` sums -/

/-- `Σ_{z < n} g z` in `K`, left to right. -/
def lsum (g : Nat → FK) : Nat → FK
  | 0 => 0
  | n + 1 => lsum g n + g n

/-- **Bits of a sum of disjoint single-bit words.** If the `z`-th term (`z < n`) has bit `i` set
exactly when `f z` and `e z = i`, with `e` injective on the support, bit `i` of the sum says
whether `i` is hit. -/
theorem ubit_lsum (g : Nat → FK) (f : Nat → Bool) (e : Nat → Nat) (i : Nat) :
    ∀ n, (∀ z < n, ubit (g z).val i = (f z && decide (e z = i))) →
    (∀ z < n, ∀ z' < n, f z = true → f z' = true → e z = e z' → z = z') →
    (ubit (lsum g n).val i = true ↔ ∃ z < n, f z = true ∧ e z = i)
  | 0, _, _ => by simp [lsum, ubit_val_zero]
  | n + 1, hg, hinj => by
    have ih := ubit_lsum g f e i n (fun z hz => hg z (by omega))
      (fun z hz z' hz' => hinj z (by omega) z' (by omega))
    rw [lsum, show (lsum g n + g n).val = (lsum g n).val ^^^ (g n).val from rfl, ubit_xor,
      hg n (by omega)]
    by_cases hn : f n = true ∧ e n = i
    · have hno : ¬ ∃ z < n, f z = true ∧ e z = i := fun ⟨z, hz, h1, h2⟩ =>
        absurd (hinj z (by omega) n (by omega) h1 hn.1 (h2.trans hn.2.symm)) (by omega)
      have hl : ubit (lsum g n).val i = false := by
        cases h : ubit (lsum g n).val i
        · rfl
        · exact absurd (ih.mp h) hno
      simp only [hl, hn.1, hn.2, decide_true, Bool.and_true, Bool.false_xor, true_iff]
      exact ⟨n, by omega, hn.1, hn.2⟩
    · have hb : (f n && decide (e n = i)) = false := by
        cases h : f n <;> simp_all
      rw [hb, Bool.xor_false, ih]
      constructor
      · rintro ⟨z, hz, h⟩; exact ⟨z, by omega, h⟩
      · rintro ⟨z, hz, h⟩
        refine ⟨z, ?_, h⟩
        rcases Nat.lt_or_ge z n with h' | h'
        · exact h'
        · exact absurd (show z = n by omega ▸ h) hn

/-! ## The `BITS` row -/

/-- A derived output of a `BITS` row. -/
inductive BOut where
  /-- `w <<< k`. -/
  | shl (k : Nat)
  /-- `w >>> k`. -/
  | shr (k : Nat)
  /-- Bit `z` of `w`, as the word `0` or `1`. -/
  | bit (z : Nat)
  /-- The `m` bits of `w` from bit `z` on, placed at bit `d` (A20: a position field, or the part of
  one that lies in this lane). -/
  | fld (z m d : Nat)
  deriving DecidableEq, Repr

/-- The output's word function. -/
def BOut.word : BOut → UInt64 → UInt64
  | .shl k, w => w <<< k.toUInt64
  | .shr k, w => w >>> k.toUInt64
  | .bit z, w => (w >>> z.toUInt64) &&& 1
  | .fld z m d, w => ((w >>> z.toUInt64) <<< (64 - m : Nat).toUInt64) >>> (64 - m - d : Nat).toUInt64

/-- Shifts and fields inside the word. -/
def BOut.Valid : BOut → Prop
  | .shl k => k < 64
  | .shr k => k < 64
  | .bit z => z < 64
  | .fld z m d => z < 64 ∧ 1 ≤ m ∧ m + d ≤ 64

/-- The bit an output's bit `i` comes from (meaningful when `BOut.hit`). -/
def BOut.src : BOut → Nat → Nat
  | .shl k, i => i - k
  | .shr k, i => i + k
  | .bit z, i => i + z
  | .fld z _ d, i => i + z - d

/-- Where bit `z` of the word lands in the output, and whether it lands. -/
def BOut.dst : BOut → Nat → Nat
  | .shl k, z => z + k
  | .shr k, z => z - k
  | .bit z₀, z => z - z₀
  | .fld z₀ _ d, z => z - z₀ + d

/-- Whether bit `z` of the word reaches the output. -/
def BOut.hit : BOut → Nat → Bool
  | .shl k, z => decide (z + k < 64)
  | .shr k, z => decide (k ≤ z)
  | .bit z₀, z => decide (z = z₀)
  | .fld z₀ m d, z => decide (z₀ ≤ z ∧ z < z₀ + m ∧ z - z₀ + d < 64)

/-- The coefficient of bit column `β_z` in the output's linear form. -/
def BOut.coef (o : BOut) (z : Nat) : FK :=
  if o.hit z then ⟨(1 : UInt64) <<< (o.dst z).toUInt64⟩ else 0

/-- A `BITS` row: the word and its 64 bit columns. -/
structure Row where
  /-- The word read. -/
  w : FK
  /-- The bit columns. -/
  β : Nat → FK

/-- The weight of bit `z` in the word: `x^z`, as a word. -/
def wt (z : Nat) : FK := ⟨(1 : UInt64) <<< z.toUInt64⟩

theorem wt_eq_pow {z : Nat} (hz : z < 64) : wt z = FK.x ^ z :=
  (FK.x_pow_word ⟨z, hz⟩).symm

/-- **The row's constraints** (degree 2): Boolean bits, and the word is their weighted sum. -/
def Row.Constraints (r : Row) : Prop :=
  (∀ z < 64, r.β z * r.β z + r.β z = 0) ∧ r.w + lsum (fun z => wt z * r.β z) 64 = 0

/-- A derived output: the linear form `Σ_z coef z · β_z`. -/
def Row.out (r : Row) (o : BOut) : FK := lsum (fun z => o.coef z * r.β z) 64

theorem bool_of_idem {b : FK} (h : b * b + b = 0) : b = 0 ∨ b = 1 := by
  have : b * (b + 1) = 0 := by rw [mul_add, mul_one, h]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · right
    have := congrArg (· + 1) h
    simpa [add_assoc, CharTwo.add_self_eq_zero] using this

theorem FK.eq_neg_of_add {a b : FK} (h : a + b = 0) : a = b := by
  have := congrArg (· + b) h
  simpa [add_assoc, CharTwo.add_self_eq_zero] using this

/-- A Boolean bit column times a word. -/
theorem ubit_mul_bit (c : UInt64) {b : FK} (hb : b = 0 ∨ b = 1) (i : Nat) :
    ubit ((⟨c⟩ : FK) * b).val i = (decide (b = 1) && ubit c i) := by
  rcases hb with rfl | rfl
  · rw [mul_zero]; simp [ubit_val_zero, show ((0 : FK) = 1) ↔ False from by decide]
  · rw [mul_one]; simp

theorem BOut.dst_lt {o : BOut} (ho : o.Valid) {z : Nat} (hz : z < 64) (hh : o.hit z = true) :
    o.dst z < 64 := by
  cases o <;> simp_all [BOut.Valid, BOut.hit, BOut.dst] <;> omega

theorem BOut.dst_inj (o : BOut) {z z' : Nat} (hh : o.hit z = true) (hh' : o.hit z' = true)
    (h : o.dst z = o.dst z') : z = z' := by
  cases o with
  | fld z₀ m d =>
    simp only [BOut.hit, BOut.dst, decide_eq_true_eq] at hh hh' h; omega
  | _ => simp_all [BOut.hit, BOut.dst] <;> omega

/-- Bit `i < 64` of a valid output word: the source bit when it is hit. -/
theorem BOut.ubit_word {o : BOut} (ho : o.Valid) (w : UInt64) {i : Nat} (hi : i < 64) :
    ubit (o.word w) i = true ↔ ∃ z < 64, (o.hit z && ubit w z) = true ∧ o.dst z = i := by
  cases o with
  | shl k =>
    simp only [BOut.Valid] at ho
    simp only [BOut.word, ubit_shl w ho, BOut.hit, BOut.dst, hi, decide_true, Bool.true_and,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨i - k, by omega, ⟨by omega, h2⟩, by omega⟩
    · rintro ⟨z, hz, ⟨h1, h2⟩, rfl⟩; exact ⟨by omega, by simpa using h2⟩
  | shr k =>
    simp only [BOut.Valid] at ho
    simp only [BOut.word, ubit_shr w ho, BOut.hit, BOut.dst, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro h
      have : k + i < 64 := by
        by_contra hc; rw [ubit_ge _ (by omega)] at h; exact absurd h (by simp)
      exact ⟨k + i, this, ⟨by omega, h⟩, by omega⟩
    · rintro ⟨z, hz, ⟨h1, h2⟩, rfl⟩; rwa [show k + (z - k) = z by omega]
  | bit z₀ =>
    simp only [BOut.Valid] at ho
    simp only [BOut.word, ubit_and, ubit_shr w ho, ubit_one, BOut.hit, BOut.dst,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨z₀, ho, ⟨rfl, by simpa using h1⟩, by omega⟩
    · rintro ⟨z, hz, ⟨rfl, h2⟩, h3⟩; exact ⟨by rw [show z + i = z by omega]; exact h2, by omega⟩
  | fld z₀ m d =>
    obtain ⟨h0, h1, h2⟩ := ho
    simp only [BOut.word, ubit_shr _ (show 64 - m - d < 64 by omega),
      ubit_shl _ (show 64 - m < 64 by omega), ubit_shr _ h0, BOut.hit, BOut.dst,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨h3, h4⟩, h5⟩
      refine ⟨z₀ + (64 - m - d + i - (64 - m)), ?_, ⟨⟨by omega, by omega, by omega⟩, h5⟩, by omega⟩
      by_contra hc; rw [ubit_ge _ (by omega)] at h5; exact absurd h5 (by simp)
    · rintro ⟨z, hz, ⟨⟨h3, h4, h5⟩, h6⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by rwa [show z₀ + (64 - m - d + (z - z₀ + d) - (64 - m)) = z by omega]⟩

/-- **`BITS` soundness**: the constraints force bit column `z` to be bit `z` of `w`, and every
valid derived output to be its word function of `w`. -/
theorem row_sound {r : Row} (h : r.Constraints) :
    (∀ z < 64, r.β z = if ubit r.w.val z then 1 else 0) ∧
      ∀ o : BOut, o.Valid → r.out o = ⟨o.word r.w.val⟩ := by
  have hb : ∀ z < 64, r.β z = 0 ∨ r.β z = 1 := fun z hz => bool_of_idem (h.1 z hz)
  have hw : r.w = lsum (fun z => wt z * r.β z) 64 := FK.eq_neg_of_add h.2
  have hbit : ∀ i < 64, ubit r.w.val i = decide (r.β i = 1) := by
    intro i hi
    have := ubit_lsum (fun z => wt z * r.β z) (fun z => decide (r.β z = 1)) id i 64
      (fun z hz => by
        rw [wt, ubit_mul_bit _ (hb z hz), ubit_one_shl hz]; simp [eq_comm])
      (fun z _ z' _ _ _ h => h)
    rw [← hw] at this
    apply Bool.eq_iff_iff.mpr
    rw [this]
    simp only [id, decide_eq_true_eq]
    exact ⟨fun ⟨z, _, h1, h2⟩ => h2 ▸ h1, fun h1 => ⟨i, hi, h1, rfl⟩⟩
  refine ⟨fun z hz => ?_, fun o ho => ?_⟩
  · rw [hbit z hz]; rcases hb z hz with h0 | h1 <;> simp [*]
  · suffices key : (r.out o).val = o.word r.w.val by rw [← key]
    apply u64_ext
    intro i hi
    apply Bool.eq_iff_iff.mpr
    rw [BOut.ubit_word ho _ hi, Row.out,
      ubit_lsum _ (fun z => o.hit z && decide (r.β z = 1)) o.dst i 64 (fun z hz => by
        rw [BOut.coef]
        split
        · rename_i hh
          rw [ubit_mul_bit _ (hb z hz), ubit_one_shl (BOut.dst_lt ho hz hh)]
          simp [hh, eq_comm, Bool.and_comm]
        · rename_i hh
          rw [zero_mul, ubit_val_zero]; simp [hh])
      (fun z _ z' _ h1 h2 h => o.dst_inj (by simp only [Bool.and_eq_true] at h1; exact h1.1)
        (by simp only [Bool.and_eq_true] at h2; exact h2.1) h)]
    constructor
    · rintro ⟨z, hz, h1, h2⟩; exact ⟨z, hz, by rw [hbit z hz]; exact h1, h2⟩
    · rintro ⟨z, hz, h1, h2⟩; exact ⟨z, hz, by rw [← hbit z hz]; exact h1, h2⟩

end Lvm.Bits
