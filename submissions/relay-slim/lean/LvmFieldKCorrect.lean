-- Ported from `rf-k` `submissions/flock-recursive/lean/FRFieldBaseCorrect.lean` (branch kk/base at 8bff272b),
-- renamed `FR.B64` → `Lvm.FK`; the `beta`/`mulBeta` lemmas dropped. FR's file is a copy of spartan-srom's
-- `SpartanSromFieldBaseCorrect.lean` with the product proved through `P_clmul64`.
import LvmFieldK
import CompPoly.Fields.Binary.BF64.Bytes

/-!
# `FK` agrees with CompPoly's `BF64`

`toBF64 : FK → BF64` reads the word as CompPoly's `BitVec 64` coordinates. It is a bijection
(`equivBF64`) that commutes with every operation, and `FK` is a field through it.

## Main statements

* `toBF64_add`, `toBF64_mul`, `toBF64_sq`, `toBF64_inv`: the word operations are `BF64`'s.
* `ringEquivBF64 : FK ≃+* BF64`: the bijection as a ring isomorphism.
* `instField`: `FK` is a field, with computable word operations.
* `card_FK`: every enumeration of `FK` has `2 ^ 64` elements.
* `toBytes_eq`, `ofBytes_eq`: the byte codec is `ByteCodec BF64`'s.

## How the product is proved

`mulLoop` is proved against CompPoly's specification, not against its `carryLessMul`: every word
denotes a polynomial over `ZMod 2` (CompPoly's `toPoly`), and the loop keeps the polynomial
`lo + x^64 hi + a (bl + x^64 bh)` invariant (`mulStep_inv`); `reduce` maps `lo + x^64 hi` to the
same class of `AdjoinRoot basePoly` (`mk_reduce`). The class map is CompPoly's `BF64.toQuot`,
which is injective and multiplicative (`BF64.toQuot_injective`, `BF64.toQuot_mul`), so the word
product is `BF64`'s product.
-/

namespace Lvm.FK

open Polynomial BinaryField

/-! ## The map to `BF64` -/

/-- The `BF64` element with the same polynomial-basis bits. -/
def toBF64 (a : FK) : BF64 := BF64.ofBitVec a.val.toBitVec

/-- The `FK` element with the same polynomial-basis bits. -/
def ofBF64 (a : BF64) : FK := ⟨UInt64.ofBitVec a.toBitVec⟩

@[simp] theorem toBF64_ofBF64 (a : BF64) : toBF64 (ofBF64 a) = a := rfl

@[simp] theorem ofBF64_toBF64 (a : FK) : ofBF64 (toBF64 a) = a := rfl

/-- `FK` and `BF64` are in bijection by their common coordinates. -/
def equivBF64 : FK ≃ BF64 where
  toFun := toBF64
  invFun := ofBF64
  left_inv := ofBF64_toBF64
  right_inv := toBF64_ofBF64

theorem toBF64_injective : Function.Injective toBF64 := equivBF64.injective

theorem toBF64_inj {a b : FK} : toBF64 a = toBF64 b ↔ a = b := toBF64_injective.eq_iff

/-! ## Words as polynomials (proof helpers) -/

/-- The polynomial over `ZMod 2` denoted by a word, CompPoly's `toPoly`. -/
noncomputable abbrev P (x : UInt64) : (ZMod 2)[X] := toPoly x.toBitVec

/-- The class of a word in `AdjoinRoot basePoly`, which is `BF64.toQuot` of its `BF64`. -/
noncomputable abbrev Q (x : UInt64) : BF64.BF64Quot := AdjoinRoot.mk BF64.basePoly (P x)

theorem toQuot_toBF64 (a : FK) : BF64.toQuot (toBF64 a) = Q a.val := rfl

private theorem coeff_toPoly (x : BitVec 64) (n : ℕ) :
    (toPoly x).coeff n = if x.getLsbD n then 1 else 0 := by
  rw [toPoly_coeff]
  by_cases h : n < 64
  · simp [h, BitVec.getLsb, BitVec.getLsbD]
  · simp [h, BitVec.getLsbD_of_ge x n (by omega)]

/-- Multiplying by `x^k` splits into the truncated left shift and the bits shifted out. -/
private theorem toPoly_mul_X_pow (x : BitVec 64) (k : ℕ) (hk : k ≤ 64) :
    toPoly x * X ^ k = toPoly (x <<< k) + X ^ 64 * toPoly (x >>> (64 - k)) := by
  ext n
  simp only [coeff_add, coeff_mul_X_pow', coeff_X_pow_mul', coeff_toPoly,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h64 : 64 ≤ n
  · have : ¬ n < 64 := by omega
    have e : 64 - k + (n - 64) = n - k := by omega
    simp [h64, this, e, show k ≤ n by omega]
  · by_cases hkn : k ≤ n <;> simp [h64, hkn, show n < 64 by omega]

/-- The low bit splits off a word: `a = x * (a >>> 1) + (a &&& 1)`. -/
private theorem toPoly_split_low (a : BitVec 64) :
    toPoly a = toPoly (a >>> 1) * X + toPoly (a &&& 1#64) := by
  ext n
  rcases n with _ | n
  · simp [coeff_toPoly]
  · simp [coeff_toPoly, BitVec.getLsbD_and, BitVec.getLsbD_one, coeff_mul_X,
      BitVec.getLsbD_ushiftRight, Nat.add_comm 1 n]

theorem P_xor (x y : UInt64) : P (x ^^^ y) = P x + P y := by
  simp [P, toPoly_xor]

private theorem P_zero : P 0 = 0 := toPoly_zero_eq_zero

/-- `toPoly_mul_X_pow` for words; the caller supplies the two shifts as `BitVec` shifts. -/
theorem P_shiftLeft (x : UInt64) (k : ℕ) (hk : k ≤ 64) {s r : UInt64}
    (hs : (x <<< s).toBitVec = x.toBitVec <<< k)
    (hr : (x >>> r).toBitVec = x.toBitVec >>> (64 - k)) :
    P (x <<< s) = P x * X ^ k - X ^ 64 * P (x >>> r) := by
  have h := toPoly_mul_X_pow x.toBitVec k hk
  simp only [P, hs, hr]
  linear_combination (-1 : (ZMod 2)[X]) * h

/-- The mask `0 - (a &&& 1)` selects `x` exactly when bit `0` of `a` is set. -/
private theorem and_mask (a x : UInt64) :
    x &&& (0 - (a &&& 1)) = if a.toBitVec.getLsbD 0 then x else 0 := by
  have h : a &&& 1 = if a.toBitVec.getLsbD 0 then 1 else 0 := by
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    rintro (_ | i) hi <;> split_ifs <;> simp_all
  rw [h]
  split_ifs <;> simp

/-! ## The product loop -/

/-- The polynomial a product state stands for: the accumulator plus what is left to add. -/
private noncomputable def Φ (s : MulState) : (ZMod 2)[X] :=
  P s.lo + X ^ 64 * P s.hi + P s.a * (P s.bl + X ^ 64 * P s.bh)

/-- The bounds that keep the shifted multiplicand inside 128 bits: `r` bits of `a` are left. -/
private def Good (r : ℕ) (s : MulState) : Prop := s.a.toNat < 2 ^ r ∧ s.bh.toNat < 2 ^ (64 - r)

/-- One step keeps the denoted polynomial, provided the top bit of `bh` is clear. -/
private theorem mulStep_inv (s : MulState) (h : s.bh.toNat < 2 ^ 63) :
    Φ (mulStep s) = Φ s := by
  have hbh : s.bh >>> 63 = 0 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    simpa using h
  have e1 := P_shiftLeft s.bl 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have e2 := P_shiftLeft s.bh 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have hand : s.a.toBitVec &&& 1#64 = if s.a.toBitVec.getLsbD 0 then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases i with _ | i
    · split_ifs with h <;> simp_all [BitVec.getLsbD_eq_getElem]
    · split_ifs <;> simp
  have ea : P s.a = P (s.a >>> 1) * X + if s.a.toBitVec.getLsbD 0 then 1 else 0 := by
    have h1 : toPoly (1#64) = 1 := toPoly_one_eq_one (by norm_num)
    have hA : (s.a >>> 1).toBitVec = s.a.toBitVec >>> 1 := by simp
    simp only [P, hA]
    rw [toPoly_split_low s.a.toBitVec, hand]
    split_ifs <;> simp [h1, toPoly_zero_eq_zero]
  simp only [Φ, mulStep, P_xor, and_mask, hbh, P_zero, mul_zero, sub_zero] at e2 ⊢
  rw [e1, e2, ea]
  split_ifs <;> (try simp only [P_zero]) <;> ring

/-- One step uses up one bit of `a` and keeps the multiplicand inside 128 bits. -/
private theorem mulStep_good {r : ℕ} {s : MulState} (h : Good (r + 1) s) (hr : r < 64) :
    Good r (mulStep s) ∧ Φ (mulStep s) = Φ s := by
  obtain ⟨ha, hb⟩ := h
  have hb63 : s.bh.toNat < 2 ^ 63 :=
    lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨⟨?_, ?_⟩, mulStep_inv s hb63⟩
  · simp only [mulStep, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    simpa [pow_succ] using ha
  · simp only [mulStep, UInt64.toNat_xor, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    refine Nat.xor_lt_two_pow ?_ ?_
    · refine lt_of_le_of_lt (Nat.mod_le _ _) ?_
      have : 64 - r = (64 - (r + 1)) + 1 := by omega
      rw [this, pow_succ]
      simpa using hb
    · have : s.bl.toNat / 2 ^ 63 < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]; exact s.bl.toNat_lt
      exact lt_of_lt_of_le this
        (by simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ 64 - r by omega))

/-! ## The reduction -/

/-- The bits of `reduce`'s fold word `d` above position 60 are those of `hi`. -/
private theorem fold_shiftRight (hi : UInt64) (s : UInt64) (hs : 60 ≤ s.toNat)
    (hs' : s.toNat < 64) :
    (hi ^^^ (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)) >>> s = hi >>> s := by
  have key : ∀ x : UInt64, (x >>> s).toBitVec = x.toBitVec >>> s.toNat := by
    intro x; simp [Nat.mod_eq_of_lt hs']
  apply UInt64.toBitVec_inj.mp
  rw [key, key]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  have k63 : (hi >>> 63).toBitVec = hi.toBitVec >>> 63 := by simp
  have k61 : (hi >>> 61).toBitVec = hi.toBitVec >>> 61 := by simp
  have k60 : (hi >>> 60).toBitVec = hi.toBitVec >>> 60 := by simp
  rw [k63, k61, k60]
  simp only [BitVec.getLsbD_ushiftRight]
  rw [BitVec.getLsbD_of_ge _ (63 + (s.toNat + i)) (by omega),
    BitVec.getLsbD_of_ge _ (61 + (s.toNat + i)) (by omega),
    BitVec.getLsbD_of_ge _ (60 + (s.toNat + i)) (by omega)]
  simp

/-- `reduce lo hi` is the class of `lo + x^64 hi` modulo the `GF(2^64)` modulus. -/
theorem mk_reduce (lo hi : UInt64) : Q (reduce lo hi) = AdjoinRoot.mk BF64.basePoly
    (P lo + X ^ 64 * P hi) := by
  set d := hi ^^^ (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60) with hd
  have e1 := P_shiftLeft d 1 (by norm_num) (s := 1) (r := 63) (by simp) (by simp)
  have e3 := P_shiftLeft d 3 (by norm_num) (s := 3) (r := 61) (by simp) (by simp)
  have e4 := P_shiftLeft d 4 (by norm_num) (s := 4) (r := 60) (by simp) (by simp)
  rw [fold_shiftRight hi 63 (by decide) (by decide)] at e1
  rw [fold_shiftRight hi 61 (by decide) (by decide)] at e3
  rw [fold_shiftRight hi 60 (by decide) (by decide)] at e4
  have ed : P d = P hi + P (hi >>> 63) + P (hi >>> 61) + P (hi >>> 60) := by
    simp only [hd, P_xor]
  have er : P (reduce lo hi) = P lo + P d + P (d <<< 1) + P (d <<< 3) + P (d <<< 4) := by
    simp only [reduce, P_xor, hd]
  rw [Q, er, e1, e3, e4, ed, AdjoinRoot.mk_eq_mk, BF64.basePoly_eq]
  refine ⟨-(P hi + P (hi >>> 63) + P (hi >>> 61) + P (hi >>> 60)), ?_⟩
  linear_combination ((X ^ 4 + X ^ 3 + X + 1) * (P hi + P (hi >>> 63) + P (hi >>> 61) +
    P (hi >>> 60))) * ZMod2Poly.two_eq_zero

/-! ## The product -/

/-- `n` rounds of the loop compute the class of the polynomial the start state stands for. -/
private theorem mulLoop_spec (n : ℕ) (a bl bh lo hi : UInt64) (hn : 4 * n ≤ 64)
    (h : Good (4 * n) ⟨a, bl, bh, lo, hi⟩) :
    Q (mulLoop n a bl bh lo hi) = AdjoinRoot.mk BF64.basePoly (Φ ⟨a, bl, bh, lo, hi⟩) := by
  induction n generalizing a bl bh lo hi with
  | zero =>
    have ha : a = 0 := UInt64.toNat_inj.mp (by simpa [Good] using h.1)
    simp [mulLoop, mk_reduce, Φ, ha, P_zero]
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 3 + 1 by ring] at h
    obtain ⟨g1, e1⟩ := mulStep_good h (by omega)
    obtain ⟨g2, e2⟩ := mulStep_good g1 (by omega)
    obtain ⟨g3, e3⟩ := mulStep_good g2 (by omega)
    obtain ⟨g4, e4⟩ := mulStep_good g3 (by omega)
    rw [mulLoop]
    set s4 := mulStep (mulStep (mulStep (mulStep ⟨a, bl, bh, lo, hi⟩)))
    exact (ih s4.a s4.bl s4.bh s4.lo s4.hi (by omega) g4).trans
      (congrArg _ (e4.trans (e3.trans (e2.trans e1))))

/-- The class of v3's loop product is the product of the classes. -/
private theorem Q_mulLoop (a b : FK) : Q (mulLoop 16 a.val b.val 0 0 0) = Q a.val * Q b.val := by
  rw [mulLoop_spec 16 _ _ _ _ _ (by norm_num) ⟨a.val.toNat_lt, by simp⟩, ← map_mul]
  simp [Φ, P_zero]

/-! ## The product of words below `2^32` (`clmul32`)

A natural number below `2^64` is the value at `2` of the `ℕ`-polynomial of its bits (`bpN`). If
`u` and `v` have bits only at positions `≡ r` and `≡ s (mod 4)` below `32` (`Holes`), the
coefficients of `bpN u * bpN v` are at most `8` and sit at positions `≡ r + s`, so the bits of
`u * v` there are the coefficients' parities (`testBit_mul_holes`, from `testBit_eval_two_sparse`:
a column below `16` never reaches the next position of its class). Summing the four products of
each class gives the carry-less product (`P_clmul32`). -/

private theorem eval_two_divX (D : ℕ[X]) : D.eval 2 = 2 ^ 1 * (divX D).eval 2 + D.coeff 0 := by
  conv_lhs => rw [← divX_mul_X_add D]
  simp only [eval_add, eval_mul, eval_X, eval_C]; ring

/-- A polynomial with coefficients below `2` evaluates at `2` to the number with those bits. -/
private theorem testBit_eval_two_dense (n : ℕ) : ∀ (D : ℕ[X]), (∀ k, D.coeff k < 2) →
    (D.eval 2).testBit n = decide (D.coeff n = 1) := by
  induction n with
  | zero =>
    intro D h
    rw [eval_two_divX, Nat.testBit_two_pow_mul_add _ (h 0)]
    rw [ite_eq_left (by norm_num), Nat.testBit_zero]
    rcases (by have := h 0; omega : D.coeff 0 = 0 ∨ D.coeff 0 = 1) with h' | h' <;> simp [h']
  | succ n ih =>
    intro D h
    rw [eval_two_divX, Nat.testBit_two_pow_mul_add _ (h 0), ite_eq_right (by omega),
      Nat.add_sub_cancel, ih _ fun k => by rw [coeff_divX]; exact h _, coeff_divX]

private theorem testBit_eval_two_sparse (n : ℕ) : ∀ (D : ℕ[X]) (t : ℕ), (∀ k, D.coeff k < 16) →
    (∀ k, D.coeff k ≠ 0 → k % 4 = t) → n % 4 = t →
    (D.eval 2).testBit n = decide (D.coeff n % 2 = 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D t hb hs hn
  by_cases h0 : D.coeff 0 = 0
  · rw [eval_two_divX, h0, Nat.testBit_two_pow_mul_add _ (show 0 < 2 ^ 1 by norm_num)]
    split_ifs with hlt
    · obtain rfl : n = 0 := by omega
      simp [h0]
    · rw [ih (n - 1) (by omega) (divX D) ((t + 3) % 4) (fun k => by rw [coeff_divX]; exact hb _)
          (fun k hk => by rw [coeff_divX] at hk; have := hs _ hk; omega) (by omega),
        coeff_divX, Nat.sub_add_cancel (by omega)]
  · have ht : t = 0 := by have := hs 0 h0; omega
    have z : ∀ k, k % 4 ≠ 0 → D.coeff k = 0 := fun k hk => by
      by_contra hne; exact hk (by rw [hs k hne, ht])
    set D4 := divX (divX (divX (divX D)))
    have c4 : ∀ k, D4.coeff k = D.coeff (k + 4) := fun k => by simp only [D4, coeff_divX]
    have e : D.eval 2 = 2 ^ 4 * D4.eval 2 + D.coeff 0 := by
      rw [eval_two_divX D, eval_two_divX (divX D), eval_two_divX (divX (divX D)),
        eval_two_divX (divX (divX (divX D)))]
      simp only [coeff_divX, z 1 (by decide), z 2 (by decide), z 3 (by decide)]
      ring
    rw [e, Nat.testBit_two_pow_mul_add _ (hb 0)]
    split_ifs with hlt
    · have : n = 0 := by omega
      subst this; simp
    · rw [ih (n - 4) (by omega) D4 0 (fun k => by rw [c4]; exact hb _)
        (fun k hk => by rw [c4] at hk; have := hs _ hk; omega) (by omega), c4,
        Nat.sub_add_cancel (by omega)]


/-- The `ℕ`-polynomial of the bits of `u` below `2^64`. -/
private noncomputable def bpN (u : ℕ) : ℕ[X] :=
  ∑ i ∈ Finset.range 64, monomial i (if u.testBit i then 1 else 0)

private theorem coeff_bpN (u n : ℕ) : (bpN u).coeff n = if n < 64 ∧ u.testBit n then 1 else 0 := by
  rw [bpN, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range 64) n (fun i => if u.testBit i then 1 else 0)]
  simp only [Finset.mem_range]
  by_cases hn : n < 64 <;> simp [hn]

private theorem eval_bpN {u : ℕ} (hu : u < 2 ^ 64) : (bpN u).eval 2 = u :=
  Nat.eq_of_testBit_eq fun n => by
    rw [testBit_eval_two_dense n _ (fun k => by rw [coeff_bpN]; split_ifs <;> omega), coeff_bpN]
    by_cases hn : n < 64
    · by_cases hb : u.testBit n <;> simp [hn, hb]
    · simp [hn, Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (n := 2)
        (by norm_num) (show 64 ≤ n by omega)))]

/-- `u` has bits only at positions `≡ r (mod 4)` below `32`. -/
private def Holes (u r : ℕ) : Prop := ∀ i, u.testBit i = true → i % 4 = r ∧ i < 32

private theorem Holes.lt {u r : ℕ} (h : Holes u r) : u < 2 ^ 32 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    by_contra hb; exact absurd (h i (by simpa using hb)).2 (by omega)

private theorem Holes.coeff_le {u r : ℕ} (h : Holes u r) (i : ℕ) :
    (bpN u).coeff i ≤ if i % 4 = r ∧ i < 32 then 1 else 0 := by
  rw [coeff_bpN]
  split_ifs with h1 h2 <;> first | omega | exact absurd (h i h1.2) h2

private theorem support_holes {u v r s : ℕ} (hu : Holes u r) (hv : Holes v s) {n : ℕ}
    (h : (bpN u * bpN v).coeff n ≠ 0) : n % 4 = (r + s) % 4 ∧ n < 64 := by
  rw [coeff_mul] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_antidiagonal] at hx
  rw [coeff_bpN, coeff_bpN] at hne
  split_ifs at hne with h1 h2
  · obtain ⟨r1, r2⟩ := hu _ h1.2; obtain ⟨s1, s2⟩ := hv _ h2.2; omega
  all_goals simp at hne

private theorem coeff_holes_le {u v r : ℕ} (hu : Holes u r) (hr : r < 4) (n : ℕ) :
    (bpN u * bpN v).coeff n ≤ 8 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (bpN u).coeff i *
    (bpN v).coeff j)]
  calc ∑ i ∈ Finset.range n.succ, (bpN u).coeff i * (bpN v).coeff (n - i)
      ≤ ∑ i ∈ Finset.range n.succ, if i % 4 = r ∧ i < 32 then 1 else 0 :=
        Finset.sum_le_sum fun i _ => by
          have h1 := hu.coeff_le i
          have h2 : (bpN v).coeff (n - i) ≤ 1 := by rw [coeff_bpN]; split_ifs <;> omega
          calc (bpN u).coeff i * (bpN v).coeff (n - i) ≤ (bpN u).coeff i * 1 :=
                Nat.mul_le_mul_left _ h2
            _ ≤ _ := by rw [Nat.mul_one]; exact h1
    _ ≤ ∑ i ∈ Finset.range 32, if i % 4 = r ∧ i < 32 then 1 else 0 := by
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
    _ = 8 := by
        rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> decide

/-- **The integer product of two words with holes**, read at the positions of its residue class,
is the carry-less product. -/
private theorem testBit_mul_holes {u v r s : ℕ} (hu : Holes u r) (hv : Holes v s) (hr : r < 4)
    {n : ℕ} (hn : n % 4 = (r + s) % 4) :
    (u * v).testBit n = decide ((bpN u * bpN v).coeff n % 2 = 1) := by
  have hu64 : u < 2 ^ 64 := lt_trans hu.lt (by norm_num)
  have hv64 : v < 2 ^ 64 := lt_trans hv.lt (by norm_num)
  have e : u * v = (bpN u * bpN v).eval 2 := by rw [eval_mul, eval_bpN hu64, eval_bpN hv64]
  rw [e]
  exact testBit_eval_two_sparse n _ ((r + s) % 4)
    (fun k => lt_of_le_of_lt (coeff_holes_le (v := v) hu hr k) (by norm_num))
    (fun k hk => (support_holes hu hv hk).1) hn


/-- The bits of a constant below `2^k`, from its bits below `k`. -/
private theorem testBit_const {m k : ℕ} {p : ℕ → Bool} (hm : m < 2 ^ k)
    (h : ∀ i < k, m.testBit i = p i) (hp : ∀ i, k ≤ i → p i = false) (i : ℕ) :
    m.testBit i = p i := by
  by_cases hi : i < k
  · exact h i hi
  · rw [hp i (by omega), Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The input masks: bits `≡ r (mod 4)` below `32`. -/
private def maskIn : ℕ → ℕ
  | 0 => 0x11111111
  | 1 => 0x22222222
  | 2 => 0x44444444
  | _ => 0x88888888

private theorem testBit_maskIn {r : ℕ} (hr : r < 4) (i : ℕ) :
    (maskIn r).testBit i = decide (i % 4 = r ∧ i < 32) := by
  refine testBit_const (k := 32) (p := fun i => decide (i % 4 = r ∧ i < 32)) ?_ ?_
    (fun i hi => by simp; omega) i <;>
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> decide

private theorem holes_maskIn (u : ℕ) {r : ℕ} (hr : r < 4) : Holes (u &&& maskIn r) r := by
  intro i hi
  rw [Nat.testBit_and, testBit_maskIn hr, Bool.and_eq_true, decide_eq_true_eq] at hi
  exact hi.2


private theorem testBit_lt_of_lt {x k : ℕ} (hx : x < 2 ^ k) {i : ℕ} (hi : k ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

private theorem bpN_split {x : ℕ} (hx : x < 2 ^ 32) :
    bpN x = ∑ r ∈ Finset.range 4, bpN (x &&& maskIn r) := by
  ext i
  rw [finsetSum_coeff]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, coeff_bpN, Nat.testBit_and,
    testBit_maskIn (r := 0) (by norm_num), testBit_maskIn (r := 1) (by norm_num),
    testBit_maskIn (r := 2) (by norm_num), testBit_maskIn (r := 3) (by norm_num)]
  by_cases hb : x.testBit i
  · have : i < 32 := by by_contra h; rw [testBit_lt_of_lt hx (by omega)] at hb; simp at hb
    simp only [hb, this, show i < 64 by omega, and_self, Bool.true_and, decide_eq_true_eq, and_true,
      true_and, ↓reduceIte]
    split_ifs <;> omega
  · simp [hb]

private theorem coeff_mul_split {x y : ℕ} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (n : ℕ) :
    (bpN x * bpN y).coeff n =
      ∑ r ∈ Finset.range 4,
        (bpN (x &&& maskIn r) * bpN (y &&& maskIn ((n + 4 - r) % 4))).coeff n := by
  rw [bpN_split hx, bpN_split hy, Finset.sum_mul_sum, finsetSum_coeff]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [finsetSum_coeff]
  refine Finset.sum_eq_single_of_mem _ (by simp; omega) fun s hs hne => ?_
  rw [Finset.mem_range] at hs
  by_contra h
  have := (support_holes (holes_maskIn x hr) (holes_maskIn y hs) h).1
  omega

private theorem coeff_mul_zero {x y : ℕ} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) {n : ℕ} (hn : 64 ≤ n) :
    (bpN x * bpN y).coeff n = 0 := by
  rw [coeff_mul_split hx hy]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.mem_range] at hr
  by_contra h
  have := (support_holes (holes_maskIn x hr) (holes_maskIn y (Nat.mod_lt _ (by norm_num))) h).2
  omega

private theorem decide_odd_add (a b : ℕ) :
    decide ((a + b) % 2 = 1) = (decide (a % 2 = 1) ^^ decide (b % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;> simp [Nat.add_mod, h, h']

private theorem prod_bit {x y : UInt64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) {r s : ℕ}
    (hr : r < 4) (hs : s < 4) {mr ms : UInt64} (hmr : mr.toNat = maskIn r)
    (hms : ms.toNat = maskIn s)
    {n : ℕ} (hn : n % 4 = (r + s) % 4) :
    ((x &&& mr) * (y &&& ms)).toNat.testBit n =
      decide ((bpN (x.toNat &&& maskIn r) * bpN (y.toNat &&& maskIn s)).coeff n % 2 = 1) := by
  rw [UInt64.toNat_mul, UInt64.toNat_and, UInt64.toNat_and, hmr, hms, Nat.mod_eq_of_lt]
  · exact testBit_mul_holes (holes_maskIn _ hr) (holes_maskIn _ hs) hr hn
  · calc (x.toNat &&& maskIn r) * (y.toNat &&& maskIn s) < 2 ^ 32 * 2 ^ 32 :=
          Nat.mul_lt_mul'' (lt_of_le_of_lt Nat.and_le_left hx) (lt_of_le_of_lt Nat.and_le_left hy)
      _ = 2 ^ 64 := by norm_num

/-- One residue class of the product: the four integer products whose classes add up to `t`. -/
private theorem z_bit {x y : UInt64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) {n t : ℕ}
    (ht : n % 4 = t) {m0 m1 m2 m3 : UInt64} (h0 : m0.toNat = maskIn ((t + 4) % 4))
    (h1 : m1.toNat = maskIn ((t + 3) % 4)) (h2 : m2.toNat = maskIn ((t + 2) % 4))
    (h3 : m3.toNat = maskIn ((t + 1) % 4)) :
    ((x &&& 0x11111111) * (y &&& m0) ^^^ (x &&& 0x22222222) * (y &&& m1) ^^^
      (x &&& 0x44444444) * (y &&& m2) ^^^ (x &&& 0x88888888) * (y &&& m3)).toNat.testBit n =
      decide ((bpN x.toNat * bpN y.toNat).coeff n % 2 = 1) := by
  simp only [UInt64.toNat_xor, Nat.testBit_xor]
  rw [prod_bit hx hy (r := 0) (by norm_num) (Nat.mod_lt _ (by norm_num)) rfl h0 (by omega),
    prod_bit hx hy (r := 1) (by norm_num) (Nat.mod_lt _ (by norm_num)) rfl h1 (by omega),
    prod_bit hx hy (r := 2) (by norm_num) (Nat.mod_lt _ (by norm_num)) rfl h2 (by omega),
    prod_bit hx hy (r := 3) (by norm_num) (Nat.mod_lt _ (by norm_num)) rfl h3 (by omega),
    coeff_mul_split hx hy]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, decide_odd_add]
  rw [show (n + 4 - 0) % 4 = (t + 4) % 4 by omega, show (n + 4 - 1) % 4 = (t + 3) % 4 by omega,
    show (n + 4 - 2) % 4 = (t + 2) % 4 by omega, show (n + 4 - 3) % 4 = (t + 1) % 4 by omega]

/-- The output masks: bits `≡ t (mod 4)`. -/
private def maskOut : ℕ → ℕ
  | 0 => 0x1111111111111111
  | 1 => 0x2222222222222222
  | 2 => 0x4444444444444444
  | _ => 0x8888888888888888

private theorem testBit_maskOut {t : ℕ} (ht : t < 4) {n : ℕ} (hn : n < 64) :
    (maskOut t).testBit n = decide (n % 4 = t) := by
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl <;>
    revert n <;> decide

private theorem or4_bit (z0 z1 z2 z3 : UInt64) {n : ℕ} (hn : n < 64) :
    ((z0 &&& 0x1111111111111111) ||| (z1 &&& 0x2222222222222222) |||
      (z2 &&& 0x4444444444444444) ||| (z3 &&& 0x8888888888888888)).toNat.testBit n =
    ((decide (n % 4 = 0) && z0.toNat.testBit n) || (decide (n % 4 = 1) && z1.toNat.testBit n) ||
      (decide (n % 4 = 2) && z2.toNat.testBit n) ||
      (decide (n % 4 = 3) && z3.toNat.testBit n)) := by
  simp only [UInt64.toNat_or, UInt64.toNat_and, Nat.testBit_or, Nat.testBit_and]
  rw [show (0x1111111111111111 : UInt64).toNat = maskOut 0 from rfl,
    show (0x2222222222222222 : UInt64).toNat = maskOut 1 from rfl,
    show (0x4444444444444444 : UInt64).toNat = maskOut 2 from rfl,
    show (0x8888888888888888 : UInt64).toNat = maskOut 3 from rfl,
    testBit_maskOut (by norm_num) hn, testBit_maskOut (by norm_num) hn,
    testBit_maskOut (by norm_num) hn, testBit_maskOut (by norm_num) hn]
  simp only [Bool.and_comm]

/-- **The bits of `clmul32`** are the coefficients of the carry-less product. -/
private theorem testBit_clmul32 {x y : UInt64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32)
    (n : ℕ) :
    (clmul32 x y).toNat.testBit n = decide ((bpN x.toNat * bpN y.toNat).coeff n % 2 = 1) := by
  by_cases hn : 64 ≤ n
  · rw [coeff_mul_zero hx hy hn, testBit_lt_of_lt (clmul32 x y).toNat_lt hn]; rfl
  simp only [clmul32]
  rw [or4_bit _ _ _ _ (by omega)]
  rcases (by omega : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3) with h | h | h | h <;>
    simp only [h, Nat.reduceEqDiff, decide_true, decide_false, Bool.true_and, Bool.false_and,
      Bool.false_or, Bool.or_false] <;>
    refine z_bit hx hy h ?_ ?_ ?_ ?_ <;> rfl



private theorem P_eq_map (w : UInt64) : P w = (bpN w.toNat).map (Nat.castRingHom (ZMod 2)) := by
  ext n
  rw [coeff_map, coeff_bpN, P, coeff_toPoly]
  change (if w.toNat.testBit n then _ else _) = _
  by_cases hn : n < 64
  · by_cases hb : w.toNat.testBit n <;> simp [hn, hb]
  · rw [testBit_lt_of_lt w.toNat_lt (by omega)]; simp [hn]

/-- **`clmul32` is the carry-less product** of two words below `2^32`. -/
private theorem P_clmul32 {x y : UInt64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    P (clmul32 x y) = P x * P y := by
  ext n
  rw [P_eq_map x, P_eq_map y, ← Polynomial.map_mul, coeff_map, P, coeff_toPoly]
  change (if (clmul32 x y).toNat.testBit n then _ else _) = _
  rw [testBit_clmul32 hx hy]
  generalize (bpN x.toNat * bpN y.toNat).coeff n = c
  show _ = (c : ZMod 2)
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

/-! ## The product -/

/-- A word is its low half plus `x^32` times its high half. -/
private theorem P_halves (a : UInt64) : P a = P (a &&& 0xFFFFFFFF) + X ^ 32 * P (a >>> 32) := by
  ext n
  simp only [coeff_add, coeff_X_pow_mul', P, coeff_toPoly]
  change (if a.toNat.testBit n then _ else _) =
    (if (a &&& 0xFFFFFFFF).toNat.testBit n then _ else _) +
    if 32 ≤ n then (if (a >>> 32).toNat.testBit (n - 32) then _ else _) else 0
  rw [UInt64.toNat_and, Nat.testBit_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.testBit_two_pow_sub_one, UInt64.toNat_shiftRight,
    show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.testBit_shiftRight]
  by_cases h : 32 ≤ n
  · simp [h, show ¬ n < 32 by omega, Nat.add_sub_cancel' h]
  · simp [h, show n < 32 by omega]

private theorem lt_and32 (a : UInt64) : (a &&& 0xFFFFFFFF).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_and]; exact lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem lt_shr32 (a : UInt64) : (a >>> 32).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by norm_num)]
  exact a.toNat_lt

private theorem lt_xor32 {a b : UInt64} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a ^^^ b).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_xor]; exact Nat.xor_lt_two_pow ha hb

/-- **`clmul64` is the carry-less product** of two words: Karatsuba over the halves, each half
product by `P_clmul32`. -/
theorem P_clmul64 (a b : UInt64) :
    P (clmul64 a b).lo + X ^ 64 * P (clmul64 a b).hi = P a * P b := by
  have h0 := P_clmul32 (lt_and32 a) (lt_and32 b)
  have h2 := P_clmul32 (lt_shr32 a) (lt_shr32 b)
  have hm := P_clmul32 (lt_xor32 (lt_and32 a) (lt_shr32 a)) (lt_xor32 (lt_and32 b) (lt_shr32 b))
  have es := fun pm : UInt64 => P_shiftLeft pm 32 (by norm_num) (s := 32) (r := 32) (by simp)
    (by simp)
  have ha := P_halves a
  have hb := P_halves b
  dsimp only [clmul64]
  simp only [P_xor, es, hm, h0, h2] at ha hb ⊢
  rw [ha, hb]
  linear_combination (X ^ 32 * (P (a &&& 0xFFFFFFFF) * P (b &&& 0xFFFFFFFF) +
    P (a >>> 32) * P (b >>> 32))) * ZMod2Poly.two_eq_zero

/-- **The class of the word product is the product of the classes**: `clmul64`, then
`reduce`. -/
theorem Q_mul (a b : FK) : Q (a * b).val = Q a.val * Q b.val := by
  rw [show a * b = mul a b from rfl]
  dsimp only [mul]
  rw [mk_reduce, P_clmul64, Q, Q, ← map_mul]

/-- **The product is v3's shift-and-add loop's** (the verifier's arithmetic is unchanged). -/
theorem mul_eq_mulLoop (a b : FK) : a * b = ⟨mulLoop 16 a.val b.val 0 0 0⟩ := by
  apply toBF64_injective
  apply BF64.toQuot_injective
  rw [toQuot_toBF64, toQuot_toBF64, Q_mul, Q_mulLoop]

/-- **Multiplication is `BF64`'s.** -/
@[simp] theorem toBF64_mul (a b : FK) : toBF64 (a * b) = toBF64 a * toBF64 b := by
  apply BF64.toQuot_injective
  rw [BF64.toQuot_mul, toQuot_toBF64, toQuot_toBF64, toQuot_toBF64, Q_mul]

/-! ## Squaring -/

/-! ### `spread`, one mask-and-shift step at a time

After the steps down to chunk size `c`, bit `j` of the word is bit `j / (2c) * c + j % (2c)` of
the input when `j % (2c) < c`, and `0` otherwise (`c = 32` after the first mask, `c = 1` at the
end). One lemma covers every step (`spread_stage`); its mask, shift and index arithmetic are
decided by the kernel over the 64 bit positions for each `c`. -/

/-- One mask-and-shift step of `spread`, from chunks of `2 c` bits to chunks of `c`. -/
private theorem spread_stage (c : ℕ) (s m x y : UInt64) (hy : ∀ j < 64, y.toBitVec.getLsbD j =
      (decide (j % (4 * c) < 2 * c) && x.toBitVec.getLsbD (j / (4 * c) * (2 * c) + j % (4 * c))))
    (hs : s.toNat % 64 = c := by decide)
    (hm : ∀ j < 64, m.toBitVec.getLsbD j = decide (j % (2 * c) < c) := by decide +kernel)
    (h1 : ∀ j < 64, j % (2 * c) < c → j % (4 * c) < 2 * c →
      j / (4 * c) * (2 * c) + j % (4 * c) = j / (2 * c) * c + j % (2 * c) ∧
        (c ≤ j → ¬ (j - c) % (4 * c) < 2 * c) := by decide +kernel)
    (h2 : ∀ j < 64, j % (2 * c) < c → ¬ j % (4 * c) < 2 * c → c ≤ j ∧ (j - c) % (4 * c) < 2 * c ∧
      (j - c) / (4 * c) * (2 * c) + (j - c) % (4 * c) = j / (2 * c) * c + j % (2 * c) :=
        by decide +kernel) :
    ∀ j < 64, ((y ||| (y <<< s)) &&& m).toBitVec.getLsbD j =
      (decide (j % (2 * c) < c) && x.toBitVec.getLsbD (j / (2 * c) * c + j % (2 * c))) := by
  intro j hj
  have hsh : (y <<< s).toBitVec = y.toBitVec <<< c := by simp [hs]
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, hsh, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hm j hj, hy j hj]
  by_cases hmc : j % (2 * c) < c
  · by_cases ht : j % (4 * c) < 2 * c
    · obtain ⟨e, h3⟩ := h1 j hj hmc ht
      by_cases hh : j < c
      · simp [hmc, ht, e, hh, hj]
      · rw [hy (j - c) (by omega)]
        simp [hmc, ht, e, hh, hj, h3 (by omega)]
    · obtain ⟨hcj, h4, e⟩ := h2 j hj hmc ht
      rw [hy (j - c) (by omega)]
      simp [hmc, ht, e, hj, h4, show ¬ j < c by omega]
  · simp [hmc]

/-- `spread` moves bit `i` of the low half to bit `2 i` and clears the odd bits. -/
private theorem spread_getLsbD (x : UInt64) (j : ℕ) (hj : j < 64) :
    (spread x).toBitVec.getLsbD j = (decide (j % 2 = 0) && x.toBitVec.getLsbD (j / 2)) := by
  have h32 : ∀ j < 64, (x &&& 0x00000000FFFFFFFF).toBitVec.getLsbD j =
      (decide (j % 64 < 32) && x.toBitVec.getLsbD (j / 64 * 32 + j % 64)) := fun j hj => by
    have hm : (0x00000000FFFFFFFF : UInt64).toBitVec.getLsbD j = decide (j < 32) := by
      revert j; decide +kernel
    simp only [UInt64.toBitVec_and, BitVec.getLsbD_and, hm, Nat.mod_eq_of_lt hj,
      Nat.div_eq_of_lt hj, Nat.zero_mul, Nat.zero_add, Bool.and_comm]
  have h := spread_stage 1 1 0x5555555555555555 x _ <| spread_stage 2 2 0x3333333333333333 x _ <|
    spread_stage 4 4 0x0F0F0F0F0F0F0F0F x _ <| spread_stage 8 8 0x00FF00FF00FF00FF x _ <|
    spread_stage 16 16 0x0000FFFF0000FFFF x _ h32
  rw [spread, h j hj]
  by_cases h2 : j % 2 = 0
  · simp [h2]
  · simp [show ¬ j % 2 < 1 by omega, h2]

/-- In characteristic two the square of a word's polynomial spreads its bits. -/
private theorem P_spread (a : UInt64) :
    P (spread a) + X ^ 64 * P (spread (a >>> 32)) = P a ^ 2 := by
  rw [← ZMod.expand_card]
  ext n
  simp only [coeff_add, coeff_X_pow_mul', coeff_expand (by norm_num : 0 < 2), P, coeff_toPoly]
  have hs : ((a >>> 32).toBitVec) = a.toBitVec >>> 32 := by simp
  by_cases h64 : n < 64
  · simp only [spread_getLsbD a n h64, show ¬ 64 ≤ n by omega, ite_false, add_zero]
    by_cases h2 : n % 2 = 0
    · simp [h2, Nat.dvd_iff_mod_eq_zero]
    · simp [h2, Nat.dvd_iff_mod_eq_zero]
  · by_cases h128 : n < 128
    · simp only [spread_getLsbD _ (n - 64) (by omega), show 64 ≤ n by omega, ite_true, hs,
        BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ n (by omega : 64 ≤ n),
        Bool.false_eq_true, ite_false, zero_add]
      have e : 32 + (n - 64) / 2 = n / 2 := by omega
      by_cases h2 : n % 2 = 0
      · simp [h2, Nat.dvd_iff_mod_eq_zero, e, show (n - 64) % 2 = 0 by omega]
      · simp [h2, Nat.dvd_iff_mod_eq_zero, show (n - 64) % 2 ≠ 0 by omega]
    · simp only [BitVec.getLsbD_of_ge _ n (by omega : 64 ≤ n),
        BitVec.getLsbD_of_ge _ (n - 64) (by omega : 64 ≤ n - 64), show 64 ≤ n by omega,
        Bool.false_eq_true, ite_false, ite_true, add_zero]
      rw [BitVec.getLsbD_of_ge _ (n / 2) (by omega)]
      simp

/-- **Squaring is `BF64`'s.** -/
@[simp] theorem toBF64_sq (a : FK) : toBF64 (sq a) = toBF64 a * toBF64 a := by
  apply BF64.toQuot_injective
  rw [BF64.toQuot_mul, toQuot_toBF64, toQuot_toBF64]
  change Q (reduce _ _) = _
  rw [mk_reduce, P_spread, map_pow, _root_.sq]

/-! ## Addition, constants, powers and the inverse -/

@[simp] theorem toBF64_zero : toBF64 0 = 0 := rfl

@[simp] theorem toBF64_one : toBF64 1 = 1 := rfl

/-- **Addition is `BF64`'s.** -/
@[simp] theorem toBF64_add (a b : FK) : toBF64 (a + b) = toBF64 a + toBF64 b := by
  apply BF64.ext
  simp [toBF64, HAdd.hAdd, Add.add, add]

@[simp] theorem toBF64_neg (a : FK) : toBF64 (-a) = -toBF64 a := rfl

@[simp] theorem toBF64_sub (a b : FK) : toBF64 (a - b) = toBF64 a - toBF64 b := by
  apply BF64.ext
  simp [toBF64, HSub.hSub, Sub.sub, add, BF64.ofBitVec]

theorem toBF64_eq_zero {a : FK} : toBF64 a = 0 ↔ a.val = 0 := by
  rw [← toBF64_zero, toBF64_inj]
  exact ⟨fun h => h ▸ rfl, fun h => by cases a; cases h; rfl⟩

@[simp] theorem toBF64_frob (k : ℕ) (a : FK) :
    toBF64 (frob k a) = BF64.powTwoPow (toBF64 a) k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp only [frob, BF64.powTwoPow, ih, toBF64_sq]

/-- **The inverse is `BF64`'s Itoh-Tsujii inverse.** -/
@[simp] theorem toBF64_inv (a : FK) : toBF64 a⁻¹ = (toBF64 a)⁻¹ := by
  change toBF64 (inv a) = BF64.invItohTsujii (toBF64 a)
  by_cases h : a.val = 0
  · have h' := toBF64_eq_zero.mpr h
    simp only [inv, h, ↓reduceIte, BF64.invItohTsujii, h']
    rfl
  · have h' : ¬ toBF64 a = 0 := fun h' => h (toBF64_eq_zero.mp h')
    simp only [inv, h, ↓reduceIte, BF64.invItohTsujii, h', toBF64_mul, toBF64_frob,
      toBF64_sq]

/-! ## The field structure, transported from `BF64` -/

instance : SMul ℕ FK := ⟨nsmulRec⟩
instance : SMul ℤ FK := ⟨zsmulRec nsmulRec⟩

/-- Cast a natural number by its parity, as `BF64.natCast`. -/
@[inline] def natCast (n : ℕ) : FK := if n % 2 = 0 then 0 else 1

instance : NatCast FK := ⟨natCast⟩
instance : IntCast FK := ⟨Int.castDef⟩

@[simp] theorem toBF64_natCast (n : ℕ) : toBF64 (n : FK) = (n : BF64) := by
  change toBF64 (natCast n) = BF64.natCast n
  unfold natCast BF64.natCast
  split_ifs <;> rfl

@[simp] theorem toBF64_intCast (n : ℤ) : toBF64 (n : FK) = (n : BF64) := by
  rcases n with n | n
  · exact toBF64_natCast n
  · change toBF64 (-((n + 1 : ℕ) : FK)) = -((n + 1 : ℕ) : BF64)
    rw [toBF64_neg, toBF64_natCast]

theorem toBF64_nsmul (n : ℕ) (a : FK) : toBF64 (n • a) = n • toBF64 a := by
  change toBF64 (nsmulRec n a) = nsmulRec n (toBF64 a)
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsmulRec, toBF64_add, ih]

theorem toBF64_zsmul (n : ℤ) (a : FK) : toBF64 (n • a) = n • toBF64 a := by
  rcases n with n | n
  · exact toBF64_nsmul n a
  · change toBF64 (-(nsmulRec (n + 1) a)) = -(nsmulRec (n + 1) (toBF64 a))
    rw [toBF64_neg]
    exact congrArg _ (toBF64_nsmul (n + 1) a)

theorem toBF64_powGo (k : ℕ) (b : FK) (e : ℕ) (acc : FK) (he : e ≤ k) :
    toBF64 (powGo k b e acc) = toBF64 acc * toBF64 b ^ e := by
  induction k generalizing b e acc with
  | zero => obtain rfl : e = 0 := by omega
            simp [powGo]
  | succ k ih =>
    rw [powGo]
    split_ifs with h0 ho
    · simp [h0]
    · rw [ih _ _ _ (by omega)]; simp only [toBF64_mul, toBF64_sq]
      conv_rhs => rw [show e = 2 * (e / 2) + 1 by omega, pow_succ, pow_mul, _root_.sq]
      ring
    · rw [ih _ _ _ (by omega), toBF64_sq]
      conv_rhs => rw [show e = 2 * (e / 2) by omega, pow_mul, _root_.sq]

theorem toBF64_npow (a : FK) (n : ℕ) : toBF64 (a ^ n) = toBF64 a ^ n := by
  change toBF64 (powGo n a n 1) = _
  rw [toBF64_powGo n a n 1 le_rfl, toBF64_one, one_mul]

/-- The ring structure, pulled back along the injective `toBF64`. -/
instance instCommRing : CommRing FK :=
  toBF64_injective.commRing _ toBF64_zero toBF64_one toBF64_add toBF64_mul toBF64_neg
    toBF64_sub toBF64_nsmul toBF64_zsmul toBF64_npow toBF64_natCast toBF64_intCast

instance : Div FK := ⟨fun a b => a * b⁻¹⟩

/-- **`FK` is a field**, with the word operations. -/
instance instField : Field FK where
  inv := inv
  div a b := a * b⁻¹
  div_eq_mul_inv _ _ := rfl
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel a h := toBF64_injective (by
    show toBF64 (a * a⁻¹) = toBF64 1
    rw [toBF64_mul, toBF64_inv, toBF64_one]
    exact mul_inv_cancel₀ (fun h' => h (by rw [← toBF64_inj, h', toBF64_zero])))
  inv_zero := rfl
  qsmul := (Rat.castRec · * ·)
  nnqsmul := (NNRat.castRec · * ·)

/-- `toBF64` as a ring isomorphism. -/
def ringEquivBF64 : FK ≃+* BF64 where
  toEquiv := equivBF64
  map_mul' := toBF64_mul
  map_add' := toBF64_add

@[simp] theorem ringEquivBF64_apply (a : FK) : ringEquivBF64 a = toBF64 a := rfl

@[simp] theorem toBF64_div (a b : FK) : toBF64 (a / b) = toBF64 a / toBF64 b := by
  change toBF64 (a * b⁻¹) = _
  rw [toBF64_mul, toBF64_inv, div_eq_mul_inv]

instance : CharP FK 2 where
  cast_eq_zero_iff n := by
    rw [← toBF64_inj, toBF64_natCast, toBF64_zero]
    exact CharP.cast_eq_zero_iff BF64 2 n

/-! ## Cardinality -/

instance : Finite FK := Finite.of_equiv BF64 equivBF64.symm

/-- `FK` has `2 ^ 64` elements. -/
theorem nat_card_FK : Nat.card FK = 2 ^ 64 := by
  rw [Nat.card_congr equivBF64, BF64.nat_card_bf64]

/-- An enumeration of `FK`, for statements that need one. It is noncomputable on purpose: a
computable enumeration of `2 ^ 64` elements would be a closed term built at program start. -/
noncomputable instance : Fintype FK := Fintype.ofFinite FK

/-- Every enumeration of `FK` has `2 ^ 64` elements. -/
theorem card_FK [Fintype FK] : Fintype.card FK = 2 ^ 64 := by
  rw [← Nat.card_eq_fintype_card, nat_card_FK]

/-! ## Word access, Frobenius powers and the conjugates of `x` -/

@[simp] theorem toUInt64_ofUInt64 (w : UInt64) : (ofUInt64 w).toUInt64 = w := rfl

@[simp] theorem ofUInt64_toUInt64 (a : FK) : ofUInt64 a.toUInt64 = a := rfl

theorem sq_eq_mul (a : FK) : sq a = a * a := toBF64_injective (by rw [toBF64_sq, toBF64_mul])

/-- `frob k` is the `2 ^ k`-th power. -/
theorem frob_eq_pow (k : ℕ) (a : FK) : frob k a = a ^ (2 ^ k) := by
  induction k generalizing a with
  | zero => simp [frob]
  | succ k ih => rw [frob, ih, sq_eq_mul, ← _root_.sq, ← pow_mul, pow_succ, mul_comm]

/-- **The 64 conjugates `x^(2^k)`, `k < 64`, of the generator over `GF(2)` are distinct.**
Kernel-decided on the word arithmetic. -/
theorem conj_distinct : ((List.range 64).map (fun k => x ^ (2 ^ k))).Nodup := by
  have h : (fun k => x ^ (2 ^ k)) = (fun k => frob k x) := funext fun k => (frob_eq_pow k x).symm
  rw [h]
  decide +kernel

/-- The power `x ^ i`, `i < 64`, is the word with only bit `i` set (no reduction below degree
64). Proved through the polynomial, not by evaluation, so its kernel check is cheap. -/
theorem x_pow_word (i : Fin 64) : x ^ (i : ℕ) = ⟨(1 : UInt64) <<< i.val.toUInt64⟩ := by
  apply toBF64_injective
  apply BF64.toQuot_injective
  rw [toBF64_npow, BF64.toQuot_npow, toQuot_toBF64, toQuot_toBF64]
  have h1 : ((1 : UInt64) <<< i.val.toUInt64).toBitVec = ((1 <<< i.val : ℕ) : BitVec 64) := by
    have := i.isLt
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mod_eq_of_lt i.isLt, Nat.toUInt64, Nat.shiftLeft_eq]
  have h2 : x.val.toBitVec = ((1 <<< 1 : ℕ) : BitVec 64) := by decide
  show AdjoinRoot.mk BF64.basePoly (toPoly x.val.toBitVec) ^ (i : ℕ) =
    AdjoinRoot.mk BF64.basePoly (toPoly ((1 : UInt64) <<< i.val.toUInt64).toBitVec)
  rw [h1, h2, toPoly_one_shiftLeft (w := 64) _ i.isLt,
    toPoly_one_shiftLeft (w := 64) 1 (by norm_num), pow_one, map_pow]

/-! ## Bytes -/

/-- The encoding is the eight little-endian bytes of the word. -/
theorem toBytes_toList (a : FK) : (toBytes a).toList = CompPoly.Bytes.toListLE 8 a.val.toNat := by
  simp [toBytes, CompPoly.Bytes.toListLE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]

/-- **The encoding is CompPoly's `ByteCodec BF64` encoding.** -/
theorem toBytes_eq (a : FK) :
    (toBytes a).toList = (CompPoly.ByteCodec.toBytes (toBF64 a)).toList := by
  rw [toBytes_toList]
  change _ = CompPoly.Bytes.toListLE (CompPoly.ByteCodec.width BF64) a.val.toBitVec.toNat
  rw [BF64.byteCodec_width]
  rfl

/-- The decoding reads the little-endian natural of the bytes. -/
theorem ofBytes_toNat (v : Vector UInt8 8) : (ofBytes v).val.toNat = CompPoly.Bytes.ofVecLE v := by
  obtain ⟨⟨l⟩, hl⟩ := v
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [ofBytes, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, UInt64.toNat_add, UInt8.toNat_toUInt64, UInt64.toNat_shiftLeft,
      UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow, Nat.add_mod_mod,
      Nat.mod_add_mod, CompPoly.Bytes.ofVecLE, Vector.toList_mk, CompPoly.Bytes.ofListLE_cons,
      CompPoly.Bytes.ofListLE_nil, mul_zero, add_zero]
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
    omega

/-- **The decoding is CompPoly's** (`CanonicalNat.ofBytesModOrder`, the total decoder; on
eight bytes it never reduces). -/
theorem ofBytes_eq (v : Vector UInt8 8) :
    toBF64 (ofBytes v) = CompPoly.CanonicalNat.ofBytesModOrder v := by
  apply BF64.ext
  change (ofBytes v).val.toBitVec = BitVec.ofNat 64 (CompPoly.Bytes.ofVecLE v)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← ofBytes_toNat]
  simp [Nat.mod_eq_of_lt (ofBytes v).val.toNat_lt]

/-- Decoding inverts encoding. -/
@[simp] theorem ofBytes_toBytes (a : FK) : ofBytes (toBytes a) = a := by
  have h : (ofBytes (toBytes a)).val.toNat = a.val.toNat := by
    rw [ofBytes_toNat, CompPoly.Bytes.ofVecLE, toBytes_toList,
      CompPoly.Bytes.ofListLE_toListLE_of_lt (by simpa using a.val.toNat_lt)]
  cases a
  exact congrArg FK.mk (UInt64.toNat_inj.mp h)

/-- Encoding inverts decoding: every eight-byte string is the encoding of one element. -/
@[simp] theorem toBytes_ofBytes (v : Vector UInt8 8) : toBytes (ofBytes v) = v := by
  apply Vector.toList_inj.mp
  rw [toBytes_toList, ofBytes_toNat, CompPoly.Bytes.ofVecLE]
  simpa using CompPoly.Bytes.toListLE_ofListLE v.toList

end Lvm.FK
