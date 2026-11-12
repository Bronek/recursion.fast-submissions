import LvmQEqKeccakAlg2

/-!
# QA1: Keccak weight algebra, part 3 (the first claim, `keccakOpen`'s fold)

See `LvmQEqKeccakAlg` for the overview.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Finset

/-! ## The first claim: weights `lanes ⊗ x^z` -/

/-- `F`'s first-claim weights (`keccakFirstClaim`): lane `ℓ`'s weight times the word `x^z`. -/
def firstW (lanes : List FE) : List FE :=
  (List.range keccakBits).map fun j => lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))

theorem toUInt64_two_pow : ∀ z < 64, (2 ^ z : ℕ).toUInt64 = (1 : UInt64) <<< z.toUInt64 := by
  decide

/-- `x^z` as `F` writes it (`eOfNat (2^z)`), `z < 64`. -/
theorem eOfNat_two_pow {z : ℕ} (hz : z < 64) : eOfNat (2 ^ z) = FE.ofK (FK.x ^ z) := by
  unfold eOfNat
  rw [show z = ((⟨z, hz⟩ : Fin 64) : ℕ) from rfl, FK.x_pow_word ⟨z, hz⟩, toUInt64_two_pow z hz]

theorem ofK_pow (a : FK) (n : ℕ) : FE.ofK (a ^ n) = FE.ofK a ^ n := map_pow FE.ofKRingHom a n

theorem firstW_getD (lanes : List FE) {l z : ℕ} (hl : l < 25) (hz : z < 64) :
    (firstW lanes).getD (64 * l + z) 0 = lanes.getD l 0 * gen ^ z := by
  have h : 64 * l + z < 1600 := by omega
  simp only [firstW, keccakBits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h, Option.map_some, Option.getD_some]
  rw [show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega, eOfNat_two_pow hz,
    ofK_pow]
  rfl

/-- `Σ_{z<2^n} eq(β, z)·g^z = Π_t ((1 + β_t) + β_t·g^(2^t))` (product formula). -/
theorem sum_eqProd_pow (β : ℕ → FE) (g : FE) : ∀ n : ℕ,
    ∑ z ∈ range (2 ^ n), (∏ t ∈ range n, (if z.testBit t then β t else 1 + β t)) * g ^ z =
      ∏ t ∈ range n, ((1 + β t) + β t * g ^ (2 ^ t))
  | 0 => by simp
  | n + 1 => by
    have h1 : ∑ z ∈ range (2 ^ n), (∏ t ∈ range (n + 1), (if z.testBit t then β t else 1 + β t)) * g ^ z =
        ∑ z ∈ range (2 ^ n), (∏ t ∈ range n, (if z.testBit t then β t else 1 + β t)) * g ^ z * (1 + β n) := by
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz' := Finset.mem_range.mp hz
      rw [Finset.prod_range_succ, Nat.testBit_lt_two_pow hz']
      simp only [Bool.false_eq_true, ite_false]
      ring
    have h2 : ∑ z ∈ range (2 ^ n),
        (∏ t ∈ range (n + 1), (if (2 ^ n + z).testBit t then β t else 1 + β t)) * g ^ (2 ^ n + z) =
        ∑ z ∈ range (2 ^ n), (∏ t ∈ range n, (if z.testBit t then β t else 1 + β t)) * g ^ z *
          (β n * g ^ (2 ^ n)) := by
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz' := Finset.mem_range.mp hz
      rw [Finset.prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hz', pow_add]
      simp only [Bool.not_false, ite_true]
      rw [Finset.prod_congr rfl (fun t ht => by rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.mp ht)])]
      ring
    rw [pow_succ, show 2 ^ n * 2 = 2 ^ n + 2 ^ n by ring, Finset.sum_range_add, h1, h2,
      Finset.prod_range_succ, ← sum_eqProd_pow β g n, ← Finset.sum_mul, ← Finset.sum_mul, ← mul_add]

theorem indexMleFrom_eq : ∀ (rs : List FE) (gp acc : FE),
    indexMleFrom gp rs acc = acc * ∏ i ∈ range rs.length, (1 + rs.getD i 0 * (1 + gp ^ (2 ^ i)))
  | [], gp, acc => by simp [indexMleFrom]
  | r :: rs, gp, acc => by
    rw [indexMleFrom, indexMleFrom_eq rs, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, pow_one]
    rw [Finset.prod_congr rfl (fun i _ => by rw [← pow_mul, ← pow_succ']), mul_assoc,
      mul_comm (∏ i ∈ range rs.length, _)]

/-- `Σ_z eq(b, z)·x^z = indexMle b` for a six-point. -/
theorem sum_eq_gen_pow {b : List FE} (hb : b.length = 6) :
    ∑ z ∈ range 64, eqAt b z * gen ^ z = indexMle b := by
  rw [Finset.sum_congr rfl (fun z hz => by
    rw [eqAt_prod b (by rw [hb]; exact Finset.mem_range.mp hz)])]
  unfold eqProd indexMle
  rw [hb, show (64 : ℕ) = 2 ^ 6 from rfl, sum_eqProd_pow (fun t => b.getD t 0) gen 6, indexMleFrom_eq, hb,
    one_mul]
  refine Finset.prod_congr rfl fun t _ => by ring

/-- **The first claim's final-check weight**: `(Σ_ℓ f(ℓ)·lanes(ℓ))·indexMle b`. -/
theorem weighted_first (f lanes b : List FE) (hb : b.length = 6) :
    weightedF f (eqKernel b) (firstW lanes) =
      sumE ((List.range 25).map fun l => f.getD l 0 * lanes.getD l 0) * indexMle b := by
  unfold weightedF
  rw [sumE_range, sumE_range, Finset.sum_mul, ← sum_eq_gen_pow hb]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [sumE_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [firstW_getD lanes (Finset.mem_range.mp hl) (Finset.mem_range.mp hz)]
  unfold eqAt
  ring

/-- **The first claim's iota term**, per bit: `Σ_i rcBit_i · lanes(0)·x^(2^i−1)`. -/
theorem iota_first {rc : UInt64} (hrc : rc ∈ keccakRC) (lanes : List FE) :
    iotaF rc (firstW lanes) =
      sumE ((List.range 7).map fun i => rcBit rc i * (lanes.getD 0 0 * FE.ofK (FK.x ^ iotaPos i))) := by
  rw [iotaF_reduce hrc]
  refine congrArg sumE (List.map_congr_left (fun i hi => ?_))
  have h := firstW_getD lanes (l := 0) (by decide) (iotaPos_lt (List.mem_range.mp hi))
  rw [Nat.mul_zero, Nat.zero_add] at h
  rw [h, show gen = FE.ofK FK.x from rfl, ← ofK_pow]

end Lvm.Q1
