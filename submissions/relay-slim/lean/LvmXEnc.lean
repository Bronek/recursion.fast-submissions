-- WP-13b. adapted from rf-k/submissions/flock-recursive/lean@8bff272b, generic over the field:
-- FRRS.lean (sections Generic (`rsCode` part), Bits, Tensor, NovelBasis, Linear, Enc), FRSoundnessCoreTruths.lean
-- (section `Twin`, formerly `FRRSEval`), FRXBaryDefs.lean (sections `Bfly`, `Pure`) and FRXFwd.lean (section
-- `FRXEncB`, generalised from FR's domain `D` to any additive `pt`: `pt_block`, `normW_block`, `fwdRun_block`,
-- `fwdRun_enc`). Namespace `FR` → `Lvm.Nb`. Proofs verbatim except where the generalisation needs it.
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.GetD

/-!
# The novel basis, its encoder, the additive NTT and interpolation (generic)

Over a field `L` of characteristic 2 with a domain `pt : ℕ → L` additive in the bits
(`pt (a xor b) = pt a + pt b`) and injective on `[0, 2^N)`, and an extension `M ⊇ L`:

* `normW pt v = Ŵ_v` (LCH14's normalised subspace polynomial `W_v / W_v(pt 2^v)`,
  `W_v = Π_{a < 2^v} (X − pt a)`), `novelX pt x = X_x = Π_{v ∈ bits x} Ŵ_v`;
* `enc`, `encN`: `Enc_k(c)[j] = Σ_{x<k} c_x X_x(pt j)`, injective for `k ≤ n ≤ 2^N`
  (`enc_injective`); its range is the Reed–Solomon code on `pt` (`encCode_eq_rsCode`);
* `wRow`, `wAt`: the computable table `Ŵ_v(pt 2^i)` (LCH recursion) and `Ŵ_v(pt j)` by additivity
  (`wAt_eq`);
* `coeffsAt` (the inverse additive NTT, top-down) and `bflyRun` (the same, bottom-up in place):
  values on `pt [0, 2^ℓ)` to novel-basis coefficients (`coeffs_spec`, `coeffs_unique`,
  `bflyRun_coeffs`);
* `fwdRun` (the forward additive NTT, in place): `Enc` of a zero-padded message at every position
  (`fwdRun_enc`);
* `interpF` (Lagrange interpolation at `pt`), `interpF_eq`, `decode_row` (interpolate on `2^ℓ`
  agreeing positions, then take coefficients: the message), and the barycentric forms
  `interpF_self`, `interpF_bary`.

lvm's instance (`L = K = BF64`, `pt j = K.ofBits j`, `N = 15`) is in `LvmXDec`.
-/

namespace Lvm.Nb

open Polynomial Finset

section Generic

variable {K : Type*} [Field K] {n : ℕ}

/-- The word of the evaluations of `p` at the points `x`. -/
def evalWord (x : Fin n → K) (p : K[X]) : Fin n → K := fun j => p.eval (x j)

/-- `evalWord x` as a `K`-linear map. -/
noncomputable def evalWordL (x : Fin n → K) : K[X] →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun j => Polynomial.leval (x j)

theorem evalWordL_apply (x : Fin n → K) (p : K[X]) : evalWordL x p = evalWord x p := rfl

/-- **The Reed–Solomon code** `RS[K, x, k]`: evaluations at `x` of the polynomials of degree
`< k`. -/
noncomputable def rsCode (x : Fin n → K) (k : ℕ) : Submodule K (Fin n → K) :=
  (degreeLT K k).map (evalWordL x)

theorem mem_rsCode {x : Fin n → K} {k : ℕ} {w : Fin n → K} :
    w ∈ rsCode x k ↔ ∃ p : K[X], p.degree < k ∧ evalWord x p = w := by
  simp [rsCode, mem_degreeLT, evalWordL_apply]

theorem evalWord_mem_rsCode {x : Fin n → K} {k : ℕ} {p : K[X]} (hp : p.degree < k) :
    evalWord x p ∈ rsCode x k := mem_rsCode.2 ⟨p, hp, rfl⟩

variable [DecidableEq K]

/-- Two polynomials of degree `< k` agreeing at `k` distinct points `x j`, `j ∈ S`, are equal. -/
theorem poly_eq_of_agree {x : Fin n → K} (hx : Function.Injective x) {k : ℕ} {p q : K[X]}
    (hp : p.degree < k) (hq : q.degree < k) (S : Finset (Fin n)) (hS : k ≤ S.card)
    (h : ∀ j ∈ S, p.eval (x j) = q.eval (x j)) : p = q := by
  have hS' : (k : WithBot ℕ) ≤ (S.image x).card := by
    rw [card_image_of_injective _ hx]; exact_mod_cast hS
  exact eq_of_degrees_lt_of_eval_finset_eq _ (hp.trans_le hS') (hq.trans_le hS')
    (forall_mem_image.2 h)

end Generic

/-! ## Bit products, `eq` on the bits, the tensor identity -/

section Bits

variable {R : Type*} [CommMonoid R]

/-- `∏_{i<ℓ} (f_i if bit i of j else g_i)`. -/
def bitSel (f g : ℕ → R) (ℓ j : ℕ) : R := ∏ i ∈ range ℓ, if j.testBit i then f i else g i

/-- `∏_{i<ℓ} f_i^{bit_i j}` (spartan-srom's `bitProd`). -/
def bitProd (f : ℕ → R) (ℓ j : ℕ) : R := bitSel f 1 ℓ j

theorem bitSel_succ_lo (f g : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitSel f g (ℓ + 1) j = bitSel f g ℓ j * g ℓ := by
  simp [bitSel, prod_range_succ, Nat.testBit_lt_two_pow hj]

theorem bitSel_succ_hi (f g : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitSel f g (ℓ + 1) (2 ^ ℓ + j) = bitSel f g ℓ j * f ℓ := by
  simp only [bitSel, prod_range_succ, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj,
    Bool.not_false, ite_true]
  congr 1
  exact prod_congr rfl fun i hi => by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hi)]

theorem bitProd_succ_lo (f : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitProd f (ℓ + 1) j = bitProd f ℓ j := by
  simp [bitProd, bitSel_succ_lo _ _ hj]

theorem bitProd_succ_hi (f : ℕ → R) {ℓ j : ℕ} (hj : j < 2 ^ ℓ) :
    bitProd f (ℓ + 1) (2 ^ ℓ + j) = bitProd f ℓ j * f ℓ := bitSel_succ_hi _ _ hj

/-- Induction on `ℓ` for statements about `j < 2^ℓ`, splitting off the top bit (spartan-srom). -/
theorem bit_induction {P : ℕ → ℕ → Prop} (h0 : P 0 0)
    (hlo : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j → P (ℓ + 1) j)
    (hhi : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j → P (ℓ + 1) (2 ^ ℓ + j)) : ∀ ℓ j, j < 2 ^ ℓ → P ℓ j := by
  intro ℓ
  induction ℓ with
  | zero => intro j hj; rwa [Nat.lt_one_iff.1 hj]
  | succ ℓ ih =>
    intro j hj
    by_cases hlt : j < 2 ^ ℓ
    · exact hlo ℓ j hlt (ih j hlt)
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlt)
      have : j' < 2 ^ ℓ := by rw [pow_succ] at hj; omega
      exact hhi ℓ j' this (ih j' this)

/-- `bitProd f ℓ j` does not depend on `ℓ` once `j < 2^ℓ`. -/
theorem bitProd_congr (f : ℕ → R) {ℓ ℓ' j : ℕ} (hj : j < 2 ^ ℓ) (hj' : j < 2 ^ ℓ') :
    bitProd f ℓ j = bitProd f ℓ' j := by
  have key : ∀ a b, j < 2 ^ a → a ≤ b → bitProd f b j = bitProd f a j := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ b hab ih =>
      rw [bitProd_succ_lo _ (ha.trans_le (Nat.pow_le_pow_right (by norm_num) hab)), ih]
  rcases le_total ℓ ℓ' with h | h
  · exact (key _ _ hj h).symm
  · exact key _ _ hj' h

end Bits

section Tensor

variable {R : Type*} [CommRing R]

/-- `eq(r, x)` on the bits of `x`, bit `v` of `x` against `r_v` (little-endian):
`∏_{v<ℓ} (r_v if bit v of x else 1 − r_v)`. -/
def eqBits (r : ℕ → R) (ℓ x : ℕ) : R := bitSel r (fun v => 1 - r v) ℓ x

/-- **The tensor identity** (BLUEPRINT §2.1, BP-C-M4), over any commutative ring:
`Σ_{x<2^ℓ} eq(r, x) ∏_{v ∈ bits x} w_v = ∏_{v<ℓ} (1 − r_v + r_v w_v)`. -/
theorem tensor_identity (r w : ℕ → R) (ℓ : ℕ) :
    ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * bitProd w ℓ x = ∏ v ∈ range ℓ, (1 - r v + r v * w v) := by
  induction ℓ with
  | zero => simp [eqBits, bitSel, bitProd]
  | succ ℓ ih =>
    rw [pow_succ, mul_two, sum_range_add, prod_range_succ, ← ih, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun x hx => ?_
    have hx' := mem_range.1 hx
    simp only [eqBits, bitSel_succ_lo _ _ hx', bitSel_succ_hi _ _ hx', bitProd_succ_lo _ hx',
      bitProd_succ_hi _ hx']
    ring

end Tensor

/-! ## The novel basis (LCH14; BLUEPRINT §2.1, Appendix A.1) -/

section NovelBasis

variable {L : Type*} [Field L]

/-- The subspace vanishing polynomial `W_v(X) = ∏_{a < 2^v} (X − pt a)`. -/
noncomputable def subW (pt : ℕ → L) (v : ℕ) : L[X] := ∏ a ∈ range (2 ^ v), (X - C (pt a))

/-- The normalised `Ŵ_v = W_v / W_v(pt (2^v))`. -/
noncomputable def normW (pt : ℕ → L) (v : ℕ) : L[X] :=
  C ((subW pt v).eval (pt (2 ^ v)))⁻¹ * subW pt v

/-- The novel basis polynomial `X_x = ∏_{v ∈ bits x} Ŵ_v`. -/
noncomputable def novelX (pt : ℕ → L) (x : ℕ) : L[X] := bitProd (normW pt) x x

theorem eval_subW (pt : ℕ → L) (v : ℕ) (y : L) :
    (subW pt v).eval y = ∏ a ∈ range (2 ^ v), (y - pt a) := by
  simp [subW, eval_prod]

theorem subW_monic (pt : ℕ → L) (v : ℕ) : (subW pt v).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (pt a)

theorem natDegree_subW (pt : ℕ → L) (v : ℕ) : (subW pt v).natDegree = 2 ^ v := by
  rw [subW, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C (pt a)]
  simp

variable {pt : ℕ → L} {N : ℕ}

/-- `W_v(pt (2^v)) ≠ 0` for `v < N` when `pt` is injective on `[0, 2^N)`. -/
theorem subW_eval_ne (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {v : ℕ} (hv : v < N) :
    (subW pt v).eval (pt (2 ^ v)) ≠ 0 := by
  have hvN : 2 ^ v < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) hv
  rw [eval_subW, prod_ne_zero_iff]
  intro a ha h
  have := hpt (Set.mem_Iio.2 hvN) (Set.mem_Iio.2 ((mem_range.1 ha).trans hvN)) (sub_eq_zero.1 h)
  exact absurd (mem_range.1 ha) (by omega)

theorem normW_eval_self (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {v : ℕ} (hv : v < N) :
    (normW pt v).eval (pt (2 ^ v)) = 1 := by
  rw [normW, eval_mul, eval_C, inv_mul_cancel₀ (subW_eval_ne hpt hv)]

/-- `Ŵ_v` vanishes on `pt a`, `a < 2^v`. -/
theorem normW_eval_lt (pt : ℕ → L) {v a : ℕ} (ha : a < 2 ^ v) : (normW pt v).eval (pt a) = 0 := by
  rw [normW, eval_mul, eval_C, eval_subW pt v (pt a), prod_eq_zero (mem_range.2 ha) (sub_self _),
    mul_zero]

theorem normW_natDegree (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {v : ℕ} (hv : v < N) :
    normW pt v ≠ 0 ∧ (normW pt v).natDegree = 2 ^ v := by
  have hc : ((subW pt v).eval (pt (2 ^ v)))⁻¹ ≠ 0 := inv_ne_zero (subW_eval_ne hpt hv)
  refine ⟨mul_ne_zero (C_ne_zero.2 hc) (subW_monic pt v).ne_zero, ?_⟩
  rw [normW, natDegree_C_mul hc, natDegree_subW]

theorem novelX_eq_bitProd (pt : ℕ → L) {ℓ x : ℕ} (hx : x < 2 ^ ℓ) :
    novelX pt x = bitProd (normW pt) ℓ x :=
  bitProd_congr _ Nat.lt_two_pow_self hx

/-- **`novelX_natDegree`**: `X_x ≠ 0` has degree exactly `x` for `x < 2^N`. -/
theorem novelX_natDegree (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {x : ℕ} (hx : x < 2 ^ N) :
    novelX pt x ≠ 0 ∧ (novelX pt x).natDegree = x := by
  rw [novelX_eq_bitProd pt hx]
  have key : ∀ ℓ j, j < 2 ^ ℓ → ℓ ≤ N →
      bitProd (normW pt) ℓ j ≠ 0 ∧ (bitProd (normW pt) ℓ j).natDegree = j := by
    apply bit_induction
    · intro _; simp [bitProd, bitSel]
    · intro ℓ j hj ih hℓ; rw [bitProd_succ_lo _ hj]; exact ih (by omega)
    · intro ℓ j hj ih hℓ
      obtain ⟨h0, hd⟩ := ih (by omega)
      obtain ⟨hW0, hWd⟩ := normW_natDegree hpt (show ℓ < N by omega)
      rw [bitProd_succ_hi _ hj]
      exact ⟨mul_ne_zero h0 hW0, by rw [natDegree_mul h0 hW0, hd, hWd, add_comm]⟩
  exact key N x hx le_rfl

/-- **Block-triangularity** (BLUEPRINT §2.1): `X_x(pt j) = 0` when bit `v` of `x` is set and
`j < 2^v`. -/
theorem novelX_eval_zero (pt : ℕ → L) {x v j : ℕ} (hb : x.testBit v = true) (hj : j < 2 ^ v) :
    (novelX pt x).eval (pt j) = 0 := by
  have hv : v < x := Nat.lt_two_pow_self.trans_le (Nat.ge_two_pow_of_testBit hb)
  rw [novelX, bitProd, bitSel, eval_prod]
  exact prod_eq_zero (mem_range.2 hv) (by simp only [hb, ite_true]; exact normW_eval_lt pt hj)

/-- Block-triangularity at the top bit: `X_x(pt j) = 0` for `j < 2^msb(x)`. -/
theorem novelX_eval_lt_msb (pt : ℕ → L) {x j : ℕ} (hx : x ≠ 0) (hj : j < 2 ^ x.log2) :
    (novelX pt x).eval (pt j) = 0 :=
  novelX_eval_zero pt (Nat.testBit_log2 hx) hj

/-- The tensor identity for the novel basis: `Σ_{x<2^ℓ} eq(r, x) X_x(y) =
∏_{v<ℓ} (1 − r_v + r_v Ŵ_v(y))`. -/
theorem novelX_tensor (pt : ℕ → L) (r : ℕ → L) (ℓ : ℕ) (y : L) :
    ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * (novelX pt x).eval y =
      ∏ v ∈ range ℓ, (1 - r v + r v * (normW pt v).eval y) := by
  rw [← tensor_identity]
  refine sum_congr rfl fun x hx => ?_
  rw [novelX_eq_bitProd pt (mem_range.1 hx), bitProd, bitSel, bitProd, bitSel, eval_prod]
  congr 1
  exact prod_congr rfl fun v _ => by split_ifs <;> simp

end NovelBasis

/-! ## `W_v` is additive on a subspace domain (`W_linear`) -/

section Linear

variable {L : Type*} [Field L] [CharP L 2] {pt : ℕ → L}

theorem two_pow_add_eq_xor {v a : ℕ} (ha : a < 2 ^ v) : 2 ^ v + a = 2 ^ v ^^^ a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  rcases lt_trichotomy i v with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [h.ne']
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha]; simp
  · have h1 : 2 ^ v + a < 2 ^ i :=
      calc 2 ^ v + a < 2 ^ v + 2 ^ v := by omega
        _ = 2 ^ (v + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    rw [Nat.testBit_lt_two_pow h1,
      Nat.testBit_lt_two_pow (ha.trans (Nat.pow_lt_pow_right (by norm_num) h))]
    simp [h.ne]

omit [CharP L 2] in
/-- The recursion `W_{v+1}(y) = W_v(y) (W_v(y) − W_v(pt 2^v))`, given the additivity of `W_v`. -/
theorem eval_subW_succ (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) {v : ℕ}
    (hW : ∀ y z, (subW pt v).eval (y + z) = (subW pt v).eval y + (subW pt v).eval z) (y : L) :
    (subW pt (v + 1)).eval y =
      (subW pt v).eval y * ((subW pt v).eval y - (subW pt v).eval (pt (2 ^ v))) := by
  have hsh : (subW pt v).eval y - (subW pt v).eval (pt (2 ^ v)) =
      (subW pt v).eval (y - pt (2 ^ v)) := by
    rw [sub_eq_iff_eq_add, ← hW, sub_add_cancel]
  rw [hsh, eval_subW pt (v + 1) y, eval_subW pt v y, eval_subW pt v (y - pt (2 ^ v)), pow_succ,
    mul_two, prod_range_add]
  congr 1
  refine prod_congr rfl fun a ha => ?_
  rw [two_pow_add_eq_xor (mem_range.1 ha), hadd]
  ring

/-- **`W_linear`** (Appendix A.1): on a domain with `pt (a xor b) = pt a + pt b`, every `W_v` is
additive (a linearised polynomial). -/
theorem subW_add (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (v : ℕ) (y z : L) :
    (subW pt v).eval (y + z) = (subW pt v).eval y + (subW pt v).eval z := by
  induction v generalizing y z with
  | zero =>
    have h0 : pt 0 = 0 := by simpa using hadd 0 0
    simp [eval_subW, h0]
  | succ v ih =>
    rw [eval_subW_succ hadd ih, eval_subW_succ hadd ih, eval_subW_succ hadd ih, ih]
    linear_combination ((subW pt v).eval y * (subW pt v).eval z) * CharTwo.two_eq_zero (R := L)

theorem normW_add (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (v : ℕ) (y z : L) :
    (normW pt v).eval (y + z) = (normW pt v).eval y + (normW pt v).eval z := by
  simp only [normW, eval_mul, eval_C, subW_add hadd, mul_add]

/-- The LCH recursion on normalised values: with `p = pt 2^{v+1}`,
`Ŵ_{v+1}(y) = Ŵ_v(y)(Ŵ_v(y) − 1) / (Ŵ_v(p)(Ŵ_v(p) − 1))`. -/
theorem normW_succ (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) {N : ℕ}
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {v : ℕ} (hv : v + 1 < N) (y : L) :
    (normW pt (v + 1)).eval y =
      (normW pt v).eval y * ((normW pt v).eval y - 1) /
        ((normW pt v).eval (pt (2 ^ (v + 1))) * ((normW pt v).eval (pt (2 ^ (v + 1))) - 1)) := by
  have hc := subW_eval_ne hpt (show v < N by omega)
  have hc1 := subW_eval_ne hpt hv
  simp only [normW, eval_mul, eval_C] at hc1 ⊢
  rw [eval_subW_succ hadd (subW_add hadd v), eval_subW_succ hadd (subW_add hadd v)] at *
  set a := (subW pt v).eval y
  set b := (subW pt v).eval (pt (2 ^ (v + 1)))
  set c := (subW pt v).eval (pt (2 ^ v))
  have hb : b * (b - c) ≠ 0 := hc1
  have hb' : c⁻¹ * b * (c⁻¹ * b - 1) ≠ 0 := by
    rw [show c⁻¹ * b * (c⁻¹ * b - 1) = c⁻¹ * c⁻¹ * (b * (b - c)) by field_simp]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hc) (inv_ne_zero hc)) hb
  field_simp

end Linear

/-! ## The encoding `Enc_k` (BLUEPRINT §2.1) -/

section Enc

variable {L M : Type*} [Field L] [Field M] [Algebra L M]

/-- **`Enc_k`**: `Enc_k(c)[j] = Σ_{x<k} c_x X_x(pt j)` for `c ∈ M^k`, `j < n`; the message is the
vector of novel-basis coefficients. -/
noncomputable def enc (pt : ℕ → L) (n k : ℕ) (c : Fin k → M) : Fin n → M :=
  fun j => ∑ x : Fin k, c x * algebraMap L M ((novelX pt x).eval (pt j))

/-- `Enc_k` as an `M`-linear map. -/
noncomputable def encL (pt : ℕ → L) (n k : ℕ) : (Fin k → M) →ₗ[M] (Fin n → M) where
  toFun := enc pt n k
  map_add' c c' := by funext j; simp [enc, add_mul, sum_add_distrib]
  map_smul' a c := by funext j; simp [enc, mul_sum, mul_assoc]

/-- The code `C_M = Enc_k(M^k)` (`C_K` over `K`, `C_F` over `F`). -/
noncomputable def encCode (pt : ℕ → L) (n k : ℕ) : Submodule M (Fin n → M) :=
  LinearMap.range (encL (M := M) pt n k)

/-- The polynomial `Σ_x c_x X_x ∈ M[X]` that `Enc_k(c)` evaluates. -/
noncomputable def encPoly (pt : ℕ → L) {k : ℕ} (c : Fin k → M) : M[X] :=
  ∑ x : Fin k, C (c x) * (novelX pt x).map (algebraMap L M)

theorem encPoly_eval (pt : ℕ → L) (n k : ℕ) (c : Fin k → M) (j : Fin n) :
    (encPoly pt c).eval (algebraMap L M (pt j)) = enc pt n k c j := by
  simp only [encPoly, enc, eval_finsetSum, eval_mul, eval_C, eval_map, eval₂_at_apply]

variable {pt : ℕ → L} {N : ℕ}

theorem novelX_map (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {x : ℕ} (hx : x < 2 ^ N) :
    ((novelX pt x).map (algebraMap L M)).natDegree = x ∧
      ((novelX pt x).map (algebraMap L M)).leadingCoeff ≠ 0 := by
  obtain ⟨h0, hd⟩ := novelX_natDegree hpt hx
  refine ⟨by rw [natDegree_map, hd], ?_⟩
  rw [leadingCoeff_map, ne_eq, map_eq_zero, leadingCoeff_eq_zero]
  exact h0

theorem encPoly_mem (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k ≤ 2 ^ N)
    (c : Fin k → M) : encPoly pt c ∈ degreeLT M k := by
  refine sum_mem fun x _ => ?_
  rw [← smul_eq_C_mul]
  refine Submodule.smul_mem _ _ (mem_degreeLT.2 (degree_le_natDegree.trans_lt ?_))
  rw [(novelX_map (M := M) hpt (x.2.trans_le hk)).1]; exact_mod_cast x.2

theorem encPoly_add (pt : ℕ → L) {k : ℕ} (c c' : Fin k → M) :
    encPoly pt (c + c') = encPoly pt c + encPoly pt c' := by
  simp [encPoly, add_mul, sum_add_distrib]

theorem encPoly_single (pt : ℕ → L) {k : ℕ} (t : Fin k) (a : M) :
    encPoly pt (Pi.single t a) = C a * (novelX pt t).map (algebraMap L M) := by
  classical
  rw [encPoly, sum_eq_single t (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- Every polynomial of degree `< k ≤ 2^N` is `Σ_x c_x X_x`. -/
theorem exists_encPoly (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k ≤ 2 ^ N) :
    ∀ d, d < k → ∀ p : M[X], p.natDegree ≤ d → ∃ c : Fin k → M, encPoly pt c = p := by
  intro d
  induction d with
  | zero =>
    intro h0 p hp
    refine ⟨Pi.single ⟨0, h0⟩ (p.coeff 0), ?_⟩
    rw [encPoly_single, eq_C_of_natDegree_le_zero hp]
    simp [novelX, bitProd, bitSel]
  | succ d ih =>
    intro hd p hp
    set t : Fin k := ⟨d + 1, hd⟩
    obtain ⟨hdeg, hlc⟩ := novelX_map (M := M) hpt (show d + 1 < 2 ^ N by omega)
    set Y := (novelX pt (d + 1)).map (algebraMap L M)
    set q := p - C (p.coeff (d + 1) / Y.leadingCoeff) * Y
    have hq : q.natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      simp only [q, coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (d + 1) i with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt h),
          coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt h), mul_zero, sub_zero]
      · obtain rfl : i = d + 1 := by omega
        rw [show Y.coeff (d + 1) = Y.leadingCoeff by rw [leadingCoeff, hdeg],
          div_mul_cancel₀ _ hlc, sub_self]
    obtain ⟨c, hc⟩ := ih (by omega) q hq
    refine ⟨c + Pi.single t (p.coeff (d + 1) / Y.leadingCoeff), ?_⟩
    rw [encPoly_add, hc, encPoly_single]
    simp [q, Y, t]

/-- **`C_M = RS[M, pt, k]`**: the novel-basis code is the Reed–Solomon code on the points `pt j`
(for `k ≤ 2^N`). Distance, interpolation and the proximity lemmas therefore apply to it. -/
theorem encCode_eq_rsCode (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {n k : ℕ} (hk : k ≤ 2 ^ N) :
    encCode (M := M) pt n k = rsCode (fun j : Fin n => algebraMap L M (pt j)) k := by
  ext w
  rw [mem_rsCode]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨encPoly pt c, mem_degreeLT.1 (encPoly_mem hpt hk c),
      funext fun j => encPoly_eval pt n k c j⟩
  · rintro ⟨p, hp, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · obtain rfl : p = 0 := by simpa using hp
      exact ⟨0, funext fun j => by simp [evalWord, encL, enc]⟩
    obtain ⟨c, rfl⟩ := exists_encPoly hpt hk (k - 1) (by omega) p
      (natDegree_le_pred (natDegree_le_of_degree_le hp.le) (coeff_eq_zero_of_degree_lt hp))
    exact ⟨c, funext fun j => (encPoly_eval pt n k c j).symm⟩

/-- `Σ_x c_x X_x ≠ 0` for `c ≠ 0`: its coefficient at the top nonzero index `t` is
`c_t · lc(X_t) ≠ 0`. -/
theorem encPoly_ne_zero (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {k : ℕ} (hk : k ≤ 2 ^ N)
    {c : Fin k → M} (h : c ≠ 0) : encPoly pt c ≠ 0 := by
  classical
  have hne : (univ.filter fun x => c x ≠ 0).Nonempty := by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 h; exact ⟨x, by simpa using hx⟩
  set t := (univ.filter fun x => c x ≠ 0).max' hne
  have ht : c t ≠ 0 := by simpa using (univ.filter fun x => c x ≠ 0).max'_mem hne
  intro h0
  have hc := congrArg (fun p => p.coeff t) h0
  simp only [encPoly, finsetSum_coeff, coeff_C_mul, coeff_zero] at hc
  rw [sum_eq_single t] at hc
  · obtain ⟨hdeg, hlc⟩ := novelX_map (M := M) hpt (t.2.trans_le hk)
    rw [leadingCoeff, hdeg] at hlc
    exact mul_ne_zero ht hlc hc
  · intro x _ hxt
    by_cases hx : c x = 0
    · simp [hx]
    rw [coeff_eq_zero_of_natDegree_lt (by
      rw [(novelX_map (M := M) hpt (x.2.trans_le hk)).1]
      exact (le_max' _ x (by simpa using hx)).lt_of_ne hxt), mul_zero]
  · simp

/-- **`enc_injective`** (`coeffs_of_values` is well defined): with `k ≤ n` points, `Enc_k` is
injective, so a codeword has one message. -/
theorem enc_injective (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {n k : ℕ} (hk : k ≤ 2 ^ N)
    (hn : n ≤ 2 ^ N) (hkn : k ≤ n) : Function.Injective (enc (M := M) pt n k) := by
  classical
  intro c c' h
  by_contra hne
  apply encPoly_ne_zero hpt hk (sub_ne_zero.2 hne)
  have hinj : Function.Injective fun j : Fin n => algebraMap L M (pt j) := fun a b e =>
    Fin.ext (hpt (Set.mem_Iio.2 (a.2.trans_le hn)) (Set.mem_Iio.2 (b.2.trans_le hn))
      ((algebraMap L M).injective e))
  have hc := poly_eq_of_agree hinj (mem_degreeLT.1 (encPoly_mem hpt hk c))
    (mem_degreeLT.1 (encPoly_mem hpt hk c')) univ (by simpa using hkn) fun j _ => by
      rw [encPoly_eval pt n k, encPoly_eval pt n k, h]
  rw [show encPoly pt (c - c') = encPoly pt c - encPoly pt c' by
    simp [encPoly, sub_mul, sum_sub_distrib], hc, sub_self]

end Enc
section Twin

variable {L : Type*} [Field L]

/-- **The basis table row** `v`: `(Ŵ_v(pt 2^i))_{i<N}`, by the LCH recursion on values. -/
def wRow (pt : ℕ → L) (N : ℕ) : ℕ → List L
  | 0 => (List.range N).map fun i => (pt (2 ^ i) - pt 0) / (pt 1 - pt 0)
  | v + 1 =>
    let r := wRow pt N v
    let b := r.getD (v + 1) 0
    r.map fun a => a * (a - 1) / (b * (b - 1))

/-- **`Ŵ_v(pt j)`** from the table: the sum over the set bits `i` of `j` of `Ŵ_v(pt 2^i)`. -/
def wAt (pt : ℕ → L) (N v j : ℕ) : L :=
  ∑ i ∈ range N, if j.testBit i then (wRow pt N v).getD i 0 else 0

theorem wRow_length (pt : ℕ → L) (N : ℕ) : ∀ v, (wRow pt N v).length = N
  | 0 => by simp [wRow]
  | v + 1 => by simp [wRow, wRow_length pt N v]

theorem normW_zero_eval (pt : ℕ → L) (y : L) :
    (normW pt 0).eval y = (y - pt 0) / (pt 1 - pt 0) := by
  simp [normW, eval_subW, div_eq_mul_inv, mul_comm]

variable [CharP L 2] {pt : ℕ → L} {N : ℕ}

/-- The table holds the values of `Ŵ_v` at the basis points. -/
theorem wRow_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ v, v < N → ∀ i, i < N → (wRow pt N v).getD i 0 = (normW pt v).eval (pt (2 ^ i)) := by
  intro v
  induction v with
  | zero =>
    intro _ i hi
    simp [wRow, List.getD_eq_getElem?_getD, hi, normW_zero_eval]
  | succ v ih =>
    intro hv i hi
    have hlen := wRow_length pt N v
    rw [wRow, List.getD_eq_getElem _ _ (by simpa [hlen]), List.getElem_map,
      ← List.getD_eq_getElem _ 0, ih (by omega) i hi, ih (by omega) (v + 1) hv,
      normW_succ hadd hpt hv]

omit [CharP L 2] in
/-- `pt j` is the sum of `pt 2^i` over the set bits `i` of `j < 2^ℓ`. -/
theorem pt_bits (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) :
    ∀ ℓ j, j < 2 ^ ℓ → pt j = ∑ i ∈ range ℓ, if j.testBit i then pt (2 ^ i) else 0 := by
  have h0 : pt 0 = 0 := by simpa using hadd 0 0
  apply bit_induction
  · simp [h0]
  · intro ℓ j hj ih
    rw [sum_range_succ, Nat.testBit_lt_two_pow hj, ih]; simp
  · intro ℓ j hj ih
    rw [two_pow_add_eq_xor hj, hadd, ← two_pow_add_eq_xor hj, sum_range_succ,
      Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj, ih]
    simp only [Bool.not_false, ite_true]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun i hi => by rw [Nat.testBit_two_pow_add_gt (mem_range.1 hi)]

theorem normW_eval_sum (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (v : ℕ) {ι : Type*}
    (s : Finset ι) (g : ι → L) :
    (normW pt v).eval (∑ i ∈ s, g i) = ∑ i ∈ s, (normW pt v).eval (g i) := by
  classical
  have h0 : (normW pt v).eval 0 = 0 := by simpa using normW_add hadd v 0 0
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, normW_add hadd, ih]

/-- **`wAt_eq`**: the table value is `Ŵ_v(pt j)` (`v < N`, `j < 2^N`). -/
theorem wAt_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b) (hpt : Set.InjOn pt (Set.Iio (2 ^ N)))
    {v j : ℕ} (hv : v < N) (hj : j < 2 ^ N) : wAt pt N v j = (normW pt v).eval (pt j) := by
  rw [pt_bits hadd N j hj, normW_eval_sum hadd, wAt]
  refine sum_congr rfl fun i hi => ?_
  split_ifs
  · exact wRow_spec hadd hpt v hv i (mem_range.1 hi)
  · simpa using (normW_eval_sum hadd v (∅ : Finset ℕ) fun _ => (0 : L)).symm

variable {M : Type*} [Field M] [Algebra L M]

/-- **The computable `Enc_{2^ℓ}`**: `Σ_x c_x ∏_{v ∈ bits x} Ŵ_v(pt j)` from the table. -/
def encTwin (pt : ℕ → L) (N ℓ : ℕ) {n : ℕ} (c : Fin (2 ^ ℓ) → M) (j : Fin n) : M :=
  ∑ x : Fin (2 ^ ℓ), c x * bitProd (fun v => algebraMap L M (wAt pt N v j)) ℓ x

/-- **The verifier's tensor weight** `∏_{v<ℓ} (1 − r_v + r_v Ŵ_v(pt j))` (`tensorW`, A.5). -/
def tensorTwin (pt : ℕ → L) (N ℓ : ℕ) (r : ℕ → M) (j : ℕ) : M :=
  ∏ v ∈ range ℓ, (1 - r v + r v * algebraMap L M (wAt pt N v j))

theorem bitProd_map {R S : Type*} [CommMonoid R] [CommMonoid S] (φ : R →* S) (f : ℕ → R)
    (ℓ x : ℕ) : φ (bitProd f ℓ x) = bitProd (fun v => φ (f v)) ℓ x := by
  simp only [bitProd, bitSel, map_prod]
  exact prod_congr rfl fun v _ => by split_ifs <;> simp

/-- `X_x(pt j)` from the table. -/
theorem novelX_eval_twin (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ x j : ℕ} (hℓ : ℓ ≤ N) (hx : x < 2 ^ ℓ)
    (hj : j < 2 ^ N) :
    algebraMap L M ((novelX pt x).eval (pt j)) =
      bitProd (fun v => algebraMap L M (wAt pt N v j)) ℓ x := by
  rw [novelX_eq_bitProd pt hx, bitProd, bitSel, eval_prod, map_prod, bitProd, bitSel]
  refine prod_congr rfl fun v hv => ?_
  split_ifs
  · rw [wAt_eq hadd hpt (by have := mem_range.1 hv; omega) hj]
  · simp

/-- **`encTwin_eq`**: the computable encoding is `Enc_{2^ℓ}` (`ℓ ≤ N`, `n ≤ 2^N`). -/
theorem encTwin_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ n : ℕ} (hℓ : ℓ ≤ N) (hn : n ≤ 2 ^ N)
    (c : Fin (2 ^ ℓ) → M) (j : Fin n) : encTwin pt N ℓ c j = enc pt n (2 ^ ℓ) c j := by
  refine sum_congr rfl fun x _ => ?_
  rw [novelX_eval_twin hadd hpt hℓ x.2 (j.2.trans_le hn)]

/-- **`tensorTwin_eq`** (the tensor identity, computed): `tensorTwin = Σ_x eq(r, x) X_x(pt j)`. -/
theorem tensorTwin_eq (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ j : ℕ} (hℓ : ℓ ≤ N) (hj : j < 2 ^ N) (r : ℕ → M) :
    tensorTwin pt N ℓ r j =
      ∑ x ∈ range (2 ^ ℓ), eqBits r ℓ x * algebraMap L M ((novelX pt x).eval (pt j)) := by
  rw [tensorTwin, ← tensor_identity]
  exact sum_congr rfl fun x hx => by rw [novelX_eval_twin hadd hpt hℓ (mem_range.1 hx) hj]

/-! ## Values to coefficients, interpolation (S-D2; BLUEPRINT §6.2) -/

/-- `Enc` as a word indexed by `ℕ`: `encN pt c j = Σ_x c_x X_x(pt j)` (`enc pt n k c j` for
`j < n`, `enc_eq_encN`). -/
noncomputable def encN (pt : ℕ → L) {k : ℕ} (c : Fin k → M) (j : ℕ) : M :=
  ∑ x : Fin k, c x * algebraMap L M ((novelX pt x).eval (pt j))

omit [CharP L 2] in
theorem enc_eq_encN (pt : ℕ → L) {n k : ℕ} (c : Fin k → M) (j : Fin n) :
    enc pt n k c j = encN pt c j := rfl

omit [CharP L 2] in
theorem novelX_two_pow_add (pt : ℕ → L) {ℓ x : ℕ} (hx : x < 2 ^ ℓ) :
    novelX pt (2 ^ ℓ + x) = novelX pt x * normW pt ℓ := by
  rw [novelX_eq_bitProd pt (show 2 ^ ℓ + x < 2 ^ (ℓ + 1) by rw [pow_succ]; omega),
    bitProd_succ_hi _ hx, ← novelX_eq_bitProd pt hx]

/-- **The inverse additive NTT** on the coset `pt s + pt [0, 2^ℓ)`: from the values `y j` at
`pt (s + j)`, `j < 2^ℓ`, the novel-basis coefficients (`coeffsAt_spec`). One level: with
`α = Ŵ_ℓ(pt s)`, the halves give `u = c_lo + α c_hi` and `w = c_lo + (α + 1) c_hi`. -/
def coeffsAt (pt : ℕ → L) (N : ℕ) : ℕ → ℕ → (ℕ → M) → ℕ → M
  | 0, _, y => y
  | ℓ + 1, s, y => fun x =>
    let u := coeffsAt pt N ℓ s y
    let w := coeffsAt pt N ℓ (s + 2 ^ ℓ) fun j => y (2 ^ ℓ + j)
    let α := algebraMap L M (wAt pt N ℓ s)
    if x < 2 ^ ℓ then u x - α * (w x - u x) else w (x - 2 ^ ℓ) - u (x - 2 ^ ℓ)

omit [CharP L 2] in
theorem sum_novel_succ (pt : ℕ → L) (ℓ : ℕ) (c : ℕ → M) (P : L) :
    ∑ x ∈ range (2 ^ (ℓ + 1)), c x * algebraMap L M ((novelX pt x).eval P) =
      ∑ x ∈ range (2 ^ ℓ), (c x + c (2 ^ ℓ + x) * algebraMap L M ((normW pt ℓ).eval P)) *
        algebraMap L M ((novelX pt x).eval P) := by
  rw [pow_succ, mul_two, sum_range_add, ← sum_add_distrib]
  refine sum_congr rfl fun x hx => ?_
  rw [novelX_two_pow_add pt (mem_range.1 hx), eval_mul, map_mul]
  ring

/-- **`coeffsAt_spec`**: on a coset `pt s + pt [0, 2^ℓ)` (`pt (s + j) = pt s + pt j`), the
coefficients reproduce the values. -/
theorem coeffsAt_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ ℓ s (y : ℕ → M), ℓ ≤ N → s + 2 ^ ℓ ≤ 2 ^ N → (∀ j < 2 ^ ℓ, pt (s + j) = pt s + pt j) →
      ∀ j < 2 ^ ℓ, ∑ x ∈ range (2 ^ ℓ),
        coeffsAt pt N ℓ s y x * algebraMap L M ((novelX pt x).eval (pt (s + j))) = y j := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s y _ _ _ j hj
    obtain rfl : j = 0 := by simpa using hj
    simp [coeffsAt, novelX, bitProd, bitSel]
  | succ ℓ ih =>
    intro s y hN hs H j hj
    have hsN : s < 2 ^ N := by have := Nat.one_le_two_pow (n := ℓ + 1); omega
    have hα : (normW pt ℓ).eval (pt s) = wAt pt N ℓ s := (wAt_eq hadd hpt (by omega) hsN).symm
    have hpow : 2 ^ (ℓ + 1) = 2 ^ ℓ + 2 ^ ℓ := by rw [pow_succ]; ring
    have hW : ∀ i < 2 ^ ℓ, (normW pt ℓ).eval (pt i) = 0 := fun i hi => normW_eval_lt pt hi
    have hup : ∀ j' < 2 ^ ℓ, pt (2 ^ ℓ + j') = pt (2 ^ ℓ) + pt j' := fun j' h' => by
      rw [two_pow_add_eq_xor h', hadd]
    rw [sum_novel_succ]
    simp only [coeffsAt]
    by_cases hlo : j < 2 ^ ℓ
    · rw [H j (by omega), normW_add hadd, hW j hlo, add_zero, hα, ← H j (by omega)]
      rw [← ih s y (by omega) (by omega) (fun i hi => H i (by omega)) j hlo]
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      simp only [hx', ite_true, show ¬ (2 ^ ℓ + x < 2 ^ ℓ) by omega, ite_false,
        Nat.add_sub_cancel_left]
      ring
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlo)
      have hj' : j' < 2 ^ ℓ := by omega
      have hP : pt (s + (2 ^ ℓ + j')) = pt (s + 2 ^ ℓ + j') := by rw [Nat.add_assoc]
      have H' : ∀ i < 2 ^ ℓ, pt (s + 2 ^ ℓ + i) = pt (s + 2 ^ ℓ) + pt i := fun i hi => by
        rw [Nat.add_assoc, H _ (by omega), H _ (by omega), hup i hi, add_assoc]
      have hWv : (normW pt ℓ).eval (pt (s + (2 ^ ℓ + j'))) = wAt pt N ℓ s + 1 := by
        rw [H _ (by omega), normW_add hadd, hup j' hj', normW_add hadd, hW j' hj',
          normW_eval_self hpt (by omega), add_zero, hα]
      rw [hWv, hP]
      rw [← ih (s + 2 ^ ℓ) (fun i => y (2 ^ ℓ + i)) (by omega) (by omega) H' j' hj']
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      simp only [hx', ite_true, show ¬ (2 ^ ℓ + x < 2 ^ ℓ) by omega, ite_false,
        Nat.add_sub_cancel_left, map_add, map_one]
      ring

/-- **`coeffs_of_values`**: the novel-basis message of the codeword whose values on
`pt 0, …, pt (2^ℓ − 1)` are `y` (the inverse additive NTT, `O(ℓ 2^ℓ)` butterflies). -/
def coeffsOfValues (pt : ℕ → L) (N ℓ : ℕ) (y : ℕ → M) : Fin (2 ^ ℓ) → M :=
  fun x => coeffsAt pt N ℓ 0 y x

/-- **`coeffs_spec`**: `Enc(coeffs_of_values y)` takes the values `y` on `pt [0, 2^ℓ)`. -/
theorem coeffs_spec (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) (y : ℕ → M) {j : ℕ}
    (hj : j < 2 ^ ℓ) : encN pt (coeffsOfValues pt N ℓ y) j = y j := by
  have h0 : pt 0 = 0 := by simpa using hadd 0 0
  have := coeffsAt_spec hadd hpt ℓ 0 y hℓ (by simpa using Nat.pow_le_pow_right two_pos hℓ)
    (fun i _ => by simp [h0]) j hj
  rw [zero_add] at this
  rw [encN, ← this]
  exact Fin.sum_univ_eq_sum_range (fun x => coeffsAt pt N ℓ 0 y x *
    algebraMap L M ((novelX pt x).eval (pt j))) _

/-- The message is determined by the values on `pt [0, 2^ℓ)`: `coeffs_of_values` inverts
`Enc`. -/
theorem coeffs_unique (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) (y : ℕ → M)
    (c : Fin (2 ^ ℓ) → M) (hc : ∀ j < 2 ^ ℓ, encN pt c j = y j) :
    coeffsOfValues pt N ℓ y = c := by
  have hk : 2 ^ ℓ ≤ 2 ^ N := Nat.pow_le_pow_right two_pos hℓ
  refine enc_injective (n := 2 ^ ℓ) hpt hk hk le_rfl (funext fun j => ?_)
  rw [enc_eq_encN, enc_eq_encN, coeffs_spec hadd hpt hℓ y j.2, hc j j.2]

/-- **`interpF`**: Lagrange interpolation through the values `y i` at `pt i`, `i ∈ J`, evaluated at
`pt j`: `Σ_{i∈J} y_i ∏_{m ∈ J∖i} (pt j − pt m)/(pt i − pt m)`. -/
def interpF (pt : ℕ → L) (J : Finset ℕ) (y : ℕ → M) (j : ℕ) : M :=
  ∑ i ∈ J, y i * ∏ m ∈ J.erase i,
    (algebraMap L M (pt j) - algebraMap L M (pt m)) /
      (algebraMap L M (pt i) - algebraMap L M (pt m))

omit [CharP L 2] in
theorem interpF_congr (pt : ℕ → L) (J : Finset ℕ) {y y' : ℕ → M} (h : ∀ i ∈ J, y i = y' i)
    (j : ℕ) : interpF pt J y j = interpF pt J y' j :=
  sum_congr rfl fun i hi => by rw [h i hi]

omit [CharP L 2] in
/-- **`interpF_eq`**: on distinct points, `interpF` evaluates every polynomial of degree `< |J|`
from its values on `J`. -/
theorem interpF_eq {pt : ℕ → L} {J : Finset ℕ} (hJ : Set.InjOn pt J) {p : M[X]}
    (hp : p.degree < J.card) (j : ℕ) :
    interpF pt J (fun i => p.eval (algebraMap L M (pt i))) j = p.eval (algebraMap L M (pt j)) := by
  have hv : Set.InjOn (fun i => algebraMap L M (pt i)) J := fun a ha b hb h =>
    hJ ha hb ((algebraMap L M).injective h)
  conv_rhs => rw [Lagrange.eq_interpolate hv hp]
  simp [interpF, Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor,
    eval_finsetSum, eval_prod, div_eq_inv_mul]

/-- **Erasure decoding of a row** (BLUEPRINT §6.2): if the word `u` agrees with `Enc(c)` on a set
`J` of `2^ℓ` distinct points, interpolating on `J` and taking coefficients returns `c`. -/
theorem decode_row (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ : ℕ} (hℓ : ℓ ≤ N) {J : Finset ℕ}
    (hJ : Set.InjOn pt J) (hJc : J.card = 2 ^ ℓ) (c : Fin (2 ^ ℓ) → M) (u : ℕ → M)
    (hu : ∀ i ∈ J, u i = encN pt c i) :
    coeffsOfValues pt N ℓ (interpF pt J u) = c := by
  refine coeffs_unique hadd hpt hℓ _ c fun j _ => ?_
  have hdeg : (encPoly pt c).degree < J.card := by
    rw [hJc]; exact mem_degreeLT.1 (encPoly_mem hpt (Nat.pow_le_pow_right two_pos hℓ) c)
  have he : ∀ i, encN pt c i = (encPoly pt c).eval (algebraMap L M (pt i)) := fun i =>
    (encPoly_eval pt (i + 1) _ c ⟨i, by omega⟩).symm
  rw [interpF_congr pt J hu, funext he, interpF_eq hJ hdeg]

end Twin
section Bfly

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **One butterfly level** `l`: in each block of `2^(l+1)` at `base`, the halves' coefficients
`u` (low) and `w` (high) merge into `u − α (w − u)` (low) and `w − u` (high), with
`α = Ŵ_l(pt (s₀ + base))` (`coeffsAt`'s step). -/
def bflyLevel (pt : ℕ → L) (N s0 l : ℕ) (A : ℕ → M) (i : ℕ) : M :=
  let base := i / 2 ^ (l + 1) * 2 ^ (l + 1)
  let x := i % 2 ^ (l + 1)
  let u := A (base + x % 2 ^ l)
  let w := A (base + 2 ^ l + x % 2 ^ l)
  let α := algebraMap L M (wAt pt N l (s0 + base))
  if x < 2 ^ l then u - α * (w - u) else w - u

/-- **The iteration**: levels `0, …, ℓ − 1`. -/
def bflyRun (pt : ℕ → L) (N s0 : ℕ) : ℕ → (ℕ → M) → ℕ → M
  | 0, A => A
  | l + 1, A => bflyLevel pt N s0 l (bflyRun pt N s0 l A)

/-- **The block invariant**: after `l` levels, block `b` holds `coeffsAt` of its coset. -/
theorem bflyRun_block (pt : ℕ → L) (N s0 : ℕ) (y : ℕ → M) :
    ∀ l b x, x < 2 ^ l → bflyRun pt N s0 l y (b * 2 ^ l + x) =
      coeffsAt pt N l (s0 + b * 2 ^ l) (fun j => y (b * 2 ^ l + j)) x := by
  intro l
  induction l with
  | zero =>
    intro b x hx
    obtain rfl : x = 0 := by simpa using hx
    simp [bflyRun, coeffsAt]
  | succ l ih =>
    intro b x hx
    have hp : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ l := by positivity
    have hdiv : (b * 2 ^ (l + 1) + x) / 2 ^ (l + 1) = b := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hx,
        Nat.zero_add]
    have hmod : (b * 2 ^ (l + 1) + x) % 2 ^ (l + 1) = x := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
    have hu := ih (2 * b) (x % 2 ^ l) (Nat.mod_lt _ hpos)
    have hw := ih (2 * b + 1) (x % 2 ^ l) (Nat.mod_lt _ hpos)
    have e1 : 2 * b * 2 ^ l = b * 2 ^ (l + 1) := by rw [hp]; ring
    have e2 : (2 * b + 1) * 2 ^ l = b * 2 ^ (l + 1) + 2 ^ l := by rw [hp]; ring
    rw [e1] at hu
    rw [e2] at hw
    simp only [bflyRun, bflyLevel, hdiv, hmod, coeffsAt]
    rw [hu, hw]
    have hY : (fun j => y (b * 2 ^ (l + 1) + 2 ^ l + j)) =
        fun j => (fun j => y (b * 2 ^ (l + 1) + j)) (2 ^ l + j) := by
      funext j; rw [Nat.add_assoc]
    rw [hY, ← Nat.add_assoc]
    by_cases hx' : x < 2 ^ l
    · rw [if_pos hx', if_pos hx', Nat.mod_eq_of_lt hx']
    · rw [if_neg hx', if_neg hx', show x % 2 ^ l = x - 2 ^ l by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]

/-- **The iteration is `coeffsAt`** on the array's first `2^ℓ` entries. -/
theorem bflyRun_eq (pt : ℕ → L) (N s0 ℓ : ℕ) (y : ℕ → M) {i : ℕ} (hi : i < 2 ^ ℓ) :
    bflyRun pt N s0 ℓ y i = coeffsAt pt N ℓ s0 y i := by
  simpa using bflyRun_block pt N s0 y ℓ 0 i hi

/-- From offset `0`, the iteration is `coeffsOfValues`. -/
theorem bflyRun_coeffs (pt : ℕ → L) (N ℓ : ℕ) (y : ℕ → M) (i : Fin (2 ^ ℓ)) :
    bflyRun pt N 0 ℓ y i = coeffsOfValues pt N ℓ y i :=
  bflyRun_eq pt N 0 ℓ y i.2

end Bfly

/-! ## The pure form -/

section Pure

variable {L : Type*} [Field L] {M : Type*} [Field M] [Algebra L M]

/-- **On `J`, the interpolation returns the value.** -/
theorem interpF_self {pt : ℕ → L} {J : Finset ℕ} (hJ : Set.InjOn pt J) (y : ℕ → M) {s : ℕ}
    (hs : s ∈ J) : interpF pt J y s = y s := by
  unfold interpF
  rw [Finset.sum_eq_single s]
  · rw [Finset.prod_eq_one, mul_one]
    intro m hm
    obtain ⟨hne, hmJ⟩ := Finset.mem_erase.1 hm
    have : algebraMap L M (pt s) - algebraMap L M (pt m) ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hne (hJ hmJ hs ((algebraMap L M).injective h).symm)
    exact div_self this
  · intro i hi hne
    rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm hne, hs⟩) (by simp), mul_zero]
  · intro h; exact absurd hs h

/-- **Off `J`, the interpolation is barycentric**: `ℓ(s) · Σ_i y i · w_i (pt s − pt i)⁻¹`. -/
theorem interpF_bary {pt : ℕ → L} {J : Finset ℕ} {s : ℕ} (hs : ∀ m ∈ J, pt s ≠ pt m)
    (y : ℕ → M) :
    interpF pt J y s = algebraMap L M (∏ m ∈ J, (pt s - pt m)) *
      ∑ i ∈ J, y i * algebraMap L M ((∏ m ∈ J.erase i, (pt i - pt m))⁻¹ * (pt s - pt i)⁻¹) := by
  unfold interpF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsi : pt s - pt i ≠ 0 := sub_ne_zero.2 (hs i hi)
  have hl : ∏ m ∈ J, (pt s - pt m) = (pt s - pt i) * ∏ m ∈ J.erase i, (pt s - pt m) :=
    (Finset.mul_prod_erase J (fun m => pt s - pt m) hi).symm
  have e : ∏ m ∈ J.erase i, (algebraMap L M (pt s) - algebraMap L M (pt m)) /
      (algebraMap L M (pt i) - algebraMap L M (pt m)) =
      algebraMap L M (∏ m ∈ J.erase i, (pt s - pt m) / (pt i - pt m)) := by
    rw [map_prod]; simp [map_sub, map_div₀]
  rw [e, Finset.prod_div_distrib, hl]
  rw [mul_left_comm, ← map_mul]
  congr 2
  field_simp

end Pure

/-- `b·2^k + j = b·2^k ⊕ j` for `j < 2^k`. -/
theorem mul_two_pow_add_eq_xor {b k j : ℕ} (hj : j < 2 ^ k) : b * 2 ^ k + j = b * 2 ^ k ^^^ j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hj, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases h : i < k
  · simp [h, show ¬ (k ≤ i) by omega]
  · rw [if_neg h, Nat.testBit_lt_two_pow (hj.trans_le (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
    simp [show k ≤ i by omega]

/-- `pt` is additive on an aligned block: `pt (b·2^k + j) = pt (b·2^k) + pt j` (`j < 2^k`). -/
theorem pt_block {L : Type*} [Field L] {pt : ℕ → L} (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    {b k j : ℕ} (hj : j < 2 ^ k) : pt (b * 2 ^ k + j) = pt (b * 2 ^ k) + pt j := by
  rw [mul_two_pow_add_eq_xor hj, hadd]

section Fwd

variable {L : Type*} [Field L] [CharP L 2] {M : Type*} [Field M] [Algebra L M]

/-- **One forward level** `l`: in each block of `2^(l+1)` at `base`, the halves `u` (low) and
`w` (high) become `u + α w` (low) and `u + α w + w` (high), `α = Ŵ_l(pt base)` (`bflyLevel`'s
inverse). -/
def fwdLevel (pt : ℕ → L) (N : ℕ) (l : ℕ) (A : ℕ → M) (i : ℕ) : M :=
  let base := i / 2 ^ (l + 1) * 2 ^ (l + 1)
  let x := i % 2 ^ (l + 1)
  let u := A (base + x % 2 ^ l)
  let w := A (base + 2 ^ l + x % 2 ^ l)
  let α := algebraMap L M (wAt pt N l base)
  if x < 2 ^ l then u + α * w else u + α * w + w

/-- **The forward iteration**: levels `ℓ − 1, ℓ − 2, …, 0`. -/
def fwdRun (pt : ℕ → L) (N : ℕ) : ℕ → (ℕ → M) → ℕ → M
  | 0, A => A
  | l + 1, A => fwdRun pt N l (fwdLevel pt N l A)

/-- `Ŵ_ℓ` on the block `b` of size `2^(ℓ+1)`: `Ŵ_ℓ(pt(b·2^(ℓ+1) + j))` is `α` on the low half
and `α + 1` on the high half. -/
theorem normW_block {pt : ℕ → L} {N : ℕ} (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {ℓ b j : ℕ} (hN : (b + 1) * 2 ^ (ℓ + 1) ≤ 2 ^ N)
    (hj : j < 2 ^ (ℓ + 1)) :
    (normW pt ℓ).eval (pt (b * 2 ^ (ℓ + 1) + j)) =
      wAt pt N ℓ (b * 2 ^ (ℓ + 1)) + if j < 2 ^ ℓ then 0 else 1 := by
  have hℓ : ℓ < N := by
    by_contra h
    have : 2 ^ (N + 1) ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (ℓ + 1) ≤ (b + 1) * 2 ^ (ℓ + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 2 ^ N < 2 ^ (N + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hb : b * 2 ^ (ℓ + 1) < 2 ^ N := by
    have : 0 < 2 ^ (ℓ + 1) := by positivity
    nlinarith
  rw [pt_block hadd hj, normW_add hadd, wAt_eq hadd hpt hℓ hb]
  congr 1
  split_ifs with h
  · exact normW_eval_lt pt h
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 h)
    rw [two_pow_add_eq_xor (show j' < 2 ^ ℓ by omega), hadd, normW_add hadd,
      normW_eval_lt pt (show j' < 2 ^ ℓ by omega), add_zero]
    exact normW_eval_self hpt hℓ

/-- **The block invariant**: after the levels `ℓ − 1, …, 0`, position `j` of block `b` holds the
value at `pt(b·2^ℓ + j)` of the block's coefficients. -/
theorem fwdRun_block {pt : ℕ → L} {N : ℕ} (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) :
    ∀ (ℓ : ℕ) (A : ℕ → M) (b j : ℕ), j < 2 ^ ℓ → (b + 1) * 2 ^ ℓ ≤ 2 ^ N →
    fwdRun pt N ℓ A (b * 2 ^ ℓ + j) = ∑ x ∈ range (2 ^ ℓ),
      A (b * 2 ^ ℓ + x) * algebraMap L M ((novelX pt x).eval (pt (b * 2 ^ ℓ + j))) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro A b j hj _
    obtain rfl : j = 0 := by simpa using hj
    simp [fwdRun, novelX, bitProd, bitSel]
  | succ ℓ ih =>
    intro A b j hj hN
    have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ ℓ := by positivity
    -- the level's value at the two halves
    have hval : ∀ x < 2 ^ ℓ, ∀ e < 2, fwdLevel pt N ℓ A ((2 * b + e) * 2 ^ ℓ + x) =
        A (b * 2 ^ (ℓ + 1) + x) + algebraMap L M (wAt pt N ℓ (b * 2 ^ (ℓ + 1))) *
          A (b * 2 ^ (ℓ + 1) + 2 ^ ℓ + x) + if e = 0 then 0 else A (b * 2 ^ (ℓ + 1) + 2 ^ ℓ + x) := by
      intro x hx e he
      have hi : (2 * b + e) * 2 ^ ℓ + x = b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x) := by rw [hp]; ring
      have hlt : e * 2 ^ ℓ + x < 2 ^ (ℓ + 1) := by
        rw [hp]; interval_cases e <;> omega
      have hdiv : (b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x)) / 2 ^ (ℓ + 1) = b := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
          Nat.zero_add]
      have hmod : (b * 2 ^ (ℓ + 1) + (e * 2 ^ ℓ + x)) % 2 ^ (ℓ + 1) = e * 2 ^ ℓ + x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
      have hxm : (e * 2 ^ ℓ + x) % 2 ^ ℓ = x := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rw [hi, fwdLevel]
      simp only [hdiv, hmod, hxm]
      interval_cases e
      · simp [hx]
      · rw [if_neg (by omega), if_neg (by omega)]
    -- the target, split by the top coefficient bit
    have hN' : (2 * b + 1 + 1) * 2 ^ ℓ ≤ 2 ^ N := by
      have : (2 * b + 1 + 1) * 2 ^ ℓ = (b + 1) * 2 ^ (ℓ + 1) := by rw [hp]; ring
      omega
    have key : ∀ e < 2, ∀ j' < 2 ^ ℓ, j = e * 2 ^ ℓ + j' →
        fwdRun pt N (ℓ + 1) A (b * 2 ^ (ℓ + 1) + j) = ∑ x ∈ range (2 ^ (ℓ + 1)),
          A (b * 2 ^ (ℓ + 1) + x) * algebraMap L M ((novelX pt x).eval (pt (b * 2 ^ (ℓ + 1) + j))) := by
      intro e he j' hj' hjj
      have hpos2 : b * 2 ^ (ℓ + 1) + j = (2 * b + e) * 2 ^ ℓ + j' := by rw [hjj, hp]; ring
      rw [fwdRun, hpos2, ih (fwdLevel pt N ℓ A) (2 * b + e) j' hj' (by
        have : (2 * b + e + 1) * 2 ^ ℓ ≤ (2 * b + 1 + 1) * 2 ^ ℓ :=
          Nat.mul_le_mul_right _ (by omega)
        omega)]
      rw [← hpos2, sum_novel_succ, normW_block hadd hpt (by rwa [show (b + 1) * 2 ^ (ℓ + 1) =
        (2 * b + 1 + 1) * 2 ^ ℓ by rw [hp]; ring]) hj]
      refine sum_congr rfl fun x hx => ?_
      have hx' := mem_range.1 hx
      rw [hval x hx' e he]
      have hjlt : (j < 2 ^ ℓ) ↔ e = 0 := by
        constructor
        · intro h; by_contra h'; have : e = 1 := by omega
          subst this; omega
        · intro h; subst h; omega
      by_cases h0 : e = 0
      · rw [if_pos h0, if_pos (hjlt.2 h0), Nat.add_assoc, add_zero, add_zero]; ring
      · rw [if_neg h0, if_neg (fun h => h0 (hjlt.1 h)), Nat.add_assoc, map_add, map_one]; ring
    by_cases hlo : j < 2 ^ ℓ
    · exact key 0 (by norm_num) j hlo (by ring)
    · exact key 1 (by norm_num) (j - 2 ^ ℓ) (by rw [hp] at hj; omega) (by omega)

/-- **The forward run is `Enc`**: on a message `c` of `2^m` coefficients zero-padded to `2^n`
(`m ≤ n ≤ N`), the `n` forward levels give `encN pt c j` at every position `j < 2^n`. -/
theorem fwdRun_enc {pt : ℕ → L} {N : ℕ} (hadd : ∀ a b, pt (a ^^^ b) = pt a + pt b)
    (hpt : Set.InjOn pt (Set.Iio (2 ^ N))) {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ N)
    (c : Fin (2 ^ m) → M)
    (A : ℕ → M) (hA : ∀ x, A x = if h : x < 2 ^ m then c ⟨x, h⟩ else 0) {j : ℕ} (hj : j < 2 ^ n) :
    fwdRun pt N n A j = encN pt c j := by
  have hnN : 2 ^ n ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hn
  have hN : (0 + 1) * 2 ^ n ≤ 2 ^ N := by omega
  have h := fwdRun_block hadd hpt n A 0 j hj hN
  simp only [Nat.zero_mul, Nat.zero_add] at h
  have hm : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hmn
  rw [h, encN, ← sum_range_add_sum_Ico _ hm, sum_eq_zero (s := Ico _ _) (fun x hx => by
      rw [hA x, dif_neg (by have := (mem_Ico.1 hx).1; omega), zero_mul]), add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun x => A x * algebraMap L M ((novelX pt x).eval (pt j)))]
  exact sum_congr rfl fun x _ => by rw [hA x, dif_pos x.2]

end Fwd

end Lvm.Nb
