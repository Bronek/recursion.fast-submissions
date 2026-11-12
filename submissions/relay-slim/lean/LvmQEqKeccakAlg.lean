import LvmQKeccakSpec
import LvmQSumcheck

/-!
# QA1: `F`'s materialised Keccak weights = the circuit's structured forms (`Lvm.FE` algebra)

Pure algebra on `Lvm.FE` (no reader, no builder). `F` = `LvmDecideKeccak` (leanVM's verifier on the
fast field types); the structured forms are `LvmQKeccakSpec`'s.

* `lt_getD`: `keccakLinearTranspose` in closed form, `θᵀ` of the weights moved back through `ρπ`
  (adapted from WP-2's `LvmKeccakLinear`, which proves it over `LeanVM.Parameters.E` for the
  ported verifier; here for `F`'s copy over `Lvm.FE`).
* **`lane_dot`**: `Σ_z u(z)·Lᵀ(prodW A B)(64ℓ + z) = laneForm B (rotSum u A) ℓ`; **`weighted_kForm`**:
  `F`'s final-check weight on `Lᵀ(prodW A B)` is `kForm`.
* `eqAt_prod` (product formula of `eqKernel`), `eqAt_split`, **`shift_LH`**: the rotated `eq` sum
  through the guest's two 8-entry tables.
* **`iota_flips`**: `F`'s iota sum on `Lᵀ(prodW A B)` for every round constant is
  `Σ_{i<7} rcBit·flipForm` (round constants use bits `2^i − 1` only).
* First claim (`w1 = lanes ⊗ x^z`): **`weighted_first`** (`(Σ f·lanes)·indexMle b`), **`iota_first`**.
* `keccakOpen`'s fold: `slotWeights_getD`, `foldAll_eq` (adapted from WP-2's
  `LvmKeccakSlotWeights`), **`open_committed`**, **`open_input`**.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Finset

/-! ## Sums and lists (adapted from rf-lvm-QA1 LvmKeccakLinear.lean, WP-2) -/

theorem listSum_range (f : ℕ → FE) (n : ℕ) :
    ((List.range n).map f).sum = ∑ y ∈ range n, f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sumE_range (f : ℕ → FE) (n : ℕ) : sumE ((List.range n).map f) = ∑ y ∈ range n, f y := by
  rw [sumE_eq_sum, listSum_range]

theorem sum_range_mul' (a b : ℕ) (F : ℕ → FE) :
    ∑ p ∈ range (a * b), F p = ∑ i ∈ range a, ∑ k ∈ range b, F (b * i + k) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Nat.mul_comm a b]

theorem array_getD_toArray' (l : List FE) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem setIfInBounds_getD' (a : Array FE) (i p : ℕ) (x : FE) :
    (a.setIfInBounds i x).getD p 0 = if i = p ∧ i < a.size then x else a.getD p 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs <;> simp_all
  omega

/-- A row of a grid flattened by rows. -/
theorem flatMap_getD' (F : ℕ → ℕ → FE) (m : ℕ) :
    ∀ (n x z : ℕ), x < n → z < m →
      ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).getD (m * x + z) 0 = F x z
  | 0, _, _, hx, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, x, z, hx, hz => by
    have hlen : ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
      simp [List.length_flatMap, List.sum_replicate]
    rw [List.range_succ, List.flatMap_append]
    by_cases hxn : x < n
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; nlinarith)]
      exact flatMap_getD' F m n x z hxn hz
    · have : x = n := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; nlinarith), hlen]
      simp [Nat.mul_comm, hz, List.getD_eq_getElem?_getD]

theorem flatMap_length' (F : ℕ → ℕ → FE) (m n : ℕ) :
    ((List.range n).flatMap fun x ↦ (List.range m).map (F x)).length = n * m := by
  simp [List.length_flatMap, List.sum_replicate]

/-! ## `keccakLinearTranspose` in closed form (adapted from WP-2's `LvmKeccakLinear`) -/

/-- A θ column sum: `Σ_y v(x + 5y, z)`. -/
def colLE (v : ℕ → FE) (x z : ℕ) : FE := ∑ y ∈ range 5, v (64 * (x + 5 * y) + z)

/-- The transpose of θ: `g` plus the columns `x + 1` at `z` and `x − 1` at `z + 1`. -/
def thetaTE (g : ℕ → FE) (p : ℕ) : FE :=
  g p + colLE g ((p / 64 % 5 + 1) % 5) (p % 64) + colLE g ((p / 64 % 5 + 4) % 5) ((p % 64 + 1) % 64)

/-- Where `ρπ` takes position `p` from: lane `π(ℓ)`, slice `z + ρ_ℓ`. -/
def rhoPiDstE (p : ℕ) : ℕ := 64 * keccakPi (p / 64) + (p % 64 + keccakRho.getD (p / 64) 0) % 64

/-- θ's input weights after ρπ. -/
def gOfE (w : List FE) (p : ℕ) : FE := w.getD (rhoPiDstE p) 0

theorem inner_loopE (W : ℕ → FE) (lane : ℕ) (g : Array FE) :
    ∀ Z, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).size =
        g.size ∧
      ∀ p, ((List.range Z).foldl (fun g z ↦ g.setIfInBounds (64 * lane + z) (W z)) g).getD p 0 =
        if 64 * lane ≤ p ∧ p < 64 * lane + Z ∧ p < g.size then W (p - 64 * lane)
        else g.getD p 0
  | 0 => ⟨rfl, fun p ↦ by simp; omega⟩
  | Z + 1 => by
    obtain ⟨hs, hg⟩ := inner_loopE W lane g Z
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by simp [hs], fun p ↦ ?_⟩
    rw [setIfInBounds_getD', hg p, hs]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

theorem outer_loopE (w : List FE) :
    ∀ L, L ≤ 25 →
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).size = 1600 ∧
      ∀ p, ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)).getD p 0 = if p < 64 * L then gOfE w p else 0
  | 0, _ => ⟨by simp [keccakBits], fun p ↦ by
      simp [Array.getD_eq_getD_getElem?, keccakBits, Array.getElem?_replicate]
      split_ifs <;> rfl⟩
  | L + 1, hL => by
    obtain ⟨hs, hg⟩ := outer_loopE w L (by omega)
    rw [List.range_succ (n := L), List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_loopE
      (fun z ↦ w.toArray.getD (64 * keccakPi L + (z + keccakRho.getD L 0) % 64) 0) L
      ((List.range L).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
        g.setIfInBounds (64 * lane + z)
          (w.toArray.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
        (Array.replicate keccakBits 0)) 64
    refine ⟨hs'.trans hs, fun p ↦ ?_⟩
    rw [hg' p, hg p, hs]
    by_cases h1 : 64 * L ≤ p ∧ p < 64 * L + 64 ∧ p < 1600
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArray', gOfE, rhoPiDstE]
      have e1 : p / 64 = L := by omega
      have e2 : p % 64 = p - 64 * L := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : p < 64 * L
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem columns_getDE (A : Array FE) {x z : ℕ} (hx : x < 5) (hz : z < 64) :
    ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
        sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
      (64 * x + z) 0 = colLE (fun p ↦ A.getD p 0) x z := by
  rw [array_getD_toArray', flatMap_getD' (fun x z ↦
    sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)) 64 5 x z hx hz]
  rw [sumE_range]
  rfl

theorem transposeList_getDE (A : Array FE) (g : ℕ → FE) (hA : ∀ p < 1600, A.getD p 0 = g p)
    {p : ℕ} (hp : p < 1600) :
    ((List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
      A.getD (64 * lane + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 1) % 5) + z) 0 +
        ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
          sumE ((List.range 5).map fun y ↦ A.getD (64 * (x + 5 * y) + z) 0)).toArray.getD
          (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0).getD p 0 = thetaTE g p := by
  have hp' : p = 64 * (p / 64) + p % 64 := by omega
  conv_lhs => rw [hp']
  rw [flatMap_getD' _ 64 25 (p / 64) (p % 64) (by omega) (Nat.mod_lt _ (by omega))]
  rw [columns_getDE _ (by omega) (Nat.mod_lt _ (by omega)),
    columns_getDE _ (by omega) (Nat.mod_lt _ (by omega)), ← hp', hA p hp]
  have hcol : ∀ x z, x < 5 → z < 64 → colLE (fun p ↦ A.getD p 0) x z = colLE g x z := by
    intro x z hx hz
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    simp only [Finset.mem_range] at hy
    exact hA _ (by omega)
  rw [hcol _ _ (by omega) (Nat.mod_lt _ (by omega)), hcol _ _ (by omega) (Nat.mod_lt _ (by omega))]
  rfl

/-- **`keccakLinearTranspose` in closed form** (`F`'s copy over `Lvm.FE`). -/
theorem lt_getD (w : List FE) {p : ℕ} (hp : p < 1600) :
    (keccakLinearTranspose w).getD p 0 = thetaTE (gOfE w) p := by
  obtain ⟨-, hg⟩ := outer_loopE w 25 le_rfl
  exact transposeList_getDE _ (gOfE w) (fun q hq ↦ by rw [hg, ite_eq_left (by omega)]) hp

theorem lt_length (w : List FE) : (keccakLinearTranspose w).length = 1600 := by
  unfold keccakLinearTranspose
  simp only []
  rw [flatMap_length']

end Lvm.Q1
