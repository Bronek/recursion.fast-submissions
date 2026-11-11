-- New for lvm2 (WP T-V): S2's WHIR openings (FRZ-0 §2.1, row `LvmWhirParams`): `C_main` at ν = 24 (P20)
-- and S2's P8 test set (`C_main` ν = 23 with three levels, `C_rec` ν = 18), their unique-decoding codes
-- and per-group error bounds, by `norm_num` on natural numbers, with v1's helpers from `LvmWhirParams`.
/-
  LeanVM.Protocol.Whir.Sound (lvm2 S2 parameters)

  The configurations `cfgMain24`, `cfgMain23`, `cfgRec18`, their codes, the arithmetic
  `LadderArithUd`, the escape bounds `whirEpsUd ≤ 2^-129` (P20) and `≤ 2^-20` (P8), and the
  stacked-opening specifications at those parameters. `C_rec` at P20 stays v1's `cfgRec20`.
-/

import LvmWhirParams

/-!
# lvm2's S2 WHIR parameters

| opening | `μ` | levels `(ℓ, R, t)` | `κ_i` | root `c₀` of `n₀` |
|---|---|---|---|---|
| `cfgMain24` (`C_main`, P20) | 24 | (6,1,311) (4,2,191) (4,3,156) | 18 14 10 | 0 of 2 |
| `cfgRec20` (`C_rec`, P20, v1) | 19 | (6,2,191) | 13 | 1 of 2 |
| `cfgMain23` (`C_main`, P8) | 23 | (6,1,49) (4,2,30) (4,3,25) | 17 13 9 | 0 of 2 |
| `cfgRec18` (`C_rec`, P8) | 18 | (6,2,30) | 12 | 1 of 2 |

As in v1: 8 positions per challenge, `direct = false`, every level's code `LevelCode.ud κ_i R_i`;
the final residuals are `2^10` (`cfgMain24`), `2^9` (`cfgMain23`) and `2^12` (`cfgRec18`) scalars.
`C_main` is root 0 and `C_rec` root 1 of `n₀ = 2`, exactly as v1.

Per-group bounds at P20 (A13):

* fold, per challenge: `eFold ≤ 2^-151, 2^-160, 2^-167` (exact `2^-152.0`, `2^-160.4`, `2^-167.2`;
  level 0's numerator `2^40 + 2^24 + 2` is just above `2^40`, hence 151);
* positions and query groups (with `λ`) `≤ 2^-129` at `t = 311, 191, 156`;
* `whirEpsUd ≤ 2^-129`. At P8 (20-bit test set) `≤ 2^-20`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

-- The positions' bounds raise `(A − 1)` to the query counts (up to 311): let `norm_num` evaluate them.
set_option exponentiation.threshold 512

section

/-! ## The configurations -/

/-- `C_main` at S2 P20: `μ = 24`, levels `(6,1,311) (4,2,191) (4,3,156)`, root `0` of `2`. -/
def cfgMain24 : UdConfig := ⟨24, [⟨6, 1, 311⟩, ⟨4, 2, 191⟩, ⟨4, 3, 156⟩], 8, 0, 2, false, 0⟩

/-- `C_main` at S2 P8: `μ = 23`, levels `(6,1,49) (4,2,30) (4,3,25)`, root `0` of `2`. -/
def cfgMain23 : UdConfig := ⟨23, [⟨6, 1, 49⟩, ⟨4, 2, 30⟩, ⟨4, 3, 25⟩], 8, 0, 2, false, 0⟩

/-- `C_rec` at S2 P8: `μ = 18`, one level `(6,2,30)`, final `2^12` scalars, root `1` of `2`. -/
def cfgRec18 : UdConfig := ⟨18, [⟨6, 2, 30⟩], 8, 1, 2, false, 0⟩

/-- The UD codes of `C_main` at S2 P20: `κ = 18, 14, 10`, `R = 1, 2, 3`. -/
noncomputable def codesMain24 : ℕ → LevelCode
  | 0 => LevelCode.ud 18 1 (by norm_num) (by norm_num) (by norm_num)
  | 1 => LevelCode.ud 14 2 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 10 3 (by norm_num) (by norm_num) (by norm_num)

/-- The UD codes of `C_main` at S2 P8: `κ = 17, 13, 9`, `R = 1, 2, 3`. -/
noncomputable def codesMain23 : ℕ → LevelCode
  | 0 => LevelCode.ud 17 1 (by norm_num) (by norm_num) (by norm_num)
  | 1 => LevelCode.ud 13 2 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 9 3 (by norm_num) (by norm_num) (by norm_num)

/-- The UD code of `C_rec` at S2 P8: `κ = 12`, `R = 2`. -/
noncomputable def codesRec18 : ℕ → LevelCode
  | _ => LevelCode.ud 12 2 (by norm_num) (by norm_num) (by norm_num)

/-! ## P20: per-group bounds (A13) -/

/-- **Fold, per challenge** (A13): `C_main` levels `≤ 2^-151, 2^-160, 2^-167`. -/
theorem eFold_main24 :
    eFold (codesMain24 0) 6 ≤ (2 : ENNReal)⁻¹ ^ 151 ∧ eFold (codesMain24 1) 4 ≤ (2 : ENNReal)⁻¹ ^ 160 ∧
      eFold (codesMain24 2) 4 ≤ (2 : ENNReal)⁻¹ ^ 167 := by
  refine ⟨eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_⟩ <;>
    simp only [udMca, mcaUd, udThr] <;> norm_num

/-- **Positions** (A13): `((A_i − 1)/n_i)^{t_i} ≤ 2^-129` at every level of `C_main`. -/
theorem positions_main24 :
    ((((codesMain24 0).thr - 1 : ℕ) : ENNReal) / (codesMain24 0).n) ^ 311 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain24 1).thr - 1 : ℕ) : ENNReal) / (codesMain24 1).n) ^ 191 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain24 2).thr - 1 : ℕ) : ENNReal) / (codesMain24 2).n) ^ 156 ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  refine ⟨positions_ud_le _ _ ?_, positions_ud_le _ _ ?_, positions_ud_le _ _ ?_⟩ <;>
    simp only [udThr] <;> norm_num

/-- The query groups (positions and `λ`) of `C_main` at S2 P20. -/
theorem eQuery_main24 :
    eQueryUd (codesMain24 0) (codesMain24 1) 311 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      eQueryUd (codesMain24 1) (codesMain24 2) 191 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      eQueryFinal (codesMain24 2) 156 ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  refine ⟨eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_⟩ <;>
    simp only [udThr] <;> norm_num

/-- **`εmax` of `C_main` at S2 P20**: every group escape is at most `2^-129`. -/
theorem whirEps_main24 : whirEpsUd codesMain24 cfgMain24.grind cfgMain24.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨f0, f1, f2⟩ := eFold_main24
  obtain ⟨q0, q1, q2⟩ := eQuery_main24
  simp only [whirEpsUd, cfgMain24, levelEpsUd, max_le_iff, pow_zero, one_mul]
  exact ⟨⟨f0.trans (inv_two_pow_anti (by norm_num)), q0⟩,
    ⟨f1.trans (inv_two_pow_anti (by norm_num)), q1⟩,
    f2.trans (inv_two_pow_anti (by norm_num)), q2, eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

/-- **The levels' arithmetic of `C_main` at S2 P20.** -/
theorem ladderArith_main24 :
    LadderArithUd cfgMain24.μ cfgMain24.per codesMain24 0 0 cfgMain24.levels := by
  obtain ⟨q0, q1, q2⟩ := eQuery_main24
  have h := inv_two_pow_lt_one (c := 129) (by norm_num)
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgMain24, codesMain24], le_rfl,
    rfl, rfl, q1.trans_lt h, by norm_num [cfgMain24, codesMain24], le_rfl,
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain24, codesMain24]⟩

/-! ## S2 P8: the test set, `2^-20` -/

/-- **`εmax` of `C_main` at S2 P8**: every group escape is at most `2^-20`. -/
theorem whirEps_main23 : whirEpsUd codesMain23 cfgMain23.grind cfgMain23.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgMain23, levelEpsUd, max_le_iff, pow_zero, one_mul]
  refine ⟨⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩, ⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩,
    eFold_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;>
    norm_num

/-- **`εmax` of `C_rec` at S2 P8.** -/
theorem whirEps_rec18 : whirEpsUd codesRec18 cfgRec18.grind cfgRec18.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgRec18, levelEpsUd, max_le_iff, pow_zero, one_mul]
  refine ⟨eFold_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;>
    norm_num

/-- The query groups of S2 P8 (for the arithmetic). -/
theorem eQuery_P8s2 :
    eQueryUd (codesMain23 0) (codesMain23 1) 49 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryUd (codesMain23 1) (codesMain23 2) 30 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryFinal (codesMain23 2) 25 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryFinal (codesRec18 0) 30 ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  refine ⟨eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eQueryFinal_ud_le _ _ ?_⟩ <;> simp only [udThr] <;> norm_num

/-- **The levels' arithmetic of `C_main` at S2 P8.** -/
theorem ladderArith_main23 :
    LadderArithUd cfgMain23.μ cfgMain23.per codesMain23 0 0 cfgMain23.levels := by
  obtain ⟨q0, q1, q2, -⟩ := eQuery_P8s2
  have h := inv_two_pow_lt_one (c := 20) (by norm_num)
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgMain23, codesMain23], le_rfl,
    rfl, rfl, q1.trans_lt h, by norm_num [cfgMain23, codesMain23], le_rfl,
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain23, codesMain23]⟩

/-- **The levels' arithmetic of `C_rec` at S2 P8.** -/
theorem ladderArith_rec18 :
    LadderArithUd cfgRec18.μ cfgRec18.per codesRec18 0 0 cfgRec18.levels :=
  ⟨rfl, rfl, eQuery_P8s2.2.2.2.trans_lt (inv_two_pow_lt_one (by norm_num)),
    by norm_num [cfgRec18, codesRec18]⟩

/-! ## The stacked openings at S2's parameters -/

/-- **`C_main`'s stacked opening at S2 P20**: groups escape at most `2^-129`, the batching challenge
`(J − 1)/|E|`. -/
noncomputable def stackedMain24Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain24.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain24 claims)
      (fun h ↦ StackedPreUd cfgMain24 (codesMain24 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesMain24 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain24]) rfl (by norm_num [cfgMain24])
    (by norm_num [cfgMain24]) (by norm_num [cfgMain24]) ladderArith_main24 whirEps_main24 T

/-- **`C_main`'s stacked opening at S2 P8.** -/
noncomputable def stackedMain23Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain23.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain23 claims)
      (fun h ↦ StackedPreUd cfgMain23 (codesMain23 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesMain23 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain23]) rfl (by norm_num [cfgMain23])
    (by norm_num [cfgMain23]) (by norm_num [cfgMain23]) ladderArith_main23 whirEps_main23 T

/-- **`C_rec`'s stacked opening at S2 P8.** -/
noncomputable def stackedRec18Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec18.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec18 claims)
      (fun h ↦ StackedPreUd cfgRec18 (codesRec18 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec18 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec18]) rfl (by norm_num [cfgRec18])
    (by norm_num [cfgRec18]) (by norm_num [cfgRec18]) ladderArith_rec18 whirEps_rec18 T

/-- The batching challenge at `C_main`'s S2 root: at most `2^-129` for `J ≤ 2^63` claims. -/
theorem eBatch_main24 (J : ℕ) (hJ : J ≤ 2 ^ 63) :
    eBatch J (codesMain24 0) ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  have h : (J - 1) * 2 ^ 129 ≤ 2 ^ 192 :=
    (Nat.mul_le_mul_right _ ((Nat.sub_le J 1).trans hJ)).trans (by norm_num)
  exact eBatch_ud_le _ _ h

end
end LeanVM.Protocol.Whir.Sound
