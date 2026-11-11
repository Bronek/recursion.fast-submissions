-- New for lvm (WP-7): the WHIR openings of lvm's parameter sets `P20` and `P8` (BLUEPRINT §3.1, A11, A13;
-- `docs/lvm/ref/params.py`), their unique-decoding codes, and their per-group error bounds, by `norm_num` on
-- natural numbers (no `decide` tables). Replaces leanVM's `Whir/Params/{Check,Deployed}`.
/-
  LeanVM.Protocol.Whir.Sound (lvm parameters)

  The configurations `cfgMain20`, `cfgRec20`, `cfgMain8`, `cfgRec8`, their codes, the arithmetic
  `LadderArithUd`, the escape bounds `whirEpsUd ≤ 2^-129` (P20) and `≤ 2^-20` (P8), and the
  stacked-opening specifications at those parameters.
-/

import LvmWhirSpec

/-!
# lvm's WHIR parameters

| opening | `μ` | levels `(ℓ, R, t)` | `κ_i` | root `c₀` of `n₀` |
|---|---|---|---|---|
| `cfgMain20` (`C_main`, P20) | 26 | (6,1,311) (4,2,191) (4,3,156) (4,4,142) | 20 16 12 8 | 0 of 2 |
| `cfgRec20` (`C_rec`, P20) | 19 | (6,2,191) | 13 | 1 of 2 |
| `cfgMain8` (`C_main`, P8) | 23 | (6,1,49) (4,2,30) (4,3,25) (4,4,22) | 17 13 9 5 | 0 of 2 |
| `cfgRec8` (`C_rec`, P8) | 17 | (6,2,30) | 11 | 1 of 2 |

8 positions per challenge (BLUEPRINT §2.2). Neither commitment checks its opened positions directly
against the residual's encoding (`direct = false`; A20 drops A10's direct check of `C_rec`). Every level's code is `LevelCode.ud κ_i R_i`
(threshold `udThr`, list `1`, MCA `udMca`); the final residuals are `2^8`, `2^13`, `2^5`, `2^11`
scalars (`κ` of the last level). The schedule's commitments: `main0` (index 0), `rec0` (index 1);
`C_rec` is opened first and adds none, so both openings start with `n₀ = 2`.

Per-group bounds at P20 (BLUEPRINT §3.2 as amended by A13), each proved from a natural-number
inequality by `norm_num`:

* fold, per challenge: `eFold ≤ 2^-147` (`C_main` level 0; the others smaller);
* positions: `((A_i − 1)/n_i)^{t_i} ≤ 2^-129` (`(A − 1)/n < (1 + 2^-R)/2 = 1 − δ`, WP-6
  `udThr_query`), and the whole query group with its `λ` (`+ t/|E|`) `≤ 2^-129`;
* tail rounds `2/|E|`, batching `(J − 1)/|E|` (`eBatch_ud`);
* `whirEpsUd ≤ 2^-129` for both openings. At P8 (20-bit test set) `≤ 2^-20`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

-- The positions' bounds raise `(A − 1)` to the query counts (up to 311): let `norm_num` evaluate them.
set_option exponentiation.threshold 512

section

/-! ## Inequalities in `ENNReal` from inequalities in `ℕ` -/

theorem two_pow_cast (k : ℕ) : ((2 ^ k : ℕ) : ENNReal) = 2 ^ k := by
  rw [Nat.cast_pow, Nat.cast_ofNat]

theorem card_E_ennreal : (Fintype.card E : ENNReal) = 2 ^ 192 := by
  rw [card_E, two_pow_cast]

/-- `N / M ≤ 2^-c` from `N · 2^c ≤ M`. -/
theorem natCast_div_le_inv_pow {N M c : ℕ} (_hM : 0 < M) (h : N * 2 ^ c ≤ M) :
    (N : ENNReal) / M ≤ (2 : ENNReal)⁻¹ ^ c := by
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.inv_pow, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  exact_mod_cast h

/-- `A / B + C / D ≤ 2^-c` from `(A D + C B) · 2^c ≤ B D`. -/
theorem natCast_div_add_div_le {A B C D c : ℕ} (hB : 0 < B) (hD : 0 < D)
    (h : (A * D + C * B) * 2 ^ c ≤ B * D) :
    (A : ENNReal) / B + (C : ENNReal) / D ≤ (2 : ENNReal)⁻¹ ^ c := by
  have hB0 : (B : ENNReal) ≠ 0 := by exact_mod_cast hB.ne'
  have hD0 : (D : ENNReal) ≠ 0 := by exact_mod_cast hD.ne'
  have h1 : (A : ENNReal) / B = ((A * D : ℕ) : ENNReal) / ((B * D : ℕ) : ENNReal) := by
    push_cast
    exact (ENNReal.mul_div_mul_right _ _ hD0 (ENNReal.natCast_ne_top D)).symm
  have h2 : (C : ENNReal) / D = ((C * B : ℕ) : ENNReal) / ((B * D : ℕ) : ENNReal) := by
    push_cast
    rw [mul_comm (B : ENNReal) (D : ENNReal)]
    exact (ENNReal.mul_div_mul_right _ _ hB0 (ENNReal.natCast_ne_top B)).symm
  rw [h1, h2, ENNReal.div_add_div_same, ← Nat.cast_add]
  exact natCast_div_le_inv_pow (Nat.mul_pos hB hD) h

/-- `(a / n)^t = a^t / n^t` in `ENNReal`, for naturals. -/
theorem natCast_div_pow (a n t : ℕ) :
    ((a : ENNReal) / n) ^ t = ((a ^ t : ℕ) : ENNReal) / ((n ^ t : ℕ) : ENNReal) := by
  push_cast
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_pow, ENNReal.inv_pow]

theorem inv_two_pow_lt_one {c : ℕ} (hc : 0 < c) : (2 : ENNReal)⁻¹ ^ c < 1 :=
  pow_lt_one₀ (by simp) (ENNReal.inv_lt_one.mpr (by norm_num)) hc.ne'

theorem inv_two_pow_anti {a b : ℕ} (h : a ≤ b) : (2 : ENNReal)⁻¹ ^ b ≤ (2 : ENNReal)⁻¹ ^ a :=
  pow_le_pow_right_of_le_one' (by simp [ENNReal.inv_le_one]) h

/-! ## The escapes of a unique-decoding level -/

/-- **The fold escape** of a UD level from its numerator: `(2 + 2^(ℓ−1)·udMca)·2^c ≤ 2^192`. -/
theorem eFold_ud_le {κ R : ℕ} {h64 hκ hR} (ℓ c : ℕ)
    (h : (2 * 1 + 2 ^ (ℓ - 1) * udMca κ R) * 2 ^ c ≤ 2 ^ 192) :
    eFold (LevelCode.ud κ R h64 hκ hR) ℓ ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eFold, card_E_ennreal, ← two_pow_cast 192]
  exact natCast_div_le_inv_pow (by positivity) h

/-- **The positions alone** of a UD level: `((udThr − 1)/n)^t ≤ 2^-c` from `(udThr − 1)^t·2^c ≤ n^t`. -/
theorem positions_ud_le {κ R : ℕ} {h64 hκ hR} (t c : ℕ)
    (h : (udThr κ R - 1) ^ t * 2 ^ c ≤ (2 ^ (κ + R)) ^ t) :
    ((((LevelCode.ud κ R h64 hκ hR).thr - 1 : ℕ) : ENNReal) / (LevelCode.ud κ R h64 hκ hR).n) ^ t ≤
      (2 : ENNReal)⁻¹ ^ c := by
  simp only [LevelCode.ud_thr, LevelCode.n, LevelCode.ud_κ, LevelCode.ud_R]
  rw [natCast_div_pow]
  exact natCast_div_le_inv_pow (by positivity) h

/-- **The final query group** of a UD level: positions and `λ`. -/
theorem eQueryFinal_ud_le {κ R : ℕ} {h64 hκ hR} (t c : ℕ)
    (h : ((udThr κ R - 1) ^ t * 2 ^ 192 + t * (2 ^ (κ + R)) ^ t) * 2 ^ c ≤
      (2 ^ (κ + R)) ^ t * 2 ^ 192) :
    eQueryFinal (LevelCode.ud κ R h64 hκ hR) t ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eQueryFinal, card_E_ennreal]
  simp only [LevelCode.ud_thr, LevelCode.n, LevelCode.ud_κ, LevelCode.ud_R]
  rw [natCast_div_pow, ← two_pow_cast 192]
  exact natCast_div_add_div_le (by positivity) (by positivity) h

/-- **The query group of a level with a next UD level**: positions and `λ` (`L' = 1`). -/
theorem eQueryUd_ud_le {κ R κ' R' : ℕ} {h64 hκ hR h64' hκ' hR'} (t c : ℕ)
    (h : ((udThr κ R - 1) ^ t * 2 ^ 192 + t * (2 ^ (κ + R)) ^ t) * 2 ^ c ≤
      (2 ^ (κ + R)) ^ t * 2 ^ 192) :
    eQueryUd (LevelCode.ud κ R h64 hκ hR) (LevelCode.ud κ' R' h64' hκ' hR') t ≤
      (2 : ENNReal)⁻¹ ^ c := by
  have := eQueryFinal_ud_le (h64 := h64) (hκ := hκ) (hR := hR) t c h
  rwa [eQueryUd, LevelCode.ud_listMax, mul_one, ← eQueryFinal]

/-- The tail rounds: `2/|E| ≤ 2^-191`. -/
theorem eTail_le : eTail ≤ (2 : ENNReal)⁻¹ ^ 191 := by
  rw [eTail, card_E_ennreal, ← two_pow_cast 192,
    show (2 : ENNReal) = ((2 : ℕ) : ENNReal) by norm_num]
  exact natCast_div_le_inv_pow (by positivity) (by norm_num)

/-- **The batching challenge** of a UD root: `eBatch J = (J − 1)/|E|`, at most `2^-c` when
`(J − 1)·2^c ≤ 2^192`. -/
theorem eBatch_ud_le {κ R : ℕ} {h64 hκ hR} (J c : ℕ) (h : (J - 1) * 2 ^ c ≤ 2 ^ 192) :
    eBatch J (LevelCode.ud κ R h64 hκ hR) ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eBatch, LevelCode.ud_listMax, mul_one, card_E_ennreal,
    ← two_pow_cast 192]
  exact natCast_div_le_inv_pow (by positivity) h

/-! ## The configurations -/

/-- `C_main` at P20: `μ = 26`, levels `(6,1,311) (4,2,191) (4,3,156) (4,4,142)`, root `0` of `2`. -/
def cfgMain20 : UdConfig := ⟨26, [⟨6, 1, 311⟩, ⟨4, 2, 191⟩, ⟨4, 3, 156⟩, ⟨4, 4, 142⟩], 8, 0, 2, false, 0⟩

/-- `C_rec` at P20: `μ = 19`, one level `(6,2,191)`, final `2^13` scalars, root `1` of `2`; no direct
final check (A20). -/
def cfgRec20 : UdConfig := ⟨19, [⟨6, 2, 191⟩], 8, 1, 2, false, 0⟩

/-- `C_main` at P8: `μ = 23`, levels `(6,1,49) (4,2,30) (4,3,25) (4,4,22)`, root `0` of `2`. -/
def cfgMain8 : UdConfig := ⟨23, [⟨6, 1, 49⟩, ⟨4, 2, 30⟩, ⟨4, 3, 25⟩, ⟨4, 4, 22⟩], 8, 0, 2, false, 0⟩

/-- `C_rec` at P8: `μ = 17`, one level `(6,2,30)`, final `2^11` scalars, root `1` of `2`. -/
def cfgRec8 : UdConfig := ⟨17, [⟨6, 2, 30⟩], 8, 1, 2, false, 0⟩

/-- The UD codes of `C_main` at P20: `κ = 20, 16, 12, 8`, `R = 1, 2, 3, 4`. -/
noncomputable def codesMain20 : ℕ → LevelCode
  | 0 => LevelCode.ud 20 1 (by norm_num) (by norm_num) (by norm_num)
  | 1 => LevelCode.ud 16 2 (by norm_num) (by norm_num) (by norm_num)
  | 2 => LevelCode.ud 12 3 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 8 4 (by norm_num) (by norm_num) (by norm_num)

/-- The UD code of `C_rec` at P20: `κ = 13`, `R = 2`. -/
noncomputable def codesRec20 : ℕ → LevelCode
  | _ => LevelCode.ud 13 2 (by norm_num) (by norm_num) (by norm_num)

/-- The UD codes of `C_main` at P8: `κ = 17, 13, 9, 5`, `R = 1, 2, 3, 4`. -/
noncomputable def codesMain8 : ℕ → LevelCode
  | 0 => LevelCode.ud 17 1 (by norm_num) (by norm_num) (by norm_num)
  | 1 => LevelCode.ud 13 2 (by norm_num) (by norm_num) (by norm_num)
  | 2 => LevelCode.ud 9 3 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 5 4 (by norm_num) (by norm_num) (by norm_num)

/-- The UD code of `C_rec` at P8: `κ = 11`, `R = 2`. -/
noncomputable def codesRec8 : ℕ → LevelCode
  | _ => LevelCode.ud 11 2 (by norm_num) (by norm_num) (by norm_num)

/-! ## P20: per-group bounds (A13) -/

/-- **Fold, per challenge** (A13): `C_main` levels `≤ 2^-147, 2^-156, 2^-163, 2^-170`, `C_rec`
`≤ 2^-160`. -/
theorem eFold_P20 :
    eFold (codesMain20 0) 6 ≤ (2 : ENNReal)⁻¹ ^ 147 ∧ eFold (codesMain20 1) 4 ≤ (2 : ENNReal)⁻¹ ^ 156 ∧
      eFold (codesMain20 2) 4 ≤ (2 : ENNReal)⁻¹ ^ 163 ∧
      eFold (codesMain20 3) 4 ≤ (2 : ENNReal)⁻¹ ^ 170 ∧
      eFold (codesRec20 0) 6 ≤ (2 : ENNReal)⁻¹ ^ 160 := by
  refine ⟨eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_,
    eFold_ud_le _ _ ?_⟩ <;> simp only [udMca, mcaUd, udThr] <;> norm_num

/-- **Positions** (A13): `((A_i − 1)/n_i)^{t_i} ≤ 2^-129` at every level of both openings. -/
theorem positions_P20 :
    ((((codesMain20 0).thr - 1 : ℕ) : ENNReal) / (codesMain20 0).n) ^ 311 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain20 1).thr - 1 : ℕ) : ENNReal) / (codesMain20 1).n) ^ 191 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain20 2).thr - 1 : ℕ) : ENNReal) / (codesMain20 2).n) ^ 156 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesMain20 3).thr - 1 : ℕ) : ENNReal) / (codesMain20 3).n) ^ 142 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      ((((codesRec20 0).thr - 1 : ℕ) : ENNReal) / (codesRec20 0).n) ^ 191 ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  refine ⟨positions_ud_le _ _ ?_, positions_ud_le _ _ ?_, positions_ud_le _ _ ?_,
    positions_ud_le _ _ ?_, positions_ud_le _ _ ?_⟩ <;> simp only [udThr] <;> norm_num

/-- The query groups (positions and `λ`) of `C_main` at P20. -/
theorem eQuery_main20 :
    eQueryUd (codesMain20 0) (codesMain20 1) 311 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      eQueryUd (codesMain20 1) (codesMain20 2) 191 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      eQueryUd (codesMain20 2) (codesMain20 3) 156 ≤ (2 : ENNReal)⁻¹ ^ 129 ∧
      eQueryFinal (codesMain20 3) 142 ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  refine ⟨eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_,
    eQueryFinal_ud_le _ _ ?_⟩ <;> simp only [udThr] <;> norm_num

/-- The query group of `C_rec` at P20. -/
theorem eQuery_rec20 : eQueryFinal (codesRec20 0) 191 ≤ (2 : ENNReal)⁻¹ ^ 129 :=
  eQueryFinal_ud_le _ _ (by simp only [udThr]; norm_num)

/-- **`εmax` of `C_main` at P20**: every group escape is at most `2^-129`. -/
theorem whirEps_main20 : whirEpsUd codesMain20 cfgMain20.grind cfgMain20.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨f0, f1, f2, f3, -⟩ := eFold_P20
  obtain ⟨q0, q1, q2, q3⟩ := eQuery_main20
  simp only [whirEpsUd, cfgMain20, levelEpsUd, max_le_iff, pow_zero, one_mul]
  exact ⟨⟨f0.trans (inv_two_pow_anti (by norm_num)), q0⟩,
    ⟨f1.trans (inv_two_pow_anti (by norm_num)), q1⟩,
    ⟨f2.trans (inv_two_pow_anti (by norm_num)), q2⟩,
    f3.trans (inv_two_pow_anti (by norm_num)), q3, eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

/-- **`εmax` of `C_rec` at P20.** -/
theorem whirEps_rec20 : whirEpsUd codesRec20 cfgRec20.grind cfgRec20.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨-, -, -, -, f⟩ := eFold_P20
  simp only [whirEpsUd, cfgRec20, levelEpsUd, max_le_iff, pow_zero, one_mul]
  exact ⟨f.trans (inv_two_pow_anti (by norm_num)), eQuery_rec20,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

/-- **The levels' arithmetic of `C_main` at P20.** -/
theorem ladderArith_main20 :
    LadderArithUd cfgMain20.μ cfgMain20.per codesMain20 0 0 cfgMain20.levels := by
  obtain ⟨q0, q1, q2, q3⟩ := eQuery_main20
  have h := inv_two_pow_lt_one (c := 129) (by norm_num)
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgMain20, codesMain20], le_rfl, rfl, rfl, q1.trans_lt h, by norm_num [cfgMain20, codesMain20], le_rfl,
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain20, codesMain20], le_rfl, rfl, rfl, q3.trans_lt h, by norm_num [cfgMain20, codesMain20]⟩

/-- **The levels' arithmetic of `C_rec` at P20.** -/
theorem ladderArith_rec20 :
    LadderArithUd cfgRec20.μ cfgRec20.per codesRec20 0 0 cfgRec20.levels :=
  ⟨rfl, rfl, eQuery_rec20.trans_lt (inv_two_pow_lt_one (by norm_num)),
    by norm_num [cfgRec20, codesRec20]⟩

/-! ## P8: the test set, `2^-20` -/

/-- **`εmax` of `C_main` at P8**: every group escape is at most `2^-20`. -/
theorem whirEps_main8 : whirEpsUd codesMain8 cfgMain8.grind cfgMain8.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgMain8, levelEpsUd, max_le_iff, pow_zero, one_mul]
  refine ⟨⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩, ⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩,
    ⟨eFold_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_⟩, eFold_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;>
    norm_num

/-- **`εmax` of `C_rec` at P8.** -/
theorem whirEps_rec8 : whirEpsUd codesRec8 cfgRec8.grind cfgRec8.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgRec8, levelEpsUd, max_le_iff, pow_zero, one_mul]
  refine ⟨eFold_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;> simp only [udMca, mcaUd, udThr] <;>
    norm_num

/-- The query groups of P8 (for the arithmetic). -/
theorem eQuery_P8 :
    eQueryUd (codesMain8 0) (codesMain8 1) 49 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryUd (codesMain8 1) (codesMain8 2) 30 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryUd (codesMain8 2) (codesMain8 3) 25 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryFinal (codesMain8 3) 22 ≤ (2 : ENNReal)⁻¹ ^ 20 ∧
      eQueryFinal (codesRec8 0) 30 ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  refine ⟨eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_,
    eQueryFinal_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_⟩ <;> simp only [udThr] <;> norm_num

/-- **The levels' arithmetic of `C_main` at P8.** -/
theorem ladderArith_main8 :
    LadderArithUd cfgMain8.μ cfgMain8.per codesMain8 0 0 cfgMain8.levels := by
  obtain ⟨q0, q1, q2, q3, -⟩ := eQuery_P8
  have h := inv_two_pow_lt_one (c := 20) (by norm_num)
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgMain8, codesMain8], le_rfl, rfl, rfl, q1.trans_lt h, by norm_num [cfgMain8, codesMain8], le_rfl,
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain8, codesMain8], le_rfl, rfl, rfl, q3.trans_lt h, by norm_num [cfgMain8, codesMain8]⟩

/-- **The levels' arithmetic of `C_rec` at P8.** -/
theorem ladderArith_rec8 :
    LadderArithUd cfgRec8.μ cfgRec8.per codesRec8 0 0 cfgRec8.levels :=
  ⟨rfl, rfl, eQuery_P8.2.2.2.2.trans_lt (inv_two_pow_lt_one (by norm_num)),
    by norm_num [cfgRec8, codesRec8]⟩

/-! ## The stacked openings at lvm's parameters -/

/-- **`C_main`'s stacked opening at P20**: groups escape at most `2^-129`, the batching challenge
`(J − 1)/|E|`. -/
noncomputable def stackedMain20Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain20.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain20 claims)
      (fun h ↦ StackedPreUd cfgMain20 (codesMain20 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesMain20 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain20]) rfl (by norm_num [cfgMain20])
    (by norm_num [cfgMain20]) (by norm_num [cfgMain20]) ladderArith_main20 whirEps_main20 T

/-- **`C_rec`'s stacked opening at P20.** -/
noncomputable def stackedRec20Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec20 claims)
      (fun h ↦ StackedPreUd cfgRec20 (codesRec20 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesRec20 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec20]) rfl (by norm_num [cfgRec20])
    (by norm_num [cfgRec20]) (by norm_num [cfgRec20]) ladderArith_rec20 whirEps_rec20 T

/-- **`C_main`'s stacked opening at P8.** -/
noncomputable def stackedMain8Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain8.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain8 claims)
      (fun h ↦ StackedPreUd cfgMain8 (codesMain8 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesMain8 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain8]) rfl (by norm_num [cfgMain8])
    (by norm_num [cfgMain8]) (by norm_num [cfgMain8]) ladderArith_main8 whirEps_main8 T

/-- **`C_rec`'s stacked opening at P8.** -/
noncomputable def stackedRec8Spec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec8.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec8 claims)
      (fun h ↦ StackedPreUd cfgRec8 (codesRec8 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec8 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec8]) rfl (by norm_num [cfgRec8])
    (by norm_num [cfgRec8]) (by norm_num [cfgRec8]) ladderArith_rec8 whirEps_rec8 T

/-- The batching challenge at the roots: at most `2^-129` for `J ≤ 2^63` claims. -/
theorem eBatch_P20 (J : ℕ) (hJ : J ≤ 2 ^ 63) :
    eBatch J (codesMain20 0) ≤ (2 : ENNReal)⁻¹ ^ 129 ∧ eBatch J (codesRec20 0) ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  have h : (J - 1) * 2 ^ 129 ≤ 2 ^ 192 :=
    (Nat.mul_le_mul_right _ ((Nat.sub_le J 1).trans hJ)).trans (by norm_num)
  exact ⟨eBatch_ud_le _ _ h, eBatch_ud_le _ _ h⟩

end
end LeanVM.Protocol.Whir.Sound
