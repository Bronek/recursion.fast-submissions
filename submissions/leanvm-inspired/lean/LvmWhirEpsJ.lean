-- New for lvm2 (WP JB-L): the group escapes of the Johnson WHIR levels (JB-DES §1.2, §2.2), numerically.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: Johnson escapes)
-/

import LvmWhirParams
import LvmWhirCodeJ
import LvmWhirEscapeJ

/-!
# The escapes of the Johnson levels

Per group of a WHIR level (`LvmWhirFolds.eFold`, `LvmWhirEscapeJ.eOod`/`eQuery`,
`LvmWhirDefs.eQueryFinal`), at JB-DES's J1/J2 shapes with the codes of `LvmWhirCodeJ`, before the
proof-of-work discount `2^-g` (`g = 14` gives the query groups `≤ 7·2^-131 < 2^-128`):

| group | `C_main` (6,1,230) (4,2,115) (4,3,77) | `C_rec` (J2) (6,3,77) (3,3,77) |
|---|---|---|
| fold, per challenge | `≤ 2^-130` each | `≤ 2^-130`, `≤ 2^-131` |
| OOD point (next list) | `≤ 2^-170` each | `≤ 2^-170` |
| positions + `λ` + openings | `≤ 7·2^-117` each (exact: 2^-114.30, 2^-114.80, final 2^-115.44) | `≤ 7·2^-117` each (2^-115.07, final 2^-115.44) |

Exact values from JB-L's group model. `eFold_le_of`, `eOod_le_of`, `eQuery_le_of`,
`eQueryFinal_le_of` turn each bound into one inequality of naturals, checked by `norm_num`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir

set_option exponentiation.threshold 512

section

/-! ## From naturals -/

/-- The fold escape from its numerator: `(2L + 2^(ℓ−1) M)·2^c ≤ 2^192`. -/
theorem eFold_le_of (P : LevelCode) (ℓ c : ℕ)
    (h : (2 * P.listMax + 2 ^ (ℓ - 1) * P.mcaMax) * 2 ^ c ≤ 2 ^ 192) :
    eFold P ℓ ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eFold, card_E_ennreal, ← two_pow_cast 192]
  exact natCast_div_le_inv_pow (by positivity) h

/-- The OOD escape from its numerator: `C(L', 2)·κ·2^c ≤ 2^192`. -/
theorem eOod_le_of (P' : LevelCode) (κ c : ℕ) (h : P'.listMax.choose 2 * κ * 2 ^ c ≤ 2 ^ 192) :
    eOod P' κ ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eOod, card_E_ennreal, ← two_pow_cast 192]
  exact natCast_div_le_inv_pow (by positivity) h

/-- The query group with a next list: `((A−1)^t·2^192 + (t+1)L'·n^t)·2^c ≤ n^t·2^192`. -/
theorem eQuery_le_of (P P' : LevelCode) (t c : ℕ)
    (h : ((P.thr - 1) ^ t * 2 ^ 192 + (t + 1) * P'.listMax * P.n ^ t) * 2 ^ c ≤
      P.n ^ t * 2 ^ 192) :
    eQuery P P' t ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eQuery, card_E_ennreal, natCast_div_pow, ← two_pow_cast 192]
  exact natCast_div_add_div_le (by positivity) (by positivity) h

/-- The final query group: `((A−1)^t·2^192 + t·n^t)·2^c ≤ n^t·2^192`. -/
theorem eQueryFinal_le_of (P : LevelCode) (t c : ℕ)
    (h : ((P.thr - 1) ^ t * 2 ^ 192 + t * P.n ^ t) * 2 ^ c ≤ P.n ^ t * 2 ^ 192) :
    eQueryFinal P t ≤ (2 : ENNReal)⁻¹ ^ c := by
  rw [eQueryFinal, card_E_ennreal, natCast_div_pow, ← two_pow_cast 192]
  exact natCast_div_add_div_le (by positivity) (by positivity) h

/-! ## Up to a factor -/

/-- `N / M ≤ k·2^-c` from `N · 2^c ≤ k · M`. -/
theorem natCast_div_le_mul_inv_pow {N M c k : ℕ} (h : N * 2 ^ c ≤ k * M) :
    (N : ENNReal) / M ≤ k * (2 : ENNReal)⁻¹ ^ c := by
  apply ENNReal.div_le_of_le_mul
  rw [mul_assoc, ← ENNReal.inv_pow, ← ENNReal.div_eq_inv_mul, ← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  exact_mod_cast h

/-- `A / B + C / D = (A D + C B) / (B D)` for naturals. -/
theorem natCast_div_add_div_eq {A B C D : ℕ} (hB : 0 < B) (hD : 0 < D) :
    (A : ENNReal) / B + (C : ENNReal) / D = ((A * D + C * B : ℕ) : ENNReal) / ((B * D : ℕ) : ENNReal) := by
  have hB0 : (B : ENNReal) ≠ 0 := by exact_mod_cast hB.ne'
  have hD0 : (D : ENNReal) ≠ 0 := by exact_mod_cast hD.ne'
  have h1 : (A : ENNReal) / B = ((A * D : ℕ) : ENNReal) / ((B * D : ℕ) : ENNReal) := by
    rw [Nat.cast_mul, Nat.cast_mul]
    exact (ENNReal.mul_div_mul_right _ _ hD0 (ENNReal.natCast_ne_top D)).symm
  have h2 : (C : ENNReal) / D = ((C * B : ℕ) : ENNReal) / ((B * D : ℕ) : ENNReal) := by
    rw [Nat.cast_mul, Nat.cast_mul, mul_comm (B : ENNReal) (D : ENNReal)]
    exact (ENNReal.mul_div_mul_right _ _ hB0 (ENNReal.natCast_ne_top B)).symm
  rw [h1, h2, ENNReal.div_add_div_same, ← Nat.cast_add]

/-- The final query group, up to a factor `k`. -/
theorem eQueryFinal_le_mul_of (P : LevelCode) (t c k : ℕ)
    (h : ((P.thr - 1) ^ t * 2 ^ 192 + t * P.n ^ t) * 2 ^ c ≤ k * (P.n ^ t * 2 ^ 192)) :
    eQueryFinal P t ≤ k * (2 : ENNReal)⁻¹ ^ c := by
  rw [eQueryFinal, card_E_ennreal, natCast_div_pow, ← two_pow_cast 192]
  exact (natCast_div_add_div_eq (by positivity) (by positivity)).trans_le
    (natCast_div_le_mul_inv_pow h)

/-- The discount turns `7·2^-117` into `7·2^-131`. -/
theorem disc7 {x : ENNReal} (h : x ≤ 7 * (2 : ENNReal)⁻¹ ^ 117) :
    (2 : ENNReal)⁻¹ ^ 14 * x ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 :=
  calc (2 : ENNReal)⁻¹ ^ 14 * x ≤ (2 : ENNReal)⁻¹ ^ 14 * (7 * (2 : ENNReal)⁻¹ ^ 117) := by gcongr
    _ = 7 * (2 : ENNReal)⁻¹ ^ 131 := by rw [show (131 : ℕ) = 14 + 117 by rfl, pow_add]; ring

/-- The query group with a next list, up to a factor `k`. -/
theorem eQuery_le_mul_of (P P' : LevelCode) (t c k : ℕ)
    (h : ((P.thr - 1) ^ t * 2 ^ 192 + (t + 1) * P'.listMax * P.n ^ t) * 2 ^ c ≤
      k * (P.n ^ t * 2 ^ 192)) :
    eQuery P P' t ≤ k * (2 : ENNReal)⁻¹ ^ c := by
  rw [eQuery, card_E_ennreal, natCast_div_pow, ← two_pow_cast 192]
  exact (natCast_div_add_div_eq (by positivity) (by positivity)).trans_le
    (natCast_div_le_mul_inv_pow h)

/-- `8·2^-(n+3) = 2^-n`. -/
theorem eight_mul_inv_pow (n : ℕ) : 8 * (2 : ENNReal)⁻¹ ^ (n + 3) = (2 : ENNReal)⁻¹ ^ n := by
  have h8 : (2 : ENNReal) ^ 3 * (2 : ENNReal)⁻¹ ^ 3 = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  rw [pow_add, show (8 : ENNReal) = 2 ^ 3 by norm_num, mul_comm, mul_assoc,
    mul_comm ((2 : ENNReal)⁻¹ ^ 3), h8, mul_one]

/-- `7·2^-131 + 2^-131 = 2^-128`. -/
theorem seven_add_one : 7 * (2 : ENNReal)⁻¹ ^ 131 + (2 : ENNReal)⁻¹ ^ 131 = (2 : ENNReal)⁻¹ ^ 128 := by
  rw [← eight_mul_inv_pow 128, show (8 : ENNReal) = 7 + 1 by norm_num, add_mul, one_mul]

/-- `7·2^-117 < 1`. -/
theorem seven_inv_lt_one : 7 * (2 : ENNReal)⁻¹ ^ 117 < 1 :=
  calc 7 * (2 : ENNReal)⁻¹ ^ 117 ≤ 8 * (2 : ENNReal)⁻¹ ^ (114 + 3) := by gcongr; norm_num
    _ = (2 : ENNReal)⁻¹ ^ 114 := eight_mul_inv_pow 114
    _ < 1 := inv_two_pow_lt_one (by norm_num)

/-! ## The Johnson levels -/

/-- **The fold escapes** of the Johnson levels. -/
theorem eFold_J : eFold codeJ18R1 6 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧
    eFold codeJ14R2 4 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧ eFold codeJ10R3 4 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧
    eFold codeJ13R3 6 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧ eFold codeJ10R3 3 ≤ (2 : ENNReal)⁻¹ ^ 131 := by
  refine ⟨eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_,
    eFold_le_of _ _ _ ?_⟩ <;> norm_num [codeJ18R1, codeJ14R2, codeJ10R3, codeJ13R3]

/-- **The OOD escapes**: the point after `C_main` levels 0 and 1 (`κ = 18, 14`; next lists
`L' = 390, 646`) and after `C_rec` level 0 (`κ = 13`, `L' = 646`). -/
theorem eOod_J : eOod codeJ14R2 18 ≤ (2 : ENNReal)⁻¹ ^ 170 ∧
    eOod codeJ10R3 14 ≤ (2 : ENNReal)⁻¹ ^ 170 ∧ eOod codeJ10R3 13 ≤ (2 : ENNReal)⁻¹ ^ 170 := by
  refine ⟨eOod_le_of _ _ _ ?_, eOod_le_of _ _ _ ?_, eOod_le_of _ _ _ ?_⟩ <;>
    norm_num [codeJ14R2, codeJ10R3, Nat.choose_two_right]

/-- **The query groups**, before the discount, all within `7·2^-117` (`2^-114.19`; exact: `C_main`
2^-114.30, 2^-114.80, final 2^-115.44; `C_rec` (J2) 2^-115.07, final as `C_main`'s). -/
theorem eQuery_J7 : eQuery codeJ18R1 codeJ14R2 230 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQuery codeJ14R2 codeJ10R3 115 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQueryFinal codeJ10R3 77 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQuery codeJ13R3 codeJ10R3 77 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 := by
  refine ⟨eQuery_le_mul_of _ _ _ _ _ ?_, eQuery_le_mul_of _ _ _ _ _ ?_,
    eQueryFinal_le_mul_of _ _ _ _ ?_, eQuery_le_mul_of _ _ _ _ _ ?_⟩ <;>
    norm_num [codeJ18R1, codeJ14R2, codeJ10R3, codeJ13R3, LevelCode.n]

end
end LeanVM.Protocol.Whir.Sound
