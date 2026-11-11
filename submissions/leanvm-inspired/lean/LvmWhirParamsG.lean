-- New for lvm2 (WP PI-GRIND): S2's WHIR openings with in-answer grinding, the query counts lowered by the
-- discount `2^-g` (PI-OPT R4: g = 14 on every position group at P20; g = 4 on the P8 test set).
/-
  LeanVM.Protocol.Whir.Sound (lvm2 S2 parameters with grinding)

  The configurations `cfgMain24G`, `cfgRec20G` (P20, g = 14) and `cfgMain23G`, `cfgRec18G` (P8,
  g = 4), the escape bounds `whirEpsUd ≤ 2^-129` (P20) and `≤ 2^-20` (P8), the arithmetic and
  the stacked-opening specifications. The codes are `LvmWhirParams24`'s and v1's: grinding changes
  only the query counts.
-/

import LvmWhirParams24

/-!
# S2's WHIR parameters with grinding

| opening | `μ` | levels `(ℓ, R, t)` | `g` | root `c₀` of `n₀` |
|---|---|---|---|---|
| `cfgMain24G` (`C_main`, P20) | 24 | (6,1,278) (4,2,170) (4,3,139) | 14 | 0 of 2 |
| `cfgRec20G` (`C_rec`, P20) | 19 | (6,2,170) | 14 | 1 of 2 |
| `cfgMain23G` (`C_main`, P8) | 23 | (6,1,39) (4,2,24) (4,3,20) | 4 | 0 of 2 |
| `cfgRec18G` (`C_rec`, P8) | 18 | (6,2,24) | 4 | 1 of 2 |

`t = udQueries (sec − g) R` (`sec = 129` at P20, `20` at P8). The query groups (positions and `λ`)
escape with at most `2^-(sec − g)` before the discount (`eQuery_main24G`, …), so at most `2^-sec`
after it (`disc_le`). The folds and the tail are unchanged.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

set_option exponentiation.threshold 512

section

/-- The discount turns a `2^-c` escape into `2^-(g + c)`. -/
theorem disc_le {x : ENNReal} {c : ℕ} (g : ℕ) (h : x ≤ (2 : ENNReal)⁻¹ ^ c) :
    (2 : ENNReal)⁻¹ ^ g * x ≤ (2 : ENNReal)⁻¹ ^ (g + c) := by
  rw [pow_add]; gcongr

/-! ## The configurations -/

/-- `C_main` at S2 P20 with grinding: levels `(6,1,278) (4,2,170) (4,3,139)`, `g = 14`. -/
def cfgMain24G : UdConfig := ⟨24, [⟨6, 1, 278⟩, ⟨4, 2, 170⟩, ⟨4, 3, 139⟩], 8, 0, 2, false, 14⟩

/-- `C_rec` at P20 with grinding: one level `(6,2,170)`, `g = 14`. -/
def cfgRec20G : UdConfig := ⟨19, [⟨6, 2, 170⟩], 8, 1, 2, false, 14⟩

/-- `C_main` at S2 P8 with grinding: levels `(6,1,39) (4,2,24) (4,3,20)`, `g = 4`. -/
def cfgMain23G : UdConfig := ⟨23, [⟨6, 1, 39⟩, ⟨4, 2, 24⟩, ⟨4, 3, 20⟩], 8, 0, 2, false, 4⟩

/-- `C_rec` at S2 P8 with grinding: one level `(6,2,24)`, `g = 4`. -/
def cfgRec18G : UdConfig := ⟨18, [⟨6, 2, 24⟩], 8, 1, 2, false, 4⟩

/-! ## P20 -/

/-- The query groups at P20 with `g = 14`: `≤ 2^-115` before the discount. -/
theorem eQuery_main24G :
    eQueryUd (codesMain24 0) (codesMain24 1) 278 ≤ (2 : ENNReal)⁻¹ ^ 115 ∧
      eQueryUd (codesMain24 1) (codesMain24 2) 170 ≤ (2 : ENNReal)⁻¹ ^ 115 ∧
      eQueryFinal (codesMain24 2) 139 ≤ (2 : ENNReal)⁻¹ ^ 115 ∧
      eQueryFinal (codesRec20 0) 170 ≤ (2 : ENNReal)⁻¹ ^ 115 := by
  refine ⟨eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eQueryFinal_ud_le _ _ ?_⟩ <;> simp only [udThr] <;> norm_num

/-- **`εmax` of `C_main` at S2 P20 with grinding**: every group escape is at most `2^-129`. -/
theorem whirEps_main24G :
    whirEpsUd codesMain24 cfgMain24G.grind cfgMain24G.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨f0, f1, f2⟩ := eFold_main24
  obtain ⟨q0, q1, q2, -⟩ := eQuery_main24G
  simp only [whirEpsUd, cfgMain24G, levelEpsUd, max_le_iff]
  exact ⟨⟨f0.trans (inv_two_pow_anti (by norm_num)), disc_le 14 q0⟩,
    ⟨f1.trans (inv_two_pow_anti (by norm_num)), disc_le 14 q1⟩,
    f2.trans (inv_two_pow_anti (by norm_num)), disc_le 14 q2,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

/-- **`εmax` of `C_rec` at P20 with grinding.** -/
theorem whirEps_rec20G :
    whirEpsUd codesRec20 cfgRec20G.grind cfgRec20G.levels ≤ (2 : ENNReal)⁻¹ ^ 129 := by
  obtain ⟨-, -, -, -, f⟩ := eFold_P20
  simp only [whirEpsUd, cfgRec20G, levelEpsUd, max_le_iff]
  exact ⟨f.trans (inv_two_pow_anti (by norm_num)), disc_le 14 eQuery_main24G.2.2.2,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

/-- **The levels' arithmetic of `C_main` at S2 P20 with grinding.** -/
theorem ladderArith_main24G :
    LadderArithUd cfgMain24G.μ cfgMain24G.per codesMain24 0 0 cfgMain24G.levels := by
  obtain ⟨q0, q1, q2, -⟩ := eQuery_main24G
  have h := inv_two_pow_lt_one (c := 115) (by norm_num)
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgMain24G, codesMain24], le_rfl,
    rfl, rfl, q1.trans_lt h, by norm_num [cfgMain24G, codesMain24], le_rfl,
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain24G, codesMain24]⟩

/-- **The levels' arithmetic of `C_rec` at P20 with grinding.** -/
theorem ladderArith_rec20G :
    LadderArithUd cfgRec20G.μ cfgRec20G.per codesRec20 0 0 cfgRec20G.levels :=
  ⟨rfl, rfl, eQuery_main24G.2.2.2.trans_lt (inv_two_pow_lt_one (by norm_num)),
    by norm_num [cfgRec20G, codesRec20]⟩

/-! ## P8 -/

/-- The query groups at P8 with `g = 4`: `≤ 2^-16` before the discount. -/
theorem eQuery_P8G :
    eQueryUd (codesMain23 0) (codesMain23 1) 39 ≤ (2 : ENNReal)⁻¹ ^ 16 ∧
      eQueryUd (codesMain23 1) (codesMain23 2) 24 ≤ (2 : ENNReal)⁻¹ ^ 16 ∧
      eQueryFinal (codesMain23 2) 20 ≤ (2 : ENNReal)⁻¹ ^ 16 ∧
      eQueryFinal (codesRec18 0) 24 ≤ (2 : ENNReal)⁻¹ ^ 16 := by
  refine ⟨eQueryUd_ud_le _ _ ?_, eQueryUd_ud_le _ _ ?_, eQueryFinal_ud_le _ _ ?_,
    eQueryFinal_ud_le _ _ ?_⟩ <;> simp only [udThr] <;> norm_num

/-- **`εmax` of `C_main` at S2 P8 with grinding**: every group escape is at most `2^-20`. -/
theorem whirEps_main23G :
    whirEpsUd codesMain23 cfgMain23G.grind cfgMain23G.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  obtain ⟨q0, q1, q2, -⟩ := eQuery_P8G
  simp only [whirEpsUd, cfgMain23G, levelEpsUd, max_le_iff]
  refine ⟨⟨eFold_ud_le _ _ ?_, disc_le 4 q0⟩, ⟨eFold_ud_le _ _ ?_, disc_le 4 q1⟩,
    eFold_ud_le _ _ ?_, disc_le 4 q2, eTail_le.trans (inv_two_pow_anti (by norm_num))⟩ <;>
    simp only [udMca, mcaUd, udThr] <;> norm_num

/-- **`εmax` of `C_rec` at S2 P8 with grinding.** -/
theorem whirEps_rec18G :
    whirEpsUd codesRec18 cfgRec18G.grind cfgRec18G.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  simp only [whirEpsUd, cfgRec18G, levelEpsUd, max_le_iff]
  refine ⟨eFold_ud_le _ _ ?_, disc_le 4 eQuery_P8G.2.2.2,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩
  simp only [udMca, mcaUd, udThr]; norm_num

/-- **The levels' arithmetic of `C_main` at S2 P8 with grinding.** -/
theorem ladderArith_main23G :
    LadderArithUd cfgMain23G.μ cfgMain23G.per codesMain23 0 0 cfgMain23G.levels := by
  obtain ⟨q0, q1, q2, -⟩ := eQuery_P8G
  have h := inv_two_pow_lt_one (c := 16) (by norm_num)
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgMain23G, codesMain23], le_rfl,
    rfl, rfl, q1.trans_lt h, by norm_num [cfgMain23G, codesMain23], le_rfl,
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain23G, codesMain23]⟩

/-- **The levels' arithmetic of `C_rec` at S2 P8 with grinding.** -/
theorem ladderArith_rec18G :
    LadderArithUd cfgRec18G.μ cfgRec18G.per codesRec18 0 0 cfgRec18G.levels :=
  ⟨rfl, rfl, eQuery_P8G.2.2.2.trans_lt (inv_two_pow_lt_one (by norm_num)),
    by norm_num [cfgRec18G, codesRec18]⟩

/-! ## The stacked openings -/

/-- **`C_main`'s stacked opening at S2 P20 with grinding**: groups escape at most `2^-129`. -/
noncomputable def stackedMain24GSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain24G.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain24G claims)
      (fun h ↦ StackedPreUd cfgMain24G (codesMain24 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesMain24 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain24G]) rfl (by norm_num [cfgMain24G])
    (by norm_num [cfgMain24G]) (by norm_num [cfgMain24G]) ladderArith_main24G whirEps_main24G T

/-- **`C_rec`'s stacked opening at P20 with grinding.** -/
noncomputable def stackedRec20GSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20G.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec20G claims)
      (fun h ↦ StackedPreUd cfgRec20G (codesRec20 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 129) (eBatch claims.length (codesRec20 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec20G]) rfl (by norm_num [cfgRec20G])
    (by norm_num [cfgRec20G]) (by norm_num [cfgRec20G]) ladderArith_rec20G whirEps_rec20G T

/-- **`C_main`'s stacked opening at S2 P8 with grinding.** -/
noncomputable def stackedMain23GSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgMain23G.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgMain23G claims)
      (fun h ↦ StackedPreUd cfgMain23G (codesMain23 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesMain23 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgMain23G]) rfl (by norm_num [cfgMain23G])
    (by norm_num [cfgMain23G]) (by norm_num [cfgMain23G]) ladderArith_main23G whirEps_main23G T

/-- **`C_rec`'s stacked opening at S2 P8 with grinding.** -/
noncomputable def stackedRec18GSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec18G.μ c.1) (T : ENNReal) :
    Spec (verifyStackedUd cfgRec18G claims)
      (fun h ↦ StackedPreUd cfgRec18G (codesRec18 0) claims (commits h)) (fun _ _ ↦ False)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec18 0)) T :=
  stackedUdSpec claims hcl rfl rfl (by norm_num [cfgRec18G]) rfl (by norm_num [cfgRec18G])
    (by norm_num [cfgRec18G]) (by norm_num [cfgRec18G]) ladderArith_rec18G whirEps_rec18G T

end
end LeanVM.Protocol.Whir.Sound
