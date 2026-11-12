-- New for lvm2 (WP JB-L): S2's WHIR openings in the Johnson regime (JB-DES §0/§1.2: J1 = `C_main` Johnson,
-- `C_rec` unique decoding; J2 = both Johnson), their escape bounds `≤ 2^-128`, the levels' arithmetic and the
-- stacked-opening specifications; the candidate count of a Johnson root.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: Johnson parameters)
-/

import LvmWhirSpecJ
import LvmWhirEpsJ
import LvmWhirParamsG

/-!
# S2's WHIR parameters at the Johnson radius

| opening | `μ` | levels `(ℓ, R, t)` | codes | `g` | OOD | root `c₀` of `n₀` |
|---|---|---|---|---|---|---|
| `cfgMain24J n₀` (`C_main`, J1 and J2) | 24 | (6,1,230) (4,2,115) (4,3,77) | `codesMain24J` | 14 | yes | 0 of `n₀` |
| `cfgRec20J` (`C_rec`, J2) | 19 | (6,3,77) (3,3,77) | `codesRec20J` | 14 | yes | 1 of 2 |
| `cfgRec20U` (`C_rec`, J1: R5's UD shape) | 19 | (6,3,138) (3,3,138) | `codesRec20U` (UD) | 14 | no | 1 of 2 |

`n₀` is the number of commitments present when `C_main`'s opening starts: 3 when `C_rec`'s
two-level opening (X-REC2) runs first and adds its level-1 commitment, 2 with a one-level `C_rec`.
The escape bounds do not depend on it.

* `whirEps_main24J`, `whirEps_rec20J`, `whirEps_rec20U`: every group escapes with at most
  `2^-128`; with a margin, `+ 2^-131 ≤ 2^-128` (the room left for the extractor's luck and the hash
  terms, JB-DES §2.2: the largest group is `C_main` level 0's query group, `2^-128.30`).
* `ladderArith_main24J`, `ladderArith_rec20J`, `ladderArith_rec20U`.
* `stackedMain24JSpec`, `stackedRec20JSpec`: the stacked openings' specifications (lead
  `eBatch J (codes 0)`, now `(J − 1)·L₀/|E|` with `L₀ = 98` for `C_main` and `231` for `C_rec`).
* `candidates_ncard_le`: the candidates of a root at a level code's threshold are at most its list
  bound (`L₀ = 98` for `C_main`, J1/J2): the front end's `candPairs.ncard ≤ L₀(main)·L₀(rec)`
  (`kgSpec`'s `L₀`) in place of `candPairs_ncard_le_one`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

set_option exponentiation.threshold 512

section

/-! ## The configurations -/

/-- `C_main` at S2 P20, Johnson: levels `(6,1,230) (4,2,115) (4,3,77)`, `g = 14`, OOD; root `0` of
`n₀` commitments. -/
def cfgMain24J (n₀ : ℕ) : WhirConfig := ⟨⟨24, [⟨6, 1, 230⟩, ⟨4, 2, 115⟩, ⟨4, 3, 77⟩], 8, 0, n₀, false, 14⟩, true⟩

/-- `C_rec` at P20, Johnson (J2): levels `(6,3,77) (3,3,77)`, `g = 14`, OOD; root `1` of `2`. -/
def cfgRec20J : WhirConfig := ⟨⟨19, [⟨6, 3, 77⟩, ⟨3, 3, 77⟩], 8, 1, 2, false, 14⟩, true⟩

/-- `C_rec` at P20, unique decoding (J1, PI-OPT R5's shape): levels `(6,3,138) (3,3,138)`,
`g = 14`, no OOD; root `1` of `2`. -/
def cfgRec20U : WhirConfig := ⟨⟨19, [⟨6, 3, 138⟩, ⟨3, 3, 138⟩], 8, 1, 2, false, 14⟩, false⟩

/-- The UD codes of `cfgRec20U`: `κ = 13, 10`, `R = 3`. -/
noncomputable def codesRec20U : ℕ → LevelCode
  | 0 => LevelCode.ud 13 3 (by norm_num) (by norm_num) (by norm_num)
  | _ => LevelCode.ud 10 3 (by norm_num) (by norm_num) (by norm_num)

/-! ## The escapes -/

/-- A group of at most `2^-129` is at most `7·2^-131`. -/
theorem le_seven_of {x : ENNReal} {c : ℕ} (hc : 129 ≤ c) (h : x ≤ (2 : ENNReal)⁻¹ ^ c) :
    x ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 := by
  have h4 : (2 : ENNReal)⁻¹ ^ 129 = 4 * (2 : ENNReal)⁻¹ ^ 131 := by
    have h2 : (2 : ENNReal) ^ 2 * (2 : ENNReal)⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    rw [show (131 : ℕ) = 129 + 2 by rfl, pow_add, ← mul_assoc, mul_comm (4 : ENNReal), mul_assoc,
      show (4 : ENNReal) = 2 ^ 2 by norm_num, h2, mul_one]
  refine h.trans ((inv_two_pow_anti hc).trans ?_)
  rw [h4]
  gcongr
  norm_num

/-- A group within `7·2^-131` leaves the margin `2^-131`. -/
theorem add_margin_le {x : ENNReal} (h : x ≤ 7 * (2 : ENNReal)⁻¹ ^ 131) :
    x + (2 : ENNReal)⁻¹ ^ 131 ≤ (2 : ENNReal)⁻¹ ^ 128 :=
  (add_le_add h le_rfl).trans_eq seven_add_one

/-- `C_main` level 0's query group: `2^-14·eQuery ≤ 7·2^-131` (it is `2^-128.30`). -/
theorem query_main0J :
    (2 : ENNReal)⁻¹ ^ 14 * eQuery codeJ18R1 codeJ14R2 230 ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 :=
  disc7 eQuery_J7.1

/-- `C_main`'s other query groups: `2^-14·eQuery ≤ 7·2^-131` (`2^-128.80`, `2^-129.44`). -/
theorem query_main12J :
    (2 : ENNReal)⁻¹ ^ 14 * eQuery codeJ14R2 codeJ10R3 115 ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 ∧
      (2 : ENNReal)⁻¹ ^ 14 * eQueryFinal codeJ10R3 77 ≤ 7 * (2 : ENNReal)⁻¹ ^ 131 :=
  ⟨disc7 eQuery_J7.2.1, disc7 eQuery_J7.2.2.1⟩

/-- **`εmax` of `C_main` at the Johnson radius** (J1, J2): every group escape is at most `2^-128`,
with `2^-131` to spare. -/
theorem whirEps_main24J (n₀ : ℕ) :
    whirEpsJ codesMain24J (cfgMain24J n₀).grind (cfgMain24J n₀).levels + (2 : ENNReal)⁻¹ ^ 131 ≤
      (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨f0, f1, f2, -, -⟩ := eFold_J
  obtain ⟨o0, o1, -⟩ := eOod_J
  obtain ⟨q1, q2⟩ := query_main12J
  refine add_margin_le ?_
  simp only [whirEpsJ, cfgMain24J, levelEpsJ, max_le_iff]
  exact ⟨⟨le_seven_of (by norm_num) f0, le_seven_of (by norm_num) o0⟩, query_main0J,
    ⟨le_seven_of (by norm_num) f1, le_seven_of (by norm_num) o1⟩, q1,
    le_seven_of (by norm_num) f2, q2,
    le_seven_of (by norm_num) eTail_le⟩

/-- **`εmax` of `C_rec` at the Johnson radius** (J2). -/
theorem whirEps_rec20J :
    whirEpsJ codesRec20J cfgRec20J.grind cfgRec20J.levels + (2 : ENNReal)⁻¹ ^ 131 ≤
      (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨-, -, -, f0, f1⟩ := eFold_J
  obtain ⟨-, -, o0⟩ := eOod_J
  obtain ⟨-, -, q1, q0⟩ := eQuery_J7
  refine add_margin_le ?_
  simp only [whirEpsJ, cfgRec20J, levelEpsJ, max_le_iff]
  exact ⟨⟨le_seven_of (by norm_num) f0, le_seven_of (by norm_num) o0⟩, disc7 q0,
    le_seven_of (by norm_num) f1, disc7 q1,
    le_seven_of (by norm_num) eTail_le⟩

/-- The escapes of `cfgRec20U` (UD): folds `≤ 2^-150`, queries `≤ 2^-114` before the discount. -/
theorem eps_rec20U : eFold (codesRec20U 0) 6 ≤ (2 : ENNReal)⁻¹ ^ 150 ∧
    eFold (codesRec20U 1) 3 ≤ (2 : ENNReal)⁻¹ ^ 150 ∧
    eQueryUd (codesRec20U 0) (codesRec20U 1) 138 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQueryFinal (codesRec20U 1) 138 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 := by
  refine ⟨eFold_ud_le _ _ ?_, eFold_ud_le _ _ ?_, ?_, eQueryFinal_le_mul_of _ _ _ _ ?_⟩
  · simp only [udMca, mcaUd, udThr]; norm_num
  · simp only [udMca, mcaUd, udThr]; norm_num
  · rw [eQueryUd, show (codesRec20U 1).listMax = 1 from rfl, mul_one, ← eQueryFinal]
    exact eQueryFinal_le_mul_of _ _ _ _ (by simp only [codesRec20U, LevelCode.ud, udThr]; norm_num)
  · simp only [codesRec20U, LevelCode.ud, udThr]; norm_num

/-- **`εmax` of `C_rec` in unique decoding** (J1, R5's shape). -/
theorem whirEps_rec20U :
    whirEpsUd codesRec20U cfgRec20U.grind cfgRec20U.levels + (2 : ENNReal)⁻¹ ^ 131 ≤
      (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨f0, f1, q0, q1⟩ := eps_rec20U
  refine add_margin_le ?_
  simp only [whirEpsUd, cfgRec20U, levelEpsUd, max_le_iff]
  exact ⟨⟨le_seven_of (by norm_num) f0, disc7 q0⟩, le_seven_of (by norm_num) f1, disc7 q1,
    le_seven_of (by norm_num) eTail_le⟩

/-- The bound without the margin. -/
theorem le_of_add_margin {x : ENNReal} (h : x + (2 : ENNReal)⁻¹ ^ 131 ≤ (2 : ENNReal)⁻¹ ^ 128) :
    x ≤ (2 : ENNReal)⁻¹ ^ 128 :=
  le_self_add.trans h

/-! ## The levels' arithmetic -/

theorem ladderArith_main24J (n₀ : ℕ) :
    LadderArithJ (cfgMain24J n₀).μ (cfgMain24J n₀).per codesMain24J 0 0 (cfgMain24J n₀).levels := by
  obtain ⟨o0, o1, -⟩ := eOod_J
  obtain ⟨q0, q1, q2, -⟩ := eQuery_J7
  have h := seven_inv_lt_one
  have ho := inv_two_pow_lt_one (c := 170) (by norm_num)
  exact ⟨rfl, rfl, o0.trans_lt ho, q0.trans_lt h, by norm_num [cfgMain24J, codesMain24J, codeJ18R1],
    rfl, rfl, o1.trans_lt ho, q1.trans_lt h, by norm_num [cfgMain24J, codesMain24J, codeJ14R2],
    rfl, rfl, q2.trans_lt h, by norm_num [cfgMain24J, codesMain24J, codeJ10R3]⟩

theorem ladderArith_rec20J :
    LadderArithJ cfgRec20J.μ cfgRec20J.per codesRec20J 0 0 cfgRec20J.levels := by
  obtain ⟨-, -, o0⟩ := eOod_J
  obtain ⟨-, -, q1, q0⟩ := eQuery_J7
  have h := seven_inv_lt_one
  exact ⟨rfl, rfl, o0.trans_lt (inv_two_pow_lt_one (by norm_num)), q0.trans_lt h,
    by norm_num [cfgRec20J, codesRec20J, codeJ13R3],
    rfl, rfl, q1.trans_lt h, by norm_num [cfgRec20J, codesRec20J, codeJ10R3]⟩

theorem ladderArith_rec20U :
    LadderArithUd cfgRec20U.μ cfgRec20U.per codesRec20U 0 0 cfgRec20U.levels := by
  obtain ⟨-, -, q0, q1⟩ := eps_rec20U
  have h := seven_inv_lt_one
  exact ⟨rfl, rfl, q0.trans_lt h, by norm_num [cfgRec20U, codesRec20U], le_rfl,
    rfl, rfl, q1.trans_lt h, by norm_num [cfgRec20U, codesRec20U]⟩

/-! ## The stacked openings -/

/-- **`C_main`'s stacked opening at the Johnson radius** (J1, J2): groups escape at most
`2^-128`. -/
noncomputable def stackedMain24JSpec (n₀ : ℕ) (hn₀ : 0 < n₀) (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine (cfgMain24J n₀).μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ (cfgMain24J n₀) claims)
      (fun h ↦ StackedPreUd (cfgMain24J n₀).toUdConfig (codesMain24J 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesMain24J 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgMain24J]) rfl hn₀ (by norm_num [cfgMain24J])
    (by norm_num [cfgMain24J]) (ladderArith_main24J n₀) (le_of_add_margin (whirEps_main24J n₀)) T

/-- **`C_rec`'s stacked opening at the Johnson radius** (J2). -/
noncomputable def stackedRec20JSpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20J.μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ cfgRec20J claims)
      (fun h ↦ StackedPreUd cfgRec20J.toUdConfig (codesRec20J 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesRec20J 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgRec20J]) rfl (by norm_num [cfgRec20J])
    (by norm_num [cfgRec20J]) (by norm_num [cfgRec20J]) ladderArith_rec20J
    (le_of_add_margin whirEps_rec20J) T

/-- **`C_rec`'s stacked opening in unique decoding** (J1). -/
noncomputable def stackedRec20USpec (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20U.μ c.1) (T : ENNReal) :
    Spec (verifyStackedJ cfgRec20U claims)
      (fun h ↦ StackedPreUd cfgRec20U.toUdConfig (codesRec20U 0) claims (commits h))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesRec20U 0)) T :=
  (stackedUdSpec (cfg := cfgRec20U.toUdConfig) (codes := codesRec20U) claims hcl rfl rfl
    (by norm_num [cfgRec20U]) rfl (by norm_num [cfgRec20U]) (by norm_num [cfgRec20U])
    (by norm_num [cfgRec20U]) ladderArith_rec20U
    (le_of_add_margin whirEps_rec20U) T).congr (verifyStackedJ_ud cfgRec20U rfl claims).symm

/-! ## The candidates of a Johnson root -/

/-- **The candidates are at most the list bound**: the candidates of `W` at a level code's
threshold inject into the code's list (`encStack`), so there are at most `listMax`. -/
theorem candidates_ncard_le {μ R : ℕ} (P : LevelCode) (hμ : laneBits ≤ μ)
    (hκ : P.κ = μ - laneBits) (hR : P.R = R) (W : Word) :
    (Candidates μ R P.thr W).ncard ≤ P.listMax := by
  rcases P with ⟨κ, R', h64, hκ1, hR1, thr, lM, mM, facts⟩
  simp only at hκ hR ⊢
  subst hκ hR
  have hle := Set.ncard_le_ncard_of_injOn (encStack μ R')
    (t := ((iList (rsCode (domain (μ - laneBits) R' h64) (2 ^ (μ - laneBits))) thr
      (laneWord μ R' W) : Finset _) : Set _))
    (fun q hq ↦ Finset.mem_coe.mpr (mem_iList_of_candidate h64 hq))
    (fun q _ q' _ h ↦ encStack_injective hμ h64 h)
  rw [Set.ncard_coe_finset] at hle
  exact hle.trans (facts.card_iList_le _ _)

/-- `C_main`'s candidates at the Johnson threshold (J1, J2): at most `98`. -/
theorem candidates_main24J_ncard_le (W : Word) :
    (Candidates 24 1 (codesMain24J 0).thr W).ncard ≤ 98 := -- layout-lint: allow (cfgMain24J's μ)
  candidates_ncard_le (codesMain24J 0) (by norm_num) rfl rfl W

/-- `C_rec`'s candidates at the Johnson threshold (J2): at most `231`. -/
theorem candidates_rec20J_ncard_le (W : Word) :
    (Candidates 19 3 (codesRec20J 0).thr W).ncard ≤ 231 :=
  candidates_ncard_le (codesRec20J 0) (by norm_num) rfl rfl W

end
end LeanVM.Protocol.Whir.Sound
