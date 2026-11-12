-- New for lvm2 (WP J2P-L, roll 5): J2′, Johnson on `C_rec` with X-REC2's two-level shape (SYN2 §3.1):
-- levels (ℓ, R, t) = (6, 2, 115), (4, 3, 77), final 2^9, `g = 14`, one OOD sample after level 0; the P8 twin.
-- Constants from JB-L's J2P model (JB-DES's `jcode_jb`; slack the least with fold numerator
-- `≤ 2^62` at level 0, `η = 1/n` at level 1 and at P8), checked here exactly.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: J2′ parameters)
-/

import LvmWhirSuffixR
import LvmWhirParamsJ8

/-!
# J2′: `C_rec` at the Johnson radius on X-REC2's shape

| opening | `μ` | levels `(ℓ, R, t)` | codes `(κ, R, A, L)` | `g` |
|---|---|---|---|---|
| `cfgRec20Jp` (P20) | 19 | (6,2,115) (4,3,77) | `codeJ13R2p` (13,2,16410,304), `codeJ9R3` (9,3,1451,311) | 14 |
| `cfgRec18Jp` (P8) | 18 | (6,2,17) (4,3,11) | `codeJ12R2` (12,2,8195,1024), `codeJ8R3` (8,3,727,153) | 4 |

Query counts re-derived with exact fractions at these `n` [exact]: P20 groups after the discount
`2^-128.75` (level 0, OOD next list `L' = 311`) and `2^-129.36` (final), folds `2^-130.0`, `2^-134.5`, OOD
`2^-172.7`; so `whirEps + 2^-131 ≤ 2^-128` (`whirEps_rec20Jp`). P8: `≤ 2^-20`.

`stackedPrefixRec20JpSpec` and `finSuffixRec20JpSpec` are JB-L's relativised prefix spec and the suffix from
`ResC` at this configuration; `candidates_rec20Jp_ncard_le`: at most `304` root candidates (`L₀(rec)`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd JBAgreement JB.CodingTheory.InterleavedJohnson

set_option exponentiation.threshold 512

section

/-! ## The codes -/

/-- `C_rec` level 0 of J2′ (P20): `κ = 13`, `R = 2`, `η = 216187/2^30`. -/
noncomputable def codeJ13R2p : LevelCode where
  κ := 13
  R := 2
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 16410
  listMax := 304
  mcaMax := 144114095172611933
  facts := codeFacts_johnson (domain _ _ _) (216187 / 2 ^ 30) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_rec` level 0 of J2′ at P8: `κ = 12`, `R = 2`, `η = 1/2^14`. -/
noncomputable def codeJ12R2 : LevelCode where
  κ := 12
  R := 2
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 8195
  listMax := 1024
  mcaMax := 2593599402341678809
  facts := codeFacts_johnson (domain _ _ _) (1 / 2 ^ 14) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_rec` level 1 of J2′ at P8: `κ = 8`, `R = 3`, `η = 1/2^11`. -/
noncomputable def codeJ8R3 : LevelCode where
  κ := 8
  R := 3
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 727
  listMax := 153
  mcaMax := 1620249964965508
  facts := codeFacts_johnson (domain _ _ _) (1 / 2 ^ 11) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- The codes of J2′'s `C_rec` (P20): level 0 `codeJ13R2p`, level 1 `codeJ9R3` (`LvmWhirParamsJ8`). -/
noncomputable def codesRec20Jp : ℕ → LevelCode
  | 0 => codeJ13R2p
  | _ => codeJ9R3

/-- The codes of J2′'s `C_rec` at P8. -/
noncomputable def codesRec18Jp : ℕ → LevelCode
  | 0 => codeJ12R2
  | _ => codeJ8R3

/-- **J2′'s `C_rec` (P20)**: `(6,2,115) (4,3,77)`, `g = 14`, OOD; root `1` of `2`. -/
def cfgRec20Jp : WhirConfig := ⟨⟨19, [⟨6, 2, 115⟩, ⟨4, 3, 77⟩], 8, 1, 2, false, 14⟩, true⟩

/-- **J2′'s `C_rec` at P8**: `(6,2,17) (4,3,11)`, `g = 4`, OOD; root `1` of `2`. -/
def cfgRec18Jp : WhirConfig := ⟨⟨18, [⟨6, 2, 17⟩, ⟨4, 3, 11⟩], 8, 1, 2, false, 4⟩, true⟩

/-! ## The escapes -/

/-- The groups of J2′ (P20) before the discount: folds `≤ 2^-130`, OOD `≤ 2^-170`, queries within
`7·2^-117`. -/
theorem eps_rec20Jp : eFold codeJ13R2p 6 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧
    eFold codeJ9R3 4 ≤ (2 : ENNReal)⁻¹ ^ 130 ∧ eOod codeJ9R3 13 ≤ (2 : ENNReal)⁻¹ ^ 170 ∧
    eQuery codeJ13R2p codeJ9R3 115 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 ∧
    eQueryFinal codeJ9R3 77 ≤ 7 * (2 : ENNReal)⁻¹ ^ 117 := by
  refine ⟨eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_, eOod_le_of _ _ _ ?_,
    eQuery_le_mul_of _ _ _ _ _ ?_, eQueryFinal_le_mul_of _ _ _ _ ?_⟩ <;>
    norm_num [codeJ13R2p, codeJ9R3, LevelCode.n, Nat.choose_two_right]

/-- **`εmax` of J2′'s `C_rec`** (P20): every group within `7·2^-131`, so `+ 2^-131 ≤ 2^-128`. -/
theorem whirEps_rec20Jp :
    whirEpsJ codesRec20Jp cfgRec20Jp.grind cfgRec20Jp.levels + (2 : ENNReal)⁻¹ ^ 131 ≤
      (2 : ENNReal)⁻¹ ^ 128 := by
  obtain ⟨f0, f1, o0, q0, q1⟩ := eps_rec20Jp
  refine add_margin_le ?_
  simp only [whirEpsJ, cfgRec20Jp, levelEpsJ, max_le_iff]
  exact ⟨⟨le_seven_of (by norm_num) f0, le_seven_of (by norm_num) o0⟩, disc7 q0,
    le_seven_of (by norm_num) f1, disc7 q1, le_seven_of (by norm_num) eTail_le⟩

theorem ladderArith_rec20Jp :
    LadderArithJ cfgRec20Jp.μ cfgRec20Jp.per codesRec20Jp 0 0 cfgRec20Jp.levels := by
  obtain ⟨-, -, o0, q0, q1⟩ := eps_rec20Jp
  exact ⟨rfl, rfl, o0.trans_lt (inv_two_pow_lt_one (by norm_num)), q0.trans_lt seven_inv_lt_one,
    by norm_num [cfgRec20Jp, codesRec20Jp, codeJ13R2p],
    rfl, rfl, q1.trans_lt seven_inv_lt_one, by norm_num [cfgRec20Jp, codesRec20Jp, codeJ9R3]⟩

/-- The groups of J2′ at P8 before the discount: folds and OOD `≤ 2^-21`, queries `≤ 2^-16`. -/
theorem eps_rec18Jp : eFold codeJ12R2 6 ≤ (2 : ENNReal)⁻¹ ^ 21 ∧
    eFold codeJ8R3 4 ≤ (2 : ENNReal)⁻¹ ^ 21 ∧ eOod codeJ8R3 12 ≤ (2 : ENNReal)⁻¹ ^ 21 ∧
    eQuery codeJ12R2 codeJ8R3 17 ≤ (2 : ENNReal)⁻¹ ^ 16 ∧
    eQueryFinal codeJ8R3 11 ≤ (2 : ENNReal)⁻¹ ^ 16 := by
  refine ⟨eFold_le_of _ _ _ ?_, eFold_le_of _ _ _ ?_, eOod_le_of _ _ _ ?_,
    eQuery_le_of _ _ _ _ ?_, eQueryFinal_le_of _ _ _ ?_⟩ <;>
    norm_num [codeJ12R2, codeJ8R3, LevelCode.n, Nat.choose_two_right]

/-- **`εmax` of J2′'s `C_rec` at P8.** -/
theorem whirEps_rec18Jp :
    whirEpsJ codesRec18Jp cfgRec18Jp.grind cfgRec18Jp.levels ≤ (2 : ENNReal)⁻¹ ^ 20 := by
  obtain ⟨f0, f1, o0, q0, q1⟩ := eps_rec18Jp
  have a : ∀ {x : ENNReal}, x ≤ (2 : ENNReal)⁻¹ ^ 21 → x ≤ (2 : ENNReal)⁻¹ ^ 20 :=
    fun h ↦ h.trans (inv_two_pow_anti (by norm_num))
  simp only [whirEpsJ, cfgRec18Jp, levelEpsJ, max_le_iff]
  exact ⟨⟨a f0, a o0⟩, disc_le 4 q0, a f1, disc_le 4 q1,
    eTail_le.trans (inv_two_pow_anti (by norm_num))⟩

theorem ladderArith_rec18Jp :
    LadderArithJ cfgRec18Jp.μ cfgRec18Jp.per codesRec18Jp 0 0 cfgRec18Jp.levels := by
  obtain ⟨-, -, o0, q0, q1⟩ := eps_rec18Jp
  have h := inv_two_pow_lt_one (c := 16) (by norm_num)
  exact ⟨rfl, rfl, o0.trans_lt (inv_two_pow_lt_one (by norm_num)), q0.trans_lt h,
    by norm_num [cfgRec18Jp, codesRec18Jp, codeJ12R2],
    rfl, rfl, q1.trans_lt h, by norm_num [cfgRec18Jp, codesRec18Jp, codeJ8R3]⟩

/-! ## The specifications -/

/-- **J2′'s `C_rec` opening up to the residual, relativised** (P20), `εmax = 2^-128`; post `PostR`
(`GoodRes ∨ ResC`); the follower's allowance is the final query group's `2^-14·eQueryFinal`. -/
noncomputable def stackedPrefixRec20JpSpec (Good : Column cfgRec20Jp.μ → Prop)
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20Jp.μ c.1) :
    Spec (stackPrefixJ cfgRec20Jp claims)
      (fun h ↦ StackedPreR cfgRec20Jp.toUdConfig (codesRec20Jp 0) Good claims (commits h))
      (fun x h ↦ PostR cfgRec20Jp.μ laneBits
        (fun point ↦ dot (powers x.1 claims.length) (claims.map fun c ↦ c.1 point)) codesRec20Jp
        cfgRec20Jp.c₀ cfgRec20Jp.n₀ 0 0 cfgRec20Jp.levels
        (gdRoot (codesRec20Jp 0) Good (viewC cfgRec20Jp.c₀ cfgRec20Jp.n₀ (commits h))) x.2 h)
      ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesRec20Jp 0))
      ((2 : ENNReal)⁻¹ ^ 14 * eQueryFinal (codesRec20Jp 1) 77) :=
  stackedPrefixSpecR Good claims hcl rfl rfl (by norm_num [cfgRec20Jp]) rfl
    (by norm_num [cfgRec20Jp]) (by norm_num [cfgRec20Jp]) (by norm_num [cfgRec20Jp])
    ladderArith_rec20Jp (le_of_add_margin whirEps_rec20Jp)

/-- **J2′'s `C_rec` after the residual** (P20; final level `(4, 3, 77)`, index `1`, code `codeJ9R3`,
`6` fold challenges before it): from `ResC`, rejection but for `2^-14·eQueryFinal` and `eTail`. -/
noncomputable def finSuffixRec20JpSpec (w : List E → E) (hw : IsMultiaffine 19 w)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ 19 laneBits 8 1 2 14 false w 1 ⟨4, 3, 77⟩ a)
      (fun h ↦ ResC 19 laneBits w 1 codeJ9R3 4 6 a.1 a.2 (viewC 1 2 (commits h)))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) ((2 : ENNReal)⁻¹ ^ 14 * eQueryFinal codeJ9R3 77) 0 :=
  finSuffixSpecR (level := ⟨4, 3, 77⟩) ⟨hw, by norm_num, by norm_num [codeJ9R3], rfl, by norm_num,
      by norm_num, by norm_num [codeJ9R3]⟩ (by norm_num)
    (eps_rec20Jp.2.2.2.2.trans_lt seven_inv_lt_one)
    ((disc7 eps_rec20Jp.2.2.2.2).trans (le_self_add.trans_eq seven_add_one))
    (eTail_le.trans (inv_two_pow_anti (by norm_num))) a

/-- **J2′'s `C_rec` at P8, up to the residual**, `εmax = 2^-20`. -/
noncomputable def stackedPrefixRec18JpSpec (Good : Column cfgRec18Jp.μ → Prop)
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec18Jp.μ c.1) :
    Spec (stackPrefixJ cfgRec18Jp claims)
      (fun h ↦ StackedPreR cfgRec18Jp.toUdConfig (codesRec18Jp 0) Good claims (commits h))
      (fun x h ↦ PostR cfgRec18Jp.μ laneBits
        (fun point ↦ dot (powers x.1 claims.length) (claims.map fun c ↦ c.1 point)) codesRec18Jp
        cfgRec18Jp.c₀ cfgRec18Jp.n₀ 0 0 cfgRec18Jp.levels
        (gdRoot (codesRec18Jp 0) Good (viewC cfgRec18Jp.c₀ cfgRec18Jp.n₀ (commits h))) x.2 h)
      ((2 : ENNReal)⁻¹ ^ 20) (eBatch claims.length (codesRec18Jp 0))
      ((2 : ENNReal)⁻¹ ^ 4 * eQueryFinal (codesRec18Jp 1) 11) :=
  stackedPrefixSpecR Good claims hcl rfl rfl (by norm_num [cfgRec18Jp]) rfl
    (by norm_num [cfgRec18Jp]) (by norm_num [cfgRec18Jp]) (by norm_num [cfgRec18Jp])
    ladderArith_rec18Jp whirEps_rec18Jp

/-- **J2′'s `C_rec` at P8 after the residual** (final level `(4, 3, 11)`, code `codeJ8R3`). -/
noncomputable def finSuffixRec18JpSpec (w : List E → E) (hw : IsMultiaffine 18 w)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ 18 laneBits 8 1 2 4 false w 1 ⟨4, 3, 11⟩ a)
      (fun h ↦ ResC 18 laneBits w 1 codeJ8R3 4 6 a.1 a.2 (viewC 1 2 (commits h)))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 20) ((2 : ENNReal)⁻¹ ^ 4 * eQueryFinal codeJ8R3 11) 0 :=
  finSuffixSpecR (level := ⟨4, 3, 11⟩) ⟨hw, by norm_num, by norm_num [codeJ8R3], rfl, by norm_num,
      by norm_num, by norm_num [codeJ8R3]⟩ (by norm_num)
    (eps_rec18Jp.2.2.2.2.trans_lt (inv_two_pow_lt_one (by norm_num)))
    (disc_le 4 eps_rec18Jp.2.2.2.2)
    (eTail_le.trans (inv_two_pow_anti (by norm_num))) a

/-! ## The candidates -/

/-- J2′'s `C_rec` root candidates (P20): at most `304`, the `C_rec` factor of `kgSpec`'s `L₀`. -/
theorem candidates_rec20Jp_ncard_le (W : Word) :
    (Candidates 19 2 (codesRec20Jp 0).thr W).ncard ≤ 304 :=
  candidates_ncard_le (codesRec20Jp 0) (by norm_num) rfl rfl W

/-- J2′'s `C_rec` root candidates at P8: at most `1024`. -/
theorem candidates_rec18Jp_ncard_le (W : Word) :
    (Candidates 18 2 (codesRec18Jp 0).thr W).ncard ≤ 1024 :=
  candidates_ncard_le (codesRec18Jp 0) (by norm_num) rfl rfl W

end
end LeanVM.Protocol.Whir.Sound
