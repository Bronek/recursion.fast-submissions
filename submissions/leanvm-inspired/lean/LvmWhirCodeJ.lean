-- New for lvm2 (WP JB-L): WHIR level codes at the Johnson radius (JB-DES §1.2, J1/J2 levels), from
-- `LvmMcaJohnson.codeFacts_johnson`. Constants from JB-DES's model (`jcode_jb`:
-- the smallest slack `η = e/2^30` with fold numerator `2L + 2^(ℓ−1)·M ≤ 2^62`).
import LvmWhirCode
import LvmMcaJohnson

/-!
# Johnson level codes

| code | `κ`, `R`, `n` | slack `η` | threshold `A` | list `L` | MCA count `M` |
|---|---|---|---|---|---|
| `codeJ18R1` (`C_main` level 0) | 18, 1, 2^19 | 401595/2^30 | 371512 | 98 | 144115061680871682 |
| `codeJ14R2` (`C_main` level 1) | 14, 2, 2^16 | 85809/2^29 | 32809 | 390 | 576458108990386070 |
| `codeJ10R3` (`C_main` level 2, `C_rec` level 1) | 10, 3, 2^13 | 1/2^13 | 2899 | 646 | 414094616521326733 |
| `codeJ13R3` (`C_rec` level 0, J2) | 13, 3, 2^16 | 185939/2^29 | 23261 | 231 | 144115057437445356 |

`A = ⌈√((k−1) n)⌉ + ⌈4 η n⌉`, `L = listBound n (n − k + 1) (n − A)`, `M = ⌈johnsonThreshold k n (n − A) η⌉`
(`k = 2^κ`). Each `facts` field is `codeFacts_johnson` with its hypotheses checked by `norm_num`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir JBAgreement JB.CodingTheory.InterleavedJohnson

/-- `C_main` level 0 at the Johnson radius: `κ = 18`, `R = 1`. -/
noncomputable def codeJ18R1 : LevelCode where
  κ := 18
  R := 1
  h64 := by norm_num
  hκ := by norm_num
  hR := le_rfl
  thr := 371512
  listMax := 98
  mcaMax := 144115061680871682
  facts := codeFacts_johnson (domain _ _ _) (401595 / 2 ^ 30) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_main` level 1 at the Johnson radius: `κ = 14`, `R = 2`. -/
noncomputable def codeJ14R2 : LevelCode where
  κ := 14
  R := 2
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 32809
  listMax := 390
  mcaMax := 576458108990386070
  facts := codeFacts_johnson (domain _ _ _) (85809 / 2 ^ 29) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_main` level 2 and `C_rec` level 1 at the Johnson radius: `κ = 10`, `R = 3`. -/
noncomputable def codeJ10R3 : LevelCode where
  κ := 10
  R := 3
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 2899
  listMax := 646
  mcaMax := 414094616521326733
  facts := codeFacts_johnson (domain _ _ _) (1 / 2 ^ 13) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- `C_rec` level 0 at the Johnson radius (J2): `κ = 13`, `R = 3`. -/
noncomputable def codeJ13R3 : LevelCode where
  κ := 13
  R := 3
  h64 := by norm_num
  hκ := by norm_num
  hR := by norm_num
  thr := 23261
  listMax := 231
  mcaMax := 144115057437445356
  facts := codeFacts_johnson (domain _ _ _) (185939 / 2 ^ 29) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by unfold johnsonThreshold; norm_num) (by norm_num [denominator])
    (by norm_num [listBound, denominator])

/-- The codes of `C_main`'s Johnson levels `(6,1) (4,2) (4,3)` (ν = 24). -/
noncomputable def codesMain24J : ℕ → LevelCode
  | 0 => codeJ18R1
  | 1 => codeJ14R2
  | _ => codeJ10R3

/-- The codes of `C_rec`'s Johnson levels `(6,3) (3,3)` (J2, P20; `μ = 19`). -/
noncomputable def codesRec20J : ℕ → LevelCode
  | 0 => codeJ13R3
  | _ => codeJ10R3

end LeanVM.Protocol.Whir.Sound
