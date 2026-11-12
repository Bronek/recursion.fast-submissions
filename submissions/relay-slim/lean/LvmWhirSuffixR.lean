-- New for lvm2 (WP JB-L, J2): the opening after the residual, from the residual's doom: the second half of
-- `stackedPrefixSpecR` (LvmWhirSpecR), as `LvmCertSRes` uses `finQuerySpec` for unique decoding.
/-
  LeanVM.Protocol.Whir.Sound (lvm2: the relativised opening after the residual)
-/

import LvmWhirSpecR

/-!
# After the residual

`verifyStackedJ_eq_prefix` splits the opening at the final residual into `stackPrefixJ` and
`stackSuffixJ`. `stackedPrefixSpecR` ends in `PostR`: the residual is good (`GoodRes`: the extractor's
case) or the residual's doom `ResC` holds. This module closes the second case:

* `finInfo_index`, `finInfo_snd_fst`, `finInfo_snd_snd`: `finInfo`'s final index, fold count before
  it and fold count are the last level's (`levels.length − 1 + i`, `pre + Σ` of the others, its
  `fold`), the form `PostR`'s `ResC` and `finQuerySpec`'s `FinHyp` use;
* `finSuffixSpecR`: from `ResC` the suffix (`finSuffixJ`: proof of work, query group, glue, tail,
  terminal check) rejects but with probability `2^-g·eQueryFinal` at the query group and `eTail`
  per tail round (`grindPreInv`, then WP-7's `finQuerySpec`); post `False`;
* `finSuffixRec20JSpec`: at J2's `C_rec` (`cfgRec20J`, final level `(3, 3, 77)`, code `codeJ10R3`).

So an accepting run of J2's `C_rec` opening is, but for these escapes and `stackedPrefixSpecR`'s,
in `GoodRes` at the residual: it ends in a fold of a good candidate.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd VerifierProgram Finset

section

/-- The final level's fold count. -/
theorem finInfo_snd_snd : ∀ (i pre : ℕ) (levels : List Whir.Level) (hne : levels ≠ []),
    (finInfo i pre levels).2.2 = (levels.getLast hne).fold
  | _, _, [], hne => absurd rfl hne
  | _, _, [_], _ => rfl
  | i, pre, level :: next :: rest, _ => by
    rw [finInfo, finInfo_snd_snd (i + 1) (pre + level.fold) (next :: rest) (List.cons_ne_nil _ _),
      List.getLast_cons (List.cons_ne_nil _ _)]

/-- The final level's index. -/
theorem finInfo_index : ∀ (i pre : ℕ) (levels : List Whir.Level),
    (finInfo i pre levels).1 = i + (levels.length - 1)
  | _, _, [] => rfl
  | _, _, [_] => rfl
  | i, pre, level :: next :: rest => by
    rw [finInfo, finInfo_index (i + 1) (pre + level.fold) (next :: rest)]
    simp only [List.length_cons]
    omega

/-- The fold challenges before the final level. -/
theorem finInfo_snd_fst : ∀ (i pre : ℕ) (levels : List Whir.Level),
    (finInfo i pre levels).2.1 = pre + ((levels.dropLast).map (·.fold)).sum
  | _, _, [] => by simp [finInfo]
  | _, _, [_] => by simp [finInfo]
  | i, pre, level :: next :: rest => by
    rw [finInfo, finInfo_snd_fst (i + 1) (pre + level.fold) (next :: rest)]
    simp only [List.dropLast_cons_cons, List.map_cons, List.sum_cons]
    omega

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P : LevelCode}
  {level : Whir.Level} {pre : ℕ} {εmax : ENNReal}

/-- **The opening after the residual, from the residual's doom**: the proof of work, the query
group (escape `2^-g·eQueryFinal`), the glue, the tail (`eTail` per round) and the terminal check;
it never returns in doom. -/
noncomputable def finSuffixSpecR (H : FinHyp μ ℓ₀ per c₀ n₀ w P level pre) (hg : g ≤ 192)
    (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries ≤ εmax) (hεT : eTail ≤ εmax)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ μ ℓ₀ per c₀ n₀ g dir w i level a)
      (fun h ↦ ResC μ ℓ₀ w i P level.fold pre a.1 a.2 (viewC c₀ n₀ (commits h)))
      (fun _ _ ↦ False) εmax ((2 : ENNReal)⁻¹ ^ g * eQueryFinal P level.queries) 0 :=
  Spec.congr (p := (grindPre g).bind fun _ ↦
      (queryFragG g per (μ - a.1.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦ finFinish μ ℓ₀ dir w i level a.1 a.2 gg.1 gg.2.1 gg.2.2)
    (by
      simp only [finSuffixJ]
      congr 1
      funext _
      exact (query_bindG' per g (cidx c₀ n₀ i) _ _ _).symm)
    ((grindPreInv (fun cs ↦ ResC μ ℓ₀ w i P level.fold pre a.1 a.2 (viewC c₀ n₀ cs)) g hεQ).bind
      fun _ ↦ finQuerySpec H hg hQlt hεT a.1 a.2)

/-- **J2's `C_rec` after the residual** (final level `(3, 3, 77)`, index `1`, code `codeJ10R3`, `6`
fold challenges before it): from `ResC`, rejection but for `2^-14·eQueryFinal` and `eTail`, at
`εmax = 2^-128`. -/
noncomputable def finSuffixRec20JSpec (w : List E → E) (hw : IsMultiaffine 19 w)
    (a : (WhirStateT × List E) × List E) :
    Spec (finSuffixJ 19 laneBits 8 1 2 14 false w 1 ⟨3, 3, 77⟩ a)
      (fun h ↦ ResC 19 laneBits w 1 codeJ10R3 3 6 a.1 a.2 (viewC 1 2 (commits h)))
      (fun _ _ ↦ False) ((2 : ENNReal)⁻¹ ^ 128) ((2 : ENNReal)⁻¹ ^ 14 * eQueryFinal codeJ10R3 77) 0 :=
  finSuffixSpecR (level := ⟨3, 3, 77⟩) ⟨hw, by norm_num, by norm_num [codeJ10R3], rfl, by norm_num,
      by norm_num, by norm_num [codeJ10R3]⟩ (by norm_num)
    (eQuery_J7.2.2.1.trans_lt seven_inv_lt_one)
    ((disc7 eQuery_J7.2.2.1).trans (le_self_add.trans_eq seven_add_one))
    (eTail_le.trans (inv_two_pow_anti (by norm_num))) a

end
end LeanVM.Protocol.Whir.Sound
