-- New for lvm2 (WP JB-L): the specification of the WHIR opening with out-of-domain samples (Johnson regime), ported
-- from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean` (formal rev 0b850750) onto
-- LvmWhirLevelMidSpec/LvmWhirSpec (PI-GRIND). Changed against leanVM: the opening is `verifyWhirJ cfg` with
-- `cfg.ood = true` (levels from the configuration, positions `per` per challenge, the root `c₀` of `n₀`
-- commitments, the proof of work of `cfg.grind` bits), the precondition is lvm's `WhirPreUd`/`StackedPreUd`, and
-- the ladder carries the positions' width. `anyT`, `LevelPreL`, `eBatch` and the batching lemmas are reused from
-- `LvmWhirSpec`.
/-
  LeanVM.Protocol.Whir.Sound.SpecJ

  The round-by-round soundness of lvm's WHIR opening with out-of-domain samples as a
  specification of the verifier program, with the explicit escape bound `whirEpsJ`.
-/

import LvmWhirMidJ
import LvmWhirSpec

/-!
# The specification of the WHIR opening (Johnson regime)

For an opening `cfg : WhirConfig` with `cfg.ood = true` and a code `codes i` per level
(`LevelCode`: `κ_i`, `R_i`, threshold `A_i`, list bound `L_i`, MCA count `E_i`):

* `LadderArithJ`: the arithmetic of the levels, the positions' width `per·(κ_i + R_i) ≤ 192`, and
  the joint groups' escapes below `1`: `eOod (codes (i+1)) κ_i < 1` and
  `eQuery (codes i) (codes (i+1)) t_i < 1` at a level with a next one (no list bound),
  `eQueryFinal` at the final level;
* `levelEpsJ codes g i levels`, `whirEpsJ codes g levels`: the largest group escape, **the `εmax`
  of the opening**:

  `max_i max( (2·L_i + 2^(ℓ_i−1)·E_i)/|E|,  C(L_{i+1}, 2)·κ_i/|E|,
             2^-g·(((A_i − 1)/n_i)^{t_i} + (t_i + 1)·L_{i+1}/|E|) )`
  over the levels with a next level, and for the final level `levelEpsUd`'s
  `max( (2·L + 2^(ℓ−1)·E)/|E|, 2^-g·(((A − 1)/n)^t + t/|E|), 2/|E| )`;
* `levelsSpecJ`: the levels from `LevelPre` of the first (`midSpecJ`, and `finSpec` through
  `whirLevelsJ_one` at the final level), returning never in doom;
* `whirSpecJ`: **`verifyWhirJ cfg t w` from `WhirPreUd`**, lead `0`;
* `stackedSpecJ`: **`verifyStackedJ cfg claims` from `StackedPreUd`**, with the batching
  challenge's escape `eBatch J P₀ = (J − 1)·L₀/|E|` as lead (`card_batch_bad_le`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd Finset

section

/-! ## The levels' arithmetic and escapes -/

section Ladder

variable (μ per : ℕ) (codes : ℕ → LevelCode)

/-- The arithmetic of the levels, the positions' width and the joint groups' escapes below `1`. -/
def LadderArithJ : ℕ → ℕ → List Whir.Level → Prop
  | _, _, [] => True
  | i, pre, [level] => (codes i).κ + pre + level.fold = μ ∧ (codes i).R = level.logInvRate ∧
      eQueryFinal (codes i) level.queries < 1 ∧ per * ((codes i).κ + (codes i).R) ≤ 192
  | i, pre, level :: next :: rest => (codes i).κ + pre + level.fold = μ ∧
      (codes i).R = level.logInvRate ∧ eOod (codes (i + 1)) (codes i).κ < 1 ∧
      eQuery (codes i) (codes (i + 1)) level.queries < 1 ∧
      per * ((codes i).κ + (codes i).R) ≤ 192 ∧
      LadderArithJ (i + 1) (pre + level.fold) (next :: rest)

end Ladder

section Eps

variable (codes : ℕ → LevelCode) (g : ℕ)

/-- **The largest group escape** of the levels from level `i` (Johnson regime), the query groups
discounted by the proof of work of `g` bits. -/
noncomputable def levelEpsJ : ℕ → List Whir.Level → ENNReal
  | _, [] => 0
  | i, [level] => max (eFold (codes i) level.fold)
      (max ((2 : ENNReal)⁻¹ ^ g * eQueryFinal (codes i) level.queries) eTail)
  | i, level :: next :: rest => max (max (eFold (codes i) level.fold)
      (eOod (codes (i + 1)) (codes i).κ)) (max ((2 : ENNReal)⁻¹ ^ g *
        eQuery (codes i) (codes (i + 1)) level.queries) (levelEpsJ (i + 1) (next :: rest)))

/-- **The `εmax` of the WHIR opening with OOD samples.** -/
noncomputable def whirEpsJ (levels : List Whir.Level) : ENNReal := levelEpsJ codes g 0 levels

end Eps

/-! ## The levels -/

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {codes : ℕ → LevelCode} {εmax : ENNReal}

/-- **The levels' specification** (Johnson regime). -/
noncomputable def levelsSpecJ (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (hc : c₀ < n₀)
    (hper : 1 ≤ per) (hg : g ≤ 192) :
    (levels : List Whir.Level) → (i pre : ℕ) → LadderArithJ μ per codes i pre levels →
      levelEpsJ codes g i levels ≤ εmax → (s : WhirStateT) →
      Spec (whirLevelsJ μ ℓ₀ per c₀ n₀ g dir w i levels s)
        (fun h ↦ LevelPreL μ codes ℓ₀ w i pre levels s (viewC c₀ n₀ (commits h)))
        (fun _ _ ↦ False) εmax εmax 0
  | [], i, pre, _, _, s => (Spec.fail (Pre := fun h ↦ LevelPreL μ codes ℓ₀ w i pre [] s
        (viewC c₀ n₀ (commits h))) (Post := fun _ _ ↦ False)).mono (fun _ h ↦ h)
        (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | [level], i, pre, hA, hε, s =>
    (finSpec ⟨hw, hℓ₀, hA.1, hA.2.1, hc, hper, hA.2.2.2⟩ hg ((le_max_left _ _).trans hε)
      hA.2.2.1 ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_right _ _).trans hε)) s).congr
      (whirLevelsJ_one μ ℓ₀ per c₀ n₀ g dir w i level s).symm
  | level :: next :: rest, i, pre, hA, hε, s =>
    midSpecJ ⟨hw, hℓ₀, hA.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.1, hA.2.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.2.1, hc, hper, hA.2.2.2.2.1⟩ hg
      ((le_max_left _ _).trans ((le_max_left _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_left _ _).trans hε)) hA.2.2.1 hA.2.2.2.1
      ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      (fun s' ↦ levelsSpecJ hw hℓ₀ hc hper hg (next :: rest) (i + 1) (pre + level.fold)
        hA.2.2.2.2.2 ((le_max_right _ _).trans ((le_max_right _ _).trans hε)) s') s

/-! ## The opening -/

/-- `verifyWhirJ` with OOD on a configuration with levels: the first round polynomial, then the
levels. -/
theorem verifyWhirJ_eq {cfg : WhirConfig} {t : E} {level : Whir.Level} {rest : List Whir.Level}
    (hood : cfg.ood = true) (hc : cfg.levels = level :: rest) :
    verifyWhirJ cfg t w = (sumcheckRoundPoly 3 t none).bind fun quad ↦
      whirLevelsJ cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ cfg.grind cfg.direct w 0 (level :: rest)
        ⟨t, quad, [], []⟩ := by
  rw [verifyWhirJ, hood, hc]
  rfl

/-- **The specification of the WHIR opening with out-of-domain samples.** From `WhirPreUd` (the
history has the `n₀` commitments the opening starts with, its root `c₀` is shaped as level `0`,
and every candidate of the root's word violates `(w, t)`), the opening's groups escape with
probability at most `εmax ≥ whirEpsJ codes cfg.grind cfg.levels` each, and it never returns in
doom. -/
noncomputable def whirSpecJ {cfg : WhirConfig} {t : E} {level : Whir.Level}
    {rest : List Whir.Level} (hood : cfg.ood = true) (hc : cfg.levels = level :: rest)
    (hℓ : level.fold = laneBits) (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits)
    (hcn : cfg.c₀ < cfg.n₀) (hper : 1 ≤ cfg.per) (hg : cfg.grind ≤ 192)
    (hw : IsMultiaffine cfg.μ w) (hA : LadderArithJ cfg.μ cfg.per codes 0 0 (level :: rest))
    (hε : whirEpsJ codes cfg.grind (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyWhirJ cfg t w) (fun h ↦ WhirPreUd cfg.toUdConfig (codes 0) w t (commits h))
      (fun _ _ ↦ False) εmax 0 T :=
  anyT (Spec.congr (p' := verifyWhirJ cfg t w) (by rw [verifyWhirJ_eq hood hc, hℓ]; rfl)
    ((roundPolyInv (WhirPreUd cfg.toUdConfig (codes 0) w t) t (T := εmax) le_rfl).bind' fun quad ↦
      (levelsSpecJ (ℓ₀ := laneBits) hw hμ hcn hper hg (level :: rest) 0 0 hA hε
          ⟨t, quad, [], []⟩).mono
        (fun h hp ↦ by
          show LevelPre cfg.μ laneBits w 0 (codes 0) level.fold 0 _ _
          rw [hℓ]
          exact levelPre_zero (codes 0) hκ₀ rfl hμ w t quad _ (whirPre_of_ud hp.2) hp.1)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)) T

/-! ## The stacked opening -/

/-- `verifyStackedJ`: the batching challenge, then the opening. -/
theorem verifyStackedJ_eq (cfg : WhirConfig) (claims : List StackClaim) :
    verifyStackedJ cfg claims = VerifierProgram.sampleChallenge.bind fun ρ ↦
      verifyWhirJ cfg (dot (powers ρ claims.length) (claims.map (·.2)))
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point)) := rfl

open Classical in
/-- **The specification of the stacked opening with out-of-domain samples.** From `StackedPreUd`
(every candidate of the root violates one of the `J` claims), the batching challenge escapes with
probability at most `eBatch J P₀ = (J − 1)·L₀/|E|` and the opening (`whirSpecJ`) follows. -/
noncomputable def stackedSpecJ {cfg : WhirConfig} {level : Whir.Level} {rest : List Whir.Level}
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfg.μ c.1)
    (hood : cfg.ood = true) (hc : cfg.levels = level :: rest) (hℓ : level.fold = laneBits)
    (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits) (hcn : cfg.c₀ < cfg.n₀)
    (hper : 1 ≤ cfg.per) (hg : cfg.grind ≤ 192)
    (hA : LadderArithJ cfg.μ cfg.per codes 0 0 (level :: rest))
    (hε : whirEpsJ codes cfg.grind (level :: rest) ≤ εmax) (T : ENNReal) :
    Spec (verifyStackedJ cfg claims)
      (fun h ↦ StackedPreUd cfg.toUdConfig (codes 0) claims (commits h)) (fun _ _ ↦ False) εmax
      (eBatch claims.length (codes 0)) T :=
  by
  have S0 : Spec VerifierProgram.sampleChallenge (fun h ↦ StackedPreUd cfg.toUdConfig (codes 0)
      claims (commits h))
      (fun ρ h ↦ WhirPreUd cfg.toUdConfig (codes 0)
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
        (dot (powers ρ claims.length) (claims.map (·.2))) (commits h)) εmax
      (eBatch claims.length (codes 0) + 0) 0 :=
    Spec.sampleE (eBatch claims.length (codes 0)) fun h₀ hp ↦ by
      have hb := card_batch_bad_le (codes 0) hκ₀ rfl hμ claims _ hp.2.2.2
      rw [eBatch, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((Finset.card_le_card fun ρ hρ ↦ ?_).trans
        (hb.trans (le_of_eq (mul_comm _ _)))))
      rw [Finset.mem_filter] at hρ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hρ2 := hρ.2
      simp only [commits_sample] at hρ2
      by_contra hno
      exact hρ2 ⟨hp.1, hp.2.1, hp.2.2.1, fun q hq hh ↦ hno ⟨q, hq, hh⟩⟩
  have F0 := fun ρ : E ↦
    whirSpecJ (w := fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
      (t := dot (powers ρ claims.length) (claims.map (·.2))) hood hc hℓ hμ hκ₀ hcn hper hg
      (isMultiaffine_batched claims hcl ρ) hA hε 0
  have S1 := Spec.bind S0 F0
  exact anyT (Spec.congr (p' := verifyStackedJ cfg claims)
    (verifyStackedJ_eq cfg claims).symm
    (S1.mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl)) T

end
end LeanVM.Protocol.Whir.Sound
