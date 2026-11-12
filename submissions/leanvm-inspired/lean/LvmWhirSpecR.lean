-- New for lvm2 (WP JB-L, J2): the specification of the WHIR opening with OOD samples, cut at the final residual,
-- under the relativised doom: the twin of `LvmWhirSpecJ` (itself ported from leanVM
-- `formal/lean_vm/LeanVM/Protocol/Whir/Sound/Spec.lean`, formal rev 0b850750) on `LvmWhirPrefixJ`'s prefix, with
-- `LvmWhirLevelFinal.finTailSpec`'s residual read at the end. Changed against `LvmWhirSpecJ`: the doom is `ViolR`
-- for the good root set (`gdRoot`), the precondition is `StackedPreR`, and the post is `PostR`.
/-
  LeanVM.Protocol.Whir.Sound.SpecR
-/

import LvmWhirMidR
import LvmWhirParamsJ

/-!
# The opening up to the residual, relativised

For an opening `cfg : WhirConfig` and a code `codes i` per level, with `Good` the statement's good
candidates of the root:

* `finPrefixSpecR`: the final level's fold rounds (`foldRoundsSpecR`), then the residual read
  (`readNInvSucc`) with `GoodRes ∨ ResC` (`goodRes_or_resC`) at its return.
* `levelsSpecR`: the levels from `LevelPreR` of the first for a good set `Gd`, post
  `s.folds <+: a.folds ∧ PostR … Gd`; a level with a next one by `midSpecR`, the next levels for
  `gdNext` at the next level's start (`nextSpecR`: the start view's good set is the end view's,
  `gdNext_stable`).
* `stackedPrefixSpecR`: **`stackPrefixJ cfg claims` from `StackedPreR`** (every candidate of the
  root that is not good violates one of the claims): the batching challenge escapes with
  probability at most `eBatch J P₀` (`card_batch_bad_le_R`), the groups after it at most
  `εmax ≥ whirEpsJ`, and a return in doom has `PostR` for the good root set **on the end
  history's view** (`gdRoot … (viewC c₀ n₀ (commits h))`, the same set as at the start:
  `gdRoot_stable`); the follower's allowance is the final query group's escape
  `finLeadJ = 2^-g·eQueryFinal(P_final, t_final)`, which `finTailSpec`'s residual read leads with.
* `stackedPrefixRec20JSpec`: the instance at J2's `C_rec` (`cfgRec20J`, `codesRec20J`),
  `εmax = 2^-128`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd VerifierProgram Finset

section

/-! ## Definitions -/

/-- The relativised doom at the start of the levels from `i`. -/
def LevelPreRL (μ : ℕ) (codes : ℕ → LevelCode) (ℓ₀ : ℕ) (w : List E → E) :
    ℕ → ℕ → List Whir.Level → Set (Column μ) → WhirStateT → List (ℕ × ℕ × Word) → Prop
  | _, _, [], _, _, _ => True
  | i, pre, level :: _, Gd, s, cs => LevelPreR μ ℓ₀ w i (codes i) level.fold pre Gd s cs

/-- **The final level's query escape** `2^-g·eQueryFinal(P_final, t_final)`: the follower's lead
of the prefix (the suffix's first group). -/
noncomputable def finLeadJ (codes : ℕ → LevelCode) (g : ℕ) : ℕ → List Whir.Level → ENNReal
  | _, [] => 0
  | i, [level] => (2 : ENNReal)⁻¹ ^ g * eQueryFinal (codes i) level.queries
  | i, _ :: next :: rest => finLeadJ codes g (i + 1) (next :: rest)

theorem finLeadJ_le {codes : ℕ → LevelCode} {g : ℕ} {εmax : ENNReal} :
    ∀ (i : ℕ) (levels : List Whir.Level), levelEpsJ codes g i levels ≤ εmax →
      finLeadJ codes g i levels ≤ εmax
  | _, [], _ => zero_le
  | _, [_], h => (le_max_left _ _).trans ((le_max_right _ _).trans h)
  | i, _ :: next :: rest, h =>
    finLeadJ_le (i + 1) (next :: rest) ((le_max_right _ _).trans ((le_max_right _ _).trans h))

/-! ## The good sets do not change along the run -/

theorem wordOf_append_of_lt (cs l : List (ℕ × ℕ × Word)) {j : ℕ} (hj : j < cs.length) :
    wordOf (cs ++ l) j = wordOf cs j := by
  simp [wordOf, List.getElem?_append_left hj]

theorem viewC_ne_nil {c₀ n₀ : ℕ} {cs : List (ℕ × ℕ × Word)} (h : n₀ ≤ cs.length) :
    viewC c₀ n₀ cs ≠ [] := by
  simp [viewC, h]

/-- A later history's view extends the earlier's, once the latter is not empty. -/
theorem viewC_prefix {c₀ n₀ : ℕ} {h₁ h : List Ev} (hp : h₁ <+: h)
    (hne : viewC c₀ n₀ (commits h₁) ≠ []) :
    ∃ l, viewC c₀ n₀ (commits h) = viewC c₀ n₀ (commits h₁) ++ l := by
  obtain ⟨l, rfl⟩ := hp
  rw [commits_append, viewC_append (le_length_of_viewC hne)]
  exact ⟨_, rfl⟩

/-- **The next good set is read once its oracle is committed.** -/
theorem gdNext_stable {c₀ n₀ : ℕ} (P : LevelCode) (ℓ j : ℕ) (fs : List E) {μ : ℕ}
    (Gd : Set (Column μ)) {h₁ h : List Ev} (hp : h₁ <+: h)
    (hl : (viewC c₀ n₀ (commits h₁)).length = j + 1) :
    gdNext P ℓ j (viewC c₀ n₀ (commits h₁)) fs Gd = gdNext P ℓ j (viewC c₀ n₀ (commits h)) fs Gd := by
  obtain ⟨l, hl'⟩ := viewC_prefix hp (by intro he; rw [he] at hl; simp at hl)
  rw [hl']
  have hlane : laneO j (viewC c₀ n₀ (commits h₁) ++ l) P.n = laneO j (viewC c₀ n₀ (commits h₁)) P.n := by
    funext a v
    simp only [laneO, wordOf_append_of_lt _ l (by omega : j < (viewC c₀ n₀ (commits h₁)).length)]
  simp only [gdNext, ConsAt, hlane]

/-- **The good root set is read once the root is present.** -/
theorem gdRoot_stable {c₀ n₀ μ : ℕ} (P₀ : LevelCode) (Good : Column μ → Prop) {h₁ h : List Ev}
    (hp : h₁ <+: h) (hne : viewC c₀ n₀ (commits h₁) ≠ []) :
    gdRoot P₀ Good (viewC c₀ n₀ (commits h₁)) = gdRoot P₀ Good (viewC c₀ n₀ (commits h)) := by
  obtain ⟨l, hl'⟩ := viewC_prefix hp hne
  rw [hl']
  simp only [gdRoot, wordOf_append_of_lt _ l (List.length_pos_of_ne_nil hne)]

/-! ## The levels -/

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {w : List E → E} {codes : ℕ → LevelCode} {εmax T : ENNReal}

/-- **The next levels from the good set at their start**: a specification for every good set
gives one for `gdNext` read on the start history's view, with `PostR` for `gdNext` read on the
end history's view (the same set: `gdNext_stable`). -/
noncomputable def nextSpecR {j pre' : ℕ} {next : Whir.Level} {rest : List Whir.Level}
    {Gd : Set (Column μ)} {s' : WhirStateT} {L : ENNReal}
    (S : ∀ Gd' : Set (Column μ), Spec (whirPrefixJ μ per c₀ n₀ g j (next :: rest) s')
      (fun h ↦ LevelPreR μ ℓ₀ w j (codes j) next.fold pre' Gd' s' (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s'.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ j pre' (next :: rest) Gd' a h) εmax L T) :
    Spec (whirPrefixJ μ per c₀ n₀ g j (next :: rest) s')
      (fun h ↦ LevelPreR μ ℓ₀ w j (codes j) next.fold pre'
        (gdNext (codes j) next.fold j (viewC c₀ n₀ (commits h)) s'.folds Gd) s'
        (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s'.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ j pre' (next :: rest)
          (gdNext (codes j) next.fold j (viewC c₀ n₀ (commits h)) s'.folds Gd) a h) εmax L T :=
  (specAnchor (Q := fun h₁ a h ↦ (viewC c₀ n₀ (commits h₁)).length = j + 1 ∧
      s'.folds <+: a.1.1.folds ∧ PostR μ ℓ₀ w codes c₀ n₀ j pre' (next :: rest)
        (gdNext (codes j) next.fold j (viewC c₀ n₀ (commits h₁)) s'.folds Gd) a h) fun h₁ ↦
    specCases ((viewC c₀ n₀ (commits h₁)).length = j + 1)
      (fun hl ↦ (S (gdNext (codes j) next.fold j (viewC c₀ n₀ (commits h₁)) s'.folds Gd)).mono
        (fun h hp ↦ by obtain ⟨rfl, hp⟩ := hp; exact hp) (fun _ _ hp ↦ ⟨hl, hp⟩)
        le_rfl le_rfl le_rfl)
      (fun hl ↦ Spec.dead.mono (fun h hp ↦ by obtain ⟨rfl, hp⟩ := hp; exact hl hp.2.1)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)).mono
    (fun _ h ↦ h)
    (fun a h hp ↦ by
      obtain ⟨h₁, hpre, hl, hp⟩ := hp
      rwa [gdNext_stable _ _ _ _ _ hpre hl] at hp) le_rfl le_rfl le_rfl

/-- **The final level up to the residual**: the fold rounds (`foldRoundsSpecR`), then the
residual, after which every run is good (`GoodRes`) or in the residual's doom (`ResC`). -/
noncomputable def finPrefixSpecR {i pre : ℕ} {level : Whir.Level} (hw : IsMultiaffine μ w)
    (hℓ₀ : ℓ₀ ≤ μ) (hεF : eFold (codes i) level.fold ≤ εmax) (hT : T ≤ εmax)
    (Gd : Set (Column μ)) (s : WhirStateT) :
    Spec (whirPrefixJ μ per c₀ n₀ g i [level] s)
      (fun h ↦ LevelPreR μ ℓ₀ w i (codes i) level.fold pre Gd s (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s.folds <+: a.1.1.folds ∧ PostR μ ℓ₀ w codes c₀ n₀ i pre [level] Gd a h)
      εmax εmax T :=
  (((specRetFact (R := fun r ↦ s.folds <+: r.1.folds)
      (foldRoundsSpecR μ ℓ₀ w i (codes i) level.fold pre Gd (viewC c₀ n₀)
        (fun cs ↦ ShapeOK i (codes i) level.fold (viewC c₀ n₀ cs)) hw hℓ₀ hεF level.fold s [])
      fun ha ↦ foldRoundsT_folds_prefix _ _ _ ha).bind' fun r ↦
    specCases (s.folds <+: r.1.folds)
      (fun hr ↦ Spec.congr (p := (readScalars (2 ^ (μ - r.1.folds.length) - 1 + 1)).bind
          fun res ↦ VerifierProgram.ret (r, res))
        (by rw [Nat.sub_add_cancel Nat.one_le_two_pow])
        (((readNInvSucc (fun cs ↦ AfterFoldR μ ℓ₀ w i (codes i) level.fold pre Gd r
            (viewC c₀ n₀ cs)) (T := T) hT (2 ^ (μ - r.1.folds.length) - 1)).bind fun res ↦
          (Spec.ret (Post := fun a h ↦ s.folds <+: a.1.1.folds ∧
              PostR μ ℓ₀ w codes c₀ n₀ i pre [level] Gd a h) (εmax := εmax) (T := T)
              (r, res)).mono
            (fun _ hp ↦ ⟨hr, goodRes_or_resC hp.2
              (by rw [hp.1, Nat.sub_add_cancel Nat.one_le_two_pow])⟩)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
          (fun _ hp ↦ hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl))
      (fun hr ↦ Spec.dead.mono (fun _ hp ↦ hr hp.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirPrefixJ_one μ per c₀ n₀ g i level s).symm

/-- **The levels' specification up to the residual, relativised.** -/
noncomputable def levelsSpecR (hw : IsMultiaffine μ w) (hℓ₀ : ℓ₀ ≤ μ) (hc : c₀ < n₀)
    (hper : 1 ≤ per) (hg : g ≤ 192) (hT : T ≤ εmax) :
    (levels : List Whir.Level) → (i pre : ℕ) → LadderArithJ μ per codes i pre levels →
      levelEpsJ codes g i levels ≤ εmax → (Gd : Set (Column μ)) → (s : WhirStateT) →
      Spec (whirPrefixJ μ per c₀ n₀ g i levels s)
        (fun h ↦ LevelPreRL μ codes ℓ₀ w i pre levels Gd s (viewC c₀ n₀ (commits h)))
        (fun a h ↦ s.folds <+: a.1.1.folds ∧ PostR μ ℓ₀ w codes c₀ n₀ i pre levels Gd a h)
        εmax εmax T
  | [], i, pre, _, _, Gd, s => (Spec.fail (Pre := fun h ↦ LevelPreRL μ codes ℓ₀ w i pre [] Gd s
        (viewC c₀ n₀ (commits h)))
      (Post := fun a h ↦ s.folds <+: a.1.1.folds ∧ PostR μ ℓ₀ w codes c₀ n₀ i pre [] Gd a h)).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl zero_le le_rfl
  | [_], _, _, _, hε, Gd, s => finPrefixSpecR hw hℓ₀ ((le_max_left _ _).trans hε) hT Gd s
  | level :: next :: rest, i, pre, hA, hε, Gd, s =>
    midSpecR ⟨hw, hℓ₀, hA.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.1, hA.2.1, by
        have := hA.2.2.2.2.2
        cases rest <;> exact this.2.1, hc, hper, hA.2.2.2.2.1⟩ hg
      ((le_max_left _ _).trans ((le_max_left _ _).trans hε))
      ((le_max_right _ _).trans ((le_max_left _ _).trans hε)) hA.2.2.1 hA.2.2.2.1
      ((le_max_left _ _).trans ((le_max_right _ _).trans hε))
      (fun s' ↦ nextSpecR fun Gd' ↦ levelsSpecR hw hℓ₀ hc hper hg hT (next :: rest) (i + 1)
        (pre + level.fold) hA.2.2.2.2.2 ((le_max_right _ _).trans ((le_max_right _ _).trans hε))
        Gd' s') s

/-! ## The stacked opening -/

open Classical in
/-- **The stacked opening up to the residual, relativised.** From `StackedPreR` (every candidate
of the root that is not good violates one of the `J` claims), the batching challenge escapes with
probability at most `eBatch J P₀ = (J − 1)·L₀/|E|`, every later group at most
`εmax ≥ whirEpsJ codes g levels`, and a return in doom (the batching challenge `ρ`, the final
level's fold state and the residual) has `PostR` for the good root set: the residual is good or in
its doom `ResC`. The follower's allowance is the final query group's escape `finLeadJ`. -/
noncomputable def stackedPrefixSpecR {cfg : WhirConfig} {level : Whir.Level}
    {rest : List Whir.Level} (Good : Column cfg.μ → Prop) (claims : List StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine cfg.μ c.1) (hc : cfg.levels = level :: rest)
    (hℓ : level.fold = laneBits) (hμ : laneBits ≤ cfg.μ) (hκ₀ : (codes 0).κ = cfg.μ - laneBits)
    (hcn : cfg.c₀ < cfg.n₀) (hper : 1 ≤ cfg.per) (hg : cfg.grind ≤ 192)
    (hA : LadderArithJ cfg.μ cfg.per codes 0 0 cfg.levels)
    (hε : whirEpsJ codes cfg.grind cfg.levels ≤ εmax) :
    Spec (stackPrefixJ cfg claims)
      (fun h ↦ StackedPreR cfg.toUdConfig (codes 0) Good claims (commits h))
      (fun x h ↦ PostR cfg.μ laneBits
        (fun point ↦ dot (powers x.1 claims.length) (claims.map fun c ↦ c.1 point)) codes
        cfg.c₀ cfg.n₀ 0 0 cfg.levels (gdRoot (codes 0) Good (viewC cfg.c₀ cfg.n₀ (commits h)))
        x.2 h)
      εmax (eBatch claims.length (codes 0)) (finLeadJ codes cfg.grind 0 cfg.levels) := by
  have S0 : Spec VerifierProgram.sampleChallenge
      (fun h ↦ StackedPreR cfg.toUdConfig (codes 0) Good claims (commits h))
      (fun ρ h ↦ WhirPreR cfg.toUdConfig (codes 0) Good
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
        (dot (powers ρ claims.length) (claims.map (·.2))) (commits h)) εmax
      (eBatch claims.length (codes 0) + 0) 0 :=
    Spec.sampleE (eBatch claims.length (codes 0)) fun h₀ hp ↦ by
      have hb := card_batch_bad_le_R (codes 0) hκ₀ rfl hμ Good claims _ hp.2.2.2
      rw [eBatch, ENNReal.div_eq_inv_mul]
      refine mul_le_mul' le_rfl (Nat.cast_le.mpr ((Finset.card_le_card fun ρ hρ ↦ ?_).trans
        (hb.trans (le_of_eq (mul_comm _ _)))))
      rw [Finset.mem_filter] at hρ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have hρ2 := hρ.2
      simp only [commits_sample] at hρ2
      by_contra hno
      exact hρ2 ⟨hp.1, hp.2.1, hp.2.2.1, fun q hq hng hh ↦ hno ⟨q, hq, hng, hh⟩⟩
  have hT : finLeadJ codes cfg.grind 0 cfg.levels ≤ εmax := finLeadJ_le 0 cfg.levels hε
  have F0 := fun ρ : E ↦
    (roundPolyInv (WhirPreR cfg.toUdConfig (codes 0) Good
        (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
        (dot (powers ρ claims.length) (claims.map (·.2))))
        (dot (powers ρ claims.length) (claims.map (·.2))) (T := εmax) le_rfl).bind' fun quad ↦
      (specAnchor (Q := fun h₁ a h ↦ viewC cfg.c₀ cfg.n₀ (commits h₁) ≠ [] ∧
          (([] : List E) <+: a.1.1.folds ∧ PostR cfg.μ laneBits
            (fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point)) codes
            cfg.c₀ cfg.n₀ 0 0 cfg.levels
            (gdRoot (codes 0) Good (viewC cfg.c₀ cfg.n₀ (commits h₁))) a h)) fun h₁ ↦
        specCases (viewC cfg.c₀ cfg.n₀ (commits h₁) ≠ [])
          (fun hne ↦ (levelsSpecR (ℓ₀ := laneBits)
              (w := fun point ↦ dot (powers ρ claims.length) (claims.map fun c ↦ c.1 point))
              (isMultiaffine_batched claims hcl ρ) hμ hcn hper hg hT cfg.levels 0 0 hA hε
              (gdRoot (codes 0) Good (viewC cfg.c₀ cfg.n₀ (commits h₁)))
              ⟨dot (powers ρ claims.length) (claims.map (·.2)), quad, [], []⟩).mono
            (fun h hp ↦ by
              obtain ⟨rfl, hq, hpre⟩ := hp
              rw [hc]
              show LevelPreR cfg.μ laneBits _ 0 (codes 0) level.fold 0 _ _ _
              rw [hℓ]
              exact levelPre_zeroR (codes 0) hκ₀ hμ Good _ _ quad _ hpre hq)
            (fun _ _ hp ↦ ⟨hne, hp⟩) le_rfl le_rfl le_rfl)
          (fun hne ↦ Spec.dead.mono (fun h hp ↦ by
              obtain ⟨rfl, -, hpre⟩ := hp
              exact hne (viewC_ne_nil (le_of_eq hpre.2.1.symm)))
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl)).bind' fun a ↦
        (Spec.ret (Post := fun x h ↦ PostR cfg.μ laneBits
          (fun point ↦ dot (powers x.1 claims.length) (claims.map fun c ↦ c.1 point)) codes
          cfg.c₀ cfg.n₀ 0 0 cfg.levels (gdRoot (codes 0) Good (viewC cfg.c₀ cfg.n₀ (commits h)))
          x.2 h) (εmax := εmax) (T := finLeadJ codes cfg.grind 0 cfg.levels) (ρ, a)).mono
          (fun h hp ↦ by
            obtain ⟨h₁, hpre, hne, -, hp⟩ := hp
            rwa [gdRoot_stable _ _ hpre hne] at hp)
          (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  exact (Spec.bind S0 F0).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl

/-! ## The instance at J2's `C_rec` -/

/-- **J2's `C_rec` opening up to the residual, relativised** (`cfgRec20J`: `μ = 19`, levels
`(6, 3, 77)`, `(3, 3, 77)`, `g = 14`, root `1` of `2`), `εmax = 2^-128`; the follower's allowance is
the final level's query escape `2^-14·eQueryFinal(codesRec20J 1, 77)`. -/
noncomputable def stackedPrefixRec20JSpec (Good : Column cfgRec20J.μ → Prop)
    (claims : List StackClaim) (hcl : ∀ c ∈ claims, IsMultiaffine cfgRec20J.μ c.1) :
    Spec (stackPrefixJ cfgRec20J claims)
      (fun h ↦ StackedPreR cfgRec20J.toUdConfig (codesRec20J 0) Good claims (commits h))
      (fun x h ↦ PostR cfgRec20J.μ laneBits
        (fun point ↦ dot (powers x.1 claims.length) (claims.map fun c ↦ c.1 point)) codesRec20J
        cfgRec20J.c₀ cfgRec20J.n₀ 0 0 cfgRec20J.levels
        (gdRoot (codesRec20J 0) Good (viewC cfgRec20J.c₀ cfgRec20J.n₀ (commits h))) x.2 h)
      ((2 : ENNReal)⁻¹ ^ 128) (eBatch claims.length (codesRec20J 0))
      ((2 : ENNReal)⁻¹ ^ 14 * eQueryFinal (codesRec20J 1) 77) :=
  stackedPrefixSpecR Good claims hcl rfl rfl (by norm_num [cfgRec20J]) rfl
    (by norm_num [cfgRec20J]) (by norm_num [cfgRec20J]) (by norm_num [cfgRec20J])
    ladderArith_rec20J (le_of_add_margin whirEps_rec20J)

end
end LeanVM.Protocol.Whir.Sound
