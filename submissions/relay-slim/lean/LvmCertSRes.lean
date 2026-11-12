-- WP-14 (ASM), two-level `C_rec` for lvm2 S4 (X-REC2-CERT). The residual's doom of `P_S` (part of
-- the certificate's doom, joined to `psSpec` and `midSpec1` by `Spec.or`). It reuses WP-7's final-level query spec
-- (`finQuerySpec`, `LvmWhirLevelFinal`) from the residual's doom `ResC`, and creates that doom at the
-- residual's last scalar (`Spec.atRet`) from no doom, instead of from the fold rounds' doom.
import LvmCertSNo

/-!
# The residual's doom (lvm2 S4: the final residual of `C_rec`'s level 1)

`psSpec`'s doom is the statement's: no candidate pair of the roots is good. Outside it nothing ties
`C_rec`'s final residual `f₂` to the level-1 word, but the extractor needs `Enc₁(f₂)` in the list of
the level-1 word folded by `α₁` (`¬ FinalDoomL`, `LvmWhirDoom2`). This module adds that doom:

* `resTailSpec`: after a final level's fold rounds (state `r`), the residual is read; doom is
  created at its last scalar iff `ResC` holds; then WP-7's `finQuerySpec` rejects but with
  probability `≤ eQueryFinal`, then `eTail`.
* `stacked_two_eq`, `midTail_fin_eq`: a two-level stacked opening unfolded (batching challenge,
  round polynomial, level-0 folds, level-1 commitment, level-0 query group, query intro
  polynomial, level-1 folds, final tail).
* `recRes2Spec`: a two-level stacked opening from no doom, doom only `resTailSpec`'s at level 1.
* `resSpec`: `P_S` from no doom: roots and middle phases dead, `C_rec`'s opening by `recRes2Spec`
  (when the claims are multiaffine; else dead), `C_main`'s opening dead.
* `resSpec_D`: at the boundary after the final residual's last scalar, `ResC` (level 1) is doom.
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound
open scoped ENNReal

variable {α β : Type}

/-! ## The doom of a sequence at and after a return of its first part -/

theorem bind_D_after {p : VerifierProgram α} {f : α → VerifierProgram β} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {Q : β → List Ev → Prop} {εmax Lp Lf T : ℝ≥0∞}
    (S : Spec p Pre Post εmax Lp Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T)
    {h₀ l₁ l₂ : List Ev} {a : α} (ha : p.after l₁ = some (.ret a)) (hne : l₂ ≠ []) :
    (S.bind F).D h₀ (l₁ ++ l₂) ↔ (F a).D (h₀ ++ l₁) l₂ := by
  rw [Spec.bind_D]
  unfold Spec.bindD
  rw [retSplit_of_after p l₁ l₂ ha]
  simp [hne]

theorem bind_D_ret {p : VerifierProgram α} {f : α → VerifierProgram β} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {Q : β → List Ev → Prop} {εmax Lp Lf T : ℝ≥0∞}
    (S : Spec p Pre Post εmax Lp Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T)
    {h₀ l₁ : List Ev} {a : α} (ha : p.after l₁ = some (.ret a)) :
    (S.bind F).D h₀ l₁ ↔ S.D h₀ l₁ ∧ (F a).D (h₀ ++ l₁) [] := by
  rw [Spec.bind_D]
  unfold Spec.bindD
  have := retSplit_of_after p l₁ [] ha
  rw [List.append_nil] at this
  rw [this]
  simp

/-! ## The residual's doom after the fold rounds -/

section Tail

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {dir : Bool} {w : List E → E} {i : ℕ} {P : LevelCode}
  {level : LeanVM.Parameters.Whir.Level} {pre : ℕ} {εmax : ℝ≥0∞}

/-- The final level after its fold rounds, as the residual's read, the moves before the proof of
work (PI-GRIND; nothing at `g = 0`), then the query group with the proof of work. -/
theorem finTail_eq (r : WhirStateT × List E) :
    finTail μ ℓ₀ per c₀ n₀ g dir w i level r =
      (readScalars (2 ^ (μ - r.1.folds.length))).bind fun res ↦ (grindPre g).bind fun _ ↦
        (queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
          (cidx c₀ n₀ i)).bind fun gg ↦ finFinish μ ℓ₀ dir w i level r res gg.1 gg.2.1 gg.2.2 := by
  simp only [finTail]
  congr 1
  funext res
  congr 1
  funext _
  exact query_bindG per g (cidx c₀ n₀ i) _ _ _

/-- **After the fold rounds, from no doom**: doom is created at the residual's last scalar iff
`ResC` holds; then WP-7's query group, tail and terminal check. -/
noncomputable def resTailSpec (H : FinHyp μ ℓ₀ per c₀ n₀ w P level pre) (hg : g ≤ 192)
    (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ℝ≥0∞)⁻¹ ^ g * eQueryFinal P level.queries ≤ εmax)
    (hεT : eTail ≤ εmax) (r : WhirStateT × List E) :
    Spec (finTail μ ℓ₀ per c₀ n₀ g dir w i level r) (fun _ ↦ False) (fun _ _ ↦ False) εmax 0 0 :=
  Spec.congr (finTail_eq r).symm
    ((Spec.atRet (Post := fun res h ↦ ResC μ ℓ₀ w i P level.fold pre r res
        (viewC c₀ n₀ (commits h))) (movesOnly_readScalars _) hεQ).bind fun res ↦
      (grindPreInv (fun cs ↦ ResC μ ℓ₀ w i P level.fold pre r res (viewC c₀ n₀ cs)) g
        hεQ).bind fun _ ↦ finQuerySpec H hg hQlt hεT r res)

/-- **The residual's doom**: at the boundary after the residual's last scalar, `ResC` is doom. -/
theorem resTailSpec_D (H : FinHyp μ ℓ₀ per c₀ n₀ w P level pre) (hg : g ≤ 192)
    (hQlt : eQueryFinal P level.queries < 1)
    (hεQ : (2 : ℝ≥0∞)⁻¹ ^ g * eQueryFinal P level.queries ≤ εmax)
    (hεT : eTail ≤ εmax) (r : WhirStateT × List E) {h₀ l : List Ev} {res : List E}
    (ha : (readScalars (2 ^ (μ - r.1.folds.length))).after l = some (.ret res))
    (hR : ResC μ ℓ₀ w i P level.fold pre r res (viewC c₀ n₀ (commits (h₀ ++ l)))) :
    (resTailSpec (dir := dir) (i := i) H hg hQlt hεQ hεT r).D h₀ l := by
  rw [resTailSpec, Spec.congr_D, bind_D_ret _ _ ha]
  exact ⟨⟨res, ha, hR⟩, ((grindPreInv (fun cs ↦ ResC μ ℓ₀ w i P level.fold pre r res
    (viewC c₀ n₀ cs)) g hεQ).bind fun _ ↦ finQuerySpec (dir := dir) H hg hQlt hεT r res).start_D _ hR⟩

end Tail

/-! ## `C_rec`'s opening, from no doom -/

/-- The batched target of the claims `cl` under the batching challenge `ρ`. -/
def batT (cl : List LeanVM.Protocol.Verifier.StackClaim) (ρ : E) : E := LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers ρ cl.length) (cl.map (·.2))

/-- The batched evaluation basis of the claims `cl` under `ρ`. -/
def batW (cl : List LeanVM.Protocol.Verifier.StackClaim) (ρ : E) : List E → E :=
  fun point ↦ LeanVM.Protocol.Verifier.dot (LeanVM.Protocol.Verifier.powers ρ cl.length) (cl.map fun c ↦ c.1 point)

/-- **A two-level stacked opening, unfolded** (lvm2 S4): the batching challenge, the first round
polynomial, the level-0 fold rounds, then the rest of level 0 (`midTail`, WP-7). -/
theorem stacked_two_eq (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
    (hc : cfg.levels = [level, next]) (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    verifyStackedUd cfg cl = sampleChallenge.bind fun ρ ↦
      (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).bind fun quad ↦
        (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).bind fun r ↦
          midTail cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ cfg.grind cfg.direct (batW cl ρ) 0 level
            next [] r := by
  rw [verifyStackedUd_eq]
  congr 1
  funext ρ
  rw [verifyWhirUd_eq hc]
  rfl

/-- **The rest of a level followed by the final level, unfolded**: the next commitment, the moves
before the proof of work (S2J's `grindPre`), the query group with the proof of work, the query
intro polynomial, the final level's fold rounds, then its tail. -/
theorem midTail_fin_eq (μ ℓ₀ per c₀ n₀ g : ℕ) (dir : Bool) (w : List E → E) (i : ℕ)
    (level next : LeanVM.Parameters.Whir.Level) (r : WhirStateT × List E) :
    midTail μ ℓ₀ per c₀ n₀ g dir w i level next [] r =
      (readCommitment (μ - r.1.folds.length - next.fold + next.logInvRate)
          (3 * 2 ^ next.fold)).bind fun _ ↦ (grindPre g).bind fun _ ↦
        (queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
            (cidx c₀ n₀ i)).bind fun gg ↦
          (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf i r.2 gg.1 gg.2.1 gg.2.2) none).bind
            fun hq ↦ (foldRoundsT next.fold (glueLv μ i r gg.1 gg.2.1 gg.2.2 hq) []).bind fun r₁ ↦
              finTail μ ℓ₀ per c₀ n₀ g dir w (i + 1) next r₁ := by
  unfold midTail
  congr 1
  funext _
  congr 1
  funext _
  exact query_bindG per g (cidx c₀ n₀ i) _ _ _

section Rec2

variable (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
  (hc : cfg.levels = [level, next]) (P₁ : LevelCode) (cl : List LeanVM.Protocol.Verifier.StackClaim)
  {εmax : ℝ≥0∞}
  (H : ∀ ρ, FinHyp cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ (batW cl ρ) P₁ next level.fold)
  (hg : cfg.grind ≤ 192) (hQlt : eQueryFinal P₁ next.queries < 1)
  (hεQ : (2 : ℝ≥0∞)⁻¹ ^ cfg.grind * eQueryFinal P₁ next.queries ≤ εmax)
  (hεT : eTail ≤ εmax)

/-- **A two-level stacked opening from no doom**, doom only the final (level-1) residual's. -/
noncomputable def recRes2Spec :
    Spec (verifyStackedUd cfg cl) (fun _ ↦ False) (fun _ _ ↦ False) εmax 0 0 :=
  Spec.congr (stacked_two_eq cfg level next hc cl).symm
    ((Spec.dead (p := sampleChallenge) (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun ρ ↦
      (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun quad ↦
        (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun r ↦
          Spec.congr (midTail_fin_eq _ _ _ _ _ _ _ _ _ level next r).symm
            ((Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun _ ↦
              (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun _ ↦
                (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun gg ↦
                  (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun hq ↦
                    (Spec.dead (Post := fun _ _ ↦ False) (L := 0) (T := 0)).bind fun r₁ ↦
                      resTailSpec (dir := cfg.direct) (i := 0 + 1) (H ρ) hg hQlt hεQ hεT r₁))

/-- The doom of `recRes2Spec` after the final residual: `resTailSpec`'s. -/
theorem recRes2Spec_D {h₀ lq lf lc lgp lg lhq lf1 lres : List Ev} {ρ : E} {quad hq : List E}
    {r r₁ : WhirStateT × List E} {g : List ℕ × E × List (List K)}
    (hq' : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).after lq =
      some (.ret quad))
    (hf : (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (cfg.μ - r.1.folds.length - next.fold + next.logInvRate)
      (3 * 2 ^ next.fold)).after lc = some (.ret ()))
    (hgp : (grindPre cfg.grind).after lgp = some (.ret ()))
    (hgq : (queryFragG cfg.grind cfg.per (cfg.μ - r.1.folds.length + level.logInvRate)
      level.queries (cidx cfg.c₀ cfg.n₀ 0)).after lg = some (.ret g))
    (hh : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after
      lhq = some (.ret hq))
    (hf1 : (foldRoundsT next.fold (glueLv cfg.μ 0 r g.1 g.2.1 g.2.2 hq) []).after lf1 =
      some (.ret r₁))
    (hne : lres ≠ []) :
    (recRes2Spec cfg level next hc P₁ cl H hg hQlt hεQ hεT).D h₀
        ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lgp ++ (lg ++ (lhq ++ (lf1 ++ lres)))))))) ↔
      (resTailSpec (dir := cfg.direct) (i := 0 + 1) (H ρ) hg hQlt hεQ hεT r₁).D
        (h₀ ++ [Ev.sample ρ] ++ lq ++ lf ++ lc ++ lgp ++ lg ++ lhq ++ lf1) lres := by
  rw [recRes2Spec, Spec.congr_D, bind_D_after _ _ (rfl : sampleChallenge.after [Ev.sample ρ] = _)
    (by simp [hne]), bind_D_after _ _ hq' (by simp [hne]), bind_D_after _ _ hf (by simp [hne]),
    Spec.congr_D, bind_D_after _ _ hcm (by simp [hne]), bind_D_after _ _ hgp (by simp [hne]),
    bind_D_after _ _ hgq (by simp [hne]), bind_D_after _ _ hh (by simp [hne]),
    bind_D_after _ _ hf1 hne]

end Rec2

/-! ## Runs through a sequence -/

/-- Where `p` reaches a node that is not a return, it has not returned. -/
theorem retSplit_eq_none_of_after {p q : VerifierProgram α} {l : List Ev} (h : p.after l = some q)
    (hq : ∀ a, q ≠ .ret a) : p.retSplit l = none := by
  rcases hs : p.retSplit l with _ | ⟨a, l₁, l₂⟩
  · rfl
  · obtain ⟨rfl, h1⟩ := retSplit_eq_some_iff.1 hs
    rw [after_append, h1] at h
    cases l₂ with
    | nil => simp [after] at h; exact absurd h.symm (hq a)
    | cons e es => cases e <;> simp [after] at h

/-- Inside `p` (at a node that is not a return), the doom of `S.bind F` is `S`'s. -/
theorem bind_D_inside {p : VerifierProgram α} {f : α → VerifierProgram β} {Pre : List Ev → Prop}
    {Post : α → List Ev → Prop} {Q : β → List Ev → Prop} {εmax Lp Lf T : ℝ≥0∞}
    (S : Spec p Pre Post εmax Lp Lf) (F : ∀ a, Spec (f a) (Post a) Q εmax Lf T)
    {h₀ l : List Ev} {q : VerifierProgram α} (ha : p.after l = some q) (hq : ∀ a, q ≠ .ret a) :
    (S.bind F).D h₀ l ↔ S.D h₀ l := by
  rw [Spec.bind_D]
  exact Spec.bindD_none (retSplit_eq_none_of_after ha hq)

/-- **A return of a sequence** splits into a return of its first part and one of its second. -/
theorem after_bind_ret {p : VerifierProgram α} {f : α → VerifierProgram β} {l : List Ev} {b : β}
    (h : (p.bind f).after l = some (.ret b)) :
    ∃ a l₁ l₂, l = l₁ ++ l₂ ∧ p.after l₁ = some (.ret a) ∧ (f a).after l₂ = some (.ret b) := by
  rcases after_bind_cases f h with ⟨q, hq, he⟩ | ⟨a, l₁, l₂, rfl, h1, -, h2⟩
  · cases q with
    | ret a => exact ⟨a, l, [], by simp, hq, by simpa [after] using he.symm⟩
    | _ => simp [VerifierProgram.bind] at he
  · exact ⟨a, l₁, l₂, rfl, h1, h2⟩

/-- The positions' first challenge: a query group with at least one position (after the moves
before the proof of work, PI-GRIND) starts with a challenge. -/
theorem queryFrag_bind_ne_ret (gb per d t c : ℕ) (ht : t ≠ 0)
    (g : List ℕ × E × List (List K) → VerifierProgram Unit) (a : Unit) :
    ((grindPre gb).bind fun _ ↦ (queryFragG gb per d t c).bind g) ≠ .ret a := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
  by_cases hg : gb = 0
  · subst hg
    simp [grindPre, powCheck, queryFragG, queryFrag, samplePositions, samplePositionsAux,
      VerifierProgram.bind, VerifierProgram.sampleChallenge]
  · simp [grindPre, hg, VerifierProgram.bind, VerifierProgram.sampleChallenge]

/-- **A two-level stacked opening, after its level-1 commitment**, is before its level-0 query
group (the moves before the proof of work, then the group). -/
theorem after_stacked_two_commit (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
    (hc : cfg.levels = [level, next]) (cl : List LeanVM.Protocol.Verifier.StackClaim)
    {lq lf lc : List Ev} {ρ : E} {quad : List E} {r : WhirStateT × List E}
    (hq : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).after lq = some (.ret quad))
    (hf : (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (cfg.μ - r.1.folds.length - next.fold + next.logInvRate)
      (3 * 2 ^ next.fold)).after lc = some (.ret ())) :
    ∃ g', (verifyStackedUd cfg cl).after ([Ev.sample ρ] ++ (lq ++ (lf ++ lc))) =
      some ((grindPre cfg.grind).bind fun _ ↦
        (queryFragG cfg.grind cfg.per (cfg.μ - r.1.folds.length + level.logInvRate) level.queries
          (cidx cfg.c₀ cfg.n₀ 0)).bind g') := by
  refine ⟨fun g ↦ (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2)
    none).bind fun hq ↦ (foldRoundsT next.fold (glueLv cfg.μ 0 r g.1 g.2.1 g.2.2 hq) []).bind
      fun r₁ ↦ finTail cfg.μ level.fold cfg.per cfg.c₀ cfg.n₀ cfg.grind cfg.direct (batW cl ρ)
        (0 + 1) next r₁, ?_⟩
  rw [stacked_two_eq cfg level next hc cl,
    after_bind_append _ (rfl : sampleChallenge.after [Ev.sample ρ] = _), after_bind_append _ hq,
    after_bind_append _ hf, midTail_fin_eq, ← List.append_nil lc, after_bind_append _ hcm]
  simp [VerifierProgram.after]

/-- **A two-level stacked opening, after its final residual**, is before its level-1 query group. -/
theorem after_stacked_two_res (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
    (hc : cfg.levels = [level, next]) (cl : List LeanVM.Protocol.Verifier.StackClaim)
    {lq lf lc lgp lg lhq lf1 lres : List Ev} {ρ : E} {quad hq res : List E}
    {r r₁ : WhirStateT × List E} {g : List ℕ × E × List (List K)}
    (hq' : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl ρ) none).after lq =
      some (.ret quad))
    (hf : (foldRoundsT level.fold ⟨batT cl ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (cfg.μ - r.1.folds.length - next.fold + next.logInvRate)
      (3 * 2 ^ next.fold)).after lc = some (.ret ()))
    (hgp : (grindPre cfg.grind).after lgp = some (.ret ()))
    (hgq : (queryFragG cfg.grind cfg.per (cfg.μ - r.1.folds.length + level.logInvRate)
      level.queries (cidx cfg.c₀ cfg.n₀ 0)).after lg = some (.ret g))
    (hh : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after
      lhq = some (.ret hq))
    (hf1 : (foldRoundsT next.fold (glueLv cfg.μ 0 r g.1 g.2.1 g.2.2 hq) []).after lf1 =
      some (.ret r₁))
    (hres : (readScalars (2 ^ (cfg.μ - r₁.1.folds.length))).after lres = some (.ret res)) :
    ∃ g', (verifyStackedUd cfg cl).after
        ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lgp ++ (lg ++ (lhq ++ (lf1 ++ lres)))))))) =
      some ((grindPre cfg.grind).bind fun _ ↦
        (queryFragG cfg.grind cfg.per (cfg.μ - r₁.1.folds.length + next.logInvRate) next.queries
          (cidx cfg.c₀ cfg.n₀ (0 + 1))).bind g') := by
  refine ⟨fun g ↦ finFinish cfg.μ level.fold cfg.direct (batW cl ρ) (0 + 1) next r₁ res g.1 g.2.1
    g.2.2, ?_⟩
  rw [stacked_two_eq cfg level next hc cl,
    after_bind_append _ (rfl : sampleChallenge.after [Ev.sample ρ] = _), after_bind_append _ hq',
    after_bind_append _ hf, midTail_fin_eq, after_bind_append _ hcm, after_bind_append _ hgp,
    after_bind_append _ hgq, after_bind_append _ hh, after_bind_append _ hf1, finTail_eq,
    ← List.append_nil lres, after_bind_append _ hres]
  simp [VerifierProgram.after]

/-! ## P20: `C_rec`'s opening and `P_S` (lvm2 S4 on S2J: two levels, `g = 14`) -/

/-- `C_rec`'s level 0 at P20: fold `6`, rate `2`, `170` positions. -/
def recLevel0 : LeanVM.Parameters.Whir.Level := ⟨6, 2, 170⟩

/-- `C_rec`'s level 1 at P20: fold `4`, rate `3`, `139` positions. -/
def recLevel1 : LeanVM.Parameters.Whir.Level := ⟨4, 3, 139⟩

theorem rec20_levels : cfgRec20G.levels = [recLevel0, recLevel1] := rfl

theorem finHyp1_rec20 (cl : List LeanVM.Protocol.Verifier.StackClaim)
    (hcl : ∀ c ∈ cl, IsMultiaffine 19 c.1) (ρ : E) :
    FinHyp cfgRec20G.μ recLevel0.fold cfgRec20G.per cfgRec20G.c₀ cfgRec20G.n₀ (batW cl ρ)
      (codesRec20 1) recLevel1 recLevel0.fold :=
  ⟨isMultiaffine_batched cl hcl ρ, by decide, rfl, rfl, by decide, by decide, by decide⟩

theorem hg20 : cfgRec20G.grind ≤ 192 := by decide

theorem hQlt1_20 : eQueryFinal (codesRec20 1) recLevel1.queries < 1 :=
  eQuery_rec20G.2.trans_lt (inv_two_pow_lt_one (by norm_num))

theorem hεQ1_20 :
    (2 : ℝ≥0∞)⁻¹ ^ cfgRec20G.grind * eQueryFinal (codesRec20 1) recLevel1.queries ≤ εS :=
  (disc_le 14 eQuery_rec20G.2).trans pow129_le_εS

theorem hεT20 : eTail ≤ εS := (eTail_le.trans (inv_two_pow_anti (by norm_num))).trans pow129_le_εS

section Concrete

attribute [local irreducible] verifyStackedUd verifyStackedJ recRes2Spec resTailSpec

open Classical in
/-- **`C_rec`'s opening at P20 from no doom**, doom only the final residual's (dead when the
claims are not multiaffine). -/
noncomputable def recRes20 (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    Spec (verifyStackedUd cfgRec20G cl) (fun _ ↦ False) (fun _ _ ↦ False) εS 0 0 :=
  if hcl : ∀ c ∈ cl, IsMultiaffine 19 c.1 then
    recRes2Spec cfgRec20G recLevel0 recLevel1 rec20_levels (codesRec20 1) cl (finHyp1_rec20 cl hcl)
      hg20 hQlt1_20 hεQ1_20 hεT20
  else Spec.dead

/-- The openings from no doom, doom only `C_rec`'s final residual's. -/
noncomputable def openRes (cl : OpenClaims) :
    Spec (openProg cl) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0 :=
  (recRes20 cl.1).bind' fun _ ↦ Spec.dead

/-- **The residual's doom of `P_S`** (from no doom; lvm2: the final residual of `C_rec`'s level 1). -/
noncomputable def resSpec (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    Spec (PSWith mid x) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0 :=
  (Spec.bind' (Spec.dead (p := commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G)
      (Post := fun _ _ ↦ False) (L := 0) (T := 0)) fun _ ↦
    Spec.bind' (Spec.dead (p := mid x) (Post := fun _ _ ↦ False) (L := 0) (T := 0)) fun cl ↦
      openRes cl).congr (PSWith_eq mid x).symm

/-- **The residual's doom at the boundary after the final residual**: a run through the roots,
the middle phases, `C_rec`'s batching challenge, first round polynomial, level-0 fold rounds,
level-1 commitment, the moves before the proof of work (`hgp`), level-0 query group with the proof
of work (`hgq`), query intro polynomial, level-1 fold rounds and residual, with multiaffine claims,
is doomed there if the level-1 `ResC` holds. -/
theorem resSpec_D (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8)
    {hr lm lq lf lc lgp lg lhq lf1 lres : List Ev} {cl : OpenClaims} {ρ : E} {quad hq res : List E}
    {r r₁ : WhirStateT × List E} {g : List ℕ × E × List (List K)}
    (hroots : (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G).after hr = some (.ret ()))
    (hm : (mid x).after lm = some (.ret cl))
    (hcl : ∀ c ∈ cl.1, IsMultiaffine 19 c.1)
    (hq' : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq =
      some (.ret quad))
    (hf : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (hcm : (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).after lc = some (.ret ()))
    (hgp : (grindPre 14).after lgp = some (.ret ()))
    (hgq : (queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).after lg =
      some (.ret g))
    (hh : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after
      lhq = some (.ret hq))
    (hf1 : (foldRoundsT 4 (glueLv 19 0 r g.1 g.2.1 g.2.2 hq) []).after lf1 = some (.ret r₁))
    (hres : (readScalars (2 ^ (19 - r₁.1.folds.length))).after lres = some (.ret res))
    (hR : ResC 19 6 (batW cl.1 ρ) 1 (codesRec20 1) 4 6 r₁ res
      (viewC 1 2 (commits (hr ++ lm ++ [Ev.sample ρ] ++ lq ++ lf ++ lc ++ lgp ++ lg ++ lhq ++ lf1 ++
        lres)))) :
    (resSpec mid x).D []
      (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lgp ++ (lg ++ (lhq ++ (lf1 ++
        lres))))))))))
      := by
  have hne : lres ≠ [] := by
    intro h; subst h
    simp only [VerifierProgram.after, Option.some.injEq] at hres
    cases (Nat.two_pow_pos (19 - r₁.1.folds.length)).ne' (by
      cases h : 2 ^ (19 - r₁.1.folds.length) with
      | zero => rfl
      | succ n => rw [h] at hres; simp [readScalars, VerifierProgram.bind, readScalar] at hres)
  rw [resSpec, Spec.congr_D]
  rw [show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_after _ _ hroots (by simp)]
  rw [show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_after _ _ hm (by simp)]
  obtain ⟨g', hafter⟩ := after_stacked_two_res cfgRec20G recLevel0 recLevel1 rec20_levels cl.1 hq' hf
    hcm hgp hgq hh hf1 hres
  rw [openRes, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ hafter (queryFrag_bind_ne_ret _ _ _ _ _ (by decide) _)]
  rw [recRes20, dif_pos hcl]
  refine (recRes2Spec_D cfgRec20G recLevel0 recLevel1 rec20_levels (codesRec20 1) cl.1
    (finHyp1_rec20 cl.1 hcl) hg20 hQlt1_20 hεQ1_20 hεT20 hq' hf hcm hgp hgq hh hf1 hne).2 ?_
  refine resTailSpec_D _ _ _ _ _ r₁ hres ?_
  simp only [List.nil_append, List.append_assoc] at hR ⊢
  exact hR

end Concrete

end Lvm.ASM
