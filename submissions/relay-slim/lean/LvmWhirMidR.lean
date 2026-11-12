-- New for lvm2 (WP JB-L, J2): a WHIR level with a next commitment under the relativised doom, the twin of
-- `LvmWhirMidJ` (itself ported from leanVM `formal/lean_vm/LeanVM/Protocol/Whir/Sound/{LevelMid,LevelMidSpec}.lean`,
-- formal rev 0b850750) on the program cut at the residual (`LvmWhirPrefixJ`). Changed against `LvmWhirMidJ`: the
-- doom is `ViolR` for a good set `Gd`, the next level starts from `gdNext`, and the post is `PostR`.
/-
  LeanVM.Protocol.Whir.Sound.MidR
-/

import LvmWhirFoldsR
import LvmWhirEscapeR
import LvmWhirPrefixJ

/-!
# A level with a next commitment, relativised

`whirPrefixJ μ per c₀ n₀ g i (level :: next :: rest) s` is the fold rounds, then `midTailPJ`
(commitment, OOD point `z`, OOD answer `y` and its intro polynomial, `grindPre g`, the query group
with the proof of work, the query intro polynomial, the glue, the next levels' prefix).

* Combinators: `specRetFact` (a fact of every return of the program joins the post),
  `specCases` (a case split on a proposition of the parameters), `specAnchor` (the post may name
  the start history `h₁`, a prefix of the end history).
* Doom along the level: `AfterFoldR`, `MidCR` (the next oracle committed), `OodCR` (the next list
  is separated at `z`), `GlueCR` (every tracked member of the next list violates the glued claim);
  `levelPre_nextR` gives `LevelPreR` of the next level for `gdNext` (`tracked_gdNext_iff`).
* `midSpecR`: from `LevelPreR` of level `i` for `Gd`, the level's groups escape with probability
  at most `eFold`, `eOod`, `2^-g·eQuery` (R2's `escRet_queryFragG_le_R`), and the level hands
  `LevelPreR` of level `i + 1` for `gdNext … (view) s'.folds Gd` to the next levels' spec `K`;
  the post is `s.folds <+: a.folds ∧ PostR … i pre (level :: next :: rest) Gd a h`
  (`postR_mid`: `PostR` of the next levels for `gdNext` is `PostR` of this level).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir VerifierProgram Finset

section

/-! ## Combinators -/

section Combinators

variable {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax L T : ENNReal}

/-- **A fact of every return** of the program joins the post. -/
def specRetFact {R : α → Prop} (S : Spec p Pre Post εmax L T)
    (hR : ∀ {l : List Ev} {a : α}, p.after l = some (.ret a) → R a) :
    Spec p Pre (fun a h ↦ R a ∧ Post a h) εmax L T :=
  { S with post := fun hl ha hD ↦ ⟨hR ha, S.post hl ha hD⟩ }

open Classical in
/-- **A case split** on a proposition (of the parameters, not of the history). -/
noncomputable def specCases (c : Prop) (S₁ : c → Spec p Pre Post εmax L T)
    (S₂ : ¬ c → Spec p Pre Post εmax L T) : Spec p Pre Post εmax L T :=
  if hc : c then S₁ hc else S₂ hc

/-- **The start history in the post**: a family of specifications, one per start history `h₁`,
gives a specification whose post holds for some prefix `h₁` of the end history. -/
def specAnchor {Q : List Ev → α → List Ev → Prop}
    (S : ∀ h₁, Spec p (fun h ↦ h = h₁ ∧ Pre h) (Q h₁) εmax L T) :
    Spec p Pre (fun a h ↦ ∃ h₁, h₁ <+: h ∧ Q h₁ a h) εmax L T where
  D h₀ l := (S h₀).D h₀ l
  V h₀ l := (S h₀).V h₀ l
  le_one h₀ l := (S h₀).le_one h₀ l
  start_D h₀ hp := (S h₀).start_D h₀ ⟨rfl, hp⟩
  start_V h₀ hp := (S h₀).start_V h₀ ⟨rfl, hp⟩
  read {h₀ _ _} x hl ha hD := (S h₀).read x hl ha hD
  grind {h₀ _ _ _} hl ha hD := (S h₀).grind hl ha hD
  commit {h₀ _ _ _ _} word hl ha hw hD := (S h₀).commit word hl ha hw hD
  sample {h₀ _ _} hl ha := (S h₀).sample hl ha
  query {h₀ _ _ _ _ _} hl ha hq := (S h₀).query hl ha hq
  moveEnd {h₀ _ _} hl ha hm hD := (S h₀).moveEnd hl ha hm hD
  retEnd {h₀ _ _} hl ha hD := (S h₀).retEnd hl ha hD
  retDoom {h₀ _ _} hl ha hD := (S h₀).retDoom hl ha hD
  post {h₀ _ _} hl ha hD := ⟨h₀, List.prefix_append _ _, (S h₀).post hl ha hD⟩
  bound {h₀ _} hl hne hm hD := (S h₀).bound hl hne hm hD

end Combinators

/-! ## Doom along the level -/

section Doom

variable (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P P' : LevelCode) (ℓ ℓ' pre : ℕ)
  (Gd : Set (Column μ))

/-- After the commitment of the next oracle (`MidC` relativised). -/
def MidCR (r : WhirStateT × List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  ∃ cs₀ W', cs = cs₀ ++ [(P'.κ + P'.R, 3 * 2 ^ ℓ', W')] ∧ WellShaped (3 * 2 ^ ℓ') W' ∧
    AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs₀

/-- After the out-of-domain point: the next list is separated at `z`. -/
def OodCR (r : WhirStateT × List E) (z : List E) (cs : List (ℕ × ℕ × Word)) : Prop :=
  MidCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r cs ∧ z.length = P.κ ∧
    OodSep P' (rowsOf ℓ' (laneO (i + 1) cs P'.n)) z

/-- After the query group: every tracked member of the next list violates the glued claim. -/
def GlueCR (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E)
    (g : List ℕ × E × List (List K)) (cs : List (ℕ × ℕ × Word)) : Prop :=
  (QuadOK hy y ∧ OodCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r z cs) ∧
    ViolR P' Gd r.1.folds (rowsOf ℓ' (laneO (i + 1) cs P'.n))
      (runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []))
      (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []).target

end Doom

/-! ## Bookkeeping lemmas -/

section Lemmas

variable {μ ℓ₀ : ℕ} {w : List E → E} {i : ℕ} {P P' : LevelCode} {ℓ ℓ' pre : ℕ}
  {Gd : Set (Column μ)}

theorem afterFoldR_len {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs) : r.1.folds.length = pre + ℓ := by
  obtain ⟨⟨⟨hl, -⟩, -⟩, hr⟩ := h
  omega

theorem afterFoldR_κ {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs) : μ - r.1.folds.length = P.κ := by
  have := afterFoldR_len h
  obtain ⟨⟨⟨-, -, hκ, -⟩, -⟩, -⟩ := h
  omega

/-- The glue keeps the fold challenges. -/
theorem glueMid_folds (r : WhirStateT × List E) (z : List E) (y : E) (hy : List E) (qs : List ℕ)
    (lam : E) (words : List (List K)) (hq : List E) :
    (glueMid μ i r z y hy qs lam words hq).folds = r.1.folds := by
  rw [glueMid, glue_twoJ]

/-- After the commitment: the next oracle's word is appended. -/
theorem midCR_of_commit {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)} {W : Word}
    (next : Whir.Level) (hℓ' : next.fold = ℓ') (hP' : P'.κ + (pre + ℓ) + ℓ' = μ)
    (hR' : P'.R = next.logInvRate) (h : AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs)
    (hW : WellShaped (3 * 2 ^ next.fold) W) :
    MidCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r
      (cs ++ [(μ - r.1.folds.length - next.fold + next.logInvRate, 3 * 2 ^ next.fold, W)]) := by
  have hlen := afterFoldR_len h
  subst hℓ'
  refine ⟨cs, W, ?_, hW, h⟩
  congr 3
  omega

/-- The commitments after the next commitment, at index `i`. -/
theorem midCR_word {r : WhirStateT × List E} {cs : List (ℕ × ℕ × Word)}
    (h : MidCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r cs) :
    ∃ cs₀, cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs₀ i) ∧ wordOf cs i = wordOf cs₀ i ∧
      laneO i cs P.n = laneO i cs₀ P.n ∧ AfterFoldR μ ℓ₀ w i P ℓ pre Gd r cs₀ := by
  obtain ⟨cs₀, W', rfl, -, haf⟩ := h
  have hsh := haf.1.2
  have hi : i < cs₀.length := by rw [hsh.1]; omega
  exact ⟨cs₀, shapeOK_append hsh _, wordOf_append _ _ hi, laneO_append _ _ hi _, haf⟩

/-- **The next level's relativised doom** from the glued doom and the query intro polynomial,
for the next good set `gdNext`. -/
theorem levelPre_nextR (hP' : P'.κ + (pre + ℓ) + ℓ' = μ) (r : WhirStateT × List E) (z : List E)
    (y : E) (hy : List E) (g : List ℕ × E × List (List K)) (hq : List E)
    (cs : List (ℕ × ℕ × Word)) (hglue : GlueCR μ ℓ₀ w i P P' ℓ ℓ' pre Gd r z y hy g cs)
    (hhq : QuadOK hq (enfOf i r.2 g.1 g.2.1 g.2.2)) :
    LevelPreR μ ℓ₀ w (i + 1) P' ℓ' (pre + ℓ)
      (gdNext P' ℓ' (i + 1) cs (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq).folds Gd)
      (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq) cs := by
  obtain ⟨⟨hhy, ⟨cs₀, W', rfl, hW', haf⟩, hz, -⟩, hviol⟩ := hglue
  have hlen := afterFoldR_len haf
  have hκm := afterFoldR_κ haf
  obtain ⟨⟨⟨-, -, -, hg, hquad, -⟩, hshape⟩, -⟩ := haf
  refine ⟨⟨?_, by simp, hP', ?_, ?_, ?_⟩, ?_⟩
  · rw [glueMid, glue_twoJ]; simp [hlen]
  · intro c hc
    rw [glueMid, glue_twoJ] at hc
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rw [glueMid, glue_twoJ]
    rcases hc with hc | rfl | rfl
    · exact hg c hc
    · refine ⟨le_rfl, ?_⟩
      rw [hκm, ← hz]
      exact isMultiaffine_eqEval z
    · exact ⟨le_rfl, isMultiaffine_inducedWeight _ _ _ (length_powers _ _)⟩
  · rw [glueMid, glue_twoJ]
    exact quadOK_zipWith (quadOK_zipWith hquad hhy _) hhq _
  · have hr : runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq) =
        runW w ℓ₀ (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []) := by
      rw [glueMid_runW, glueMid_runW]
    have ht : (glueMid μ i r z y hy g.1 g.2.1 g.2.2 hq).target =
        (glueMid μ i r z y hy g.1 g.2.1 g.2.2 []).target := by
      rw [glueMid_target, glueMid_target]
    simp only [List.length_nil, Nat.sub_zero, foldsN, List.foldl_nil, hr, ht, glueMid_folds]
    intro V hV htr
    exact hviol V hV ((tracked_gdNext_iff P' ℓ' (i + 1) _ r.1.folds Gd hV).mp htr)
  · refine ⟨by simp [hshape.1], W', ?_, ?_⟩
    · rw [List.getElem?_append_right (by rw [hshape.1]), hshape.1, Nat.sub_self]
      simp [wdOf]
    · simpa [wdOf] using hW'

/-- **The post of the next levels is the post of this level**: `PostR` from level `i + 1` for
`gdNext` at the fold challenges `fs` of the level's end, `fs` a prefix of the run's. -/
theorem postR_mid {ℓ₀ c₀ n₀ : ℕ} {w : List E → E} {codes : ℕ → LevelCode} {pre : ℕ}
    {level next : Whir.Level} {rest : List Whir.Level} {fs : List E}
    (hfs : fs.length = pre + level.fold) {a : (WhirStateT × List E) × List E} {h : List Ev}
    (hpre : fs <+: a.1.1.folds)
    (hp : PostR μ ℓ₀ w codes c₀ n₀ (i + 1) (pre + level.fold) (next :: rest)
      (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) fs Gd) a h) :
    PostR μ ℓ₀ w codes c₀ n₀ i pre (level :: next :: rest) Gd a h := by
  have ht : a.1.1.folds.take (pre + level.fold) = fs := by
    rw [← hfs]; exact (List.prefix_iff_eq_take.mp hpre).symm
  simp only [PostR, finInfo, gdFinal, ht]
  exact hp

end Lemmas

/-! ## The specification -/

variable {μ ℓ₀ per c₀ n₀ g : ℕ} {w : List E → E} {codes : ℕ → LevelCode} {i : ℕ}
  {level next : Whir.Level} {rest : List Whir.Level} {pre : ℕ} {Gd : Set (Column μ)}
  {εmax T : ENNReal}

/-- The query group of a level with a next level, the query intro polynomial and the next
levels' prefix. -/
noncomputable def midQuerySpecR
    (H : MidHypJ μ ℓ₀ per c₀ n₀ w (codes i) (codes (i + 1)) level next pre) (hg : g ≤ 192)
    (hQlt : eQuery (codes i) (codes (i + 1)) level.queries < 1)
    (K : ∀ s', Spec (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s')
      (fun h ↦ LevelPreR μ ℓ₀ w (i + 1) (codes (i + 1)) next.fold (pre + level.fold)
        (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) s'
        (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s'.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ (i + 1) (pre + level.fold) (next :: rest)
          (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) a h)
      εmax εmax T)
    (r : WhirStateT × List E) (hr : r.1.folds.length = pre + level.fold) (z : List E) (y : E)
    (hy : List E) :
    Spec ((queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i)).bind fun gg ↦
          midFinishPJ μ per c₀ n₀ g i next rest r z y hy gg.1 gg.2.1 gg.2.2)
      (fun h ↦ QuadOK hy y ∧ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd
        r z (viewC c₀ n₀ (commits h)))
      (fun a h ↦ r.1.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ i pre (level :: next :: rest) Gd a h)
      εmax ((2 : ENNReal)⁻¹ ^ g * eQuery (codes i) (codes (i + 1)) level.queries) T :=
  ((Spec.ofNoMove (p := queryFragG g per (μ - r.1.folds.length + level.logInvRate) level.queries
        (cidx c₀ n₀ i))
      (Pre := fun h ↦ QuadOK hy y ∧ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold
        pre Gd r z (viewC c₀ n₀ (commits h)))
      (Post := fun gg h ↦ GlueCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd
        r z y hy gg (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_queryFragG _ _ _ _ _).noMove
      ((grind_disc_le g _).trans_lt hQlt) fun h₀ hp ↦ by
        obtain ⟨cs₀, hW, -, -, haf⟩ := midCR_word hp.2.1
        have hκm := afterFoldR_κ haf
        have hd : μ - r.1.folds.length + level.logInvRate = (codes i).κ + (codes i).R := by
          rw [hκm, H.hR]
        have hκ' : (codes i).κ = next.fold + (codes (i + 1)).κ := by
          have := H.hP; have := H.hP'; omega
        have hlf : r.2.length = level.fold := haf.2
        have hviol : ViolR (codes i) Gd r.1.folds
            (fun _ : Fin 0 → Bool ↦ fun v ↦ foldsN r.2 (laneO i cs₀ (codes i).n) 0 v)
            (runW w ℓ₀ r.1) r.1.target := by
          have := haf.1.1.2.2.2.2.2
          rwa [hlf, Nat.sub_self, rowsOf_zero] at this
        have hW' := commits_cidx H.hc hW
        rw [hd]
        refine escRet_queryFragG_le_R g hg (codes i) (codes (i + 1)) hκ' per level.queries
          (cidx c₀ n₀ i) H.hper H.hpd h₀ hW' Gd r.1.folds
          (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) (codes (i + 1)).n)) _
          (runW w ℓ₀ r.1) r.1.target z y hviol hp.2.2.2
          (fun gg cs ↦ GlueCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z y
            hy gg (viewC c₀ n₀ cs))
          fun qs lam hr' hlen hv ↦ ⟨hp, ?_⟩
        rw [glueMid_runW, glueMid_target, enfOf_eq haf.1.2 r.2 hlf qs hr' lam, hκm]
        exact hv).mono (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun gg ↦
    (roundPolyInv (fun cs ↦ GlueCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd
        r z y hy gg (viewC c₀ n₀ cs)) (enfOf i r.2 gg.1 gg.2.1 gg.2.2) (T := εmax) le_rfl).bind'
      fun hq ↦
      (K (glueMid μ i r z y hy gg.1 gg.2.1 gg.2.2 hq)).mono
        (fun h hp ↦ levelPre_nextR H.hP' r z y hy gg hq _ hp.2 hp.1)
        (fun a h hp ↦ by
          rw [glueMid_folds] at hp
          exact ⟨hp.1, postR_mid hr hp.1 hp.2⟩)
        le_rfl le_rfl le_rfl

/-- After the fold rounds of a level with a next level: the commitment, the out-of-domain group,
the OOD answer and intro polynomial, the moves before the proof of work, the query group. -/
noncomputable def midTailSpecR
    (H : MidHypJ μ ℓ₀ per c₀ n₀ w (codes i) (codes (i + 1)) level next pre) (hg : g ≤ 192)
    (hεO : eOod (codes (i + 1)) (codes i).κ ≤ εmax) (hOlt : eOod (codes (i + 1)) (codes i).κ < 1)
    (hQlt : eQuery (codes i) (codes (i + 1)) level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQuery (codes i) (codes (i + 1)) level.queries ≤ εmax)
    (K : ∀ s', Spec (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s')
      (fun h ↦ LevelPreR μ ℓ₀ w (i + 1) (codes (i + 1)) next.fold (pre + level.fold)
        (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) s'
        (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s'.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ (i + 1) (pre + level.fold) (next :: rest)
          (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) a h)
      εmax εmax T)
    (r : WhirStateT × List E) (hr : r.1.folds.length = pre + level.fold) :
    Spec (midTailPJ μ per c₀ n₀ g i level next rest r)
      (fun h ↦ AfterFoldR μ ℓ₀ w i (codes i) level.fold pre Gd r (viewC c₀ n₀ (commits h)))
      (fun a h ↦ r.1.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ i pre (level :: next :: rest) Gd a h) εmax 0 T :=
  (commitInv (fun cs ↦ AfterFoldR μ ℓ₀ w i (codes i) level.fold pre Gd r (viewC c₀ n₀ cs))
      (fun cs ↦ MidCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r
        (viewC c₀ n₀ cs))
      (μ - r.1.folds.length - next.fold + next.logInvRate) (3 * 2 ^ next.fold)
      (fun cs W h hW ↦ by
        rw [viewC_append (le_length_of_viewC (ne_nil_of_shapeOK h.1.2))]
        exact midCR_of_commit next rfl H.hP' H.hR' h hW)
      (T := eOod (codes (i + 1)) (codes i).κ) hεO).bind' fun _ ↦
  ((Spec.ofNoMove (p := sampleChallenges (μ - r.1.folds.length))
      (Pre := fun h ↦ MidCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r
        (viewC c₀ n₀ (commits h)))
      (Post := fun z h ↦ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z
        (viewC c₀ n₀ (commits h)))
      (εmax := εmax) (T := 0) (noMoves_sampleN _).noMove hOlt fun h₀ hp ↦ by
        obtain ⟨cs₀, -, -, -, haf⟩ := midCR_word hp
        have hκm := afterFoldR_κ haf
        have hκ : μ - r.1.folds.length = next.fold + (codes (i + 1)).κ := by
          rw [hκm]; have := H.hP; have := H.hP'; omega
        have hκ1 : 1 ≤ μ - r.1.folds.length := by rw [hκm]; exact (codes i).hκ
        refine (escRet_sampleN_le (codes (i + 1)) hκ hκ1
          (rowsOf next.fold (laneO (i + 1) (viewC c₀ n₀ (commits h₀)) (codes (i + 1)).n))
          (fun z cs ↦ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z
            (viewC c₀ n₀ cs)) h₀
          fun z hz hsep ↦ ⟨hp, hz.trans hκm, hsep⟩).trans (by rw [hκm])).mono
      (fun _ h ↦ h) (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun z ↦
  (readInv (fun cs ↦ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z
      (viewC c₀ n₀ cs)) (T := 0) zero_le).bind' fun y ↦
  (roundPolyInv (fun cs ↦ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold next.fold pre Gd r z
      (viewC c₀ n₀ cs)) y
      (T := (2 : ENNReal)⁻¹ ^ g * eQuery (codes i) (codes (i + 1)) level.queries) hεQ).bind'
    fun hy ↦
  (grindPreInv (fun cs ↦ QuadOK hy y ∧ OodCR μ ℓ₀ w i (codes i) (codes (i + 1)) level.fold
      next.fold pre Gd r z (viewC c₀ n₀ cs)) g hεQ).bind' fun _ ↦
  (midQuerySpecR H hg hQlt K r hr z y hy).congr
    (query_bindG' per g (cidx c₀ n₀ i) (μ - r.1.folds.length + level.logInvRate) level.queries
      fun qs lam words ↦ midFinishPJ μ per c₀ n₀ g i next rest r z y hy qs lam words).symm

/-- **The specification of a level with a next level, relativised**, on the program cut at the
residual: from `LevelPreR` for `Gd`, the post is `PostR` for `Gd` and the fold challenges extend
`s.folds`. -/
noncomputable def midSpecR
    (H : MidHypJ μ ℓ₀ per c₀ n₀ w (codes i) (codes (i + 1)) level next pre) (hg : g ≤ 192)
    (hεF : eFold (codes i) level.fold ≤ εmax) (hεO : eOod (codes (i + 1)) (codes i).κ ≤ εmax)
    (hOlt : eOod (codes (i + 1)) (codes i).κ < 1)
    (hQlt : eQuery (codes i) (codes (i + 1)) level.queries < 1)
    (hεQ : (2 : ENNReal)⁻¹ ^ g * eQuery (codes i) (codes (i + 1)) level.queries ≤ εmax)
    (K : ∀ s', Spec (whirPrefixJ μ per c₀ n₀ g (i + 1) (next :: rest) s')
      (fun h ↦ LevelPreR μ ℓ₀ w (i + 1) (codes (i + 1)) next.fold (pre + level.fold)
        (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) s'
        (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s'.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ (i + 1) (pre + level.fold) (next :: rest)
          (gdNext (codes (i + 1)) next.fold (i + 1) (viewC c₀ n₀ (commits h)) s'.folds Gd) a h)
      εmax εmax T)
    (s : WhirStateT) :
    Spec (whirPrefixJ μ per c₀ n₀ g i (level :: next :: rest) s)
      (fun h ↦ LevelPreR μ ℓ₀ w i (codes i) level.fold pre Gd s (viewC c₀ n₀ (commits h)))
      (fun a h ↦ s.folds <+: a.1.1.folds ∧
        PostR μ ℓ₀ w codes c₀ n₀ i pre (level :: next :: rest) Gd a h) εmax εmax T :=
  (((specRetFact (R := fun r ↦ s.folds <+: r.1.folds)
      (foldRoundsSpecR μ ℓ₀ w i (codes i) level.fold pre Gd (viewC c₀ n₀)
        (fun cs ↦ ShapeOK i (codes i) level.fold (viewC c₀ n₀ cs)) H.hw H.hℓ₀ hεF level.fold s [])
      fun ha ↦ foldRoundsT_folds_prefix _ _ _ ha).bind' fun r ↦
    specCases (s.folds <+: r.1.folds ∧ r.1.folds.length = pre + level.fold)
      (fun hr ↦ (midTailSpecR H hg hεO hOlt hQlt hεQ K r hr.2).mono (fun _ hp ↦ hp.2)
        (fun _ _ hp ↦ ⟨hr.1.trans hp.1, hp.2⟩) le_rfl le_rfl le_rfl)
      (fun hr ↦ Spec.dead.mono (fun _ hp ↦ hr ⟨hp.1, afterFoldR_len hp.2⟩) (fun _ _ h ↦ h)
        le_rfl le_rfl le_rfl)).mono
    (fun _ hp ↦ ⟨⟨hp.1, hp.2⟩, by simp⟩) (fun _ _ h ↦ h) le_rfl hεF le_rfl).congr
    (whirPrefixJ_mid μ per c₀ n₀ g i level next rest s).symm

end
end LeanVM.Protocol.Whir.Sound
