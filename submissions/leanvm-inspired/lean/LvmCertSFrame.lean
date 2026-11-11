-- WP-14 (ASM). `Spec.frame`, `Spec.retInv`, `Spec.congr_D`: ported from leanVM
-- `formal/lean_vm/LeanVM/Protocol/EndToEnd/Sound/Frame.lean` (formal rev 40f877dc), unchanged
-- statements and proofs (namespace `LeanVM.Protocol.Compile`); `Spec.orStable` is new for lvm (two
-- commitments opened one after the other, BLUEPRINT A16).
import LvmSpecRulesBind

/-!
# Frame rules for the assembly

* `Spec.frame` (leanVM): an invariant `J` of the history that the sub-program's runs keep is
  carried from the precondition to the postcondition.
* `Spec.retInv` (leanVM): a property of every value the program can return is added to the
  postcondition.
* **`Spec.orStable`** (new): a sub-program specified from `A` with postcondition `False` (it never
  returns in doom: a stacked opening), and a predicate `M` its runs keep (it commits nothing that
  `M` reads), give a specification from `A ∨ M` with postcondition `M`. Doom is `A`'s where `A`
  holds at the start, else `M`, kept to the return; the potential there is the follower's
  allowance. This is how `C_main`'s opening precondition is carried across `C_rec`'s opening
  (WP-7 hand-off a): the doom before the openings is "`C_rec`'s claims fail or `C_main`'s fail".
* **`Spec.or`** (new): two specifications of one program give one whose doom is the union (the
  potential is the smaller of the two). `P_S`'s certificate is the union of the statement's doom
  (`psSpec`) and the residual's doom (`LvmCertSRes`): not doomed at every boundary then gives both
  a good candidate pair and a residual that is the fold of `C_rec`'s candidate (the decoder's input).
* **`Spec.atRet`** (new): a program of prover moves only (`MovesOnly`, e.g. `readScalars n`), from no
  doom, whose doom is created at its return (`Post` there), as `Spec.commitP` creates it at a
  commitment.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

section

variable {α : Type} {p : VerifierProgram α} {Pre : List Ev → Prop} {Post : α → List Ev → Prop}
  {εmax L T : ENNReal}

namespace Spec

open Classical in
/-- **The frame rule** (leanVM): an invariant `J` of the history that every run of `p` keeps is
carried from the precondition to the postcondition. -/
noncomputable def frame (S : Spec p Pre Post εmax L T) (J : List Ev → Prop)
    (hJ : ∀ h₀ l, p.Reach h₀ l → J h₀ → J (h₀ ++ l)) :
    Spec p (fun h ↦ Pre h ∧ J h) (fun a h ↦ Post a h ∧ J h) εmax L T where
  D h₀ l := J h₀ ∧ S.D h₀ l
  V h₀ l := if J h₀ then S.V h₀ l else 1
  le_one h₀ l := by split_ifs; exacts [S.le_one _ _, le_rfl]
  start_D h₀ h := ⟨h.2, S.start_D h₀ h.1⟩
  start_V h₀ h := by simp only [h.2, ↓reduceIte]; exact S.start_V h₀ h.1
  read x hl ha hD := ⟨hD.1, S.read x hl ha hD.2⟩
  grind hl ha hD := ⟨hD.1, S.grind hl ha hD.2⟩
  commit word hl ha hw hD := ⟨hD.1, S.commit word hl ha hw hD.2⟩
  sample {h₀ _ _} hl ha := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.sample hl ha
    · simp only [hJ0, ↓reduceIte]; exact avg_le_one _ fun _ ↦ le_rfl
  query {h₀ _ _ _ _ _} hl ha hans := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.query hl ha hans
    · simp [hJ0]
  moveEnd {h₀ _ _} hl ha hm hD := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.moveEnd hl ha hm fun h ↦ hD ⟨hJ0, h⟩
    · simp [hJ0]
  retEnd {h₀ _ _} hl ha hD := by
    by_cases hJ0 : J h₀
    · simp only [hJ0, ↓reduceIte]; exact S.retEnd hl ha fun h ↦ hD ⟨hJ0, h⟩
    · simp [hJ0]
  retDoom hl ha hD := by simp only [hD.1, ↓reduceIte]; exact S.retDoom hl ha hD.2
  post hl ha hD := ⟨S.post hl ha hD.2, hJ _ _ hl hD.1⟩
  bound hl hne hm hD := by simp only [hD.1, ↓reduceIte]; exact S.bound hl hne hm hD.2

/-- The doom of a framed specification. -/
theorem frame_D (S : Spec p Pre Post εmax L T) (J : List Ev → Prop)
    (hJ : ∀ h₀ l, p.Reach h₀ l → J h₀ → J (h₀ ++ l)) (h₀ l : List Ev) :
    (S.frame J hJ).D h₀ l ↔ J h₀ ∧ S.D h₀ l := Iff.rfl

/-- **A return invariant** (leanVM): a property of every value `p` returns is added to the
postcondition. -/
def retInv (S : Spec p Pre Post εmax L T) (Q : α → Prop)
    (hQ : ∀ l a, p.after l = some (.ret a) → Q a) :
    Spec p Pre (fun a h ↦ Post a h ∧ Q a) εmax L T where
  D := S.D
  V := S.V
  le_one := S.le_one
  start_D := S.start_D
  start_V := S.start_V
  read := S.read
  grind := S.grind
  commit := S.commit
  sample := S.sample
  query := S.query
  moveEnd := S.moveEnd
  retEnd := S.retEnd
  retDoom := S.retDoom
  post hl ha hD := ⟨S.post hl ha hD, hQ _ _ ha⟩
  bound := S.bound

/-- The doom of a specification transported along an equality of programs is unchanged. -/
theorem congr_D {p' : VerifierProgram α} (h : p = p') (S : Spec p Pre Post εmax L T) :
    (S.congr h).D = S.D := by
  subst h; rfl

/-- The average of a constant over the challenges is the constant. -/
theorem avg_const (k : ENNReal) : (Fintype.card E : ENNReal)⁻¹ * ∑ _c : E, k = k := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

open Classical in
/-- **Carry a stable predicate across a sub-program that never returns in doom** (new): from
`A ∨ M`, doom is `S`'s where `A` holds at the start, otherwise `M`, which every run keeps; the
postcondition is `M`. The lead is the larger of `S`'s and the follower's allowance. -/
noncomputable def orStable {A M : List Ev → Prop} (S : Spec p A (fun _ _ ↦ False) εmax L T)
    (hM : ∀ h₀ l, p.Reach h₀ l → M h₀ → M (h₀ ++ l)) (hT : T ≤ εmax) :
    Spec p (fun h ↦ A h ∨ M h) (fun _ h ↦ M h) εmax (max L T) T where
  D h₀ l := if A h₀ then S.D h₀ l else M h₀
  V h₀ l := if A h₀ then S.V h₀ l else if M h₀ then min 1 T else 1
  le_one h₀ l := by split_ifs; exacts [S.le_one _ _, min_le_left _ _, le_rfl]
  start_D h₀ h := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte]; exact S.start_D h₀ hA
    · simp only [hA, ↓reduceIte]; exact h.resolve_left hA
  start_V h₀ h := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte]; exact (S.start_V h₀ hA).trans (le_max_left _ _)
    · simp only [hA, h.resolve_left hA, ↓reduceIte]
      exact (min_le_right _ _).trans (le_max_right _ _)
  read {h₀ _ _} x hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.read x hl ha hD
    · simp only [hA, ↓reduceIte] at hD ⊢; exact hD
  grind {h₀ _ _ _} hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.grind hl ha hD
    · simp only [hA, ↓reduceIte] at hD ⊢; exact hD
  commit {h₀ _ _ _ _} word hl ha hw hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.commit word hl ha hw hD
    · simp only [hA, ↓reduceIte] at hD ⊢; exact hD
  sample {h₀ _ _} hl ha := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte]; exact S.sample hl ha
    · by_cases hM0 : M h₀
      · simp only [hA, hM0, ↓reduceIte, avg_const, le_refl]
      · simp only [hA, hM0, ↓reduceIte]; exact avg_le_one _ fun _ ↦ le_rfl
  query {h₀ _ _ _ _ _} hl ha hans := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte]; exact S.query hl ha hans
    · simp only [hA, ↓reduceIte]; exact le_rfl
  moveEnd {h₀ _ _} hl ha hm hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.moveEnd hl ha hm hD
    · simp only [hA, ↓reduceIte] at hD ⊢; simp [hD]
  retEnd {h₀ _ _} hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.retEnd hl ha hD
    · simp only [hA, ↓reduceIte] at hD ⊢; simp [hD]
  retDoom {h₀ _ _} hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.retDoom hl ha hD
    · simp only [hA, ↓reduceIte] at hD ⊢; simp [hD]
  post {h₀ _ _} hl ha hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD; exact (S.post hl ha hD).elim
    · simp only [hA, ↓reduceIte] at hD; exact hM _ _ hl hD
  bound {h₀ _} hl hne hm hD := by
    by_cases hA : A h₀
    · simp only [hA, ↓reduceIte] at hD ⊢; exact S.bound hl hne hm hD
    · simp only [hA, ↓reduceIte] at hD ⊢
      simp only [hD, ↓reduceIte]
      calc (2 : ENNReal)⁻¹ ^ grindBits _ * min 1 T ≤ 1 * min 1 T := by
            gcongr; exact pow_le_one₀ (by simp) (ENNReal.inv_le_one.2 (by norm_num))
        _ ≤ εmax := by rw [one_mul]; exact (min_le_right _ _).trans hT

open Classical in
/-- **The union of two dooms** (new): doom is either's, the potential the smaller one. -/
noncomputable def or {Pre₁ Pre₂ : List Ev → Prop} {Post₁ Post₂ : α → List Ev → Prop}
    (S₁ : Spec p Pre₁ Post₁ εmax L T) (S₂ : Spec p Pre₂ Post₂ εmax L T) :
    Spec p (fun h ↦ Pre₁ h ∨ Pre₂ h) (fun a h ↦ Post₁ a h ∨ Post₂ a h) εmax L T where
  D h₀ l := S₁.D h₀ l ∨ S₂.D h₀ l
  V h₀ l := min (S₁.V h₀ l) (S₂.V h₀ l)
  le_one h₀ l := (min_le_left _ _).trans (S₁.le_one _ _)
  start_D h₀ h := h.imp (S₁.start_D h₀) (S₂.start_D h₀)
  start_V h₀ h := h.elim (fun h ↦ (min_le_left _ _).trans (S₁.start_V h₀ h))
    (fun h ↦ (min_le_right _ _).trans (S₂.start_V h₀ h))
  read x hl ha hD := hD.imp (S₁.read x hl ha) (S₂.read x hl ha)
  grind hl ha hD := hD.imp (S₁.grind hl ha) (S₂.grind hl ha)
  commit word hl ha hw hD := hD.imp (S₁.commit word hl ha hw) (S₂.commit word hl ha hw)
  sample {h₀ l _} hl ha := le_min
    (le_trans (by gcongr with c; exact min_le_left _ _) (S₁.sample hl ha))
    (le_trans (by gcongr with c; exact min_le_right _ _) (S₂.sample hl ha))
  query hl ha hans := min_le_min (S₁.query hl ha hans) (S₂.query hl ha hans)
  moveEnd hl ha hm hD := le_min (S₁.moveEnd hl ha hm fun h ↦ hD (.inl h))
    (S₂.moveEnd hl ha hm fun h ↦ hD (.inr h))
  retEnd hl ha hD := le_min (S₁.retEnd hl ha fun h ↦ hD (.inl h))
    (S₂.retEnd hl ha fun h ↦ hD (.inr h))
  retDoom {h₀ l _} hl ha _ := le_min
    (if h1 : S₁.D h₀ l then S₁.retDoom hl ha h1 else (min_le_left _ _).trans (S₁.retEnd hl ha h1))
    (if h2 : S₂.D h₀ l then S₂.retDoom hl ha h2 else (min_le_left _ _).trans (S₂.retEnd hl ha h2))
  post hl ha hD := hD.imp (S₁.post hl ha) (S₂.post hl ha)
  bound hl hne hm hD := hD.elim
    (fun h ↦ le_trans (by gcongr; exact min_le_left _ _) (S₁.bound hl hne hm h))
    (fun h ↦ le_trans (by gcongr; exact min_le_right _ _) (S₂.bound hl hne hm h))

/-- The doom of a union. -/
theorem or_D {Pre₁ Pre₂ : List Ev → Prop} {Post₁ Post₂ : α → List Ev → Prop}
    (S₁ : Spec p Pre₁ Post₁ εmax L T) (S₂ : Spec p Pre₂ Post₂ εmax L T) (h₀ l : List Ev) :
    (S₁.or S₂).D h₀ l ↔ S₁.D h₀ l ∨ S₂.D h₀ l := Iff.rfl

end Spec

/-! ## Programs of prover moves only -/

namespace VerifierProgram

/-- **`p` has no challenge and no opening** (only prover moves, returns and rejections). -/
def MovesOnly : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, MovesOnly (k x)
  | .sample _ => False
  | .grind _ k => MovesOnly k
  | .commit _ _ k => MovesOnly k
  | .query _ _ _ => False

variable {β : Type}

theorem MovesOnly.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.MovesOnly)
    (hf : ∀ a, (f a).MovesOnly) : (p.bind f).MovesOnly := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact hp.elim
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact ih hp
  | query i ps k ih => exact hp.elim

theorem MovesOnly.after {p q : VerifierProgram α} (hp : p.MovesOnly) {l : List Ev}
    (h : p.after l = some q) : q.MovesOnly := by
  induction l generalizing p with
  | nil => cases p <;> (cases h; exact hp)
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact hp.elim
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

theorem movesOnly_readScalars : ∀ n, (readScalars n).MovesOnly
  | 0 => trivial
  | n + 1 => MovesOnly.bind (p := readScalar) (fun _ ↦ trivial) fun _ ↦
      MovesOnly.bind (movesOnly_readScalars n) fun _ ↦ trivial

end VerifierProgram

namespace Spec

open Classical in
/-- **Doom created at the return** of a program of prover moves only (new): from no doom, doom is
`Post` at the return; the boundary there carries the follower's allowance. -/
noncomputable def atRet {Post : α → List Ev → Prop} (hp : p.MovesOnly) (hT : T ≤ εmax) :
    Spec p (fun _ ↦ False) Post εmax 0 T where
  D h₀ l := ∃ a, p.after l = some (.ret a) ∧ Post a (h₀ ++ l)
  V h₀ l := if ∃ a, p.after l = some (.ret a) ∧ Post a (h₀ ++ l) then min 1 T else 1
  le_one h₀ l := by split_ifs <;> simp
  start_D _ h := h.elim
  start_V _ h := h.elim
  read := by
    rintro _ _ _ _ - ha ⟨a, ha', -⟩; rw [ha] at ha'; cases ha'
  grind := by
    rintro _ _ _ _ - ha ⟨a, ha', -⟩; rw [ha] at ha'; cases ha'
  commit := by
    rintro _ _ _ _ _ _ - ha - ⟨a, ha', -⟩; rw [ha] at ha'; cases ha'
  sample := by
    intro _ _ _ _ ha; exact ((hp.after ha : VerifierProgram.MovesOnly (.sample _)) : False).elim
  query := by
    intro _ _ _ _ _ _ _ ha; exact ((hp.after ha : VerifierProgram.MovesOnly (.query _ _ _)) : False).elim
  moveEnd := by intro _ _ _ _ _ _ hD; simp [hD]
  retEnd := by intro _ _ _ _ _ hD; simp [hD]
  retDoom := by intro _ _ _ _ _ hD; simp [hD]
  post := by
    rintro _ _ a - ha ⟨a', ha', hP⟩
    rw [ha] at ha'; cases ha'; exact hP
  bound := by
    intro _ _ _ _ _ hD
    simp only [hD, ↓reduceIte]
    calc (2 : ENNReal)⁻¹ ^ grindBits _ * min 1 T ≤ 1 * min 1 T := by
          gcongr; exact pow_le_one₀ (by simp) (ENNReal.inv_le_one.2 (by norm_num))
      _ ≤ εmax := by rw [one_mul]; exact (min_le_right _ _).trans hT

/-- The doom of `atRet`. -/
theorem atRet_D {Post : α → List Ev → Prop} (hp : p.MovesOnly) (hT : T ≤ εmax) (h₀ l : List Ev) :
    (atRet (Post := Post) hp hT).D h₀ l ↔ ∃ a, p.after l = some (.ret a) ∧ Post a (h₀ ++ l) :=
  Iff.rfl

end Spec

/-! ## Programs with no commitment and no proof of work -/

namespace VerifierProgram

/-- **`p` commits nothing** (every node reachable in `p` is not a commitment). -/
def NoCommit : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoCommit (k x)
  | .sample k => ∀ c, NoCommit (k c)
  | .grind _ k => NoCommit k
  | .commit _ _ _ => False
  | .query _ _ k => ∀ r, NoCommit (k r)

/-- **`p` asks no proof of work.** -/
def NoGrind : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoGrind (k x)
  | .sample k => ∀ c, NoGrind (k c)
  | .grind _ _ => False
  | .commit _ _ k => NoGrind k
  | .query _ _ k => ∀ r, NoGrind (k r)

variable {β : Type}

theorem commits_app (h l : List Ev) : commits (h ++ l) = commits h ++ commits l := by
  induction h with
  | nil => rfl
  | cons e es ih => cases e <;> simp [commits, ih]

theorem NoCommit.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.NoCommit)
    (hf : ∀ a, (f a).NoCommit) : (p.bind f).NoCommit := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact hp.elim
  | query i ps k ih => exact fun r ↦ ih r (hp r)

theorem NoGrind.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.NoGrind)
    (hf : ∀ a, (f a).NoGrind) : (p.bind f).NoGrind := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact hp.elim
  | commit ht w k ih => exact ih hp
  | query i ps k ih => exact fun r ↦ ih r (hp r)

theorem NoCommit.after {p q : VerifierProgram α} (hp : p.NoCommit) {l : List Ev}
    (h : p.after l = some q) : q.NoCommit := by
  induction l generalizing p with
  | nil => cases p <;> (cases h; exact hp)
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact hp.elim
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

theorem NoGrind.after {p q : VerifierProgram α} (hp : p.NoGrind) {l : List Ev}
    (h : p.after l = some q) : q.NoGrind := by
  induction l generalizing p with
  | nil => cases p <;> (cases h; exact hp)
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact hp.elim
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

/-- **The runs of a program that commits nothing have no commitment.** -/
theorem NoCommit.reach_commits {p : VerifierProgram α} (hp : p.NoCommit) {h₀ l : List Ev}
    (hl : p.Reach h₀ l) : commits l = [] := by
  induction hl with
  | nil => rfl
  | read x _ _ ih | sample x _ _ ih => simp [commits_app, ih, commits]
  | grind _ _ ih => simp [commits_app, ih, commits]
  | query _ _ _ ih => simp [commits_app, ih, commits]
  | commit word _ ha _ ih => exact ((hp.after ha) : False).elim

end VerifierProgram

end
end LeanVM.Protocol.Compile
