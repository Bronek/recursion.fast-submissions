-- WP-14 (ASM). New for lvm (O11, O5a): the extraction map of the `S` branch (WP-13b's decoder on
-- `C_rec`'s word, fold challenges and residual read off the history), its correctness at an
-- accepted history outside doom and luck, and the knowledge certificate of `schemeS` with the
-- middle phases abstract.
import LvmCertSLuck
import LvmXDecUd

/-!
# The extraction and the knowledge certificate of the `S` branch

* `accept_split`: an accepted history of `P_S` is the roots, the middle phases, `C_rec`'s batching
  challenge, first round polynomial, fold rounds and residual, then the rest.
* `recData mid x h`: `C_rec`'s fold state and residual, read off `h` by the same splits;
  **`extS mid child c x h`** `= witOf x (child (colOf (decodeRec (wdOf W) (alphaN α) (fNr f))))`
  (WP-13b's decoder on `C_rec`'s word `W`, its fold challenges `α` and residual `f`, O11).
* **`extract_S`**: at an accepted history whose every boundary is outside the doom `psSpec ∨ resSpec`
  and that is not lucky, the witness is one of the relation (from `NodeSound`): not doomed after the
  roots gives a good candidate pair (`psSpec_D_roots`), not doomed after the residual gives
  `¬ FinalDoomUd` (`resSpec_D`, WP-7 `not_finViol_of_not_resC`, `not_finalDoomUd`), not lucky gives
  `¬ FoldAllLuck`, and WP-13b's `decodeRec_of_ud_ws` returns the good candidate.
* **`kcertS`**: `KCert (schemeS vk (PSWith mid)) (Rel (accV VS vk))` with `ε = 2^-129`,
  `εB = 2^-130` (so `εFS ≤ 2^-128`), from `MidSpec`, the middle phases' shape (`MidShape`: no
  commitment, no proof of work, multiaffine `C_rec` claims) and `NodeSound`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir
open scoped NNReal ENNReal

variable {α β : Type}

/-! ## Facts about runs -/

theorem MovesOnly.after_samples {p q : VerifierProgram α} (hp : p.MovesOnly) {l : List Ev}
    (h : p.after l = some q) : l.filterMap sampleOf = [] := by
  induction l generalizing p with
  | nil => rfl
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact (hp : False).elim
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

theorem NoCommit.after_commits {p q : VerifierProgram α} (hp : p.NoCommit) {l : List Ev}
    (h : p.after l = some q) : commits l = [] := by
  induction l generalizing p with
  | nil => rfl
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | exact ih (hp _) h
      | exact (hp : False).elim
      | (refine ih ?_ h; exact hp)
      | (split_ifs at h; refine ih ?_ h; exact hp)

theorem readScalars_after_len : ∀ (n : ℕ) {l : List Ev} {xs : List E},
    (readScalars n).after l = some (.ret xs) → xs.length = n
  | 0, l, xs, h => by
    cases l with
    | nil => simp [readScalars, VerifierProgram.after] at h; subst h; rfl
    | cons e es => cases e <;> simp [readScalars, VerifierProgram.after] at h
  | n + 1, l, xs, h => by
    obtain ⟨y, l₁, l₂, rfl, -, h2⟩ := after_bind_ret (p := readScalar) h
    obtain ⟨ys, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    have := readScalars_after_len n h3
    cases m₂ with
    | nil => simp [VerifierProgram.after] at h4; subst h4; simp [this]
    | cons e es => cases e <;> simp [VerifierProgram.after] at h4

theorem sample_after {l : List Ev} {c : E} (h : sampleChallenge.after l = some (.ret c)) :
    l = [Ev.sample c] := by
  rcases l with _ | ⟨e, _ | ⟨e', es⟩⟩
  · simp [sampleChallenge, VerifierProgram.after] at h
  · cases e <;> simp [sampleChallenge, VerifierProgram.after] at h; subst h; rfl
  · cases e <;> cases e' <;> simp [sampleChallenge, VerifierProgram.after] at h

theorem movesOnly_ret (a : α) : (VerifierProgram.ret a).MovesOnly := trivial

theorem movesOnly_roundPoly (t : E) :
    (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 t none).MovesOnly := by
  unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly
  exact MovesOnly.bind (p := readScalar) (fun _ ↦ trivial) fun _ ↦
    MovesOnly.bind (movesOnly_readScalars _) fun _ ↦ movesOnly_ret _

/-- The plain round polynomial of three coefficients meets its claim. -/
theorem roundPoly_after {t : E} {l : List Ev} {q : List E}
    (h : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 t none).after l = some (.ret q)) :
    QuadOK q t := by
  unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly at h
  obtain ⟨c₀, l₁, l₂, rfl, -, h2⟩ := after_bind_ret (p := readScalar) h
  obtain ⟨tl, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
  have hl := readScalars_after_len _ h3
  cases m₂ with
  | nil =>
    simp [VerifierProgram.after] at h4; subst h4
    obtain ⟨c₂, rfl⟩ : ∃ c₂, tl = [c₂] := by
      rcases tl with _ | ⟨a, _ | ⟨b, t'⟩⟩ <;> simp at hl ⊢
    exact quadOK_roundPoly t c₀ c₂
  | cons e es => cases e <;> simp [VerifierProgram.after] at h4

/-- **The fold rounds' state**: the challenges are the samples of the run. -/
theorem foldRoundsT_after : ∀ (n : ℕ) (s : WhirStateT) (lf : List E) {l : List Ev}
    {r : WhirStateT × List E}, (foldRoundsT n s lf).after l = some (.ret r) →
      r.2 = lf ++ l.filterMap sampleOf ∧ (l.filterMap sampleOf).length = n ∧
        r.1.folds = s.folds ++ l.filterMap sampleOf ∧ r.1.glued = s.glued ∧
        (0 < n → QuadOK r.1.quad r.1.target)
  | 0, s, lf, l, r, h => by
    cases l with
    | nil => simp [foldRoundsT, VerifierProgram.after] at h; subst h; simp
    | cons e es => cases e <;> simp [foldRoundsT, VerifierProgram.after] at h
  | n + 1, s, lf, l, r, h => by
    unfold foldRoundsT at h
    obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
    obtain rfl := sample_after h1
    obtain ⟨quad, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
    have hs3 := MovesOnly.after_samples (movesOnly_roundPoly _) h3
    obtain ⟨e1, e2, e3, e4, e5⟩ := foldRoundsT_after n _ _ h4
    simp only [List.filterMap_append, hs3, List.nil_append] at e1 e2 e3 ⊢
    refine ⟨by rw [e1]; simp [sampleOf], by simp [sampleOf, e2], by rw [e3]; simp [sampleOf],
      e4, fun _ ↦ ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · cases m₂ with
      | nil =>
        simp [foldRoundsT, VerifierProgram.after] at h4; subst h4
        exact roundPoly_after h3
      | cons e es => cases e <;> simp [foldRoundsT, VerifierProgram.after] at h4
    · exact e5 hn

theorem roots_after {l : List Ev} (h : rootsProg.after l = some (.ret ())) :
    ∃ W₁ W₂, l = [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] := by
  rcases l with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, es⟩⟩⟩
  · simp [rootsProg, commitRootUd, cfgMain20, cfgRec20, VerifierProgram.readCommitment,
      VerifierProgram.bind, VerifierProgram.after] at h
  · cases e₁ <;> simp [rootsProg, commitRootUd, cfgMain20, cfgRec20, VerifierProgram.readCommitment,
      VerifierProgram.bind, VerifierProgram.after] at h
  · cases e₁ <;> cases e₂ <;> simp [rootsProg, commitRootUd, cfgMain20, cfgRec20,
      VerifierProgram.readCommitment, VerifierProgram.bind, VerifierProgram.after] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    exact ⟨_, _, rfl⟩
  · cases e₁ <;> cases e₂ <;> cases e₃ <;> simp [rootsProg, commitRootUd, cfgMain20, cfgRec20,
      VerifierProgram.readCommitment, VerifierProgram.bind, VerifierProgram.after] at h

/-- The words a reachable history commits are well shaped. -/
theorem reachable_commit_ws {p : VerifierProgram α} {h : List Ev} (hr : p.Reachable h) :
    ∀ ht w W, Ev.commit ht w W ∈ h → WellShaped w W := by
  induction hr with
  | nil => simp
  | read x _ _ ih | sample x _ _ ih =>
    intro ht w W hm; rcases List.mem_append.1 hm with hm | hm
    · exact ih _ _ _ hm
    · simp at hm
  | grind _ _ ih | query _ _ _ ih =>
    intro ht w W hm; rcases List.mem_append.1 hm with hm | hm
    · exact ih _ _ _ hm
    · simp at hm
  | commit word _ ha hw ih =>
    intro ht w W hm; rcases List.mem_append.1 hm with hm | hm
    · exact ih _ _ _ hm
    · simp only [List.mem_singleton, Ev.commit.injEq] at hm
      obtain ⟨-, rfl, rfl⟩ := hm
      exact hw

/-- A run of a program of scalar reads only is scalar reads. -/
theorem reads_of_after {p q : VerifierProgram α} (hm : p.MovesOnly) (hc : p.NoCommit)
    (hg : p.NoGrind) {l : List Ev} (h : p.after l = some q) : ∀ e ∈ l, ∃ y, e = Ev.read y := by
  induction l generalizing p with
  | nil => simp
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    all_goals first
      | (intro e' he'
         rcases List.mem_cons.1 he' with rfl | he'
         · exact ⟨_, rfl⟩
         · exact ih (hm _) (hc _) (hg _) h e' he')
      | exact (hm : False).elim
      | exact (hc : False).elim
      | exact (hg : False).elim

theorem readScalars_reads (n : ℕ) {l : List Ev} {q : VerifierProgram (List E)}
    (h : (readScalars n).after l = some q) : ∀ e ∈ l, ∃ y, e = Ev.read y :=
  reads_of_after (movesOnly_readScalars n) (nc_readScalars n) (ng_readScalars n) h

/-! ## The accepted runs of `P_S` -/

section Concrete

attribute [local irreducible] verifyStackedUd

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

/-- **An accepted history of `P_S`** is the roots, the middle phases, `C_rec`'s batching challenge,
first round polynomial, fold rounds and residual, then the rest. -/
theorem accept_split {h : List Ev} (hacc : (PSWith mid x).after h = some (.ret true)) :
    ∃ (hr lm : List Ev) (cl : OpenClaims) (ρ : E) (lq : List Ev) (quad : List E) (lf : List Ev)
      (r : WhirStateT × List E) (lres : List Ev) (res : List E) (rest : List Ev),
      h = hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lres ++ rest))))) ∧
      rootsProg.after hr = some (.ret ()) ∧ (mid x).after lm = some (.ret cl) ∧
      (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq =
        some (.ret quad) ∧
      (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r) ∧
      (readScalars (2 ^ (19 - r.1.folds.length))).after lres = some (.ret res) := by
  rw [PSWith_eq] at hacc
  obtain ⟨_, hr, l₂, rfl, h1, h2⟩ := after_bind_ret (p := rootsProg) hacc
  obtain ⟨cl, lm, l₃, rfl, h3, h4⟩ := after_bind_ret (p := mid x) h2
  obtain ⟨_, lrec, lmain, rfl, h5, -⟩ := after_bind_ret (p := verifyStackedUd cfgRec20 cl.1) h4
  rw [stacked_one_eq cfgRec20 recLevel rec20_levels cl.1] at h5
  obtain ⟨ρ, l₆, l₇, rfl, h6, h7⟩ := after_bind_ret h5
  obtain rfl := sample_after h6
  obtain ⟨quad, lq, l₈, rfl, h8, h9⟩ := after_bind_ret h7
  obtain ⟨r, lf, l₉, rfl, h10, h11⟩ := after_bind_ret h9
  rw [finTail_eq] at h11
  obtain ⟨res, lres, l₁₀, rfl, h12, -⟩ := after_bind_ret h11
  exact ⟨hr, lm, cl, ρ, lq, quad, lf, r, lres, res, l₁₀ ++ lmain, by simp, h1, h3, h8, h10, h12⟩

end Concrete

/-! ## The extraction map (O11) -/

/-- `C_rec`'s fold state and residual, read off a history (the splits of `accept_split`). -/
def recData (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    Option ((WhirStateT × List E) × List E) :=
  match rootsProg.retSplit h with
  | none => none
  | some (_, _, l₂) => match (mid x).retSplit l₂ with
    | none => none
    | some (cl, _, l₃) => match sampleChallenge.retSplit l₃ with
      | none => none
      | some (ρ, _, l₄) =>
        match (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).retSplit l₄ with
        | none => none
        | some (quad, _, l₅) => match (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).retSplit l₅ with
          | none => none
          | some (r, _, l₆) => match (readScalars (2 ^ (19 - r.1.folds.length))).retSplit l₆ with
            | none => none
            | some (res, _, _) => some (r, res)

/-- The column of a decoded word list (zero when decoding fails). -/
def colOf (o : Option (List K)) : Column 19 := ⟨Vector.ofFn fun i ↦ (o.getD []).getD i 0⟩

theorem colOf_msgOf (q : Column 19) :
    colOf (some ((List.range (2 ^ 19)).map (Lvm.X.msgOf q))) = q := by
  rcases q with ⟨v⟩
  unfold colOf
  rw [Option.getD_some]
  refine congrArg Column.mk (Vector.ext fun i hi ↦ ?_)
  rw [Vector.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi)]
  rw [List.getElem_map, List.getElem_range]
  unfold Lvm.X.msgOf
  show Vector.getD v i 0 = v[i]
  unfold Vector.getD
  rw [Array.getD_eq_getD_getElem?]
  simp only [Vector.getElem?_toArray]
  rw [Vector.getElem?_eq_getElem hi]
  rfl

/-- **The `S` branch's extraction map**: WP-13b's decoder on `C_rec`'s word, fold challenges and
residual; the witness with the decoded column's child. -/
noncomputable def extS (mid : List UInt8 → VerifierProgram OpenClaims)
    (child : Column 19 → Signed) (_c : RecursionFast.Digest) (x : List UInt8) (h : List Ev) : Wit :=
  witOf x (child (colOf ((recData mid x h).bind fun d ↦
    Lvm.X.decodeRec (Lvm.X.wdOf (WrOf h)) (Lvm.X.alphaN fun i ↦ d.1.2.getD i 0)
      (Lvm.X.fNr (resMsg d.2)))))

/-! ## The doom after the roots, and at the start -/

theorem rootsProg_after_roots (W₁ W₂ : Compile.Word) :
    rootsProg.after [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] = some (.ret ()) := by
  simp [rootsProg, commitRootUd, cfgMain20, cfgRec20, VerifierProgram.readCommitment,
    VerifierProgram.bind, VerifierProgram.after]

theorem rootsProg_ne_ret (a : Unit) : rootsProg ≠ .ret a := by
  simp [rootsProg, commitRootUd, cfgMain20, VerifierProgram.readCommitment, VerifierProgram.bind]

theorem after_nil' (p : VerifierProgram α) : p.after [] = some p := by simp [VerifierProgram.after]

section Doom

attribute [local irreducible] verifyStackedUd

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}

/-- **The doom right after the roots** (`rootsSpec`): the doom the second root creates. -/
theorem rootsSpec_D {Post : Unit → List Ev → Prop} {εm T : ℝ≥0∞} (hT : T ≤ εm) (W₁ W₂ : Compile.Word) :
    (rootsSpec Post hT).D [] [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] ↔
      Post () [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] := by
  have h1 : (commitRootUd cfgMain20).after [Ev.commit 21 64 W₁] = some (.ret ()) := by
    simp [commitRootUd, cfgMain20, VerifierProgram.readCommitment, VerifierProgram.after]
  rw [rootsSpec, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    show [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] = [Ev.commit 21 64 W₁] ++ [Ev.commit 15 64 W₂]
      from rfl, bind_D_after _ _ h1 (by simp)]
  exact Iff.rfl

/-- **The statement's doom after the roots**: `CommitDoomS ∧ RootShape` is doom there. -/
theorem psSpec_D_roots (hnc : RecNoCommit) (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS)
    (x : List UInt8) (W₁ W₂ : Compile.Word)
    (h : CommitDoomS Good x [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] ∧
      RootShape [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂]) :
    (psSpec hnc hmid hLm x).D [] [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] := by
  rw [psSpec, Spec.congr_D, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_ret _ _ (rootsProg_after_roots W₁ W₂)]
  exact ⟨(rootsSpec_D _ W₁ W₂).2 h, Spec.start_D _ _ (by simpa using h)⟩

/-- No doom at the start of `psSpec`. -/
theorem psSpec_D_nil (hnc : RecNoCommit) (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS)
    (x : List UInt8) : ¬ (psSpec hnc hmid hLm x).D [] [] := by
  rw [psSpec, Spec.congr_D, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ (after_nil' rootsProg) rootsProg_ne_ret, rootsSpec,
    show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ (after_nil' _) (by
      simp [commitRootUd, cfgMain20, VerifierProgram.readCommitment])]
  exact id

/-- No doom at the start of `resSpec`. -/
theorem resSpec_D_nil (x : List UInt8) : ¬ (resSpec mid x).D [] [] := by
  rw [resSpec, Spec.congr_D, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ (after_nil' rootsProg) rootsProg_ne_ret]
  exact id

/-- **`P_S`'s whole specification**: the union of the statement's doom and the residual's. -/
noncomputable def SPS (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    Spec (PSWith mid x) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0 :=
  ((psSpec recNoCommit hmid hLm x).or (resSpec mid x)).mono (fun _ h ↦ .inl h)
    (fun _ _ h ↦ h.elim id id) le_rfl le_rfl le_rfl

theorem SPS_D (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) (h₀ l : List Ev) :
    (SPS hmid hLm x).D h₀ l ↔ (psSpec recNoCommit hmid hLm x).D h₀ l ∨ (resSpec mid x).D h₀ l :=
  Iff.rfl

theorem SPS_D_nil (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    ¬ (SPS hmid hLm x).D [] [] := by
  rw [SPS_D]
  exact fun h ↦ h.elim (psSpec_D_nil recNoCommit hmid hLm x) (resSpec_D_nil x)

end Doom

/-! ## The extraction (O11) -/

/-- **The middle phases' shape** (structural facts of the concrete phases): no commitment, no
proof of work, and the claims on `C_rec` they return are multiaffine. -/
structure MidShape (mid : List UInt8 → VerifierProgram OpenClaims) : Prop where
  noCommit : ∀ x, (mid x).NoCommit
  noGrind : ∀ x, (mid x).NoGrind
  recAffine : ∀ x l cl, (mid x).after l = some (.ret cl) → ∀ c ∈ cl.1, IsMultiaffine 19 c.1

section Extract

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}
  {x : List UInt8} {hr lm lq lf lres rest : List Ev} {cl : OpenClaims} {ρ : E} {quad res : List E}
  {r : WhirStateT × List E}

theorem recData_split (h1 : rootsProg.after hr = some (.ret ())) (h3 : (mid x).after lm = some (.ret cl))
    (h8 : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq = some (.ret quad))
    (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (h12 : (readScalars (2 ^ (19 - r.1.folds.length))).after lres = some (.ret res)) :
    recData mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lres ++ rest)))))) =
      some (r, res) := by
  unfold recData
  rw [retSplit_of_after _ _ _ h1]
  dsimp only
  rw [retSplit_of_after _ _ _ h3]
  dsimp only
  rw [retSplit_of_after sampleChallenge [Ev.sample ρ] _ rfl]
  dsimp only
  rw [retSplit_of_after _ _ _ h8]
  dsimp only
  rw [retSplit_of_after _ _ _ h10]
  dsimp only
  rw [retSplit_of_after _ _ _ h12]

theorem rootsOf_split (h1 : rootsProg.after hr = some (.ret ())) (l : List Ev) :
    rootsOf (hr ++ l) = hr := by
  unfold rootsOf
  rw [retSplit_of_after _ _ _ h1]

theorem foldChal_split (h1 : rootsProg.after hr = some (.ret ())) (h3 : (mid x).after lm = some (.ret cl))
    (h8 : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq = some (.ret quad))
    (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
    (h12 : (readScalars (2 ^ (19 - r.1.folds.length))).after lres = some (.ret res)) :
    foldChal mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lres ++ rest)))))) = r.2 := by
  obtain ⟨e1, e2, -⟩ := foldRoundsT_after 6 _ [] h10
  rw [List.nil_append] at e1
  have hq := MovesOnly.after_samples (movesOnly_roundPoly _) h8
  have hs := MovesOnly.after_samples (movesOnly_readScalars _) h12
  unfold foldChal afterMid
  rw [retSplit_of_after _ _ _ h1]
  dsimp only
  rw [retSplit_of_after _ _ _ h3]
  dsimp only
  simp only [List.filterMap_append, hq, hs, ← e1, List.nil_append]
  rw [show [Ev.sample ρ].filterMap sampleOf = [ρ] from rfl, List.singleton_append, List.drop_one,
    List.tail_cons, List.take_append_of_le_length (by rw [e1, e2]),
    List.take_of_length_le (by rw [e1, e2])]

theorem boundary_of_last_read {h : List Ev} {y : E} (hy : h.getLast? = some (Ev.read y)) :
    Boundary h := by
  cases h with
  | nil => simp at hy
  | cons e es =>
    unfold Boundary
    simp only [hy]

open Classical in
/-- **The decoder succeeds** (O11, WP-14d split it out of `extract_S` for O5c): at an accepted
history of `P_S` outside the doom `psSpec ∨ resSpec` at every boundary and not lucky, `C_rec`'s fold
state and residual are read off the history, and WP-13b's decoder on its word, fold challenges and
residual returns the words of a candidate `q` of a good pair. -/
theorem decode_S (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {h : List Ev} (hreach : (PSWith mid x).Reachable h)
    (hacc : (PSWith mid x).after h = some (.ret true)) (hB : ¬ LuckB mid x h)
    (hD : ∀ h', h' <+: h → Boundary h' → ¬ (SPS hmid hLm x).D [] h') :
    ∃ qm q, Good x qm q ∧ ∃ r res, recData mid x h = some (r, res) ∧
      Lvm.X.decodeRec (Lvm.X.wdOf (WrOf h)) (Lvm.X.alphaN fun i ↦ r.2.getD i 0)
        (Lvm.X.fNr (resMsg res)) = some ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)) := by
  obtain ⟨hr, lm, cl, ρ, lq, quad, lf, r, lres, res, rest, rfl, h1, h3, h8, h10, h12⟩ :=
    accept_split hacc
  obtain ⟨W₁, W₂, rfl⟩ := roots_after h1
  have hws := reachable_commit_ws hreach
  have hW₁ : WellShaped 64 W₁ := hws 21 64 W₁ (by simp)
  have hW₂ : WellShaped 64 W₂ := hws 15 64 W₂ (by simp)
  -- the fold state and the residual
  obtain ⟨e1, e2, e3, e4, e5⟩ := foldRoundsT_after 6 _ [] h10
  rw [List.nil_append] at e1 e3
  have hlen6 : r.2.length = 6 := by rw [e1]; exact e2
  have hfl : r.1.folds.length = 6 := by rw [e3]; exact e2
  have hreslen : res.length = 2 ^ (19 - r.1.folds.length) := readScalars_after_len _ h12
  -- the commitments up to the residual
  have hcm : commits lm = [] := NoCommit.after_commits (hsh.noCommit x) h3
  have hcq : commits lq = [] := NoCommit.after_commits (nc_roundPoly _ _ _) h8
  have hcf : commits lf = [] := NoCommit.after_commits (nc_foldRoundsT _ _ _) h10
  have hcr : commits lres = [] := NoCommit.after_commits (nc_readScalars _) h12
  have hcs : commits ([Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] ++ lm ++ [Ev.sample ρ] ++ lq ++ lf ++
      lres) = [(21, 64, W₁), (15, 64, W₂)] := by
    simp only [commits_append, hcm, hcq, hcf, hcr, List.append_nil]
    rfl
  -- (1) a good candidate pair
  have hDr := hD [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] (List.prefix_append _ _) (by
    simp [Boundary])
  have hRS : RootShape [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] := ⟨W₁, W₂, rfl, hW₁, hW₂⟩
  have hgood : ¬ CommitDoomS Good x [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] := fun hc ↦
    hDr ((SPS_D hmid hLm x _ _).2 (.inl (psSpec_D_roots recNoCommit hmid hLm x W₁ W₂ ⟨hc, hRS⟩)))
  simp only [CommitDoomS, not_forall, not_not] at hgood
  obtain ⟨⟨qm, qr⟩, ⟨-, hqr⟩, hG⟩ := hgood
  have hqr' : qr ∈ Candidates 19 2 (udThr 13 2) W₂ := hqr
  -- (2) the residual is consistent
  have hcl := hsh.recAffine x lm cl h3
  have hne : lres ≠ [] := by
    intro he; subst he
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.two_pow_pos (19 - r.1.folds.length)).ne'
    rw [hn] at h12
    simp [readScalars, VerifierProgram.readScalar, VerifierProgram.bind, VerifierProgram.after] at h12
  have hlast : ∃ y, lres.getLast? = some (Ev.read y) := by
    obtain ⟨e, he⟩ := List.getLast?_isSome.2 hne |> Option.isSome_iff_exists.1
    obtain ⟨y, rfl⟩ := readScalars_reads _ h12 e (List.mem_of_getLast? he)
    exact ⟨y, he⟩
  have hbnd : Boundary ([Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] ++ (lm ++ ([Ev.sample ρ] ++
      (lq ++ (lf ++ lres))))) := by
    obtain ⟨y, hy⟩ := hlast
    refine boundary_of_last_read (y := y) ?_
    rw [List.getLast?_append_of_ne_nil _ (by simp [hne]), List.getLast?_append_of_ne_nil _ (by simp [hne]),
      List.getLast?_append_of_ne_nil _ (by simp [hne]), List.getLast?_append_of_ne_nil _ (by simp [hne]),
      List.getLast?_append_of_ne_nil _ hne, hy]
  have hDres := hD _ ⟨rest, by simp [List.append_assoc]⟩ hbnd
  have hnR : ¬ ResC 19 6 (batW cl.1 ρ) 0 (codesRec20 0) 6 0 r res
      (viewC 1 2 (commits ([Ev.commit 21 64 W₁, Ev.commit 15 64 W₂] ++ lm ++ [Ev.sample ρ] ++ lq ++
        lf ++ lres))) := fun hR ↦
    hDres ((SPS_D hmid hLm x _ _).2 (.inr (resSpec_D mid x h1 h3 hcl h8 h10 h12 hR)))
  rw [hcs] at hnR
  have hview : viewC 1 2 [(21, 64, W₁), (15, 64, W₂)] = [(15, 64, W₂)] := rfl
  rw [hview] at hnR
  have hbook : res.length = 2 ^ (19 - r.1.folds.length) ∧
      FinBook 19 0 (codesRec20 0) 6 0 r [(15, 64, W₂)] := by
    refine ⟨hreslen, ⟨by rw [hfl, hlen6], by rw [hlen6], rfl, ?_, e5 (by norm_num)⟩, ?_, hlen6⟩
    · intro c' hc'
      rw [e4] at hc'
      simp at hc'
    · exact ⟨rfl, W₂, rfl, hW₂⟩
  have hnv := not_finViol_of_not_resC hbook hnR
  have hfd := (not_finalDoomUd (μ := 19) (R := 2) (by norm_num) (by norm_num) (by norm_num) r hlen6
    _ _ _ _ hnv).2
  -- (3) the decoder
  obtain ⟨q, hq, rfl, -, hdec⟩ := Lvm.X.decodeRec_of_ud_ws (fun q ↦ q = qr) W₂
    (fun i ↦ r.2.getD i 0) (resMsg res) hW₂ (fun hcd ↦ hcd qr hqr' rfl) hfd
  -- (4) no luck
  have hnl : ¬ FoldAllLuck (fun i : Fin LeanVM.Protocol.EndToEnd.laneBits ↦ r.2.getD i 0)
      (laneRows 19 2 W₂) (encRows 19 2 q) := by
    intro hFL
    apply hB
    refine ⟨q, ?_, ?_⟩
    · unfold WrOf
      rw [rootsOf_split h1]
      exact hqr
    · unfold WrOf
      rw [rootsOf_split h1, foldChal_split h1 h3 h8 h10 h12]
      exact roundsLuck_of_foldAllLuck _ _ _ _ hlen6 hFL
  -- (5) the decoder on the history's inputs
  refine ⟨qm, q, hG, r, res, recData_split h1 h3 h8 h10 h12, ?_⟩
  unfold WrOf
  rw [rootsOf_split h1, show wordOf (commits [Ev.commit 21 64 W₁, Ev.commit 15 64 W₂]) 1 = W₂ from rfl,
    hdec hnl]

/-- **The extraction is a witness** (O11): at an accepted history of `P_S` outside the doom
`psSpec ∨ resSpec` at every boundary and not lucky, `extS` gives a witness of the relation. -/
theorem extract_S (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {VS : SProg} {vk : RecursionFast.Digest} {child : Column 19 → Signed}
    (hnode : NodeSound VS vk Good child) {c : RecursionFast.Digest} {h : List Ev}
    (hok : okS vk c x = true) (hreach : (PSWith mid x).Reachable h)
    (hacc : (PSWith mid x).after h = some (.ret true)) (hB : ¬ LuckB mid x h)
    (hD : ∀ h', h' <+: h → Boundary h' → ¬ (SPS hmid hLm x).D [] h') :
    Rel (accV VS vk) c (extS mid child c x h) := by
  obtain ⟨qm, q, hG, r, res, hrd, hdec⟩ := decode_S hmid hLm hsh hreach hacc hB hD
  unfold extS
  rw [hrd, Option.bind_some, hdec, colOf_msgOf]
  exact hnode c x qm q hok hG

end Extract

/-! ## The knowledge certificate of the `S` branch (O5a, `mid` abstract) -/

section KCert

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}

theorem coe_εS : (((2 : ℝ≥0)⁻¹ ^ 129 : ℝ≥0) : ℝ≥0∞) = εS := by
  rw [ENNReal.coe_pow, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]

theorem coe_εB : (((2 : ℝ≥0)⁻¹ ^ 130 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ ^ 130 := by
  rw [ENNReal.coe_pow, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]

/-- `P_S`'s specification at the certificate's `ε = 2^-129` (as `ℝ≥0`). -/
noncomputable def SPSε (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    Spec (PSWith mid x) (fun _ ↦ False) (fun b _ ↦ b = false)
      ((((2 : ℝ≥0)⁻¹ ^ 129 : ℝ≥0)) : ℝ≥0∞) 0 0 :=
  (SPS hmid hLm x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) coe_εS.ge le_rfl le_rfl

/-- The luck and the extraction of the `S` branch. -/
noncomputable def luckExtS (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {VS : SProg} {vk : RecursionFast.Digest} {child : Column 19 → Signed}
    (hnode : NodeSound VS vk Good child) :
    LuckExt (schemeS vk (PSWith mid)) (Rel (accV VS vk)) fun x ↦ (SPSε hmid hLm x).D [] where
  B := LuckB mid
  εB := (2 : ℝ≥0)⁻¹ ^ 130
  εB_lt_one := pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)
  B_nil _ := LuckB_nil
  B_read _ _ _ hB := not_luckB_snoc rfl hB
  B_commit _ _ _ _ hB := not_luckB_snoc rfl hB
  B_group {x h p} _ _ _ _ hB := by
    refine (esc_luck_le p h hB).trans ?_
    rw [coe_εB]
    refine le_trans ?_ six_δL_le
    gcongr
    exact_mod_cast Nat.sub_le 6 _
  ext := extS mid child
  extract hok hr ha hB _ hD := extract_S hmid hLm hsh hnode hok hr ha hB hD

/-- **The knowledge certificate of the `S` branch** (O5a with the middle phases abstract): from
`MidSpec` (the middle phases from the doom root, every group `≤ 2^-129`, lead `≤ 2^-129`), the
middle phases' shape and `NodeSound`. -/
noncomputable def kcertS (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {VS : SProg} {vk : RecursionFast.Digest} {child : Column 19 → Signed}
    (hnode : NodeSound VS vk Good child) :
    KCert (schemeS vk (PSWith mid)) (Rel (accV VS vk)) :=
  kcertOfSpec (S := schemeS vk (PSWith mid)) (SPSε hmid hLm)
    (fun x hD ↦ (SPS_D_nil hmid hLm x hD).elim) (pow_lt_one₀ (by positivity) (by norm_num) (by norm_num))
    (fun x _ hr ↦ NoGrind.reach_grindBits (ng_PSWith hsh.noGrind x) hr) (luckExtS hmid hLm hsh hnode)

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertS (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {VS : SProg} {vk : RecursionFast.Digest} {child : Column 19 → Signed}
    (hnode : NodeSound VS vk Good child) :
    Scheme.εFS (kcertS hmid hLm hsh hnode) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  εFS_kcertOfSpec _ _ _ _ _ le_rfl le_rfl

end KCert

end Lvm.ASM
