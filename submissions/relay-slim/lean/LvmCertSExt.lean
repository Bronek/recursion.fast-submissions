-- WP-14 (ASM), adapted for lvm2 S4 (X-REC2-CERT): the extraction map of the `S` branch (DEC's
-- level-1 decoder `decodeRec1` then WP-13b's level-0 decoder `decodeRec`, on `C_rec`'s two words,
-- fold challenges and final residual read off the history), its correctness at an accepted history
-- outside doom and luck, and the knowledge certificate of `schemeS` with the middle phases abstract.
import LvmCertSLuck
import LvmCertS2Mid
import LvmXDecUd
import LvmXDec1Ud

/-!
# The extraction and the knowledge certificate of the `S` branch (two-level `C_rec`)

* `accept_split`: an accepted history of `P_S` is the roots, the middle phases, `C_rec`'s batching
  challenge, first round polynomial, level-0 fold rounds, level-1 commitment, level-0 query group,
  query intro polynomial, level-1 fold rounds and final residual, then the rest.
* `recData2 mid x h`: `C_rec`'s level-0 fold state `r₀` (`α₀ = r₀.2`), level-1 fold state `r₁`
  (`α₁ = r₁.2`) and final residual, read off `h` by the same splits; `WrOf h`, `Wr1Of h`: `C_rec`'s
  root word (commitment 1) and level-1 word (commitment 2).
* `SPS`: the certificate's doom `psSpec ∨ resSpec ∨ midSpec1` (statement, final residual, level-1
  commitment).
* **`decodeFacts_S`**: at an accepted history, not lucky and outside doom at every boundary, a good
  pair `(qm, qr)` and the decoders' hypotheses on the history's values: `¬ CommitDoomUd`,
  `¬ MidDoomUd`, `¬ FinalDoomL`, no fold luck at either level, well-shaped words.
* **`extS`**, `decode_S`, `extract_S`: level 1 is decoded first (`decodeRec1` on `Wr1Of h`, `α₁`,
  `f₂`), its output is the level-0 residual input of `decodeRec` (on `WrOf h`, `α₀`); with
  `ud_extract_rec20` the result is the good candidate's words.
* **`kcertS`**: `KCert (schemeS vk (PSWith mid)) (Rel (accV VS vk))` with `ε = 2^-129`,
  `εB = 2^-130` (so `εFS ≤ 2^-128`), from `MidSpec`, `MidShape` and `NodeSound`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Ud
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
    ∃ W₁ W₂, l = [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] := by
  rcases l with _ | ⟨e₁, _ | ⟨e₂, _ | ⟨e₃, es⟩⟩⟩
  · simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G, VerifierProgram.readCommitment,
      VerifierProgram.bind, VerifierProgram.after] at h
  · cases e₁ <;> simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G, VerifierProgram.readCommitment,
      VerifierProgram.bind, VerifierProgram.after] at h
  · cases e₁ <;> cases e₂ <;> simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G,
      VerifierProgram.readCommitment, VerifierProgram.bind, VerifierProgram.after] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    exact ⟨_, _, rfl⟩
  · cases e₁ <;> cases e₂ <;> cases e₃ <;> simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G,
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

theorem queryOpenings_after {i : ℕ} {ps : List ℕ} {l : List Ev} {w : List (List K)}
    (h : (queryOpenings i ps).after l = some (.ret w)) : l = [Ev.query w] := by
  rcases l with _ | ⟨e, _ | ⟨e', es⟩⟩
  · simp [queryOpenings, VerifierProgram.after] at h
  · cases e <;> simp [queryOpenings, VerifierProgram.after] at h; subst h; rfl
  · cases e <;> cases e' <;> simp [queryOpenings, VerifierProgram.after] at h

/-- The challenges of a completed run of the positions: one per `per` positions. -/
def posCount (per : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, rem => if rem = 0 then 0 else posCount per fuel (rem - min per rem) + 1

theorem samplePositionsAux_after (per depth : ℕ) : ∀ (fuel rem : ℕ) {l : List Ev} {qs : List ℕ},
    (samplePositionsAux per depth fuel rem).after l = some (.ret qs) →
      (l.filterMap sampleOf).length = posCount per fuel rem
  | 0, rem, l, qs, h => by
    cases l with
    | nil => rfl
    | cons e es => cases e <;> simp [samplePositionsAux, VerifierProgram.after] at h
  | fuel + 1, rem, l, qs, h => by
    unfold samplePositionsAux at h
    by_cases hr : rem = 0
    · rw [if_pos hr] at h
      cases l with
      | nil => simp [posCount, hr]
      | cons e es => cases e <;> simp [VerifierProgram.after] at h
    · rw [if_neg hr] at h
      obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
      obtain rfl := sample_after h1
      obtain ⟨rest, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
      have := samplePositionsAux_after per depth fuel _ h3
      cases m₂ with
      | nil => simp [posCount, hr, List.filterMap_append, this, sampleOf]
      | cons e es => cases e <;> simp [VerifierProgram.after] at h4

/-- **The query group's challenges**: the positions' and `λ`. -/
theorem queryFrag_after_samples {per d t c : ℕ} {l : List Ev} {g : List ℕ × E × List (List K)}
    (h : (queryFrag per d t c).after l = some (.ret g)) :
    (l.filterMap sampleOf).length = posCount per t t + 1 := by
  unfold queryFrag at h
  obtain ⟨qs, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
  obtain ⟨lam, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
  obtain rfl := sample_after h3
  obtain ⟨w, n₁, n₂, rfl, h5, h6⟩ := after_bind_ret h4
  obtain rfl := queryOpenings_after h5
  have := samplePositionsAux_after per d t t h1
  cases n₂ with
  | nil => simp [List.filterMap_append, this, sampleOf]
  | cons e es => cases e <;> simp [VerifierProgram.after] at h6

theorem nc_queryFrag (per d t c : ℕ) : (queryFrag per d t c).NoCommit :=
  NoCommit.bind (nc_samplePositions _ _ _) fun _ ↦ NoCommit.bind nc_sample fun _ ↦
    NoCommit.bind (nc_query _ _) fun _ ↦ nc_ret _

theorem require_after {c : Prop} [Decidable c] {l : List Ev}
    (h : (VerifierProgram.require c).after l = some (.ret ())) : l = [] := by
  unfold VerifierProgram.require at h
  split at h
  · cases l with
    | nil => rfl
    | cons e es => cases e <;> simp [VerifierProgram.after] at h
  · cases l with
    | nil => simp [VerifierProgram.after] at h
    | cons e es => cases e <;> simp [VerifierProgram.after] at h

/-- **The query group with the proof of work** (S2J, `g ≠ 0`): the PoW challenge, the positions'
challenges and `λ`. -/
theorem queryFragG_after_samples {g per d t c : ℕ} (hg : g ≠ 0) {l : List Ev}
    {gg : List ℕ × E × List (List K)} (h : (queryFragG g per d t c).after l = some (.ret gg)) :
    (l.filterMap sampleOf).length = posCount per t t + 2 := by
  unfold queryFragG powCheck at h
  rw [if_neg hg, VerifierProgram.bind_assoc] at h
  obtain ⟨c', l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
  obtain rfl := sample_after h1
  obtain ⟨_, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret h2
  obtain rfl := require_after h3
  have := queryFrag_after_samples h4
  simp only [List.filterMap_append, this, List.nil_append, List.length_append]
  simp [sampleOf]
  omega

/-- **The moves before the proof of work** (S2J, `g ≠ 0`): the separating challenge and the nonce. -/
theorem grindPre_after_samples {g : ℕ} (hg : g ≠ 0) {l : List Ev}
    (h : (grindPre g).after l = some (.ret ())) : (l.filterMap sampleOf).length = 1 := by
  unfold grindPre at h
  rw [if_neg hg] at h
  obtain ⟨c, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret (p := sampleChallenge) h
  obtain rfl := sample_after h1
  obtain ⟨y, m₁, m₂, rfl, h3, h4⟩ := after_bind_ret (p := readScalar) h2
  have := MovesOnly.after_samples (p := readScalar) (fun _ ↦ trivial) h3
  cases m₂ with
  | nil => simp [List.filterMap_append, this, sampleOf]
  | cons e es => cases e <;> simp [VerifierProgram.after, pure] at h4

/-- The level-0 query group of `C_rec` with the proof of work (S2J P20, `g = 14`): `25` challenges
(separating, PoW, `22` positions' challenges for `170` positions, `λ`). -/
theorem qgRec_after_samples {d c : ℕ} {l : List Ev} {gg : List ℕ × E × List (List K)}
    (h : ((grindPre 14).bind fun _ ↦ queryFragG 14 8 d 170 c).after l = some (.ret gg)) :
    (l.filterMap sampleOf).length = 25 := by
  obtain ⟨_, l₁, l₂, rfl, h1, h2⟩ := after_bind_ret h
  rw [List.filterMap_append, List.length_append, grindPre_after_samples (by decide) h1,
    queryFragG_after_samples (by decide) h2]
  rfl

theorem nc_qgRec (d c : ℕ) : ((grindPre 14).bind fun _ ↦ queryFragG 14 8 d 170 c).NoCommit :=
  NoCommit.bind (nc_grindPre _) fun _ ↦ NoCommit.bind (nc_powCheck _) fun _ ↦ nc_queryFrag _ _ _ _

/-- The first commitment after a commitment-free prefix. -/
theorem splitCommit_of_noCommit : ∀ (pre : List Ev), commits pre = [] → ∀ ht w W b,
    splitCommit (pre ++ Ev.commit ht w W :: b) = some (W, b)
  | [], _, _, _, _, _ => rfl
  | e :: pre, h, ht, w, W, b => by
    cases e with
    | commit => simp [commits] at h
    | _ =>
      simp only [List.cons_append, splitCommit]
      exact splitCommit_of_noCommit pre (by simpa [commits] using h) ht w W b

theorem gluedOK_of_folds {μ : ℕ} {s s' : WhirStateT} (hg : GluedOK μ s) (hgl : s'.glued = s.glued)
    (hfl : s.folds.length ≤ s'.folds.length) : GluedOK μ s' := by
  intro c hc
  rw [hgl] at hc
  exact ⟨(hg c hc).1.trans hfl, (hg c hc).2⟩

/-! ## The accepted runs of `P_S` -/

section Concrete

attribute [local irreducible] verifyStackedUd

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}

/-- **An accepted history of `P_S`** (lvm2: two-level `C_rec`) is the roots, the middle phases,
`C_rec`'s batching challenge, first round polynomial, level-0 fold rounds, level-1 commitment,
level-0 query group, query intro polynomial, level-1 fold rounds and final residual, then the rest. -/
theorem accept_split {h : List Ev} (hacc : (PSWith mid x).after h = some (.ret true)) :
    ∃ (hr lm : List Ev) (cl : OpenClaims) (ρ : E) (lq : List Ev) (quad : List E) (lf : List Ev)
      (r : WhirStateT × List E) (lc lg : List Ev) (g : List ℕ × E × List (List K)) (lhq : List Ev)
      (hq : List E) (lf1 : List Ev) (r₁ : WhirStateT × List E) (lres : List Ev) (res : List E)
      (rest : List Ev),
      h = hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
        (lres ++ rest))))))))) ∧
      rootsProg.after hr = some (.ret ()) ∧ (mid x).after lm = some (.ret cl) ∧
      (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq =
        some (.ret quad) ∧
      (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r) ∧
      (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).after lc = some (.ret ()) ∧
      ((grindPre 14).bind fun _ ↦ queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).after lg = some (.ret g) ∧
      (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after lhq =
        some (.ret hq) ∧
      (foldRoundsT 4 (glueLv 19 0 r g.1 g.2.1 g.2.2 hq) []).after lf1 = some (.ret r₁) ∧
      (readScalars (2 ^ (19 - r₁.1.folds.length))).after lres = some (.ret res) := by
  rw [PSWith_eq] at hacc
  obtain ⟨_, hr, l₂, rfl, h1, h2⟩ := after_bind_ret (p := rootsProg) hacc
  obtain ⟨cl, lm, l₃, rfl, h3, h4⟩ := after_bind_ret (p := mid x) h2
  obtain ⟨_, lrec, lmain, rfl, h5, -⟩ := after_bind_ret (p := verifyStackedUd cfgRec20G cl.1) h4
  rw [stacked_two_eq cfgRec20G recLevel0 recLevel1 rec20_levels cl.1] at h5
  obtain ⟨ρ, l₆, l₇, rfl, h6, h7⟩ := after_bind_ret h5
  obtain rfl := sample_after h6
  obtain ⟨quad, lq, l₈, rfl, h8, h9⟩ := after_bind_ret h7
  obtain ⟨r, lf, l₉, rfl, h10, h11⟩ := after_bind_ret h9
  rw [midTail_fin_eq] at h11
  obtain ⟨_, lc, l₁₀, rfl, h12, h13⟩ := after_bind_ret h11
  obtain ⟨_, lgp, l₁₁', rfl, h14a, h14b⟩ := after_bind_ret h13
  obtain ⟨g, lgq, l₁₁, rfl, h14c, h15⟩ := after_bind_ret h14b
  have h14 : ((grindPre 14).bind fun _ ↦ queryFragG 14 8 (19 - r.1.folds.length + 2) 170
      (cidx 1 2 0)).after (lgp ++ lgq) = some (.ret g) := by
    exact (after_bind_append (fun _ ↦ queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0))
      (p := grindPre 14) h14a lgq).trans h14c
  obtain ⟨hq, lhq, l₁₂, rfl, h16, h17⟩ := after_bind_ret h15
  obtain ⟨r₁, lf1, l₁₃, rfl, h18, h19⟩ := after_bind_ret h17
  rw [finTail_eq] at h19
  obtain ⟨res, lres, l₁₄, rfl, h20, -⟩ := after_bind_ret h19
  exact ⟨hr, lm, cl, ρ, lq, quad, lf, r, lc, lgp ++ lgq, g, lhq, hq, lf1, r₁, lres, res, l₁₄ ++ lmain,
    by simp, h1, h3, h8, h10, h12, h14, h16, h18, h20⟩

end Concrete

/-! ## The history's values -/

/-- **`C_rec`'s fold states and final residual**, read off a history (the splits of
`accept_split`): the level-0 fold state `r₀` (`α₀ = r₀.2`), the level-1 fold state `r₁`
(`α₁ = r₁.2`) and the residual. -/
def recData2 (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) (h : List Ev) :
    Option ((WhirStateT × List E) × (WhirStateT × List E) × List E) :=
  match rootsProg.retSplit h with
  | none => none
  | some (_, _, l₂) => match (mid x).retSplit l₂ with
    | none => none
    | some (cl, _, l₃) => match sampleChallenge.retSplit l₃ with
      | none => none
      | some (ρ, _, l₄) =>
        match (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).retSplit l₄ with
        | none => none
        | some (quad, _, l₅) =>
          match (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).retSplit l₅ with
          | none => none
          | some (r, _, l₆) =>
            match (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).retSplit l₆ with
            | none => none
            | some (_, _, l₇) =>
              match ((grindPre 14).bind fun _ ↦ queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).retSplit l₇ with
              | none => none
              | some (g, _, l₈) => match (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3
                  (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).retSplit l₈ with
                | none => none
                | some (hq, _, l₉) =>
                  match (foldRoundsT 4 (glueLv 19 0 r g.1 g.2.1 g.2.2 hq) []).retSplit l₉ with
                  | none => none
                  | some (r₁, _, l₁₀) =>
                    match (readScalars (2 ^ (19 - r₁.1.folds.length))).retSplit l₁₀ with
                    | none => none
                    | some (res, _, _) => some (r, r₁, res)

/-- **`C_rec`'s level-1 word** (commitment `2`). -/
def Wr1Of (h : List Ev) : Compile.Word := wordOf (commits h) 2

section Split

variable {mid : List UInt8 → VerifierProgram OpenClaims} {x : List UInt8}
  {hr lm lq lf lc lg lhq lf1 lres rest : List Ev} {cl : OpenClaims} {ρ : E} {quad hq res : List E}
  {r r₁ : WhirStateT × List E} {g : List ℕ × E × List (List K)}
  (h1 : rootsProg.after hr = some (.ret ())) (h3 : (mid x).after lm = some (.ret cl))
  (h8 : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (batT cl.1 ρ) none).after lq =
    some (.ret quad))
  (h10 : (foldRoundsT 6 ⟨batT cl.1 ρ, quad, [], []⟩ []).after lf = some (.ret r))
  (hcm : (readCommitment (19 - r.1.folds.length - 4 + 3) (3 * 2 ^ 4)).after lc = some (.ret ()))
  (hg : ((grindPre 14).bind fun _ ↦ queryFragG 14 8 (19 - r.1.folds.length + 2) 170 (cidx 1 2 0)).after lg = some (.ret g))
  (hh : (LeanVM.Protocol.Verifier.sumcheckRoundPoly 3 (enfOf 0 r.2 g.1 g.2.1 g.2.2) none).after
    lhq = some (.ret hq))
  (hf1 : (foldRoundsT 4 (glueLv 19 0 r g.1 g.2.1 g.2.2 hq) []).after lf1 = some (.ret r₁))
  (hres : (readScalars (2 ^ (19 - r₁.1.folds.length))).after lres = some (.ret res))
include h1 h3 h8 h10 hcm hg hh hf1 hres

theorem recData2_split :
    recData2 mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = some (r, r₁, res) := by
  unfold recData2
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
  rw [retSplit_of_after _ _ _ hcm]
  dsimp only
  rw [retSplit_of_after _ _ _ hg]
  dsimp only
  rw [retSplit_of_after _ _ _ hh]
  dsimp only
  rw [retSplit_of_after _ _ _ hf1]
  dsimp only
  rw [retSplit_of_after _ _ _ hres]

omit h3 h8 h10 hcm hg hh hf1 hres in
theorem rootsOf_split (l : List Ev) : rootsOf (hr ++ l) = hr := by
  unfold rootsOf
  rw [retSplit_of_after _ _ _ h1]

/-- **The level-0 fold challenges read by the luck are the run's.** -/
theorem foldChal_split :
    foldChal mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = r.2 := by
  obtain ⟨e1, e2, -⟩ := foldRoundsT_after 6 _ [] h10
  rw [List.nil_append] at e1
  have hq := MovesOnly.after_samples (movesOnly_roundPoly _) h8
  unfold foldChal afterMid
  rw [retSplit_of_after _ _ _ h1]
  dsimp only
  rw [retSplit_of_after _ _ _ h3]
  dsimp only
  simp only [List.filterMap_append, hq, ← e1, List.nil_append]
  rw [show [Ev.sample ρ].filterMap sampleOf = [ρ] from rfl, List.singleton_append, List.drop_one,
    List.tail_cons, List.take_append_of_le_length (by rw [e1, e2]),
    List.take_of_length_le (by rw [e1, e2])]

/-- **`C_rec`'s level-1 commitment as the luck reads it** is the run's. -/
theorem rec1Of_split {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W]) :
    rec1Of mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = some (W, lg ++ (lhq ++ (lf1 ++ (lres ++ rest)))) := by
  have hcq := NoCommit.after_commits (nc_roundPoly _ _ _) h8
  have hcf := NoCommit.after_commits (nc_foldRoundsT _ _ _) h10
  unfold rec1Of afterMid
  rw [retSplit_of_after _ _ _ h1]
  dsimp only
  rw [retSplit_of_after _ _ _ h3]
  dsimp only
  subst hlc
  have := splitCommit_of_noCommit ([Ev.sample ρ] ++ lq ++ lf) (by
    simp only [commits_append, hcq, hcf]; rfl) ht w W (lg ++ (lhq ++ (lf1 ++ (lres ++ rest))))
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using this

/-- **The level-1 fold challenges read by the luck are the run's.** -/
theorem foldChal1_split {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W]) :
    foldChal1 mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = r₁.2 := by
  obtain ⟨e1, e2, -⟩ := foldRoundsT_after 4 _ [] hf1
  rw [List.nil_append] at e1
  have hgs := qgRec_after_samples hg
  have hhs := MovesOnly.after_samples (movesOnly_roundPoly _) hh
  have hrs := MovesOnly.after_samples (movesOnly_readScalars _) hres
  unfold foldChal1
  rw [rec1Of_split h1 h3 h8 h10 hcm hg hh hf1 hres hlc]
  dsimp only
  have h25 : (lg.filterMap sampleOf).length = 25 := hgs
  simp only [List.filterMap_append, hhs, hrs, ← e1, List.nil_append]
  rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
    List.nil_append, List.take_append_of_le_length (by rw [e1, e2]),
    List.take_of_length_le (by rw [e1, e2])]

/-- The level-1 word read by the luck is the run's. -/
theorem W1L_split {W : Compile.Word} {ht w : ℕ} (hlc : lc = [Ev.commit ht w W]) :
    W1L mid x (hr ++ (lm ++ ([Ev.sample ρ] ++ (lq ++ (lf ++ (lc ++ (lg ++ (lhq ++ (lf1 ++
      (lres ++ rest)))))))))) = W :=
  W1L_of_rec1Of (rec1Of_split h1 h3 h8 h10 hcm hg hh hf1 hres hlc)

end Split

theorem boundary_of_last_read {h : List Ev} {y : E} (hy : h.getLast? = some (Ev.read y)) :
    Boundary h := by
  cases h with
  | nil => simp at hy
  | cons e es =>
    unfold Boundary
    simp only [hy]

theorem boundary_of_last_commit {h : List Ev} {ht w : ℕ} {W : Compile.Word}
    (hy : h.getLast? = some (Ev.commit ht w W)) : Boundary h := by
  cases h with
  | nil => simp at hy
  | cons e es =>
    unfold Boundary
    simp only [hy]

/-! ## The extraction map (O11) -/

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

/-! ## The doom after the roots, and at the start -/

theorem rootsProg_after_roots (W₁ W₂ : Compile.Word) :
    rootsProg.after [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] = some (.ret ()) := by
  simp [rootsProg, commitRootUd, cfgMain24G, cfgRec20G, VerifierProgram.readCommitment,
    VerifierProgram.bind, VerifierProgram.after]

theorem rootsProg_ne_ret (a : Unit) : rootsProg ≠ .ret a := by
  simp [rootsProg, commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.bind]

theorem after_nil' (p : VerifierProgram α) : p.after [] = some p := by simp [VerifierProgram.after]

section Doom

attribute [local irreducible] verifyStackedUd

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}

/-- **The doom right after the roots** (`rootsSpec`): the doom the second root creates. -/
theorem rootsSpec_D {Post : Unit → List Ev → Prop} {εm T : ℝ≥0∞} (hT : T ≤ εm) (W₁ W₂ : Compile.Word) :
    (rootsSpec Post hT).D [] [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] ↔
      Post () [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] := by
  have h1 : (commitRootUd cfgMain24G).after [Ev.commit 19 64 W₁] = some (.ret ()) := by
    simp [commitRootUd, cfgMain24G, VerifierProgram.readCommitment, VerifierProgram.after]
  rw [rootsSpec, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    show [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] = [Ev.commit 19 64 W₁] ++ [Ev.commit 15 64 W₂]
      from rfl, bind_D_after _ _ h1 (by simp)]
  exact Iff.rfl

/-- **The statement's doom after the roots**: `CommitDoomS ∧ RootShape` is doom there. -/
theorem psSpec_D_roots (hnc : RecCommitsOne) (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS)
    (x : List UInt8) (W₁ W₂ : Compile.Word)
    (h : CommitDoomS Good x [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] ∧
      RootShape [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂]) :
    (psSpec hnc hmid hLm x).D [] [Ev.commit 19 64 W₁, Ev.commit 15 64 W₂] := by
  rw [psSpec, Spec.congr_D, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_ret _ _ (rootsProg_after_roots W₁ W₂)]
  exact ⟨(rootsSpec_D _ W₁ W₂).2 h, Spec.start_D _ _ (by simpa using h)⟩

/-- No doom at the start of `psSpec`. -/
theorem psSpec_D_nil (hnc : RecCommitsOne) (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS)
    (x : List UInt8) : ¬ (psSpec hnc hmid hLm x).D [] [] := by
  rw [psSpec, Spec.congr_D, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ (after_nil' rootsProg) rootsProg_ne_ret, rootsSpec,
    show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ (after_nil' _) (by
      simp [commitRootUd, cfgMain24G, VerifierProgram.readCommitment])]
  exact id

/-- No doom at the start of `resSpec`. -/
theorem resSpec_D_nil (x : List UInt8) : ¬ (resSpec mid x).D [] [] := by
  rw [resSpec, Spec.congr_D, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ (after_nil' rootsProg) rootsProg_ne_ret]
  exact id

/-- No doom at the start of `midSpec1`. -/
theorem midSpec1_D_nil (x : List UInt8) : ¬ (midSpec1 mid x).D [] [] := by
  rw [midSpec1, Spec.congr_D, show (Spec.bind' _ _ : Spec (_ >>= _) _ _ _ _ _) = Spec.bind _ _ from rfl,
    bind_D_inside _ _ (after_nil' rootsProg) rootsProg_ne_ret]
  exact id

/-- **`P_S`'s whole specification** (lvm2): the union of the statement's doom, the final residual's
and the level-1 commitment's. -/
noncomputable def SPS (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    Spec (PSWith mid x) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0 :=
  (((psSpec recCommitsOne hmid hLm x).or (resSpec mid x)).or (midSpec1 mid x)).mono
    (fun _ h ↦ .inl (.inl h)) (fun _ _ h ↦ h.elim (fun h ↦ h.elim id id) id) le_rfl le_rfl le_rfl

theorem SPS_D (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) (h₀ l : List Ev) :
    (SPS hmid hLm x).D h₀ l ↔ ((psSpec recCommitsOne hmid hLm x).D h₀ l ∨ (resSpec mid x).D h₀ l) ∨
      (midSpec1 mid x).D h₀ l :=
  Iff.rfl

theorem SPS_D_nil (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    ¬ (SPS hmid hLm x).D [] [] := by
  rw [SPS_D]
  exact fun h ↦ h.elim (fun h ↦ h.elim (psSpec_D_nil recCommitsOne hmid hLm x) (resSpec_D_nil x))
    (midSpec1_D_nil x)

end Doom

/-! ## The decoders' hypotheses from the doom (P20) -/

/-- The level-0 folded word of `C_rec`'s opening is the fold of the root's lane rows. -/
theorem foldedW0_eq {r : WhirStateT × List E} (hlen : r.2.length = EndToEnd.laneBits) (W₀ : Compile.Word)
    (rest : List (ℕ × ℕ × Compile.Word)) :
    foldedW 0 (codesRec20 0) r ((15, 64, W₀) :: rest) =
      foldAll (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) (laneRows 19 2 W₀) Fin.elim0 := by
  have h1 := rowsOf_foldsN_eq_foldAll EndToEnd.laneBits r.2 hlen
    (laneO 0 ((15, 64, W₀) :: rest) (2 ^ (19 - EndToEnd.laneBits + 2)))
  rw [rowsOf_laneO_zero 19 2, rowsOf_zero] at h1
  exact congrFun h1 Fin.elim0

/-- The level-1 folded word of `C_rec`'s opening is the fold of the level-1 rows. -/
theorem foldedW1_eq {r₁ : WhirStateT × List E} (hlen : r₁.2.length = 4)
    (cs : List (ℕ × ℕ × Compile.Word)) :
    (fun _ : Fin 0 → Bool ↦ foldedW 1 (codesRec20 1) r₁ cs) =
      foldAll (fun i : Fin 4 ↦ r₁.2.getD i 0) (rows1 4 (codesRec20 1).n (wordOf cs 1)) := by
  have h1 := rowsOf_foldsN_eq_foldAll 4 r₁.2 hlen (laneO 1 cs (codesRec20 1).n)
  rw [rowsOf_zero] at h1
  exact h1

/-- **The level-1 commitment's doom from the extractor's**: with the level-0 bookkeeping,
`MidDoomUd` of the history's words is `FarC` of the opening's view. -/
theorem farC_of_midDoom20 {w : List E → E} {r : WhirStateT × List E} {W₀ W₁ : Compile.Word} {ht : ℕ}
    (hlen : r.2.length = 6) (hfl : r.1.folds.length = 6) (hgl : r.1.glued = [])
    (hquad : QuadOK r.1.quad r.1.target) (hW₀ : WellShaped 64 W₀) (hW₁ : WellShaped (3 * 2 ^ 4) W₁)
    (hht : ht = 12)
    (hD : MidDoomUd (udThr 13 2) (codesRec20 1) (by rfl : 19 - EndToEnd.laneBits = 4 + (codesRec20 1).κ)
      (foldAll (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) (laneRows 19 2 W₀) Fin.elim0)
      (rows1 4 (codesRec20 1).n W₁)) :
    FarC 19 6 w 0 (codesRec20 0) (codesRec20 1) 6 4 0 hκ_rec20 r
      [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] := by
  subst hht
  refine ⟨[(15, 64, W₀)], W₁, rfl, hW₁, ⟨⟨by rw [hfl, hlen], by rw [hlen], rfl, ?_, hquad⟩,
    ⟨rfl, W₀, rfl, hW₀⟩, hlen⟩, ?_⟩
  · intro c hc; rw [hgl] at hc; simp at hc
  · rw [foldedW0_eq hlen W₀ []]
    exact farU_of_midDoom _ _ _ _ _ _ _ hD

/-- `FinalDoomL` from the final level's `FinViol` (generic in the code). -/
theorem not_finalDoomL_of_not_finViol {P : LevelCode} {ℓ : ℕ} {Q' : (Fin ℓ → Bool) → Fin P.n → E}
    {α : Fin ℓ → E} {C : Fin P.n → E} {Φ : List E → E} {σ : E} {f : (Fin P.κ → Bool) → E}
    (hC : (fun _ : Fin 0 → Bool ↦ C) = foldAll α Q') (h : ¬ FinViol P C Φ σ f) :
    ¬ FinalDoomL P Q' α f := by
  simp only [FinViol, not_or, not_not] at h
  rw [hC] at h
  exact not_not.mpr h.2

/-- **The final residual's doom from the specification's** at `C_rec`'s level 1: with the
bookkeeping, not `ResC` gives not `FinalDoomL`. -/
theorem not_finalDoomL20 {w : List E → E} {r₁ : WhirStateT × List E} {res : List E} {W₀ W₁ : Compile.Word}
    {ht : ℕ} (hlen : r₁.2.length = 4) (hfl : r₁.1.folds.length = 10) (hgl : GluedOK 19 r₁.1)
    (hquad : QuadOK r₁.1.quad r₁.1.target) (hW₁ : WellShaped (3 * 2 ^ 4) W₁) (hht : ht = 12)
    (hres : res.length = 2 ^ (19 - r₁.1.folds.length))
    (hn : ¬ ResC 19 6 w 1 (codesRec20 1) 4 6 r₁ res [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)]) :
    ¬ FinalDoomL (codesRec20 1) (rows1 4 (codesRec20 1).n W₁) (fun i : Fin 4 ↦ r₁.2.getD i 0)
      (resMsg res) := by
  subst hht
  have hbook : res.length = 2 ^ (19 - r₁.1.folds.length) ∧
      FinBook 19 1 (codesRec20 1) 4 6 r₁ [(15, 64, W₀), (12, 3 * 2 ^ 4, W₁)] :=
    ⟨hres, ⟨by rw [hfl, hlen], by rw [hlen], rfl, hgl, hquad⟩, ⟨rfl, W₁, rfl, hW₁⟩, hlen⟩
  have hnv := not_finViol_of_not_resC hbook hn
  have e := foldedW1_eq hlen [(15, 64, W₀), (12, 3 * 2 ^ 4, W₁)]
  have hw1 : wordOf [(15, 64, W₀), (12, 3 * 2 ^ 4, W₁)] 1 = W₁ := rfl
  rw [hw1] at e
  exact not_finalDoomL_of_not_finViol e hnv

/-- No fold luck of a list from no luck by rounds (four rounds). -/
theorem not_foldAllLuck_of_not_rounds {ι : Type} [Fintype ι]
    {L : Finset ((Fin 4 → Bool) → ι → E)} {O : (Fin 4 → Bool) → ι → E} {α : List E}
    (hl : α.length = 4) (h : ¬ ∃ V ∈ L, RoundsLuck 4 α O V) :
    ∀ V ∈ L, ¬ FoldAllLuck (fun i : Fin 4 ↦ α.getD i 0) O V :=
  fun V hV hF ↦ h ⟨V, hV, roundsLuck_of_foldAllLuck 4 α O V hl hF⟩

/-! ## The decoder facts -/

/-- **The middle phases' shape** (structural facts of the concrete phases): no commitment, no
proof of work, and the claims on `C_rec` they return are multiaffine. -/
structure MidShape (mid : List UInt8 → VerifierProgram OpenClaims) : Prop where
  noCommit : ∀ x, (mid x).NoCommit
  noGrind : ∀ x, (mid x).NoGrind
  recAffine : ∀ x l cl, (mid x).after l = some (.ret cl) → ∀ c ∈ cl.1, IsMultiaffine 19 c.1

section Extract

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}
  {x : List UInt8}

/-- **The decoders' hypotheses** (lvm2 S4, the hand-off to the extractor): at an accepted,
reachable history of `P_S` outside the doom `psSpec ∨ resSpec ∨ midSpec1` at every boundary and not
lucky, there is a good candidate pair `(qm, qr)`, and the history's values (`recData2`: `r₀`, `r₁`,
the residual; `C_rec`'s words `WrOf h`, `Wr1Of h`) satisfy the hypotheses of `ud_extract_rec20` and
of both decoders: no commitment doom for `qr`, no level-1 doom, no final doom, no fold luck at
either level, well-shaped words. -/
theorem decodeFacts_S (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {h : List Ev} (hreach : (PSWith mid x).Reachable h)
    (hacc : (PSWith mid x).after h = some (.ret true)) (hB : ¬ LuckB mid x h)
    (hD : ∀ h', h' <+: h → Boundary h' → ¬ (SPS hmid hLm x).D [] h') :
    ∃ qm qr, Good x qm qr ∧ ∃ r r₁ res, recData2 mid x h = some (r, r₁, res) ∧
      r.2.length = 6 ∧ r₁.2.length = 4 ∧ WellShaped 64 (WrOf h) ∧ WellShaped 48 (Wr1Of h) ∧
      qr ∈ Candidates 19 2 (udThr 13 2) (WrOf h) ∧
      ¬ CommitDoomUd 19 2 (udThr 13 2) (· = qr) (WrOf h) ∧
      ¬ MidDoomUd (udThr 13 2) (codesRec20 1) (by rfl : 19 - EndToEnd.laneBits = 4 + (codesRec20 1).κ)
        (foldAll (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) (laneRows 19 2 (WrOf h)) Fin.elim0)
        (rows1 4 (codesRec20 1).n (Wr1Of h)) ∧
      ¬ FinalDoomL (codesRec20 1) (rows1 4 (codesRec20 1).n (Wr1Of h))
        (fun i : Fin 4 ↦ r₁.2.getD i 0) (resMsg res) ∧
      ¬ FoldAllLuck (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) (laneRows 19 2 (WrOf h))
        (encRows 19 2 qr) ∧
      ∀ V ∈ iList (codesRec20 1).code (codesRec20 1).thr (rows1 4 (codesRec20 1).n (Wr1Of h)),
        ¬ FoldAllLuck (fun i : Fin 4 ↦ r₁.2.getD i 0) (rows1 4 (codesRec20 1).n (Wr1Of h)) V := by
  obtain ⟨hr, lm, cl, ρ, lq, quad, lf, r, lc, lg, g, lhq, hq, lf1, r₁, lres, res, rest, rfl, h1, h3,
    h8, h10, hcm, hg, hh, hf1, hres⟩ := accept_split hacc
  have hrd := recData2_split (rest := rest) h1 h3 h8 h10 hcm hg hh hf1 hres
  have hfc0 := foldChal_split (rest := rest) h1 h3 h8 h10 hcm hg hh hf1 hres
  obtain ⟨W₁, hlc⟩ := readCommitment_after hcm
  have hfc1 := foldChal1_split (rest := rest) h1 h3 h8 h10 hcm hg hh hf1 hres hlc
  have hW1L := W1L_split (rest := rest) h1 h3 h8 h10 hcm hg hh hf1 hres hlc
  obtain ⟨Wm, W₀, rfl⟩ := roots_after h1
  subst hlc
  have hws := reachable_commit_ws hreach
  have hW₀ : WellShaped 64 W₀ := hws 15 64 W₀ (by simp)
  have hW₁ : WellShaped (3 * 2 ^ 4) W₁ := hws (19 - r.1.folds.length - 4 + 3) _ W₁ (by simp)
  -- the fold states
  obtain ⟨e1, e2, e3, e4, e5⟩ := foldRoundsT_after 6 _ [] h10
  rw [List.nil_append] at e1 e3
  have hlen6 : r.2.length = 6 := by rw [e1]; exact e2
  have hfl : r.1.folds.length = 6 := by rw [e3]; exact e2
  obtain ⟨f1, f2, f3, f4, f5⟩ := foldRoundsT_after 4 _ [] hf1
  rw [List.nil_append] at f1
  have hlen4 : r₁.2.length = 4 := by rw [f1]; exact f2
  have hfl1 : r₁.1.folds.length = 10 := by
    rw [f3, glueLv_folds, List.length_append, hfl, f2]
  have hgl0 : GluedOK 19 r.1 := fun c hc ↦ by rw [e4] at hc; simp at hc
  have hgl1 : GluedOK 19 r₁.1 :=
    gluedOK_of_folds (gluedOK_glueLv (i := 0) hgl0 _ _ _ _) f4 (by rw [f3]; simp)
  have hreslen : res.length = 2 ^ (19 - r₁.1.folds.length) := readScalars_after_len _ hres
  have hht : 19 - r.1.folds.length - 4 + 3 = 12 := by rw [hfl]
  -- the commitments
  have hcm' : commits lm = [] := NoCommit.after_commits (hsh.noCommit x) h3
  have hcq := NoCommit.after_commits (nc_roundPoly _ _ _) h8
  have hcf := NoCommit.after_commits (nc_foldRoundsT _ _ _) h10
  have hcg := NoCommit.after_commits (nc_qgRec _ _) hg
  have hch := NoCommit.after_commits (nc_roundPoly _ _ _) hh
  have hcf1 := NoCommit.after_commits (nc_foldRoundsT _ _ _) hf1
  have hcr := NoCommit.after_commits (nc_readScalars _) hres
  set ht := 19 - r.1.folds.length - 4 + 3 with hhtdef
  have hcsM : commits ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ lm ++ [Ev.sample ρ] ++ lq ++ lf ++
      [Ev.commit ht (3 * 2 ^ 4) W₁]) = [(19, 64, Wm), (15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] := by
    simp only [commits_append, hcm', hcq, hcf, List.append_nil]
    rfl
  have hcsR : commits ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ lm ++ [Ev.sample ρ] ++ lq ++ lf ++
      [Ev.commit ht (3 * 2 ^ 4) W₁] ++ lg ++ lhq ++ lf1 ++ lres) =
      [(19, 64, Wm), (15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] := by
    rw [commits_append, commits_append, commits_append, commits_append, hcsM, hcg, hch, hcf1, hcr]
    simp
  have hview : viewC 1 2 [(19, 64, Wm), (15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] =
      [(15, 64, W₀), (ht, 3 * 2 ^ 4, W₁)] := rfl
  have hWr : WrOf ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ (lm ++ ([Ev.sample ρ] ++ (lq ++
      (lf ++ ([Ev.commit ht (3 * 2 ^ 4) W₁] ++ (lg ++ (lhq ++ (lf1 ++ (lres ++ rest)))))))))) = W₀ := by
    unfold WrOf
    rw [rootsOf_split h1]
    rfl
  have hWr1 : Wr1Of ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ (lm ++ ([Ev.sample ρ] ++ (lq ++
      (lf ++ ([Ev.commit ht (3 * 2 ^ 4) W₁] ++ (lg ++ (lhq ++ (lf1 ++ (lres ++ rest)))))))))) = W₁ := by
    unfold Wr1Of
    have : [Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ (lm ++ ([Ev.sample ρ] ++ (lq ++
        (lf ++ ([Ev.commit ht (3 * 2 ^ 4) W₁] ++ (lg ++ (lhq ++ (lf1 ++ (lres ++ rest))))))))) =
        ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ lm ++ [Ev.sample ρ] ++ lq ++ lf ++
          [Ev.commit ht (3 * 2 ^ 4) W₁]) ++ (lg ++ (lhq ++ (lf1 ++ (lres ++ rest)))) := by
      simp only [List.append_assoc]
    rw [this, commits_append, hcsM]
    simp [wordOf]
  rw [hWr, hWr1]
  have hcl := hsh.recAffine x lm cl h3
  -- (1) a good candidate pair
  have hDr := hD [Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] (List.prefix_append _ _) (by
    simp [Boundary])
  have hRS : RootShape [Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] :=
    ⟨Wm, W₀, rfl, hws 19 64 Wm (by simp), hW₀⟩
  have hgood : ¬ CommitDoomS Good x [Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] := fun hc ↦
    hDr ((SPS_D hmid hLm x _ _).2 (.inl (.inl
      (psSpec_D_roots recCommitsOne hmid hLm x Wm W₀ ⟨hc, hRS⟩))))
  simp only [CommitDoomS, not_forall, not_not] at hgood
  obtain ⟨⟨qm, qr⟩, ⟨-, hqr⟩, hG⟩ := hgood
  have hqr' : qr ∈ Candidates 19 2 (udThr 13 2) W₀ := hqr
  -- (2) the level-1 commitment
  have hbM : Boundary ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ (lm ++ ([Ev.sample ρ] ++
      (lq ++ (lf ++ [Ev.commit ht (3 * 2 ^ 4) W₁]))))) :=
    boundary_of_last_commit (ht := ht) (w := 3 * 2 ^ 4) (W := W₁) (by
      simp only [← List.append_assoc]; exact List.getLast?_concat)
  have hDM := hD _ ⟨lg ++ (lhq ++ (lf1 ++ (lres ++ rest))), by simp⟩ hbM
  have hnF : ¬ FarC 19 6 (batW cl.1 ρ) 0 (codesRec20 0) (codesRec20 1) 6 4 0 hκ_rec20 r
      (viewC 1 2 (commits ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ lm ++ [Ev.sample ρ] ++ lq ++
        lf ++ [Ev.commit ht (3 * 2 ^ 4) W₁]))) := fun hF ↦
    hDM ((SPS_D hmid hLm x _ _).2 (.inr (midSpec1_D mid x h1 h3 hcl h8 h10 hcm hF)))
  rw [hcsM, hview] at hnF
  have hnM := fun hM ↦ hnF (farC_of_midDoom20 (w := batW cl.1 ρ) hlen6 hfl
    (by rw [e4]) (e5 (by norm_num)) hW₀ hW₁ hht hM)
  -- (3) the final residual
  have hne : lres ≠ [] := by
    intro he; subst he
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.two_pow_pos (19 - r₁.1.folds.length)).ne'
    rw [hn] at hres
    simp [readScalars, VerifierProgram.readScalar, VerifierProgram.bind, VerifierProgram.after] at hres
  have hlast : ∃ y, lres.getLast? = some (Ev.read y) := by
    obtain ⟨e, he⟩ := List.getLast?_isSome.2 hne |> Option.isSome_iff_exists.1
    obtain ⟨y, rfl⟩ := readScalars_reads _ hres e (List.mem_of_getLast? he)
    exact ⟨y, he⟩
  have hbR : Boundary ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ (lm ++ ([Ev.sample ρ] ++
      (lq ++ (lf ++ ([Ev.commit ht (3 * 2 ^ 4) W₁] ++ (lg ++ (lhq ++ (lf1 ++ lres))))))))) := by
    obtain ⟨y, hy⟩ := hlast
    refine boundary_of_last_read (y := y) ?_
    simp only [← List.append_assoc]
    rw [List.getLast?_append_of_ne_nil _ hne, hy]
  have hDR := hD _ ⟨rest, by simp [List.append_assoc]⟩ hbR
  have hnR : ¬ ResC 19 6 (batW cl.1 ρ) 1 (codesRec20 1) 4 6 r₁ res
      (viewC 1 2 (commits ([Ev.commit 19 64 Wm, Ev.commit 15 64 W₀] ++ lm ++ [Ev.sample ρ] ++ lq ++
        lf ++ [Ev.commit ht (3 * 2 ^ 4) W₁] ++ lg ++ lhq ++ lf1 ++ lres))) := fun hR ↦ by
    obtain ⟨_, lgp, lgq, hlg, hgp, hgq⟩ := after_bind_ret hg
    subst hlg
    apply hDR
    refine (SPS_D hmid hLm x _ _).2 (.inl (.inr ?_))
    have := resSpec_D mid x h1 h3 hcl h8 h10 hcm hgp hgq hh hf1 hres
      (by simpa only [List.append_assoc] using hR)
    simpa only [List.append_assoc] using this
  rw [hcsR, hview] at hnR
  have hnFD := not_finalDoomL20 hlen4 hfl1 hgl1 (f5 (by norm_num)) hW₁ hht hreslen hnR
  -- (4) no luck
  have hB0 : ¬ LuckB0 mid x _ := fun h' ↦ hB (.inl h')
  have hB1 : ¬ LuckB1 mid x _ := fun h' ↦ hB (.inr h')
  have hnl0 : ¬ FoldAllLuck (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) (laneRows 19 2 W₀)
      (encRows 19 2 qr) := by
    intro hFL
    apply hB0
    refine ⟨qr, ?_, ?_⟩
    · rw [hWr]; exact hqr
    · rw [hWr, hfc0]
      exact roundsLuck_of_foldAllLuck _ _ _ _ hlen6 hFL
  unfold LuckB1 at hB1
  rw [hW1L, hfc1] at hB1
  refine ⟨qm, qr, hG, r, r₁, res, hrd, hlen6, hlen4, hW₀, hW₁, hqr', fun hcd ↦ hcd qr hqr' rfl, hnM,
    hnFD, hnl0, not_foldAllLuck_of_not_rounds hlen4 hB1⟩

/-! ## The extraction map (O11) -/

/-- **The `S` branch's extraction map** (lvm2): DEC's level-1 decoder on `C_rec`'s level-1 word,
level-1 fold challenges and final residual, then WP-13b's level-0 decoder on the root word, the
level-0 fold challenges and the level-1 output; the witness with the decoded column's child. -/
noncomputable def extS (mid : List UInt8 → VerifierProgram OpenClaims)
    (child : Column 19 → Signed) (_c : RecursionFast.Digest) (x : List UInt8) (h : List Ev) : Wit :=
  witOf x (child (colOf ((recData2 mid x h).bind fun d ↦
    (Lvm.X.decodeRec1 (Lvm.X.wdOf (Wr1Of h)) (Lvm.X.alphaN1 fun i ↦ d.2.1.2.getD i 0)
        (Lvm.X.fN2 (resMsg d.2.2))).bind fun m ↦
      Lvm.X.decodeRec (Lvm.X.wdOf (WrOf h)) (Lvm.X.alphaN fun i ↦ d.1.2.getD i 0) m)))

open Classical in
/-- **The decoders succeed** (O11): at an accepted history of `P_S` outside the doom at every
boundary and not lucky, `C_rec`'s fold states and residual are read off the history, DEC's level-1
decoder returns a message `m`, and WP-13b's decoder on the root word, the level-0 fold challenges
and `m` returns the words of the candidate `q` of a good pair. -/
theorem decode_S (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {h : List Ev} (hreach : (PSWith mid x).Reachable h)
    (hacc : (PSWith mid x).after h = some (.ret true)) (hB : ¬ LuckB mid x h)
    (hD : ∀ h', h' <+: h → Boundary h' → ¬ (SPS hmid hLm x).D [] h') :
    ∃ qm q, Good x qm q ∧ ∃ r r₁ res, recData2 mid x h = some (r, r₁, res) ∧ ∃ m,
      Lvm.X.decodeRec1 (Lvm.X.wdOf (Wr1Of h)) (Lvm.X.alphaN1 fun i ↦ r₁.2.getD i 0)
        (Lvm.X.fN2 (resMsg res)) = some m ∧
      Lvm.X.decodeRec (Lvm.X.wdOf (WrOf h)) (Lvm.X.alphaN fun i ↦ r.2.getD i 0) m =
        some ((List.range (2 ^ 19)).map (Lvm.X.msgOf q)) := by
  obtain ⟨qm, qr, hG, r, r₁, res, hrd, -, -, hW₀, hW₁, hqr, hC, hM, hF, hl0, hl1⟩ :=
    decodeFacts_S hmid hLm hsh hreach hacc hB hD
  have hx := ud_extract_rec20 (· = qr) (WrOf h) (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0)
    (rows1 4 (codesRec20 1).n (Wr1Of h)) (fun i : Fin 4 ↦ r₁.2.getD i 0) (resMsg res) hC hM hF
  simp only [mem_iList] at hx hl1
  obtain ⟨q, hq, rfl, -, V, ⟨hcw, hcl⟩, -, hjoin, hf₂, -⟩ := hx
  have hdec1 := Lvm.X.decodeRec1_of_ud (Wr1Of h) (fun v _ ↦ hW₁ v)
    (fun i : Fin 4 ↦ r₁.2.getD i 0) (resMsg res) V hcw hcl hf₂ (hl1 V ⟨hcw, hcl⟩)
  rw [hjoin] at hdec1
  obtain ⟨q', hq', rfl, -, hdec⟩ := Lvm.X.decodeRec_of_ud_ws (· = q) (WrOf h)
    (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) (foldMsg (fun i : Fin EndToEnd.laneBits ↦ r.2.getD i 0) q) hW₀
    (fun hcd ↦ hcd q hq rfl) (not_finalDoomUd_foldMsg (by norm_num) hq _)
  exact ⟨qm, q', hG, r, r₁, res, hrd, _, hdec1, hdec hl0⟩

/-- **The extraction is a witness** (O11): at an accepted history of `P_S` outside the doom at
every boundary and not lucky, `extS` gives a witness of the relation. -/
theorem extract_S (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {VS : SProg} {vk : RecursionFast.Digest} {child : Column 19 → Signed}
    (hnode : NodeSound VS vk Good child) {c : RecursionFast.Digest} {h : List Ev}
    (hok : okS vk c x = true) (hreach : (PSWith mid x).Reachable h)
    (hacc : (PSWith mid x).after h = some (.ret true)) (hB : ¬ LuckB mid x h)
    (hD : ∀ h', h' <+: h → Boundary h' → ¬ (SPS hmid hLm x).D [] h') :
    Rel (accV VS vk) c (extS mid child c x h) := by
  obtain ⟨qm, q, hG, r, r₁, res, hrd, m, hdec1, hdec⟩ := decode_S hmid hLm hsh hreach hacc hB hD
  unfold extS
  rw [hrd, Option.bind_some]
  dsimp only
  rw [hdec1, Option.bind_some, hdec, colOf_msgOf]
  exact hnode c x qm q hok hG

end Extract

/-! ## The knowledge certificate of the `S` branch (O5a, `mid` abstract) -/

section KCert

variable {mid : List UInt8 → VerifierProgram OpenClaims} {Good : GoodRel} {Lm : ℝ≥0∞}

theorem coe_εS : ((7 * (2 : ℝ≥0)⁻¹ ^ 131 : ℝ≥0) : ℝ≥0∞) = εS := by
  rw [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat, ENNReal.coe_ofNat]

theorem coe_εB : (((2 : ℝ≥0)⁻¹ ^ 132 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ ^ 132 := by
  rw [ENNReal.coe_pow, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]

/-- `P_S`'s specification at the certificate's `ε = εS = 7·2^-131` (as `ℝ≥0`). -/
noncomputable def SPSε (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    Spec (PSWith mid x) (fun _ ↦ False) (fun b _ ↦ b = false)
      (((7 * (2 : ℝ≥0)⁻¹ ^ 131 : ℝ≥0)) : ℝ≥0∞) 0 0 :=
  (SPS hmid hLm x).mono (fun _ h ↦ h) (fun _ _ h ↦ h) coe_εS.ge le_rfl le_rfl

/-- The luck and the extraction of the `S` branch. -/
noncomputable def luckExtS (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {VS : SProg} {vk : RecursionFast.Digest} {child : Column 19 → Signed}
    (hnode : NodeSound VS vk Good child) :
    LuckExt (schemeS vk (PSWith mid)) (Rel (accV VS vk)) fun x ↦ (SPSε hmid hLm x).D [] where
  B := LuckB mid
  εB := (2 : ℝ≥0)⁻¹ ^ 132
  εB_lt_one := pow_lt_one₀ (by positivity) (by norm_num) (by norm_num)
  B_nil _ := LuckB_nil
  B_read _ _ _ hB := not_luckB_snoc rfl hB
  B_commit _ _ _ _ hB := not_luckB_snoc rfl hB
  B_group {x h p} _ _ _ _ hB := by
    refine (esc_luck_le p h hB).trans ?_
    rw [coe_εB]
    refine le_trans ?_ ten_δL_le
    gcongr
    exact_mod_cast (show (6 - (foldChal mid x h).length) + (4 - (foldChal1 mid x h).length) ≤ 10
      by omega)
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
    (fun x hD ↦ (SPS_D_nil hmid hLm x hD).elim)
    (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num)
    (fun x _ hr ↦ NoGrind.reach_grindBits (ng_PSWith hsh.noGrind x) hr) (luckExtS hmid hLm hsh hnode)

/-- **Its error**: `εFS ≤ 2^-128`. -/
theorem εFS_kcertS (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (hsh : MidShape mid)
    {VS : SProg} {vk : RecursionFast.Digest} {child : Column 19 → Signed}
    (hnode : NodeSound VS vk Good child) :
    Scheme.εFS (kcertS hmid hLm hsh hnode) ≤ (2 : ℝ≥0)⁻¹ ^ 128 :=
  εFS_kcertOfSpec _ _ _ _ _ le_rfl le_rfl

end KCert

end Lvm.ASM
