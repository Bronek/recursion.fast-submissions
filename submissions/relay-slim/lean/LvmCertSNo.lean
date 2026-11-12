-- WP-14 (ASM). New for lvm: the structural facts O7a (`C_rec`'s opening commits exactly its level-1
-- oracle; lvm2 S4, was "nothing" at one level) and O7b (`P_S` asks no proof of work), by induction on
-- WP-7's UD programs (`LvmWhirProg`).
import LvmCertSOpen

/-!
# `C_rec`'s opening commits one word, and `P_S` grinds nowhere

* `CommitsN p n`: every completed run of `p` commits exactly `n` words (`CommitsN.after_ret`).
  `commitsN_stacked_two`: a two-level stacked opening commits one (its level-1 oracle; the final
  level reads the residual); **`recCommitsOne`** (O7a, `RecCommitsOne`).
* `noGrind_stacked`: every stacked UD opening asks no proof of work; `noGrind_PSWith`: neither does
  `P_S` when its middle phases do not; `NoGrind.reach_grindBits`: a reachable history of a program
  with no proof of work ends in no grind (`grindBits = 0`, the `hng` of `kcertOfSpec`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound

variable {α β : Type}

/-! ## Leaves -/

theorem nc_sample : (sampleChallenge : VerifierProgram E).NoCommit := fun _ ↦ trivial
theorem ng_sample : (sampleChallenge : VerifierProgram E).NoGrind := fun _ ↦ trivial
theorem nc_readScalar : (readScalar : VerifierProgram E).NoCommit := fun _ ↦ trivial
theorem ng_readScalar : (readScalar : VerifierProgram E).NoGrind := fun _ ↦ trivial
theorem nc_query (i : ℕ) (ps : List ℕ) : (queryOpenings i ps).NoCommit := fun _ ↦ trivial
theorem ng_query (i : ℕ) (ps : List ℕ) : (queryOpenings i ps).NoGrind := fun _ ↦ trivial
theorem ng_commit (ht w : ℕ) : (readCommitment ht w).NoGrind := trivial
theorem nc_ret (a : α) : (VerifierProgram.ret a).NoCommit := trivial
theorem ng_ret (a : α) : (VerifierProgram.ret a).NoGrind := trivial

theorem nc_readScalars : ∀ n, (readScalars n).NoCommit
  | 0 => trivial
  | n + 1 => NoCommit.bind nc_readScalar fun _ ↦ NoCommit.bind (nc_readScalars n) fun _ ↦ nc_ret _

theorem ng_readScalars : ∀ n, (readScalars n).NoGrind
  | 0 => trivial
  | n + 1 => NoGrind.bind ng_readScalar fun _ ↦ NoGrind.bind (ng_readScalars n) fun _ ↦ ng_ret _

theorem nc_roundPoly (c : ℕ) (t : E) :
    ∀ e, (LeanVM.Protocol.Verifier.sumcheckRoundPoly c t e).NoCommit
  | none => by
    unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly
    exact NoCommit.bind nc_readScalar fun _ ↦ NoCommit.bind (nc_readScalars _) fun _ ↦ nc_ret _
  | some _ => by
    unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly
    exact NoCommit.bind (nc_readScalars _) fun _ ↦ nc_ret _

theorem ng_roundPoly (c : ℕ) (t : E) :
    ∀ e, (LeanVM.Protocol.Verifier.sumcheckRoundPoly c t e).NoGrind
  | none => by
    unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly
    exact NoGrind.bind ng_readScalar fun _ ↦ NoGrind.bind (ng_readScalars _) fun _ ↦ ng_ret _
  | some _ => by
    unfold LeanVM.Protocol.Verifier.sumcheckRoundPoly
    exact NoGrind.bind (ng_readScalars _) fun _ ↦ ng_ret _

theorem nc_foldRoundsT : ∀ n s lf, (foldRoundsT n s lf).NoCommit
  | 0, _, _ => trivial
  | n + 1, _, _ => NoCommit.bind nc_sample fun _ ↦
      NoCommit.bind (nc_roundPoly _ _ _) fun _ ↦ nc_foldRoundsT n _ _

theorem ng_foldRoundsT : ∀ n s lf, (foldRoundsT n s lf).NoGrind
  | 0, _, _ => trivial
  | n + 1, _, _ => NoGrind.bind ng_sample fun _ ↦
      NoGrind.bind (ng_roundPoly _ _ _) fun _ ↦ ng_foldRoundsT n _ _

theorem nc_tailRoundsT : ∀ n t q, (tailRoundsT n t q).NoCommit
  | 0, _, _ => trivial
  | n + 1, _, _ => NoCommit.bind nc_sample fun _ ↦ by
      split
      · trivial
      · exact NoCommit.bind (nc_roundPoly _ _ _) fun _ ↦
          NoCommit.bind (nc_tailRoundsT n _ _) fun _ ↦ nc_ret _

theorem ng_tailRoundsT : ∀ n t q, (tailRoundsT n t q).NoGrind
  | 0, _, _ => trivial
  | n + 1, _, _ => NoGrind.bind ng_sample fun _ ↦ by
      split
      · trivial
      · exact NoGrind.bind (ng_roundPoly _ _ _) fun _ ↦
          NoGrind.bind (ng_tailRoundsT n _ _) fun _ ↦ ng_ret _

theorem nc_samplePositionsAux (per depth : ℕ) : ∀ fuel rem, (samplePositionsAux per depth fuel rem).NoCommit
  | 0, _ => trivial
  | fuel + 1, rem => by
    unfold samplePositionsAux
    split
    · trivial
    · exact NoCommit.bind nc_sample fun _ ↦
        NoCommit.bind (nc_samplePositionsAux per depth fuel _) fun _ ↦ nc_ret _

theorem ng_samplePositionsAux (per depth : ℕ) : ∀ fuel rem, (samplePositionsAux per depth fuel rem).NoGrind
  | 0, _ => trivial
  | fuel + 1, rem => by
    unfold samplePositionsAux
    split
    · trivial
    · exact NoGrind.bind ng_sample fun _ ↦
        NoGrind.bind (ng_samplePositionsAux per depth fuel _) fun _ ↦ ng_ret _

theorem nc_require (c : Prop) [Decidable c] : (require c).NoCommit := by
  unfold require; split <;> trivial

theorem ng_require (c : Prop) [Decidable c] : (require c).NoGrind := by
  unfold require; split <;> trivial

theorem nc_samplePositions (per depth count : ℕ) : (samplePositions per depth count).NoCommit :=
  nc_samplePositionsAux _ _ _ _

theorem ng_samplePositions (per depth count : ℕ) : (samplePositions per depth count).NoGrind :=
  ng_samplePositionsAux _ _ _ _

/-- The separating challenge and the nonce (PI-GRIND) ask no proof of work and commit nothing. -/
theorem ng_grindPre (g : ℕ) : (grindPre g).NoGrind := by
  unfold grindPre; split
  · trivial
  · exact NoGrind.bind ng_sample fun _ ↦ NoGrind.bind ng_readScalar fun _ ↦ ng_ret _

theorem nc_grindPre (g : ℕ) : (grindPre g).NoCommit := by
  unfold grindPre; split
  · trivial
  · exact NoCommit.bind nc_sample fun _ ↦ NoCommit.bind nc_readScalar fun _ ↦ nc_ret _

/-- The proof of work's challenge and check (PI-GRIND): no `grind` node, no commitment. -/
theorem ng_powCheck (g : ℕ) : (powCheck g).NoGrind := by
  unfold powCheck; split
  · trivial
  · exact NoGrind.bind ng_sample fun _ ↦ ng_require _

theorem nc_powCheck (g : ℕ) : (powCheck g).NoCommit := by
  unfold powCheck; split
  · trivial
  · exact NoCommit.bind nc_sample fun _ ↦ nc_require _

/-! ## The level loop -/

theorem ng_whirLevelsUd (logN lf per c₀ n₀ g : ℕ) (dir : Bool) (eb : List E → E) :
    ∀ (levels : List LeanVM.Parameters.Whir.Level) i s,
      (whirLevelsUd logN lf per c₀ n₀ g dir eb i levels s).NoGrind
  | [], _, _ => trivial
  | [level], i, s => by
    unfold whirLevelsUd
    refine NoGrind.bind (ng_foldRoundsT _ _ _) fun r ↦ ?_
    rcases r with ⟨s', lf'⟩
    dsimp only
    refine NoGrind.bind (ng_readScalars _) fun res ↦ ?_
    refine NoGrind.bind (ng_grindPre _) fun _ ↦ ?_
    refine NoGrind.bind (ng_powCheck _) fun _ ↦ ?_
    refine NoGrind.bind (ng_samplePositions _ _ _) fun qs ↦ ?_
    refine NoGrind.bind ng_sample fun lam ↦ ?_
    refine NoGrind.bind (ng_query _ _) fun words ↦ ?_
    refine NoGrind.bind (ng_roundPoly _ _ _) fun intro ↦ ?_
    refine NoGrind.bind ?_ fun _ ↦ ?_
    · split
      · exact ng_require _
      · exact trivial
    refine NoGrind.bind (ng_tailRoundsT _ _ _) fun x ↦ ?_
    rcases x with ⟨tf, t⟩
    exact ng_require _
  | level :: next :: rest, i, s => by
    unfold whirLevelsUd
    refine NoGrind.bind (ng_foldRoundsT _ _ _) fun r ↦ ?_
    rcases r with ⟨s', lf'⟩
    dsimp only
    refine NoGrind.bind (ng_commit _ _) fun _ ↦ ?_
    refine NoGrind.bind (ng_ret _) fun res ↦ ?_
    refine NoGrind.bind (ng_grindPre _) fun _ ↦ ?_
    refine NoGrind.bind (ng_powCheck _) fun _ ↦ ?_
    refine NoGrind.bind (ng_samplePositions _ _ _) fun qs ↦ ?_
    refine NoGrind.bind ng_sample fun lam ↦ ?_
    refine NoGrind.bind (ng_query _ _) fun words ↦ ?_
    refine NoGrind.bind (ng_roundPoly _ _ _) fun intro ↦ ?_
    exact ng_whirLevelsUd logN lf per c₀ n₀ g dir eb (next :: rest) (i + 1) _

theorem ng_sampleChallengesN : ∀ n, (VerifierProgram.sampleChallenges n).NoGrind
  | 0 => trivial
  | n + 1 => by
    unfold VerifierProgram.sampleChallenges
    exact NoGrind.bind ng_sample fun _ ↦ NoGrind.bind (ng_sampleChallengesN n) fun _ ↦ ng_ret _

/-- **The level loop with OOD samples asks no proof of work** beyond PI-GRIND's (lvm2 JB-VQP). -/
theorem ng_whirLevelsJ (logN lf per c₀ n₀ g : ℕ) (dir : Bool) (eb : List E → E) :
    ∀ (levels : List LeanVM.Parameters.Whir.Level) i s,
      (whirLevelsJ logN lf per c₀ n₀ g dir eb i levels s).NoGrind
  | [], _, _ => trivial
  | [level], i, s => by
    rw [whirLevelsJ_one]
    exact ng_whirLevelsUd logN lf per c₀ n₀ g dir eb [level] i s
  | level :: next :: rest, i, s => by
    unfold whirLevelsJ
    refine NoGrind.bind (ng_foldRoundsT _ _ _) fun r ↦ ?_
    rcases r with ⟨s', lf'⟩
    dsimp only
    refine NoGrind.bind (ng_commit _ _) fun _ ↦ ?_
    refine NoGrind.bind (ng_sampleChallengesN _) fun _ ↦ ?_
    refine NoGrind.bind ng_readScalar fun _ ↦ ?_
    refine NoGrind.bind (ng_roundPoly _ _ _) fun _ ↦ ?_
    refine NoGrind.bind (ng_grindPre _) fun _ ↦ ?_
    refine NoGrind.bind (ng_powCheck _) fun _ ↦ ?_
    refine NoGrind.bind (ng_samplePositions _ _ _) fun qs ↦ ?_
    refine NoGrind.bind ng_sample fun lam ↦ ?_
    refine NoGrind.bind (ng_query _ _) fun words ↦ ?_
    refine NoGrind.bind (ng_roundPoly _ _ _) fun intro ↦ ?_
    exact ng_whirLevelsJ logN lf per c₀ n₀ g dir eb (next :: rest) (i + 1) _

/-- The one-level loop commits nothing (the residual is read, no next oracle). -/
theorem nc_whirLevelsUd_one (logN lf per c₀ n₀ g : ℕ) (dir : Bool) (eb : List E → E)
    (level : LeanVM.Parameters.Whir.Level) (i : ℕ) (s : WhirStateT) :
    (whirLevelsUd logN lf per c₀ n₀ g dir eb i [level] s).NoCommit := by
  unfold whirLevelsUd
  refine NoCommit.bind (nc_foldRoundsT _ _ _) fun r ↦ ?_
  rcases r with ⟨s', lf'⟩
  dsimp only
  refine NoCommit.bind (nc_readScalars _) fun res ↦ ?_
  refine NoCommit.bind (nc_grindPre _) fun _ ↦ ?_
  refine NoCommit.bind (nc_powCheck _) fun _ ↦ ?_
  refine NoCommit.bind (nc_samplePositions _ _ _) fun qs ↦ ?_
  refine NoCommit.bind nc_sample fun lam ↦ ?_
  refine NoCommit.bind (nc_query _ _) fun words ↦ ?_
  refine NoCommit.bind (nc_roundPoly _ _ _) fun intro ↦ ?_
  refine NoCommit.bind ?_ fun _ ↦ ?_
  · split
    · exact nc_require _
    · exact trivial
  refine NoCommit.bind (nc_tailRoundsT _ _ _) fun x ↦ ?_
  rcases x with ⟨tf, t⟩
  exact nc_require _

/-! ## The stacked openings -/

theorem ng_stacked (cfg : UdConfig) (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    (verifyStackedUd cfg cl).NoGrind := by
  unfold verifyStackedUd verifyWhirUd
  exact NoGrind.bind ng_sample fun _ ↦
    NoGrind.bind (ng_roundPoly _ _ _) fun _ ↦ ng_whirLevelsUd _ _ _ _ _ _ _ _ _ _ _

/-- The stacked opening with OOD samples (`verifyStackedJ`) asks no proof of work beyond PI-GRIND's. -/
theorem ng_stackedJ (cfg : WhirConfig) (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    (verifyStackedJ cfg cl).NoGrind := by
  unfold verifyStackedJ verifyWhirJ
  refine NoGrind.bind ng_sample fun _ ↦ ?_
  split
  · exact NoGrind.bind (ng_roundPoly _ _ _) fun _ ↦ ng_whirLevelsJ _ _ _ _ _ _ _ _ _ _ _
  · unfold verifyWhirUd
    exact NoGrind.bind (ng_roundPoly _ _ _) fun _ ↦ ng_whirLevelsUd _ _ _ _ _ _ _ _ _ _ _

/-- A one-level stacked opening commits nothing (generic in the configuration, so that no
concrete program is unfolded). -/
theorem nc_stacked_one (cfg : UdConfig) (level : LeanVM.Parameters.Whir.Level)
    (hc : cfg.levels = [level]) (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    (verifyStackedUd cfg cl).NoCommit := by
  rw [verifyStackedUd_eq]
  refine NoCommit.bind nc_sample fun ρ ↦ ?_
  rw [verifyWhirUd_eq hc]
  exact NoCommit.bind (nc_roundPoly _ _ _) fun _ ↦ nc_whirLevelsUd_one _ _ _ _ _ _ _ _ _ _ _

/-! ## Commitment counts (lvm2, S4) -/

end Lvm.ASM

namespace LeanVM.Protocol.Compile.VerifierProgram

variable {α β : Type}

/-- **Every completed run of `p` commits exactly `n` words.** -/
def CommitsN : VerifierProgram α → ℕ → Prop
  | .ret _, n => n = 0
  | .fail, _ => True
  | .read k, n => ∀ x, CommitsN (k x) n
  | .sample k, n => ∀ c, CommitsN (k c) n
  | .grind _ k, n => CommitsN k n
  | .commit _ _ _, 0 => False
  | .commit _ _ k, n + 1 => CommitsN k n
  | .query _ _ k, n => ∀ r, CommitsN (k r) n

theorem CommitsN.bind {p : VerifierProgram α} {f : α → VerifierProgram β} {m n : ℕ}
    (hp : p.CommitsN m) (hf : ∀ a, (f a).CommitsN n) : (p.bind f).CommitsN (m + n) := by
  induction p generalizing m with
  | ret a =>
    have hm : m = 0 := hp
    subst hm; rw [Nat.zero_add]; exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit ht w k ih =>
    cases m with
    | zero => exact hp.elim
    | succ m =>
      rw [show m + 1 + n = (m + n) + 1 by omega]
      exact ih hp
  | query i ps k ih => exact fun r ↦ ih r (hp r)

theorem CommitsN.bind' {p : VerifierProgram α} {f : α → VerifierProgram β} {m n k : ℕ}
    (hp : p.CommitsN m) (hf : ∀ a, (f a).CommitsN n) (hk : m + n = k) : (p.bind f).CommitsN k :=
  hk ▸ CommitsN.bind hp hf

theorem CommitsN.of_noCommit {p : VerifierProgram α} (hp : p.NoCommit) : p.CommitsN 0 := by
  induction p with
  | ret a => rfl
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact (hp : False).elim
  | query i ps k ih => exact fun r ↦ ih r (hp r)

/-- **A completed run of `p` commits `n` words.** -/
theorem CommitsN.after_ret {p : VerifierProgram α} {n : ℕ} {l : List Ev} {a : α}
    (hp : p.CommitsN n) (h : p.after l = some (.ret a)) : (commits l).length = n := by
  induction l generalizing p n with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq] at h
    subst h
    exact (hp : n = 0).symm
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at h
    · exact ih (hp _) h
    · exact ih (hp _) h
    · split_ifs at h
      refine ih ?_ h; exact hp
    · split_ifs at h
      cases n with
      | zero => exact (hp : False).elim
      | succ n =>
        simp only [commits, List.length_cons, Nat.add_right_cancel_iff]
        refine ih ?_ h; exact hp
    · exact ih (hp _) h

end LeanVM.Protocol.Compile.VerifierProgram

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound

variable {α β : Type}

theorem cn_commit (ht w : ℕ) : (readCommitment ht w).CommitsN 1 := rfl

/-- A level with a next level, followed by a final level: one commitment. -/
theorem commitsN_whirLevelsUd_two (logN lf per c₀ n₀ g : ℕ) (dir : Bool) (eb : List E → E)
    (level next : LeanVM.Parameters.Whir.Level) (i : ℕ) (s : WhirStateT) :
    (whirLevelsUd logN lf per c₀ n₀ g dir eb i [level, next] s).CommitsN 1 := by
  rw [whirLevels_mid]
  refine CommitsN.bind' (CommitsN.of_noCommit (nc_foldRoundsT _ _ _)) (fun r ↦ ?_) (Nat.zero_add 1)
  refine CommitsN.bind' (cn_commit _ _) (fun _ ↦ ?_) (Nat.add_zero 1)
  refine CommitsN.bind' (CommitsN.of_noCommit (nc_grindPre _)) (fun _ ↦ ?_) (Nat.zero_add 0)
  refine CommitsN.bind' (CommitsN.of_noCommit (nc_powCheck _)) (fun _ ↦ ?_) (Nat.zero_add 0)
  refine CommitsN.bind' (CommitsN.of_noCommit (nc_samplePositions _ _ _)) (fun qs ↦ ?_)
    (Nat.zero_add 0)
  refine CommitsN.bind' (CommitsN.of_noCommit nc_sample) (fun lam ↦ ?_) (Nat.zero_add 0)
  refine CommitsN.bind' (CommitsN.of_noCommit (nc_query _ _)) (fun words ↦ ?_) (Nat.zero_add 0)
  refine CommitsN.bind' (CommitsN.of_noCommit (nc_roundPoly _ _ _)) (fun hq ↦ ?_) (Nat.zero_add 0)
  exact CommitsN.of_noCommit (nc_whirLevelsUd_one _ _ _ _ _ _ _ _ _ _ _)

/-- **A two-level stacked opening commits one word** (generic in the configuration, so that no
concrete program is unfolded). -/
theorem commitsN_stacked_two (cfg : UdConfig) (level next : LeanVM.Parameters.Whir.Level)
    (hc : cfg.levels = [level, next]) (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    (verifyStackedUd cfg cl).CommitsN 1 := by
  rw [verifyStackedUd_eq]
  refine CommitsN.bind' (CommitsN.of_noCommit nc_sample) (fun ρ ↦ ?_) (Nat.zero_add 1)
  rw [verifyWhirUd_eq hc]
  exact CommitsN.bind' (CommitsN.of_noCommit (nc_roundPoly _ _ _))
    (fun _ ↦ commitsN_whirLevelsUd_two _ _ _ _ _ _ _ _ _ _ _ _) (Nat.zero_add 1)

/-! ## The concrete openings (kept folded: unfolding a P20 opening is expensive) -/

section Concrete

attribute [local irreducible] verifyStackedUd verifyStackedJ

/-- `C_rec`'s levels at P20 (lvm2 S4 on S2J): `(6, 2, 170)`, `(4, 3, 139)`. -/
theorem rec20_levels2 : cfgRec20G.levels = [⟨6, 2, 170⟩, ⟨4, 3, 139⟩] := rfl

/-- **`C_rec`'s opening commits one word.** -/
theorem commitsN_stackedRec (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    (verifyStackedUd cfgRec20G cl).CommitsN 1 :=
  commitsN_stacked_two cfgRec20G _ _ rec20_levels2 cl

/-- **O7a**: every completed run of `C_rec`'s two-level opening commits exactly one word. -/
theorem recCommitsOne : RecCommitsOne := fun cl _ _ hl ↦ (commitsN_stackedRec cl).after_ret hl

theorem ng_commitRootUd (cfg : UdConfig) : (commitRootUd cfg).NoGrind := by
  unfold commitRootUd; split
  · exact trivial
  · exact ng_commit _ _

theorem ng_seq2 {p q : VerifierProgram Unit} (hp : p.NoGrind) (hq : q.NoGrind) :
    (p >>= fun _ ↦ q >>= fun _ ↦ VerifierProgram.ret true).NoGrind :=
  NoGrind.bind hp fun _ ↦ NoGrind.bind hq fun _ ↦ ng_ret _

theorem ng_openProg (cl : OpenClaims) : (openProg cl).NoGrind :=
  ng_seq2 (ng_stacked cfgRec20G cl.1) (ng_stackedJ (cfgMain24J 3) cl.2)

theorem ng_seq3 {p q : VerifierProgram Unit} {m : VerifierProgram OpenClaims}
    {o : OpenClaims → VerifierProgram Bool} (hp : p.NoGrind) (hq : q.NoGrind) (hm : m.NoGrind)
    (ho : ∀ cl, (o cl).NoGrind) : ((p >>= fun _ ↦ q) >>= fun _ ↦ m >>= o).NoGrind :=
  NoGrind.bind (NoGrind.bind hp fun _ ↦ hq) fun _ ↦ NoGrind.bind hm ho

/-- **`P_S` asks no proof of work** when its middle phases do not. -/
theorem ng_PSWith {mid : List UInt8 → VerifierProgram OpenClaims} (hm : ∀ x, (mid x).NoGrind)
    (x : List UInt8) : (PSWith mid x).NoGrind := by
  rw [PSWith_eq]
  exact ng_seq3 (ng_commitRootUd cfgMain24G) (ng_commitRootUd cfgRec20G) (hm x) ng_openProg

end Concrete

/-- A reachable history of a program with no proof of work has no grind event. -/
theorem NoGrind.reach_noGrind {p : VerifierProgram α} (hp : p.NoGrind) {h : List Ev}
    (hr : p.Reachable h) : ∀ e ∈ h, ∀ b, e ≠ Ev.grind b := by
  induction hr with
  | nil => simp
  | read x _ _ ih | sample x _ _ ih =>
    intro e he b; rcases List.mem_append.1 he with he | he
    · exact ih e he b
    · simp at he; subst he; simp
  | query _ _ _ ih =>
    intro e he b; rcases List.mem_append.1 he with he | he
    · exact ih e he b
    · simp at he; subst he; simp
  | commit word _ _ _ ih =>
    intro e he b; rcases List.mem_append.1 he with he | he
    · exact ih e he b
    · simp at he; subst he; simp
  | grind _ ha _ => exact ((hp.after ha) : False).elim

/-- **`hng`**: a reachable history of a program with no proof of work ends in no grind. -/
theorem NoGrind.reach_grindBits {p : VerifierProgram α} (hp : p.NoGrind) {h : List Ev}
    (hr : p.Reachable h) : grindBits h = 0 := by
  have hn := NoGrind.reach_noGrind hp hr
  unfold grindBits
  split
  · rename_i b hb
    exact absurd rfl (hn _ (List.mem_of_getLast? hb) b)
  · rfl

end Lvm.ASM
