-- WP-14 (ASM). New for lvm: the structural facts O7a (`C_rec`'s opening commits nothing) and O7b
-- (`P_S` asks no proof of work), by induction on WP-7's UD programs (`LvmWhirProg`).
import LvmCertSOpen

/-!
# `P_S` commits nothing after its roots in `C_rec`'s opening, and grinds nowhere

* `noCommit_stackedRec`: `verifyStackedUd cfgRec20 cl` commits nothing (one level: the residual is
  read, no next commitment); **`recNoCommit`** (O7a, `RecNoCommit`).
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

/-! ## The level loop -/

theorem ng_whirLevelsUd (logN lf per c₀ n₀ : ℕ) (dir : Bool) (eb : List E → E) :
    ∀ (levels : List LeanVM.Parameters.Whir.Level) i s,
      (whirLevelsUd logN lf per c₀ n₀ dir eb i levels s).NoGrind
  | [], _, _ => trivial
  | [level], i, s => by
    unfold whirLevelsUd
    refine NoGrind.bind (ng_foldRoundsT _ _ _) fun r ↦ ?_
    rcases r with ⟨s', lf'⟩
    dsimp only
    refine NoGrind.bind (ng_readScalars _) fun res ↦ ?_
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
    refine NoGrind.bind (ng_samplePositions _ _ _) fun qs ↦ ?_
    refine NoGrind.bind ng_sample fun lam ↦ ?_
    refine NoGrind.bind (ng_query _ _) fun words ↦ ?_
    refine NoGrind.bind (ng_roundPoly _ _ _) fun intro ↦ ?_
    exact ng_whirLevelsUd logN lf per c₀ n₀ dir eb (next :: rest) (i + 1) _

/-- The one-level loop commits nothing (the residual is read, no next oracle). -/
theorem nc_whirLevelsUd_one (logN lf per c₀ n₀ : ℕ) (dir : Bool) (eb : List E → E)
    (level : LeanVM.Parameters.Whir.Level) (i : ℕ) (s : WhirStateT) :
    (whirLevelsUd logN lf per c₀ n₀ dir eb i [level] s).NoCommit := by
  unfold whirLevelsUd
  refine NoCommit.bind (nc_foldRoundsT _ _ _) fun r ↦ ?_
  rcases r with ⟨s', lf'⟩
  dsimp only
  refine NoCommit.bind (nc_readScalars _) fun res ↦ ?_
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
    NoGrind.bind (ng_roundPoly _ _ _) fun _ ↦ ng_whirLevelsUd _ _ _ _ _ _ _ _ _ _

/-- A one-level stacked opening commits nothing (generic in the configuration, so that no
concrete program is unfolded). -/
theorem nc_stacked_one (cfg : UdConfig) (level : LeanVM.Parameters.Whir.Level)
    (hc : cfg.levels = [level]) (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    (verifyStackedUd cfg cl).NoCommit := by
  rw [verifyStackedUd_eq]
  refine NoCommit.bind nc_sample fun ρ ↦ ?_
  rw [verifyWhirUd_eq hc]
  exact NoCommit.bind (nc_roundPoly _ _ _) fun _ ↦ nc_whirLevelsUd_one _ _ _ _ _ _ _ _ _ _

/-! ## The concrete openings (kept folded: unfolding a P20 opening is expensive) -/

section Concrete

attribute [local irreducible] verifyStackedUd

/-- **`C_rec`'s opening commits nothing.** -/
theorem nc_stackedRec (cl : List LeanVM.Protocol.Verifier.StackClaim) :
    (verifyStackedUd cfgRec20 cl).NoCommit :=
  nc_stacked_one cfgRec20 ⟨6, 2, 191⟩ rfl cl

/-- **O7a**: `C_rec`'s one-level opening commits nothing. -/
theorem recNoCommit : RecNoCommit := fun cl _ _ hl ↦ (nc_stackedRec cl).reach_commits hl

theorem ng_commitRootUd (cfg : UdConfig) : (commitRootUd cfg).NoGrind := by
  unfold commitRootUd; split
  · exact trivial
  · exact ng_commit _ _

theorem ng_seq2 {p q : VerifierProgram Unit} (hp : p.NoGrind) (hq : q.NoGrind) :
    (p >>= fun _ ↦ q >>= fun _ ↦ VerifierProgram.ret true).NoGrind :=
  NoGrind.bind hp fun _ ↦ NoGrind.bind hq fun _ ↦ ng_ret _

theorem ng_openProg (cl : OpenClaims) : (openProg cl).NoGrind :=
  ng_seq2 (ng_stacked cfgRec20 cl.1) (ng_stacked cfgMain20 cl.2)

theorem ng_seq3 {p q : VerifierProgram Unit} {m : VerifierProgram OpenClaims}
    {o : OpenClaims → VerifierProgram Bool} (hp : p.NoGrind) (hq : q.NoGrind) (hm : m.NoGrind)
    (ho : ∀ cl, (o cl).NoGrind) : ((p >>= fun _ ↦ q) >>= fun _ ↦ m >>= o).NoGrind :=
  NoGrind.bind (NoGrind.bind hp fun _ ↦ hq) fun _ ↦ NoGrind.bind hm ho

/-- **`P_S` asks no proof of work** when its middle phases do not. -/
theorem ng_PSWith {mid : List UInt8 → VerifierProgram OpenClaims} (hm : ∀ x, (mid x).NoGrind)
    (x : List UInt8) : (PSWith mid x).NoGrind := by
  rw [PSWith_eq]
  exact ng_seq3 (ng_commitRootUd cfgMain20) (ng_commitRootUd cfgRec20) (hm x) ng_openProg

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
