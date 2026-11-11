-- WP-14 (ASM). New for lvm: the specifications of `P_S`'s first and last parts — the two root
-- commitments (leanVM `EndToEnd/Sound/Frame.lean`'s `commitSpec` pattern: from no doom, the doom
-- created at the root) and the two stacked openings (WP-7's `stackedRec20Spec`,
-- `stackedMain20Spec`, joined by `Spec.orStable`), and `P_S`'s whole specification from `MidSpec`.
import LvmCertS
import LvmCertSFrame

/-!
# The roots, the openings, and `P_S`'s specification

* **`rootsSpec Post`** (O8): `commitRootUd cfgMain20; commitRootUd cfgRec20` from no doom; the doom
  after `C_rec`'s root is `Post`, created there (Pre `False`, as leanVM's `commitSpec`).
* **`openSpec cl`** (O7): `C_rec`'s opening, `C_main`'s opening, `ret true`, from `OpenPost cl`
  (which splits into "`C_rec`'s claims fail" or "`C_main`'s claims fail", `openPost_split`) to
  rejection, every group's escape at most `2^-129`, lead at most `2^-129`. `C_main`'s
  precondition is carried across `C_rec`'s opening by `Spec.orStable`: `C_rec`'s opening commits
  nothing (hypothesis `hnc`, the open fact O7a).
* **`psSpec`**: `PSWith mid x` from no doom, given `MidSpec mid Good` at `2^-129` with lead at
  most `2^-129`: roots (doom `CommitDoomS Good x ∧ RootShape`), the middle phases, the openings.
-/

set_option autoImplicit false

namespace Lvm.ASM

open RecursionFast Lvm.FS Lvm.T
open LeanVM.Parameters
open LeanVM.Protocol.Compile hiding Proof Bytes
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open scoped NNReal ENNReal

/-- The per-group error of `P_S`: `2^-129`. -/
noncomputable abbrev εS : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ ^ 129

/-! ## The roots (O8) -/

/-- **The two roots**, from no doom; the doom created at `C_rec`'s root is `Post`. -/
noncomputable def rootsSpec (Post : Unit → List Ev → Prop) {εm T : ℝ≥0∞} (hT : T ≤ εm) :
    Spec (commitRootUd cfgMain20 >>= fun _ ↦ commitRootUd cfgRec20) (fun _ ↦ False) Post εm 0 T :=
  Spec.bind' ((Spec.commitP (Pre := fun _ ↦ False) (Post := fun _ _ ↦ False) (εmax := εm) 21 64
      (fun _ _ h _ ↦ h.elim) zero_le).congr rfl) fun _ ↦
    (Spec.commitP (Pre := fun _ ↦ False) (Post := Post) 15 64 (fun _ _ h _ ↦ h.elim) hT).congr rfl

/-! ## The openings (O7) -/

/-- **O7a** (open): `C_rec`'s one-level opening commits nothing. -/
def RecNoCommit : Prop :=
  ∀ (cl : List LeanVM.Protocol.Verifier.StackClaim) (h₀ l : List Ev),
    (verifyStackedUd cfgRec20 cl).Reach h₀ l → commits l = []

/-- `C_main`'s opening precondition survives a run that commits nothing. -/
theorem stackedPre_keep {cl : List LeanVM.Protocol.Verifier.StackClaim} {h₀ l : List Ev}
    (hl : commits l = []) (h : StackedPreUd cfgMain20 (codesMain20 0) cl (commits h₀)) :
    StackedPreUd cfgMain20 (codesMain20 0) cl (commits (h₀ ++ l)) := by
  rwa [LeanVM.Protocol.Whir.Sound.commits_append, hl, List.append_nil]

/-- The program of the openings. -/
def openProg (cl : OpenClaims) : VerifierProgram Bool :=
  verifyStackedUd cfgRec20 cl.1 >>= fun _ ↦ verifyStackedUd cfgMain20 cl.2 >>= fun _ ↦ .ret true

open Classical in
/-- **The openings** (O7), from `OpenPost cl`. -/
noncomputable def openSpec (hnc : RecNoCommit) (cl : OpenClaims) :
    Spec (openProg cl) (OpenPost cl) (fun b _ ↦ b = false) εS εS 0 :=
  if hside : (∀ c ∈ cl.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ cl.2, IsMultiaffine 26 c.1) ∧
      cl.1.length ≤ 2 ^ 63 ∧ cl.2.length ≤ 2 ^ 63 then
    have hb1 := (eBatch_P20 _ hside.2.2.1).2
    have hb2 := (eBatch_P20 _ hside.2.2.2).1
    let S1 := (stackedRec20Spec cl.1 hside.1 (eBatch cl.2.length (codesMain20 0))).orStable
      (M := fun h ↦ StackedPreUd cfgMain20 (codesMain20 0) cl.2 (commits h))
      (fun _ _ hl hM ↦ stackedPre_keep (hnc _ _ _ hl) hM) hb2
    let S2 := (stackedMain20Spec cl.2 hside.2.1 0).bind' fun _ ↦
      ((Spec.ret (Post := fun b (_ : List Ev) ↦ b = false) (εmax := εS) (T := 0) true).mono
        (fun _ h ↦ h.elim) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl :
        Spec (VerifierProgram.ret true) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0)
    (S1.bind' fun _ ↦ S2).mono (fun _ hp ↦ openPost_split hp) (fun _ _ h ↦ h) le_rfl
      (max_le hb1 hb2) le_rfl
  else Spec.dead.mono (fun _ hp ↦ hside hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## `P_S` -/

/-- `P_S` as the roots, then the middle phases and the openings. -/
theorem PSWith_eq (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    PSWith mid x = ((commitRootUd cfgMain20 >>= fun _ ↦ commitRootUd cfgRec20) >>= fun _ ↦
      mid x >>= openProg) := rfl

/-- **`P_S`'s specification** (from no doom, rejection where it returns in doom, every group's
escape at most `2^-129`, lead `0`), from the middle phases' `MidSpec` at `2^-129` with a lead at
most `2^-129` and O7a. -/
noncomputable def psSpec (hnc : RecNoCommit) {mid : List UInt8 → VerifierProgram OpenClaims}
    {Good : GoodRel} {Lm : ℝ≥0∞} (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    Spec (PSWith mid x) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0 :=
  (Spec.bind' (rootsSpec (fun _ h ↦ CommitDoomS Good x h ∧ RootShape h) hLm) fun _ ↦
    Spec.bind' (hmid x εS le_rfl).some fun cl ↦ openSpec hnc cl).congr (PSWith_eq mid x).symm

end Lvm.ASM
