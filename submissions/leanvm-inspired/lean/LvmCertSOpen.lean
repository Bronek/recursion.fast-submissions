-- WP-14 (ASM). New for lvm: the specifications of `P_S`'s first and last parts — the two root
-- commitments (leanVM `EndToEnd/Sound/Frame.lean`'s `commitSpec` pattern: from no doom, the doom
-- created at the root) and the two stacked openings (WP-7's `stackedRec20GSpec`,
-- `stackedMain24GSpec`, joined by `Spec.orStable`), and `P_S`'s whole specification from `MidSpec`.
import LvmCertS
import LvmCertSFrame

/-!
# The roots, the openings, and `P_S`'s specification

* **`rootsSpec Post`** (O8): `commitRootUd cfgMain24G; commitRootUd cfgRec20G` from no doom; the doom
  after `C_rec`'s root is `Post`, created there (Pre `False`, as leanVM's `commitSpec`).
* **`openSpec cl`** (O7): `C_rec`'s opening, `C_main`'s opening, `ret true`, from `OpenPost cl`
  (which splits into "`C_rec`'s claims fail" or "`C_main`'s claims fail", `openPost_split`) to
  rejection, every group's escape at most `2^-129`, lead at most `2^-129`. `C_main`'s
  precondition (`MainPre`, two commitments) is carried across `C_rec`'s two-level opening by
  `Spec.orStableRet`: that opening's completed runs commit exactly one word (hypothesis `hnc`,
  O7a `RecCommitsOne`), after which it is `C_main`'s `StackedPreUd` (three commitments).
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

/-- The per-group error of `P_S` (lvm2 JB-VQP, J1: the exact budget, JB-L §1): `7·2^-131 = 2^-128 − 2^-131`.
`C_main`'s Johnson query groups reach `2^-128.30`; the luck (`2^-132`) and the hash term (`2^-139`) fit the
margin `2^-131`. Every other group is at most `2^-129` (`pow129_le_εS`). -/
noncomputable abbrev εS : ℝ≥0∞ := 7 * (2 : ℝ≥0∞)⁻¹ ^ 131

theorem inv_pow_131_ne_top : (2 : ℝ≥0∞)⁻¹ ^ 131 ≠ ⊤ :=
  ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero)

theorem inv_pow_add2 (k : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ k = (2 : ℝ≥0∞)⁻¹ ^ (k + 2) * 4 := by
  rw [pow_add, mul_assoc, show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← mul_pow,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]

/-- Every group bounded by `2^-129` is within `εS`. -/
theorem pow129_le_εS : (2 : ℝ≥0∞)⁻¹ ^ 129 ≤ εS := by
  rw [inv_pow_add2 129]
  show (2 : ℝ≥0∞)⁻¹ ^ 131 * 4 ≤ 7 * (2 : ℝ≥0∞)⁻¹ ^ 131
  rw [mul_comm]
  exact mul_le_mul' (by norm_num) le_rfl

/-- `2^-128 = 7·2^-131 + 2^-131`. -/
theorem inv_pow_128_eq : (2 : ℝ≥0∞)⁻¹ ^ 128 = 7 * (2 : ℝ≥0∞)⁻¹ ^ 131 + (2 : ℝ≥0∞)⁻¹ ^ 131 := by
  rw [inv_pow_add2 128, inv_pow_add2 130, show 128 + 2 + 2 = 131 + 1 from rfl]
  rw [show (2 : ℝ≥0∞)⁻¹ ^ (131 + 1) * 4 * 4 = (2 : ℝ≥0∞)⁻¹ ^ (131 + 1) * 2 * 8 by ring,
    pow_succ, mul_assoc ((2 : ℝ≥0∞)⁻¹ ^ 131), ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  ring

/-- `x + 2^-131 ≤ 2^-128` gives `x ≤ εS` (JB-L's margin form of the Johnson groups). -/
theorem le_εS_of_margin {x : ℝ≥0∞} (h : x + (2 : ℝ≥0∞)⁻¹ ^ 131 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128) : x ≤ εS := by
  rw [inv_pow_128_eq] at h
  exact (ENNReal.add_le_add_iff_right inv_pow_131_ne_top).1 h

theorem εS_le_128 : εS ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := le_self_add.trans_eq inv_pow_128_eq.symm

/-! ## The roots (O8) -/

/-- **The two roots**, from no doom; the doom created at `C_rec`'s root is `Post`. -/
noncomputable def rootsSpec (Post : Unit → List Ev → Prop) {εm T : ℝ≥0∞} (hT : T ≤ εm) :
    Spec (commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G) (fun _ ↦ False) Post εm 0 T :=
  Spec.bind' ((Spec.commitP (Pre := fun _ ↦ False) (Post := fun _ _ ↦ False) (εmax := εm) 19 64
      (fun _ _ h _ ↦ h.elim) zero_le).congr rfl) fun _ ↦
    (Spec.commitP (Pre := fun _ ↦ False) (Post := Post) 15 64 (fun _ _ h _ ↦ h.elim) hT).congr rfl

/-! ## The openings (O7) -/

/-- **O7a** (lvm2, S4): every completed run of `C_rec`'s two-level opening commits exactly one
word (its level-1 oracle). -/
def RecCommitsOne : Prop :=
  ∀ (cl : List LeanVM.Protocol.Verifier.StackClaim) (l : List Ev) (a : Unit),
    (verifyStackedUd cfgRec20G cl).after l = some (.ret a) → (commits l).length = 1

/-- The program of the openings. -/
def openProg (cl : OpenClaims) : VerifierProgram Bool :=
  verifyStackedUd cfgRec20G cl.1 >>= fun _ ↦ verifyStackedJ (cfgMain24J 3) cl.2 >>= fun _ ↦ .ret true

/-- **`C_main`'s stacked opening at the Johnson radius at `εS`** (JB-L's `stackedMain24JSpec` at the
exact budget: `whirEps_main24J`'s margin `2^-131` left for luck and hash). -/
noncomputable def stackedMain24JSpecS (claims : List LeanVM.Protocol.Verifier.StackClaim)
    (hcl : ∀ c ∈ claims, IsMultiaffine (cfgMain24J 3).μ c.1) (T : ℝ≥0∞) :
    Spec (verifyStackedJ (cfgMain24J 3) claims)
      (fun h ↦ StackedPreUd (cfgMain24J 3).toUdConfig (codesMain24J 0) claims (commits h))
      (fun _ _ ↦ False) εS (eBatch claims.length (codesMain24J 0)) T :=
  stackedSpecJ claims hcl rfl rfl rfl (by norm_num [cfgMain24J]) rfl (by norm_num [cfgMain24J])
    (by norm_num [cfgMain24J]) (by norm_num [cfgMain24J]) (ladderArith_main24J 2)
    (le_εS_of_margin (whirEps_main24J 2)) T

/-- The stacked batching of `C_main` at the Johnson radius: `(J − 1)·98/|E| ≤ 2^-129` for at most
`2^40` claims. -/
theorem eBatch_main24J (J : ℕ) (hJ : J ≤ 2 ^ 40) : eBatch J (codesMain24J 0) ≤ εS := by
  refine le_trans ?_ pow129_le_εS
  unfold eBatch
  rw [card_E_ennreal, ← two_pow_cast 192]
  refine natCast_div_le_inv_pow (by positivity) ?_
  have h98 : (codesMain24J 0).listMax = 98 := rfl
  rw [h98]
  calc (J - 1) * 98 * 2 ^ 129 ≤ 2 ^ 40 * 98 * 2 ^ 129 := by gcongr; exact (Nat.sub_le J 1).trans hJ
    _ ≤ 2 ^ 192 := by norm_num

open Classical in
/-- **The openings** (O7), from `OpenPost cl`. -/
noncomputable def openSpec (hnc : RecCommitsOne) (cl : OpenClaims) :
    Spec (openProg cl) (OpenPost cl) (fun b _ ↦ b = false) εS εS 0 :=
  if hside : (∀ c ∈ cl.1, IsMultiaffine 19 c.1) ∧ (∀ c ∈ cl.2, IsMultiaffine CMain.nu20 c.1) ∧
      cl.1.length ≤ 2 ^ 63 ∧ cl.2.length ≤ 2 ^ 40 then
    have hb1 := (eBatch_P20 _ hside.2.2.1).2.trans pow129_le_εS
    have hb2 := eBatch_main24J _ hside.2.2.2
    let S1 := ((stackedRec20GSpec cl.1 hside.1 (eBatch cl.2.length (codesMain24J 0))).mono
        (fun _ h ↦ h) (fun _ _ h ↦ h) pow129_le_εS le_rfl le_rfl).orStableRet
      (M := fun h ↦ MainPre cl.2 (commits h))
      (M' := fun h ↦ StackedPreUd (cfgMain24J 3).toUdConfig (codesMain24J 0) cl.2 (commits h))
      (fun _ _ _ _ ha hM ↦ by
        rw [LeanVM.Protocol.Whir.Sound.commits_append]
        exact stackedPreUd_of_mainPre hM (hnc _ _ _ ha)) hb2
    let S2 := (stackedMain24JSpecS cl.2 hside.2.1 0).bind' fun _ ↦
      ((Spec.ret (Post := fun b (_ : List Ev) ↦ b = false) (εmax := εS) (T := 0) true).mono
        (fun _ h ↦ h.elim) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl :
        Spec (VerifierProgram.ret true) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0)
    (S1.bind' fun _ ↦ S2).mono (fun _ hp ↦ openPost_split hp) (fun _ _ h ↦ h) le_rfl
      (max_le hb1 hb2) le_rfl
  else Spec.dead.mono (fun _ hp ↦ hside hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## `P_S` -/

/-- `P_S` as the roots, then the middle phases and the openings. -/
theorem PSWith_eq (mid : List UInt8 → VerifierProgram OpenClaims) (x : List UInt8) :
    PSWith mid x = ((commitRootUd cfgMain24G >>= fun _ ↦ commitRootUd cfgRec20G) >>= fun _ ↦
      mid x >>= openProg) := rfl

/-- **`P_S`'s specification** (from no doom, rejection where it returns in doom, every group's
escape at most `2^-129`, lead `0`), from the middle phases' `MidSpec` at `2^-129` with a lead at
most `2^-129` and O7a (`RecCommitsOne`). -/
noncomputable def psSpec (hnc : RecCommitsOne) {mid : List UInt8 → VerifierProgram OpenClaims}
    {Good : GoodRel} {Lm : ℝ≥0∞} (hmid : MidSpec mid Good εS Lm) (hLm : Lm ≤ εS) (x : List UInt8) :
    Spec (PSWith mid x) (fun _ ↦ False) (fun b _ ↦ b = false) εS 0 0 :=
  (Spec.bind' (rootsSpec (fun _ h ↦ CommitDoomS Good x h ∧ RootShape h) hLm) fun _ ↦
    Spec.bind' (hmid x εS le_rfl).some fun cl ↦ openSpec hnc cl).congr (PSWith_eq mid x).symm

end Lvm.ASM
