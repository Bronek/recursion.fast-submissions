-- WP-14 (ASM). New for lvm (BLUEPRINT §7.1 "glue", A15); the pattern is FR's
-- `FRSubmission4Fin`/`FRNodeRows4RepF` (`certificate_sub4F`, `boundsOK`, `boundsOK_claim`) at
-- rf-k@8bff272b, with the `S` branch's soundness from WP-5's compiler (`kstate_of_kcert`,
-- `KState.congr`) instead of FR's per-chain potential.
import LvmVerifier
import LvmVerifierS
import LvmXComputes
import LvmCompileKS

/-!
# The submission and its certificate from named obligations

`subWith VS E ext` is the submission with

* `V := Vwith VS` (`'S'` → `VS`, otherwise the witness-sending decision, `LvmVerifier`);
* `P := encodeF` (the `W` kind; `δ = 0`, `LvmVerifier.complete`);
* `E`, `ext`: the extractor's specification and program (WP-13a: `Eden … (extIRWith piSz dec)`
  on the domain, the search/`W` branch outside it);
* `ε = 2^-128` and `δ = 0` as casts from `ℚ≥0` (gate rule 4), `qV = 16384`,
  `fuel t = 2^46 + 2^13 t` (`Lvm.X.fuel`).

**`certificate_subWith`**: the contract's `Certificate (subWith VS E ext)` from five obligations,
whose statements are final (they are generic in `VS`, `E`, `ext`; the final assembly instantiates
them):

| name | statement | owner |
|---|---|---|
| `hq` | `∀ H vk c π, isS π → |(VS vk c π).queries H| ≤ qVlvm` | WP-11a driver / WP-14 |
| `hc` | `Computes ext E Lvm.X.fuel` | WP-13a |
| `hsz` | `ext.body.size ≤ progCap` | WP-13a |
| `hEW` | `∀ c π L, isS π = false → E c π L = decode π` | WP-13a (FR `ext_W`) |
| `hS` | `∀ vk, SSound VS E vk` | WP-14 (`LvmCertS`), WP-13a (`E = Ex`) |

**`SSound VS E vk`**: a scheme `Sc` (WP-5 `Scheme`) and a knowledge certificate
`K : KCert Sc (Rel (accV VS vk))` with `εFS K ≤ 2^-128`, such that `VS` accepting an `'S'` proof on a
log implies `Sc.V` accepting it (`KState.congrV`'s condition), and `E` equal to `Sc.Ex K.ext` on
accepted `'S'` proofs over logs of potential below `1` (`μ K L < 1`: no bad entry, and the replayed
history is outside doom and luck, `LvmCertSGood.final_good`), or else a witness of the relation
(FR's search branch outside the domain). The proof is `KState.congr` on `kstate_of_kcert K`, then `KState.mono` and
`KState.ks`.

The current instance and its open obligations are in `LvmSubmissionS`.
-/

namespace Lvm.T

open RecursionFast
open RecursionFast.WitnessSending (encode decode encodeF)
open scoped NNReal

/-- The `S` proof size at `P20` (`sizes_P20`: 783,192 bytes). -/
def piSz : ℕ := Lvm.piSize Lvm.P20

/-- **The submission** with SNARK branch `VS`, extractor specification `E` and program `ext`. -/
def subWith (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg) : Submission where
  V := Vwith VS
  P := fun _ _ w => .ret (encodeF w)
  E := E
  ext := ext
  ε := ((1 / 2 ^ 128 : ℚ≥0) : ℝ≥0)
  δ := ((0 : ℚ≥0) : ℝ≥0)
  qV := qVlvm
  fuel := Lvm.X.fuel

section Facts
variable (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg)

theorem subWith_acc : (subWith VS E ext).acc = accV VS := acc_eq VS _ rfl rfl

theorem subWith_ε : (subWith VS E ext).ε = (2 : ℝ≥0)⁻¹ ^ 128 := by
  simp only [subWith]; push_cast; rw [one_div, inv_pow]

theorem subWith_δ : (subWith VS E ext).δ = 0 := by simp [subWith]

end Facts

/-- **The `S` branch's knowledge soundness** (see the module docstring). -/
def SSound (VS : SProg) (E : Digest → Proof → Log → Option Wit) (vk : Digest) : Prop :=
  ∃ (Sc : Lvm.FS.Scheme) (K : Lvm.FS.KCert Sc (Rel (accV VS vk))),
    Lvm.FS.Scheme.εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 ∧
    (∀ L c π, isS π = true → (VS vk c π).runLog L = some true → (Sc.V c π).runLog L = some true) ∧
    (∀ L c π, isS π = true → L.length ≤ logCap → Lvm.FS.Scheme.μ K L < 1 →
      (Sc.V c π).runLog L = some true →
      (∃ w, E c π L = some w ∧ Rel (accV VS vk) c w) ∨ E c π L = Sc.Ex K.ext c π L)

/-- **Knowledge soundness of `Vwith VS`** under the key `vk`, from `SSound` and `E`'s `W` branch. -/
theorem ks_subWith (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg)
    (hq : ∀ H vk c π, isS π = true → ((VS vk c π).queries H).length ≤ qVlvm)
    (hEW : ∀ c π L, isS π = false → E c π L = decode π) (vk : Digest) (hS : SSound VS E vk) :
    KS (Rel ((subWith VS E ext).acc vk)) ((subWith VS E ext).V vk) (subWith VS E ext).E
      (subWith VS E ext).ε (subWith VS E ext).qV := by
  obtain ⟨Sc, K, hε, hV, hE⟩ := hS
  rw [subWith_acc, subWith_ε]
  have k := (Lvm.FS.KState.congr (Lvm.FS.Scheme.kstate_of_kcert K) (V' := Vwith VS vk) (E' := E) (by
    intro L c π hl hμ hacc
    cases h : isS π
    · left
      obtain ⟨w, hw, hR⟩ := V_W_runLog VS vk c π h hacc
      exact ⟨w, by rw [hEW c π L h, hw], hR⟩
    · rw [V_S VS vk c π h] at hacc
      have hv := hV L c π h hacc
      rcases hE L c π h hl hμ hv with hw | he
      · exact .inl hw
      · exact .inr ⟨hv, he⟩)).mono hε
  exact k.ks fun H c π => V_queries_le VS H (hq H) vk c π

/-- **The contract's `Certificate`** of `subWith VS E ext` from the five obligations. -/
theorem certificate_subWith (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg)
    (hq : ∀ H vk c π, isS π = true → ((VS vk c π).queries H).length ≤ qVlvm)
    (hc : Computes ext E Lvm.X.fuel) (hsz : ext.body.size ≤ progCap)
    (hEW : ∀ c π L, isS π = false → E c π L = decode π) (hS : ∀ vk, SSound VS E vk) :
    Certificate (subWith VS E ext) where
  secure vk := ks_subWith VS E ext hq hEW vk (hS vk)
  complete vk := by
    rw [subWith_δ]; exact complete VS _ rfl rfl rfl vk
  computes := hc
  cap := ⟨by rw [subWith_ε]; rfl, by rw [subWith_δ]; exact zero_le, show qVlvm ≤ 2 ^ 16 by decide,
    Lvm.X.fuel_le_budget, hsz⟩

/-! ## The declared claim -/

/-- The submission's numbers are within `D`'s, and `D`'s fuel within the budget. -/
def BoundsOK (D : Declared) (S : Submission) : Prop :=
  S.ε ≤ D.ε ∧ S.δ ≤ D.δ ∧ S.qV ≤ D.qV ∧ ∀ t, S.fuel t ≤ D.fuel t ∧ D.fuel t ≤ extractorBudget t

/-- **The certificate against a declared claim.** -/
theorem certificateR_of {D : Declared} {S : Submission} (hC : Certificate S) (hb : BoundsOK D S) :
    CertificateR D S := ⟨hC, hb⟩

/-- **The bounds at `claim.json`'s numbers** (the rendered forms of `render-challenge.py`):
`error 1/2^128`, `completeness_error 0`, `qV 16384`, `fuel_base 2^46`, `fuel_per_word 8192`. -/
theorem boundsOK_claim (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg) :
    BoundsOK ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS E ext) := by
  refine ⟨?_, by simp [subWith], le_of_eq rfl, fun t => ⟨le_of_eq ?_, ?_⟩⟩
  · simp only [subWith]; push_cast; norm_num
  · simp [subWith, Lvm.X.fuel, Lvm.X.fuelBase, Lvm.X.fuelPerWord]
  · simp only [extractorBudget]; omega

/-- (−) **The bounds are not vacuous**: a declared query bound below `qVlvm` fails them. -/
theorem not_boundsOK_qV (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg) :
    ¬ BoundsOK ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, 0, 16383,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS E ext) := fun h => by
  have h1 := h.2.2.1
  simp only [subWith, qVlvm] at h1
  omega

/-- **The obligations** of a submission `subWith VS E ext` (the five hypotheses of
`certificate_subWith`). -/
def OpenWith (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg) : Prop :=
  (∀ H vk c π, isS π = true → ((VS vk c π).queries H).length ≤ qVlvm) ∧ Computes ext E Lvm.X.fuel ∧
    ext.body.size ≤ progCap ∧ (∀ c π L, isS π = false → E c π L = decode π) ∧
    ∀ vk, SSound VS E vk

/-- The certificate of `subWith VS E ext` against `claim.json`, from its obligations. -/
theorem certificateR_claim (VS : SProg) (E : Digest → Proof → Log → Option Wit) (ext : XProg)
    (h : OpenWith VS E ext) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subWith VS E ext) :=
  certificateR_of (certificate_subWith VS E ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (boundsOK_claim VS E ext)

end Lvm.T
