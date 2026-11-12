-- New for lvm (WP-16a2, BLUEPRINT A24): `V_S` behind a static guard. The facts about the node program
-- that the kernel cannot evaluate are one closed Bool `b` (`LvmFinStatic.staticOkB`), checked by the
-- compiled `V` once per process; the certificate case-splits on `b`.
import LvmSubmissionS

/-!
# The static guard of `V_S` (A24)

* **`VSg b VS`**: `VS` when `b`, else every `S` proof is rejected (`.ret false`, no query).
* **`subG b VS`**: `subWith (VSg b VS) (EX (accV (VSg b VS))) extX` (the extractor specification
  follows the guarded `V_S`, as `EX20` follows `VS20`).
* **`certificateR_reject`**: with the guard off the `S` branch accepts nothing, so its knowledge
  soundness holds with a trivial scheme (`P_S := .ret false`, empty doom, no luck); the `W` branch,
  completeness (`P := encode`, `δ = 0`) and the extractor are those of every `subWith`.
* **`certificateR_guardT`**: the certificate of `subG b (VSt tabs)` from the open obligations under
  `b = true` (lvm2 S2-CERT: generic in the node program's tables; v1's `certificateR_guard` at
  `VS20`, `subG_true` and `subG_F` are in `LvmFinCert`, which imports the node program).
-/

set_option autoImplicit false

namespace Lvm.Fin

open RecursionFast Lvm.T Lvm.ASM Lvm.FS
open RecursionFast.WitnessSending (encode decode encodeF)
open LeanVM.Protocol.Compile hiding Proof Bytes
open scoped NNReal ENNReal

/-- **`V_S` behind the guard `b`**: `VS` when `b`, else reject. -/
def VSg (b : Bool) (VS : SProg) : SProg := fun vk c π => if b then VS vk c π else .ret false

/-- **The submission with the guarded `V_S`.** -/
def subG (b : Bool) (VS : SProg) : Submission :=
  subWith (VSg b VS) (Lvm.X.EX (accV (VSg b VS))) Lvm.X.extX

theorem VSg_true (VS : SProg) : VSg true VS = VS := rfl

/-! ## The guard off: a scheme that rejects -/

/-- The scheme of `P_S := .ret false`. -/
def schemeR (vk : Digest) : Scheme := schemeS vk fun _ => .ret false

theorem after_ret_false {h : List Ev} {p : VerifierProgram Bool}
    (hp : (VerifierProgram.ret false : VerifierProgram Bool).after h = some p) : p = .ret false := by
  cases h with
  | nil => simpa [VerifierProgram.after] using hp.symm
  | cons e es => cases e <;> simp [VerifierProgram.after] at hp

/-- The empty doom certificate of `.ret false`. -/
noncomputable def certR : Cert (VerifierProgram.ret false : VerifierProgram Bool) where
  D _ := False
  ε _ := 0
  read _ _ _ hD := hD.elim
  grind _ _ hD := hD.elim
  commit _ _ _ _ hD := hD.elim
  group _ _ _ _ hD := hD.elim
  final _ _ hD := hD

/-- **The trivial knowledge certificate** of the rejecting scheme. -/
noncomputable def kcertR (vk : Digest) (R : Digest → Wit → Prop) : KCert (schemeR vk) R where
  cert _ := certR
  ε := 0
  cert_ε _ _ _ _ hD := hD.elim
  ε_lt_one := zero_lt_one
  B _ _ := False
  εB := 0
  εB_lt_one := zero_lt_one
  B_nil _ := id
  B_read _ _ _ _ := id
  B_commit _ _ _ _ _ := id
  B_group _ _ hp hk _ := by
    have := after_ret_false hp
    subst this
    rcases hk with ⟨k, hk⟩ | ⟨i, ps, k, hk⟩ <;> cases hk
  ext _ _ _ := .leaf (dg []) 0
  extract _ _ hp _ _ _ := by have := after_ret_false hp; cases this

theorem εFS_kcertR (vk : Digest) (R : Digest → Wit → Prop) :
    Scheme.εFS (kcertR vk R) ≤ (2 : ℝ≥0)⁻¹ ^ 128 := by
  unfold Scheme.εFS
  show (0 : ℝ≥0) + 0 + (badCount : ℝ≥0) / 2 ^ 256 ≤ _
  rw [zero_add, zero_add]
  exact badCount_div_le.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num))

/-- The rejecting scheme's compiled verifier accepts nothing. -/
theorem schemeR_rejects (vk c : Digest) (π : Proof) (L : Log) :
    ((schemeR vk).V c π).runLog L ≠ some true := by
  have ht : ∀ st body, ((schemeR vk).trun L (.ret false) st [] [] body []).map Prod.fst = some false :=
    fun _ _ => rfl
  rw [Scheme.runLog_V]
  rcases (schemeR vk).hdr π with _ | ⟨x, body⟩
  · simp
  · simp only
    split_ifs
    · intro h
      obtain ⟨e₀, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e₁, -, h⟩ := Option.bind_eq_some_iff.mp h
      rw [show (schemeR vk).P x = .ret false from rfl, ht] at h
      cases h
    · simp

/-- **`SSound` with the guard off**: `V_S` rejects every `S` proof. -/
theorem sSound_reject (VS : SProg) (E : Digest → Proof → Log → Option Wit) (vk : Digest) :
    SSound (VSg false VS) E vk :=
  ⟨schemeR vk, kcertR vk (Rel (accV (VSg false VS) vk)), εFS_kcertR vk _,
    fun L c π _ h => by simp [VSg, OProg.runLog] at h,
    fun L c π _ _ _ h => (schemeR_rejects vk c π L h).elim⟩

/-- **The certificate with the guard off** (A24's false branch). -/
theorem certificateR_reject (VS : SProg) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subG false VS) :=
  certificateR_claim _ _ _
    ⟨fun H vk c π _ => by simp [VSg, OProg.queries], Lvm.X.computesX _, Lvm.X.extX_caps.2,
      fun c π L h => Lvm.X.EX_W _ c π L fun h0 => by
        have : π.data.getD 0 0 = 0x53 := by rw [Array.getD_eq_getD_getElem?, h0]; rfl
        simp [isS, this, sByte] at h,
      fun vk => sSound_reject VS _ vk⟩

/-- **The certificate of the guarded submission on the tables `tabs`** from the open obligations
under `b = true`. -/
theorem certificateR_guardT (tabs : Lvm.Pub → List Lvm.M3.Tab) {b : Bool} (h : b = true → OpenT tabs) :
    CertificateR ⟨(1 : ℝ≥0) / 340282366920938463463374607431768211456, (0 : ℝ≥0) / 1, 16384,
      fun t => 70368744177664 + 8192 * t⟩ (subG b (VSt tabs)) := by
  cases b with
  | false => exact certificateR_reject _
  | true => exact certificateR_openT tabs (h rfl)

end Lvm.Fin
