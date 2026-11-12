-- WP-5 (FS). New for lvm (BLUEPRINT §7.1, §7.3): the generic Fiat–Shamir compiler theorem.
import LvmCompileFinal
import RecursionFast.Library.PaperTheorem

/-!
# The compiler theorem

**`kstate_of_kcert`**: a knowledge certificate `K` for the scheme `S` gives the Library's knowledge
state for the compiled verifier `S.V` and the specification extractor `S.Ex K.ext`, at the error

`εFS K = K.ε + K.εB + badCount / 2^256`  (`badCount / 2^256 < 2^-139`).

**`ks_of_kcert`**: with the query bound `qV` of the compiled verifier, the contract's knowledge
soundness `KS R S.V (S.Ex K.ext) (εFS K) qV` (through `KState.ks`).

**`εFS_le_of`**: `ε + εB + 2^-139 ≤ 2^-128` gives `εFS K ≤ 2^-128` (the contract's cap);
**`εFS_le`**: the special case `ε ≤ 2^-129`, `εB ≤ 2^-130`.

**`KState.congrE`**: an extractor that agrees with the specification extractor on accepted proofs
over logs of potential below `1` inherits the knowledge state (for the extractor program).
**`KState.congrV`**: a verifier whose acceptance implies the compiled verifier's inherits it (for a
fast verifier that refines `S.V`). **`KState.congr`** (both, plus a native branch): a verifier
`V'` and extractor `E'` such that, on logs of potential below `1`, every proof `V'` accepts is
either extracted natively (the `W` kind) or accepted by `V` with `E' = E` there (the `S` kind).

The hypotheses are the certificate's fields; the scheme's fields (`enc_inj`, `q0_short`,
`chal_sum`) are facts about the encoding. No length rule is needed: every Fiat–Shamir query is
checked against `queryCap` at run time, and the forest classifies entries by the program.
-/

namespace Lvm.FS

open LeanVM.Parameters RecursionFast
open LeanVM.Protocol.Compile hiding Proof  -- INT-1: WP-2's DSL also has a `Proof`; here it is `RecursionFast.Proof`
open scoped NNReal

namespace Scheme

variable {S : Scheme} {R : Digest → Wit → Prop}

/-- **The Fiat–Shamir compiler theorem** (knowledge state). -/
noncomputable def kstate_of_kcert (K : KCert S R) : KState R S.V (S.Ex K.ext) (εFS K) where
  μ := μ K
  empty := mu_empty K
  step L q hl hμ hq := mu_step K L q hl hμ hq
  final L c π _ hμ hacc := final_law K L c π hμ hacc

/-- **The Fiat–Shamir compiler theorem** (the contract's knowledge soundness). -/
theorem ks_of_kcert (K : KCert S R) {qV : ℕ} (hq : ∀ H c π, ((S.V c π).queries H).length ≤ qV) :
    KS R S.V (S.Ex K.ext) (εFS K) qV :=
  (kstate_of_kcert K).ks hq

/-- **The ε budget** (general form): the groups and the luck fit the contract's cap `2^-128` when
they leave room for the hash term. -/
theorem εFS_le_of (K : KCert S R) (h : K.ε + K.εB + (2 : ℝ≥0)⁻¹ ^ 139 ≤ (2 : ℝ≥0)⁻¹ ^ 128) :
    εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 := by
  unfold εFS
  exact (add_le_add le_rfl badCount_div_le).trans h

/-- **The ε budget**: groups at `2^-129` and luck at `2^-130` fit the contract's cap `2^-128`
with the hash term. -/
theorem εFS_le (K : KCert S R) (hε : K.ε ≤ (2 : ℝ≥0)⁻¹ ^ 129) (hεB : K.εB ≤ (2 : ℝ≥0)⁻¹ ^ 130) :
    εFS K ≤ (2 : ℝ≥0)⁻¹ ^ 128 := by
  unfold εFS
  refine (add_le_add (add_le_add hε hεB) badCount_div_le).trans ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  norm_num

end Scheme

/-- An extractor that agrees with `E` on accepted proofs over logs of potential below `1`. -/
def KState.congrE {R : Digest → Wit → Prop} {V : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} (k : KState R V E ε)
    (E' : Digest → Proof → Log → Option Wit)
    (h : ∀ L c π, L.length ≤ logCap → k.μ L < 1 → (V c π).runLog L = some true →
      E' c π L = E c π L) : KState R V E' ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hl hμ hacc := by rw [h L c π hl hμ hacc]; exact k.final L c π hl hμ hacc

/-- A verifier whose acceptance on a log implies `V`'s. -/
def KState.congrV {R : Digest → Wit → Prop} {V V' : Digest → Proof → OProg Bool}
    {E : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} (k : KState R V E ε)
    (h : ∀ L c π, (V' c π).runLog L = some true → (V c π).runLog L = some true) :
    KState R V' E ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hl hμ hacc := k.final L c π hl hμ (h L c π hacc)

/-- **Transfer to a dispatching verifier**: every proof `V'` accepts on a log of potential below
`1` is either extracted by `E'` directly, or accepted by `V` with `E'` agreeing with `E`. -/
def KState.congr {R : Digest → Wit → Prop} {V V' : Digest → Proof → OProg Bool}
    {E E' : Digest → Proof → Log → Option Wit} {ε : ℝ≥0} (k : KState R V E ε)
    (h : ∀ L c π, L.length ≤ logCap → k.μ L < 1 → (V' c π).runLog L = some true →
      (∃ w, E' c π L = some w ∧ R c w) ∨
        ((V c π).runLog L = some true ∧ E' c π L = E c π L)) :
    KState R V' E' ε where
  μ := k.μ
  empty := k.empty
  step := k.step
  final L c π hl hμ hacc := by
    rcases h L c π hl hμ hacc with hw | ⟨hv, he⟩
    · exact hw
    · rw [he]; exact k.final L c π hl hμ hv

end Lvm.FS
