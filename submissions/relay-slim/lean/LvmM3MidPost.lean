-- new for lvm (WP-9b): `midBusTableSpec` with a post on the returned claims alone (WP-14's next
-- phase, `kgSpec`, carries a predicate of the claims inside one `Doomed`), per stack and per
-- commitment block; and the phases 2–3 program commits nothing and asks no proof of work (the
-- leaves adapted from WP-14's `LvmCertSNo` on lvm/ASM 220a1249, `nc_*`/`ng_*`, as one predicate).
import LvmM3Mid
import LvmM3MidStack
import LvmCertSFrame

/-!
# The bus/table phases' post on the claims, and their structure

* **`CommittedHolds tabs q c`**: the table phase's claim `c` (a global column, a point, a value),
  decoded with `colLoc`, holds of the stack `q` when it is on a committed column (claims on fixed
  columns are vacuous); **`BlockHolds L tabs qm qr c`**: the same on the commitments' block
  (`comBlock`, the native `BlockClaim.point ⟨τ, off⟩`); `committedHolds_iff_block` under `LayOk`.
* **`midBusTableSpec'`**: Post `Doomed C (fun p ↦ (∀ c ∈ cl, CommittedHolds tabs (stk p) c) ∧ R p)`;
  **`midBusTableSpecB`**: candidates are pairs `(qm, qr)`, `stk = stackOf`, Post with `BlockHolds`.
* **`noCG_lbusTableCheckProg`**: `lbusTableCheckProg` commits nothing and asks no proof of work
  (`NoCommit ∧ NoGrind`, LvmCertSFrame), so `RootShape`-like facts of the history carry through
  (`Spec.frame` with `NoCommit.reach_commits`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

/-! ## No commitment, no proof of work -/

section NoCG

open VerifierProgram

variable {α β : Type}

/-- `p` commits nothing and asks no proof of work. -/
def NoCG (p : VerifierProgram α) : Prop := p.NoCommit ∧ p.NoGrind

theorem NoCG.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoCG p)
    (hf : ∀ a, NoCG (f a)) : NoCG (p.bind f) :=
  ⟨NoCommit.bind hp.1 fun a ↦ (hf a).1, NoGrind.bind hp.2 fun a ↦ (hf a).2⟩

theorem cg_ret (a : α) : NoCG (VerifierProgram.ret a) := ⟨trivial, trivial⟩
theorem cg_sample : NoCG (sampleChallenge : VerifierProgram E) := ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
theorem cg_readScalar : NoCG (readScalar : VerifierProgram E) := ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
theorem cg_require (c : Prop) [Decidable c] : NoCG (require c) := by
  unfold require; split <;> exact ⟨trivial, trivial⟩

theorem cg_readScalars : ∀ n, NoCG (readScalars n)
  | 0 => cg_ret _
  | n + 1 => NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_readScalars n) fun _ ↦ cg_ret _

theorem cg_sampleChallenges : ∀ n, NoCG (sampleChallenges n)
  | 0 => cg_ret _
  | n + 1 => NoCG.bind cg_sample fun _ ↦ NoCG.bind (cg_sampleChallenges n) fun _ ↦ cg_ret _

theorem cg_roundPoly (c : ℕ) (t : E) : ∀ e, NoCG (Verifier.sumcheckRoundPoly c t e)
  | none => by
    unfold Verifier.sumcheckRoundPoly
    exact NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦ cg_ret _
  | some _ => by
    unfold Verifier.sumcheckRoundPoly
    exact NoCG.bind (cg_readScalars _) fun _ ↦ cg_ret _

theorem cg_sumcheck (count : ℕ) : ∀ (es : List (Option E)) (claim : E),
    NoCG (Verifier.sumcheck claim count es)
  | [], _ => cg_ret _
  | e :: es, claim => by
    unfold Verifier.sumcheck
    refine NoCG.bind (cg_roundPoly _ _ e) fun msg ↦ NoCG.bind cg_sample fun ch ↦ ?_
    exact NoCG.bind (cg_sumcheck count es _) fun r ↦ cg_ret _

theorem cg_gkrStep (step : ℕ) (s : Verifier.GkrState) : NoCG (Verifier.gkrStep step s) := by
  unfold Verifier.gkrStep
  refine NoCG.bind cg_sample fun _ ↦ NoCG.bind (cg_sumcheck _ _ _) fun r ↦ ?_
  obtain ⟨x, claim⟩ := r
  exact NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_readScalars _) fun _ ↦
    NoCG.bind (cg_readScalars _) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
      NoCG.bind (cg_sampleChallenges _) fun _ ↦ cg_ret _

theorem cg_gkrLayers : ∀ (n : ℕ) (s : Verifier.GkrState), NoCG (Verifier.gkrLayers n s)
  | 0, _ => cg_ret _
  | 1, s => by
    unfold Verifier.gkrLayers
    exact NoCG.bind (cg_gkrStep 1 s) fun _ ↦ cg_ret _
  | n + 2, s => by
    unfold Verifier.gkrLayers
    split
    · exact NoCG.bind (cg_gkrStep 1 s) fun s' ↦ cg_gkrLayers (n + 1) s'
    · exact NoCG.bind (cg_gkrStep 2 s) fun s' ↦ cg_gkrLayers n s'

theorem cg_verifyGkr (depth : ℕ) : NoCG (Verifier.verifyGkrGrandProducts depth) := by
  unfold Verifier.verifyGkrGrandProducts
  exact NoCG.bind cg_readScalar fun _ ↦ NoCG.bind cg_readScalar fun _ ↦
    NoCG.bind (cg_gkrLayers _ _) fun _ ↦ cg_ret _

theorem cg_abProg : NoCG abProg :=
  NoCG.bind (cg_sampleChallenges 4) fun _ ↦ NoCG.bind cg_sample fun _ ↦ cg_ret _

theorem cg_lvmBusProg (μ : ℕ) : NoCG (lvmBusProg μ) :=
  NoCG.bind cg_abProg fun _ ↦ NoCG.bind (cg_verifyGkr μ) fun _ ↦ NoCG.bind (cg_require _) fun _ ↦
    NoCG.bind cg_readScalar fun _ ↦ NoCG.bind (cg_require _) fun _ ↦ cg_ret _

theorem cg_tableTermsClaims (tables : List Verifier.Table) (cps fps pt : List E) :
    ∀ (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      NoCG (Verifier.tableTermsClaims tables cps fps pt rows cursor final claims)
  | [], _, _, _ => cg_ret _
  | (table, height, forms, weight) :: rest, cursor, final, claims => by
    unfold Verifier.tableTermsClaims
    exact NoCG.bind (cg_readScalars _) fun _ ↦ cg_tableTermsClaims tables cps fps pt rest _ _ _

theorem cg_tablePhaseClaims (tables : List Verifier.Table) (layout : Verifier.Layout)
    (bus : Verifier.BusResult) : NoCG (Verifier.tablePhaseClaims tables layout bus) := by
  unfold Verifier.tablePhaseClaims Verifier.tableSumcheckClaims
  refine NoCG.bind cg_sample fun _ ↦ NoCG.bind (NoCG.bind (cg_sumcheck _ _ _) fun r ↦ ?_)
    fun _ ↦ cg_ret _
  obtain ⟨ch, claim⟩ := r
  refine NoCG.bind (cg_tableTermsClaims _ _ _ _ _ _ _ _) fun r ↦ ?_
  obtain ⟨final, cl⟩ := r
  exact NoCG.bind (cg_require _) fun _ ↦ cg_ret _

/-- **V_S phases 2–3 commit nothing and ask no proof of work.** -/
theorem noCG_lbusTableCheckProg (tabs : List Tab) (μ : ℕ) : NoCG (lbusTableCheckProg tabs μ) :=
  NoCG.bind (NoCG.bind (cg_lvmBusProg μ) fun _ ↦ cg_tablePhaseClaims _ _ _) fun _ ↦
    NoCG.bind (cg_require _) fun _ ↦ cg_ret _

end NoCG

/-! ## The claims' post -/

section Post

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **A table-phase claim on a committed column holds of the stack `q`**: decoded with `colLoc` to
column `i` of table `j`, a committed column, its extension at the claim's point is the value
(claims on fixed columns, and claims that do not decode, are vacuous). -/
def CommittedHolds (q : Column L.μ) (c : Verifier.ColumnClaim) : Prop :=
  ∀ j i (hj : j < tabs.length) (hi : i < (tabs.get ⟨j, hj⟩).w) (rec : Bool) (off : ℕ),
    colLoc tabs c.column = some (j, i) → (tabs.get ⟨j, hj⟩).cols[i]? = some (.com rec off) →
    eval₂Mle ((inst L tabs hτ).column q ⟨⟨j, hj⟩, ⟨i, hi⟩⟩).values (algebraMap K E)
      (vecOf _ c.point) = c.value

/-- **A table-phase claim on a committed column holds of its commitment's block**: as
`CommittedHolds`, on `comBlock qm qr rec τ off` (the native `BlockClaim.point ⟨τ, off⟩ pt v` on
`C_rec` if `rec`, else `C_main`). -/
def BlockHolds (qm : Column L.nuMain) (qr : Column L.nuRec) (c : Verifier.ColumnClaim) : Prop :=
  ∀ j i (hj : j < tabs.length) (rec : Bool) (off : ℕ),
    colLoc tabs c.column = some (j, i) → (tabs.get ⟨j, hj⟩).cols[i]? = some (.com rec off) →
    eval₂Mle (comBlock L qm qr rec (tabs.get ⟨j, hj⟩).τ off).values (algebraMap K E)
      (vecOf _ c.point) = c.value

/-- Under `LayOk`, a claim holds of the stack of the commitments iff it holds of its block. -/
theorem committedHolds_iff_block (hlay : LayOk L tabs) (qm : Column L.nuMain) (qr : Column L.nuRec)
    (c : Verifier.ColumnClaim) :
    CommittedHolds L tabs hτ (stackOf L qm qr) c ↔ BlockHolds L tabs qm qr c := by
  constructor
  · intro h j i hj rec off hl hcol
    have hi : i < (tabs.get ⟨j, hj⟩).w := (List.getElem?_eq_some_iff.mp hcol).1
    have := h j i hj hi rec off hl hcol
    rwa [column_stackOf L tabs hτ hlay qm qr ⟨j, hj⟩ ⟨i, hi⟩ hcol] at this
  · intro h j i hj hi rec off hl hcol
    rw [column_stackOf L tabs hτ hlay qm qr ⟨j, hj⟩ ⟨i, hi⟩ hcol]
    exact h j i hj rec off hl hcol

theorem vecOf_toList {n : ℕ} (v : Vector E n) : vecOf n v.toList = v := by
  apply Vector.ext; intro i hi
  simp [vecOf, hi]

/-- A table-phase output's committed claims hold when the program's claims (all of them, on the
committed columns) do. -/
theorem holds_of_committed {cl : List Verifier.ColumnClaim} {q : Column L.μ}
    {tout : Unit × TableOut (inst L tabs hτ)}
    (hmem : ∀ c ∈ tout.2.columns.toList,
      (⟨colOfL L tabs hτ c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈ cl)
    (h : ∀ c ∈ cl, CommittedHolds L tabs hτ q c) :
    ∀ c ∈ tout.2.columns.toList, (inst L tabs hτ).derived c.col = none → c.Holds q := by
  intro c hc hder
  have hloc := colLoc_colOfL L tabs hτ c.col
  have hi' : c.col.2.val < (tabs.get c.col.1).w := c.col.2.isLt
  obtain ⟨rec, off, hcol⟩ : ∃ rec off, (tabs.get c.col.1).cols[c.col.2.val]? =
      some (.com rec off) := by
    have hsome : ((tabs.get c.col.1).cols[c.col.2.val]?).isSome := by
      rw [List.getElem?_eq_getElem hi']; rfl
    obtain ⟨src, hsrc⟩ := Option.isSome_iff_exists.mp hsome
    cases src with
    | com rec off => exact ⟨rec, off, hsrc⟩
    | fix f ev =>
      exfalso
      have : (inst L tabs hτ).derived c.col ≠ none := by
        simp only [inst, Tab.fixedOf, hsrc, Option.map_some]; simp
      exact this hder
  have := h _ (hmem c hc) c.col.1.val c.col.2.val c.col.1.isLt hi' rec off hloc hcol
  unfold ColumnClaim.Holds
  rw [vecOf_toList] at this
  exact this

variable {β : Type} (C : List Ev → Set β) (stk : β → Column L.μ) (R : β → Prop) {L₀ : ℕ}
  {εmax : ℝ≥0∞}

/-- **`midBusTableSpec` with a post on the claims alone**: every candidate meeting `R` fails a
committed claim the phases return. -/
noncomputable def midBusTableSpec' (hsc : AllSc tabs) (hkey : KeysOk tabs)
    (hw : ∀ t ∈ tabs, 0 < t.w) (hfix : FixOk tabs) (G : List Ev → Prop)
    (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst L tabs hτ).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L tabs hτ) () (stk p) ∧ R p) h)
      (fun cl h ↦ Doomed C (fun p ↦ (∀ c ∈ cl, CommittedHolds L tabs hτ (stk p) c) ∧ R p) h)
      εmax (abError (inst L tabs hτ) L₀ + 0) T :=
  (midBusTableSpec L tabs hτ hsc C stk R hkey hw hfix G hCG hf hc hμ hab he4 hT hlam he3 hTf
    hxi).mono (fun _ h ↦ h)
    (fun cl h ⟨tout, hD, hmem, _⟩ p hp ⟨hall, hR⟩ ↦
      hD p hp ⟨holds_of_committed L tabs hτ hmem hall, hR⟩) le_rfl le_rfl le_rfl

/-- **The same on the commitments' blocks** (candidates `(qm, qr)`, the stack `stackOf`): every
candidate pair meeting `R` fails a committed claim on its `C_main`/`C_rec` block, under `LayOk`. -/
noncomputable def midBusTableSpecB (C : List Ev → Set (Column L.nuMain × Column L.nuRec))
    (R : Column L.nuMain × Column L.nuRec → Prop) (hlay : LayOk L tabs)
    (hsc : AllSc tabs) (hkey : KeysOk tabs)
    (hw : ∀ t ∈ tabs, 0 < t.w) (hfix : FixOk tabs) (G : List Ev → Prop)
    (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst L tabs hτ).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L tabs hτ) () (stackOf L p.1 p.2) ∧ R p) h)
      (fun cl h ↦ Doomed C (fun p ↦ (∀ c ∈ cl, BlockHolds L tabs p.1 p.2 c) ∧ R p) h)
      εmax (abError (inst L tabs hτ) L₀ + 0) T :=
  (midBusTableSpec' L tabs hτ C (fun p ↦ stackOf L p.1 p.2) R hsc hkey hw hfix G hCG hf hc hμ hab
    he4 hT hlam he3 hTf hxi).mono (fun _ h ↦ h)
    (fun cl h hD p hp ⟨hall, hR⟩ ↦ hD p hp ⟨fun c hc ↦
      (committedHolds_iff_block L tabs hτ hlay p.1 p.2 c).mpr (hall c hc), hR⟩) le_rfl le_rfl le_rfl

end Post

end Lvm.M3
