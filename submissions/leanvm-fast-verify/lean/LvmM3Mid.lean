-- new for lvm (WP-9b): the bus phase, the table sumcheck and the fixed-column check of the lvm
-- instance in the form WP-14's `MidSpec` composes (`Doomed C (… ∧ R)` over the candidate pairs,
-- as WP-8's `kgSpec`), from the history-doom specs `lbusTableSpec` (LvmM3FidTab) and
-- `tableCheckSpec` (LvmM3FidFixC) through a gluing rule (`Spec.glue`, new).
import LvmM3FidTab
import LvmM3FidFixC
import LvmFrontMech

/-!
# The bus and table phases for `MidSpec`

* **`lbusTableCheckSpec`**: V_S phases 2–3 (`decideProg`'s bus phase, table sumcheck and
  `require (tableCheck)`) on the program objects of `LvmM3Fid`: from the commitment's doom to the
  committed claims' doom (`TablePostC`), over history candidates `cands`.
* **`Spec.glue`**: a family of specifications of one program indexed by `σ h₀` is one
  specification, when `σ` does not move along a run (`G h₀ → σ (h₀ ++ l) = σ h₀`). The fields of
  `Spec` are statements at each start `h₀`, so the glued doom and potential are the family's at
  `σ h₀` (where `G h₀` fails, no doom and potential `1`).
* **`midBusTableSpec`**: `lbusTableCheckSpec` glued at the candidate set `stk '' {p ∈ C h₀ | R p}`
  (candidates `β`, e.g. WP-14's pairs `(qm, qr)`, `stk` their stack). Pre: WP-14's root doom
  `Doomed C (M3Holds ∘ stk ∧ R)` (with a first commitment and `G`); Post `MidTablePost`: some table
  seam output whose committed claims, carried with `R`, are doomed on `C`, and whose claims are
  among the program's (the claims WP-14 hands to the openings).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

/-! ## Phases 2–3 with the fixed-column check -/

/-- **V_S phases 2–3** on the program objects: the bus phase, the table sumcheck, then the
fixed-column check (`decideProg`'s `require (m.tableCheck pub evals)`); the claims. -/
def lbusTableCheckProg (tabs : List Tab) (μ : ℕ) : VerifierProgram (List Verifier.ColumnClaim) :=
  (lvmBusTableProg (vTables tabs) (vLayout tabs) μ (busResV tabs)).bind fun cl ↦
    (VerifierProgram.require (tableCheckVB tabs cl = true)).bind fun _ ↦ VerifierProgram.ret cl

section Phase

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)
  (cands : Word → Set (∀ i, TheOracle (inst L tabs hτ) i)) {εmax : ℝ≥0∞}

/-- **The lvm bus phase, the table sumcheck and the fixed-column check**: from the commitment's
doom to the committed columns' claims' doom (`TablePostC`), with `lbusTableSpec`'s side
conditions and errors and the closed forms' `FixOk`. -/
noncomputable def lbusTableCheckSpec (hkey : KeysOk tabs) (hw : ∀ t ∈ tabs, 0 < t.w)
    (hfix : FixOk tabs) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : (inst L tabs hτ).μBus ≠ 0) (hab : abError (inst L tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst L tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst L tabs hτ).μBus)
      (HDoom cands (Seam.commit (inst L tabs hτ)) ())
      (TablePostC (inst L tabs hτ) cands () (colOfL L tabs hτ)) εmax
      (abError (inst L tabs hτ) L₀ + 0) T :=
  (lbusTableSpec L tabs hτ hsc cands hkey hw hfin hcard hμ hab he4 hT hlam he3 hTf hxi).bind
    fun cl ↦ (tableCheckSpec L tabs hτ hfix cands cl (T := T)).bind fun _ ↦
      Spec.ret (Post := TablePostC (inst L tabs hτ) cands () (colOfL L tabs hτ)) cl

end Phase

/-! ## Gluing a family of specifications -/

section Glue

variable {α ι : Type} {p : VerifierProgram α} {Pre : ι → List Ev → Prop}
  {Post : ι → α → List Ev → Prop} {εmax L T : ℝ≥0∞}

theorem avg_one : (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ _c : E, (1 : ℝ≥0∞) ≤ 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_le_one _

open Classical in
/-- **Gluing.** A specification of `p` for every index, the index read off the start `σ h₀`, stable
along a run where `G h₀` holds, is one specification: doom and potential are the index's (no doom,
potential `1`, where `G h₀` fails). -/
noncomputable def Spec.glue (σ : List Ev → ι) (G : List Ev → Prop)
    (hσ : ∀ h₀ l, G h₀ → σ (h₀ ++ l) = σ h₀) (F : ∀ i, Spec p (Pre i) (Post i) εmax L T) :
    Spec p (fun h ↦ G h ∧ Pre (σ h) h) (fun a h ↦ Post (σ h) a h) εmax L T where
  D h₀ l := G h₀ ∧ (F (σ h₀)).D h₀ l
  V h₀ l := if G h₀ then (F (σ h₀)).V h₀ l else 1
  le_one h₀ l := by split_ifs <;> simp [(F _).le_one]
  start_D h₀ hp := ⟨hp.1, (F _).start_D h₀ hp.2⟩
  start_V h₀ hp := by rw [if_pos hp.1]; exact (F _).start_V h₀ hp.2
  read x hr ha hD := ⟨hD.1, (F _).read x hr ha hD.2⟩
  grind hr ha hD := ⟨hD.1, (F _).grind hr ha hD.2⟩
  commit word hr ha hw hD := ⟨hD.1, (F _).commit word hr ha hw hD.2⟩
  sample {h₀ l k} hr ha := by
    by_cases hG : G h₀
    · simp only [if_pos hG]; exact (F _).sample hr ha
    · simp only [if_neg hG]; exact avg_one
  query {h₀ l i ps k rows} hr ha hans := by
    by_cases hG : G h₀
    · simp only [if_pos hG]; exact (F _).query hr ha hans
    · simp only [if_neg hG]; exact le_rfl
  moveEnd {h₀ l q} hr ha hm hD := by
    by_cases hG : G h₀
    · rw [if_pos hG]; exact (F _).moveEnd hr ha hm fun h ↦ hD ⟨hG, h⟩
    · rw [if_neg hG]
  retEnd {h₀ l a} hr ha hD := by
    by_cases hG : G h₀
    · rw [if_pos hG]; exact (F _).retEnd hr ha fun h ↦ hD ⟨hG, h⟩
    · rw [if_neg hG]
  retDoom hr ha hD := by rw [if_pos hD.1]; exact (F _).retDoom hr ha hD.2
  post {h₀ l a} hr ha hD := by
    rw [hσ h₀ l hD.1]; exact (F _).post hr ha hD.2
  bound hr hne hm hD := by rw [if_pos hD.1]; exact (F _).bound hr hne hm hD.2

end Glue

/-! ## The doomed candidates' form -/

section Mid

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) (hsc : AllSc tabs)
  {β : Type} (C : List Ev → Set β) (stk : β → Column L.μ) (R : β → Prop) {L₀ : ℕ}
  {εmax : ℝ≥0∞}

/-- The stack of a candidate as the instance's one oracle. -/
def oraOf (q : Column L.μ) : ∀ i, TheOracle (inst L tabs hτ) i := fun _ ↦ q

/-- The candidate set the history-doom specs run at: the stacks of the candidates meeting `R`,
finite and at most `L₀` when `C h` is. -/
def candSet (h : List Ev) : Set (∀ i, TheOracle (inst L tabs hτ) i) :=
  (fun p ↦ oraOf L tabs hτ (stk p)) '' {p | p ∈ C h ∧ R p}

theorem candSet_finite {h : List Ev} (hf : (C h).Finite) : (candSet L tabs hτ C stk R h).Finite :=
  (hf.subset fun _ hp ↦ hp.1).image _

theorem candSet_ncard {h : List Ev} (hf : (C h).Finite) :
    (candSet L tabs hτ C stk R h).ncard ≤ (C h).ncard :=
  (Set.ncard_image_le (hf.subset fun _ hp ↦ hp.1)).trans (Set.ncard_le_ncard (fun _ hp ↦ hp.1) hf)

/-- The index of the glued family: a candidate set, finite and at most `L₀`. -/
abbrev CandIdx (L₀ : ℕ) : Type :=
  {S : Set (∀ i, TheOracle (inst L tabs hτ) i) // S.Finite ∧ S.ncard ≤ L₀}

/-- The candidate set of a history as an index. -/
noncomputable def candIdx (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀) (h : List Ev) :
    CandIdx L tabs hτ L₀ :=
  ⟨candSet L tabs hτ C stk R h, candSet_finite L tabs hτ C stk R (hf h),
    (candSet_ncard L tabs hτ C stk R (hf h)).trans (hc h)⟩

/-- **The table seam for `MidSpec`**: a table seam output whose committed claims, with `R`, hold of
no candidate's stack, every claim of which the program returned. (The public lines and the Keccak
predicate are empty for the lvm instance.) -/
def MidTablePost (claims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ tout : Unit × TableOut (inst L tabs hτ),
    Doomed C (fun p ↦ (∀ c ∈ tout.2.columns.toList, (inst L tabs hτ).derived c.col = none →
      c.Holds (stk p)) ∧ R p) h ∧
    (∀ c ∈ tout.2.columns.toList,
      (⟨colOfL L tabs hτ c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈ claims) ∧
    ∃ (st : SumcheckRound.Stmt (Data (inst L tabs hτ)) E (inst L tabs hτ).τmax)
      (v : Vector E (inst L tabs hτ).tableColumns), tout = tableOut (inst L tabs hτ) st v

theorem publicLines_lvm (q : Column L.μ) : (inst L tabs hτ).PublicLinesHold () q := by
  intro l hl; simp [inst] at hl

theorem auxAt_lvm (pt : List E) (q : Column L.μ) : (inst L tabs hτ).auxAt pt q := by
  intro r hr; simp [inst] at hr

/-- **The bus phase, the table sumcheck and the fixed-column check in `MidSpec`'s form**: from
`Doomed C (M3Holds ∘ stk ∧ R)` (at a history with a first commitment, where `G` holds) to
`MidTablePost`. `C` is finite with at most `L₀` candidates, and stable along runs from where `G`
holds (`hCG`; for WP-14's `candPairs`, `G h := 2 ≤ (commits h).length`). -/
noncomputable def midBusTableSpec (hkey : KeysOk tabs) (hw : ∀ t ∈ tabs, 0 < t.w)
    (hfix : FixOk tabs) (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
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
      (MidTablePost L tabs hτ C stk R) εmax (abError (inst L tabs hτ) L₀ + 0) T :=
  let σ := candIdx L tabs hτ C stk R hf hc
  ((Spec.glue (Pre := fun (S : CandIdx L tabs hτ L₀) ↦
        HDoom (fun _ ↦ S.1) (Seam.commit (inst L tabs hτ)) ())
      (Post := fun (S : CandIdx L tabs hτ L₀) ↦
        TablePostC (inst L tabs hτ) (fun _ ↦ S.1) () (colOfL L tabs hτ))
      σ G (fun h₀ l hG ↦ by simp only [σ, candIdx, candSet, hCG h₀ l hG])
      fun S ↦ lbusTableCheckSpec L tabs hτ hsc (fun _ ↦ S.1) hkey hw hfix
        (fun _ ↦ S.2.1) (fun _ ↦ S.2.2) hμ hab he4 hT hlam he3 hTf hxi)).mono
    (fun h ⟨hG, ⟨W, hW⟩, hD⟩ ↦ ⟨hG, W, hW, fun o ho hR ↦ by
      obtain ⟨p, ⟨hpC, hpR⟩, rfl⟩ := ho
      exact hD p hpC ⟨hR, hpR⟩⟩)
    (fun cl h hp ↦ by
      obtain ⟨W, tout, -, hD, -, hcl, hout⟩ := hp
      refine ⟨tout, fun p hpC ⟨hcm, hpR⟩ ↦ hD _ ⟨p, ⟨hpC, hpR⟩, rfl⟩
        ⟨hcm, publicLines_lvm L tabs hτ _, auxAt_lvm L tabs hτ _ _⟩, hcl, hout⟩)
    le_rfl le_rfl le_rfl

end Mid

end Lvm.M3
