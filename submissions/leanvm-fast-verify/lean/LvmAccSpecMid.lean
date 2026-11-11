-- new for lvm (AC-S): V_S phases 2–3b in the form WP-14's `MidSpec` composes, as WP-9b's
-- `midBusTableSpec` → `midBusTableSpec'` → `midBusTableSpecB` → `midBusTableSpecS` (`LvmM3Mid`,
-- `LvmM3MidPost`, `LvmM3MidCert`) do for phases 2–3, with `lbusTableAccSpec` in place of
-- `lbusTableCheckSpec` and `AccOk acc_in` carried in the candidates' predicate.
import LvmAccSpecT
import LvmM3MidCert

/-!
# Phases 2–3b on WP-14's candidate pairs

* `cg_accProg`, **`noCG_lbusTableAccProg`**: phases 2–3b commit nothing and ask no proof of work;
* `midBusTableAccSpec` (glued at the candidate set, WP-9b's `Spec.glue`), `midBusTableAccSpec'`,
  `midBusTableAccSpecB`;
* **`midBusTableAccSpecS`** (WP-14's objects, `lay26`): from `RootShape ∧ Doomed candPairs (M3Holds ∘
  stackOf ∧ R ∧ AccOk acc_in)` to `Doomed candPairs ((∀ c ∈ cl, BlockHolds …) ∧ R) ∧ RootShape`:
  WP-9b's `midBusTableSpecS` with `AccOk` discharged (BLUEPRINT §12.6: `Good := GoodN ∧ AccOk`).
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (Tab sumcheckTabs vTables vLayout busResV Lay inst colOfL TablePostC lvmBusTableProg
  NoCG cg_ret cg_sample cg_readScalar cg_require cg_readScalars cg_sampleChallenges cg_lvmBusProg
  cg_tablePhaseClaims MidTablePost CandIdx candIdx candSet oraOf publicLines_lvm auxAt_lvm
  CommittedHolds BlockHolds stackOf lay26 holds_of_committed committedHolds_iff_block)
open scoped ENNReal

/-! ## No commitment, no proof of work -/

theorem cg_accProg (dk D : ℕ) (ok : Bool) (yIn : E) (a : List E) (yOwn : List E → E)
    (bOf : List E → List E) (Φ : List E → E) : NoCG (accProg dk D ok yIn a yOwn bOf Φ) :=
  Lvm.M3.NoCG.bind (cg_sampleChallenges dk) fun _ ↦ Lvm.M3.NoCG.bind (cg_readScalars _) fun _ ↦
    Lvm.M3.NoCG.bind cg_sample fun _ ↦ Lvm.M3.NoCG.bind cg_readScalar fun _ ↦ cg_require _

/-- **V_S phases 2–3b commit nothing and ask no proof of work.** -/
theorem noCG_lbusTableAccProg (P : Params) (tabs : Pub → List Tab) (pub : Pub) (μ : ℕ) :
    NoCG (lbusTableAccProg P tabs pub μ) :=
  Lvm.M3.NoCG.bind (Lvm.M3.NoCG.bind (cg_lvmBusProg μ) fun _ ↦ cg_tablePhaseClaims _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind (cg_accProg _ _ _ _ _ _ _ _) fun _ ↦ cg_ret _

/-! ## Glued at the candidate set -/

section Mid

variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
  {β : Type} (C : List Ev → Set β) (stk : β → Column L.μ) (R : β → Prop) {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **Phases 2–3b in `MidSpec`'s form** (WP-9b's `midBusTableSpec` with phase 3b): from
`Doomed C (M3Holds ∘ stk ∧ R ∧ AccOk acc_in)` to `MidTablePost`. -/
noncomputable def midBusTableAccSpec (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst L (sumcheckTabs (tabs pub)) hτL).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L (sumcheckTabs (tabs pub)) hτL) () (stk p) ∧ R p ∧
          AccOkE P tabs pub) h)
      (MidTablePost L (sumcheckTabs (tabs pub)) hτL C stk R) εmax
      (abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  let σ := candIdx L (sumcheckTabs (tabs pub)) hτL C stk R hf hc
  ((Lvm.M3.Spec.glue (Pre := fun (S : CandIdx L (sumcheckTabs (tabs pub)) hτL L₀) ↦
        HDoom (candsA (fun _ ↦ S.1) (AccOkE P tabs pub))
          (Seam.commit (inst L (sumcheckTabs (tabs pub)) hτL)) ())
      (Post := fun (S : CandIdx L (sumcheckTabs (tabs pub)) hτL L₀) ↦
        TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) (fun _ ↦ S.1) ()
          (colOfL L (sumcheckTabs (tabs pub)) hτL))
      σ G (fun h₀ l hG ↦ by simp only [σ, candIdx, candSet, hCG h₀ l hG])
      fun S ↦ lbusTableAccSpec L P tabs pub hτL hsc (fun _ ↦ S.1) H hkey hw (fun _ ↦ S.2.1)
        (fun _ ↦ S.2.2) hμ hab he4 hT hlam he3 hTa hxi hD hTf)).mono
    (fun h ⟨hG, ⟨W, hW⟩, hDm⟩ ↦ ⟨hG, W, hW, fun o ⟨ho, hA⟩ hR ↦ by
      obtain ⟨p, ⟨hpC, hpR⟩, rfl⟩ := ho
      exact hDm p hpC ⟨hR, hpR, hA⟩⟩)
    (fun cl h hp ↦ by
      obtain ⟨W, tout, -, hDm, -, hcl, hout⟩ := hp
      refine ⟨tout, fun p hpC ⟨hcm, hpR⟩ ↦ hDm _ ⟨p, ⟨hpC, hpR⟩, rfl⟩
        ⟨hcm, publicLines_lvm L _ hτL _, auxAt_lvm L _ hτL _ _⟩, hcl, hout⟩)
    le_rfl le_rfl le_rfl

/-- **Phases 2–3b with a post on the claims alone** (WP-9b's `midBusTableSpec'`). -/
noncomputable def midBusTableAccSpec' (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst L (sumcheckTabs (tabs pub)) hτL).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L (sumcheckTabs (tabs pub)) hτL) () (stk p) ∧ R p ∧
          AccOkE P tabs pub) h)
      (fun cl h ↦ Doomed C (fun p ↦ (∀ c ∈ cl, CommittedHolds L (sumcheckTabs (tabs pub)) hτL (stk p) c) ∧
        R p) h) εmax (abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  (midBusTableAccSpec L P tabs pub hτL hsc C stk R H hkey hw G hCG hf hc hμ hab he4 hT hlam he3 hTa
    hxi hD hTf).mono (fun _ h ↦ h)
    (fun cl h ⟨tout, hDm, hmem, _⟩ p hp ⟨hall, hR⟩ ↦
      hDm p hp ⟨holds_of_committed L _ hτL hmem hall, hR⟩) le_rfl le_rfl le_rfl

end Mid

section Blocks

variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
  {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **Phases 2–3b on the commitments' blocks** (WP-9b's `midBusTableSpecB`). -/
noncomputable def midBusTableAccSpecB (C : List Ev → Set (Column L.nuMain × Column L.nuRec))
    (R : Column L.nuMain × Column L.nuRec → Prop) (hlay : Lvm.M3.LayOk L (sumcheckTabs (tabs pub)))
    (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (G : List Ev → Prop) (hCG : ∀ h₀ l, G h₀ → C (h₀ ++ l) = C h₀)
    (hf : ∀ h, (C h).Finite) (hc : ∀ h, (C h).ncard ≤ L₀)
    (hμ : (inst L (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst L (sumcheckTabs (tabs pub)) hτL).μBus)
      (fun h ↦ G h ∧ (∃ W, firstWord h = some W) ∧
        Doomed C (fun p ↦ M3Holds (inst L (sumcheckTabs (tabs pub)) hτL) () (stackOf L p.1 p.2) ∧ R p ∧
          AccOkE P tabs pub) h)
      (fun cl h ↦ Doomed C (fun p ↦ (∀ c ∈ cl, BlockHolds L (sumcheckTabs (tabs pub)) p.1 p.2 c) ∧ R p) h)
      εmax (abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  (midBusTableAccSpec' L P tabs pub hτL hsc C (fun p ↦ stackOf L p.1 p.2) R H hkey hw G hCG hf hc hμ
    hab he4 hT hlam he3 hTa hxi hD hTf).mono (fun _ h ↦ h)
    (fun cl h hDm p hp ⟨hall, hR⟩ ↦ hDm p hp ⟨fun c hc ↦
      (committedHolds_iff_block L _ hτL hlay p.1 p.2 c).mpr (hall c hc), hR⟩) le_rfl le_rfl le_rfl

end Blocks

section Pairs

variable (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ lay26.μ) {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **V_S phases 2–3b on WP-14's candidate pairs** (WP-9b's `midBusTableSpecS` with phase 3b in place
of the fixed-column check, BLUEPRINT §12.6): from `RootShape` and the root doom of
`M3Holds ∘ stackOf ∧ R ∧ AccOk acc_in` to the doom of the returned claims on the pairs' blocks, with
`R`, and `RootShape`. `AccOk acc_in` is discharged: it is not in the post. -/
noncomputable def midBusTableAccSpecS (R : Column 26 × Column 19 → Prop)
    (hlay : Lvm.M3.LayOk lay26 (sumcheckTabs (tabs pub))) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
    (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (hc : ∀ h, (Lvm.ASM.candPairs h).ncard ≤ L₀)
    (hμ : (inst lay26 (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst lay26 (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞}
    (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst lay26 (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst lay26 (sumcheckTabs (tabs pub)) hτL).μBus)
      (fun h ↦ Lvm.ASM.RootShape h ∧ Doomed Lvm.ASM.candPairs
        (fun p ↦ M3Holds (inst lay26 (sumcheckTabs (tabs pub)) hτL) () (stackOf lay26 p.1 p.2) ∧ R p ∧
          AccOkE P tabs pub) h)
      (fun cl h ↦ Doomed Lvm.ASM.candPairs
        (fun p ↦ (∀ c ∈ cl, BlockHolds lay26 (sumcheckTabs (tabs pub)) p.1 p.2 c) ∧ R p) h ∧
          Lvm.ASM.RootShape h)
      εmax (abError (inst lay26 (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  ((midBusTableAccSpecB lay26 P tabs pub hτL hsc Lvm.ASM.candPairs R hlay H hkey hw
      (fun h ↦ 2 ≤ (commits h).length) (fun h₀ l h2 ↦ Lvm.M3.candPairs_append h₀ l h2)
      (fun _ ↦ Set.toFinite _) hc hμ hab he4 hT hlam he3 hTa hxi hD hTf).frame Lvm.ASM.RootShape
    (fun _ _ hl hr ↦ Lvm.M3.rootShape_append
      ((noCG_lbusTableAccProg P tabs pub _).1.reach_commits hl) hr)).mono
    (fun h ⟨hr, hDm⟩ ↦ ⟨⟨Lvm.M3.rootShape_two hr, Lvm.M3.rootShape_firstWord hr, hDm⟩, hr⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Pairs

end Lvm.Acc
