-- new for lvm (WP-9b): the bus/table phases at WP-14's candidate pairs (`LvmCertS.candPairs`,
-- `RootShape`), from `midBusTableSpecB` and WP-14's `Spec.frame` (LvmCertSFrame).
import LvmM3MidPost
import LvmCertS

/-!
# The bus/table phases on WP-14's candidate pairs

* `wordOf_commits_append`, `candPairs_append`: the candidate pairs read only the first two
  commitments, so they do not move once two are made (the `hCG` of `midBusTableSpec*`, with
  `G h := 2 ≤ (commits h).length`);
* `rootShape_two`, `rootShape_firstWord`, `rootShape_append` (after a run that commits nothing);
* **`midBusTableSpecS`**: V_S phases 2–3 from `RootShape ∧ Doomed candPairs (M3Holds ∘ stackOf ∧ R)`
  to `Doomed candPairs ((∀ c ∈ cl, BlockHolds …) ∧ R) ∧ RootShape`, the stack of a pair being
  `stackOf ⟨26, 19⟩ qm qr` (`μ = 27`, `C_rec` at `2^26`).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck LeanVM.Protocol.Whir.Sound CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

/-- A commitment's word does not change once it is made. -/
theorem wordOf_commits_append (h₀ l : List Ev) {i : ℕ} (hi : i < (commits h₀).length) :
    wordOf (commits (h₀ ++ l)) i = wordOf (commits h₀) i := by
  simp only [wordOf, commits_append, List.getElem?_append_left hi]

/-- **The candidate pairs do not move once two commitments are made.** -/
theorem candPairs_append (h₀ l : List Ev) (h2 : 2 ≤ (commits h₀).length) :
    Lvm.ASM.candPairs (h₀ ++ l) = Lvm.ASM.candPairs h₀ := by
  simp only [Lvm.ASM.candPairs, wordOf_commits_append h₀ l (show 0 < (commits h₀).length by omega),
    wordOf_commits_append h₀ l (show 1 < (commits h₀).length by omega)]

theorem rootShape_two {h : List Ev} (hr : Lvm.ASM.RootShape h) : 2 ≤ (commits h).length := by
  obtain ⟨Wm, Wr, hc, -⟩ := hr; rw [hc]; simp

theorem rootShape_firstWord {h : List Ev} (hr : Lvm.ASM.RootShape h) : ∃ W, firstWord h = some W := by
  obtain ⟨Wm, Wr, hc, -⟩ := hr
  exact ⟨Wm, by simp [firstWord, hc]⟩

/-- `RootShape` survives a run that commits nothing. -/
theorem rootShape_append {h₀ l : List Ev} (hl : commits l = []) (hr : Lvm.ASM.RootShape h₀) :
    Lvm.ASM.RootShape (h₀ ++ l) := by
  obtain ⟨Wm, Wr, hc, hw⟩ := hr
  exact ⟨Wm, Wr, by rw [commits_append, hl, List.append_nil, hc], hw⟩

/-- WP-14's commitment sizes as a layout: `C_main` 2^26 words, `C_rec` 2^19. -/
abbrev lay26 : Lay := ⟨26, 19⟩

variable (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ lay26.μ) {L₀ : ℕ} {εmax : ℝ≥0∞}

/-- **V_S phases 2–3 on WP-14's candidate pairs**: from `RootShape` and the root doom of
`M3Holds ∘ stackOf ∧ R` to the doom of the returned claims on the pairs' blocks, with `R`, and
`RootShape`. `hc` is the unique-decoding bound on the candidate pairs (WP-14's
`candPairs_ncard_le_one` for `L₀ = 1`). -/
noncomputable def midBusTableSpecS (R : Column 26 × Column 19 → Prop) (hlay : LayOk lay26 tabs)
    (hsc : AllSc tabs) (hkey : KeysOk tabs) (hw : ∀ t ∈ tabs, 0 < t.w) (hfix : FixOk tabs)
    (hc : ∀ h, (Lvm.ASM.candPairs h).ncard ≤ L₀)
    (hμ : (inst lay26 tabs hτ).μBus ≠ 0) (hab : abError (inst lay26 tabs hτ) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax)
    (hTf : T ≤ εmax)
    (hxi : xiError (inst lay26 tabs hτ) L₀ +
      sumcheckLead (List.replicate ((vLayout tabs).tableLogHeights.foldl max 0) none) T ≤ εmax) :
    Spec (lbusTableCheckProg tabs (inst lay26 tabs hτ).μBus)
      (fun h ↦ Lvm.ASM.RootShape h ∧ Doomed Lvm.ASM.candPairs
        (fun p ↦ M3Holds (inst lay26 tabs hτ) () (stackOf lay26 p.1 p.2) ∧ R p) h)
      (fun cl h ↦ Doomed Lvm.ASM.candPairs
        (fun p ↦ (∀ c ∈ cl, BlockHolds lay26 tabs p.1 p.2 c) ∧ R p) h ∧ Lvm.ASM.RootShape h)
      εmax (abError (inst lay26 tabs hτ) L₀ + 0) T :=
  ((midBusTableSpecB lay26 tabs hτ Lvm.ASM.candPairs R hlay hsc hkey hw hfix
      (fun h ↦ 2 ≤ (commits h).length) (fun h₀ l h2 ↦ candPairs_append h₀ l h2)
      (fun _ ↦ Set.toFinite _) hc hμ hab he4 hT hlam he3 hTf hxi).frame Lvm.ASM.RootShape
    (fun _ _ hl hr ↦ rootShape_append ((noCG_lbusTableCheckProg tabs _).1.reach_commits hl) hr)).mono
    (fun h ⟨hr, hD⟩ ↦ ⟨⟨rootShape_two hr, rootShape_firstWord hr, hD⟩, hr⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.M3
