-- new for lvm (WP-9b): the fixed-column step after the table sumcheck (`require (tableCheck)`):
-- the derived columns' claims hold of every stack, so the table seam's doom is the committed
-- claims' doom. Built on WP-2's `TablePost` (`LvmFrontTablePhase`) and `Spec.require`.
import LvmM3FidFix
import LvmM3Loop

/-!
# The fixed-column check

The table phase hands on one claim per column of every table (`TablePost`); a fixed column of the
lvm instance is a derived column (`inst`, `derived`), its claims hold of every stack as soon as their
values are the column's extension. The program checks exactly that (`tableCheckVB`: every claim on
a fixed column has the closed form's value, `fixedEvalV`), and the closed forms are the extensions
(`FixOk`, `fixOk_lvmTabs`). So after the check, the table seam's doom is the doom of the committed
columns' claims (`TablePostC`): **`tableCheckSpec`**.

* `colLoc_colOfL`: the program's global column of the protocol's column `⟨j, i⟩` is located back
  at `(j, i)`;
* `derived_holds`: a claim on a derived column that passed the check holds of every stack;
* `fixOk_lvmTabs`: `FixOk` of the lvm tables from `GrpOk` (members listed once);
* `fixOk_arrs` (non-vacuity): the input arrays' address columns (and no group, no auxiliary
  table) meet `FixOk`.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.TableSumcheck CompPoly CMlPolynomialEval
open scoped ENNReal

/-! ## The global numbering, read back -/

theorem tableWidths_vTables (tabs : List Tab) :
    Verifier.tableWidths (vTables tabs) = tabs.map (·.w) := by
  simp only [Verifier.tableWidths, vTables, List.map_map]
  conv_rhs => rw [← List.zipIdx_map_fst 0 tabs, List.map_map]
  exact List.map_congr_left fun _ _ ↦ by simp [vTable, Verifier.Table.width]

theorem base_eq (tabs : List Tab) {j : ℕ} (hj : j < tabs.length) :
    (Verifier.globalColumnBases (vTables tabs)).getD j 0 =
      Verifier.globalColumnCount + ((tabs.map (·.w)).take j).sum := by
  simp [Verifier.globalColumnBases, length_vTables, tableWidths_vTables, List.getD_eq_getElem?_getD, hj]

theorem sum_take_mono (l : List ℕ) {a b : ℕ} (h : a ≤ b) : (l.take a).sum ≤ (l.take b).sum := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  omega

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

/-- **The protocol's column `⟨j, i⟩` is located back** from its global number. -/
theorem colLoc_colOfL (c : (inst L tabs hτ).ColumnId) :
    colLoc tabs (colOfL L tabs hτ c) = some (c.1.val, c.2.val) := by
  obtain ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ := c
  have hj' : j < tabs.length := hj
  have hi' : i < tabs[j].w := hi
  have hw : ∀ k (hk : k < tabs.length), (tabs[k]?.map (·.w)).getD 0 = tabs[k].w := fun k hk ↦ by
    simp [List.getElem?_eq_getElem hk]
  unfold colLoc colOfL
  simp only
  rw [Option.map_eq_some_iff]
  refine ⟨j, ?_, ?_⟩
  · rw [List.find?_range_eq_some]
    refine ⟨?_, List.mem_range.mpr hj, fun k hk ↦ ?_⟩
    · rw [hw j hj, base_eq tabs hj]
      simp [hi']
    · have hk' : k < tabs.length := by omega
      rw [hw k hk', base_eq tabs hk', base_eq tabs hj]
      have h1 : ((tabs.map (·.w)).take k).sum + tabs[k].w ≤ ((tabs.map (·.w)).take j).sum := by
        have := sum_take_mono (tabs.map (·.w)) (show k + 1 ≤ j by omega)
        rwa [List.sum_take_succ _ _ (by simpa using hk'), List.getElem_map] at this
      have hn : ¬ (Verifier.globalColumnCount + ((tabs.map (·.w)).take k).sum ≤
          Verifier.globalColumnCount + ((tabs.map (·.w)).take j).sum + i ∧
          Verifier.globalColumnCount + ((tabs.map (·.w)).take j).sum + i <
            Verifier.globalColumnCount + ((tabs.map (·.w)).take k).sum + tabs[k].w) := by omega
      simp [hn]
  · simp [base_eq tabs hj]

/-! ## A checked claim on a derived column holds -/

/-- **A claim on a derived (fixed) column that passed the check holds of every stack.** -/
theorem derived_holds (hfix : FixOk tabs) (claims : List Verifier.ColumnClaim)
    (hchk : tableCheckVB tabs claims = true) (c : LeanVM.Protocol.ColumnClaim (inst L tabs hτ))
    (hd : (inst L tabs hτ).derived c.col ≠ none)
    (hc : (⟨colOfL L tabs hτ c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈ claims)
    (q : Column (inst L tabs hτ).μ) : c.Holds q := by
  obtain ⟨⟨⟨j, hj⟩, ⟨i, hi⟩⟩, pt, v⟩ := c
  have htj : tabs.get ⟨j, hj⟩ = tabs[j] := rfl
  -- the column is fixed: `.fix f ev`
  have hfo : tabs[j].fixedOf i ≠ none := by
    intro h; apply hd
    show Option.map _ ((tabs.get ⟨j, hj⟩).fixedOf i) = none
    rw [htj, h]; rfl
  obtain ⟨f, ev, hcol⟩ : ∃ f ev, tabs[j].cols[i]? = some (.fix f ev) := by
    unfold Tab.fixedOf at hfo
    split at hfo
    · exact ⟨_, _, by assumption⟩
    · exact absurd rfl hfo
  have hcolq : (inst L tabs hτ).column q ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ = fixedColumn tabs[j].τ f := by
    simp [M3Instance.column, inst, Tab.fixedOf, htj, hcol]
  -- the check on its claim
  have hev : fixedEvalV tabs (colOfL L tabs hτ ⟨⟨j, hj⟩, ⟨i, hi⟩⟩) =
      some fun pt ↦ FE.toExt3 (ev (pt.map FE.ofExt3)) := by
    unfold fixedEvalV
    rw [colLoc_colOfL]
    simp [List.getElem?_eq_getElem hj, hcol]
  have hv := List.all_eq_true.mp hchk _ hc
  simp only [hev, decide_eq_true_eq] at hv
  -- the closed form is the extension
  have hmem : ColSrc.fix f ev ∈ tabs[j].cols := List.mem_of_getElem? hcol
  have hfx := hfix _ (List.getElem_mem hj) f ev hmem (pt.toList.map FE.ofExt3) (by simp; rfl)
  show eval₂Mle ((inst L tabs hτ).column q ⟨⟨j, hj⟩, ⟨i, hi⟩⟩).values (algebraMap K E) pt = v
  rw [hcolq, hv, hfx, toExt3_mle_fixed]
  rfl

/-! ## The step -/

section Post

variable (I : M3Instance) (cands : Word → Set (∀ i, TheOracle I i)) (input : I.Stmt)

/-- **The table seam after the fixed-column check**: `TablePost` with the doom on the committed
columns' claims only (a derived column's claim holds of every stack). -/
def TablePostC (colOf : I.ColumnId → ℕ) (claims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ (W : Word) (tout : I.Stmt × TableOut I), firstWord h = some W ∧
    (∀ o ∈ cands W, ¬ ((∀ c ∈ tout.2.columns.toList, I.derived c.col = none → c.Holds (theStack o)) ∧
      I.PublicLinesHold tout.1 (theStack o) ∧ I.auxAt tout.2.point.toList (theStack o))) ∧
    tout.1 = input ∧
    (∀ c ∈ tout.2.columns.toList, (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
      claims) ∧
    ∃ (st : SumcheckRound.Stmt (Data I) E I.τmax) (v : Vector E I.tableColumns),
      tout = tableOut I st v

end Post

/-- **The fixed-column step** (`require (tableCheck)` after the table sumcheck): from the table
seam on the wire to the doom of the committed columns' claims, when the closed forms are the
extensions (`FixOk`). No challenge, no error. -/
noncomputable def tableCheckSpec (hfix : FixOk tabs) (cands : Word → Set (∀ i, TheOracle (inst L tabs hτ) i))
    (claims : List Verifier.ColumnClaim) {εmax T : ℝ≥0∞} :
    Spec (VerifierProgram.require (tableCheckVB tabs claims = true))
      (TablePost (inst L tabs hτ) cands () (colOfL L tabs hτ) claims)
      (fun _ ↦ TablePostC (inst L tabs hτ) cands () (colOfL L tabs hτ) claims) εmax T T :=
  Spec.require fun _ hp hchk ↦ by
    obtain ⟨W, tout, hW, hD, h1, hcl, hout⟩ := hp
    refine ⟨W, tout, hW, fun o ho ⟨hc, hpub, haux⟩ ↦ hD o ho ⟨fun c hcm ↦ ?_, hpub, haux⟩, h1, hcl, hout⟩
    by_cases hd : (inst L tabs hτ).derived c.col = none
    · exact hc c hcm hd
    · exact derived_holds L tabs hτ hfix claims hchk c hd (hcl c hcm) _

/-! ## `FixOk` of the lvm tables -/

/-- **`FixOk` of the lvm tables** from `GrpOk` (its `nodup`: each group's members listed once), the
public arrays' `PubOk` and the auxiliary tables' own `FixOk`. -/
theorem fixOk_lvmTabs {Q : Loop.Program} {pl : ℕ → Loop.Var → Bool × ℕ} {groups : List Grp}
    {arrs : List InArr} {aux : List Tab} (hg : GrpOk Q groups) (hpub : PubOk arrs)
    (haux : FixOk aux) : FixOk (lvmTabs Q pl groups arrs aux) :=
  fixOk_lvmTabs_of Q pl groups arrs aux
    (fun g hg' m hm ↦ by
      obtain ⟨p, hp, -, hle, hdvd⟩ := hg.mem g hg' m hm
      exact ⟨p, hp, hle, hdvd⟩)
    hg.disj hg.nodup hpub haux

/-- **Non-vacuity**: committed input arrays' address columns meet `FixOk` (every array table has a
fixed column, so the check has content). -/
theorem fixOk_arrs (Q : Loop.Program) (pl : ℕ → Loop.Var → Bool × ℕ) (arrs : List InArr)
    (hc : ∀ a ∈ arrs, a.pub = none) : FixOk (lvmTabs Q pl [] arrs []) :=
  fixOk_lvmTabs_of Q pl [] arrs [] (by simp) (by simp) (by simp)
    (fun a ha f e he ↦ by rw [hc a ha] at he; cases he) (fun _ h ↦ by simp at h)

end Lvm.M3
