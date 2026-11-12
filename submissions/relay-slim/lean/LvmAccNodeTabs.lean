-- New for lvm (AC-N, A23): two facts of WP-16a's P20 tables `M3.tabsP20` that A23 owes the
-- assembly: `Φ` is one polynomial (`FixStatic`: only `PUB`'s value column reads the header, and it
-- is not in `fixCols`), and `PUB`'s value column at sumcheck table `P20.pubTab` has the closed form
-- `pubEval` of the header lanes (AC-S's `AccInst.pubEv`, `accMidHyp_of`'s `hpub`).
import LvmQAsmV
import LvmVEqMid

/-!
# The P20 tables: `FixStatic` and `PUB`'s closed form

`M3.tabsP20 P` is the groups' tables, the 43 input arrays before `PUB`, `PUB`'s table (the only
part that reads `P`: its value column `fix (pubCell vals) (pubEval vals)`, `vals = P.hdrLanes`),
then `QLT`, the `BITS` outputs and the aux tables (`tabsP20_split`). Every group is kept by
`sumcheckTabs` (decided on the shapes, `groups_kept`), every input array too (it seeds), so `PUB` is
sumcheck table `(number of groups) + 43 = P20.pubTab` (127 at the final record) (`sumcheckTabs_split`). Then:

* **`fixStatic_P20 : FixStatic P20 M3.tabsP20`** (`fixColsR` drops exactly `PUB`'s column 0);
* **`pubEv_P20`**: `PUB`'s column 0 at table `pubTab` has closed form `pubEval P.hdrLanes`.
-/

set_option autoImplicit false

namespace Lvm.QAsm

open Lvm Lvm.M3

/-! ## Generic: `fixCols` around one table -/

/-- `fixColsR` with the table at `pubTab` changed in its column 0 only. -/
theorem fixColsR_swap (S₁ S₂ : List Tab) (t t' : Tab) (hτ : t.τ = t'.τ) (ht : t.cols.tail = t'.cols.tail)
    (h0 : ∃ f e, t.cols.head? = some (.fix f e)) (h0' : ∃ f e, t'.cols.head? = some (.fix f e)) :
    fixColsR (S₁ ++ t :: S₂) S₁.length = fixColsR (S₁ ++ t' :: S₂) S₁.length := by
  unfold fixColsR
  rw [List.zipIdx_append, List.zipIdx_append, List.flatMap_append, List.flatMap_append, List.zipIdx_cons,
    List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons]
  congr 2
  obtain ⟨f, e, hf⟩ := h0
  obtain ⟨f', e', hf'⟩ := h0'
  rcases hc : t.cols with _ | ⟨c, cs⟩
  · rw [hc] at hf; simp at hf
  rcases hc' : t'.cols with _ | ⟨c', cs'⟩
  · rw [hc'] at hf'; simp at hf'
  rw [hc] at hf ht; rw [hc'] at hf' ht
  simp only [List.head?_cons, Option.some.injEq] at hf hf'
  simp only [List.tail_cons] at ht
  subst hf hf' ht
  dsimp only
  rw [hc, hc', List.zipIdx_cons, List.zipIdx_cons, List.filterMap_cons, List.filterMap_cons]
  simp only [Nat.zero_add, beq_self_eq_true, Bool.and_self, ↓reduceIte, hτ]

/-! ## The P20 tables -/

/-- The input arrays before `PUB`. -/
def arrsPre (C : QCfg) (D : QData) : List InArr :=
  let R := 2 ^ C.rl
  (List.range 17).map (fun l => ⟨.K, C.rl, l, 17, [(true, l * R)], fin D l, none⟩) ++
  [⟨.K, 10, sgB C, 1, [(true, 17 * R)], fin D 17, none⟩] ++
  (List.range 17).map (fun l => ⟨.K, 9, xsB C + l, 17, [(false, xOff C + l * R)], fin D (18 + l), none⟩) ++
  (List.range 4).map (fun l => ⟨.K, 9, ysB C + l, 4, [(false, ksY C l + R)], fin D (35 + l), none⟩) ++
  (List.range 4).map (fun l =>
    ⟨.K, 0, mdB C + l, 4, [(false, ksY C l + (spongeBlocks C.p - 1))], fin D (39 + l), none⟩)

/-- The input arrays after `PUB`. -/
def arrsPost (C : QCfg) (D : QData) : List InArr :=
  [pubArr C.aQT (qtB C) 1 (false, 0) (fin D 44) (Lvm.QLink.qltData C.p (lay C)),
   ⟨.K, C.bo, obB C, 1, [(false, D.aval)], fin D 45, none⟩]

/-- `PUB`'s input array. -/
def pubA (C : QCfg) (D : QData) (P : Pub) : InArr := pubArr 10 (pbB C) 1 (false, 0) (fin D 43) (hdrOfPub P)

theorem arrs_split (C : QCfg) (D : QData) (P : Pub) :
    arrs C D P = arrsPre C D ++ pubA C D P :: arrsPost C D := rfl

/-- The groups' tables. -/
def grpTabs (G : PG) (D : QData) : List Tab :=
  (List.range D.groups.length).map fun i ↦
    shapeTab (D.groups.getD i default).σ (D.groups.getD i default).τ (grpFix G.C.Q (D.groups.getD i default))
      (grpEvalG G (D.groups.getD i default)) (plOf D i)

theorem tabs_split (C : QCfg) (G : PG) (D : QData) (P : Pub) :
    tabs C G D P = (grpTabs G D ++ (arrsPre C D).map InArr.tab) ++
      (pubA C D P).tab :: ((arrsPost C D).map InArr.tab ++ aux C D) := by
  simp only [tabs, lvmTabsC, grpTabs, arrs_split, List.map_append, List.map_cons, List.append_assoc,
    List.cons_append]

/-- An input array's table seeds, so `sumcheckTabs` keeps it. -/
theorem sumcheckTabs_inArr (l : List InArr) : sumcheckTabs (l.map InArr.tab) = l.map InArr.tab := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp ht
  simp [InArr.tab]

/-- Every group's shape has a constraint, a read or a write (decided on the shapes). -/
theorem groups_kept20 :
    (data20.groups.all fun g ↦ !g.σ.constraints.isEmpty || !g.σ.readFlushes.isEmpty || g.σ.writes) = true := by
  decide +kernel

theorem sumcheckTabs_grp (G : PG) (D : QData)
    (hk : (D.groups.all fun g ↦ !g.σ.constraints.isEmpty || !g.σ.readFlushes.isEmpty || g.σ.writes) = true) :
    sumcheckTabs (grpTabs G D) = grpTabs G D := by
  unfold sumcheckTabs
  rw [List.filter_eq_self]
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  have hi' := List.mem_range.mp hi
  have hg := List.all_eq_true.mp hk _ (List.getElem_mem hi')
  rw [← List.getD_eq_getElem _ default hi'] at hg
  unfold shapeTab
  simp only [List.isEmpty_map]
  revert hg
  cases (D.groups.getD i default).σ.writes <;> simp

theorem sumcheckTabs_append (a b : List Tab) : sumcheckTabs (a ++ b) = sumcheckTabs a ++ sumcheckTabs b :=
  List.filter_append _ _

/-- **`PUB` is sumcheck table `|groups| + 43`** of the P20 tables. -/
theorem sumcheckTabs_split (P : Pub) :
    sumcheckTabs (M3.tabsP20 P) = (grpTabs M3.G20 data20 ++ (arrsPre cfg20 data20).map InArr.tab) ++
      (pubA cfg20 data20 P).tab :: sumcheckTabs ((arrsPost cfg20 data20).map InArr.tab ++ aux cfg20 data20) := by
  rw [M3.tabsP20, tabs_split, sumcheckTabs_append, sumcheckTabs_append, sumcheckTabs_grp _ _ groups_kept20,
    sumcheckTabs_inArr]
  congr 1

theorem length_pre20 : (grpTabs M3.G20 data20 ++ (arrsPre cfg20 data20).map InArr.tab).length = P20.pubTab := by
  simp only [List.length_append, List.length_map, grpTabs, List.length_range, arrsPre]
  decide +kernel

/-- `PUB`'s table: τ 10, its value column, then the finalize count and the address. -/
theorem pubA_tab_cols (P : Pub) :
    (pubA cfg20 data20 P).tab.cols = .fix (pubCell (hdrOfPub P)) (pubEval (hdrOfPub P)) ::
      (pubA cfg20 data20 (default : Pub)).tab.cols.tail := by
  rfl

/-- `fixColsR` of the P20 tables does not depend on the header. -/
theorem fixColsR_P20 (pub pub' : Pub) :
    fixColsR (sumcheckTabs (M3.tabsP20 pub)) P20.pubTab = fixColsR (sumcheckTabs (M3.tabsP20 pub')) P20.pubTab := by
  rw [sumcheckTabs_split, sumcheckTabs_split, ← length_pre20,
    fixColsR_swap _ _ (pubA cfg20 data20 pub).tab (pubA cfg20 data20 pub').tab rfl
      (by rw [pubA_tab_cols, pubA_tab_cols pub']; rfl)
      ⟨_, _, by rw [pubA_tab_cols]; rfl⟩ ⟨_, _, by rw [pubA_tab_cols]; rfl⟩]

/-- **`Φ` is one polynomial for the P20 tables** (A23: only `PUB`'s value column reads the header):
the same `fixCols` (tables, heights, columns, closed forms) for every header. -/
theorem fixStatic_P20 : FixStatic P20 M3.tabsP20 := fun pub pub' ↦
  ⟨by rw [fixColsR_P20 pub pub'], by unfold fixValsR; rw [fixColsR_P20 pub pub']⟩

/-- **`PUB`'s value column has the header lanes' closed form** (AC-S's `AccInst.pubEv` at P20). -/
theorem pubEv_P20 (P : Pub) : ∀ t f e, (sumcheckTabs (M3.tabsP20 P))[P20.pubTab]? = some t →
    t.cols[0]? = some (.fix f e) → ∀ r : List FE, e r = pubEval P.hdrLanes r := by
  intro t f e ht hc r
  rw [sumcheckTabs_split, ← length_pre20, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero, Option.some.injEq] at ht
  subst ht
  rw [pubA_tab_cols, List.getElem?_cons_zero, Option.some.injEq, ColSrc.fix.injEq] at hc
  rw [← hc.2]
  rfl

end Lvm.QAsm
