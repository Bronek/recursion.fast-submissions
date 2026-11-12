-- new for lvm (AC-S, BLUEPRINT §12.6 `accSpec`): phase 3b of the lvm instance from the table seam
-- (WP-2's `TablePost`, with `AccOk acc_in` carried in the candidates) to WP-9b's `TablePostC`; then
-- with the bus and table phases (WP-9b's `lbusTableSpec`), as WP-9b's `lbusTableCheckSpec` composes
-- them with `tableCheckSpec` (`LvmM3Mid`). The good-branch lemma follows WP-9b's `derived_holds`.
import LvmAccSpecL
import LvmM3Mid

/-!
# `accSpec`: phase 3b replaces the fixed-column check

* `AccInst P T pub`: the facts of the tables and the header the phase needs (`FixOk`, heights,
  `nFix ≤ 2^accLog`, `tableRounds + accLog = accVars`, `|acc_in.pt| = accVars`, `PUB`'s closed form);
* **`holds_of_good`**: if the phase's checks can all pass (`pubOkV` and every `δ_k = 0`), every
  derived (fixed) column's claim of the table seam holds of every stack;
* `candsA cands A`: the candidates, when `A` (here `AccOk acc_in`, a property of the statement);
* **`accSpecT`**: `Spec (accProgV …) (TablePost (candsA cands AccOk) ∧ ClaimShape) TablePostC`,
  escape `1/|E|` per `κ_j`, `D/|E|` at `t`, lead `max (accLog/|E|) T` (BLUEPRINT §12.6);
* **`lbusTableAccProg`/`lbusTableAccSpec`**: V_S phases 2–3b (bus, table sumcheck, phase 3b, the
  claims returned), from the commitment's doom of the `AccOk`-candidates to `TablePostC`.
-/

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakGkr CompPoly CMlPolynomialEval
open Lvm.M3 (Tab ColSrc FixCol fixColsR sumcheckTabs vTables vLayout busResV Lay inst colOfL FixOk
  pubEval TablePostC lvmBusTableProg)
open scoped ENNReal

/-- **What phase 3b needs of the tables `T` (the sumcheck tables of `tabs pub`) and the header.**
All but `pubEv` follow from `fitsR` and `MidHyp`; `pubEv` is the real `PUB` array's closed form. -/
structure AccInst (P : Params) (T : List Tab) (pub : Pub) : Prop where
  fix : FixOk T
  rounds : (T.map (·.τ)).foldl max 0 = P.tableRounds
  τle : ∀ t ∈ T, t.τ ≤ P.tableRounds
  full : ∃ t ∈ T, t.τ = P.tableRounds ∧ 0 < t.w
  nfix : (fixColsR T P.pubTab).length ≤ 2 ^ P.accLog
  vars : P.tableRounds + P.accLog = accVars
  acc : pub.accIn.pt.length = accVars
  pubEv : ∀ t f e, T[P.pubTab]? = some t → t.cols[0]? = some (.fix f e) →
    ∀ r : List FE, r.length = t.τ → e r = pubEval pub.hdrLanes r

/-- The sent evaluations of `fixCols` as the phase reads them. -/
def vsOf (T : List Tab) (pubTab : ℕ) (cl : List Verifier.ColumnClaim) : List E :=
  (fixColsR T pubTab).map fun c ↦ (claimAt cl (gcol T c)).value

/-! ## The good branch: every fixed claim holds -/

theorem colOfL_eq (L : Lay) (T : List Tab) (hτL : ∀ t ∈ T, t.τ ≤ L.μ) (c : (inst L T hτL).ColumnId) :
    colOfL L T hτL c = (Verifier.globalColumnBases (vTables T)).getD c.1.val 0 + c.2.val := rfl

/-- **If phase 3b's checks can all pass, every fixed column's claim of the table seam holds.** -/
theorem holds_of_good {L : Lay} {T : List Tab} {hτL : ∀ t ∈ T, t.τ ≤ L.μ} {P : Params} {pub : Pub}
    {cl : List Verifier.ColumnClaim} (H : AccInst P T pub) (hsh : ClaimShape T cl)
    (hok : pubOkV T P.pubTab pub cl = true)
    (hδ : ∀ w < 2 ^ P.accLog, deltaOf (fixColsR T P.pubTab) (vsOf T P.pubTab cl) (tablePointV cl) w = 0)
    (c : LeanVM.Protocol.ColumnClaim (inst L T hτL)) (hd : (inst L T hτL).derived c.col ≠ none)
    (hc : (⟨colOfL L T hτL c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈ cl)
    (q : Column (inst L T hτL).μ) : c.Holds q := by
  obtain ⟨⟨⟨j, hj⟩, ⟨i, hi⟩⟩, pt, v⟩ := c
  have hj' : j < T.length := hj
  have htj : T.get ⟨j, hj⟩ = T[j] := rfl
  have hfo : T[j].fixedOf i ≠ none := by
    intro h; apply hd
    show Option.map _ ((T.get ⟨j, hj⟩).fixedOf i) = none
    rw [htj, h]; rfl
  obtain ⟨f, ev, hcol⟩ : ∃ f ev, T[j].cols[i]? = some (.fix f ev) := by
    unfold Tab.fixedOf at hfo
    split at hfo
    · exact ⟨_, _, by assumption⟩
    · exact absurd rfl hfo
  have hcolq : (inst L T hτL).column q ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ = Lvm.M3.fixedColumn T[j].τ f := by
    simp [M3Instance.column, inst, Tab.fixedOf, htj, hcol]
  -- the claim the phase reads is the seam's
  set n := colOfL L T hτL ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ with hn
  have hca : claimAt cl n = ⟨n, pt.toList, v⟩ := claimAt_eq hsh.1 hc
  obtain ⟨ptS, hptS, hof, hfull⟩ := hsh.2
  -- its point is the sumcheck point's prefix, and the phase's table point is the sumcheck point
  obtain ⟨j', i', hj'', hi', hcn, hpt⟩ := hof _ hc
  have hji : j = j' ∧ i = i' := by
    have h1 := Lvm.M3.colLoc_colOfL L T hτL ⟨⟨j, hj⟩, ⟨i, hi⟩⟩
    have h2 := Lvm.M3.colLoc_colOfL L T hτL ⟨⟨j', hj''⟩, ⟨i', hi'⟩⟩
    rw [colOfL_eq, base_bnd T hj''] at h2
    simp only at hcn
    rw [← hcn] at h2
    rw [h1] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    exact ⟨h2.1, h2.2⟩
  obtain ⟨hj1, hi1⟩ := hji
  subst hj1
  subst hi1
  simp only at hpt
  have hr : tablePointV cl = ptS := tablePointV_eq (fun d hd ↦ by
      obtain ⟨_, _, hk, -, -, hp⟩ := hof d hd; exact ⟨_, hp⟩)
    (hfull (by obtain ⟨t, ht, h1, h2⟩ := H.full; exact ⟨t, ht, by rw [h1, H.rounds], h2⟩))
  have hlen : pt.toList.length = T[j].τ := by simp; rfl
  -- the value is the closed form at the point
  have hv : v = FE.toExt3 (ev (pt.toList.map FE.ofExt3)) := by
    by_cases hp : j = P.pubTab ∧ i = 0
    · obtain ⟨hp1, hp2⟩ := hp
      have hn0 : (Verifier.globalColumnBases (vTables T)).getD P.pubTab 0 + 0 = n := by
        rw [hn, colOfL_eq]; simp only [hp1, hp2]
      unfold pubOkV at hok
      simp only [decide_eq_true_eq] at hok
      rw [hn0, hca] at hok
      simp only at hok
      rw [hok, H.pubEv T[j] f ev (by rw [← hp1]; exact List.getElem?_eq_getElem hj')
        (by rw [← hp2]; exact hcol) _ (by simpa using hlen)]
    · obtain ⟨k, hk, hk'⟩ := List.mem_iff_getElem.mp
        (mem_fixColsR_of (List.getElem?_eq_getElem hj') hcol hp)
      have h0 := hδ k (lt_of_lt_of_le hk H.nfix)
      rw [deltaOf, dif_pos hk, sub_eq_zero, hk'] at h0
      rw [vsOf, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, hk',
        show gcol T ⟨j, T[j].τ, i, ev⟩ = n from rfl, hca, hr, ← List.map_take, ← hpt] at h0
      exact h0
  have hmem : ColSrc.fix f ev ∈ T[j].cols := List.mem_of_getElem? hcol
  have hfx := H.fix _ (List.getElem_mem hj') f ev hmem (pt.toList.map FE.ofExt3) (by simpa using hlen)
  show eval₂Mle ((inst L T hτL).column q ⟨⟨j, hj⟩, ⟨i, hi⟩⟩).values (algebraMap K E) pt = v
  rw [hcolq, hv, hfx, Lvm.M3.toExt3_mle_fixed]
  rfl

/-! ## The phase's specification on the table seam -/

/-- The candidates, when `A` holds (`A` a property of the statement: `AccOk acc_in`). -/
def candsA {α : Type} (cands : Word → Set α) (A : Prop) : Word → Set α := fun W ↦ {o | o ∈ cands W ∧ A}

theorem candsA_finite {α : Type} {cands : Word → Set α} (hf : ∀ W, (cands W).Finite) (A : Prop) :
    ∀ W, (candsA cands A W).Finite := fun W ↦ (hf W).subset fun _ h ↦ h.1

theorem candsA_ncard {α : Type} {cands : Word → Set α} {L₀ : ℕ} (hf : ∀ W, (cands W).Finite)
    (hc : ∀ W, (cands W).ncard ≤ L₀) (A : Prop) : ∀ W, (candsA cands A W).ncard ≤ L₀ :=
  fun W ↦ (Set.ncard_le_ncard (fun _ h ↦ h.1) (hf W)).trans (hc W)

/-- **`AccOk acc_in` over `E`** (`accOk_iff`: the native one). -/
def AccOkE (P : Params) (tabs : Pub → List Tab) (pub : Pub) : Prop :=
  PhiV P tabs pub (pub.accIn.pt.map FE.toExt3) = FE.toExt3 pub.accIn.y

section Inst

variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ)

/-- The phase's table point has `tableRounds` coordinates. -/
theorem length_tablePointV {T : List Tab} {cl : List Verifier.ColumnClaim} (H : AccInst P T pub)
    (hs : ClaimShape T cl) : (tablePointV cl).length = P.tableRounds := by
  obtain ⟨ptS, hptS, hof, hfull⟩ := hs.2
  rw [tablePointV_eq (fun d hd ↦ by obtain ⟨_, _, hk, -, -, hp⟩ := hof d hd; exact ⟨_, hp⟩)
    (hfull (by obtain ⟨t, ht, h1, h2⟩ := H.full; exact ⟨t, ht, by rw [h1, H.rounds], h2⟩)),
    hptS, H.rounds]

/-- **The instance's `AccHyp`** (`accHyp_phi` at the claims' values and table point). -/
theorem accHypV {cl : List Verifier.ColumnClaim} (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hs : ClaimShape (sumcheckTabs (tabs pub)) cl) :
    AccHyp P.accLog accVars (pub.accIn.pt.map FE.toExt3) (yOwnV (sumcheckTabs (tabs pub)) P.pubTab cl)
      (fun κ ↦ tablePointV cl ++ κ) (PhiV P tabs pub)
      (deltaOf (fixColsR (sumcheckTabs (tabs pub)) P.pubTab) (vsOf (sumcheckTabs (tabs pub)) P.pubTab cl)
        (tablePointV cl)) := by
  have h := accHyp_phi (fixColsR (sumcheckTabs (tabs pub)) P.pubTab) (cellOf (sumcheckTabs (tabs pub)))
    P.tableRounds P.accLog (fixCols_τ _ _ H.τle) (fixCols_ev _ H.fix) H.nfix
    (pub.accIn.pt.map FE.toExt3) (tablePointV cl) (vsOf (sumcheckTabs (tabs pub)) P.pubTab cl)
    (by rw [List.length_map, H.acc, H.vars]) (length_tablePointV P pub H hs) (by simp [vsOf])
  rw [H.vars] at h
  exact h

/-- **`accSpec`** (BLUEPRINT §12.6, replaces WP-9b's `tableCheckSpec`): phase 3b of the lvm
instance, from the table seam of the candidates meeting `AccOk acc_in` (with the claims' shape,
a return fact of the table phase) to the doom of the committed claims of all candidates
(`TablePostC`). Escape `1/|E|` per `κ_j`, `accVars/|E|` at `t`. -/
noncomputable def accSpecT (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (cands : Word → Set (∀ i, TheOracle (inst L (sumcheckTabs (tabs pub)) hτL) i))
    (cl : List Verifier.ColumnClaim) {εmax Tf : ℝ≥0∞} (hD : errE accVars ≤ εmax) (hTf : Tf ≤ εmax) :
    Spec (accProgV P tabs pub cl)
      (fun h ↦ TablePost (inst L (sumcheckTabs (tabs pub)) hτL) (candsA cands (AccOkE P tabs pub)) ()
          (colOfL L (sumcheckTabs (tabs pub)) hτL) cl h ∧ ClaimShape (sumcheckTabs (tabs pub)) cl)
      (fun _ h ↦ TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) cands ()
        (colOfL L (sumcheckTabs (tabs pub)) hτL) cl h)
      εmax (max (P.accLog * errE 1) Tf) Tf := by
  classical
  exact if hs : ClaimShape (sumcheckTabs (tabs pub)) cl then
    (accSpecG (accHypV P tabs pub H hs)
        (TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) cands () (colOfL L (sumcheckTabs (tabs pub)) hτL) cl)
        (fun _ l _ ⟨W, tout, hW, rest⟩ ↦ ⟨W, tout, firstWord_append hW l, rest⟩) hD hTf).mono
      (fun h ⟨hp, _⟩ ↦ by
        by_cases hg : AccGood P.accLog (pubOkV (sumcheckTabs (tabs pub)) P.pubTab pub cl)
            (FE.toExt3 pub.accIn.y) (pub.accIn.pt.map FE.toExt3) (PhiV P tabs pub)
            (deltaOf (fixColsR (sumcheckTabs (tabs pub)) P.pubTab)
              (vsOf (sumcheckTabs (tabs pub)) P.pubTab cl) (tablePointV cl))
        · refine .inr ?_
          obtain ⟨W, tout, hW, hDm, h1, hcl, hout⟩ := hp
          refine ⟨W, tout, hW, fun o ho ⟨hc, hpub, haux⟩ ↦ hDm o ⟨ho, hg.2.1⟩
            ⟨fun c hcm ↦ ?_, hpub, haux⟩, h1, hcl, hout⟩
          by_cases hd : (inst L (sumcheckTabs (tabs pub)) hτL).derived c.col = none
          · exact hc c hcm hd
          · exact holds_of_good H hs hg.1 hg.2.2 c hd (hcl c hcm) _
        · exact .inl hg)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hp ↦ hs hp.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Inst

/-! ## V_S phases 2–3b -/

/-- **V_S phases 2–3b** on the program objects (BLUEPRINT §12.4): the bus phase, the table sumcheck,
phase 3b (in place of WP-9b's `require (tableCheckVB)`), the claims. -/
def lbusTableAccProg (P : Params) (tabs : Pub → List Tab) (pub : Pub) (μ : ℕ) :
    VerifierProgram (List Verifier.ColumnClaim) :=
  (lvmBusTableProg (vTables (sumcheckTabs (tabs pub))) (vLayout (sumcheckTabs (tabs pub))) μ
      (busResV (sumcheckTabs (tabs pub)))).bind fun cl ↦
    (accProgV P tabs pub cl).bind fun _ ↦ VerifierProgram.ret cl

section Phase

variable (L : Lay) (P : Params) (tabs : Pub → List Tab) (pub : Pub)
  (hτL : ∀ t ∈ sumcheckTabs (tabs pub), t.τ ≤ L.μ) (hsc : Lvm.M3.AllSc (sumcheckTabs (tabs pub)))
  (cands : Word → Set (∀ i, TheOracle (inst L (sumcheckTabs (tabs pub)) hτL) i)) {εmax : ℝ≥0∞}

/-- **V_S phases 2–3b of the lvm instance** (WP-9b's `lbusTableCheckSpec` with `accSpec` in place of
`tableCheckSpec`): from the commitment's doom of the candidates meeting `AccOk acc_in` to the
committed claims' doom of all candidates (`TablePostC`). `Ta` is phase 3b's lead
`max (accLog/|E|) T`; `T` is the follower's. -/
noncomputable def lbusTableAccSpec (H : AccInst P (sumcheckTabs (tabs pub)) pub)
    (hkey : Lvm.M3.KeysOk (sumcheckTabs (tabs pub))) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : (inst L (sumcheckTabs (tabs pub)) hτL).μBus ≠ 0)
    (hab : abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ < 1)
    (he4 : roundError L₀ 4 ≤ εmax) (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax)
    (hlam : lambdaError L₀ + 0 ≤ εmax) {T : ℝ≥0∞} (he3 : roundError L₀ 3 + max (P.accLog * errE 1) T ≤ εmax)
    (hTa : max (P.accLog * errE 1) T ≤ εmax)
    (hxi : xiError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ +
      sumcheckLead (List.replicate ((vLayout (sumcheckTabs (tabs pub))).tableLogHeights.foldl max 0) none)
        (max (P.accLog * errE 1) T) ≤ εmax)
    (hD : errE accVars ≤ εmax) (hTf : T ≤ εmax) :
    Spec (lbusTableAccProg P tabs pub (inst L (sumcheckTabs (tabs pub)) hτL).μBus)
      (HDoom (candsA cands (AccOkE P tabs pub)) (Seam.commit (inst L (sumcheckTabs (tabs pub)) hτL)) ())
      (TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) cands () (colOfL L (sumcheckTabs (tabs pub)) hτL))
      εmax (abError (inst L (sumcheckTabs (tabs pub)) hτL) L₀ + 0) T :=
  (Lvm.KG.specWithRet (Lvm.M3.lbusTableSpec L (sumcheckTabs (tabs pub)) hτL hsc
      (candsA cands (AccOkE P tabs pub)) hkey hw (candsA_finite hfin _) (candsA_ncard hfin hcard _) hμ hab
      he4 hT hlam he3 hTa hxi) (retOK_lvmBusTableProg (sumcheckTabs (tabs pub)) _)).bind fun cl ↦
    ((accSpecT L P tabs pub hτL H cands cl hD hTf).mono (fun _ ⟨hs, hp⟩ ↦ ⟨hp, hs⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind fun _ ↦
      Spec.ret (Post := TablePostC (inst L (sumcheckTabs (tabs pub)) hτL) cands ()
        (colOfL L (sumcheckTabs (tabs pub)) hτL)) cl

end Phase

end Lvm.Acc
