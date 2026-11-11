-- new for lvm (AC-S, BLUEPRINT §12.6 node level): WP-16b's O6 (`LvmCertSMid3`, lvm/CERT) for the
-- middle phases with A23's phase 3b. The pieces are WP-16b's (`midSpecOfR`, `bus_errs`, `specKgS`,
-- `link_assembleS`, `side_midS`, `retOK_lbusTableCheckProg`'s proof), with `midBusTableAccSpecS` in
-- place of `midBusTableSpecS` and `Good := GoodS ∧ AccOk acc_in`.
import LvmAccSpecMid
import LvmCertSMid3

/-!
# O6 with phase 3b: `Good := GoodN ∧ AccOk`

* `midSA tabs x`: the middle phases with phase 3b (`lbusTableAccProg`, then WP-8's `kgProgS`, then
  WP-14a's `assembleS`), i.e. AC-N's `midS` once its phases 2–3b are `lbusTableAccProg`;
* **`AccOkN tabs x`**: the statement's incoming claim holds (native `AccOk … (pubX x).accIn`);
  **`GoodA`** = WP-16b's `GoodS` with `AccOkN` (`goodA_iff`); **`nodeSound_goodA`**: `NodeSound` for
  `GoodA` from `NodeSound` for `GoodN ∧ AccOkN` (AC-N's form: `harith` gives `decideCore` and
  `accOutOf = accIn x`, `AccOkN` gives `decideF`);
* `AccMidHyp tabs`: phase 3b's facts (`AccInst`) at every statement;
* `acc_errs`: phase 3b's lead `max (11/|E|) LkS = LkS` and `28/|E| ≤ εS` (`εS`, `εFS` unchanged);
* **`midSpec_midSA`**: `MidSpec (midSA tabs) (GoodA …) εS εS`; **`midShape_midSA`**.
-/

set_option autoImplicit false

namespace Lvm.Acc

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.ASM Lvm.VEq Lvm.KG
open Lvm.M3 (Tab sumcheckTabs vTables vLayout busResV inst lay26 fitsR KeysOk FixOk AllSc)
open Lvm.NS (GoodB GoodN)
open scoped ENNReal NNReal

/-! ## The returns of phases 2–3b -/

/-- WP-16b's `TabRet` of WP-9b's bus and table phases (its proof for `lbusTableCheckProg`). -/
theorem retOK_lvmBusTableProg_tabRet (T : List Tab) (μ : ℕ) :
    RetOK (TabRet T) (Lvm.M3.lvmBusTableProg (vTables T) (vLayout T) μ (busResV T)) := by
  unfold Lvm.M3.lvmBusTableProg
  refine RetOK.bind_true fun b ↦ ?_
  unfold tablePhaseClaims
  refine RetOK.bind_true fun xi ↦ ?_
  refine (retOK_tableSumcheckClaims _ _ _ _ _ _ _ (fun c ↦ ∀ j i,
    Lvm.M3.colLoc T c.column = some (j, i) → c.point.length = (T[j]?.map (·.τ)).getD 0) ?_).bind
    fun cl hcl ↦ RetOK.ret ?_
  · intro point hpt r hr col hcol v j i hloc
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
    have hkT : k < T.length := by
      simp only [List.length_zip, Lvm.M3.length_vTables] at hk; omega
    simp only [List.getElem_zip, getElem_vTables T k (by simpa using hkT)] at hcol hloc ⊢
    simp only [Lvm.M3.vLayout, List.getElem_map, Lvm.M3.vTable, Verifier.Table.width,
      List.length_replicate] at hcol hloc hpt ⊢
    rw [colLoc_base T hkT hcol] at hloc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hloc)
    have := foldl_max_ge (T.map (·.τ)) 0 T[k].τ
      (Or.inr (List.mem_map_of_mem (List.getElem_mem hkT)))
    simp [List.getElem?_eq_getElem hkT]
    omega
  · simp only [Lvm.M3.busResV, Lvm.M3.busFinalV, List.nil_append]
    exact ⟨hcl.1, (sum_width_vTables T) ▸ hcl.2⟩

/-- **Every return of phases 2–3b meets `TabRet`** (phase 3b returns the claims unchanged). -/
theorem retOK_lbusTableAccProg (P : Params) (tabs : Pub → List Tab) (pub : Pub) (μ : ℕ) :
    RetOK (TabRet (sumcheckTabs (tabs pub))) (lbusTableAccProg P tabs pub μ) := by
  unfold lbusTableAccProg
  exact (retOK_lvmBusTableProg_tabRet _ μ).bind fun cl hcl ↦ RetOK.bind_true fun _ ↦ RetOK.ret hcl

/-! ## `Good := GoodN ∧ AccOk` -/

/-- **The statement's incoming claim holds** (`AccOk` of the header's `acc_in`, native). -/
def AccOkN (tabs : Pub → List Tab) (x : List UInt8) : Prop :=
  AccOk Lvm.P20 (M3.real Lvm.P20 tabs) (pubX x) (pubX x).accIn = true

/-- The bus half of the good pair with phase 3b: WP-16b's, and the incoming claim. -/
def GbA (tabs : Pub → List Tab) (hτ : ∀ x, ∀ t ∈ TS tabs x, t.τ ≤ lay26.μ) (x : List UInt8)
    (p : Pair) : Prop :=
  (GoodB (TS tabs) hτ x p ∧ BndS x p.1) ∧ AccOkN tabs x

/-- **The good pair with phase 3b** (BLUEPRINT §12.6: `Good := GoodN ∧ AccOk (accIn x)`). -/
def GoodA (tabs : Pub → List Tab) (hτ : ∀ x, ∀ t ∈ TS tabs x, t.τ ≤ lay26.μ) : GoodRel :=
  fun x qm qr ↦ GbA tabs hτ x (qm, qr) ∧ GkS (qm, qr)

theorem goodA_iff (tabs : Pub → List Tab) (hτ : ∀ x, ∀ t ∈ TS tabs x, t.τ ≤ lay26.μ)
    (x : List UInt8) (qm : Column 26) (qr : Column 19) :
    GoodA tabs hτ x qm qr ↔ GoodS (TS tabs) hτ x qm qr ∧ AccOkN tabs x :=
  ⟨fun ⟨⟨hb, ha⟩, hk⟩ ↦ ⟨⟨hb, hk⟩, ha⟩, fun ⟨⟨hb, hk⟩, ha⟩ ↦ ⟨⟨hb, ha⟩, hk⟩⟩

/-- **`NodeSound` for `GoodA`** from `NodeSound` for `GoodN ∧ AccOk` (as WP-16b's
`nodeSound_goodS`: `okS` bounds `n` by `2^20`). -/
theorem nodeSound_goodA {VS : Lvm.T.SProg} {vk : RecursionFast.Digest} {tabs : Pub → List Tab}
    {hτ : ∀ x, ∀ t ∈ TS tabs x, t.τ ≤ lay26.μ} {child : Column 19 → RecursionFast.Signed}
    (h : NodeSound VS vk (fun x qm qr ↦ GoodN (TS tabs) hτ x qm qr ∧ AccOkN tabs x) child) :
    NodeSound VS vk (GoodA tabs hτ) child :=
  fun c x qm qr hok hG ↦ h c x qm qr hok
    ⟨⟨hG.1.1.1, hG.2.1, hG.2.2, hG.1.1.2 (Lvm.NS.okS_n hok).2⟩, hG.1.2⟩

/-! ## Phase 3b's facts and errors -/

/-- **Phase 3b's facts at every statement** (`AccInst` of the statement's sumcheck tables). -/
def AccMidHyp (tabs : Pub → List Tab) : Prop := ∀ x, AccInst Lvm.P20 (TS tabs x) (pubX x)

theorem accLog_P20 : Lvm.P20.accLog = 11 := by decide

/-- The running maximum of a list from `0` is `0` or one of its elements. -/
theorem foldl_max_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => .inl rfl
  | b :: l, a => by
    rw [List.foldl_cons]
    rcases foldl_max_mem l (max a b) with h | h
    · rw [h]; rcases max_choice a b with h' | h'
      · exact .inl h'
      · exact .inr (by rw [h']; exact List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h)

/-- **`AccInst` from WP-14a's `Fit`** (A23's `fitsR` conjuncts), positive widths and `FixOk` (WP-16b's
`MidHyp`), the header's `acc_in` length and `PUB`'s closed form (the assembly's). -/
theorem accInst_of_fit {P : Params} {tabs : Pub → List Tab} {pub : Pub}
    (F : Lvm.VEq.Fit P (tabs pub)) (hw : ∀ t ∈ sumcheckTabs (tabs pub), 0 < t.w)
    (hfix : FixOk (sumcheckTabs (tabs pub))) (hacc : pub.accIn.pt.length = accVars)
    (hpub : ∀ t f e, (sumcheckTabs (tabs pub))[P.pubTab]? = some t → t.cols[0]? = some (.fix f e) →
      ∀ r : List FE, r.length = t.τ → e r = Lvm.M3.pubEval pub.hdrLanes r) :
    AccInst P (sumcheckTabs (tabs pub)) pub where
  fix := hfix
  rounds := F.rounds.symm
  τle t ht := F.rounds ▸ foldl_max_ge _ 0 t.τ (.inr (List.mem_map_of_mem ht))
  full := by
    have hne : sumcheckTabs (tabs pub) ≠ [] := List.ne_nil_of_length_pos (by have := F.pubTab; omega)
    obtain ⟨t₀, ht₀⟩ := List.exists_mem_of_ne_nil _ hne
    have hm : ((sumcheckTabs (tabs pub)).map (·.τ)).foldl max 0 ∈
        (sumcheckTabs (tabs pub)).map (·.τ) := by
      rcases foldl_max_mem ((sumcheckTabs (tabs pub)).map (·.τ)) 0 with h | h
      · have hle := foldl_max_ge _ 0 t₀.τ (.inr (List.mem_map_of_mem ht₀))
        rw [h] at hle ⊢
        exact (show t₀.τ = 0 by omega) ▸ List.mem_map_of_mem ht₀
      · exact h
    obtain ⟨t, ht, hτ⟩ := List.mem_map.mp hm
    exact ⟨t, ht, by rw [hτ, F.rounds], hw t ht⟩
  nfix := F.nFix
  vars := by have := F.accRounds; unfold Params.accLog; omega
  acc := hacc
  pubEv := hpub

/-- The header's `acc_in` has `accVars` coordinates (`pubOf` reads them). -/
theorem length_accIn_pt (x : List UInt8) : (pubX x).accIn.pt.length = accVars := by
  simp [pubX, pubOf]

/-- **`AccMidHyp` from WP-16b's `MidHyp`** and `PUB`'s closed form (the one fact owed). -/
theorem accMidHyp_of {tabs : Pub → List Tab} (H : MidHyp tabs)
    (hpub : ∀ x t f e, (TS tabs x)[Lvm.P20.pubTab]? = some t → t.cols[0]? = some (.fix f e) →
      ∀ r : List FE, r.length = t.τ → e r = Lvm.M3.pubEval (pubX x).hdrLanes r) :
    AccMidHyp tabs := fun x ↦
  accInst_of_fit (fit_of Lvm.P20 _ (H.fit (pubX x))) (H.width x) (H.fix x) (length_accIn_pt x) (hpub x)

/-- **Phase 3b's errors at `εS`**: its lead `11/|E|` is below the follower's `LkS = 20/|E|`, so the
table phase's follower lead is unchanged, and `t`'s `28/|E|` is below `εS`. -/
theorem acc_errs : max (Lvm.P20.accLog * errE 1) LkS = LkS ∧ errE accVars ≤ εS := by
  refine ⟨max_eq_right ?_, errE_le_εS (by decide)⟩
  rw [accLog_P20, LkS_eq, show ((11 : ℕ) : ℝ≥0∞) * errE 1 = errE (11 * 1) from errE_smul 11 1]
  exact errE_mono (by norm_num)

/-! ## The middle phases with phase 3b -/

/-- **The middle phases with phase 3b**: phases 2–3b, V_S phases 4–7, the claims. -/
def midSA (tabs : Pub → List Tab) (x : List UInt8) : VerifierProgram OpenClaims :=
  lbusTableAccProg Lvm.P20 tabs (pubX x) Lvm.P20.busDepth >>= fun a ↦ kgProgS >>= fun k ↦
    VerifierProgram.ret (assembleS (TS tabs x) (pubX x) a k)

variable {tabs : Pub → List Tab}

/-- Phases 2–3b on a statement's sumcheck tables, in `midSpecOfR`'s form (WP-16b's `specBusS`
with `midBusTableAccSpecS`). -/
noncomputable def specBusA (H : MidHyp tabs) (HA : AccMidHyp tabs) (x : List UInt8) :
    Spec (lbusTableAccProg Lvm.P20 tabs (pubX x) Lvm.P20.busDepth)
      (fun h ↦ RootShape h ∧ Doomed candPairs (fun p ↦ GbA tabs H.hτ x p ∧ GkS p) h)
      (fun a h ↦ Doomed candPairs (fun p ↦ BS tabs x a p ∧ GkS p) h ∧ RootShape h) εS εS LkS :=
  have F := fit_of Lvm.P20 _ (H.fit (pubX x))
  have hμeq : (inst lay26 (sumcheckTabs (tabs (pubX x))) (H.hτ x)).μBus = Lvm.P20.busDepth :=
    F.μBus_eq (H.hτ x)
  have hμeq' : (inst lay26 (TS tabs x) (H.hτ x)).μBus = Lvm.P20.busDepth := F.μBus_eq (H.hτ x)
  have e := bus_errs (inst lay26 (TS tabs x) (H.hτ x)) (by rw [hμeq']; exact F.busLe)
    (le_trans (B_inst_le _ _ _) (H.cons _)) (((vLayout (TS tabs x)).tableLogHeights.foldl max 0))
  have ea := acc_errs
  have S0 := midBusTableAccSpecS Lvm.P20 tabs (pubX x) (H.hτ x) (L₀ := 1) (εmax := εS)
    (fun p ↦ BndS x p.1 ∧ GkS p) F.layOk F.allSc (HA x) (H.keys _) (H.width _)
    candPairs_ncard_le_one (by rw [hμeq]; have := F.busPos; omega) e.1 e.2.2.1 e.2.2.2.1
    e.2.2.2.2.1 (T := LkS) (by rw [ea.1]; exact e.2.2.2.2.2.1) (by rw [ea.1]; exact e.2.2.2.2.2.2.1)
    (by rw [ea.1]; exact e.2.2.2.2.2.2.2) ea.2 e.2.2.2.2.2.2.1
  (hμeq ▸ S0).mono (fun _ hp ↦ ⟨hp.1, Doomed.mono hp.2 fun _ hq ↦
      ⟨⟨⟨hq.1, hq.2.1.1⟩, (accOk_iff Lvm.P20 tabs (pubX x)).mpr hq.2.2⟩, hq.2.1.2⟩⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono hp.1 fun _ hq ↦ ⟨hq.1.1, hq.1.2, hq.2⟩, hp.2⟩) le_rfl e.2.1 le_rfl

/-- **O6 with phase 3b**: the middle phases' specification for the real tables, `Good := GoodA`. -/
theorem midSpec_midSA (H : MidHyp tabs) (HA : AccMidHyp tabs) :
    MidSpec (midSA tabs) (GoodA tabs H.hτ) εS εS :=
  midSpecOfR (busP := fun x ↦ lbusTableAccProg Lvm.P20 tabs (pubX x) Lvm.P20.busDepth)
    (kgP := kgProgS) (asm := fun x a k ↦ assembleS (TS tabs x) (pubX x) a k) (Lb := εS) (Lk := LkS)
    (Gb := GbA tabs H.hτ) (Gk := fun _ ↦ GkS)
    (B := BS tabs) (Kc := KcS) (Qa := fun x ↦ TabRet (TS tabs x)) (Qk := KgRet)
    (specBusA H HA) (fun x ↦ retOK_lbusTableAccProg _ _ _ _) (fun x a T hT ↦ specKgS x a T hT)
    retOK_kgProgS cg_kgProgS (link_assembleS H) (side_midS H)

/-- **The middle phases' shape** (`hsh`) with phase 3b. -/
theorem midShape_midSA (H : MidHyp tabs) : MidShape (midSA tabs) where
  noCommit x := (Lvm.M3.NoCG.bind (noCG_lbusTableAccProg _ _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind cg_kgProgS fun _ ↦ Lvm.M3.cg_ret _).1
  noGrind x := (Lvm.M3.NoCG.bind (noCG_lbusTableAccProg _ _ _ _) fun _ ↦
    Lvm.M3.NoCG.bind cg_kgProgS fun _ ↦ Lvm.M3.cg_ret _).2
  recAffine x l cl hl :=
    ((retOK_lbusTableAccProg _ _ _ _).bind fun a ha ↦ retOK_kgProgS.bind fun k hk ↦
      LeanVM.Protocol.EndToEnd.Sound.RetOK.ret (side_midS H x a k ha hk).1 :
      RetOK (fun cl : OpenClaims ↦ ∀ c ∈ cl.1, IsMultiaffine 19 c.1) (midSA tabs x)) l cl hl

end Lvm.Acc
