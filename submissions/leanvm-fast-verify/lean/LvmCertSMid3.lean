-- WP-16b (CERT). New for lvm (O6): `MidSpec (midS tabs)` for WP-14a's middle phases, from WP-9b's
-- `midBusTableSpecS` and WP-8's `kgSpec` (WP-14's glue `LvmCertSMid.midSpecOf`, here with the
-- programs' return facts), the semantic link of `assembleS`'s claims (`LvmCertSMid3Tab/Kec/Link`)
-- and its side conditions (`LvmCertSMid3Side`); `MidShape (midS tabs)`; `NodeSound` for the good
-- pair `GoodS` from WP-14c's `GoodN`.
import LvmCertSMid2
import LvmCertSMid3Tab
import LvmCertSMid3Kec
import LvmCertSMid3Link
import LvmCertSMid3Side
import LvmVEqFit

/-!
# O6 for `midS`

* `midSpecOfR`: WP-14's `midSpecOf` with return facts `Qa`, `Qk` of the two phases (the link and
  the side conditions need the claims' lengths, which no doom carries);
* **`GoodS T hτ`**: the good pair, WP-14c's `GoodN` with the boundary claims only when the chain
  fits `CH` (`BndS`: V_S's boundary claims read row `(n − 1) mod 2^20`); **`nodeSound_goodS`**:
  `NodeSound` for `GoodS` from `NodeSound` for `GoodN` (`okS` gives `n ≤ 2^20`);
* **`MidHyp tabs`**: what the real tables must meet (`fitsR` for every public input; `KeysOk`,
  positive widths, `FixOk`, the constraint count at every statement's public values); A23: the middle
  phases' `MidSpec`/`MidShape` are AC-S's (`LvmAccSpecCert.midSpec_midSA`, `midShape_midSA`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile.VerifierProgram LeanVM.Protocol.Whir.Sound LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Lvm.KG Lvm.M3
open Lvm.NS (colM ksCol ksY2 msgM msgX Bnd GoodB GoodN)
open scoped ENNReal NNReal

/-! ## The glue with return facts -/

section Glue

variable {α κ : Type} {busP : List UInt8 → VerifierProgram α} {kgP : VerifierProgram κ}
  {asm : List UInt8 → α → κ → OpenClaims}
  {Gb Gk : List UInt8 → Pair → Prop} {B : List UInt8 → α → Pair → Prop}
  {Kc : κ → Pair → Prop} {Qa : List UInt8 → α → Prop} {Qk : κ → Prop} {Lb Lk : ℝ≥0∞}

open Classical in
/-- **`MidSpec` from the phases, with return facts** (`midSpecOf` with `Qa`, `Qk`). -/
theorem midSpecOfR
    (SB : ∀ x, Spec (busP x)
      (fun h ↦ RootShape h ∧ Doomed candPairs (fun p ↦ Gb x p ∧ Gk x p) h)
      (fun a h ↦ Doomed candPairs (fun p ↦ B x a p ∧ Gk x p) h ∧ RootShape h) εS Lb Lk)
    (hQa : ∀ x, RetOK (Qa x) (busP x))
    (SK : ∀ x a (T : ℝ≥0∞), T ≤ εS → Spec kgP (Doomed candPairs (fun p ↦ Gk x p ∧ B x a p))
      (fun k h ↦ Doomed candPairs (fun p ↦ Kc k p ∧ B x a p) h) εS Lk T)
    (hQk : RetOK Qk kgP) (hkc : NoCG kgP)
    (hasm : ∀ x a k (p : Pair), Qa x a → Qk k →
      (∀ c ∈ (asm x a k).1, StackClaim.Holds 19 c p.2) →
      (∀ c ∈ (asm x a k).2, StackClaim.Holds 26 c p.1) → Kc k p ∧ B x a p)
    (hside : ∀ x a k, Qa x a → Qk k → (∀ c ∈ (asm x a k).1, IsMultiaffine 19 c.1) ∧
      (∀ c ∈ (asm x a k).2, IsMultiaffine 26 c.1) ∧ (asm x a k).1.length ≤ 2 ^ 63 ∧
      (asm x a k).2.length ≤ 2 ^ 63) :
    MidSpec (fun x ↦ busP x >>= fun a ↦ kgP >>= fun k ↦ VerifierProgram.ret (asm x a k))
      (fun x qm qr ↦ Gb x (qm, qr) ∧ Gk x (qm, qr)) εS Lb := fun x T hT ↦
  ⟨((Lvm.KG.specWithRet (SB x) (hQa x)).bind' fun a ↦
      if ha : Qa x a then
        ((Lvm.KG.specWithRet ((SK x a T hT).frame RootShape fun _ _ hl hr ↦
            rootShape_append' (hkc.1.reach_commits hl) hr) hQk).mono
          (fun h hp ↦ ⟨Doomed.mono hp.2.1 fun p hq ↦ ⟨hq.2, hq.1⟩, hp.2.2⟩) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).bind' fun k ↦
        if hk : Qk k then
          (Spec.ret (Post := OpenPost) (εmax := εS) (T := T) (asm x a k)).mono
            (fun h hp ↦ openPost_of (hasm x a k · ha hk) (hside x a k ha hk) hp.2.1 hp.2.2)
            (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
        else Spec.dead.mono (fun _ hd ↦ hk hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ hd ↦ ha hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).mono
    (fun h hp ↦ ⟨hp.2, hp.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl⟩

end Glue

/-! ## The good pair -/

/-- The Keccak tables' relations on a pair (`GoodK` without the boundary claims). -/
def GkS (p : Pair) : Prop :=
  CHRel 20 52 (colM p.1) ∧
  KSRel 15 14 ksY2 (Lvm.contRows Lvm.P20) (colM p.1) (ksCol p.1) (msgM p.2) (msgX p.1)

/-- **The good pair of O6**: WP-14c's `GoodN` with the boundary claims when the chain fits `CH`. -/
def GoodS (T : List UInt8 → List Tab) (hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ) : GoodRel :=
  fun x qm qr ↦ (GoodB T hτ x (qm, qr) ∧ BndS x qm) ∧ GkS (qm, qr)

/-- **`NodeSound` for `GoodS`** from `NodeSound` for WP-14c's `GoodN`: `okS` bounds `n` by `2^20`. -/
theorem nodeSound_goodS {VS : Lvm.T.SProg} {vk : RecursionFast.Digest} {T : List UInt8 → List Tab}
    {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ} {child : Column 19 → RecursionFast.Signed}
    (h : NodeSound VS vk (GoodN T hτ) child) : NodeSound VS vk (GoodS T hτ) child :=
  fun c x qm qr hok hG ↦ h c x qm qr hok
    ⟨hG.1.1, hG.2.1, hG.2.2, hG.1.2 (Lvm.NS.okS_n hok).2⟩

/-! ## Errors -/

theorem coe_div_card (d : ℕ) :
    (((d : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞) = errE d := by
  rw [Nat.card_eq_fintype_card, ENNReal.coe_div (by simp), ENNReal.coe_natCast,
    ENNReal.coe_natCast, errE, div_eq_mul_inv]

theorem coe_overE (d : ℕ) : ((LeanVM.Protocol.overE d : ℝ≥0) : ℝ≥0∞) = errE d := by
  rw [LeanVM.Protocol.overE, ← Nat.card_eq_fintype_card, coe_div_card]

theorem εS_lt_one : εS < 1 := by
  unfold εS
  exact pow_lt_one₀ (by simp) (ENNReal.inv_lt_one.mpr (by norm_num)) (by norm_num)

/-- The `KS`/`CH` phases' lead at P20 with one candidate pair. -/
noncomputable abbrev LkS : ℝ≥0∞ := ((16 + 4 : ℕ) : ℝ≥0∞) * (((1 : ℕ) : ℝ≥0∞) * errE 1) + 0

theorem LkS_eq : LkS = errE 20 := by
  simp only [LkS, Nat.cast_one, one_mul, add_zero, errE_smul]

/-- **`midBusTableSpecS`'s error side conditions at `εS`**, one candidate pair, follower `LkS`. -/
theorem bus_errs (I : LeanVM.Protocol.M3Instance) (hμ : I.μBus ≤ 22) (hB : I.B ≤ 2 ^ 60) (m : ℕ) :
    abError I 1 < 1 ∧ abError I 1 + 0 ≤ εS ∧ roundError 1 4 ≤ εS ∧
    interpLead 1 2 (lambdaError 1) ≤ εS ∧ lambdaError 1 + 0 ≤ εS ∧
    roundError 1 3 + LkS ≤ εS ∧ LkS ≤ εS ∧
    xiError I 1 + sumcheckLead (List.replicate m none) LkS ≤ εS := by
  have hab : abError I 1 = errE (4 * 2 ^ I.μBus) := by
    rw [abError, coe_overE, Nat.cast_one, one_mul]
  have hab' : abError I 1 ≤ εS := by
    rw [hab]
    refine errE_le_εS (le_trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by norm_num) hμ))
      (by norm_num))
  have hr : ∀ d, roundError 1 d = errE d := fun d ↦ by
    rw [roundError, coe_div_card, Nat.cast_one, one_mul]
  have hl : lambdaError 1 = errE 2 := by
    rw [lambdaError, coe_div_card, Nat.cast_one, one_mul]
  have hu : unitError 1 = errE 1 := by simp [unitError, errE]
  have hx : xiError I 1 = errE (I.B + 3 - 1) := by
    rw [xiError, coe_div_card, Nat.cast_one, one_mul]
  refine ⟨lt_of_le_of_lt hab' εS_lt_one, by rw [add_zero]; exact hab', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr]; exact errE_le_εS (by norm_num)
  · rw [interpLead_eq, hu, hl, show ((2 : ℕ) : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from rfl, errE_smul,
      errE_add]
    exact errE_le_εS (by norm_num)
  · rw [hl, add_zero]; exact errE_le_εS (by norm_num)
  · rw [hr, LkS_eq, errE_add]; exact errE_le_εS (by norm_num)
  · rw [LkS_eq]; exact errE_le_εS (by norm_num)
  · refine le_trans (add_le_add le_rfl (sumcheckLead_le _ _)) ?_
    rw [hx, LkS_eq, errE_add]
    exact errE_le_εS (by omega)

/-! ## The middle phases' specification -/

/-- The sumcheck tables of a statement. -/
def TS (tabs : Lvm.Pub → List Tab) (x : List UInt8) : List Tab := sumcheckTabs (tabs (pubX x))

/-- **What the real tables must meet** for O6: `fitsR` (INT-2's record check) for every public
input, and at every statement's public values WP-9b's table checks (`tabsOkB`, `fixOk_lvmTabs`) and
the constraint count. -/
structure MidHyp (tabs : Lvm.Pub → List Tab) : Prop where
  fit : ∀ pub, fitsR Lvm.P20 (tabs pub) = true
  keys : ∀ x, KeysOk (TS tabs x)
  width : ∀ x, ∀ t ∈ TS tabs x, 0 < t.w
  fix : ∀ x, FixOk (TS tabs x)
  cons : ∀ x, ((TS tabs x).map fun t ↦ t.cons.length).sum ≤ 2 ^ 60

/-- The record's table evaluations are few. -/
theorem tableEvals_P20_le : Lvm.P20.tableEvals ≤ 2 ^ 62 := by decide

variable {tabs : Lvm.Pub → List Tab}

theorem MidHyp.hτ (H : MidHyp tabs) : ∀ x, ∀ t ∈ TS tabs x, t.τ ≤ lay26.μ :=
  fun x ↦ (fit_of Lvm.P20 _ (H.fit (pubX x))).hτ

theorem B_inst_le (L : Lay) (T : List Tab) (hτ : ∀ t ∈ T, t.τ ≤ L.μ) :
    (inst L T hτ).B ≤ (T.map fun t ↦ t.cons.length).sum := by
  classical
  unfold LeanVM.Protocol.M3Instance.B
  rw [← Finset.sum_subtype (Finset.univ.filter (inst L T hτ).SumcheckTable) (fun x ↦ by simp)
    (fun j ↦ ((inst L T hτ).constraints j).length)]
  refine le_trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) (le_of_eq ?_)
  change ∑ j : Fin T.length, ((T.get j).cons.map (CPoly.toMv _)).length = _
  simp only [List.length_map]
  exact Fin.sum_univ_fun_getElem T fun t ↦ t.cons.length

/-- The bus/table phase's claims on a pair (`midBusTableSpecS`'s post) and the boundary claims,
carried through V_S phases 4–7. -/
def BS (tabs : Lvm.Pub → List Tab) (x : List UInt8) (a : List ColumnClaim) (p : Pair) : Prop :=
  (∀ c ∈ a, BlockHolds lay26 (TS tabs x) p.1 p.2 c) ∧ BndS x p.1

/-- V_S phases 2–3 on a statement's sumcheck tables, in `midSpecOfR`'s form. -/
noncomputable def specBusS (H : MidHyp tabs) (x : List UInt8) :
    Spec (lbusTableCheckProg (TS tabs x) Lvm.P20.busDepth)
      (fun h ↦ RootShape h ∧ Doomed candPairs (fun p ↦ (GoodB (TS tabs) H.hτ x p ∧ BndS x p.1) ∧
        GkS p) h)
      (fun a h ↦ Doomed candPairs (fun p ↦ BS tabs x a p ∧ GkS p) h ∧ RootShape h) εS εS LkS :=
  have F := fit_of Lvm.P20 _ (H.fit (pubX x))
  have hμeq : (inst lay26 (TS tabs x) (H.hτ x)).μBus = Lvm.P20.busDepth := F.μBus_eq (H.hτ x)
  have e := bus_errs (inst lay26 (TS tabs x) (H.hτ x)) (by rw [hμeq]; exact F.busLe)
    (le_trans (B_inst_le _ _ _) (H.cons _)) (((vLayout (TS tabs x)).tableLogHeights.foldl max 0))
  have S0 := midBusTableSpecS (TS tabs x) (H.hτ x) (L₀ := 1) (εmax := εS)
    (fun p ↦ BndS x p.1 ∧ GkS p) F.layOk F.allSc (H.keys _) (H.width _) (H.fix _)
    candPairs_ncard_le_one (by rw [hμeq]; have := F.busPos; omega) e.1 e.2.2.1 e.2.2.2.1
    e.2.2.2.2.1 (T := LkS) e.2.2.2.2.2.1 e.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2
  (hμeq ▸ S0).mono (fun _ hp ↦ ⟨hp.1, Doomed.mono hp.2 fun _ hq ↦ ⟨⟨hq.1, hq.2.1⟩, hq.2.2⟩⟩)
    (fun _ _ hp ↦ ⟨Doomed.mono hp.1 fun _ hq ↦ ⟨hq.1.1, hq.1.2, hq.2⟩, hp.2⟩) le_rfl e.2.1 le_rfl

/-- V_S phases 4–7 at P20, in `midSpecOfR`'s form. -/
noncomputable def specKgS (x : List UInt8) (a : List ColumnClaim) (T : ℝ≥0∞) (hT : T ≤ εS) :
    Spec kgProgS (Doomed candPairs (fun p ↦ GkS p ∧ BS tabs x a p))
      (fun k h ↦ Doomed candPairs (fun p ↦ KcS k p ∧ BS tabs x a p) h) εS LkS T :=
  have e := kg_errs
  have s := kg_struct
  (kgSpec (C := candPairs) (L₀ := 1) (εmax := εS) (T := T) candPairs_stable candPairs_ncard_le_one
    16 52 11 14 ksY2 s.1 s.2.1 s.2.2.1 (Lvm.contRows Lvm.P20) s.2.2.2.1 s.2.2.2.2
    (fun q ↦ colM q.1) (fun q ↦ colM q.1) (fun q ↦ ksCol q.1) (fun q ↦ msgM q.2)
    (fun q ↦ msgX q.1) (BS tabs x a) e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1
    hT).mono (fun _ hd ↦ Doomed.mono hd fun _ hq ↦ ⟨⟨hq.1, hq.2.1⟩, hq.2.2⟩)
    (fun _ _ hp ↦ Doomed.mono hp.2 fun _ hq ↦ ⟨hq.1.1, hq.1.2, hq.2⟩) le_rfl le_rfl le_rfl

/-- **The semantic link**: the assembled claims holding on a pair give `KcS ∧ BS`. -/
theorem link_assembleS (H : MidHyp tabs) (x : List UInt8) (a : List ColumnClaim) (k : KgOut)
    (p : Pair) (ha : TabRet (TS tabs x) a) (hk : KgRet k)
    (h1 : ∀ c ∈ (assembleS (TS tabs x) (pubX x) a k).1, StackClaim.Holds 19 c p.2)
    (h2 : ∀ c ∈ (assembleS (TS tabs x) (pubX x) a k).2, StackClaim.Holds 26 c p.1) :
    KcS k p ∧ BS tabs x a p := by
  have hc := holdsC_of_assembleS h1 h2
  obtain ⟨⟨hr, -, hcc, -, -, hρ, -, -⟩, ⟨hrk, -, hck, -, -, hkc, hks⟩⟩ := hk
  have hm : ∀ b, (Com.main, b) ∈ claimsS (TS tabs x) (pubX x) a k →
      StackClaim.Holds 26 b.onStack p.1 := fun b hb ↦ hc _ hb
  have hKC : ∀ b ∈ keccakClaimsE chBlk k.1.1, StackClaim.Holds 26 b.onStack p.1 :=
    fun b hb ↦ hm b (by simp [claimsS, hb])
  have hF : ∀ b ∈ chFixedClaimsE k.1.1.1 k.1.1.2.1 (pubX x), StackClaim.Holds 26 b.onStack p.1 :=
    fun b hb ↦ hm b (by simp [claimsS, hb])
  have hKK : ∀ b ∈ keccakClaimsE ksBlk k.2.1, StackClaim.Holds 26 b.onStack p.1 :=
    fun b hb ↦ hm b (by simp [claimsS, hb])
  have hsub : ∀ l : List (Com × BClaim), (∀ e ∈ l, e ∈ claimsS (TS tabs x) (pubX x) a k) →
      ∀ e ∈ l, HoldsC p.1 p.2 e := fun l hl e he ↦ hc e (hl e he)
  refine ⟨⟨⟨callerClaims_ch k.1.1 hr hcc (pubX x) hKC hF,
      chLinkClaims_of k.1.2 hρ (hsub _ (fun e he ↦ by simp [claimsS, he]))⟩,
    ⟨callerClaims_ks k.2.1 hrk hck hKK (hsub _ (fun e he ↦ by simp [claimsS, he])),
      ksLinkClaims_of k.2.2.1 k.2.2.2.1 k.2.2.2.2 hkc hks
        (hsub _ (fun e he ↦ by simp [claimsS, he]))⟩⟩,
    blockHolds_of_tableClaims (T := TS tabs x) (fit_of Lvm.P20 _ (H.fit (pubX x))).layOk ha
      (hsub _ (fun e he ↦ by simp [claimsS, he])), bndS_of_chFixed x _ _ hF⟩

theorem side_midS (H : MidHyp tabs) (x : List UInt8) (a : List ColumnClaim) (k : KgOut)
    (ha : TabRet (TS tabs x) a) (hk : KgRet k) :
    (∀ c ∈ (assembleS (TS tabs x) (pubX x) a k).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleS (TS tabs x) (pubX x) a k).2, IsMultiaffine 26 c.1) ∧
    (assembleS (TS tabs x) (pubX x) a k).1.length ≤ 2 ^ 63 ∧
    (assembleS (TS tabs x) (pubX x) a k).2.length ≤ 2 ^ 63 :=
  have F := fit_of Lvm.P20 _ (H.fit (pubX x))
  side_assembleS _ _ a k F.layOk ha (F.evals ▸ tableEvals_P20_le) hk (by rw [length_pubX_h]; norm_num)

-- AC-N (A23): `midSpec_midS`/`midShape_midS'` (and `midS_eq`) were for the A21 middle phases
-- (`lbusTableCheckProg`, the per-column fixed check); `midS` now runs phase 3b and its O6 is AC-S's
-- `midSpec_midSA`/`midShape_midSA` (`LvmAccSpecCert`, `midS = midSA` by `rfl`).

end Lvm.ASM
