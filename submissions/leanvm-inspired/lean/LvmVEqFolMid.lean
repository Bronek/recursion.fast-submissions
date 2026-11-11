-- New for lvm (WP-14a, H0): the middle phases of `P_S` (`midS`, LvmVEqMid: bus, tables, `CH`, `CH` link,
-- `KS`, `KS` link) follow the schedule's items (`Fol`, LvmVEqShape), and the middle phases' shape
-- obligation of WP-14d (`MidFollows`, LvmCertSExqKinds).
import LvmVEqFol
import LvmVEqFit
import LvmVEqRel

/-!
# The middle phases follow the schedule

The phases' items of `LvmSchedule.phases` by name (`commitI`, `busI`, …, `openMainI`; `phases_eq`,
`schedule_eq`, `midItems_eq` by `rfl`), and per phase a `FolP` (from every `pp`, the program follows
the phase's atoms and keeps `pp`):

* `folP_busTabAccProg`: WP-9b's bus phase and table sumcheck, then A23's phase 3b (`folP_accProg`),
  against `busI ++ tablesI`, given the record's `leafdecReads = 1`, `tableRounds` and `tableEvals`
  of the tables (`Fit`);
* `folP_tapeProg` (lvm2 S2: `folP_tapeGkr`, `folP_wireChProg`), `folP_callerProg`, `folP_ksLinkProg`,
  `folP_kgProgS`: the tape caller and WP-8's `KS` programs against `tapeI ++ wireI ++ ksI ++ ksLinkI`;
* **`folP_midS`**, `fol_midS`: `midS tabs x` against `midItems` when every `tabs pub` fits `P20`;
* **`midFollows_midS`**: WP-14d's `MidFollows (midS tabs)`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## The phases' items -/

section Items

variable (p : Params)

/-- The commit phase: the two roots' caps. -/
def commitI : List Item := [.cap (p.level ⟨.main, 0⟩).cap ⟨.main, 0⟩, .cap (p.level ⟨.crec, 0⟩).cap ⟨.crec, 0⟩]
/-- The bus phase. -/
def busI : List Item := List.flatten [smp (busBits + 1), gpI p.busDepth, rd p.leafdecReads]
/-- The table sumcheck, then phase 3b (A23: `κ`, the line polynomial, `t`, the zero scalar). -/
def tablesI : List Item := List.flatten [smp 1, sumcheckI p.tableRounds 3, rd p.tableEvals,
  smp p.accLog, rd (accVars + 1), smp 1, rd 1]
/-- The tape (lvm2 S2, T1–T2). -/
def tapeI : List Item := List.flatten [smp p.logN, rd lanes, tapeLayersI p.logN]
/-- The wire (lvm2 S2, T3–T4). -/
def wireI : List Item := List.flatten [sumcheckI p.logN 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]
/-- `KS`'s Keccak GKR. -/
def ksI : List Item := List.flatten [smp p.ksLog, rd lanes, keccakI p.ksLog, smp ringStages]
/-- The `KS` link. -/
def ksLinkI : List Item := List.flatten [smp (p.ksLog + laneBits), sumcheckI p.ksLog 2, rd 4]
/-- `C_rec`'s opening. -/
def openRecI : List Item := smp 1 ++ whirI .crec p.recLevels p.recFinalLog p.grind
/-- `C_main`'s opening. -/
def openMainI : List Item := smp 1 ++ whirI .main p.mainLevels p.mainFinalLog p.grind

theorem phases_eq : phases p = [(.commit, commitI p), (.bus, busI p), (.tables, tablesI p), (.tape, tapeI p),
    (.wire, wireI p), (.ks, ksI p), (.ksLink, ksLinkI p), (.openRec, openRecI p),
    (.openMain, openMainI p)] := rfl

theorem schedule_eq : schedule p = commitI p ++ (busI p ++ (tablesI p ++ (tapeI p ++ (wireI p ++
    (ksI p ++ (ksLinkI p ++ (openRecI p ++ (openMainI p ++ [])))))))) := rfl

end Items

theorem midItems_eq : Lvm.ASM.midItems =
    busI P20 ++ (tablesI P20 ++ (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ (ksLinkI P20 ++ []))))) := rfl

/-! ## The bus phase and the table sumcheck -/

section BusTables

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

theorem folP_abProg : FolP cap shp idx EndToEnd.Front.abProg (List.replicate (busBits + 1) .sm) fun _ ↦ True := by
  rw [List.replicate_succ']
  exact (folP_sampleChallenges 4).bind fun _ _ ↦ folP_sampleChallenge.bind_ret fun _ _ ↦ trivial

/-- **The bus phase** against `busI`. -/
theorem folP_lvmBusProg (hl : p.leafdecReads = 1) :
    FolP cap shp idx (M3.lvmBusProg p.busDepth) (atomsOf p (busI p)) fun _ ↦ True := by
  simp only [busI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd, hl]
  unfold M3.lvmBusProg
  exact folP_abProg.bind fun _ _ ↦ (folP_verifyGkrGrandProducts p _).bind fun _ _ ↦
    (folP_require _).bind fun _ _ ↦ folP_readScalar.bind_nil fun _ _ ↦
    (folP_require _).bind_nil fun _ _ ↦ FolP.ret trivial

theorem folP_tableTermsClaims (tables : List Verifier.Table) (cp fp point : List E) :
    ∀ (rows : List (Verifier.Table × ℕ × List Verifier.Form × E)) (cursor : ℕ) (final : E)
      (claims : List Verifier.ColumnClaim),
      FolP cap shp idx (Verifier.tableTermsClaims tables cp fp point rows cursor final claims)
        (List.replicate (rows.map fun r ↦ r.1.width).sum .rd) fun _ ↦ True
  | [], _, _, _ => FolP.ret trivial
  | r :: rows, cursor, final, claims => by
    rw [List.map_cons, List.sum_cons, List.replicate_add]
    unfold Verifier.tableTermsClaims
    exact (folP_readScalars _).bind fun _ _ ↦ folP_tableTermsClaims tables cp fp point rows _ _ _

theorem length_tableWeights (heights : List ℕ) (eqp point : List E) :
    (Verifier.tableWeights heights eqp point).length = heights.length := by
  unfold Verifier.tableWeights
  suffices h : ∀ (l : List (E × ℕ)) (acc : List E), acc.length = heights.length →
      (l.foldl (fun weights (x : E × ℕ) ↦
        List.zipWith (fun weight height ↦ weight * if x.2 < height then 1 + eqp.getD x.2 0 + x.1 else x.1)
          weights heights) acc).length = heights.length from h _ _ (by simp)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x l ih => intro acc h; exact ih _ (by simp [h])

theorem folP_tableSumcheckClaims (tables : List Verifier.Table) (heights : List ℕ)
    (busForms : List (List Verifier.Form)) (cp fp eqp : List E) (target : E)
    (hh : tables.length ≤ heights.length) (hb : tables.length ≤ busForms.length) :
    FolP cap shp idx (Verifier.tableSumcheckClaims tables heights busForms cp fp eqp target)
      (atomsOf p (sumcheckI (heights.foldl max 0) 3) ++ List.replicate (tables.map (·.width)).sum .rd)
      fun _ ↦ True := by
  unfold Verifier.tableSumcheckClaims
  refine (folP_sumcheck p rfl (by norm_num) _ _ _ (List.length_replicate ..)).bind fun x _ ↦ ?_
  have hrows : ((List.zip tables (List.zip heights (List.zip busForms
      (Verifier.tableWeights heights eqp x.1.reverse)))).map fun r ↦ r.1.width) = tables.map (·.width) := by
    rw [show (fun r : Verifier.Table × ℕ × List Verifier.Form × E ↦ r.1.width) =
      Verifier.Table.width ∘ Prod.fst from rfl, ← List.map_map, List.map_fst_zip]
    simp [length_tableWeights]; omega
  rw [← List.append_nil (List.replicate _ _), ← hrows]
  exact (folP_tableTermsClaims _ _ _ _ _ _ _ _).bind fun _ _ ↦ (folP_require _).bind_nil fun _ _ ↦
    FolP.ret trivial

theorem folP_tablePhaseClaims (tables : List Verifier.Table) (layout : Verifier.Layout)
    (bus : Verifier.BusResult) (hh : tables.length ≤ layout.tableLogHeights.length)
    (hb : tables.length ≤ bus.forms.length) :
    FolP cap shp idx (Verifier.tablePhaseClaims tables layout bus)
      (.sm :: (atomsOf p (sumcheckI (layout.tableLogHeights.foldl max 0) 3) ++
        List.replicate (tables.map (·.width)).sum .rd)) fun _ ↦ True := by
  unfold Verifier.tablePhaseClaims
  exact folP_sampleChallenge.bind fun _ _ ↦
    (folP_tableSumcheckClaims p _ _ _ _ _ _ _ hh hb).bind_ret fun _ _ ↦ trivial

theorem width_vTables (T : List M3.Tab) : ((M3.vTables T).map (·.width)).sum = (T.map (·.w)).sum := by
  suffices h : ∀ k, ((T.zipIdx k).map fun x ↦ x.1.w) = T.map (·.w) by
    simp [M3.vTables, M3.vTable, Verifier.Table.width, List.map_map, Function.comp_def, h]
  induction T with
  | nil => intro; rfl
  | cons t T ih => intro k; simp [List.zipIdx_cons, ih]

/-- **Phase 3b** (AC-S's `accProg`) against its items. -/
theorem folP_accProg (dk D : ℕ) (ok : Bool) (yIn : E) (a : List E) (yOwn : List E → E)
    (bOf : List E → List E) (Φ : List E → E) :
    FolP cap shp idx (Lvm.Acc.accProg dk D ok yIn a yOwn bOf Φ)
      (atomsOf p (List.flatten [smp dk, rd (D + 1), smp 1, rd 1])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
    atomsOf_rd]
  unfold Lvm.Acc.accProg
  exact (folP_sampleChallenges dk).bind fun _ _ ↦ (folP_readScalars (D + 1)).bind fun _ _ ↦
    folP_sampleChallenge.bind fun _ _ ↦ folP_readScalar.bind_nil fun _ _ ↦
      (folP_require _).mono fun _ _ ↦ trivial

/-- **The bus phase, the table sumcheck and phase 3b** (`busTabAccProg`) against `busI ++ tablesI`
at `P20`. -/
theorem folP_busTabAccProg (tabs : Pub → List M3.Tab) (pub : Pub) (hl : P20.leafdecReads = 1)
    (hr : P20.tableRounds = ((M3.sumcheckTabs (tabs pub)).map (·.τ)).foldl max 0)
    (he : P20.tableEvals = ((M3.sumcheckTabs (tabs pub)).map (·.w)).sum) :
    FolP cap shp idx (busTabAccProg tabs pub) (atomsOf P20 (busI P20 ++ tablesI P20)) fun _ ↦ True := by
  have e : atomsOf P20 (busI P20 ++ tablesI P20) = atomsOf P20 (busI P20) ++
      (.sm :: (atomsOf P20 (sumcheckI (((M3.vLayout (M3.sumcheckTabs (tabs pub))).tableLogHeights).foldl
        max 0) 3) ++ List.replicate ((M3.vTables (M3.sumcheckTabs (tabs pub))).map (·.width)).sum .rd)) ++
      atomsOf P20 (List.flatten [smp P20.accLog, rd (accVars + 1), smp 1, rd 1]) := by
    simp only [tablesI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp,
      atomsOf_rd, width_vTables, M3.vLayout, ← hr, ← he, List.append_assoc]
    rfl
  rw [e]
  unfold busTabAccProg Lvm.Acc.lbusTableAccProg M3.lvmBusTableProg Lvm.Acc.accProgV
  exact ((folP_lvmBusProg P20 hl).bind fun b _ ↦
    folP_tablePhaseClaims P20 (M3.vTables _) (M3.vLayout _) _ (by simp [M3.vLayout])
      (by simp [M3.busResV, M3.busFinalV])).bind fun _ _ ↦
    (folP_accProg P20 _ _ _ _ _ _ _ _).bind_ret fun _ _ ↦ trivial

end BusTables

/-! ## The Keccak phases (WP-8's `kgSpec` program) -/

section Kg

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ} (p : Params)

/-- **The Keccak phase with caller claims** against `smp h, rd lanes, keccakI h, smp ringStages`. -/
theorem folP_callerProg (h : ℕ) :
    FolP cap shp idx (KG.callerProg h) (atomsOf p (List.flatten [smp h, rd lanes, keccakI h, smp ringStages]))
      fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp, atomsOf_rd]
  unfold KG.callerProg
  exact (folP_sampleChallenges h).bind fun r hr ↦ (folP_readScalars 25).bind fun v _ ↦
    (folP_verifyKeccak p h r v hr).bind fun _ _ ↦ (folP_ringSwitch _ _).bind_ret fun _ _ ↦ trivial

/-- **The `KS` link** against its items. -/
theorem folP_ksLinkProg (hk r : ℕ) (rows : List ℕ) :
    FolP cap shp idx (KG.ksLinkProg hk r rows)
      (atomsOf p (List.flatten [smp (hk + laneBits), sumcheckI hk 2, rd 4])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp, atomsOf_rd]
  unfold KG.ksLinkProg
  exact (folP_sampleChallenges _).bind fun _ _ ↦
    (folP_sumcheck p rfl (by norm_num) _ hk _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 4).bind_nil fun _ _ ↦ (folP_require _).bind_nil fun _ _ ↦ FolP.ret trivial

/-- **A generic Keccak layer** (T-G's `verifyKeccakLayerS`) against `keccakLayerI`. -/
theorem folP_verifyKeccakLayerS (sh : KeccakGkr.Shape) (logSteps step : ℕ) (claim : Verifier.KeccakClaim) :
    FolP cap shp idx (KeccakGkr.verifyKeccakLayerS sh logSteps step claim)
      (atomsOf p (keccakLayerI claim.point.length)) fun c ↦ c.point.length = claim.point.length := by
  simp only [keccakLayerI, List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append,
    atomsOf_rd, atomsOf_smp]
  unfold KeccakGkr.verifyKeccakLayerS
  exact (folP_readScalars _).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    folP_sampleChallenge.bind fun _ _ ↦ (folP_keccakPackRounds p claim.point _ _).bind fun x hx ↦
    (folP_sumcheck p rfl (by norm_num) _ localBits _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 3).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    folP_sampleChallenge.bind_ret fun _ _ ↦ hx

theorem folP_keccakLayersS (sh : KeccakGkr.Shape) (logSteps : ℕ) :
    ∀ (steps : List ℕ) (claim : Verifier.KeccakClaim),
    FolP cap shp idx (KeccakGkr.keccakLayersS sh logSteps steps claim)
      (List.replicate steps.length (atomsOf p (keccakLayerI claim.point.length))).flatten
      fun c ↦ c.point.length = claim.point.length
  | [], _ => FolP.ret rfl
  | st :: steps, claim => by
    rw [List.length_cons, List.replicate_succ, List.flatten_cons]
    exact (folP_verifyKeccakLayerS p sh logSteps st claim).bind fun c hc ↦ by
      rw [← hc]
      exact folP_keccakLayersS sh logSteps steps c

/-- **The tape's GKR** (T-G's `tapeGkr`) against `tapeLayersI`, the instance point of `logSteps`
coordinates. -/
theorem folP_tapeGkr (logSteps : ℕ) (inst output : List E) (hinst : inst.length = logSteps) :
    FolP cap shp idx (KeccakGkr.tapeGkr logSteps inst output) (atomsOf p (tapeLayersI logSteps))
      fun _ ↦ True := by
  rw [KeccakGkr.tapeGkr_eq]
  simp only [tapeLayersI, atomsOf_append, atomsOf_smp, atomsOf_flatten, List.map_replicate]
  refine (folP_sampleChallenges _).bind fun lp _ ↦ ?_
  have hpt' : (KeccakGkr.tapeFirstClaim inst lp output).point.length = logSteps - packBits := by
    simp only [KeccakGkr.tapeFirstClaim, List.length_drop, hinst]; rfl
  rw [← hpt', show tapeDepth = (List.range 24).length by simp; rfl]
  exact (folP_keccakLayersS p KeccakGkr.Shape.tape logSteps _ _).mono fun _ _ ↦ trivial

/-- **T-W's slot reduction** (two lane bits) against its items. -/
theorem folP_slotProg (sb blk : ℕ) (W : ℕ → ℕ → E) (pt : List E) (v : E) :
    FolP cap shp idx (KG.slotProg 2 sb blk W pt v)
      (atomsOf p (List.flatten [sumcheckI 2 2, rd kBits, smp ringStages])) fun _ ↦ True := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_smp, atomsOf_rd]
  unfold KG.slotProg
  exact (folP_sumcheck p rfl (by norm_num) _ 2 _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 64).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_ringSwitch _ _).bind_ret fun _ _ ↦ trivial

/-- **T-W's wiring phase** against `wireI`'s items. -/
theorem folP_wireChProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : Verifier.KeccakClaim) :
    FolP cap shp idx (KG.wireChProg w sb dsel s n claim)
      (atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]))
      fun _ ↦ True := by
  have e : atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]) =
      atomsOf p (sumcheckI w 2) ++ (List.replicate 1 .rd ++
        atomsOf p (List.flatten [sumcheckI 2 2, rd kBits, smp ringStages])) := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rd,
      atomsOf_smp, List.append_assoc]
  rw [e]
  unfold KG.wireChProg
  exact (folP_sumcheck p rfl (by norm_num) _ w _ (List.length_replicate ..)).bind fun _ _ ↦
    (folP_readScalars 1).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_slotProg p _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **The tape caller** (lvm2 S2, `tapeProg`) against the tape's and the wire's items. -/
theorem folP_tapeProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (KG.tapeProg w sb dsel s n)
      (atomsOf p (List.flatten [smp w, rd lanes, tapeLayersI w]) ++
        atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]))
      fun _ ↦ True := by
  have e : atomsOf p (List.flatten [smp w, rd lanes, tapeLayersI w]) ++
        atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]) =
      List.replicate w .sm ++ (List.replicate 25 .rd ++ (atomsOf p (tapeLayersI w) ++
        atomsOf p (List.flatten [sumcheckI w 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]))) := by
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, atomsOf_append, atomsOf_rd,
      atomsOf_smp, List.append_assoc]; rfl
  rw [e]
  unfold KG.tapeProg
  exact (folP_sampleChallenges w).bind fun r hr ↦ (folP_readScalars 25).bind fun v _ ↦
    (folP_tapeGkr p w r v hr).bind fun _ _ ↦ (folP_require _).bind fun _ _ ↦
    (folP_wireChProg p _ _ _ _ _ _).bind_ret fun _ _ ↦ trivial

/-- **V_S phases 4–7** (`kgProgS`, lvm2 S2) against the tape, the wire, `KS`, the `KS` link at
`P20`. -/
theorem folP_kgProgS (s : RecursionFast.Digest) (n : ℕ) :
    FolP cap shp idx (kgProgS s n) (atomsOf P20 (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ ksLinkI P20))))
      fun _ ↦ True := by
  have e : atomsOf P20 (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ ksLinkI P20))) =
      (atomsOf P20 (tapeI P20) ++ atomsOf P20 (wireI P20)) ++
        (atomsOf P20 (ksI P20) ++ atomsOf P20 (ksLinkI P20)) := by
    simp only [atomsOf_append, List.append_assoc]
  rw [e]
  unfold kgProgS
  exact (folP_tapeProg P20 20 2 0 s n).bind fun _ _ ↦
    (FolP.bind (S := fun _ ↦ True) (folP_callerProg P20 (11 + 4)) fun _ _ ↦
      (folP_ksLinkProg P20 (11 + 4) 14 _).bind_ret fun _ _ ↦ trivial).bind_ret fun _ _ ↦ trivial

end Kg

/-! ## The middle phases -/

section Mid

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {idx : Ref → ℕ}

/-- **The middle phases follow `midItems`** when the tables fit `P20`. -/
theorem folP_midS (tabs : Pub → List M3.Tab) (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (x : List UInt8) : FolP cap shp idx (midS tabs x) (atomsOf P20 Lvm.ASM.midItems) fun _ ↦ True := by
  have F := fit_of P20 _ (hfit (pubX x))
  have e : atomsOf P20 Lvm.ASM.midItems = atomsOf P20 (busI P20 ++ tablesI P20) ++
      atomsOf P20 (tapeI P20 ++ (wireI P20 ++ (ksI P20 ++ ksLinkI P20))) := by
    simp only [midItems_eq, atomsOf_append, List.append_nil, List.append_assoc]
  rw [e]
  unfold midS
  exact (folP_busTabAccProg tabs (pubX x) F.leafdec F.rounds F.evals).bind fun _ _ ↦
    (folP_kgProgS _ _).bind_ret fun _ _ ↦ trivial

/-- `midS` at P20's commitment table, from any pending positions (stated with `@`: elaborating a
`Fol` at concrete atoms by the default application elaborator unfolds it). -/
theorem fol_midS (tabs : Pub → List M3.Tab) (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (x : List UInt8) (pp : List ℕ) :
    Fol capS shpS idxS (midS tabs x) (atomsOf P20 Lvm.ASM.midItems) pp fun _ pp' ↦ pp' = pp :=
  @FolP.fol capS shpS idxS _ (midS tabs x) (atomsOf P20 Lvm.ASM.midItems) (fun _ ↦ True)
    (folP_midS tabs hfit x) pp

/-- Is the item a positions item. -/
def isPos : Item → Bool
  | .positions _ => true
  | _ => false

theorem midItems_noPosB : Lvm.ASM.midItems.all (fun it ↦ !isPos it) = true := by decide +kernel

theorem midItems_noPos : ∀ it ∈ Lvm.ASM.midItems, ∀ r, it ≠ .positions r := by
  intro it hit r heq
  have := List.all_eq_true.mp midItems_noPosB it hit
  subst heq
  simp [isPos] at this

/-- **WP-14d's shape obligation**: every accepted run of `midS tabs x` has the kinds of
`midItems`. -/
theorem midFollows_midS (tabs : Pub → List M3.Tab) (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true) :
    Lvm.ASM.MidFollows (midS tabs) := by
  intro x l a hl
  rw [(@fol_after capS shpS idxS _ (atomsOf P20 Lvm.ASM.midItems) (midS tabs x) [] (fun _ pp' ↦ pp' = [])
    (fol_midS tabs hfit x []) l a hl).1, atomKinds_atomsOf P20 _ midItems_noPos]

end Mid

end Lvm.VEq
