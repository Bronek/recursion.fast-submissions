-- adapted from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/BusPhase.lean` (WP-2's port
-- `LvmFrontBusPhase`, formal rev 40f877dc): `busTailSpec`/`busThenSpec` for an instance with no boundary
-- block (no framework fingerprint, no boundary value read); and from `.../Front/TablePhase.lean`
-- (`LvmFrontTablePhase`): `TableFid`, `tableSumcheckSpec`, `tablePhaseSpec`, generalised from leanISA's
-- `BusWit` result to any bus result and statement (`TableFidG`, `tableSumcheckSpecG`, `tablePhaseSpecG`);
-- new for lvm (WP-9): `Bus.Conditions` of the lvm instance, `lvmBusTableSpec`.
import LvmM3Inst
import LvmFrontBusTable

/-!
# The bus phase of the lvm instance

**Side conditions** (`inst_conditions`): the lvm instance satisfies leanVM's `Bus.Conditions`
when every constrained table reads or seeds (so it has a push flush, of its own height): each
table pushes and pulls the same number of flushes (a read's push and pull, a seed and its
finalize), so the pull side has the push side's leaves, and the count side (one block per read)
has at most that many.

**The phase on the wire** (`lvmBusProg`): leanVM's `verify_bus_balance` without its framework
blocks: the fingerprint challenges `(α, β)` (`abProg`), the grand-product GKR at the push side's
depth `μ_bus` (`verifyGkrGrandProducts`), the count root nonzero. The instance has no boundary
block, so the bus phase reads no boundary value (`busClaims = 0`): the leaf decomposition is pure.
**`lvmBusSpec`**: from the commitment's doom (`Seam.commit`, no candidate satisfies `M3Holds`) to
doom on the bus seam at the protocol's output on what was read (`Bus.busOut`), with leanVM's
errors: `abError L₀ = L₀·4·2^{μ_bus}/|E|` for `(α, β)`, `roundError L₀ 4` per GKR round,
`lambdaError L₀` per combiner.
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Front CompPoly CMlPolynomialEval
open scoped NNReal ENNReal

/-! ## Side conditions -/

section Conditions

variable (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ)

theorem flushes_push_length (t : Tab) :
    (t.flushes.filter fun f ↦ decide (f.1 = Side.push)).length = t.reads.length + t.seeds.length := by
  simp [Tab.flushes, List.filter_append, List.filter_map, Function.comp_def]

theorem flushes_pull_length (t : Tab) :
    (t.flushes.filter fun f ↦ decide (f.1 = Side.pull)).length = t.reads.length + t.seeds.length := by
  simp [Tab.flushes, List.filter_append, List.filter_map, Function.comp_def]

theorem counts_length_le (t : Tab) : t.counts.length ≤ t.reads.length + t.seeds.length := by
  unfold Tab.counts
  exact (List.length_filterMap_le _ _).trans (Nat.le_add_right _ _)

theorem sum_flatMap' {α : Type} (l : List α) (f : α → List ℕ) :
    (l.flatMap f).sum = (l.map fun a ↦ (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem two_pow_comp {I : M3Instance} :
    (fun src : Bus.Source I ↦ 2 ^ src.κ) = (fun n ↦ 2 ^ n) ∘ Bus.Source.κ := rfl

/-- A side's leaves, table by table. -/
theorem leafCount_side (k : Fin 3) (s : Side) (hk : Bus.sources (inst L tabs hτ) k = Bus.sideSources (inst L tabs hτ) s) :
    Bus.leafCount (inst L tabs hτ) k = ((List.finRange tabs.length).map fun j ↦
      (((inst L tabs hτ).flushes j).filter fun f ↦ decide (f.1 = s)).length * 2 ^ (tabs.get j).τ).sum := by
  have h := Bus.sideSources_map_κ (inst L tabs hτ) s
  have hb : (inst L tabs hτ).boundary = [] := rfl
  rw [hb] at h
  simp only [List.filter_nil, List.map_nil, List.nil_append] at h
  rw [Bus.leafCount, hk, two_pow_comp, ← List.map_map, h, List.map_flatMap, sum_flatMap']
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]

theorem leafCount_push_eq :
    Bus.leafCount (inst L tabs hτ) 0 = ((List.finRange tabs.length).map fun j ↦
      ((tabs.get j).reads.length + (tabs.get j).seeds.length) * 2 ^ (tabs.get j).τ).sum := by
  rw [leafCount_side L tabs hτ 0 .push rfl]
  exact congrArg List.sum (List.map_congr_left fun j _ ↦ by rw [← flushes_push_length])

theorem leafCount_pull_eq :
    Bus.leafCount (inst L tabs hτ) 1 = Bus.leafCount (inst L tabs hτ) 0 := by
  rw [leafCount_side L tabs hτ 1 .pull rfl, leafCount_push_eq]
  exact congrArg List.sum (List.map_congr_left fun j _ ↦ by rw [← flushes_pull_length])

theorem leafCount_count_le :
    Bus.leafCount (inst L tabs hτ) 2 ≤ Bus.leafCount (inst L tabs hτ) 0 := by
  have h := Bus.countSources_map_κ (inst L tabs hτ)
  rw [leafCount_push_eq, Bus.leafCount]
  change ((Bus.countSources (inst L tabs hτ)).map _).sum ≤ _
  rw [two_pow_comp, ← List.map_map, h, List.map_flatMap, sum_flatMap']
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul]
  exact List.sum_le_sum fun j _ ↦ Nat.mul_le_mul_right _ (counts_length_le _)

theorem leafCount_push_le :
    Bus.leafCount (inst L tabs hτ) 0 ≤ 2 ^ (inst L tabs hτ).μBus := by
  rw [← Bus.blocks_total]; exact Bus.push_fits _

/-- **The lvm instance meets leanVM's bus side conditions** when every constrained table reads or
seeds. -/
theorem inst_conditions (hcon : ∀ t ∈ tabs, t.cons ≠ [] → t.reads ≠ [] ∨ t.seeds ≠ []) :
    Bus.Conditions (inst L tabs hτ) where
  one_le_d := by show 1 ≤ 2; norm_num
  constrained j hj := by
    have hc : (tabs.get j).cons ≠ [] := by
      intro h; apply hj; show List.map _ (tabs.get j).cons = []; rw [h]; rfl
    have hpos : 1 ≤ (tabs.get j).reads.length + (tabs.get j).seeds.length := by
      rcases hcon _ (List.get_mem _ _) hc with h | h
      · have := List.length_pos_of_ne_nil h; omega
      · have := List.length_pos_of_ne_nil h; omega
    have h1 : 2 ^ (tabs.get j).τ ≤ Bus.leafCount (inst L tabs hτ) 0 := by
      rw [leafCount_push_eq]
      refine le_trans ?_ (List.le_sum_of_mem (List.mem_map_of_mem (List.mem_finRange j)))
      exact Nat.le_mul_of_pos_left _ hpos
    have h2 := h1.trans (leafCount_push_le L tabs hτ)
    exact (Nat.pow_le_pow_iff_right one_lt_two).mp h2
  pull_fits := (leafCount_pull_eq L tabs hτ).trans_le (leafCount_push_le L tabs hτ)
  count_fits := (leafCount_count_le L tabs hτ).trans (leafCount_push_le L tabs hτ)
  separator j f r r' := by
    have key : ∀ e ∈ (tabs.get j).flushes, ∃ c : K, e.2[0] = MvPolynomial.C c := by
      intro e he
      simp only [Tab.flushes, List.mem_append, List.mem_map] at he
      rcases he with (((⟨x, -, rfl⟩ | ⟨x, -, rfl⟩) | ⟨x, -, rfl⟩) | ⟨x, -, rfl⟩) <;>
        exact ⟨FK.toBF64 x.1.sep, by simp [Tab.readVec, Tab.bumpVec, Tab.seedVec, Tab.finVec, Key.vec]⟩
    obtain ⟨c, hc⟩ := key ((tabs.get j).flushes[f.1]'f.isLt) (List.getElem_mem _)
    simp only [Bus.flushPolys, Fin.getElem_fin]
    rw [hc]
    simp

/-- The lvm instance has no boundary column: the bus phase reads no value. -/
theorem busClaims_zero : (inst L tabs hτ).busClaims = 0 := by
  simp [M3Instance.busClaims, M3Instance.boundaryColumns, inst]

end Conditions

/-! ## The bus phase on the wire -/

/-- What the lvm bus phase read: the fingerprint challenges, the GKR point and values. -/
structure LBus where
  /-- The four `α`. -/
  alphas : List E
  /-- `β`. -/
  beta : E
  /-- The grand product's point. -/
  point : List E
  /-- The three trees' values there. -/
  values : List E

/-- **The lvm bus phase**: `(α, β)`, the grand product at depth `μ`, the count root nonzero, then one
prover scalar that must be zero. The instance has no boundary value to read; this scalar stands
where leanVM reads them, so that the grand product's last challenges and the table sumcheck's `ξ`
are separated by a prover move as in leanVM (the lead calculus of `gkrSpec` ends at allowance `0`).
Cost: one `E` scalar. -/
def lvmBusProg (μ : ℕ) : VerifierProgram LBus :=
  abProg.bind fun ab ↦ (verifyGkrGrandProducts μ).bind fun r ↦
    (VerifierProgram.require (r.1 ≠ 0)).bind fun _ ↦ VerifierProgram.readScalar.bind fun z ↦
      (VerifierProgram.require (z = 0)).bind fun _ ↦ VerifierProgram.ret ⟨ab.1, ab.2, r.2.1, r.2.2⟩

section Bus

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt)

/-- The protocol's statement after the bus phase, on what was read (no boundary value). -/
noncomputable def lbusStmt (b : LBus) (vals : Vector E I.busClaims) : I.Stmt × BusOut I :=
  (input, Bus.busOut hI (layerStmtOf (input, (toAlpha b.alphas, b.beta)) I.μBus ⟨b.values, b.point⟩)
    vals)

/-- **The bus seam on the wire**: the protocol's output at what was read is doomed. -/
def LBusAt (vals : Vector E I.busClaims) (b : LBus) (h : List Ev) : Prop :=
  b.point.length = I.μBus ∧ b.values.length = 3 ∧ HDoom cands (Seam.bus I) (lbusStmt I hI input b vals) h

variable {εmax : ℝ≥0∞}

/-- **The lvm bus phase, specified** (leanVM's `busThenSpec` without the framework blocks): from
the commitment's doom to doom on the bus seam at the protocol's output on what was read; `Lk` is the
follower's lead. -/
noncomputable def lvmBusSpec (vals : Vector E I.busClaims) {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite)
    (hcard : ∀ W, (cands W).ncard ≤ L₀) (hμ : I.μBus ≠ 0)
    (hab : abError I L₀ < 1) (he : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {Lk : ℝ≥0∞} (hLk : Lk ≤ εmax) :
    Spec (lvmBusProg I.μBus) (HDoom cands (Seam.commit I) input) (LBusAt I hI cands input vals) εmax
      (abError I L₀ + 0) Lk :=
  (abSpec I cands input hI hfin hcard hab (T := 0)).bind' fun ab ↦
    (gkrSpec I cands (input, (toAlpha ab.1, ab.2)) hI hfin hcard hμ he hT hlam).bind' fun r ↦
      let P : List Ev → Prop := fun h ↦ r.2.1.length = I.μBus ∧ r.2.2.length = 3 ∧
          HDoom cands (Seam.bus I) (lbusStmt I hI input ⟨ab.1, ab.2, r.2.1, r.2.2⟩ vals) h
      (Spec.require (T := 0) (Post := fun _ h ↦ P h)
        fun _ hp hc ↦ by
          obtain ⟨hl, hv, W, hW, hR⟩ := hp.resolve_left hc
          exact ⟨hl, hv, W, hW, values_keep I hI hR vals⟩).bind' fun _ ↦
      (Spec.readE (Post := fun _ h ↦ P h)
        (fun _ _ hp ↦ ⟨hp.1, hp.2.1, hp.2.2.append _⟩) hLk).bind' fun _ ↦
      (Spec.require (Post := fun _ h ↦ P h) fun _ hp _ ↦ hp).bind' fun _ ↦
      (Spec.ret (Post := LBusAt I hI cands input vals) _).mono (fun _ hp ↦ hp)
        (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Bus

/-! ## The table phase over any bus result (leanVM `TablePhase`, generalised) -/

section Table

open LeanVM.Protocol.TableSumcheck

variable (tables : List Verifier.Table) (I : M3Instance) (hI : Bus.Conditions I)
  (cands : Word → Set (∀ i, TheOracle I i)) (layout : Verifier.Layout)

/-- The sumcheck's statement after its rounds, at the bus statement `s`. -/
noncomputable def tableStmtG (s : I.Stmt × BusOut I) (ξ : E) (ch : List E) (claim : E) :
    SumcheckRound.Stmt (Data I) E I.τmax :=
  ((s, ξ), (vecOf I.τmax ch, claim))

/-- **The program's computations are the protocol's** (leanVM `TableFid`, at any bus result `bus`
and protocol statement `s`). -/
structure TableFidG (colOf : I.ColumnId → ℕ) (s : I.Stmt × BusOut I) (bus : BusResult) : Prop where
  /-- The rounds: `max` of the heights is `τ_max`. -/
  rounds : layout.tableLogHeights.foldl max 0 = I.τmax
  /-- The target is the protocol's batched claim. -/
  target : ∀ ξ, dot (fpsOf tables ξ) bus.totals = powerBatch (claimed I s) ξ
  /-- The final check's value is the protocol's formula. -/
  formula : ∀ ξ (ch : List E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf tables layout bus ch.reverse) evs →
    (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse (rowsOf tables layout bus ch.reverse)
      evs 0 0 []).1 = formula I (s, ξ) (vecOf I.τmax ch).reverse (vecOf I.tableColumns evs.flatten)
  /-- The protocol's output claims are among the program's. -/
  claims : ∀ ξ (ch : List E) (claim : E) (evs : List (List E)), ch.length = I.τmax →
    ReadShape (rowsOf tables layout bus ch.reverse) evs →
    ∀ c ∈ (tableOut I (tableStmtG I s ξ ch claim) (vecOf I.tableColumns evs.flatten)).2.columns.toList,
      (⟨colOf c.col, c.point.toList, c.value⟩ : Verifier.ColumnClaim) ∈
        bus.claims ++ (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
          (rowsOf tables layout bus ch.reverse) evs 0 0 []).2

variable {εmax : ℝ≥0∞}

/-- What the rounds and final values give (leanVM `TableSumcheckPost`, generalised). -/
def TableSumcheckPostG (s : I.Stmt × BusOut I) (bus : BusResult) (ξ : E)
    (claims' : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∃ ch claim evs, ReadShape (rowsOf tables layout bus ch.reverse) evs ∧ ch.length = I.τmax ∧
    claims' = (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse
      (rowsOf tables layout bus ch.reverse) evs 0 0 []).2 ∧
    HDoom cands (Seam.table I) (tableOut I (tableStmtG I s ξ ch claim)
      (vecOf I.tableColumns evs.flatten)) h

/-- **The table sumcheck's rounds and final values** (leanVM `tableSumcheckSpec`, generalised). -/
noncomputable def tableSumcheckSpecG (colOf : I.ColumnId → ℕ) (s : I.Stmt × BusOut I)
    (bus : BusResult) (fid : TableFidG tables I layout colOf s bus)
    (htw : ∀ t ∈ tables, 0 < t.width) (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) (ξ : E) :
    Spec (Verifier.tableSumcheckClaims tables layout.tableLogHeights bus.forms (cpsOf tables ξ)
        (fpsOf tables ξ) bus.point (dot (fpsOf tables ξ) bus.totals))
      (HDoom cands (SumcheckRound.rel (tableFamily I) 0)
        ((s, ξ), (#v[], dot (fpsOf tables ξ) bus.totals)))
      (TableSumcheckPostG tables I cands layout s bus ξ) εmax
      (sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T) T :=
  let n := layout.tableLogHeights.foldl max 0
  (wireSumcheckSpec (T := T) (tableFamily I) cands (tableFamily_consistent I hd)
    (tableFamily_sound I) hfin hcard (by norm_num) he (s, ξ) (List.replicate n none) 0 #v[]
    (dot (fpsOf tables ξ) bus.totals) (by simp [n, fid.rounds]) (fun k hk ↦ by
      have hk' : k < I.τmax := by simpa [n, fid.rounds] using hk
      simp [tableFamily, Sumcheck.familyInv, Sumcheck.domain, Sumcheck.unitWeights, wireDomain,
        hk'])).bind' fun ⟨ch, claim⟩ ↦
    let P := SumcheckPost (tableFamily I) cands (s, ξ) I.τmax #v[] (ch, claim)
    let rows := rowsOf tables layout bus ch.reverse
    ((tableTermsSpec tables hT P (fun _ _ hp ↦ ⟨hp.1, hp.2.append _⟩) (cpsOf tables ξ) (fpsOf tables ξ)
      ch.reverse rows (rowsOf_width_pos tables htw layout bus _) 0 0 []).mono (fun _ hp ↦ hp)
      (fun _ _ hp ↦ hp) le_rfl (rowsLead_le _ _) le_rfl).bind' fun ⟨final, claims⟩ ↦
    (Spec.require (c := final = claim) (Post := fun _ h ↦ ∃ evs, ReadShape rows evs ∧
        ch.length = I.τmax ∧
        claims = (refTableTerms tables (cpsOf tables ξ) (fpsOf tables ξ) ch.reverse rows evs 0 0 []).2 ∧
        HDoom cands (Seam.table I) (tableOut I (tableStmtG I s ξ ch claim)
          (vecOf I.tableColumns evs.flatten)) h)
      (fun _ hp hc ↦ by
        obtain ⟨evs, hs, heq, hlen, W, hW, hR⟩ := hp
        have hl : ch.length = I.τmax := by simpa using hlen
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        simp only at hfst hsnd
        refine ⟨evs, hs, hl, hsnd, W, hW, finalValues_keep I hR _ ?_⟩
        rw [Sumcheck.finalCheck, decide_eq_true_eq]
        show formula I (s, ξ) (vecOf I.τmax ch).reverse (vecOf I.tableColumns evs.flatten) = claim
        rw [← fid.formula ξ ch evs hl hs, ← hfst, hc])).bind' fun _ ↦
    (Spec.ret (Post := TableSumcheckPostG tables I cands layout s bus ξ) claims).mono
      (fun _ ⟨evs, hs, hl, hc, hD⟩ ↦ ⟨ch, claim, evs, hs, hl, hc, hD⟩) (fun _ _ h ↦ h) le_rfl
      le_rfl le_rfl

open Classical in
/-- **The table sumcheck** (leanVM `tablePhaseSpec`, generalised): from doom on the bus seam at `s`
to the table seam on the wire. `ξ` is charged `L₀ · (B + 2) / |E|`, each round `L₀ · 3 / |E|`. -/
noncomputable def tablePhaseSpecG (colOf : I.ColumnId → ℕ) (s : I.Stmt × BusOut I) (bus : BusResult)
    (fid : TableFidG tables I layout colOf s bus) (htw : ∀ t ∈ tables, 0 < t.width)
    (hd : I.d ≤ 2) {L₀ : ℕ}
    (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀) {T : ℝ≥0∞}
    (he : roundError L₀ 3 + T ≤ εmax) (hT : T ≤ εmax) :
    Spec (tablePhaseClaims tables layout bus) (HDoom cands (Seam.bus I) s)
      (TablePost I cands s.1 colOf) εmax
      (xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none) T)
      T :=
  (Spec.sampleE (xiError I L₀) (Post := fun ξ h ↦ HDoom cands
      (SumcheckRound.rel (tableFamily I) 0)
      ((s, ξ), (#v[], dot (fpsOf tables ξ) bus.totals)) h)
    (fun h₀ hp ↦ by
      obtain ⟨W, hW, hR⟩ := hp
      refine le_trans ?_ (xi_escape I (hfin W) (hcard W) s hR)
      gcongr with ξ _
      intro hD
      refine ⟨W, firstWord_append hW _, ?_⟩
      rw [fid.target ξ, tableFamily_rel_zero]
      exact hD)).bind' fun ξ ↦
  (tableSumcheckSpecG tables I cands layout colOf s bus fid htw hd hfin hcard he hT ξ).bind'
    fun tableClaims ↦
  (Spec.ret (Post := TablePost I cands s.1 colOf) (bus.claims ++ tableClaims)).mono
    (fun _ hp ↦ by
      obtain ⟨ch, claim, evs, hs, hl, rfl, W, hW, hR⟩ := hp
      exact ⟨W, _, hW, hR, rfl, fid.claims ξ ch claim evs hl hs, _, _, rfl⟩) (fun _ _ h ↦ h)
      le_rfl le_rfl le_rfl

end Table

/-! ## The bus phase, then the table sumcheck -/

section Compose

variable (tables : List Verifier.Table) (I : M3Instance) (hI : Bus.Conditions I)
  (cands : Word → Set (∀ i, TheOracle I i)) (input : I.Stmt) (layout : Verifier.Layout)
  {εmax : ℝ≥0∞}

/-- **The lvm bus phase, then the table sumcheck**, on the wire: `busRes` computes the bus result
(forms, totals, claims) from what the bus phase read. -/
def lvmBusTableProg (μ : ℕ) (busRes : LBus → BusResult) : VerifierProgram (List Verifier.ColumnClaim) :=
  (lvmBusProg μ).bind fun b ↦ tablePhaseClaims tables layout (busRes b)

/-- **`M3Holds` from the phase specs** (leanVM's `busTableSpec` for the lvm instance): from the
commitment's doom (no candidate satisfies `M3Holds`) to the table seam on the wire, given, for every
read of the right shape, the identities between the program's computations and the protocol's
(`TableFidG`, as leanVM's `busTableSpec` takes `TableFid`). Errors: `abError L₀ + 0` lead (the
fingerprint challenges), `roundError L₀ 4`, `lambdaError L₀` in the grand product, `xiError L₀`
and `roundError L₀ 3` per round in the table sumcheck. -/
noncomputable def lvmBusTableSpec (colOf : I.ColumnId → ℕ) (vals : Vector E I.busClaims)
    (busRes : LBus → BusResult)
    (fid : ∀ b : LBus, b.point.length = I.μBus → b.values.length = 3 →
      TableFidG tables I layout colOf (lbusStmt I hI input b vals) (busRes b))
    (htw : ∀ t ∈ tables, 0 < t.width) (hd : I.d ≤ 2)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : I.μBus ≠ 0) (hab : abError I L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none)
      T ≤ εmax) :
    Spec (lvmBusTableProg tables layout I.μBus busRes) (HDoom cands (Seam.commit I) input)
      (TablePost I cands input colOf) εmax (abError I L₀ + 0) T :=
  (lvmBusSpec I hI cands input vals hfin hcard hμ hab he4 hT hlam hxi).bind
    (fun b ↦ if hb : b.point.length = I.μBus ∧ b.values.length = 3 then
      (tablePhaseSpecG tables I cands layout colOf (lbusStmt I hI input b vals) (busRes b)
        (fid b hb.1 hb.2) htw hd hfin hcard he3 hTf).mono
        (fun _ hp ↦ hp.2.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else specOfFalse fun _ hp ↦ hb ⟨hp.1, hp.2.1⟩)

end Compose

/-! ## The per-group errors (BLUEPRINT §3.2), unique decoding (`L₀ = 1`) -/

section Errors

theorem natDivCard_le {a b : ℕ} (h : a ≤ b) :
    ((((a : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞)) ≤ (((b : ℝ≥0) / (Nat.card E : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  gcongr

/-- **Bus fingerprint**: `abError ≤ 2^24/|E|` (§3.2's row "bus fingerprint …") when `μ_bus ≤ 22`
(P20: 21; P8: 20). -/
theorem abError_le (I : M3Instance) (hμ : I.μBus ≤ 22) :
    abError I 1 ≤ ((overE (2 ^ 24) : ℝ≥0) : ℝ≥0∞) := by
  unfold abError
  rw [Nat.cast_one, one_mul]
  have : 4 * 2 ^ I.μBus ≤ 2 ^ 24 := by
    calc 4 * 2 ^ I.μBus ≤ 4 * 2 ^ 22 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hμ)
      _ = 2 ^ 24 := by norm_num
  unfold overE
  rw [← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le this

/-- **Table sumcheck batching**: `xiError ≤ 2^24/|E|` when the tables have at most `2^24 − 2`
constraints. -/
theorem xiError_le (I : M3Instance) (hB : I.B + 2 ≤ 2 ^ 24) :
    xiError I 1 ≤ ((overE (2 ^ 24) : ℝ≥0) : ℝ≥0∞) := by
  unfold xiError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le (by omega)

/-- **Sumcheck rounds** (grand product degree 3 with `4` coefficients, table sumcheck degree 3) and the
grand product's combiners: at most `4/|E|`. -/
theorem roundError_le (d : ℕ) (hd : d ≤ 4) :
    roundError 1 d ≤ ((overE 4 : ℝ≥0) : ℝ≥0∞) := by
  unfold roundError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le hd

theorem lambdaError_le : lambdaError 1 ≤ ((overE 4 : ℝ≥0) : ℝ≥0∞) := by
  unfold lambdaError overE
  rw [Nat.cast_one, one_mul, ← Nat.card_eq_fintype_card]
  exact_mod_cast natDivCard_le (by norm_num)

end Errors

end Lvm.M3
