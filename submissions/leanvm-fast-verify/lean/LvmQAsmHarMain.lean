-- New for lvm (HAR-TOP): the node-level `harith` (BLUEPRINT §12.6): Q_arith's rows and assertions (gate on)
-- give `decideCore = true` and `accOutOf = accIn x` on the child's stream, composed from the phase families'
-- replay lemmas (`busG_replays`, `tabG_replays`, `qacc_replays`, `p47_at`, the claim equations, `openPh_run`)
-- through `core_of_phases`. Generic in the configuration `C` and the placement record `D`.
import LvmQAsmHarP47
import LvmQAsmHarShape
import LvmQAsmHarIn

/-!
# `harith_core`

**`harith_core C D G …`**: wherever `qarith' C D = phases47 C >>= qarithT C D` holds and asserts at `p2`
(the node flag on, `PUB` lane 0 = 1), and the stream cells bind `Σ'` (`Streamed M Σ' T`), the child's
`decideCore` accepts and its folded accumulator is the current proof's `acc_in` (`accC M (pbB C)`, its
`PUB` cells), for `M3.real C.p (tabs C G D)` with any cache `G` (the circuit reads only the tables'
shapes, `tabs_shape`).

Hypotheses: the static facts of `(C, D)` in `HarStatic` (positions, lane bounds, glue `SLok` checks,
WHIR layouts; decidable on the final record), the memory facts (`Streamed`, the gate, `PUB`'s `vk`
lanes, `SBits`/`NBits`, the position cells `PosOk`), `1 ≤ n'`, the end of `Σ'`, and the claims'
well-formedness `ClaimsWF` on the claim list Q_arith builds (`qarithCs`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- **Q_arith on the record `D`** (`qarith C = qarith' C (dataOf C)`). -/
def qarith' (C : QCfg) (D : QData) : BM Unit := phases47 C >>= qarithT C D

theorem qarith_eq' (C : QCfg) : qarith C = qarith' C (dataOf C) := rfl

/-! ## Helpers -/

/-- A `Replays` fact and the gadget's `Ok` give a `PhaseAt` fact, the value read off `R`. -/
theorem phaseAt_of {α β : Type} {c : Ctx} {M : Mem} {sig : ByteArray} {F : DM α} {g : BM β} {ptr : Ptr}
    {P P' : Nat} {R : α → β → Prop} {v : α} (h : Replays c M sig F g ptr P P' R)
    (hok : Lvm.QSig.Ok c M g ptr) (hv : ∀ a, R a (g ptr).1 → a = v) : PhaseAt F sig P P' v :=
  fun s hs hsok => by
    obtain ⟨h1, h2, h3⟩ := h hok s hs hsok
    exact ⟨hv _ h3, h1, h2⟩

/-- The `E` constant `k'` from any cell `x` (`x + 1·x + k'`). -/
theorem constE_val {c : Ctx} {M : Mem} {k' : FK} {x : Cell} {p : Ptr}
    (h : SegsHold c M p (const .E k' x p).2) : (const .E k' x p).1.val M = FE.ofK k' := by
  have e := lin_spec (c := c) (M := M) (p := p) (τ := .E) (k := 1) (k' := k') (a := x) (b := x) h
  show (lin .E 1 k' x x p).1.val M = _
  rw [e, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add]

theorem ldEs_fst (st : Nat) : ∀ (n a : Nat) (p : Ptr),
    (Lvm.Har.ldEs a st n p).1 = (List.range n).map fun i => ec (p.e + i)
  | 0, _, _ => rfl
  | n + 1, a, p => by
    simp only [Lvm.Har.ldEs, bind_apply, pure_apply]
    rw [ldE_adv, ldEs_fst st n (a + st) ⟨p.k, p.e + 1⟩, ldE_apply, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    exact List.map_congr_left fun i _ => by simp only [Function.comp_apply]; congr 1; omega

/-! ## Phase 2 (bus) -/

/-- The bus phase's value: the output cells' values, one zero leaf-decomposition scalar. -/
def busV (M : Mem) (b : BusC) : List FE × FE × FE × List FE × List FE × List FE :=
  (vs M b.al, b.be.val M, b.cnt.val M, vs M b.pt, vs M b.vals, [0])

theorem busR_eq {M : Mem} {res : List FE × FE × FE × List FE × List FE × List FE} {b : BusC}
    (h : BusR M res b) : res = busV M b ∧ (vs M b.vals).length = 3 := by
  obtain ⟨a, b', c', d, e, f⟩ := res
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6
  exact ⟨rfl, h7⟩

theorem busG_fst (p : Params) (z o g : Cell) (P : Nat) (ptr : Ptr) :
    (busG p z o g P ptr).1.al = (List.range busBits).map (fun i => ec (ptr.e + i)) ∧
      ∃ d : PD, (busG p z o g P ptr).1.pt = d.cells := by
  simp only [busG, bind_apply, pure_apply]
  exact ⟨ldEs_fst _ _ _ _, _, rfl⟩

/-! ## Phase 3 (tables) -/

theorem evLoads_length : ∀ (ws : List Nat) (a : Nat) (p : Ptr), (evLoads a ws p).1.length = ws.length
  | [], _, _ => rfl
  | w :: ws, a, p => by
    simp only [evLoads, bind_apply, pure_apply, List.length_cons]
    rw [evLoads_length ws]

/-- **The table gadget's output**: per table its point cells (the rounds' challenge cells, reversed,
the first `τ`) and its evaluation cells. -/
theorem tabG_fst (S : List TShape) (R P : Nat) (z o g : Cell) (bc : BusC) (ptr : Ptr) :
    ∃ (qe : Nat) (evs : List (List Cell)), evs.length = S.length ∧
      (tabG S R P z o g bc ptr).1 =
        (S.zip evs).map fun x => (((List.range R).map (chC qe)).reverse.take x.1.τ, x.2) := by
  simp only [tabG, bind_apply, pure_apply]
  exact ⟨_, _, by rw [evLoads_length]; simp, rfl⟩

/-- The longest point's length (`tablePointC`) is the largest length. -/
theorem tablePointC_len : ∀ (l : List (List Cell × List Cell)) (r : List Cell),
    (l.foldl (fun r e => if r.length < e.1.length then e.1 else r) r).length =
      (l.map (·.1.length)).foldl max r.length
  | [], _ => rfl
  | e :: l, r => by
    simp only [List.foldl_cons, List.map_cons]
    rw [tablePointC_len l]
    congr 1
    split_ifs with h <;> omega

theorem foldl_max_le : ∀ (l : List Nat) (a R : Nat), a ≤ R → (∀ x ∈ l, x ≤ R) → l.foldl max a ≤ R
  | [], _, _, ha, _ => ha
  | x :: l, a, R, ha, hl => by
    simp only [List.foldl_cons]
    exact foldl_max_le l _ R (max_le ha (hl x (List.mem_cons_self ..)))
      fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- What `Q_acc` needs of the table gadget's output: `PUB`'s point cells are `E` cells, `10` of them; the
longest point has `tableRounds` cells. -/
theorem tab_facts (S : List TShape) (R P : Nat) (z o g : Cell) (bc : BusC) (ptr : Ptr) (pt : Nat)
    (hpt : pt < S.length) (hτ : (S.map (·.τ)).getD pt 0 = 10) (h10 : 10 ≤ R)
    (hmax : ∃ s ∈ S, R ≤ s.τ) :
    (∀ x ∈ ((tabG S R P z o g bc ptr).1.getD pt default).1, x.ty = .E) ∧
    ((tabG S R P z o g bc ptr).1.getD pt default).1.length = 10 ∧
    (Lvm.QAcc.tablePointC (tabG S R P z o g bc ptr).1).length = R := by
  obtain ⟨qe, evs, hl, he⟩ := tabG_fst S R P z o g bc ptr
  rw [he]
  have hz : (S.zip evs).length = S.length := by simp [hl]
  have hg : ((S.zip evs).map fun x => (((List.range R).map (chC qe)).reverse.take x.1.τ, x.2)).getD pt
      default = (((List.range R).map (chC qe)).reverse.take S[pt].τ, evs.getD pt default) := by
    rw [List.getD_eq_getElem _ _ (by simp [hz, hpt]), List.getElem_map, List.getElem_zip,
      List.getD_eq_getElem _ _ (by omega)]
  have hτ' : S[pt].τ = 10 := by
    rw [← hτ, List.getD_eq_getElem _ _ (by simpa using hpt), List.getElem_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp (List.mem_of_mem_take hx))
    rfl
  · rw [hg, hτ']
    simp only [List.length_take, List.length_reverse, List.length_map, List.length_range]
    omega
  · unfold Lvm.QAcc.tablePointC
    rw [tablePointC_len]
    have e : ((S.zip evs).map fun x => (((List.range R).map (chC qe)).reverse.take x.1.τ, x.2)).map
        (·.1.length) = S.map fun s => min s.τ R := by
      rw [List.map_map]
      have h1 : (S.zip evs).map Prod.fst = S := List.map_fst_zip (by omega)
      conv_rhs => rw [← h1]
      rw [List.map_map]
      refine List.map_congr_left fun x _ => ?_
      simp
    rw [e]
    apply le_antisymm
    · exact foldl_max_le _ _ _ (Nat.zero_le _) fun x hx => by
        obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx; exact Nat.min_le_right _ _
    · obtain ⟨s, hs, hR⟩ := hmax
      have := (le_foldl_max (S.map fun s => min s.τ R) ([] : List Cell).length).2 (min s.τ R)
        (List.mem_map.mpr ⟨s, hs, rfl⟩)
      omega

/-! ## `fixCols`' cells depend only on the shapes -/

theorem fixColsR_idx (ts : List M3.Tab) (pubTab : Nat) :
    (M3.fixColsR ts pubTab).map (fun c => (c.tab, c.col)) = fixIdx (ts.map M3.Tab.shape) pubTab := by
  unfold M3.fixColsR fixIdx
  rw [List.map_flatMap, List.zipIdx_map, List.flatMap_map]
  refine List.flatMap_congr fun x _ => ?_
  rcases x with ⟨t, j⟩
  rw [List.map_filterMap]
  simp only [M3.Tab.shape, Prod.map, id_eq]
  rw [List.zipIdx_map, List.filterMap_map]
  refine List.filterMap_congr fun ci _ => ?_
  rcases ci with ⟨col, i⟩
  cases col with
  | com rec off => rfl
  | fix f ev =>
    simp only [colKind, Function.comp_apply, Prod.map, id_eq]
    split_ifs <;> rfl

/-- `fixCellsR` on the shapes' indices. -/
theorem fixCellsR_idx (ts : List M3.Tab) (pubTab : Nat) (evc : List (List Cell × List Cell)) (zc : Cell) :
    Lvm.QAcc.fixCellsR ts pubTab evc zc =
      (fixIdx (ts.map M3.Tab.shape) pubTab).map fun ji => (evc.getD ji.1 default).2.getD ji.2 zc := by
  rw [← fixColsR_idx, List.map_map]
  rfl

theorem fixCellsR_shape (ts ts' : List M3.Tab) (pubTab : Nat) (evc : List (List Cell × List Cell)) (zc : Cell)
    (h : ts.map M3.Tab.shape = ts'.map M3.Tab.shape) :
    Lvm.QAcc.fixCellsR ts pubTab evc zc = Lvm.QAcc.fixCellsR ts' pubTab evc zc := by
  rw [fixCellsR_idx, fixCellsR_idx, h]

/-- A public array's shape does not depend on its values. -/
theorem pubArr_shape (τ base stride : Nat) (val fin : Bool × Nat) (vals vals' : List FK) :
    (M3.pubArr τ base stride val fin vals).tab.shape = (M3.pubArr τ base stride val fin vals').tab.shape :=
  inArr_shape _ _ rfl rfl rfl rfl rfl rfl rfl

/-- `arrsS` has `arrs`' shapes. -/
theorem arrsS_shape (C : QCfg) (D : QData) (P : Pub) :
    (arrsS C D).map (·.tab.shape) = (arrs C D P).map (·.tab.shape) := by
  unfold arrsS arrs
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [pubArr_shape _ _ _ _ _ [] (hdrOfPub P), pubArr_shape _ _ _ _ _ [] (Lvm.QLink.qltData C.p (lay C))]

/-- **The table shapes the circuit is built from are those of `tabs C G D pub`** (any cache, any `PUB`). -/
theorem shapesOf_eq (C : QCfg) (D : QData) (G : M3.PG) (pub : Pub) :
    shapesOf C D = (M3.sumcheckTabs (tabs C G D pub)).map M3.Tab.shape := by
  rw [shapesOf, sumcheckTabs_shape, sumcheckTabs_shape, tabsS, tabs,
    lvmTabsC_shape G0 G (plOf D) D.groups (arrsS C D) (arrs C D pub) (aux C D) (arrsS_shape C D pub)]

/-! ## The static facts -/

/-- The lane of phase 3b's start (`accInOf`'s `L`). -/
def accL (C : QCfg) (D : QData) : Nat := tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) / 8

/-- The lane of phase 3b's zero-scalar position (`AccIn.z0`); phase 4 starts at `8 · accZ0 + 24`. -/
def accZ0 (C : QCfg) (D : QData) : Nat := accL C D + 9 * C.p.accLog + 3 * (accVars + 1) + 9

/-- **The static facts of `(C, D)`** that `harith_core` uses (decidable on the final record; `T` the
stream's lanes, `P4 … P8` the starts of phases 4–8). -/
structure HarStatic (C : QCfg) (D : QData) (T P4 P5 P6 P7 P8 : Nat) : Prop where
  /-- Phases 4–7 (`p47_at`): positions, sizes, lane bounds, the links' glue checks. -/
  pos47 : P47Pos C.p P4 P5 P6 P7 P8
  hn : 4 ≤ C.p.logN
  hk : 4 ≤ C.p.ksLog
  hr : C.p.recRowsLog < C.p.ksLog
  hlay : layOk (C.p.logN - 4) = true
  hlayk : layOk (C.p.ksLog - 4) = true
  hq : 5 ≤ aLane C.p 2
  hqk : 5 ≤ aLane C.p 6
  hTg : gkrEnd (C.p.logN - 4) (aLane C.p 2) + 48 ≤ T
  hTgk : gkrEnd (C.p.ksLog - 4) (aLane C.p 6) + 48 ≤ T
  hTr : aLane C.p 0 + 9 * C.p.logN + 2 < T
  hTv : aLane C.p 1 + 3 * 25 + 2 < T
  hTrk : aLane C.p 4 + 9 * C.p.ksLog + 2 < T
  hTvk : aLane C.p 5 + 3 * 25 + 2 < T
  hD : C.p.logN ≤ 2 ^ clog2 C.p.logN
  hDk : C.p.ksLog ≤ 2 ^ clog2 C.p.ksLog
  hTl : chQC C.p.logN (aLane C.p 3) + 240 ≤ T
  hTlk : ksQV C.p.ksLog (aLane C.p 7) + 3 * 4 + 3 ≤ T
  hTlk' : aLane C.p 7 + 9 * (C.p.ksLog + laneBits) + 15 * C.p.ksLog + 12 ≤ T
  okA : SLok (chGlueA C.p.logN (aLane C.p 3)) = true
  okB : ∀ oA sh : LoopOut, SLok (chGlueB (chQB C.p.logN (aLane C.p 3)) (rhoC oA C.p.logN) (rho'C sh C.p.logN)
    (eZC oA C.p.logN) (sh.cell 5 (C.p.logN - 1))) = true
  okC : ∀ oA sh sc2 oB : LoopOut, SLok (chGlueC (chQC C.p.logN (aLane C.p 3)) [sc2.cell 2 0, sc2.cell 2 1]
    (eLC oA C.p.logN) (eZC oA C.p.logN) (rho'C sh C.p.logN) (oA.cell (2 * C.p.logN + 163) 0)
    (oB.cell (8 * C.p.logN + 123) 0) (sc2.cell 5 1) (kc (pbB C))) = true
  hB : 1 ≤ spongeBlocks C.p
  hB2 : spongeBlocks C.p ≤ 2 ^ C.p.ksLog
  hK : 2 ^ C.p.recRowsLog + 431 ≤ 2 ^ C.p.ksLog
  okE : ∀ sh : LoopOut, SLok (ksGlueE C.p.ksLog (aLane C.p 7) (ksQV C.p.ksLog (aLane C.p 7))
    (spongeBlocks C.p - 1) (2 ^ C.p.recRowsLog + 399 + 31) (2 ^ C.p.recRowsLog + 399) (rho'C sh C.p.ksLog)
    (sh.cell 2 C.p.recRowsLog) (sh.cell 5 (C.p.ksLog - 1)) (kc (pbB C))) = true
  /-- Phase 2 (`busG_replays`). -/
  hld : C.p.leafdecReads = 1
  hbP : busPos C.p % 8 = 0
  hbT : busEnd C.p (busPos C.p) + 40 ≤ 8 * T
  /-- Phase 3 (`tabG_replays`): position, lanes, `PUB`'s table, the tallest table. -/
  htP : tabPos C.p % 8 = 0
  htT : tabEnd (shapesOf C D) C.p.tableRounds (tabPos C.p) + 40 ≤ 8 * T
  hpubT : C.p.pubTab < (shapesOf C D).length
  hpubτ : ((shapesOf C D).map (·.τ)).getD C.p.pubTab 0 = 10
  h10 : 10 ≤ C.p.tableRounds
  hRmax : ∃ s ∈ shapesOf C D, C.p.tableRounds ≤ s.τ
  /-- Phase 3b (`qacc_replays`). -/
  hRacc : C.p.tableRounds ≤ accVars
  hdk1 : 1 ≤ C.p.accLog
  hnf : (fixIdx (shapesOf C D) C.p.pubTab).length ≤ 2 ^ C.p.accLog
  hzL : accZ0 C D + 5 + 2 < T
  hH : 11 + pubLanes ≤ T
  hP4 : 8 * accZ0 C D + 24 = P4
  /-- The claims (`chClaims_val`). -/
  hT29 : 29 ≤ T
  hlog : C.p.logN ≤ 64
  /-- Phases 8–9 (`openPh_run`): the layouts, the start. -/
  hlr : LayOk (cfgRec C.p (posBase C)) T = true
  hlm : LayOk (cfgMain C.p (posBase C)) T = true
  hP8 : P8 = 8 * openU C.p

/-! ## Phases 2, 3, 3b -/

theorem tabEnd_eight {S : List TShape} {R P : Nat} (hP : P % 8 = 0) : 8 * (tabEnd S R P / 8) = tabEnd S R P :=
  Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by simp only [tabEnd]; omega))

/-- **Phases 2, 3 and 3b as `PhaseAt` facts** from the bus, table and `Q_acc` gadgets' rows and
assertions (gate on): the values are the output cells' values, phase 3b's is the current proof's
`acc_in` (`accC M (pbB C)`); the bus flag holds. -/
theorem p23_at (C : QCfg) (D : QData) (G : M3.PG) (vk cL : Vector UInt8 32) {c : Ctx} {M : Mem}
    {sig : ByteArray} {T P4 P5 P6 P7 P8 : Nat} (hst : HarStatic C D T P4 P5 P6 P7 P8)
    (hS : Streamed M sig T) (hg : M.k (pbB C) = 1)
    (hvk : ∀ i < 4, M.k (pbB C + 1 + i) = (digestLanes vk).getD i 0)
    {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E) (hz : z.val M = 0) (ho : one.val M = 1)
    {q2 q3 q4 : Ptr} {bus : BusC} {tab : List (List Cell × List Cell)}
    (hB : Lvm.QSig.Ok c M (busG C.p z one (kc (pbB C)) (busPos C.p)) q2)
    (hbus : (busG C.p z one (kc (pbB C)) (busPos C.p) q2).1 = bus)
    (hT : Lvm.QSig.Ok c M (tabG (shapesOf C D) C.p.tableRounds (tabPos C.p) z one (kc (pbB C)) bus) q3)
    (htab : (tabG (shapesOf C D) C.p.tableRounds (tabPos C.p) z one (kc (pbB C)) bus q3).1 = tab)
    (hA : Lvm.QSig.Ok c M (Lvm.QAcc.qacc (accInOf C (shapesOf C D) tab z)) q4) :
    PhaseAt (busPh C.p) sig (busPos C.p) (tabPos C.p) (busV M bus) ∧
    ((M3.real C.p (tabs C G D)).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pubOf vk cL sig⟩).ok = true ∧
    PhaseAt (tabPh C.p (M3.real C.p (tabs C G D)) (pubOf vk cL sig)
      ((M3.real C.p (tabs C G D)).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
        vs M bus.vals, [0], pubOf vk cL sig⟩) (vs M bus.pt))
      sig (tabPos C.p) (8 * accL C D) (Lvm.QAcc.evV M tab) ∧
    PhaseAt (accFold C.p (M3.real C.p (tabs C G D)) (pubOf vk cL sig) (Lvm.QAcc.evV M tab)) sig
      (8 * accL C D) P4 (Lvm.QAcc.accC M (pbB C)) := by
  have hgv : (kc (pbB C)).val M = 1 := gate_val C hg
  -- phase 2
  have rb := busG_replays (c := c) hS hz ho hgv C.p hst.hld hst.hbP hst.hbT q2
  have hb : PhaseAt (busPh C.p) sig (busPos C.p) (tabPos C.p) (busV M bus) :=
    phaseAt_of rb hB fun a ha => (busR_eq (hbus ▸ ha)).1
  obtain ⟨-, -, hR⟩ := rb hB ⟨busPos C.p, 0, true⟩ rfl rfl
  rw [hbus] at hR
  have h3 := (busR_eq hR).2
  have hok : ((M3.real C.p (tabs C G D)).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pubOf vk cL sig⟩).ok = ((vs M bus.vals).length == 3 && [(0 : FE)] == [0]) := rfl
  rw [hok, h3]
  refine ⟨hb, by decide, ?_⟩
  -- phase 3
  obtain ⟨hal, d, hpt⟩ := busG_fst C.p z one (kc (pbB C)) (busPos C.p) q2
  rw [hbus] at hal hpt
  obtain ⟨hE, h10, hRl⟩ := tab_facts (shapesOf C D) C.p.tableRounds (tabPos C.p) z one (kc (pbB C)) bus q3
    C.p.pubTab hst.hpubT hst.hpubτ hst.h10 hst.hRmax
  rw [htab] at hE h10 hRl
  have hS0 := shapesOf_eq C D G (pubOf vk cL sig)
  have hL : 8 * accL C D = tabEnd ((M3.sumcheckTabs (tabs C G D (pubOf vk cL sig))).map M3.Tab.shape)
      C.p.tableRounds (tabPos C.p) := by
    rw [accL, tabEnd_eight hst.htP, hS0]
  rw [hS0] at hT htab
  have rt := tabG_replays (c := c) hS hz ho hgv hzE hoE C.p (M3.real C.p (tabs C G D)) (pubOf vk cL sig)
    (tabs C G D (pubOf vk cL sig)) rfl bus (countRoot := bus.cnt.val M) (leafdec := [0]) rfl rfl rfl rfl
    (by rw [hal]; simp [vs, busBits])
    (by rw [hal]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    (by rw [hpt]; intro x hx; obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx; rfl)
    _ rfl hst.htP (by rw [← hS0]; exact hst.htT) q3
  refine ⟨hL ▸ phaseAt_of rt hT fun a ha => by rw [htab] at ha; exact ha, ?_⟩
  -- phase 3b
  have hpp : ∀ i, ((accInOf C (shapesOf C D) tab z).pp i).ty = .E := by
    intro i
    show ((tab.getD C.p.pubTab default).1.getD i (ec 0)).ty = .E
    rw [List.getD_eq_getElem?_getD]
    cases hx : (tab.getD C.p.pubTab default).1[i]? with
    | none => rfl
    | some x => exact hE x (List.mem_of_getElem? hx)
  have hfs : (M3.real C.p (tabs C G D)).fixSent (pubOf vk cL sig) (Lvm.QAcc.evV M tab) =
      (accInOf C (shapesOf C D) tab z).fx.map (Cell.val M) := by
    show M3.fixSentR (M3.sumcheckTabs (tabs C G D (pubOf vk cL sig))) C.p.pubTab (Lvm.QAcc.evV M tab) =
      ((fixIdx (shapesOf C D) C.p.pubTab).map fun ji => (tab.getD ji.1 default).2.getD ji.2 z).map (Cell.val M)
    rw [Lvm.QAcc.fixSentR_evV _ _ _ hz, fixCellsR_idx, ← hS0]
  have ra := Lvm.QAcc.qacc_replays (c := c) (A := accInOf C (shapesOf C D) tab z) (p := q4) C.p
    (M3.real C.p (tabs C G D)) vk cL (Lvm.QAcc.evV M tab) hS (by show accZ0 C D + 5 + 2 < T; exact hst.hzL) hst.hH
    hg hpp (by show pubLanes ≤ 2 ^ 10; decide) (Nat.div_le_self _ _)
    (by show (List.map _ _).length ≤ _; rw [List.length_map]; exact hst.hnf)
    (by show (Lvm.QAcc.tablePointC tab).length + C.p.accLog = accVars
        rw [hRl, Params.accLog]; have := hst.hRacc; omega)
    rfl hst.hdk1 hvk h10 hfs (Lvm.QAcc.pubCheckR_evV _ _ _ hz) (Lvm.QAcc.tablePoint_evV tab)
  have e4 : 8 * (accInOf C (shapesOf C D) tab z).z0 + 24 = P4 := hst.hP4
  exact e4 ▸ phaseAt_of ra hA fun a ha => ha

/-! ## The claims of phases 8–9 -/

theorem real_eq (p : Params) (ts : Pub → List M3.Tab) :
    M3.real p ts = M3.ofParts p (fun i => M3.busFinalR (M3.sumcheckTabs (ts i.pub)) i)
      (fun pub => (M3.sumcheckTabs (ts pub)).map M3.nativeTable)
      (fun pub => M3.tableClaimsR (M3.sumcheckTabs (ts pub)))
      (fun pub => M3.fixValsR (M3.sumcheckTabs (ts pub)) p.pubTab)
      (fun pub => M3.fixSentR (M3.sumcheckTabs (ts pub)) p.pubTab)
      (fun pub => M3.pubCheckR p.pubTab pub) := rfl

/-- **The claim list Q_arith builds is `F`'s** (`claimsOf`, phase 8's list) on the values of the phases'
cells: the table claims (phase 3's cells), `CH`'s Keccak and fixed claims, `KS`'s Keccak claims (the ring
switches as `F` computes them after the GKRs, `ringGkr_rel`), the links' claims (`F`'s link views at
`P5`, `P7`), `KS`'s output claims. -/
theorem claims_at (C : QCfg) (D : QData) (G : M3.PG) (vk cL : Vector UInt8 32) {c : Ctx} {M : Mem}
    {sig : ByteArray} {T P4 P5 P6 P7 P8 : Nat} (hst : HarStatic C D T P4 P5 P6 P7 P8)
    (hS : Streamed M sig T) (hsb : SBits M.k (bsB C)) (hnb : NBits M.k ((sigIn C).bn + 2) C.p.logN)
    (hn1 : 1 ≤ (pubOf vk cL sig).n) {p2 : Ptr} (h47 : Lvm.QSig.Ok c M (phases47 C) p2)
    {o : P47Out} (ho47 : (phases47 C p2).1 = o)
    {ze oe : Nat} (hz : M.e ze = 0) (ho : M.e oe = 1) (bus : BusOut) (hbus : bus.claims = [])
    (tab : List (List Cell × List Cell)) {q5 q6 q7 q8 q9 : Ptr}
    (h5 : SegsHold c M q5 (ringGkr (C.p.logN - 4) (aLane C.p 2) ze q5).2)
    (h6 : SegsHold c M q6 (chFixedG C.p.logN 52 ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩ ze oe (bsB C)
      ((sigIn C).bn + 2) o.r o.v q6).2)
    (h7 : SegsHold c M q7 (chLinkG C.p.logN (aLane C.p 3) ze oe ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩ 52 q7).2)
    (h8 : SegsHold c M q8 (ringGkr (C.p.ksLog - 4) (aLane C.p 6) ze q8).2)
    (h9 : SegsHold c M q9 (ksLinkG C.p (aLane C.p 7) ze oe q9).2) :
    (claimsC (tabClaims (shapesOf C D) tab (ec ze))
      (kClaimsC ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩ o.ko (ringGkr (C.p.logN - 4) (aLane C.p 2) ze q5).1 ++
        (chFixedG C.p.logN 52 ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩ ze oe (bsB C) ((sigIn C).bn + 2) o.r o.v q6).1)
      (kClaimsC ⟨C.p.ksLog + slotLog, (layout0 C.p).ks⟩ o.kko (ringGkr (C.p.ksLog - 4) (aLane C.p 6) ze q8).1)
      (chLinkG C.p.logN (aLane C.p 3) ze oe ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩ 52 q7).1
      (ksOutC C.p o.rk o.vk ze oe) (ksLinkG C.p (aLane C.p 7) ze oe q9).1).map (CClaim.val M) =
    claimsOf C.p (M3.real C.p (tabs C G D)) (pubOf vk cL sig) bus (Lvm.QAcc.evV M tab) (vs M o.r) (vs M o.v)
      (o.ko.vals M) (ringAt (feAt sig) (8 * gkrEnd (C.p.logN - 4) (aLane C.p 2) - 40) (o.ko.vals M).slicePoint
        (o.ko.vals M).slices)
      ((M3.real C.p (tabs C G D)).chLink (chLinkView C.p (M3.real C.p (tabs C G D)) (feAt sig) P5 (vs M o.r)
        (vs M o.v) (pubOf vk cL sig))).2
      (vs M o.rk) (vs M o.vk) (o.kko.vals M)
      (ringAt (feAt sig) (8 * gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 40) (o.kko.vals M).slicePoint
        (o.kko.vals M).slices)
      ((M3.real C.p (tabs C G D)).ksLink (ksLinkView C.p (M3.real C.p (tabs C G D)) (feAt sig) P7 (vs M o.rk)
        (pubOf vk cL sig))).2 := by
  have hO := phases47_fst C p2
  simp only at hO
  rw [ho47] at hO
  have eko := congrArg P47Out.ko hO
  have ekko := congrArg P47Out.kko hO
  dsimp only at eko ekko
  have ev : o.v.length = 25 := by rw [hO]; simp only [List.length_map, List.length_range]
  have evk : o.vk.length = 25 := by rw [hO]; simp only [List.length_map, List.length_range]
  clear hO
  obtain ⟨hh, -⟩ := h47
  simp only [phases47] at hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhG, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨-, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhGk, -⟩ := hh
  have sC := gkrGadget_slices hst.hlay hst.hq hS (by have := hst.hTg; omega) hhG
  have sK := gkrGadget_slices hst.hlayk hst.hqk hS (by have := hst.hTgk; omega) hhGk
  rw [← eko] at sC
  rw [← ekko] at sK
  have rC := ringGkr_rel _ hst.hq sC hS hst.hTg hz h5
  have rK := ringGkr_rel _ hst.hqk sK hS hst.hTgk hz h8
  have hz' : (ec ze).val M = 0 := hz
  rw [real_eq]
  refine claimsC_val M C.p _ _ bus _ _ _ _ _ _ _ _ _ _ _ hbus ?_ ?_ ?_ ?_ ?_ ?_
  · rw [shapesOf_eq C D G (pubOf vk cL sig), tabClaims_val hz']
    rfl
  · exact chClaims_val C.p vk cL hS hst.hT29 hz ho ev hsb hnb hst.hlog hn1 rC h6
  · have := kClaimsC_val (M := M) ⟨C.p.ksLog + slotLog, (layout0 C.p).ks⟩ _ _ _ rK
    exact this
  · exact chLinkG_val' C.p _ _ _ hst.pos47.l5 hS hst.hTl hz ho h7
  · exact ksOutC_val C.p _ _ hz ho evk
  · exact ksLinkG_val' C.p _ _ hst.pos47.l7 hS hst.hTlk' hz ho h9

/-! ## Phases 8–9 -/

/-- **Phases 8–9 and the end**: from the openings' gadget (gate on), `F`'s `openPh` on the cells' claims,
from phase 8's start `P8` with `ok`, keeps `ok`, reads `Σ'` to its end and leaves no message pending. -/
theorem open_at (C : QCfg) (D : QData) {c : Ctx} {M : Mem} {sig : ByteArray} {T P4 P5 P6 P7 P8 : Nat}
    (hst : HarStatic C D T P4 P5 P6 P7 P8) (hS : Streamed M sig T) (hg : M.k (pbB C) = 1)
    (hposr : PosOk (cfgRec C.p (posBase C)) M sig 0 C.p.recLevels (openU C.p + 15))
    (hposm : PosOk (cfgMain C.p (posBase C)) M sig 0 C.p.mainLevels
      (stackEndL C.p.recLevels (openU C.p + 15) + 15))
    (hend : 8 * stackEndL C.p.mainLevels (stackEndL C.p.recLevels (openU C.p + 15) + 15) = sig.size)
    (cs : List CClaim) (hwr : ClaimsWF C.p.nuRec (onCom cs .crec) = true)
    (hwm : ClaimsWF C.p.nuMain (onCom cs .main) = true) {z one : Cell} (hzE : z.ty = .E) (hoE : one.ty = .E)
    (hz : z.val M = 0) (ho : one.val M = 1) {q : Ptr} (hq : 1 ≤ q.e)
    (h : Lvm.QSig.Ok c M (openG (cfgRec C.p (posBase C)) (cfgMain C.p (posBase C)) cs z one (kc (pbB C))) q) :
    ∀ s : RS, pos s = P8 → s.ok = true →
      (openPh C.p (cs.map (CClaim.val M)) sig s).2.ok = true ∧
      (openPh C.p (cs.map (CClaim.val M)) sig s).2.ent = sig.size ∧
      (openPh C.p (cs.map (CClaim.val M)) sig s).2.msg = 0 := by
  intro s hs hok
  obtain ⟨o1, o2, o3⟩ := openPh_run C.p (cfgRec C.p (posBase C)) (cfgMain C.p (posBase C)) cs z one (kc (pbB C))
    hS rfl rfl rfl rfl rfl hst.hlr hst.hlm hwr hwm hz ho hzE hoE (gate_val C hg) rfl hposr hposm hq h s
    (by rw [hs, hst.hP8]; rfl)
  refine ⟨o1.trans hok, ?_, o3⟩
  simp only [pos] at o2
  have e : 8 * stackEndL (cfgMain C.p (posBase C)).levels ((cfgMain C.p (posBase C)).U + 15) = sig.size := hend
  omega

/-! ## The composition -/

/-- The padding rows are an extra conjunct: `m` holds. -/
theorem ok_withPad {α : Type} {c : Ctx} {M : Mem} {zK zE : Cell} {m : BM α} {p : Ptr}
    (h : Lvm.QSig.Ok c M (withPad zK zE m) p) : Lvm.QSig.Ok c M m p :=
  ⟨((segsHold_append c M p _ _).mp h.1).1, ((segsAssert_append M p _ _).mp h.2).1⟩

/-- **Q_arith's claim list**: `qarithT` up to phase 8 (the claims as cells, as `qarithT` builds them;
`ClaimsWF` is a static check on it; the padding comes after them). -/
def qarithCs (C : QCfg) (D : QData) (o : P47Out) : BM (List CClaim) := do
  let g := kc (pbB C)
  let p := C.p
  let S := shapesOf C D
  let z ← const .E 0 (kc 0)
  let one ← const .E 1 (kc 0)
  let _zK ← const .K 0 (kc 0)
  let chB : Placement := ⟨p.logN + slotLog, (layout0 p).ch⟩
  let ksB : Placement := ⟨p.ksLog + slotLog, (layout0 p).ks⟩
  let bus ← busG p z one g (busPos p)
  let tab ← tabG S p.tableRounds (tabPos p) z one g bus
  Lvm.QAcc.qacc (accInOf C S tab z)
  let rgC ← ringGkr (p.logN - 4) (aLane p 2) z.n
  let chF ← chFixedG p.logN 52 chB z.n one.n (bsB C) ((sigIn C).bn + 2) o.r o.v
  let clC ← chLinkG p.logN (aLane p 3) z.n one.n chB 52
  let rgK ← ringGkr (p.ksLog - 4) (aLane p 6) z.n
  let clK ← ksLinkG p (aLane p 7) z.n one.n
  pure (claimsC (tabClaims S tab z) (kClaimsC chB o.ko rgC ++ chF) (kClaimsC ksB o.kko rgK) clC
    (ksOutC p o.rk o.vk z.n one.n) clK)

/-- **`harith`, node level** (BLUEPRINT §12.6): wherever Q_arith on the record `D` holds and asserts at
`p2` (gate on: `PUB` lane 0 is `1`) and the stream cells bind `Σ'` (`Streamed M Σ' T`), the child's
`decideCore` accepts and its folded accumulator is the current proof's `acc_in` (`PUB`'s cells), for
`M3.real C.p (tabs C G D)` with any cache `G`, `pubOf vk cL Σ'` the child's public values. -/
theorem harith_core (C : QCfg) (D : QData) (G : M3.PG) (vk cL : Vector UInt8 32) {c : Ctx} {M : Mem}
    {sig : ByteArray} {T P4 P5 P6 P7 P8 : Nat} (hst : HarStatic C D T P4 P5 P6 P7 P8)
    {p2 : Ptr} (h : Lvm.QSig.Ok c M (qarith' C D) p2)
    (hS : Streamed M sig T) (hg : M.k (pbB C) = 1)
    (hvk : ∀ i < 4, M.k (pbB C + 1 + i) = (digestLanes vk).getD i 0)
    (hsb : SBits M.k (bsB C)) (hnb : NBits M.k ((sigIn C).bn + 2) C.p.logN)
    (hn1 : 1 ≤ (pubOf vk cL sig).n)
    (hposr : PosOk (cfgRec C.p (posBase C)) M sig 0 C.p.recLevels (openU C.p + 15))
    (hposm : PosOk (cfgMain C.p (posBase C)) M sig 0 C.p.mainLevels
      (stackEndL C.p.recLevels (openU C.p + 15) + 15))
    (hend : 8 * stackEndL C.p.mainLevels (stackEndL C.p.recLevels (openU C.p + 15) + 15) = sig.size)
    (hwr : ClaimsWF C.p.nuRec
      (onCom (qarithCs C D (phases47 C p2).1 (p2.adv (phases47 C p2).2)).1 .crec) = true)
    (hwm : ClaimsWF C.p.nuMain
      (onCom (qarithCs C D (phases47 C p2).1 (p2.adv (phases47 C p2).2)).1 .main) = true) :
    decideCore C.p (M3.real C.p (tabs C G D)) vk cL sig = true ∧
      accOutOf C.p (M3.real C.p (tabs C G D)) vk cL sig = Lvm.QAcc.accC M (pbB C) := by
  obtain ⟨h47, hR⟩ := okb (m := phases47 C) (f := qarithT C D) h
  -- `o`, `q0` as opaque variables (`generalize` leaves them transparent to the kernel, which then
  -- unfolds `phases47` at every cast that reads `q0`: 13 s of kernel)
  obtain ⟨o, ho47⟩ : ∃ o, (phases47 C p2).1 = o := ⟨_, rfl⟩
  obtain ⟨q0, hq0⟩ : ∃ q0, p2.adv (phases47 C p2).2 = q0 := ⟨_, rfl⟩
  simp only [ho47, hq0] at hR hwr hwm
  simp only [qarithT] at hR
  simp only [qarithCs, bind_apply, pure_apply] at hwr hwm
  -- the constants
  obtain ⟨hZ, hR⟩ := okb hR
  have hzv : (ec q0.e).val M = 0 := (constE_val hZ.1).trans ofK_zero
  have ez : (const .E 0 (kc 0) q0).1 = ec q0.e := rfl
  rw [ez, Lvm.Loop.QRing.constE_adv] at hR hwr hwm
  obtain ⟨hO1, hR⟩ := okb hR
  have hov : (ec (q0.e + 1)).val M = 1 := (constE_val hO1.1).trans ofK_one
  have eo : (const .E 1 (kc 0) ⟨q0.k, q0.e + 1⟩).1 = ec (q0.e + 1) := rfl
  rw [eo, Lvm.Loop.QRing.constE_adv] at hR hwr hwm
  obtain ⟨-, hR⟩ := okb hR
  rw [constK_adv] at hR hwr hwm
  replace hR := ok_withPad hR
  -- phases 2, 3, 3b
  obtain ⟨hB, hR⟩ := okb hR
  generalize hbus : (busG C.p (ec q0.e) (ec (q0.e + 1)) (kc (pbB C)) (busPos C.p) ⟨q0.k + 1, q0.e + 1 + 1⟩).1 = bus
    at hR hwr hwm
  generalize hq3 : (⟨q0.k + 1, q0.e + 1 + 1⟩ : Ptr).adv
    (busG C.p (ec q0.e) (ec (q0.e + 1)) (kc (pbB C)) (busPos C.p) ⟨q0.k + 1, q0.e + 1 + 1⟩).2 = q3 at hR hwr hwm
  obtain ⟨hT, hR⟩ := okb hR
  generalize htab : (tabG (shapesOf C D) C.p.tableRounds (tabPos C.p) (ec q0.e) (ec (q0.e + 1)) (kc (pbB C))
    bus q3).1 = tab at hR hwr hwm
  generalize hq4 : q3.adv (tabG (shapesOf C D) C.p.tableRounds (tabPos C.p) (ec q0.e) (ec (q0.e + 1))
    (kc (pbB C)) bus q3).2 = q4 at hR hwr hwm
  obtain ⟨hA, hR⟩ := okb hR
  generalize hq5 : q4.adv (Lvm.QAcc.qacc (accInOf C (shapesOf C D) tab (ec q0.e)) q4).2 = q5 at hR hwr hwm
  -- the ring switches and claims
  obtain ⟨h5, hR⟩ := okb hR
  generalize hq6 : q5.adv (ringGkr (C.p.logN - 4) (aLane C.p 2) q0.e q5).2 = q6 at hR hwr hwm
  obtain ⟨h6, hR⟩ := okb hR
  generalize hq7 : q6.adv (chFixedG C.p.logN 52 ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩ q0.e (q0.e + 1) (bsB C)
    ((sigIn C).bn + 2) o.r o.v q6).2 = q7 at hR hwr hwm
  obtain ⟨h7, hR⟩ := okb hR
  generalize hq8 : q7.adv (chLinkG C.p.logN (aLane C.p 3) q0.e (q0.e + 1) ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩
    52 q7).2 = q8 at hR hwr hwm
  obtain ⟨h8, hR⟩ := okb hR
  generalize hq9 : q8.adv (ringGkr (C.p.ksLog - 4) (aLane C.p 6) q0.e q8).2 = q9 at hR hwr hwm
  obtain ⟨h9, hR⟩ := okb hR
  generalize hq10 : q9.adv (ksLinkG C.p (aLane C.p 7) q0.e (q0.e + 1) q9).2 = q10 at hR hwr hwm
  -- the pointer of the openings
  have hq : 1 ≤ q10.e := by
    have e3 := Lvm.Har.adv_e_le ⟨q0.k + 1, q0.e + 1 + 1⟩
      (busG C.p (ec q0.e) (ec (q0.e + 1)) (kc (pbB C)) (busPos C.p) ⟨q0.k + 1, q0.e + 1 + 1⟩).2
    have e4 := Lvm.Har.adv_e_le q3 (tabG (shapesOf C D) C.p.tableRounds (tabPos C.p) (ec q0.e) (ec (q0.e + 1))
      (kc (pbB C)) bus q3).2
    have e5 := Lvm.Har.adv_e_le q4 (Lvm.QAcc.qacc (accInOf C (shapesOf C D) tab (ec q0.e)) q4).2
    have e6 := Lvm.Har.adv_e_le q5 (ringGkr (C.p.logN - 4) (aLane C.p 2) q0.e q5).2
    have e7 := Lvm.Har.adv_e_le q6 (chFixedG C.p.logN 52 ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩ q0.e (q0.e + 1)
      (bsB C) ((sigIn C).bn + 2) o.r o.v q6).2
    have e8 := Lvm.Har.adv_e_le q7 (chLinkG C.p.logN (aLane C.p 3) q0.e (q0.e + 1)
      ⟨C.p.logN + slotLog, (layout0 C.p).ch⟩ 52 q7).2
    have e9 := Lvm.Har.adv_e_le q8 (ringGkr (C.p.ksLog - 4) (aLane C.p 6) q0.e q8).2
    have e10 := Lvm.Har.adv_e_le q9 (ksLinkG C.p (aLane C.p 7) q0.e (q0.e + 1) q9).2
    rw [hq3] at e3; rw [hq4] at e4; rw [hq5] at e5; rw [hq6] at e6; rw [hq7] at e7; rw [hq8] at e8
    rw [hq9] at e9; rw [hq10] at e10
    simp only at e3
    omega
  -- the phases
  obtain ⟨hb, hbok, htb, hac⟩ := p23_at C D G vk cL hst hS hg hvk (z := ec q0.e) (one := ec (q0.e + 1)) rfl rfl
    hzv hov hB hbus hT htab hA
  have hgv : (kc (pbB C)).val M = 1 := gate_val C hg
  obtain ⟨hch, hchl, hokL, hks, hksl, hokK⟩ := p47_at C (pubOf vk cL sig) hst.pos47 hst.hn hst.hk hst.hr
    hst.hlay hst.hlayk hst.hq hst.hqk hS (by have := hst.hTg; omega) (by have := hst.hTgk; omega) hst.hTr
    hst.hTv hst.hTrk hst.hTvk hst.hD hst.hDk (by have := hst.hTl; omega) hst.hTlk hst.okA hst.okB hst.okC hst.hB
    hst.hB2 hst.hK hst.okE hgv h47 o ho47 (M3.real C.p (tabs C G D)) (real_eq _ _)
  have hcl := claims_at C D G vk cL hst hS hsb hnb hn1 h47 ho47 hzv hov
    ((M3.real C.p (tabs C G D)).busFinal ⟨vs M bus.al, bus.be.val M, bus.cnt.val M, vs M bus.pt,
      vs M bus.vals, [0], pubOf vk cL sig⟩) rfl tab h5.1 h6.1 h7.1 h8.1 h9.1
  unfold busV at hb
  refine core_of_phases C.p (M3.real C.p (tabs C G D)) vk cL sig (Nat.add_assoc _ _ _).symm hb hbok htb hac
    hch hchl hokL hks hksl hokK ?_
  intro s hs hok
  have e := open_at C D hst hS hg hposr hposm hend _ hwr hwm rfl rfl hzv hov hq hR s hs hok
  rw [hcl] at e
  exact e

end Lvm.Har
