-- New for lvm (HAR-WH): Q_arith phases 8–9: one stacked WHIR opening (`stackGW`, `stack_run`) and
-- `openPh`'s two (`openG`, `openPh_replays`: `C_rec`, then `C_main`).
import LvmQAsmArith2WhirLS
import LvmQAsmArith2WhirBasis

/-!
# Phases 8–9: the stacked WHIR openings

**`stackGW C cl zc oc g`** is `F`'s `verifyStackedOpening C.levels C.nu (cl.map onStack) false` for
the claims `cl` of one commitment (cells `CClaim`): every fold and tail challenge loaded from the
stream (`preloadG`, `chLanes`' order), the batching challenge `s` and its powers, the target
`Σ s^i v_i` (`targetG`), the basis point (the challenges rotated by the first fold, `copiesG`), the
batched weight `Σ s^i onStack_i(x)` (`basisG`), `verifyWhir`'s first polynomial, the levels
(`levelsG`). **`stack_run`**: wherever it holds and asserts (gate on), `F` from any state at
position `8 U` keeps `ok`, ends at `8 · stackEndL`, `msg = 0`.

**`openPh_replays`**: `openG Cr Cm cs` (`stackGW` on `cs`' `C_rec` claims, then on its `C_main`
claims) replays `openPh p (cs.map (CClaim.val M))` (`Replays`, LvmQAsmHarBase), `C_main` starting
where `C_rec` ends. Hypotheses: the stream (`Streamed`), the static checks (`StackOk`, decidable),
the zero/one/gate cells, the positions (`PosOk`: position `j` of level `i` is the `K` cell
`pb i + j` holding `eOfNat` of `F`'s `j`-th position, `qsAt`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

variable {c : Ctx} {M : Mem}

/-- The first level's fold (`whirLevels`' `laneFolds`). -/
def SCfg.lf (C : SCfg) : Nat := (C.levels.head?.map (·.fold)).getD 0

/-- **One stacked opening** (see the module doc). -/
def stackGW (C : SCfg) (cl : List CClaim) (zc oc g : Cell) : BM Unit := do
  let pc ← preloadG (chLanes C.levels (C.U + 15))
  let sb ← ldEW (C.U + 5)
  let sp ← pows (Nat.clog 2 cl.length) sb oc zc
  let tgt ← targetG cl sp zc
  let pt := (List.range C.nu).map fun k => ec (pc + k)
  let xb ← copiesG (pt.drop C.lf ++ pt.take C.lf)
  let bas ← basisG C.nu cl sp xb zc oc g
  let zk ← const .K 0 g
  let q ← rdQ (C.U + 9) tgt
  levelsG C pc zc oc g zk.n bas C.levels 0 0 (C.U + 15) q []

/-- **The static layout checks of one stacked opening** (stream lanes below `T`). -/
def LayOk (C : SCfg) (T : Nat) : Bool :=
  lvOk C T C.levels 0 0 (C.U + 15) && (chLanes C.levels (C.U + 15)).all (fun v => decide (v + 2 < T)) &&
    decide (C.U + 20 < T) && decide (C.lf ≤ C.nu)

/-- **The static checks of one stacked opening**: the layout and the claims' shapes. -/
def StackOk (C : SCfg) (cl : List CClaim) (T : Nat) : Bool := LayOk C T && ClaimsWF C.nu cl

theorem xs_eq {pc ν lf xb : Nat} (hlf : lf ≤ ν)
    (h : ∀ i < (((List.range ν).map fun k => ec (pc + k)).drop lf ++
      ((List.range ν).map fun k => ec (pc + k)).take lf).length,
      M.e (xb + i) = ((((List.range ν).map fun k => ec (pc + k)).drop lf ++
        ((List.range ν).map fun k => ec (pc + k)).take lf).getD i default).val M) :
    (List.range ν).map (fun i => M.e (xb + i)) = (ptv M pc ν).drop lf ++ (ptv M pc ν).take lf := by
  have hc : ((((List.range ν).map fun k => ec (pc + k)).drop lf ++
      ((List.range ν).map fun k => ec (pc + k)).take lf)).map (Cell.val M) =
      (ptv M pc ν).drop lf ++ (ptv M pc ν).take lf := by
    rw [List.map_append, List.map_drop, List.map_take, List.map_map]; rfl
  rw [← hc]
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, List.getElem_map, h i (by simp; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega), Option.getD_some]

set_option maxHeartbeats 1000000 in
/-- **One stacked opening replays `F`'s `verifyStackedOpening`.** -/
theorem stack_run (C : SCfg) (cl : List CClaim) (zc oc g : Cell) {sig : ByteArray} {T : Nat}
    (hS : Lvm.Q1.Streamed M sig T) (hok : StackOk C cl T = true) (hz : zc.val M = 0)
    (ho : oc.val M = 1) (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hpos : PosOk C M sig 0 C.levels (C.U + 15)) {p : Ptr} (hp : 1 ≤ p.e)
    (h : Lvm.QSig.Ok c M (stackGW C cl zc oc g) p) (s : RS) (hs : pos s = 8 * C.U) :
    (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false 0 sig s).2.ok = s.ok ∧
    pos (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false 0 sig s).2 =
      8 * stackEndL C.levels (C.U + 15) ∧
    (verifyStackedOpening C.levels C.nu (cl.map fun cc => (cc.val M).2.onStack) false 0 sig s).2.msg = 0 := by
  simp only [StackOk, LayOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨hlv, hch⟩, hU⟩, hlf⟩, hwf⟩ := hok
  replace hU := of_decide_eq_true hU
  replace hlf := of_decide_eq_true hlf
  simp only [stackGW] at h
  -- the challenges
  obtain ⟨h1, h⟩ := okb h
  obtain ⟨epc, ech⟩ := preloadG_spec hS (fun v hv => of_decide_eq_true (hch v hv)) h1.1
  rw [epc] at h
  have hp1 := le_trans hp (adv_e_le p (preloadG (chLanes C.levels (C.U + 15)) p).2)
  generalize p.adv (preloadG (chLanes C.levels (C.U + 15)) p).2 = p1 at h hp1
  -- the batching challenge and its powers
  obtain ⟨h2, h⟩ := okb h
  have esb := ldE_spec hS (by omega) h2.1
  rw [ldE_out] at esb h
  rw [ldEW_adv] at h
  have esb' : M.e p1.e = feAt sig (8 * C.U + 40) := by
    rw [show 8 * C.U + 40 = 8 * (C.U + 5) by ring]; exact esb
  obtain ⟨h3, h⟩ := okb h
  have e3 := pows_spec h3.1 hz ho hoE
  have hsp : ∀ i < cl.length,
      M.e ((pows (Nat.clog 2 cl.length) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 + i) =
        feAt sig (8 * C.U + 40) ^ i := fun i hi => by
    rw [e3 i (le_trans hi.le (Nat.le_pow_clog (by norm_num) _)), Cell.val_E, esb']
  have hp3 : 1 ≤ ((⟨p1.k, p1.e + 1⟩ : Ptr).adv
      (pows (Nat.clog 2 cl.length) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2).e :=
    le_trans (by show 1 ≤ p1.e + 1; omega) (adv_e_le _ _)
  generalize (pows (Nat.clog 2 cl.length) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).1 = sp at h hsp
  generalize (⟨p1.k, p1.e + 1⟩ : Ptr).adv
    (pows (Nat.clog 2 cl.length) (ec p1.e) oc zc ⟨p1.k, p1.e + 1⟩).2 = p3 at h hp3
  -- the target
  obtain ⟨h4, h⟩ := okb h
  have et := targetG_spec h4.1 hz _ hsp
  have hp4 := le_trans hp3 (adv_e_le p3 (targetG cl sp zc p3).2)
  generalize (targetG cl sp zc p3).1 = tgt at h et
  generalize p3.adv (targetG cl sp zc p3).2 = p4 at h hp4
  -- the basis point and the basis
  obtain ⟨h5, h⟩ := okb h
  obtain ⟨exb, ecp⟩ := copiesG_spec (fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_drop hx); rfl
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx); rfl) h5.1
  have hxs := xs_eq (M := M) hlf ecp
  rw [exb] at h
  have hp5 : 1 ≤ (p4.adv (copiesG (((List.range C.nu).map fun k => ec (p.e + k)).drop C.lf ++
      ((List.range C.nu).map fun k => ec (p.e + k)).take C.lf) p4).2).e :=
    le_trans hp4 (adv_e_le _ _)
  generalize p4.adv (copiesG (((List.range C.nu).map fun k => ec (p.e + k)).drop C.lf ++
      ((List.range C.nu).map fun k => ec (p.e + k)).take C.lf) p4).2 = p5 at h hp5
  obtain ⟨h6, h⟩ := okb h
  have eb := basisG_spec h6.1 hwf hz ho hzE hoE hgK hp5 _ hsp
  rw [hxs] at eb
  have hp6 := le_trans hp5 (adv_e_le p5 (basisG C.nu cl sp p4.e zc oc g p5).2)
  generalize (basisG C.nu cl sp p4.e zc oc g p5).1 = bas at h eb
  generalize p5.adv (basisG C.nu cl sp p4.e zc oc g p5).2 = p6 at h hp6
  -- the `K` zero cell
  obtain ⟨h7, h⟩ := okb h
  have ez := lin_spec (τ := .K) (k := 1) (k' := 0) (a := g) (b := g) h7.1
  have hzk : M.k p6.k = 0 := by
    rw [show (lin .K 1 0 g g p6).1 = kc p6.k from rfl, Cell.val_K, hg, ofK_one, ofK_zero, one_mul,
      add_zero, CharTwo.add_self_eq_zero] at ez
    exact ofK_inj (ez.trans ofK_zero.symm)
  have hp7 := le_trans hp6 (adv_e_le p6 (const .K 0 g p6).2)
  rw [show (const .K 0 g p6).1 = kc p6.k from rfl] at h
  generalize p6.adv (const .K 0 g p6).2 = p7 at h hp7
  -- `verifyWhir`'s first polynomial
  obtain ⟨h8, h⟩ := okb h
  have eq0 := rdQ_spec hS (by omega) h8.1
  have hp8 := le_trans hp7 (adv_e_le p7 (rdQ (C.U + 9) tgt p7).2)
  generalize (rdQ (C.U + 9) tgt p7).1 = q at h eq0
  generalize p7.adv (rdQ (C.U + 9) tgt p7).2 = p8 at h hp8
  -- `F`
  simp only [verifyStackedOpening, verifyWhir]
  rw [dm_bind, sampleE_run]
  dsimp only
  rw [dm_bind, srp3_run]
  dsimp only
  refine levels_run C hS p.e zc oc g p6.k bas hz ho hzE hoE hg hgK hzk C.lf _ ?_ C.levels 0 0 (C.U + 15)
    q [] _ p8 hlv hp8 ?_ (by simp) (fun j hj => by rw [Nat.add_zero]; exact ech j hj) hpos
    ⟨by simp, by simp⟩ h _ ?_
  · rw [eb, hs]; simp only [List.map_map, List.length_map]; rfl
  · rw [eq0, et, pos_mk0, hs, List.length_map, List.map_map,
      show 8 * (C.U + 9) = 8 * C.U + 72 by ring]
    rfl
  · simp only [pos] at hs ⊢; omega

/-! ## Phases 8–9 -/

/-- The claims of one commitment. -/
def onCom (cs : List CClaim) (com : Com) : List CClaim := cs.filter fun cc => cc.com == com

theorem on_eq (cs : List CClaim) (com : Com) :
    ((cs.map (CClaim.val M)).filter (·.1 == com)).map (·.2.onStack) =
      (onCom cs com).map fun cc => (cc.val M).2.onStack := by
  rw [List.filter_map, List.map_map]; rfl

/-- **Phases 8–9**: `C_rec`'s stacked opening, then `C_main`'s. -/
def openG (Cr Cm : SCfg) (cs : List CClaim) (zc oc g : Cell) : BM Unit := do
  stackGW Cr (onCom cs .crec) zc oc g
  stackGW Cm (onCom cs .main) zc oc g

/-- **Phases 8–9 run**: `F`'s `openPh` from any state at position `8 Cr.U` keeps `ok`, ends at
`8 · stackEndL` of `C_main`, `msg = 0`. -/
theorem openPh_run (p : Params) (Cr Cm : SCfg) (cs : List CClaim) (zc oc g : Cell) {sig : ByteArray}
    {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hr : Cr.levels = p.recLevels) (hrν : Cr.nu = p.nuRec)
    (hm : Cm.levels = p.mainLevels) (hmν : Cm.nu = p.nuMain) (hgr : p.grind = 0)
    (hU : Cm.U = stackEndL Cr.levels (Cr.U + 15)) (hlr : LayOk Cr T = true) (hlm : LayOk Cm T = true) (hwr : ClaimsWF Cr.nu (onCom cs .crec) = true)
    (hwm : ClaimsWF Cm.nu (onCom cs .main) = true) (hz : zc.val M = 0) (ho : oc.val M = 1)
    (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hposr : PosOk Cr M sig 0 Cr.levels (Cr.U + 15)) (hposm : PosOk Cm M sig 0 Cm.levels (Cm.U + 15))
    {ptr : Ptr} (hp : 1 ≤ ptr.e) (h : Lvm.QSig.Ok c M (openG Cr Cm cs zc oc g) ptr) (s : RS)
    (hs : pos s = 8 * Cr.U) :
    (openPh p (cs.map (CClaim.val M)) sig s).2.ok = s.ok ∧
    pos (openPh p (cs.map (CClaim.val M)) sig s).2 = 8 * stackEndL Cm.levels (Cm.U + 15) ∧
    (openPh p (cs.map (CClaim.val M)) sig s).2.msg = 0 := by
  simp only [openG] at h
  obtain ⟨h1, h2⟩ := okb h
  simp only [openPh, hgr]
  rw [dm_bind, on_eq, on_eq, ← hr, ← hrν, ← hm, ← hmν]
  obtain ⟨o1, p1, -⟩ := stack_run Cr _ zc oc g hS (by simp [StackOk, hlr, hwr]) hz ho hzE hoE hg hgK
    hposr hp h1 s hs
  obtain ⟨o2, p2, m2⟩ := stack_run Cm _ zc oc g hS (by simp [StackOk, hlm, hwm]) hz ho hzE hoE hg hgK
    hposm (le_trans hp (adv_e_le _ _)) h2 _ (by rw [p1, hU])
  exact ⟨o2.trans o1, p2, m2⟩

/-- **Q_arith phases 8–9 replay `openPh`** (`Replays`, the soundness direction). -/
theorem openPh_replays (p : Params) (Cr Cm : SCfg) (cs : List CClaim) (zc oc g : Cell) {sig : ByteArray}
    {T : Nat} (hS : Lvm.Q1.Streamed M sig T) (hr : Cr.levels = p.recLevels) (hrν : Cr.nu = p.nuRec)
    (hm : Cm.levels = p.mainLevels) (hmν : Cm.nu = p.nuMain) (hgr : p.grind = 0)
    (hU : Cm.U = stackEndL Cr.levels (Cr.U + 15)) (hlr : LayOk Cr T = true) (hlm : LayOk Cm T = true) (hwr : ClaimsWF Cr.nu (onCom cs .crec) = true)
    (hwm : ClaimsWF Cm.nu (onCom cs .main) = true) (hz : zc.val M = 0) (ho : oc.val M = 1)
    (hzE : zc.ty = .E) (hoE : oc.ty = .E) (hg : g.val M = 1) (hgK : g.ty = .K)
    (hposr : PosOk Cr M sig 0 Cr.levels (Cr.U + 15)) (hposm : PosOk Cm M sig 0 Cm.levels (Cm.U + 15))
    {ptr : Ptr} (hp : 1 ≤ ptr.e) :
    Replays c M sig (openPh p (cs.map (CClaim.val M))) (openG Cr Cm cs zc oc g) ptr (8 * Cr.U)
      (8 * stackEndL Cm.levels (Cm.U + 15)) (fun _ _ => True) := by
  intro h s hs hok
  obtain ⟨o, q, -⟩ := openPh_run p Cr Cm cs zc oc g hS hr hrν hm hmν hgr hU hlr hlm hwr hwm hz ho hzE hoE hg
    hgK hposr hposm hp h s hs
  exact ⟨o.trans hok, q, trivial⟩

/-! ## `F`'s positions as bit fields of the answers -/

theorem paF_getD (sig : ByteArray) (h : Nat) : ∀ (n P rem j : Nat), j < min (positionsPerAnswer * n) rem →
    (paF sig h P n rem).getD j 0 = (eToNat (feAt sig (P + 72 * (j / 8) + 40)) >>> ((j % 8) * h)) % 2 ^ h
  | 0, _, _, j, hj => by simp [positionsPerAnswer] at hj
  | n + 1, P, rem, j, hj => by
    rw [paF]
    simp only [positionsPerAnswer] at hj ⊢
    by_cases hj8 : j < min 8 rem
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj8),
        List.getElem?_map, List.getElem?_range hj8]
      simp only [Option.map_some, Option.getD_some]
      have e1 : j / 8 = 0 := by omega
      have e2 : j % 8 = j := by omega
      rw [e1, e2, Nat.mul_zero, Nat.add_zero]
    · have h8 : min 8 rem = 8 := by omega
      have e := paF_getD sig h n (P + 72) (rem - 8) (j - 8) (by simp only [positionsPerAnswer]; omega)
      have hl : ((List.range (min 8 rem)).map
          (fun j => (eToNat (feAt sig (P + 40)) >>> (j * h)) % 2 ^ h)).length = 8 := by simp [h8]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; omega), hl,
        ← List.getD_eq_getElem?_getD, h8, e]
      have e1 : (j - 8) / 8 = j / 8 - 1 := by omega
      have e2 : (j - 8) % 8 = j % 8 := by omega
      have e3 : P + 72 + 72 * (j / 8 - 1) = P + 72 * (j / 8) := by
        have : 1 ≤ j / 8 := by omega
        rw [Nat.mul_sub, Nat.mul_one]; omega
      rw [e1, e2, e3]

/-- **`F`'s `j`-th position** of level `L` at position `P`: bits `(j mod 8)·height …` of the
`⌊j/8⌋`-th positions answer (lanes `0–2` as one number, `eToNat`). -/
theorem qsAt_getD (sig : ByteArray) (P : Nat) (L : Level) (j : Nat) (hj : j < L.t) :
    (qsAt sig P L).getD j 0 =
      (eToNat (feAt sig (P + 72 * (j / 8) + 40)) >>> ((j % 8) * L.height)) % 2 ^ L.height := by
  have e := (positionsAux_run L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) L.t sig
    ⟨P, 0, true⟩).1
  show (positionsAux L.height ((L.t + positionsPerAnswer - 1) / positionsPerAnswer) L.t sig
    ⟨P, 0, true⟩).1.getD j 0 = _
  rw [e, pos_mk0]
  exact paF_getD sig L.height _ P L.t j (by simp only [positionsPerAnswer]; omega)

end Lvm.Har
