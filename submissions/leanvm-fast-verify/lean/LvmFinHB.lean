-- New for lvm (WP-16a2, FIN-HB): N10, `NodeBase.harith` (A23's form) for WP-16a's P20 node program,
-- from HAR's `harith_core` (`LvmQAsmHarMain`) at `cfg20`, `data20`, `M3.G20`.
import LvmCertSFinal
import LvmFinStatic
import LvmQAsmFacts
import LvmAccNodeLen

/-!
# `harith20`: Q_arith's `harith` at P20

**`harith20 hH S BV`** is the field `NodeBase.harith` at `lay cfg20`, `sigIn cfg20`, `qarith cfg20`,
`nK cfg20`, `nE = 0`, `plOf data20`, `data20.groups`, `arrsX x = arrs cfg20 data20 (pubX x)`,
`aux cfg20 data20` (any `hτ'`, any `hτT`), from

* `hH : HarStatic cfg20 data20 (streamLanes P20) P4 P5 P6 P7 P8` (HAR's static facts, decided by FIN);
* `S : StaticFacts` (A24's guard: `hwr`, `hwm` at `p2C cfg20`);
* `BV : BVFacts hτ' hτT` (FIN-BV: `SBits`, `NBits`, `1 ≤ n'`, both `PosOk`), each under the premises
  of `NodeBase.harith` (`HBPrem`).

Proved here: the stream binds `Σ'` (`streamed_child`; `T ≤ 2^m` from `hQ20`, `T ≤ |ws|` from
`LaneLink.size`), the gate and `vk` (`InMapN.flag`, `InMapN.pub`, `hdrLanes_eq_pubX`, `okS_vk`), the end
of `Σ'` (`lay20`, `|Σ'| = hashedLen`), and the accumulator half `accC M (pbB cfg20) = (pubX x).accIn`
(`InMapN.pub`, `accIn_pt_lanes`, `accIn_y_lanes`).
-/

set_option autoImplicit false

namespace Lvm.Fin

open RecursionFast Lvm Lvm.M3 Lvm.VEq Lvm.Acc Lvm.ASM
open Lvm.T Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.SigBits Lvm.NS LeanVM.Protocol
open Lvm.QAsm (cfg20 data20 lay sigIn qarith nK aux arrs plOf p2C pbB bsB hQ20 hS20)

/-! ## Pointer, program, sizes -/

theorem p2_cfg20 : p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0 = p2C cfg20 := rfl

theorem dataOf_cfg20 : Lvm.Har.dataOf cfg20 = data20 := if_pos rfl

theorem qarith_cfg20 : qarith cfg20 = Lvm.Har.qarith' cfg20 data20 := by
  rw [Lvm.Har.qarith_eq', dataOf_cfg20]

theorem real_cfg20 :
    M3.real cfg20.p (Lvm.QAsm.tabs cfg20 M3.G20 data20) = M3.real P20 M3.tabsP20 := rfl

theorem sigma_size {p : Params} {ws : List Word} (h : hashedLen p ≤ 8 * ws.length) :
    (sigma p ws).size = hashedLen p := by
  simp only [sigma, ByteArray.size, List.size_toArray, List.length_take, wordsBytes_length]
  omega

/-! ## The `PUB` cells: the gate's `vk` lanes and the current `acc_in` -/

theorem vk_cells {M : Mem} {x : List UInt8} {pb : ℕ} {vk : RecursionFast.Digest}
    (hpub : ∀ j < pubLanes, M.k (pb + j) = hdrLane x j) (hvk : (hdrOf x).vk = vk) :
    ∀ i < 4, M.k (pb + 1 + i) = (digestLanes vk).getD i 0 := by
  intro i hi
  have hj : 1 + i < pubLanes := by rw [pubLanes_eq]; omega
  have e1 : M.k (pb + 1 + i) = (hdrLanes x).getD (1 + i) 0 := by
    rw [Nat.add_assoc, hpub _ hj, hdrLanes, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hj, Option.map_some, Option.getD_some]
  have hv : (pubX x).vk = digestLanes vk := by rw [← hvk]; rfl
  have hl : i < (digestLanes vk).length := by simp only [digestLanes, List.length_map, List.length_range]; omega
  rw [e1, hdrLanes_eq_pubX, Pub.hdrLanes, hv]
  simp only [List.append_assoc, List.singleton_append]
  rw [Nat.add_comm, List.getD_append _ _ _ _ (by rw [List.length_cons]; omega), List.getD_cons_succ]

theorem accC_eq {M : Mem} {x : List UInt8} {pb : ℕ}
    (hpub : ∀ j < pubLanes, M.k (pb + j) = hdrLane x j) : Lvm.QAcc.accC M pb = (pubX x).accIn := by
  have hP : ∀ j a, j < pubLanes → a = pb + j → M.k a = hdrLane x j := fun j a hj ha => ha ▸ hpub j hj
  have hL : pubLanes = 702 := pubLanes_eq
  have hA : accVars = 28 := rfl
  refine acc_eq_of (by simp only [Lvm.QAcc.accC, List.length_map, List.length_range])
    (length_pubOf_accIn _ _ _) (fun i hi => ?_) ?_
  · rw [accIn_pt_lanes x hi]
    simp only [Lvm.QAcc.accC, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    rw [hP (615 + 3 * i) _ (by omega) (by omega), hP (616 + 3 * i) _ (by omega) (by omega),
      hP (617 + 3 * i) _ (by omega) (by omega)]
  · rw [accIn_y_lanes x]
    simp only [Lvm.QAcc.accC]
    rw [hP (615 + 3 * accVars) _ (by omega) (by omega), hP (616 + 3 * accVars) _ (by omega) (by omega),
      hP (617 + 3 * accVars) _ (by omega) (by omega)]

/-! ## The premises and FIN-BV's facts -/

section P20

variable
  (hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0) (plOf data20)
    data20.groups (arrs cfg20 data20 (pubX x)) (aux cfg20 data20), t.τ ≤ lay26.μ)
  (hτT : ∀ x, ∀ t ∈ TS M3.tabsP20 x, t.τ ≤ lay26.μ)

/-- The memory of the P20 node program on the pair `(qm, qr)` of statement `x`. -/
noncomputable abbrev mem20 (x : List UInt8) (qm : Column 26) (qr : Column 19) : Mem :=
  memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 (plOf data20) data20.groups
    (fun x => arrs cfg20 data20 (pubX x)) (aux cfg20 data20) hτ' x qm qr

/-- The child's stream words. -/
abbrev ws20 (qr : Column 19) : List Word := wsOf (Lvm.X.laneOf (wOfCol qr))

/-- The child's trace bytes `Σ'`. -/
abbrev sig20 (qr : Column 19) : ByteArray := traceBytesB (decode P20 (ws20 qr))

/-- **The premises of `NodeBase.harith`** at the P20 node program. -/
structure HBPrem (vk c : RecursionFast.Digest) (x : List UInt8) (qm : Column 26) (qr : Column 19) : Prop where
  ok : okS vk c x = true
  b1 : (hdrOf x).b = 1
  good : GoodN (TS M3.tabsP20) hτT x qm qr
  inm : InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 (plOf data20) data20.groups
    (fun x => arrs cfg20 data20 (pubX x)) (aux cfg20 data20) hτ' vk x qm qr
  ll : LaneLink P20 (ws20 qr)
  lk : LinkOk P20 (decode P20 (ws20 qr))
  run : Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0)) (mem20 hτ' x qm qr)
    (qarith cfg20) (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0)

/-- **FIN-BV's memory facts** (`harith_core`'s `hsb`, `hnb`, `hn1`, `hposr`, `hposm`), each under
`NodeBase.harith`'s premises. -/
structure BVFacts : Prop where
  sb : ∀ vk c x qm qr, HBPrem hτ' hτT vk c x qm qr → Lvm.Har.SBits (mem20 hτ' x qm qr).k (bsB cfg20)
  nb : ∀ vk c x qm qr, HBPrem hτ' hτT vk c x qm qr →
    Lvm.Har.NBits (mem20 hτ' x qm qr).k ((sigIn cfg20).bn + 2) P20.logN
  n1 : ∀ vk c x qm qr, HBPrem hτ' hτT vk c x qm qr → 1 ≤ (pubOf vk (hdrOf x).cL (sig20 qr)).n
  posr : ∀ vk c x qm qr, HBPrem hτ' hτT vk c x qm qr →
    Lvm.Har.PosOk (Lvm.Har.cfgRec P20 (Lvm.Har.posBase cfg20)) (mem20 hτ' x qm qr) (sig20 qr) 0
      P20.recLevels (Lvm.Har.openU P20 + 15)
  posm : ∀ vk c x qm qr, HBPrem hτ' hτT vk c x qm qr →
    Lvm.Har.PosOk (Lvm.Har.cfgMain P20 (Lvm.Har.posBase cfg20)) (mem20 hτ' x qm qr) (sig20 qr) 0
      P20.mainLevels (Lvm.Har.stackEndL P20.recLevels (Lvm.Har.openU P20 + 15) + 15)

variable {hτ' hτT}

/-- **N10: `NodeBase.harith` at the P20 node program** (A23's form) from HAR's static facts `hH`, the
guard's `S` (`hwr`, `hwm`) and FIN-BV's `BV`. -/
theorem harith20 {P4 P5 P6 P7 P8 : ℕ}
    (hH : Lvm.Har.HarStatic cfg20 data20 (streamLanes P20) P4 P5 P6 P7 P8) (S : StaticFacts)
    (BV : BVFacts hτ' hτT) :
    ∀ vk c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → GoodN (TS M3.tabsP20) hτT x qm qr →
      InMapN (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 (plOf data20) data20.groups
        (fun x => arrs cfg20 data20 (pubX x)) (aux cfg20 data20) hτ' vk x qm qr →
      LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))) →
      LinkOk P20 (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) →
      Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0))
        (memX (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0 (plOf data20) data20.groups
          (fun x => arrs cfg20 data20 (pubX x)) (aux cfg20 data20) hτ' x qm qr) (qarith cfg20)
        (p2 (lay cfg20) (sigIn cfg20) (nK cfg20) 0) →
      decideCore P20 (M3.real P20 M3.tabsP20) vk (hdrOf x).cL
          (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = true ∧
        accOutOf P20 (M3.real P20 M3.tabsP20) vk (hdrOf x).cL
          (traceBytesB (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))) = (pubX x).accIn := by
  intro vk c x qm qr hok hb hgood hin hL hLk hrun
  have P : HBPrem hτ' hτT vk c x qm qr := ⟨hok, hb, hgood, hin, hL, hLk, hrun⟩
  -- the run at Q_arith's pointer, on the record
  have h : Ok (ctxOf (Qn (lay cfg20) (sigIn cfg20) (qarith cfg20) (nK cfg20) 0)) (mem20 hτ' x qm qr)
      (Lvm.Har.qarith' cfg20 data20) (p2C cfg20) := by
    rw [← qarith_cfg20, ← p2_cfg20]; exact hrun
  -- the stream binds `Σ'`
  have hT := hQ20.hT
  have hsz := hL.size
  have hS : Lvm.Q1.Streamed (mem20 hτ' x qm qr) (sig20 qr) (streamLanes P20) :=
    Lvm.Har.streamed_child cfg20 hS20 hL hin.stream (T := streamLanes P20) (by rw [streamLanes]; omega)
      (by rw [show cfg20.p = P20 from rfl, streamLanes]; omega) (by rw [streamLanes]; omega)
  -- the `PUB` cells
  have hpub : ∀ j < pubLanes, (mem20 hτ' x qm qr).k (pbB cfg20 + j) = hdrLane x j := hin.pub
  -- the end of `Σ'`
  have hend : 8 * Lvm.Har.stackEndL cfg20.p.mainLevels
      (Lvm.Har.stackEndL cfg20.p.recLevels (Lvm.Har.openU cfg20.p + 15) + 15) = (sig20 qr).size := by
    rw [show cfg20.p = P20 from rfl, (Lvm.Har.lay20 (Lvm.Har.posBase cfg20)).2.2.2.1, sig20,
      traceBytesB_decode hS20 hL, sigma_size hsz]
  -- `BV`'s position facts at `cfg20.p` (a rewrite: the kernel compares the stack ends syntactically)
  have hposr : Lvm.Har.PosOk (Lvm.Har.cfgRec cfg20.p (Lvm.Har.posBase cfg20)) (mem20 hτ' x qm qr) (sig20 qr) 0
      cfg20.p.recLevels (Lvm.Har.openU cfg20.p + 15) := by
    rw [show cfg20.p = P20 from rfl]; exact BV.posr vk c x qm qr P
  have hposm : Lvm.Har.PosOk (Lvm.Har.cfgMain cfg20.p (Lvm.Har.posBase cfg20)) (mem20 hτ' x qm qr) (sig20 qr) 0
      cfg20.p.mainLevels (Lvm.Har.stackEndL cfg20.p.recLevels (Lvm.Har.openU cfg20.p + 15) + 15) := by
    rw [show cfg20.p = P20 from rfl]; exact BV.posm vk c x qm qr P
  obtain ⟨h1, h2⟩ := Lvm.Har.harith_core cfg20 data20 M3.G20 vk (hdrOf x).cL hH h hS hin.flag
    (vk_cells hpub (okS_vk hok)) (BV.sb vk c x qm qr P) (BV.nb vk c x qm qr P) (BV.n1 vk c x qm qr P)
    hposr hposm hend S.hwr S.hwm
  rw [real_cfg20] at h1 h2
  exact ⟨h1, h2.trans (accC_eq hpub)⟩

end P20

end Lvm.Fin
