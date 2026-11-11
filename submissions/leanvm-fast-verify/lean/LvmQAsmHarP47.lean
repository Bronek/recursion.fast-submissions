-- New for lvm (HAR): phases 4–7 of `F` as `PhaseAt` facts from WP-16a's wiring (`phases47`), QA1's
-- `gkr_spec`/`chLink_sound`/`ksLink_sound`, and the reading lemmas of `LvmQAsmHar47`.
import LvmQAsmHar47
import LvmQAsmHarTop

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- `phases47`'s output cells through its sub-gadgets (pointers as the builder places them). -/
theorem phases47_fst (C : QCfg) (ptr : Ptr) :
    let A := loadEs (clog2 C.p.logN) (aLane C.p 0) 9
    let p1 := ptr.adv (A ptr).2
    let B := loadEs 5 (aLane C.p 1) 3
    let p2 := p1.adv (B p1).2
    let G := Lvm.Q1.gkrGadget (C.p.logN - 4) (aLane C.p 2) (fun i => (A ptr).1.cell 0 i)
      (fun l => (B p1).1.cell 0 l) (kc (pbB C))
    let p3 := p2.adv (G p2).2
    let L := Lvm.Q1.chLinkGadget C.p.logN (clog2 C.p.logN) (aLane C.p 3) (kc (pbB C))
    let p4 := p3.adv (L p3).2
    let Ak := loadEs (clog2 C.p.ksLog) (aLane C.p 4) 9
    let p5 := p4.adv (Ak p4).2
    let Bk := loadEs 5 (aLane C.p 5) 3
    let p6 := p5.adv (Bk p5).2
    let Gk := Lvm.Q1.gkrGadget (C.p.ksLog - 4) (aLane C.p 6) (fun i => (Ak p4).1.cell 0 i)
      (fun l => (Bk p5).1.cell 0 l) (kc (pbB C))
    (phases47 C ptr).1 = ⟨(List.range C.p.logN).map ((A ptr).1.cell 0), (List.range 25).map ((B p1).1.cell 0),
      (G p2).1, (List.range C.p.ksLog).map ((Ak p4).1.cell 0), (List.range 25).map ((Bk p5).1.cell 0), (Gk p6).1⟩ := by
  intro A p1 B p2 G p3 L p4 Ak p5 Bk p6 Gk
  simp only [phases47, bind_apply, pure_apply]
  rfl

/-- The positions of phases 4–7 the wiring assumes (`P4 … P8`: CH, CH link, KS, KS link, openings). -/
structure P47Pos (p : Params) (P4 P5 P6 P7 P8 : Nat) : Prop where
  ch0 : P4 + 40 = 8 * aLane p 0
  ch1 : kV p.logN P4 + 40 = 8 * aLane p 1
  ch2 : kG p.logN P4 = 8 * aLane p 2 - 40
  ch5 : 8 * gkrEnd (p.logN - 4) (aLane p 2) - 40 + 72 * ringStages = P5
  l5 : P5 + 40 = 8 * aLane p 3
  l6 : chP6 p P5 = P6
  ks0 : P6 + 40 = 8 * aLane p 4
  ks1 : kV p.ksLog P6 + 40 = 8 * aLane p 5
  ks2 : kG p.ksLog P6 = 8 * aLane p 6 - 40
  ks7 : 8 * gkrEnd (p.ksLog - 4) (aLane p 6) - 40 + 72 * ringStages = P7
  l7 : P7 + 40 = 8 * aLane p 7
  l8 : ksP2 p P7 + 96 = P8

/-- **Phases 4–7 from `phases47`'s rows and assertions** (gate on): each phase from its start
position yields the cells' values (the ring switch's value as `F` computes it), keeps `ok`, reaches the
next start; both links' checks hold. -/
theorem p47_at (C : QCfg) {c : Ctx} {M : Mem} {ptr : Ptr} {sig : ByteArray} {T : Nat}
    {bf : BusIn → BusOut} {tb : Pub → List TableSpec} {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)}
    {tfv : Pub → List FE → List FE} {tfs : Pub → List (List FE × List FE) → List FE}
    {tpc : Pub → List (List FE × List FE) → Bool} (pub : Pub) {P4 P5 P6 P7 P8 : Nat}
    (hpos : P47Pos C.p P4 P5 P6 P7 P8)
    (hn : 4 ≤ C.p.logN) (hk : 4 ≤ C.p.ksLog) (hr : C.p.recRowsLog < C.p.ksLog)
    (hlay : layOk (C.p.logN - 4) = true) (hlayk : layOk (C.p.ksLog - 4) = true)
    (hq : 5 ≤ aLane C.p 2) (hqk : 5 ≤ aLane C.p 6)
    (hS : Streamed M sig T) (hT : gkrEnd (C.p.logN - 4) (aLane C.p 2) ≤ T)
    (hTk : gkrEnd (C.p.ksLog - 4) (aLane C.p 6) ≤ T)
    (hTr : aLane C.p 0 + 9 * C.p.logN + 2 < T) (hTv : aLane C.p 1 + 3 * 25 + 2 < T)
    (hTrk : aLane C.p 4 + 9 * C.p.ksLog + 2 < T) (hTvk : aLane C.p 5 + 3 * 25 + 2 < T)
    (hD : C.p.logN ≤ 2 ^ clog2 C.p.logN) (hDk : C.p.ksLog ≤ 2 ^ clog2 C.p.ksLog)
    (hTl : chQC C.p.logN (aLane C.p 3) + 3 * 64 + 3 ≤ T) (hTlk : ksQV C.p.ksLog (aLane C.p 7) + 3 * 4 + 3 ≤ T)
    (hokA : SLok (chGlueA C.p.logN (aLane C.p 3)) = true)
    (hokB : ∀ oA sh : LoopOut, SLok (chGlueB (chQB C.p.logN (aLane C.p 3)) (rhoC oA C.p.logN) (rho'C sh C.p.logN)
      (eZC oA C.p.logN) (sh.cell 5 (C.p.logN - 1))) = true)
    (hokC : ∀ oA sh sc2 oB : LoopOut, SLok (chGlueC (chQC C.p.logN (aLane C.p 3)) [sc2.cell 2 0, sc2.cell 2 1]
      (eLC oA C.p.logN) (eZC oA C.p.logN) (rho'C sh C.p.logN) (oA.cell (2 * C.p.logN + 163) 0)
      (oB.cell (8 * C.p.logN + 123) 0) (sc2.cell 5 1) (kc (pbB C))) = true)
    (hB : 1 ≤ spongeBlocks C.p) (hB2 : spongeBlocks C.p ≤ 2 ^ C.p.ksLog) (hK : 2 ^ C.p.recRowsLog + 431 ≤ 2 ^ C.p.ksLog)
    (hokE : ∀ sh : LoopOut, SLok (ksGlueE C.p.ksLog (aLane C.p 7) (ksQV C.p.ksLog (aLane C.p 7)) (spongeBlocks C.p - 1)
      (2 ^ C.p.recRowsLog + 399 + 31) (2 ^ C.p.recRowsLog + 399) (rho'C sh C.p.ksLog) (sh.cell 2 C.p.recRowsLog)
      (sh.cell 5 (C.p.ksLog - 1)) (kc (pbB C))) = true)
    (hg : (kc (pbB C)).val M = 1) (h : Lvm.QSig.Ok c M (phases47 C) ptr)
    (o : P47Out) (ho : (phases47 C ptr).1 = o) (m : M3) (hm : m = M3.ofParts C.p bf tb tcl tfv tfs tpc) :
    PhaseAt (chPh C.p) sig P4 P5 (vs M o.r, vs M o.v, o.ko.vals M,
      ringAt (feAt sig) (8 * gkrEnd (C.p.logN - 4) (aLane C.p 2) - 40) (o.ko.vals M).slicePoint (o.ko.vals M).slices) ∧
    PhaseAt (chLinkPh C.p m (vs M o.r) (vs M o.v) pub) sig P5 P6
      (m.chLink (chLinkView C.p m (feAt sig) P5 (vs M o.r) (vs M o.v) pub)) ∧
    (m.chLink (chLinkView C.p m (feAt sig) P5 (vs M o.r) (vs M o.v) pub)).1 = true ∧
    PhaseAt (ksPh C.p) sig P6 P7 (vs M o.rk, vs M o.vk, o.kko.vals M,
      ringAt (feAt sig) (8 * gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 40) (o.kko.vals M).slicePoint (o.kko.vals M).slices) ∧
    PhaseAt (ksLinkPh C.p m (vs M o.rk) pub) sig P7 P8 (m.ksLink (ksLinkView C.p m (feAt sig) P7 (vs M o.rk) pub)) ∧
    (m.ksLink (ksLinkView C.p m (feAt sig) P7 (vs M o.rk) pub)).1 = true := by
  have hO := phases47_fst C ptr
  simp only at hO
  rw [ho] at hO
  subst hO hm
  obtain ⟨hh, ha⟩ := h
  simp only [phases47] at hh ha
  rw [hold_bind] at hh; obtain ⟨hhR, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhV, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhG, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhL, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhRk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhVk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhGk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhLk, -⟩ := hh
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haG, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haL, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haGk, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haLk, -⟩ := ha
  obtain ⟨e0, e1, e2, e5, l5, l6, k0, k1, k2, k7, l7, l8⟩ := hpos
  have KB := kblock_sound hn hlay hq hS hT hTr hTv hD hhR hhV hhG haG hg P4 e0 e1 e2
  have KK := kblock_sound hk hlayk hqk hS hTk hTrk hTvk hDk hhRk hhVk hhGk haGk hg P6 k0 k1 k2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hok
    rw [chPh_run C.p (by omega) sig s, hs]
    obtain ⟨f1, f2, f3, f4, f5⟩ := KB s.ok
    refine ⟨?_, ?_, ?_⟩
    · simp only [vs, List.map_map]
      rw [f4, f3, f1, f2]
      rfl
    · exact f5 hok
    · simp only [pos, Nat.add_zero]; omega
  · intro s hs hok
    rw [chLinkPh_run C.p _ _ _ pub sig s (by omega), hs]
    exact ⟨rfl, hok, by simp only [pos, Nat.add_zero]; exact l6⟩
  · exact chLink_sound C.p _ 52 (clog2 C.p.logN) _ _ pub (kc (pbB C)) (by omega) hD l5 hokA hokB hokC hS hTl hg
      hhL haL
  · intro s hs hok
    rw [ksPh_run C.p (by omega) sig s, hs]
    obtain ⟨f1, f2, f3, f4, f5⟩ := KK s.ok
    refine ⟨?_, ?_, ?_⟩
    · simp only [vs, List.map_map]
      rw [f4, f3, f1, f2]
      rfl
    · exact f5 hok
    · simp only [pos, Nat.add_zero]; omega
  · intro s hs hok
    rw [ksLinkPh_run C.p _ _ pub sig s (by omega), hs]
    exact ⟨rfl, hok, by simp only [pos]; exact l8⟩
  · exact ksLink_sound C.p (clog2 C.p.ksLog) _ pub (kc (pbB C)) (by omega) hr hDk l7 hB hB2 hK hokE hS hTlk hg
      hhLk haLk

end Lvm.Har
