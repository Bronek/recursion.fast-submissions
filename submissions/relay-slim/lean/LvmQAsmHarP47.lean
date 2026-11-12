-- New for lvm (HAR): phases 4–7 of `F` as `PhaseAt` facts from WP-16a's wiring (`phases47`), QA1's
-- `gkr_spec`/`ksLink_sound`, and the reading lemmas of `LvmQAsmHar47`. lvm2 S2 (T-Q): phases 4–5 are the
-- tape (`dTape_spec`) and the wire (`dRange_run`, `wire_spec`).
import LvmQAsmHar47
import LvmQAsmHarTop
import LvmQWireSound
import LvmQEqKeccakTape

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

/-- The `E` constant `k'` from any cell `x` (`x + 1·x + k'`). -/
theorem constE_val' {c : Ctx} {M : Mem} {k' : FK} {x : Cell} {p : Ptr}
    (h : SegsHold c M p (const .E k' x p).2) : (const .E k' x p).1.val M = FE.ofK k' := by
  have e := lin_spec (c := c) (M := M) (p := p) (τ := .E) (k := 1) (k' := k') (a := x) (b := x) h
  show (lin .E 1 k' x x p).1.val M = _
  rw [e, ofK_one, one_mul, CharTwo.add_self_eq_zero, zero_add]

/-- A claim is determined by the cells representing it. -/
theorem rep_unique {P : Nat} {cv : Nat → FE} {C1 C2 : KeccakClaim} {f : Bool} (h1 : Rep P cv C1 f)
    (h2 : Rep P cv C2 f) : C1 = C2 := by
  obtain ⟨v1, m1, p1, w1⟩ := C1
  obtain ⟨v2, m2, p2, w2⟩ := C2
  have e1 := h1.value.symm.trans h2.value
  have e2 := h1.mu.symm.trans h2.mu
  have e3 := h1.point.symm.trans h2.point
  have e4 := h1.weights.trans h2.weights.symm
  simp only at e1 e2 e3 e4
  rw [e1, e2, e3, e4]

/-- **The tape phase as a `PhaseAt` fact** (from `dTape_spec`): the result at the canonical state, tied to the
gadget's cells. -/
theorem tape_phase {c : Ctx} {M : Mem} {pT : Ptr} {P qs : Nat} {inst out : Nat → Cell} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T)
    (hT : Lvm.Q1.tapeEnd P qs + 2 ≤ T) (hh : SegsHold c M pT (tapeGadget P qs inst out b pT).2)
    (ha : SegsAssert M pT (tapeGadget P qs inst out b pT).2) (hb : b.val M = 1) {P4 P5 : Nat}
    (hinst : ((List.range (P + 5)).map fun i => (inst i).val M) = sampAt (feAt sig) P4 (P + 5))
    (hout : ((List.range 25).map fun l => (out l).val M) = scalarsAt (feAt sig) (P4 + 72 * (P + 5) + 40) 25)
    (hqs : 8 * qs - 40 = P4 + 72 * (P + 5) + 600) (hP5 : 8 * Lvm.Q1.tapeEnd P qs - 40 = P5) :
    PhaseAt (dTape (P + 5)) sig P4 P5 (dTape (P + 5) sig ⟨P4, 0, true⟩).1 ∧
    (dTape (P + 5) sig ⟨P4, 0, true⟩).1.r = (List.range (P + 5)).map (fun i => (inst i).val M) ∧
    (dTape (P + 5) sig ⟨P4, 0, true⟩).1.v = (List.range 25).map (fun l => (out l).val M) ∧
    Rep P (fun j => ((tapeGadget P qs inst out b pT).1.cv j).val M) (dTape (P + 5) sig ⟨P4, 0, true⟩).1.claim false := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := dTape_spec hP hq hS hT hh ⟨P4, 0, true⟩ (P0 := P4) (by simp) hinst hout hqs
  refine ⟨fun s hs hok => ?_, a1, a2, a4⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := dTape_spec hP hq hS hT hh s (P0 := P4) hs hinst hout hqs
  refine ⟨?_, (b7 hb).mpr ⟨hok, ha⟩, by simp only [pos]; rw [b5, b6]; omega⟩
  have hcl := rep_unique b4 a4
  generalize (dTape (P + 5) sig s).1 = X at b1 b2 b3 hcl
  generalize (dTape (P + 5) sig ⟨P4, 0, true⟩).1 = Y at a1 a2 a3 hcl
  obtain ⟨xr, xv, xl, xc⟩ := X
  obtain ⟨yr, yv, yl, yc⟩ := Y
  simp only at b1 b2 b3 a1 a2 a3 hcl ⊢
  rw [b1, b2, b3, a1, a2, a3, hcl]

/-- **The wire phase as a `PhaseAt` fact** (from `dRange_run`, `wire_spec`). -/
theorem wire_phase {c : Ctx} {M : Mem} {pW : Ptr} {P qw zE : Nat} {cv : Nat → Cell} {mb sb : List Cell}
    {b : Cell} {sig : ByteArray} {T : Nat} (hq : 5 ≤ qw) (hS : Streamed M sig T)
    (hT : Lvm.Q1.wireEnd P qw + 2 ≤ T) (hzE : M.e zE = 0)
    (hh : SegsHold c M pW (wireGadget P qw cv mb sb b zE pW).2)
    (ha : SegsAssert M pW (wireGadget P qw cv mb sb b zE pW).2) (hb : b.val M = 1)
    (pp : Params) (hlog : pp.logN = P + 5) (pub : Pub) (hn : 1 ≤ pub.n) (hN : pub.n ≤ 2 ^ (P + 5))
    {claim : KeccakClaim} (hR : Rep P (fun j => (cv j).val M) claim false)
    (hmb : vs M mb = (List.range (P + 5)).map (bitF (pub.n - 1))) (hsb : vs M sb = digBitsF pub.s)
    {P5 P6 : Nat} (hP5 : 8 * qw - 40 = P5) (hP6 : 8 * Lvm.Q1.wireEnd P qw - 40 = P6) :
    PhaseAt (wirePh pp pub claim) sig P5 P6 (wirePh pp pub claim sig ⟨P5, 0, true⟩).1 ∧
    (wirePh pp pub claim sig ⟨P5, 0, true⟩).1.sc.1 = vs M (wireGadget P qw cv mb sb b zE pW).1.sigma ∧
    (wirePh pp pub claim sig ⟨P5, 0, true⟩).1.sl.1 = vs M (wireGadget P qw cv mb sb b zE pW).1.tau ∧
    (wirePh pp pub claim sig ⟨P5, 0, true⟩).1.ring =
      ((wireGadget P qw cv mb sb b zE pW).1.ring.target.val M, fun r' => ringWeight
        ((wirePh pp pub claim sig ⟨P5, 0, true⟩).1.sc.1 ++ (wirePh pp pub claim sig ⟨P5, 0, true⟩).1.sl.1 ++
          selectorPoint (dSel pp) (dSelBits pp)) r' (vs M (wireGadget P qw cv mb sb b zE pW).1.ring.cs)) := by
  have hNl : pub.n ≤ 2 ^ pp.logN := by rw [hlog]; exact hN
  have hw : ∀ s : RS, wirePh pp pub claim sig s = dWire pp pub claim sig s := by
    intro s
    show (dRange pp pub >>= fun _ => dWire pp pub claim) sig s = _
    rw [bind_run', dRange_run pp pub sig s hn hNl]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -⟩ :=
    wire_spec hq hS hT hzE hh pp hlog pub hn hN hR hmb hsb ⟨P5, 0, true⟩ (by simp [hP5])
  rw [hw]
  refine ⟨fun s hs hok => ?_, a1, a3, Prod.ext a7 a8⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ :=
    wire_spec hq hS hT hzE hh pp hlog pub hn hN hR hmb hsb s (by simp only [pos] at hs; omega)
  rw [hw]
  refine ⟨?_, by rw [b11 hb ha]; exact hok, by simp only [pos]; rw [b9, b10]; omega⟩
  generalize (dWire pp pub claim sig s).1 = X at b1 b2 b3 b4 b5 b6 b7 b8
  generalize (dWire pp pub claim sig ⟨P5, 0, true⟩).1 = Y at a1 a2 a3 a4 a5 a6 a7 a8
  obtain ⟨⟨xσ, xf⟩, xg, ⟨xτ, xf'⟩, xsv, ⟨xt, xw⟩⟩ := X
  obtain ⟨⟨yσ, yf⟩, yg, ⟨yτ, yf'⟩, ysv, ⟨yt, yw⟩⟩ := Y
  simp only at b1 b2 b3 b4 b5 b6 b7 b8 a1 a2 a3 a4 a5 a6 a7 a8 ⊢
  subst b1 b2 b3 b4 b5 b6 b7 a1 a2 a3 a4 a5 a6 a7
  rw [b8, a8]

/-- The positions of phases 4–7 the wiring assumes (`P4 … P8`: the tape, the wire, `KS`, the `KS` link, the
openings). -/
structure P47Pos (p : Params) (P4 P5 P6 P7 P8 : Nat) : Prop where
  tp0 : P4 + 40 = 8 * aLane p 0
  tp1 : P4 + 72 * p.logN + 40 = 8 * aLane p 1
  tp2 : 8 * aLane p 2 - 40 = P4 + 72 * p.logN + 600
  tp5 : Lvm.Q1.tapeEnd (p.logN - 5) (aLane p 2) = aLane p 3
  w5 : 8 * aLane p 3 - 40 = P5
  w6 : 8 * Lvm.Q1.wireEnd (p.logN - 5) (aLane p 3) - 40 = P6
  ks0 : P6 + 40 = 8 * aLane p 4
  ks1 : kV p.ksLog P6 + 40 = 8 * aLane p 5
  ks2 : kG p.ksLog P6 = 8 * aLane p 6 - 40
  ks7 : 8 * gkrEnd (p.ksLog - 4) (aLane p 6) - 40 + 72 * ringStages = P7
  l7 : P7 + 40 = 8 * aLane p 7
  l8 : ksP2 p P7 + 96 = P8

/-- What phases 4–5 hand to the claims: the tape's result and the wire's, tied to the cells. -/
structure TW (C : QCfg) (M : Mem) (o : P47Out) (pub : Pub) (tp : TapeRes) (wo : WireOut) : Prop where
  r : tp.r = vs M o.r
  v : tp.v = vs M o.v
  rep : Rep (C.p.logN - 5) (fun j => (o.tape.cv j).val M) tp.claim false
  sc : wo.sc.1 = vs M o.wire.sigma
  sl : wo.sl.1 = vs M o.wire.tau
  ring : wo.ring = (o.wire.ring.target.val M,
    fun r' => ringWeight (wo.sc.1 ++ wo.sl.1 ++ selectorPoint (dSel C.p) (dSelBits C.p)) r' (vs M o.wire.ring.cs))
  mb : vs M o.mb = selectorPoint (pub.n - 1) C.p.logN

/-- **Phases 4–7 from `phases47`'s rows and assertions** (gate on): each phase from its start position yields
values tied to the cells (`TW` for the tape and the wire), keeps `ok`, reaches the next start; the `KS` link's
check holds. Hypotheses beyond v1's `KS` ones: Q_sig's bits of `n'` (`hnb`) and `ChildOk`'s range (`hn1`,
`hnN`), the `s'` bit class (`hsb`) and `s`'s header lanes (`hsl`). -/
theorem p47_at (C : QCfg) {c : Ctx} {M : Mem} {ptr : Ptr} {sig : ByteArray} {T : Nat}
    {bf : BusIn → BusOut} {tb : Pub → List TableSpec} {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)}
    {tfv : Pub → List FE → List FE} {tfs : Pub → List (List FE × List FE) → List FE}
    {tpc : Pub → List (List FE × List FE) → Bool} (pub : Pub) {P4 P5 P6 P7 P8 : Nat}
    (hpos : P47Pos C.p P4 P5 P6 P7 P8)
    (hn : 5 ≤ C.p.logN) (hk : 4 ≤ C.p.ksLog) (hr : C.p.recRowsLog < C.p.ksLog)
    (hlay : layOk (C.p.logN - 5) = true) (hlayk : layOk (C.p.ksLog - 4) = true)
    (hq : 5 ≤ aLane C.p 2) (hqw : 5 ≤ aLane C.p 3) (hqk : 5 ≤ aLane C.p 6)
    (hS : Streamed M sig T) (hT : Lvm.Q1.wireEnd (C.p.logN - 5) (aLane C.p 3) + 2 ≤ T)
    (hTk : gkrEnd (C.p.ksLog - 4) (aLane C.p 6) ≤ T)
    (hTr : aLane C.p 0 + 9 * C.p.logN + 2 < T) (hTv : aLane C.p 1 + 3 * 25 + 2 < T)
    (hTrk : aLane C.p 4 + 9 * C.p.ksLog + 2 < T) (hTvk : aLane C.p 5 + 3 * 25 + 2 < T)
    (hD : C.p.logN ≤ 2 ^ clog2 C.p.logN) (hDk : C.p.ksLog ≤ 2 ^ clog2 C.p.ksLog)
    (hTlk : ksQV C.p.ksLog (aLane C.p 7) + 3 * 4 + 3 ≤ T)
    (hB : 1 ≤ spongeBlocks C.p) (hB2 : spongeBlocks C.p ≤ 2 ^ C.p.ksLog) (hK : 2 ^ C.p.recRowsLog + 431 ≤ 2 ^ C.p.ksLog)
    (hokE : ∀ sh : LoopOut, SLok (ksGlueE C.p.ksLog (aLane C.p 7) (ksQV C.p.ksLog (aLane C.p 7)) (spongeBlocks C.p - 1)
      (2 ^ C.p.recRowsLog + 399 + 31) (2 ^ C.p.recRowsLog + 399) (rho'C sh C.p.ksLog) (sh.cell 2 C.p.recRowsLog)
      (sh.cell 5 (C.p.ksLog - 1)) (kc (pbB C))) = true)
    (hnb : ∀ j < C.p.logN, (kc ((sigIn C).bn + 2 + j)).val M = bitE pub.n j) (hn1 : 1 ≤ pub.n)
    (hnN : pub.n ≤ 2 ^ C.p.logN) (hsb : Lvm.Q1.SBitsS M.k (sigIn C).hd (bsB C))
    (hsl : pub.s = (List.range 4).map fun l => M.k ((sigIn C).hd + 9 + l))
    (hg : (kc (pbB C)).val M = 1) (h : Lvm.QSig.Ok c M (phases47 C) ptr)
    (o : P47Out) (ho : (phases47 C ptr).1 = o) (m : M3) (hm : m = M3.ofParts C.p bf tb tcl tfv tfs tpc) :
    ∃ tp wo, PhaseAt (tapePh C.p) sig P4 P5 tp ∧ PhaseAt (wirePh C.p pub tp.claim) sig P5 P6 wo ∧
      TW C M o pub tp wo ∧
    PhaseAt (ksPh C.p) sig P6 P7 (vs M o.rk, vs M o.vk, o.kko.vals M,
      ringAt (feAt sig) (8 * gkrEnd (C.p.ksLog - 4) (aLane C.p 6) - 40) (o.kko.vals M).slicePoint (o.kko.vals M).slices) ∧
    PhaseAt (ksLinkPh C.p m (vs M o.rk) pub) sig P7 P8 (m.ksLink (ksLinkView C.p m (feAt sig) P7 (vs M o.rk) pub)) ∧
    (m.ksLink (ksLinkView C.p m (feAt sig) P7 (vs M o.rk) pub)).1 = true := by
  subst hm
  obtain ⟨hh, ha⟩ := h
  have hO : (phases47 C ptr).1 = o := ho
  simp only [phases47, bind_apply, pure_apply] at hO
  simp only [phases47] at hh ha
  rw [hold_bind] at hh; obtain ⟨hhR, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhV, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhT, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhZ, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhO, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhB, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhW, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhRk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhVk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhGk, hh⟩ := hh
  rw [hold_bind] at hh; obtain ⟨hhLk, -⟩ := hh
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haT, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haW, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨-, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haGk, ha⟩ := ha
  rw [assert_bind] at ha; obtain ⟨haLk, -⟩ := ha
  subst hO
  obtain ⟨e0, e1, e2, e5, w5, w6, k0, k1, k2, k7, l7, l8⟩ := hpos
  have hlog5 : C.p.logN - 5 + 5 = C.p.logN := by omega
  -- the tape
  have hinst : ((List.range (C.p.logN - 5 + 5)).map fun i =>
      ((loadEs (clog2 C.p.logN) (aLane C.p 0) 9 ptr).1.cell 0 i).val M) = sampAt (feAt sig) P4 (C.p.logN - 5 + 5) := by
    rw [hlog5]; unfold sampAt
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [loadEs_val hhR hS (by omega) (by omega)]
    congr 1; omega
  have hout : ((List.range 25).map fun l =>
      ((loadEs 5 (aLane C.p 1) 3 (ptr.adv (loadEs (clog2 C.p.logN) (aLane C.p 0) 9 ptr).2)).1.cell 0 l).val M) =
      scalarsAt (feAt sig) (P4 + 72 * (C.p.logN - 5 + 5) + 40) 25 := by
    rw [hlog5]; unfold scalarsAt
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [loadEs_val hhV hS (by norm_num; omega) (by omega)]
    congr 1; omega
  have T1 := tape_phase (P4 := P4) (P5 := P5) hlay hq hS
    (by rw [e5]; simp only [Lvm.Q1.wireEnd] at hT; omega)
    hhT haT hg hinst hout (by rw [hlog5]; omega) (by rw [e5]; exact w5)
  rw [hlog5] at T1
  obtain ⟨T1a, T1r, T1v, T1c⟩ := T1
  -- the constants and the borrow chain
  have hz0 := constE_val' hhZ
  have ho1 := constE_val' hhO
  rw [Lvm.Loop.QRing.const_out] at hz0 ho1
  simp only [Cell.val, Mem.rd, Ptr.at, ofK_one, ofK_zero] at hz0 ho1
  have hmb := borrow_vs (ho := by rw [Lvm.Loop.QRing.const_out]; exact ho1) hnb hn1 hhB
  -- the wire
  have hsbv : vs M (sbCells C) = digBitsF pub.s := by
    rw [hsl, ← Lvm.Q1.sbits_vals hsb]; simp only [vs, sbCells, List.map_map]; rfl
  have W1 := wire_phase hqw hS hT (by rw [Lvm.Loop.QRing.const_out]; exact hz0) hhW haW hg C.p
    hlog5.symm pub hn1 (by rw [hlog5]; exact hnN) T1c (by rw [hmb, hlog5]; rfl) hsbv w5 w6
  obtain ⟨W1a, W1s, W1t, W1r⟩ := W1
  have KK := kblock_sound hk hlayk hqk hS hTk hTrk hTvk hDk hhRk hhVk hhGk haGk hg P6 k0 k1 k2
  refine ⟨_, _, T1a, W1a, ⟨?_, ?_, T1c, W1s, W1t, W1r, ?_⟩, ?_, ?_, ?_⟩
  · rw [T1r]; simp only [vs, List.map_map]; rfl
  · rw [T1v]; simp only [vs, List.map_map]; rfl
  · rw [hmb, selectorPoint_bits]
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
