-- New for lvm (WP-14a, H3): the top-level value refinement: V_S's whole decision (`decideProg` at
-- `M3.real P20`) refines `P_S` (`Lvm.ASM.PSWith (midS tabs) x`) on the stream, phase by phase.
import LvmVEqLink
import LvmVEqTape
import LvmVEqWire
import LvmVEqParse
import LvmVEqKec
import LvmVEqBus
import LvmVEqWhir
import LvmCertS
import LvmAccNodeFold

/-!
# V_S refines `P_S`

`decideProg P20 (M3.real P20 tabs) vk c` is, by the monad laws, `dTop`: the stream read (native
only), the two caps, the middle phases `dMid` (phases 2–7, grouped as `midS`: `dBusTab` with A23's
phase 3b, then `dKg` grouped as `kgProgS`) returning `dClaims` and the accumulator, then `dOpen`
(`decideProg_dTop`). A23: the refinement is under the promise that the accumulator passes `AccOk`
(`RefAtP`; V_S checks it after the run, the language in phase 3b: `LvmAccNodeFold.ref_busTabAcc`). Against
`PSWith (midS tabs) x`: the caps by `ref_skip` (`commitRootUd cfgMain24G/cfgRec20G` read the caps of
`(19, 64)` and `(15, 64)`, `32 · 2^8` and `32 · 2^7` bytes), phases 2–3 by H1's `ref_busTab`,
phases 4/6 by H2's `ref_dKec`, (lvm2 S2) phases 4–5 by `ref_dTapeW` (`ref_dTape`, `ref_dWire`), phase 7 by `ref_dKsLink`; the native claim list
`dClaims` is `CRel`-related to `assembleS`'s list (`dClaims_rel`), so `on_rel` relates the two
openings' stack claims, and the openings refine by H4's `ref_dOpen` (`ref_decideOf` takes it as a
hypothesis; `ref_decide` instantiates it).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Lk
open LeanVM.Protocol.Whir.Sound (cfgRec20G cfgMain24G cfgMain24J)

/-! ## `decideProg` grouped as `P_S` -/

/-- The native result of a Keccak phase (`dKec`). -/
abbrev KecN : Type := List FE × List FE × Lvm.KeccakOut × (FE × (List FE → FE))

/-- Phases 2–3b (A23: the table phase's evaluations, then phase 3b's folded accumulator). -/
def dBusTab (p : Params) (m : M3) (pub : Pub) :
    DM (((List FE × BusOut) × List (List FE × List FE)) × Acc) :=
  (dBus p m pub >>= fun pb ↦ dTab p m pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) >>= fun bt ↦
    accFold p m pub bt.2 >>= fun acc ↦ pure (bt, acc)

/-- Phases 4–7, grouped as `kgProgS` (lvm2 S2: the tape and the wire, then `KS` and its link). -/
def dKg (p : Params) (m : M3) (pub : Pub) :
    DM ((TapeRes × WireOut) × (KecN × List (Com × BlockClaim))) :=
  (dTape p.logN >>= fun tp ↦ dRange p pub >>= fun _ ↦ dWire p pub tp.claim >>= fun wo ↦
      pure (tp, wo)) >>= fun tw ↦
    (dKec p.ksLog >>= fun ks ↦ dKsLink p m ks.1 pub >>= fun klc ↦ pure (ks, klc)) >>= fun ksN ↦
      pure (tw, ksN)

/-- Phases 2–7, their claims and phase 3b's accumulator, grouped as `midS`. -/
def dMid (p : Params) (m : M3) (pub : Pub) : DM (List (Com × BlockClaim) × Acc) :=
  dBusTab p m pub >>= fun bt ↦ dKg p m pub >>= fun kg ↦
    pure (dClaims m p pub bt.1.1.2 bt.1.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2, bt.2)

/-- `decideProg` grouped as `P_S` (its value: phase 3b's accumulator). -/
def dTop (p : Params) (m : M3) (vk c : Vector UInt8 32) : DM Acc :=
  MonadReader.read >>= fun sig ↦
    DM.skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap) >>= fun _ ↦
    DM.skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap) >>= fun _ ↦
    dMid p m (pubOf vk c sig) >>= fun r ↦ dOpen p r.1 >>= fun _ ↦ pure r.2

theorem decideProg_dTop (p : Params) (m : M3) (vk c : Vector UInt8 32) :
    decideProg p m vk c = dTop p m vk c := by
  rw [decideProg_eq]
  simp only [decidePhases, dTop, dMid, dBusTab, dKg, dCommit, bind_assoc, pure_bind]

/-! ## `MonoD` -/

theorem monoD_dKg (p : Params) (m : M3) (pub : Pub) : MonoD (dKg p m pub) :=
  ((monoD_dTape _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_dWire _ _ _).bind fun _ ↦
    MonoD.pure _).bind fun _ ↦
    ((monoD_dKec _).bind fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
      MonoD.pure _

theorem monoD_dMid (p : Params) (m : M3) (pub : Pub) : MonoD (dMid p m pub) :=
  ((monoD_busTab p m pub).bind fun _ ↦ (monoD_accFold _ _ _ _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
    (monoD_dKg p m pub).bind fun _ ↦ MonoD.pure _

/-! ## The claims -/

/-- The native tape and wire against the tape caller's output (lvm2 S2). -/
def TapeWRel (tw : TapeRes × WireOut) (o : Lvm.KG.TapeOutE) : Prop :=
  o.1 = tw.1.r.map FE.toExt3 ∧ o.2.1 = tw.1.v.map FE.toExt3 ∧ o.2.2.1 = kcE tw.1.claim ∧
    WireRel 20 tw.2 o.2.2.2

/-- The native and the language's outputs of phases 4–7. -/
def KgRel (kg : (TapeRes × WireOut) × (KecN × List (Com × BlockClaim))) (kg' : KgOut) : Prop :=
  TapeWRel kg.1 kg'.1 ∧
    (KecRel (11 + 4) kg.2.1 kg'.2.1 ∧
      List.Forall₂ CRel kg.2.2 (ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2))

theorem forall₂_main {l : List BlockClaim} {l' : List BClaim} (h : List.Forall₂ BCRel l l') :
    List.Forall₂ CRel (l.map (.main, ·)) (l'.map (.main, ·)) :=
  forall₂_map_both (h.imp fun _ _ h ↦ ⟨rfl, h⟩)

/-- **The claim list of phases 2–7**: V_S's `dClaims` against `assembleS`'s, claim for claim. -/
theorem dClaims_rel (tabs : Pub → List M3.Tab) (pub : Pub)
    (bt : (List FE × BusOut) × List (List FE × List FE)) (cl : List Verifier.ColumnClaim)
    (hb : bt.1.2.claims = [])
    (ht : List.Forall₂ CRel (M3.tableClaimsR (M3.sumcheckTabs (tabs pub)) bt.2)
      (tableClaimsE (M3.sumcheckTabs (tabs pub)) cl))
    (kg : (TapeRes × WireOut) × (KecN × List (Com × BlockClaim))) (kg' : KgOut)
    (hk : KgRel kg kg') :
    List.Forall₂ CRel (dClaims (M3.real P20 tabs) P20 pub bt.1.2 bt.2 kg.1.1 kg.1.2 kg.2.1 kg.2.2)
      (tableClaimsE (M3.sumcheckTabs (tabs pub)) cl ++
        (tapeClaimsE kg'.1 pub ++ keccakClaimsE ksBlk kg'.2.1).map (.main, ·) ++
        ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1 ++
        ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2) := by
  obtain ⟨⟨hr, hv, -, hw⟩, ⟨hks, hklc⟩⟩ := hk
  have hk1 := hks.1
  have hk2 := hks.2.1
  unfold dClaims
  rw [hb, List.nil_append]
  refine forall₂_append (forall₂_append (forall₂_append ht (forall₂_main
    (forall₂_append (tapeClaims_rel _ _ _ pub hr hv hw.2.2.2.2.1 hw.2.2.2.2.2.1)
      (keccakClaims_rel hks _)))) ?_) hklc
  rw [hk1, hk2]
  exact ksOutputClaims_rel _ _

/-! ## `s` from the statement -/

theorem get!_hdX_x (x : List UInt8) (t : ℕ) :
    (⟨(List.replicate 8 0 ++ x).toArray⟩ : ByteArray).get! (8 + t) = x.getD t 0 := by
  rw [get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

theorem get!_sigOfX_x' (x : List UInt8) (t : ℕ) : (sigOfX x).get! (headerAt 8 + t) = x.getD t 0 := by
  rw [sigOfX, get!_mk, List.getD_append_right _ _ _ _ (by simp), List.length_replicate,
    Nat.add_sub_cancel_left]

/-- **The statement's chain start**: V_S's `s` lanes are the header digest `s`'s (lvm2 S2: the wire
phase's `Pad43(s)`). -/
theorem pubX_s (x : List UInt8) : (pubX x).s = digestLanes (hdX x).s := by
  have e : ∀ i < 4, ∀ j < 8, ((hdX x).s.toArray.getD (8 * i + j) 0) =
      (sigOfX x).get! (headerAt 80 + 8 * i + j) := by
    intro i hi j hj
    rw [Array.getD_eq_getD_getElem?, Vector.getElem?_toArray, Vector.getElem?_eq_getElem (by omega)]
    simp only [hdX, Header.ofProof, digestAt, Vector.getElem_ofFn, Option.getD_some, offS]
    rw [show 80 + (8 * i + j) = 8 + (72 + 8 * i + j) by omega, get!_hdX_x,
      show headerAt 80 + 8 * i + j = headerAt 8 + (72 + 8 * i + j) by simp only [headerAt]; omega,
      get!_sigOfX_x']
  unfold pubX pubOf digestLanes
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.mp hi
  have e0 := e i hi' 0 (by omega)
  simp only [Nat.add_zero] at e0
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl_cons, List.foldl_nil,
    e0, e i hi' 1 (by omega), e i hi' 2 (by omega), e i hi' 3 (by omega),
    e i hi' 4 (by omega), e i hi' 5 (by omega), e i hi' 6 (by omega), e i hi' 7 (by omega), kAt, laneAt,
    UInt64.zero_or, Nat.add_zero, Nat.add_assoc]

/-! ## Refinement -/

section Ref

variable {sig : ByteArray}

theorem dSel_P20 : dSel P20 = 0 := by decide +kernel

theorem dSelBits_P20 : dSelBits P20 = 2 := by decide +kernel

/-- The tape caller as the tape phase, then the wire phase. -/
theorem tapeProg_eq (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    Lvm.KG.tapeProg w sb dsel s n =
      (VerifierProgram.sampleChallenges w >>= fun r ↦ VerifierProgram.readScalars 25 >>= fun v ↦
        KeccakGkr.tapeGkr w r v >>= fun claim ↦ VerifierProgram.ret (r, v, claim)) >>= fun t ↦
      VerifierProgram.require (1 ≤ n ∧ n ≤ 2 ^ w) >>= fun _ ↦
      Lvm.KG.wireChProg w sb dsel s n t.2.2 >>= fun wo ↦ VerifierProgram.ret (t.1, t.2.1, t.2.2, wo) := by
  simp only [Lvm.KG.tapeProg, bind_assoc]
  rfl

/-- **Phases 4–5 refine the tape caller** (lvm2 S2). -/
theorem ref_dTapeW (pub : Pub) (d : RecursionFast.Digest) (hs : pub.s = digestLanes d) :
    Ref20 sig (dTape P20.logN >>= fun tp ↦ dRange P20 pub >>= fun _ ↦ dWire P20 pub tp.claim >>= fun wo ↦
      pure (tp, wo))
      (Lvm.KG.tapeProg 20 2 0 d pub.n) TapeWRel := by
  rw [tapeProg_eq]
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ (monoD_dWire _ _ _).bind fun _ ↦
    MonoD.pure _) (ref_dTape _) ?_
  rintro tp t ⟨h1, h2, -, -, h5, -, -⟩
  refine RefAt.bind (fun _ ↦ (monoD_dWire _ _ _).bind fun _ ↦ MonoD.pure _)
    (RefAt.require fun hc ↦ of_decide_eq_true hc) ?_
  rintro _ _ _
  have hw := ref_dWire (cap := capS) (shp := shpS) (sig := sig) P20 pub tp.claim d hs
  rw [dSel_P20, dSelBits_P20] at hw
  rw [h5]
  refine RefAt.bind (fun _ ↦ MonoD.pure _) hw ?_
  intro wo out hwo
  exact RefAt.pure ⟨h1, h2, rfl, hwo⟩

/-- **Phases 4–7 refine `kgProgS`.** -/
theorem ref_dKg (tabs : Pub → List M3.Tab) (pub : Pub) (d : RecursionFast.Digest)
    (hs : pub.s = digestLanes d) :
    Ref20 sig (dKg P20 (M3.real P20 tabs) pub) (kgProgS d pub.n) KgRel := by
  unfold dKg kgProgS
  refine RefAt.bind (fun _ ↦ ((monoD_dKec _).bind fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦
    MonoD.pure _).bind fun _ ↦ MonoD.pure _) (ref_dTapeW pub d hs) ?_
  intro tw tp htw
  refine RefAt.bind (fun _ ↦ MonoD.pure _)
    (R := fun ksN ks ↦ KecRel (11 + 4) ksN.1 ks.1 ∧
      List.Forall₂ CRel ksN.2 (ksLinkClaimsE ks.2.1 ks.2.2.1 ks.2.2.2)) ?_ ?_
  · refine RefAt.bind (fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦ MonoD.pure _) (ref_dKec _) ?_
    intro ks co hco
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dKsLink tabs ks.1 pub) ?_
    intro klc lo hlo
    exact RefAt.pure ⟨hco, hlo⟩
  intro ksN ks hks
  exact RefAt.pure ⟨htw, hks⟩

/-- **Phases 2–7 refine `midS`** under the promise that phase 3b's folded claim holds: the
openings' stack claims per commitment agree. -/
theorem ref_dMid (tabs : Pub → List M3.Tab) (x : List UInt8) (F : Fit P20 (tabs (pubX x)))
    (hw : ∀ t ∈ M3.sumcheckTabs (tabs (pubX x)), 0 < t.w) :
    RefAtP capS shpS sig (dMid P20 (M3.real P20 tabs) (pubX x)) (midS tabs x)
      (fun r cl ↦
        List.Forall₂ SCRel ((r.1.filter (·.1 == .crec)).map (·.2.onStack)) cl.1 ∧
          List.Forall₂ SCRel ((r.1.filter (·.1 == .main)).map (·.2.onStack)) cl.2)
      (fun r ↦ AccOk P20 (M3.real P20 tabs) (pubX x) r.2 = true) := by
  unfold dMid midS dBusTab
  simp only []
  apply RefAtP.bind (Q := fun bta ↦ AccOk P20 (M3.real P20 tabs) (pubX x) bta.2 = true)
  · exact fun _ ↦ (monoD_dKg _ _ _).bind fun _ ↦ MonoD.pure _
  · exact ref_busTabAcc sig tabs (pubX x) F hw
  · intro bt s h; rw [runD_bind_pure_snd] at h; exact h
  · rintro bt cl ⟨hb, ht, -, -⟩ -
    refine (RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dKg tabs (pubX x) (hdX x).s (pubX_s x)) ?_).toP _
    intro kg kg' hk
    have h := dClaims_rel tabs (pubX x) bt.1 cl hb ht kg kg' hk
    exact RefAt.pure ⟨on_rel h .crec, on_rel h .main⟩

theorem commitRootUd_main : Verifier.commitRootUd cfgMain24G = VerifierProgram.readCommitment 19 64 := rfl

theorem commitRootUd_rec : Verifier.commitRootUd cfgRec20G = VerifierProgram.readCommitment 15 64 := rfl

/-- **V_S refines `P_S`** under the promise that its value (phase 3b's accumulator) passes
`AccOk`, given the openings' refinement (H4's `ref_dOpen`, `monoD_dOpen`). -/
theorem ref_decideOf
    (hO : ∀ (claims : List (Com × Lvm.BlockClaim)) (cl : List VStackClaim × List VStackClaim),
      List.Forall₂ SCRel ((claims.filter (·.1 == .crec)).map (·.2.onStack)) cl.1 →
      List.Forall₂ SCRel ((claims.filter (·.1 == .main)).map (·.2.onStack)) cl.2 →
      Ref20 sig (dOpen P20 claims)
        (Verifier.verifyStackedUd cfgRec20G cl.1 >>= fun _ ↦ Verifier.verifyStackedJ (cfgMain24J 3) cl.2)
        fun _ _ ↦ True)
    (hmO : ∀ claims, MonoD (dOpen P20 claims))
    (tabs : Pub → List M3.Tab) (vk c : RecursionFast.Digest) (x : List UInt8)
    (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (hw : ∀ t ∈ M3.sumcheckTabs (tabs (pubX x)), 0 < t.w) (hpub : pubOf vk c sig = pubX x) :
    RefAtP capS shpS sig (decideProg P20 (M3.real P20 tabs) vk c) (Lvm.ASM.PSWith (midS tabs) x)
      (fun _ b ↦ b = true) (fun a ↦ AccOk P20 (M3.real P20 tabs) (pubX x) a = true) := by
  rw [decideProg_dTop]
  unfold dTop Lvm.ASM.PSWith
  rw [commitRootUd_main, commitRootUd_rec]
  refine RefAtP.read_left ?_
  simp only [hpub]
  -- the caps
  apply RefAtP.bind (Q := fun _ ↦ True)
  · exact fun _ ↦ (monoD_skip _).bind fun _ ↦ (monoD_dMid _ _ _).bind fun _ ↦ (hmO _).bind fun _ ↦
      MonoD.pure _
  · exact (ref_skip (n := nodeBytes * 2 ^ (P20.level ⟨.main, 0⟩).cap) rfl).toP _
  · exact fun _ _ _ ↦ trivial
  intro _ _ _ _
  apply RefAtP.bind (Q := fun _ ↦ True)
  · exact fun _ ↦ (monoD_dMid _ _ _).bind fun _ ↦ (hmO _).bind fun _ ↦ MonoD.pure _
  · exact (ref_skip (n := nodeBytes * 2 ^ (P20.level ⟨.crec, 0⟩).cap) rfl).toP _
  · exact fun _ _ _ ↦ trivial
  intro _ _ _ _
  -- phases 2–7
  apply RefAtP.bind (Q := fun r ↦ AccOk P20 (M3.real P20 tabs) (pubX x) r.2 = true)
  · exact fun _ ↦ (hmO _).bind fun _ ↦ MonoD.pure _
  · exact ref_dMid tabs x (fit_of P20 (tabs (pubX x)) (hfit (pubX x))) hw
  · intro r s h; rw [runD_bind_pure] at h; exact h
  rintro r cl ⟨h1, h2⟩ -
  -- the openings
  have h := RefAt.bind (fun _ ↦ MonoD.pure _) (hO r.1 cl h1 h2)
    fun _ _ _ ↦ RefAt.pure (R := fun (_ : Acc) (b : Bool) ↦ b = true) (b := r.2) (a := true) rfl
  have e : ((Verifier.verifyStackedUd cfgRec20G cl.1 >>= fun _ ↦
      Verifier.verifyStackedJ (cfgMain24J 3) cl.2).bind fun _ ↦ VerifierProgram.ret true) =
      (Verifier.verifyStackedUd cfgRec20G cl.1 >>= fun _ ↦ Verifier.verifyStackedJ (cfgMain24J 3) cl.2 >>=
        fun _ ↦ pure true) := VerifierProgram.bind_assoc _ _ _
  rw [e] at h
  exact h.toP _

/-- **V_S refines `P_S`** (the top-level value refinement): wherever V_S's decision ends with every
check held and its folded claim passes `AccOk` (`decideF`), `PSWith (midS tabs) x` read off the
stream returns `true` at the same cursor. -/
theorem ref_decide (sig : ByteArray) (tabs : Pub → List M3.Tab) (vk c : RecursionFast.Digest)
    (x : List UInt8) (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (hw : ∀ t ∈ M3.sumcheckTabs (tabs (pubX x)), 0 < t.w) (hpub : pubOf vk c sig = pubX x) :
    RefAtP capS shpS sig (decideProg P20 (M3.real P20 tabs) vk c) (Lvm.ASM.PSWith (midS tabs) x)
      (fun _ b ↦ b = true) (fun a ↦ AccOk P20 (M3.real P20 tabs) (pubX x) a = true) :=
  ref_decideOf (fun claims cl h1 h2 ↦ ref_dOpen claims cl h1 h2) (monoD_dOpen P20) tabs vk c x hfit
    hw hpub

end Ref

end Lvm.VEq
