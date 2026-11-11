-- New for lvm (WP-14a, H3): the top-level value refinement: V_S's whole decision (`decideProg` at
-- `M3.real P20`) refines `P_S` (`Lvm.ASM.PSWith (midS tabs) x`) on the stream, phase by phase.
import LvmVEqLink
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
`PSWith (midS tabs) x`: the caps by `ref_skip` (`commitRootUd cfgMain20/cfgRec20` read the caps of
`(21, 64)` and `(15, 64)`, `32 · 2^8` and `32 · 2^7` bytes), phases 2–3 by H1's `ref_busTab`,
phases 4/6 by H2's `ref_dKec`, phases 5/7 by `ref_dChLink`/`ref_dKsLink`; the native claim list
`dClaims` is `CRel`-related to `assembleS`'s list (`dClaims_rel`), so `on_rel` relates the two
openings' stack claims, and the openings refine by H4's `ref_dOpen` (`ref_decideOf` takes it as a
hypothesis; `ref_decide` instantiates it).
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Lk
open LeanVM.Protocol.Whir.Sound (cfgRec20 cfgMain20)

/-! ## `decideProg` grouped as `P_S` -/

/-- The native result of a Keccak phase (`dKec`). -/
abbrev KecN : Type := List FE × List FE × Lvm.KeccakOut × (FE × (List FE → FE))

/-- Phases 2–3b (A23: the table phase's evaluations, then phase 3b's folded accumulator). -/
def dBusTab (p : Params) (m : M3) (pub : Pub) :
    DM (((List FE × BusOut) × List (List FE × List FE)) × Acc) :=
  (dBus p m pub >>= fun pb ↦ dTab p m pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) >>= fun bt ↦
    accFold p m pub bt.2 >>= fun acc ↦ pure (bt, acc)

/-- Phases 4–7, grouped as `kgProgS`. -/
def dKg (p : Params) (m : M3) (pub : Pub) :
    DM ((KecN × List (Com × BlockClaim)) × (KecN × List (Com × BlockClaim))) :=
  (dKec p.logN >>= fun ch ↦ dChLink p m ch.1 ch.2.1 pub >>= fun lc ↦ pure (ch, lc)) >>= fun chN ↦
    (dKec p.ksLog >>= fun ks ↦ dKsLink p m ks.1 pub >>= fun klc ↦ pure (ks, klc)) >>= fun ksN ↦
      pure (chN, ksN)

/-- Phases 2–7, their claims and phase 3b's accumulator, grouped as `midS`. -/
def dMid (p : Params) (m : M3) (pub : Pub) : DM (List (Com × BlockClaim) × Acc) :=
  dBusTab p m pub >>= fun bt ↦ dKg p m pub >>= fun kg ↦
    pure (dClaims m p pub bt.1.1.2 bt.1.2 kg.1.1 kg.2.1 kg.1.2 kg.2.2, bt.2)

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
  ((monoD_dKec _).bind fun _ ↦ (monoD_dChLink _ _ _ _ _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
    ((monoD_dKec _).bind fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
      MonoD.pure _

theorem monoD_dMid (p : Params) (m : M3) (pub : Pub) : MonoD (dMid p m pub) :=
  ((monoD_busTab p m pub).bind fun _ ↦ (monoD_accFold _ _ _ _).bind fun _ ↦ MonoD.pure _).bind fun _ ↦
    (monoD_dKg p m pub).bind fun _ ↦ MonoD.pure _

/-! ## The claims -/

/-- The native and the language's outputs of phases 4–7. -/
def KgRel (kg : (KecN × List (Com × BlockClaim)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut) :
    Prop :=
  (KecRel (16 + 4) kg.1.1 kg'.1.1 ∧ List.Forall₂ CRel kg.1.2 (chLinkClaimsE kg'.1.2)) ∧
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
    (kg : (KecN × List (Com × BlockClaim)) × (KecN × List (Com × BlockClaim))) (kg' : KgOut)
    (hk : KgRel kg kg') :
    List.Forall₂ CRel (dClaims (M3.real P20 tabs) P20 pub bt.1.2 bt.2 kg.1.1 kg.2.1 kg.1.2 kg.2.2)
      (tableClaimsE (M3.sumcheckTabs (tabs pub)) cl ++
        ((keccakClaimsE chBlk kg'.1.1 ++ chFixedClaimsE kg'.1.1.1 kg'.1.1.2.1 pub) ++
          keccakClaimsE ksBlk kg'.2.1).map (.main, ·) ++
        chLinkClaimsE kg'.1.2 ++ ksOutputClaimsE kg'.2.1.1 kg'.2.1.2.1 ++
        ksLinkClaimsE kg'.2.2.1 kg'.2.2.2.1 kg'.2.2.2.2) := by
  obtain ⟨⟨hch, hlc⟩, ⟨hks, hklc⟩⟩ := hk
  have hc1 := hch.1
  have hc2 := hch.2.1
  have hk1 := hks.1
  have hk2 := hks.2.1
  unfold dClaims
  rw [hb, List.nil_append]
  refine forall₂_append (forall₂_append (forall₂_append (forall₂_append ht (forall₂_main
    (forall₂_append (forall₂_append (keccakClaims_rel hch _) ?_) (keccakClaims_rel hks _)))) hlc)
    ?_) hklc
  · rw [hc1, hc2]
    exact chFixedClaims_rel tabs _ _ pub
  · rw [hk1, hk2]
    exact ksOutputClaims_rel _ _

/-! ## Refinement -/

section Ref

variable {sig : ByteArray}

/-- **Phases 4–7 refine `kgProgS`.** -/
theorem ref_dKg (tabs : Pub → List M3.Tab) (pub : Pub) :
    Ref20 sig (dKg P20 (M3.real P20 tabs) pub) kgProgS KgRel := by
  unfold dKg kgProgS
  refine RefAt.bind (fun _ ↦ ((monoD_dKec _).bind fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦
    MonoD.pure _).bind fun _ ↦ MonoD.pure _)
    (R := fun chN ch ↦ KecRel (16 + 4) chN.1 ch.1 ∧ List.Forall₂ CRel chN.2 (chLinkClaimsE ch.2))
    ?_ ?_
  · refine RefAt.bind (fun _ ↦ (monoD_dChLink _ _ _ _ _).bind fun _ ↦ MonoD.pure _) (ref_dKec _) ?_
    intro ch co hco
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dChLink tabs ch.1 ch.2.1 pub) ?_
    intro lc lo hlo
    exact RefAt.pure ⟨hco, hlo⟩
  intro chN ch hch
  refine RefAt.bind (fun _ ↦ MonoD.pure _)
    (R := fun ksN ks ↦ KecRel (11 + 4) ksN.1 ks.1 ∧
      List.Forall₂ CRel ksN.2 (ksLinkClaimsE ks.2.1 ks.2.2.1 ks.2.2.2)) ?_ ?_
  · refine RefAt.bind (fun _ ↦ (monoD_dKsLink _ _ _ _).bind fun _ ↦ MonoD.pure _) (ref_dKec _) ?_
    intro ks co hco
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dKsLink tabs ks.1 pub) ?_
    intro klc lo hlo
    exact RefAt.pure ⟨hco, hlo⟩
  intro ksN ks hks
  exact RefAt.pure ⟨hch, hks⟩

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
    refine (RefAt.bind (fun _ ↦ MonoD.pure _) (ref_dKg tabs (pubX x)) ?_).toP _
    intro kg kg' hk
    have h := dClaims_rel tabs (pubX x) bt.1 cl hb ht kg kg' hk
    exact RefAt.pure ⟨on_rel h .crec, on_rel h .main⟩

theorem commitRootUd_main : Verifier.commitRootUd cfgMain20 = VerifierProgram.readCommitment 21 64 := rfl

theorem commitRootUd_rec : Verifier.commitRootUd cfgRec20 = VerifierProgram.readCommitment 15 64 := rfl

/-- **V_S refines `P_S`** under the promise that its value (phase 3b's accumulator) passes
`AccOk`, given the openings' refinement (H4's `ref_dOpen`, `monoD_dOpen`). -/
theorem ref_decideOf
    (hO : ∀ (claims : List (Com × Lvm.BlockClaim)) (cl : List VStackClaim × List VStackClaim),
      List.Forall₂ SCRel ((claims.filter (·.1 == .crec)).map (·.2.onStack)) cl.1 →
      List.Forall₂ SCRel ((claims.filter (·.1 == .main)).map (·.2.onStack)) cl.2 →
      Ref20 sig (dOpen P20 claims)
        (Verifier.verifyStackedUd cfgRec20 cl.1 >>= fun _ ↦ Verifier.verifyStackedUd cfgMain20 cl.2)
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
  have e : ((Verifier.verifyStackedUd cfgRec20 cl.1 >>= fun _ ↦
      Verifier.verifyStackedUd cfgMain20 cl.2).bind fun _ ↦ VerifierProgram.ret true) =
      (Verifier.verifyStackedUd cfgRec20 cl.1 >>= fun _ ↦ Verifier.verifyStackedUd cfgMain20 cl.2 >>=
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
