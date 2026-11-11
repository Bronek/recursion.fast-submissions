-- WP-16b (CERT). New for lvm (O6, the side conditions): every return of V_S phases 4–7 meets
-- `KgRet` (after WP-8's `retOK_verifyKeccak`), and `assembleS`'s claims are multiaffine and at
-- most `2^63` per commitment (the openings' side conditions, `OpenPost`).
import LvmCertSMid3Blk

/-!
# The side conditions

* **`retOK_kgProgS`**: every return of `kgProgS s n` meets `KgRet` (lvm2 S2: `retOK_tapeProg`, then
  `retOK_callerProg`, `retOK_ksLinkProg`; ring weights `Σ_k c_k eq(r^(2^k), ·)` are multiaffine);
* `okC_claimsS`: every assembled claim's block fits its commitment (`τ ≤ 19` on `C_rec`, `≤ 24` on
  `C_main`, from `LayOk` for the tables) with a weight multiaffine on the block;
* **`side_assembleS`**: `assembleS`'s claims are multiaffine, at most `2^63` per commitment, when
  `pub.h` has at most `2^61` lanes (`length_pubX_h`: `pubX`'s has four; `C_main` gets one boundary
  claim per lane of `pub.h`, `length_h_lt_main`, so the bound is needed).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM ksCol ksY2 msgM msgX)

/-! ## The returns of `kgProgS` -/

/-- Two return invariants of one program. -/
theorem retOK_and {α : Type} {P Q : α → Prop} {p : LeanVM.Protocol.Compile.VerifierProgram α}
    (hP : RetOK P p) (hQ : RetOK Q p) : RetOK (fun a ↦ P a ∧ Q a) p :=
  fun l a hl ↦ ⟨hP l a hl, hQ l a hl⟩

/-- A ring switch's weight is multiaffine on any number of coordinates. -/
theorem isMultiaffine_ringWeight (r cs : List E) (n : ℕ) :
    IsMultiaffine n fun y ↦ LeanVM.Protocol.Verifier.ringWeight r y cs := by
  simp only [ringWeight_eq_sum]
  exact IsMultiaffine.sum _ _ fun k _ ↦ (isMultiaffine_eqEvalN _ n).const_mul _

/-- Every weight `ringSwitch` returns is multiaffine. -/
theorem retOK_ringSwitch (point s : List E) :
    RetOK (fun r : E × (List E → E) ↦ ∀ n, IsMultiaffine n r.2)
      (LeanVM.Protocol.Verifier.ringSwitch point s) := by
  unfold LeanVM.Protocol.Verifier.ringSwitch
  exact RetOK.bind_true fun _ ↦ RetOK.ret fun n ↦ isMultiaffine_ringWeight _ _ n

/-- The facts of a return of `callerProg h`. -/
def CallerRet (h : ℕ) (co : CallerOut) : Prop :=
  co.1.length = h ∧ co.2.1.length = 25 ∧
    (∀ c ∈ co.2.2.1.1, c.column = qkeccak ∧ c.point.length = h + 6) ∧ co.2.2.1.1.length ≤ 1 ∧
    ∀ n, IsMultiaffine n co.2.2.2.2

/-- **Every return of `callerProg h`** (`4 ≤ h`) meets `CallerRet h`. -/
theorem retOK_callerProg (h : ℕ) (hh : 4 ≤ h) : RetOK (CallerRet h) (Lvm.KG.callerProg h) := by
  unfold Lvm.KG.callerProg
  refine (retOK_sampleN h).bind fun r hr ↦ (RetOK.readN 25).bind fun v hv ↦
    (retOK_and (retOK_verifyKeccak h r v (hr ▸ hh)) (retOK_verifyKeccak_count h r v)).bind
      fun res hres ↦ (retOK_ringSwitch _ _).bind fun ring hring ↦ RetOK.ret ?_
  exact ⟨hr, hv, fun c hc ↦ hr ▸ hres.1 c hc, hres.2, hring⟩

/-- Every return of the `KS` link: `hk + 5` challenges, `ρ'` has `hk` coordinates. -/
theorem retOK_ksLinkProg (hk r : ℕ) (rows : List ℕ) :
    RetOK (fun lo : List E × (List E × E) × List E ↦ lo.1.length = hk + 5 ∧ lo.2.1.1.length = hk)
      (Lvm.KG.ksLinkProg hk r rows) := by
  unfold Lvm.KG.ksLinkProg
  exact (retOK_sampleN _).bind fun kchal hk' ↦ (retOK_sumcheck _ _ _).bind fun kshift hs ↦
    RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.ret ⟨hk', by simpa using hs⟩

/-- Every return of a slot reduction: its ring weight is multiaffine. -/
theorem retOK_slotProg (b sb blk : ℕ) (W : ℕ → ℕ → E) (pt : List E) (v : E) :
    RetOK (fun o : Lvm.KG.SlotOut ↦ ∀ n, IsMultiaffine n o.ring.2) (Lvm.KG.slotProg b sb blk W pt v) := by
  unfold Lvm.KG.slotProg
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_ringSwitch _ _).bind fun _ hr ↦ RetOK.ret hr

/-- Every return of the chain wiring phase: its ring weight is multiaffine. -/
theorem retOK_wireChProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) (claim : LeanVM.Protocol.Verifier.KeccakClaim) :
    RetOK (fun o : Lvm.KG.WireChOut ↦ ∀ n, IsMultiaffine n o.d.ring.2)
      (Lvm.KG.wireChProg w sb dsel s n claim) := by
  unfold Lvm.KG.wireChProg
  exact RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦ RetOK.bind_true fun _ ↦
    (retOK_slotProg _ _ _ _ _ _).bind fun _ hd ↦ RetOK.ret hd

/-- **Every return of the tape caller** (lvm2 S2): `w` challenges `r`, 25 scalars, a multiaffine ring
weight. -/
theorem retOK_tapeProg (w sb dsel : ℕ) (s : RecursionFast.Digest) (n : ℕ) :
    RetOK (fun tp : Lvm.KG.TapeOutE ↦ tp.1.length = w ∧ tp.2.1.length = 25 ∧
      ∀ n, IsMultiaffine n tp.2.2.2.d.ring.2) (Lvm.KG.tapeProg w sb dsel s n) := by
  unfold Lvm.KG.tapeProg
  exact (retOK_sampleN w).bind fun _ hr ↦ (RetOK.readN 25).bind fun _ hv ↦ RetOK.bind_true fun _ ↦
    RetOK.bind_true fun _ ↦ (retOK_wireChProg _ _ _ _ _ _).bind fun _ hw ↦ RetOK.ret ⟨hr, hv, hw⟩

/-- **Every return of V_S phases 4–7 meets `KgRet`** (lvm2 S2: the tape, then `KS`). -/
theorem retOK_kgProgS (s : RecursionFast.Digest) (n : ℕ) : RetOK KgRet (kgProgS s n) := by
  unfold kgProgS
  refine (retOK_tapeProg 20 2 0 s n).bind fun tp htp ↦
    ((retOK_callerProg _ (by norm_num)).bind fun co hco ↦ (retOK_ksLinkProg _ _ _).bind
      fun lo hlo ↦ RetOK.ret (Q := fun ks : CallerOut × (List E × (List E × E) × List E) ↦
        CallerRet 15 ks.1 ∧ ks.2.1.length = 20 ∧ ks.2.2.1.1.length = 15) ⟨hco, hlo⟩).bind
      fun ks hks ↦ RetOK.ret ?_
  obtain ⟨⟨k1, k2, k3, k4, k5⟩, k6, k7⟩ := hks
  exact ⟨htp, ⟨k1, k2, k3, k4, k5, k6, k7⟩⟩

/-! ## The side conditions of `assembleS` -/

/-- The log-size of a commitment. -/
def nuOf : Com → ℕ
  | .crec => 19
  | .main => 24

/-- An assembled claim's block fits its commitment and its weight is multiaffine on the block. -/
def OkC (e : Com × BClaim) : Prop :=
  e.2.block.variableCount ≤ nuOf e.1 ∧ IsMultiaffine e.2.block.variableCount e.2.weight

/-- A point claim on a block that fits. -/
theorem okC_point (com : Com) (blk : VPlacement) (z : List E) (v : E)
    (h : blk.variableCount ≤ nuOf com) : OkC (com, BClaim.point blk z v) :=
  ⟨h, isMultiaffine_eqEvalN z _⟩

/-- **The table claims** sit on aligned blocks inside their commitment (`LayOk`). -/
theorem okC_tableClaimsE (T : List Lvm.M3.Tab) (cl : List ColumnClaim)
    (hlay : Lvm.M3.LayOk Lvm.M3.lay26 T) : ∀ e ∈ tableClaimsE T cl, OkC e := by
  intro e he
  simp only [tableClaimsE, List.mem_filterMap, Option.bind_eq_some_iff] at he
  obtain ⟨c, -, ji, -, h⟩ := he
  split at h
  · rename_i rec off hcol
    obtain ⟨t, ht, htc⟩ := Option.bind_eq_some_iff.mp hcol
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp htc
    have hal := hlay t (List.mem_of_getElem? ht) ji.2 hi
    simp only [Lvm.M3.Aligned, htc] at hal
    obtain ⟨-, hfit, -⟩ := hal
    cases h
    refine okC_point _ _ _ _ ?_
    simp only [ht, Option.map_some, Option.getD_some]
    cases rec
    · have hp : 2 ^ t.τ ≤ 2 ^ 24 := by
        have h' : off + 2 ^ t.τ ≤ 2 ^ 24 := hfit
        omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp
    · have hp : 2 ^ t.τ ≤ 2 ^ 19 := by
        have h' : off + 2 ^ t.τ ≤ 2 ^ 19 := hfit
        omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp
  · cases h

/-- `sumE` of multiaffine weights is multiaffine. -/
theorem isMultiaffine_sumE {n : ℕ} {γ : Type} (xs : List γ) (F : γ → List E → E)
    (hF : ∀ a ∈ xs, IsMultiaffine n (F a)) :
    IsMultiaffine n fun l ↦ LeanVM.Protocol.Verifier.sumE (xs.map fun a ↦ F a l) := by
  simp only [LeanVM.Protocol.Verifier.sumE, foldl_add_eq, zero_add]
  induction xs with
  | nil => simpa using (IsMultiaffine.zero (n := n))
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF a (List.mem_cons_self ..)).add (ih fun b hb ↦ hF b (List.mem_cons_of_mem _ hb))

/-- **A sum claim's weight is multiaffine** when its parts' blocks fit. -/
theorem isMultiaffine_sumClaimE (nu : ℕ) (parts : List (E × VPlacement × List E)) (value : E)
    (hp : ∀ p ∈ parts, p.2.1.variableCount ≤ nu) :
    IsMultiaffine nu (sumClaimE nu parts value).weight := by
  unfold sumClaimE
  refine isMultiaffine_sumE parts _ fun p hpm ↦ ?_
  obtain ⟨c, blk, z⟩ := p
  have h := (isMultiaffine_onStack (n := nu) ⟨blk, LeanVM.Protocol.Verifier.eqEval z, 0⟩
    (hp _ hpm) (isMultiaffine_eqEvalN z _)).const_mul c
  have e : (fun x ↦ c * blk.eqAbove x *
      LeanVM.Protocol.Verifier.eqEval z (x.take blk.variableCount)) =
      fun r ↦ c * (BClaim.onStack ⟨blk, LeanVM.Protocol.Verifier.eqEval z, 0⟩).1 r :=
    funext fun x ↦ mul_assoc _ _ _
  show IsMultiaffine nu fun x ↦
    c * blk.eqAbove x * LeanVM.Protocol.Verifier.eqEval z (x.take blk.variableCount)
  rw [e]
  exact h

/-- A Keccak table's claims on `C_main`. -/
theorem okC_keccakClaimsE (blk : VPlacement) (co : CallerOut) (hv : blk.variableCount ≤ 24)
    (hr : ∀ n, IsMultiaffine n co.2.2.2.2) : ∀ b ∈ keccakClaimsE blk co, OkC (.main, b) := by
  intro b hb
  simp only [keccakClaimsE, List.mem_append, List.mem_map, List.mem_singleton] at hb
  rcases hb with ⟨c, -, rfl⟩ | rfl
  · exact okC_point _ _ _ _ hv
  · exact ⟨hv, hr _⟩

/-- The tape's claims on `C_main` (lvm2 S2): point claims on `D`'s block, the ring claim on all of
`C_main`. -/
theorem okC_tapeClaimsE (tp : Lvm.KG.TapeOutE) (pub : Lvm.Pub)
    (hr : ∀ n, IsMultiaffine n tp.2.2.2.d.ring.2) : ∀ b ∈ tapeClaimsE tp pub, OkC (.main, b) := by
  intro b hb
  simp only [tapeClaimsE, List.mem_append, List.mem_map, List.mem_singleton] at hb
  rcases hb with (⟨l, -, rfl⟩ | rfl) | ⟨⟨w, l⟩, -, rfl⟩
  · exact okC_point _ _ _ _ (by simp [dBlkE, nuOf])
  · exact ⟨by simp [nuMainE, nuOf], hr _⟩
  · exact okC_point _ _ _ _ (by simp [dBlkE, nuOf])

/-- `KS`'s `Y` lane blocks fit `C_main`. -/
theorem ksYPartE_le (l : ℕ) (pt : List E) : (ksYPartE l pt).1.variableCount ≤ 24 := by
  unfold ksYPartE
  split <;> simp [slotLog, ksBlk]

/-- **Every assembled claim** fits its commitment with a multiaffine weight. -/
theorem okC_claimsS (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim) (kg : KgOut)
    (hlay : Lvm.M3.LayOk Lvm.M3.lay26 T) (hk : KgRet kg) : ∀ e ∈ claimsS T pub cl kg, OkC e := by
  obtain ⟨⟨-, -, hr1⟩, ⟨-, -, -, -, hr2, -, -⟩⟩ := hk
  intro e he
  simp only [claimsS, List.mem_append] at he
  rcases he with ((htab | hm) | hko) | hkl
  · exact okC_tableClaimsE T cl hlay e htab
  · simp only [List.mem_map, List.mem_append] at hm
    obtain ⟨b, hb | hb, rfl⟩ := hm
    · exact okC_tapeClaimsE _ _ hr1 b hb
    · exact okC_keccakClaimsE _ _ (by simp [ksBlk, slotLog]) hr2 b hb
  · simp only [ksOutputClaimsE, List.mem_map] at hko
    obtain ⟨l, -, rfl⟩ := hko
    exact okC_point _ _ _ _ (ksYPartE_le l _)
  · simp only [ksLinkClaimsE, List.mem_cons, List.mem_nil_iff, or_false] at hkl
    rcases hkl with rfl | rfl | rfl | rfl
    · refine ⟨le_rfl, isMultiaffine_sumClaimE _ _ _ fun p hp ↦ ?_⟩
      simp only [List.mem_map] at hp
      obtain ⟨l, -, rfl⟩ := hp
      exact ksYPartE_le l _
    · refine ⟨le_rfl, isMultiaffine_sumClaimE _ _ _ fun p hp ↦ ?_⟩
      simp only [List.mem_map] at hp
      obtain ⟨l, -, rfl⟩ := hp
      simp [sumClaimE, slotLog, ksBlk, nuMainE, CMain.nu20]
    · refine ⟨le_rfl, isMultiaffine_sumClaimE _ _ _ fun p hp ↦ ?_⟩
      simp only [List.mem_map] at hp
      obtain ⟨l, -, rfl⟩ := hp
      simp [sumClaimE, nuMainE, CMain.nu20]
    · refine ⟨le_rfl, isMultiaffine_sumClaimE _ _ _ fun p hp ↦ ?_⟩
      simp only [List.mem_map] at hp
      obtain ⟨l, -, rfl⟩ := hp
      simp [sumClaimE, nuMainE, CMain.nu20]

/-- `C_rec`'s claims: the tables' on it and `mC`. -/
theorem length_crec_le (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim)
    (kg : KgOut) : ((claimsS T pub cl kg).filter (·.1 == .crec)).length ≤ cl.length + 1 := by
  have hmc : (Com.main == Com.crec) = false := rfl
  simp [hmc, claimsS, ksOutputClaimsE, ksLinkClaimsE, List.filter_append,
    List.filter_map, Function.comp_def]
  exact (List.length_filter_le _ _).trans (List.length_filterMap_le _ _)

/-- The number of assembled claims. -/
theorem length_claimsS (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim)
    (kg : KgOut) : (claimsS T pub cl kg).length = (tableClaimsE T cl).length +
      kg.2.1.2.2.1.1.length + pub.h.length + 35 := by
  simp [claimsS, ksOutputClaimsE, ksLinkClaimsE, keccakClaimsE, tapeClaimsE]
  omega

/-- `C_main` holds one claim per lane of `pub.h` (`tapeClaimsE`'s boundary claims), and more. -/
theorem length_h_lt_main (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim)
    (kg : KgOut) : pub.h.length < (assembleS T pub cl kg).2.length := by
  rw [assembleS_eq]
  simp [claimsS, ksOutputClaimsE, ksLinkClaimsE, keccakClaimsE, tapeClaimsE,
    List.filter_append, List.filter_map, Function.comp_def]
  omega

/-- **`assembleS`'s side conditions**, when `pub.h` has at most `2^61` lanes. -/
theorem side_assembleS (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim)
    (kg : KgOut) (hlay : Lvm.M3.LayOk Lvm.M3.lay26 T) (hret : TabRet T cl)
    (hn : (T.map (·.w)).sum ≤ 2 ^ 62) (hk : KgRet kg) (hh : pub.h.length ≤ 2 ^ 61) :
    (∀ c ∈ (assembleS T pub cl kg).1, IsMultiaffine 19 c.1) ∧
    (∀ c ∈ (assembleS T pub cl kg).2, IsMultiaffine CMain.nu20 c.1) ∧
    (assembleS T pub cl kg).1.length ≤ 2 ^ 63 ∧ (assembleS T pub cl kg).2.length ≤ 2 ^ 63 := by
  have hok := okC_claimsS T pub cl kg hlay hk
  have hcl := hret.2
  have hk2 := hk.2.2.2.2.1
  rw [assembleS_eq]
  refine ⟨fun c hc ↦ ?_, fun c hc ↦ ?_, ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    obtain ⟨he, hcom⟩ := List.mem_filter.mp he
    obtain ⟨hv, hw⟩ := hok e he
    obtain ⟨com, b⟩ := e
    cases com
    · cases hcom
    · exact isMultiaffine_onStack b hv hw
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    obtain ⟨he, hcom⟩ := List.mem_filter.mp he
    obtain ⟨hv, hw⟩ := hok e he
    obtain ⟨com, b⟩ := e
    cases com
    · exact isMultiaffine_onStack b hv hw
    · cases hcom
  · rw [List.length_map]
    have := length_crec_le T pub cl kg
    omega
  · rw [List.length_map]
    have h1 := List.length_filter_le (·.1 == Com.main) (claimsS T pub cl kg)
    have h2 := length_claimsS T pub cl kg
    have h4 : (tableClaimsE T cl).length ≤ cl.length := List.length_filterMap_le _ _
    omega

/-- `pubX`'s chain end has four lanes. -/
theorem length_pubX_h (x : List UInt8) : (pubX x).h.length = 4 := by
  simp [pubX, Lvm.pubOf]

end Lvm.ASM
