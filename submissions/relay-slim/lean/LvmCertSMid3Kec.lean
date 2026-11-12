-- WP-16b (CERT). New for lvm (O6 link, the Keccak tables): `KS`'s assembled claims
-- (`keccakClaimsE`, `ksOutputClaimsE`) holding on `C_main` give WP-8's `CallerClaims` with WP-14c's
-- accessors. lvm2 S2 (WP S2-CERT): the tape's claims (`tapeClaimsE`) give the ring claim and the
-- tied digest lanes (`tapeClaims_of`), its boundary claims give `BndS` (`bndS_of_tape`).
import LvmCertSMid3Blk
import LvmChainTablePad
import LvmVEqParse

/-!
# The Keccak tables' claims

* **`tapeClaims_of`** (lvm2 S2): the tape's ring claim on `C_main` and `D̃_l(r) = a_l`;
* **`bndS_of_tape`** (lvm2 S2): `D_{n−1} = h` from T5's claims and the header (`pubX`);
* **`callerClaims_ks`**: `KS`'s ring claim, column claims and tied output lanes.

The helpers (namespace `Kec`): a point claim at `(a, sel(b))` on a block is slot `b`'s extension at
`a` (`holds_split`, after WP-8's `col_split`); the stream's header lanes are the statement's digest
lanes (`lane_hdr`); `pad43`'s lanes are `pad43Lane`'s (`pad43_getD`).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (RetOK)
open Lvm.VEq Finset
open Lvm.NS (colM dD ksCol ksY2 msgM msgX)

namespace Kec

/-! ## Block claims on a slot -/

/-- `selE` is the cube point `bitsE`. -/
theorem selE_eq_bitsE (z m : ℕ) : selE z m = bitsE z m := by
  show LeanVM.Protocol.Verifier.selectorPoint z m = bitsE z m
  rw [LeanVM.Protocol.EndToEnd.Front.selectorPoint_eq_boolPoint]
  induction m generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [LeanVM.Protocol.EndToEnd.Front.boolPoint_succ, bitsE, ih, Nat.testBit_zero]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one z with h0 | h1 <;> simp [*]

/-- A point claim on a block at `(a, sel(b))` is slot `b`'s extension at `a`. -/
theorem holds_split {μ h k off : ℕ} (hal : 2 ^ (h + k) ∣ off) (hfit : off + 2 ^ (h + k) ≤ 2 ^ μ)
    {a : List E} (ha : a.length = h) {b : ℕ} (hb : b < 2 ^ k) {val : E} {q : Column μ}
    (H : StackClaim.Holds μ (BClaim.point ⟨h + k, off⟩ (a ++ selE b k) val).onStack q) :
    ∑ x ∈ range (2 ^ h), eqAt a x * ofK (q.values.getD (off + (x + 2 ^ h * b)) 0) = val := by
  rw [selE_eq_bitsE] at H
  rw [holds_point hal hfit _ (by simp [ha])] at H
  have e := col_split (s := bitsE b k) ha (fun n ↦ ofK (q.values.getD (off + n) 0))
  rw [bitsE_length] at e
  rw [e, sum_eqAt_bitsE hb] at H
  exact H

/-- The ring claim on a block. -/
theorem ringCol_of_holds {μ h off : ℕ} (hal : 2 ^ (h + 6) ∣ off) (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ)
    {q : Column μ} {ring : E × (List E → E)}
    (H : StackClaim.Holds μ (⟨⟨h + 6, off⟩, ring.2, ring.1⟩ : BClaim).onStack q) :
    Lvm.KG.RingColTrue h (fun n ↦ q.values.getD (off + n) 0) ring :=
  ((holds_onStack _ hal hfit q).1 H).symm

/-- A column claim on a block. -/
theorem colTrue_of_holds {μ h off : ℕ} (hal : 2 ^ (h + 6) ∣ off)
    (hfit : off + 2 ^ (h + 6) ≤ 2 ^ μ) {q : Column μ} {c : ColumnClaim}
    (hc : c.column = qkeccak ∧ c.point.length = h + 6)
    (H : StackClaim.Holds μ (BClaim.point ⟨h + 6, off⟩ c.point c.value).onStack q) :
    colTrue h (fun n ↦ q.values.getD (off + n) 0) c :=
  ⟨hc.1, hc.2, ((holds_point hal hfit _ hc.2 _ q).1 H).symm⟩

/-! ## The header's lanes -/

/-- `laneAt` reads its eight bytes. -/
theorem laneAt_shift {b b' : ByteArray} {o o' : ℕ}
    (h : ∀ k < 8, b.get! (o + k) = b'.get! (o' + k)) : laneAt b o = laneAt b' o' := by
  apply UInt64.toNat_inj.mp
  rw [toNat_laneAt, toNat_laneAt]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h i i.isLt]

/-- A digest's lane `m < 4` is the lane of its bytes. -/
theorem blockLane_digestAt (π : ByteArray) (o : ℕ) {m : ℕ} (hm : m < 4) :
    RecursionFast.Keccak.blockLane (digestAt π o).toArray m = laneAt π (o + 8 * m) := by
  have hd : ∀ k < 8, (digestAt π o).toArray.getD (8 * m + k) 0 = π.get! (o + 8 * m + k) := by
    intro k hk
    simp [digestAt, Array.getD, show 8 * m + k < 32 by omega, Nat.add_assoc]
  have h0 := hd 0 (by omega)
  rw [Nat.add_zero, Nat.add_zero] at h0
  rw [RecursionFast.Keccak.blockLane_unfold, h0, hd 1 (by omega), hd 2 (by omega), hd 3 (by omega),
    hd 4 (by omega), hd 5 (by omega), hd 6 (by omega), hd 7 (by omega)]
  simp only [laneAt, UInt64.zero_or, Nat.add_zero]
  rfl

/-- The stream's header byte `j ≥ 8` is the statement's. -/
theorem sig_get (x : List UInt8) {j : ℕ} (hj : 8 ≤ j) (k : ℕ) :
    (sigOfX x).get! (headerAt j + k) =
      (⟨(List.replicate 8 0 ++ x).toArray⟩ : ByteArray).get! (j + k) := by
  have h8 : headerAt 8 = 88 := rfl
  have hj' : headerAt j = 88 + (j - 8) := rfl
  rw [sigOfX, get!_mk, get!_mk, List.getD_append_right, List.getD_append_right]
  · simp only [List.length_replicate]
    congr 1
    omega
  · simp only [List.length_replicate]; omega
  · simp only [List.length_replicate]; omega

/-- A lane of a header digest, from the stream. -/
theorem lane_hdr (x : List UInt8) {j : ℕ} (hj : 8 ≤ j) {m : ℕ} (hm : m < 4) :
    laneAt (sigOfX x) (headerAt j + 8 * m) =
      RecursionFast.Keccak.blockLane (digestAt ⟨(List.replicate 8 0 ++ x).toArray⟩ j).toArray m := by
  rw [blockLane_digestAt _ _ hm]
  refine laneAt_shift fun k _ ↦ ?_
  rw [Nat.add_assoc, sig_get x hj, Nat.add_assoc]

/-- `pad43`'s lanes are `pad43Lane`'s. -/
theorem pad43_getD (d : List FK) {l : ℕ} (hl : l < 25) :
    ((pad43 d).getD l 0).val = Lvm.KG.pad43Lane (fun m ↦ (d.getD m 0).val) l := by
  interval_cases l <;> rfl

/-- `pad43Lane` reads only lanes `0 … 3`. -/
theorem pad43Lane_congr {w w' : ℕ → UInt64} (h : ∀ m < 4, w m = w' m) (l : ℕ) :
    Lvm.KG.pad43Lane w l = Lvm.KG.pad43Lane w' l := by
  by_cases h0 : l = 0
  · simp only [Lvm.KG.pad43Lane, h0, ite_true, h 0 (by norm_num)]
  by_cases h4 : l < 4
  · simp only [Lvm.KG.pad43Lane, h0, h4, ite_true, ite_false, h l h4, h (l - 1) (by omega)]
  · simp only [Lvm.KG.pad43Lane, h0, h4, ite_false, h 3 (by norm_num)]

/-- An entry of a list, with its index, is in its `zipIdx`. -/
theorem getD_mem_zipIdx (L : List FK) {l : ℕ} (hl : l < L.length) : (L.getD l 0, l) ∈ L.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

end Kec

open Kec

/-- `pubX`'s chain length is the header's (`V_S` reads the header's lane of `n` from the stream). -/
theorem pubX_n (x : List UInt8) : (pubX x).n = (hdrOf x).n :=
  congrArg UInt64.toNat (laneAt_shift fun k _ ↦ sig_get x (by norm_num) k)

/-- **The tape's claims** (lvm2 S2, T1 and T4): the ring claim on the whole `C_main` (`h = 18`) and
the tied digest lanes `D̃_l(r) = a_l` on `D`'s slots 0–3. -/
theorem tapeClaims_of (tp : Lvm.KG.TapeOutE) (hr : tp.1.length = 20) (pub : Lvm.Pub) {qm : Column CMain.nu20}
    (h : ∀ b ∈ tapeClaimsE tp pub, StackClaim.Holds CMain.nu20 b.onStack qm) :
    Lvm.KG.RingColTrue 18 (colM qm) tp.2.2.2.d.ring ∧ Lvm.KG.TiedD 20 (dD qm) tp.1 tp.2.1 := by
  have hal : 2 ^ (18 + 6) ∣ 0 := dvd_zero _
  have hfit : 0 + 2 ^ (18 + 6) ≤ 2 ^ 24 := le_of_eq (by norm_num)
  have hal2 : 2 ^ (20 + 2) ∣ 0 := dvd_zero _
  have hfit2 : 0 + 2 ^ (20 + 2) ≤ 2 ^ 24 := by norm_num
  refine ⟨?_, fun l hl ↦ ?_⟩
  · have H := ringCol_of_holds (ring := tp.2.2.2.d.ring) hal hfit
      (h _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))))
    simp only [zero_add] at H
    exact H
  · have H := holds_split (h := 20) (k := 2) hal2 hfit2 hr (b := l) (by omega)
      (h _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩))))
    simp only [zero_add] at H
    simp only [stepMle, dD, Lvm.KG.dOf, colM, Lvm.NS.wd, Nat.mul_zero, Nat.add_zero]
    exact H

/-- **T5's boundary claims** give `BndS` (`D̃_l(bits(n − 1)) = h_l`, the header's `n`, `h`). -/
theorem bndS_of_tape (x : List UInt8) (tp : Lvm.KG.TapeOutE) {qm : Column CMain.nu20}
    (h : ∀ b ∈ tapeClaimsE tp (pubX x), StackClaim.Holds CMain.nu20 b.onStack qm) : BndS x qm := by
  intro hn m hm
  have hal2 : 2 ^ (20 + 2) ∣ 0 := dvd_zero _
  have hfit2 : 0 + 2 ^ (20 + 2) ≤ 2 ^ 24 := by norm_num
  have hN : (pubX x).n = (hdrOf x).n := pubX_n x
  have hH : ∀ m < 4, ((pubX x).h.getD m 0).val =
      RecursionFast.Keccak.blockLane (hdrOf x).h.toArray m := by
    intro m hm
    show (((List.range 4).map fun i ↦ kAt (sigOfX x) (headerAt 120 + 8 * i)).getD m 0).val = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
    exact lane_hdr x (by norm_num) hm
  have hlenH : (pubX x).h.length = 4 := by simp [pubX, pubOf]
  have hmem : BClaim.point dBlkE (selE ((pubX x).n - 1) 20 ++ selE m 2)
      (M3.kE ((pubX x).h.getD m 0)) ∈ tapeClaimsE tp (pubX x) :=
    List.mem_append_right _ (List.mem_map.2 ⟨_, getD_mem_zipIdx _ (by omega), rfl⟩)
  have hlt : (pubX x).n - 1 < 2 ^ 20 := by rw [hN]; omega
  have H := holds_split (h := 20) (k := 2) hal2 hfit2 (by simp [selE_eq_bitsE]) (b := m)
    (by omega) (h _ hmem)
  rw [selE_eq_bitsE, sum_eqAt_bitsE hlt, zero_add] at H
  have H' := Lvm.KG.ofK_injective H
  rw [hN] at H'
  simp only [dD, Lvm.KG.dOf, colM, Lvm.NS.wd, Nat.mul_zero, Nat.add_zero]
  rw [H', ← hH m hm]
  rfl

/-- **`KS`'s caller claims** (ring, column claims, all 25 output lanes tied). -/
theorem callerClaims_ks (co : CallerOut) (hr : co.1.length = 15)
    (hcol : ∀ c ∈ co.2.2.1.1, c.column = qkeccak ∧ c.point.length = 21) {qm : Column CMain.nu20}
    {qr : Column 19} (hk : ∀ b ∈ keccakClaimsE ksBlk co, StackClaim.Holds CMain.nu20 b.onStack qm)
    (ho : ∀ e ∈ ksOutputClaimsE co.1 co.2.1, HoldsC qm qr e) :
    Lvm.KG.CallerClaims 15 25 (ksCol qm) (Lvm.KG.ksY 15 ksY2 (colM qm) (ksCol qm)) co := by
  have hal : 2 ^ (15 + 6) ∣ CMain.ksOff20 := ⟨2, by decide⟩
  have hfit : CMain.ksOff20 + 2 ^ (15 + 6) ≤ 2 ^ 24 := by decide
  refine ⟨ringCol_of_holds (ring := co.2.2.2) hal hfit
      (hk _ (List.mem_append_right _ (List.mem_singleton_self _))),
    fun c hc ↦ colTrue_of_holds hal hfit (hcol c hc)
      (hk _ (List.mem_append_left _ (List.mem_map_of_mem hc))), fun l hl ↦ ?_⟩
  have H : StackClaim.Holds CMain.nu20
      (BClaim.point (ksYPartE l co.1).1 (ksYPartE l co.1).2 (co.2.1.getD l 0)).onStack qm :=
    ho _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)
  unfold stepMle Lvm.KG.ksY
  by_cases h14 : l < 14
  · simp only [ite_eq_left h14]
    have e : ksYPartE l co.1 = (⟨15 + slotLog, CMain.ksOff20⟩, co.1 ++ selE (50 + l) slotLog) :=
      ite_eq_left h14
    rw [e] at H
    exact holds_split (h := 15) (k := 6) hal hfit hr (by omega) H
  · simp only [ite_eq_right h14]
    have e : ksYPartE l co.1 = (⟨15, ksY2Off + (l - 14) * 2 ^ 15⟩, co.1) := ite_eq_right h14
    rw [e] at H
    have hal' : 2 ^ 15 ∣ ksY2Off + (l - 14) * 2 ^ 15 :=
      Nat.dvd_add ⟨6 * 2 ^ 5, by norm_num [ksY2Off]⟩ (Nat.dvd_mul_left _ _)
    have hfit' : ksY2Off + (l - 14) * 2 ^ 15 + 2 ^ 15 ≤ 2 ^ 24 := by
      simp only [ksY2Off]; norm_num; omega
    exact (holds_point hal' hfit' _ hr _ qm).1 H

end Lvm.ASM
