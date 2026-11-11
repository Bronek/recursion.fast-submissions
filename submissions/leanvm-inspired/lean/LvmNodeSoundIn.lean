-- WP-14c (NodeSound, O10). New for lvm: the input map (A19) from input arrays. Committed bundles
-- of strided `K` arrays (H4's `inKOf_com`) and the header's public array (WP-9b's `inKOf_pub`, INT-2's
-- `pubArr`) give `InMapN`'s value fields on the interpreter's memory (WP-10/QL `toProgram_interp`'s
-- `Inputs`).
import LvmNodeSoundMain
import LvmCertSNodeIn

/-!
# The input map from the input arrays

* **`memN_inK`**: under `AuxHyps`, an input cell of the interpreter's memory is the input read off
  the stack (`inKOf`).
* **`Bundle arrs s τ base rec off`**: for every `l < s` a committed `K` array of height `2^τ`, first
  cell `base + l`, stride `s`, value column at word `off l` of commitment `rec`. **`bundle_cells`**:
  its cell `base + j` (`j < s·2^τ`) is word `off (j % s) + j / s` (from `inKOf_com`).
* The fields: **`stream_cells`** (a 17-bundle on `C_rec`, `off l = l·2^14`: the stream lanes `laneK`),
  **`hd_cells`**, **`sg_cells`** (`σ'`: a 1-bundle at `C_rec` word `17·2^14`), **`xs_cells`** (a 17-bundle
  on `C_main` at `CMain.xOff20 + l·2^14`: `msgX`), **`y_cells`** (`ys`/`yc`/`yls`/`yns`: a 4-bundle over
  `KS` rows `[2^14, 2^14 + 2^9)`, `off l = 50·2^20 + 2^15·(50+l) + 2^14`), **`md_cells`** (a 4-bundle of
  height 1 at `KS` row `B − 1`).
* **`PUB`** (`hdrLanes x`: the header's 702 lanes from byte 8, V-computable from π): **`pub_cells`**,
  then **`flag_cell`**, **`vk_cells`**, **`cL_cells`**, **`sl_cells`** for `I.flag = pb`, `I.vk = pb + 1`,
  `I.cL = pb + 5`, `I.sl = pb + 18`.

All shapes above are aligned (`2^τ ∣ off`), as `LayOk` asks.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay Lvm.Loop Lvm.Loop.Build Lvm.QLink Lvm.QSig Lvm.M3
open LeanVM.Parameters LeanVM.Protocol

/-! ## Words of the commitments -/

theorem wd_eq {n : ℕ} (q : Column n) {i : ℕ} (hi : i < 2 ^ n) : wd q i = q.values[i] := by
  rcases q with ⟨v⟩
  show Vector.getD v i 0 = v[i]
  unfold Vector.getD
  rw [Array.getD_eq_getD_getElem?]
  simp only [Vector.getElem?_toArray]
  rw [Vector.getElem?_eq_getElem hi]
  rfl

theorem comCell_rec {L : Lay} (qm : Column L.nuMain) (qr : Column L.nuRec) {n : ℕ} (hn : n < 2 ^ L.nuRec) :
    comCell L qm qr true n = wd qr n := by
  simp [comCell, hn, wd_eq qr hn]

theorem comCell_main {L : Lay} (qm : Column L.nuMain) (qr : Column L.nuRec) {n : ℕ}
    (hn : n < 2 ^ L.nuMain) : comCell L qm qr false n = wd qm n := by
  simp [comCell, hn, wd_eq qm hn]

/-! ## Bundles of committed arrays -/

/-- **An `s`-bundle of committed `K` input arrays**: for `l < s`, an array of height `2^τ`, first
cell `base + l`, stride `s`, value column at word `off l` of commitment `rec`. -/
def Bundle (arrs : List InArr) (s τ base : ℕ) (rec : Bool) (off : ℕ → ℕ) : Prop :=
  ∀ l < s, ∃ k, ∃ hk : k < arrs.length, arrs[k].ty = .K ∧ arrs[k].pub = none ∧ arrs[k].τ = τ ∧
    arrs[k].base = base + l ∧ arrs[k].stride = s ∧ arrs[k].val = [(rec, off l)]

section Gen

variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **A bundle's cells** are the commitment's words. -/
theorem bundle_cells (hok : InOk Q arrs) (hlay : LayOk L (lvmTabs Q pl groups arrs aux))
    (qm : Column L.nuMain) (qr : Column L.nuRec) {s τ base : ℕ} {rec : Bool} {off : ℕ → ℕ}
    (hb : Bundle arrs s τ base rec off) {j : ℕ} (hj : j < s * 2 ^ τ) :
    base + j < Q.nInK ∧ (inKOf Q pl groups arrs aux L hτ (stackOf L qm qr)).getD (base + j) 0 =
      FK.ofBF64 (comCell L qm qr rec (off (j % s) + j / s)) := by
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hj
    · exact h
  obtain ⟨k, hk, hty, hpub, hτk, hbase, hstr, hval⟩ := hb (j % s) (Nat.mod_lt _ hs)
  have hx : j / s < 2 ^ arrs[k].τ := by rw [hτk]; exact Nat.div_lt_of_lt_mul hj
  have e : base + j = arrs[k].base + arrs[k].stride * (j / s) := by
    rw [hbase, hstr]; have := Nat.mod_add_div j s; omega
  refine ⟨?_, ?_⟩
  · have := hok.lt _ (List.getElem_mem hk) (j / s) hx
    rw [hty] at this; rw [e]; exact this
  · rw [e]; exact inKOf_com Q pl groups arrs aux L hτ hok hlay qm qr hk hty hpub hval hx

end Gen

/-! ## The interpreter's input cells -/

section Mem

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab} {L : Lay}
  {hτ : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, t.τ ≤ L.μ}

/-- **An input cell of the interpreter's memory is the input read off the stack.** -/
theorem memN_inK {q : Column L.μ} (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    {n : ℕ} (hn : n < nK) :
    (memN lay I qa nK nE pl groups arrs aux L hτ q).k n =
      (inKOf (Qn lay I qa nK nE) pl groups arrs aux L hτ q).getD n 0 := by
  have hsz := And.intro (inKOf_size (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
    (inEOf_size (Qn lay I qa nK nE) pl groups arrs aux L hτ q)
  obtain ⟨-, -, hin⟩ := toProgram_interp nK nE (qprog lay I qa) H.wf _ _ hsz H.inj H.inb
  exact hin.1 n hn

/-- A bundle's cells in the interpreter's memory. -/
theorem memN_bundle {qm : Column L.nuMain} {qr : Column L.nuRec}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux L hτ (stackOf L qm qr))
    (hlay : LayOk L (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux)) {s τ base : ℕ} {rec : Bool}
    {off : ℕ → ℕ} (hb : Bundle arrs s τ base rec off) {j : ℕ} (hj : j < s * 2 ^ τ) :
    (memN lay I qa nK nE pl groups arrs aux L hτ (stackOf L qm qr)).k (base + j) =
      FK.ofBF64 (comCell L qm qr rec (off (j % s) + j / s)) := by
  obtain ⟨hlt, hv⟩ := bundle_cells _ pl groups arrs aux L hτ H.inOk hlay qm qr hb hj
  rw [memN_inK H hlt]; exact hv

end Mem

/-! ## The fields (on the pair's stack `stackOf lay26 qm qr`) -/

section Fields

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrs : List InArr} {aux : List Tab}
  {hτ : ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups arrs aux, t.τ ≤ lay26.μ}
  {qm : Column CMain.nu20} {qr : Column 19}

/-- The stream lanes of the child, as lanes. -/
theorem laneK_wsOf (qr : Column 19) {j : ℕ} (hj : j < 17 * 2 ^ 14) :
    laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j = FK.ofBF64 (wd qr (Lvm.X.crecIdx j)) := by
  simp only [laneK, wsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Lvm.X.laneOf, wOfCol, FK.ofBF64, wd]

/-- **The stream** (a 17-bundle on `C_rec`, column `l` at word `l·2^14`): lane `j` of the child. -/
theorem stream_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux)) {sb : ℕ}
    (hb : Bundle arrs 17 14 sb true fun l => l * 2 ^ 14) {j : ℕ} (hj : j < 17 * 2 ^ 14) :
    (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (sb + j) =
      laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) j := by
  rw [memN_bundle H hlay hb hj, laneK_wsOf qr hj, comCell_rec (L := lay26) qm qr (by show _ < 2 ^ 19; omega)]
  rfl

/-- **The child header's cells** are the stream's lanes `11 …` (`I.hd = sb + 11`). -/
theorem hd_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux)) {sb : ℕ}
    (hb : Bundle arrs 17 14 sb true fun l => l * 2 ^ 14) (hhd : I.hd = sb + 11) :
    ∀ k < 615, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.hd + k) =
      laneK (wsOf (Lvm.X.laneOf (wOfCol qr))) (11 + k) := fun k hk => by
  rw [hhd, Nat.add_assoc]; exact stream_cells H hlay hb (by omega)

/-! ### Digests and signatures from lanes -/

theorem byteW_toBitVec {u : UInt64} {w : Word} (h : u.toBitVec = w) {t : ℕ} (ht : t < 8) :
    Lvm.Bits.byteW u t = (wordsBytes [w]).getD t 0 := by
  have e := byte_of_lane [w] 0 t ht
  simp only [Nat.mul_zero, Nat.zero_add] at e
  rw [e, Lvm.Wots.byteW_toNat _ ht, ← RecursionFast.toUInt8_mod]
  simp [lw, ← h]

/-- **Four cells whose words are `f c … f (c+3)` hold the digest `digW (wsAt f c 4)`.** -/
theorem digAt_eq_digW {v : ℕ → FK} {a : ℕ} {f : ℕ → Word} {c : ℕ}
    (h : ∀ l < 4, (v (a + l)).val.toBitVec = f (c + l)) : digAt v a = Lvm.X.digW (Lvm.X.wsAt f c 4) := by
  refine Vector.ext fun i hi => ?_
  rw [digAt, Lvm.Wots.digOfW_get _ hi]
  simp only [Lvm.X.digW, Vector.getElem_ofFn]
  have hq : i / 8 < 4 := by omega
  have h8 : i % 8 < 8 := Nat.mod_lt _ (by omega)
  conv_rhs => rw [show i = 8 * (i / 8) + i % 8 by omega]
  rw [byte_of_lane _ _ _ h8, Lvm.Wots.byteW_toNat _ h8, ← RecursionFast.toUInt8_mod]
  have hw : (Lvm.X.wsAt f c 4).getD (i / 8) 0 = f (c + i / 8) := by
    simp [Lvm.X.wsAt, List.getD_eq_getElem?_getD, hq]
  have hv : (v (a + i / 8)).val.toNat = (f (c + i / 8)).toNat := by rw [← h _ hq]; rfl
  rw [hv, lw, hw]

/-- **Cells whose words are `f 0 … f 596` hold the signature `sigOfF f`.** -/
theorem sigAt'_eq_sigOfF {v : ℕ → FK} {a : ℕ} {f : ℕ → Word}
    (h : ∀ j < 597, (v (a + j)).val.toBitVec = f j) : sigAt' v a = Lvm.X.sigOfF f := by
  have h0 := h 0 (by omega)
  rw [Nat.add_zero] at h0
  have e1 : (v a).val.toNat = (f 0).toNat := by rw [← h0]; rfl
  have e2 : ((List.range wotsLen).map fun i => digAt v (a + 1 + 4 * i)) =
      (List.range wotsLen).map fun k => Lvm.X.digW (Lvm.X.wsAt f (1 + 4 * k) 4) := by
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 133 := by simpa [wotsLen] using List.mem_range.mp hi
    exact digAt_eq_digW fun l hl => by
      rw [show a + 1 + 4 * i + l = a + (1 + 4 * i + l) by omega]; exact h _ (by omega)
  have e3 : ((List.range sigHeight).map fun t => digAt v (a + 533 + 4 * t)) =
      (List.range sigHeight).map fun k => Lvm.X.digW (Lvm.X.wsAt f (1 + 4 * wotsLen + 4 * k) 4) := by
    refine List.map_congr_left fun t ht => ?_
    have ht' : t < 16 := by simpa [sigHeight] using List.mem_range.mp ht
    refine digAt_eq_digW fun l hl => ?_
    rw [show a + 533 + 4 * t + l = a + (533 + 4 * t + l) by omega, h _ (by omega)]
    congr 1
  unfold sigAt' Lvm.X.sigOfF
  rw [e1, e2, e3]

/-- **`σ'`'s cells** (a 1-bundle at `C_rec` word `17·2^14`) hold `C_rec`'s column 17. -/
theorem sg_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux))
    (hb : Bundle arrs 1 10 I.sg true fun _ => 17 * 2 ^ 14) :
    sigAt' (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.sg =
      Lvm.X.sigOfF (Lvm.X.sigCol (wOfCol qr)) := by
  refine sigAt'_eq_sigOfF fun j hj => ?_
  rw [memN_bundle H hlay hb (by omega)]
  simp only [Nat.div_one]
  rw [comCell_rec (L := lay26) qm qr (by show _ < 2 ^ 19; omega)]
  rfl

/-- **`KS`'s `X` message cells** (a 17-bundle on `C_main` at `CMain.xOff20 + l·2^14`). -/
theorem xs_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux))
    (hb : Bundle arrs 17 9 I.xs false fun l => CMain.xOff20 + l * 2 ^ 14) :
    ∀ r < 449, ∀ l < 17,
      (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.xs + 17 * r + l) =
        FK.ofBF64 (msgX qm r l) := fun r hr l hl => by
  have hm : (17 * r + l) % 17 = l := by omega
  have hd : (17 * r + l) / 17 = r := by omega
  rw [Nat.add_assoc, memN_bundle H hlay hb (by omega), hm, hd,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 24; simp only [CMain.xOff20]; omega)]
  rfl

/-- `KS`'s output lane `l < 4` of row `i` is the `C_main` word `4·2^20 + 2^15·(50+l) + i` (lvm2 S2). -/
theorem Yq_eq (qm : Column CMain.nu20) (i : ℕ) {l : ℕ} (hl : l < 4) :
    Yq qm i l = wd qm (CMain.ksOff20 + 2 ^ 15 * (50 + l) + i) := by
  simp only [Yq, Lvm.KG.ksYRow, Lvm.KG.ksY, if_pos (show l < 14 by omega), ksCol]
  congr 1; ring

/-- The `Y` bundle's cells: row `2^14 + r` (`r < 2^9`). -/
theorem y_cell
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux)) {yb : ℕ}
    (hb : Bundle arrs 4 9 yb false fun l => CMain.ksOff20 + 2 ^ 15 * (50 + l) + 2 ^ 14) {r l : ℕ}
    (hr : r < 2 ^ 9) (hl : l < 4) :
    (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (yb + 4 * r + l) =
      FK.ofBF64 (Yq qm (2 ^ 14 + r) l) := by
  have hm : (4 * r + l) % 4 = l := by omega
  have hd : (4 * r + l) / 4 = r := by omega
  rw [Nat.add_assoc, memN_bundle H hlay hb (by omega), hm, hd,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 24; simp only [CMain.ksOff20]; omega), Yq_eq qm _ hl]
  congr 2; ring

/-- **`KS`'s digest cells** (`ys`, `yc`, `yls`, `yns` from one 4-bundle over rows `[2^14, 2^14 + 2^9)`). -/
theorem y_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux))
    (hb : Bundle arrs 4 9 I.ys false fun l => CMain.ksOff20 + 2 ^ 15 * (50 + l) + 2 ^ 14)
    (hyc : I.yc = I.ys + 4 * 430) (hyls : I.yls = I.ys + 4 * 447) (hyns : I.yns = I.ys + 4 * 448) :
    (∀ r < 399, ∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.ys + 4 * r + l) = FK.ofBF64 (Yq qm (2 ^ 14 + r) l)) ∧
    (∀ t ≤ 16, ∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.yc + 4 * t + l) = FK.ofBF64 (Yq qm (2 ^ 14 + 430 + t) l)) ∧
    (∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.yls + l) = FK.ofBF64 (Yq qm (2 ^ 14 + 447) l)) ∧
    (∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.yns + l) = FK.ofBF64 (Yq qm (2 ^ 14 + 448) l)) := by
  refine ⟨fun r hr l hl => y_cell H hlay hb (by omega) hl, fun t ht l hl => ?_,
    fun l hl => ?_, fun l hl => ?_⟩
  · rw [hyc, show I.ys + 4 * 430 + 4 * t = I.ys + 4 * (430 + t) by ring,
      show 2 ^ 14 + 430 + t = 2 ^ 14 + (430 + t) by omega]
    exact y_cell H hlay hb (by omega) hl
  · rw [hyls]; exact y_cell H hlay hb (by omega) hl
  · rw [hyns]; exact y_cell H hlay hb (by omega) hl

/-- **The trace-digest cells** (a 4-bundle of height 1 at `KS` row `B − 1`). -/
theorem md_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups arrs aux))
    (hb : Bundle arrs 4 0 I.md false fun l => CMain.ksOff20 + 2 ^ 15 * (50 + l) + (spongeBlocks P20 - 1)) :
    ∀ l < 4, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (I.md + l) =
      FK.ofBF64 (Yq qm (spongeBlocks P20 - 1) l) := fun l hl => by
  have hB : spongeBlocks P20 = 13096 := sizes_P20.2.2.2.2.2.2.2.2
  rw [memN_bundle H hlay hb (by omega), Nat.mod_eq_of_lt hl, Nat.div_eq_of_lt hl, Nat.add_zero,
    comCell_main (L := lay26) qm qr (by show _ < 2 ^ 24; simp only [CMain.ksOff20]; rw [hB]; omega), Yq_eq qm _ hl]

/-! ### `PUB`: the header's lanes -/


/-- **The header's 702 lanes** (`b`, `vk`, `c_L`, `s`, `n`, `h`, `σ_leaf`: 615; A23: `acc_in`'s 29
scalars, 87): the `PUB` values (`pubLanes`; `= (pubX x).hdrLanes`, `LvmAccNodePub.hdrLanes_eq_pubX`). -/
def hdrLanes (x : List UInt8) : List FK := (List.range pubLanes).map (hdrLane x)

theorem lt_pubLanes {j : ℕ} (h : j < 615) : j < pubLanes := by rw [pubLanes_eq]; omega

theorem u64At_lt (b : ByteArray) (o : ℕ) : u64At b o < 2 ^ 64 := UInt64.toNat_lt _

theorem toNat_hdrLane (x : List UInt8) (k : ℕ) : (hdrLane x k).val.toNat = u64At (hdrBytesX x) (8 + 8 * k) :=
  UInt64.toNat_ofNat_of_lt' (u64At_lt _ _)

theorem byteW_hdrLane (x : List UInt8) (k : ℕ) {t : ℕ} (ht : t < 8) :
    (hdrBytesX x).get! (8 + 8 * k + t) = Lvm.Bits.byteW (hdrLane x k).val t := by
  rw [Lvm.Wots.byteW_toNat _ ht, toNat_hdrLane,
    ← RecursionFast.toUInt8_mod, u64At_eq, ofLE_div_mod]
  simp [List.getD_eq_getElem?_getD, ht]


/-- **A `PUB` array of the header's lanes** at `pb` (stride 1, height `2^10`). -/
def PubAt (arrs : List InArr) (x : List UInt8) (pb : ℕ) : Prop :=
  ∃ k, ∃ hk : k < arrs.length, ∃ val fin, arrs[k] = pubArr 10 pb 1 val fin (hdrLanes x)

theorem pub_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) {j : ℕ} (hj : j < pubLanes) :
    (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (pb + j) = hdrLane x j := by
  obtain ⟨k, hk, val, fin, he⟩ := hp
  have hx : j < 2 ^ arrs[k].τ := by rw [he]; show j < 2 ^ 10; rw [pubLanes_eq] at hj; omega
  have hlt := H.inOk.lt _ (List.getElem_mem hk) j hx
  rw [he] at hlt
  have hlt' : pb + j < (Qn lay I qa nK nE).nIn .K := by simpa [pubArr] using hlt
  rw [memN_inK H hlt']
  have hv := inKOf_pub _ pl groups arrs aux lay26 hτ H.inOk (stackOf lay26 qm qr) hk (by rw [he]; rfl)
    (by rw [he]; rfl) hx
  simp only [he, pubArr, Nat.one_mul] at hv
  rw [hv]
  simp [pubCell, hdrLanes, List.getD_eq_getElem?_getD, hj]

theorem pub_bytes (x : List UInt8) :
    ∀ k < 615, ∀ t < 8, (hdrBytesX x).get! (8 + 8 * k + t) = Lvm.Bits.byteW (hdrLane x k).val t :=
  fun k _ t ht => byteW_hdrLane x k ht

theorem digOfW_congr {f g : ℕ → UInt64} (h : ∀ l < 4, f l = g l) : Lvm.Wots.digOfW f = Lvm.Wots.digOfW g := by
  refine Vector.ext fun i hi => ?_
  rw [Lvm.Wots.digOfW_get _ hi, Lvm.Wots.digOfW_get _ hi, h _ (by omega)]

/-- **The flag** (`I.flag = pb`): `1` for a node statement. -/
theorem flag_cell
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) (hfl : I.flag = pb) (hb1 : (hdrOf x).b = 1) :
    (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.flag = 1 := by
  have h0 := pub_cells H hp (j := 0) (lt_pubLanes (by omega))
  rw [Nat.add_zero] at h0
  rw [hfl, h0]
  have e : u64At (hdrBytesX x) 8 = 1 := hb1
  simp only [hdrLane, Nat.mul_zero, Nat.add_zero, e]
  rfl

/-- Four `PUB` cells from lane `k` hold the header's digest at byte `8 + 8k`. -/
theorem pub_digest
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) {k o : ℕ} (hk : k + 4 ≤ 615) (ho : 8 + 8 * k = o) :
    digAt (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (pb + k) =
      digestAt (hdrBytesX x) o := by
  rw [← ho, digestAt_of (pub_bytes x) hk]
  refine digOfW_congr fun l hl => ?_
  rw [Nat.add_assoc, pub_cells H hp (lt_pubLanes (by omega))]

/-- **The key's cells** (`I.vk = pb + 1`). -/
theorem vk_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) (hvk : I.vk = pb + 1) :
    digAt (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.vk = (hdrOf x).vk := by
  rw [hvk]; exact pub_digest H hp (by omega) rfl

/-- **The left statement's cells** (`I.cL = pb + 5`). -/
theorem cL_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) (hcL : I.cL = pb + 5) :
    digAt (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.cL = (hdrOf x).cL := by
  rw [hcL]; exact pub_digest H hp (by omega) rfl

/-- **The leaf signature's cells** (`I.sl = pb + 18`). -/
theorem sl_cells
    (H : AuxHyps (Qn lay I qa nK nE) pl groups arrs aux lay26 hτ (stackOf lay26 qm qr))
    {x : List UInt8} {pb : ℕ} (hp : PubAt arrs x pb) (hsl : I.sl = pb + 18) :
    sigAt' (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k I.sl = (hdrOf x).sig := by
  have hv : ∀ j < 597, (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k
      (pb + 18 + j) = hdrLane x (18 + j) := fun j hj => by
        rw [Nat.add_assoc]; exact pub_cells H hp (lt_pubLanes (by omega))
  have e1 : ((memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (pb + 18)).val.toNat =
      u64At (hdrBytesX x) 152 := by
    have h0 := hv 0 (by omega); rw [Nat.add_zero] at h0; rw [h0, toNat_hdrLane]
  have e2 : ((List.range wotsLen).map fun i =>
      digAt (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (pb + 18 + 1 + 4 * i)) =
      (List.range wotsLen).map fun k => digestAt (hdrBytesX x) (152 + 8 + 32 * k) := by
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 133 := by simpa [wotsLen] using List.mem_range.mp hi
    rw [show pb + 18 + 1 + 4 * i = pb + (19 + 4 * i) by omega]
    exact pub_digest H hp (by omega) (by omega)
  have e3 : ((List.range sigHeight).map fun t =>
      digAt (memN lay I qa nK nE pl groups arrs aux lay26 hτ (stackOf lay26 qm qr)).k (pb + 18 + 533 + 4 * t)) =
      (List.range sigHeight).map fun k => digestAt (hdrBytesX x) (152 + 8 + 32 * wotsLen + 32 * k) := by
    refine List.map_congr_left fun t ht => ?_
    have ht' : t < 16 := by simpa [sigHeight] using List.mem_range.mp ht
    rw [show pb + 18 + 533 + 4 * t = pb + (551 + 4 * t) by omega]
    exact pub_digest H hp (by omega) (by simp only [wotsLen]; omega)
  have hs : (hdrOf x).sig = sigAt (hdrBytesX x) 152 := rfl
  rw [hsl, hs]
  unfold sigAt' sigAt
  rw [e1, e2, e3]

end Fields

/-! ## `InMapN` from the arrays -/

section Assemble

variable {α : Type} {lay : Layout} {I : SigIn} {qa : BM α} {nK nE : ℕ}
  {pl : ℕ → Var → Bool × ℕ} {groups : List Grp} {arrsX : List UInt8 → List InArr} {aux : List Tab}
  {hτ' : ∀ x, ∀ t ∈ lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux, t.τ ≤ lay26.μ}

/-- **The input map from the input arrays**: the stream (17-bundle on `C_rec`, Q_sig's header at
lane 11), `σ'` (`C_rec` word `17·2^14`), `KS`'s `X` lanes (17-bundle) and output lanes (4-bundles on
`KS` rows `[2^14, 2^14 + 2^9)` and row `B − 1`), and the header's public lanes at `pb` (flag, key,
left statement, leaf signature). -/
theorem inMapN_of {vk : RecursionFast.Digest} {x : List UInt8} {qm : Column CMain.nu20} {qr : Column 19}
    (H : AuxHyps (Qn lay I qa nK nE) pl groups (arrsX x) aux lay26 (hτ' x) (stackOf lay26 qm qr))
    (hlay : LayOk lay26 (lvmTabs (Qn lay I qa nK nE) pl groups (arrsX x) aux))
    (hws : 2 ^ lay.m ≤ 17 * 2 ^ 14)
    (hS : Bundle (arrsX x) 17 14 lay.sb true fun l => l * 2 ^ 14) (hhd : I.hd = lay.sb + 11)
    (hSg : Bundle (arrsX x) 1 10 I.sg true fun _ => 17 * 2 ^ 14)
    (hX : Bundle (arrsX x) 17 9 I.xs false fun l => CMain.xOff20 + l * 2 ^ 14)
    (hY : Bundle (arrsX x) 4 9 I.ys false fun l => CMain.ksOff20 + 2 ^ 15 * (50 + l) + 2 ^ 14)
    (hyc : I.yc = I.ys + 4 * 430) (hyls : I.yls = I.ys + 4 * 447) (hyns : I.yns = I.ys + 4 * 448)
    (hMd : Bundle (arrsX x) 4 0 I.md false
      fun l => CMain.ksOff20 + 2 ^ 15 * (50 + l) + (spongeBlocks P20 - 1))
    {pb : ℕ} (hP : PubAt (arrsX x) x pb) (hfl : I.flag = pb) (hvkI : I.vk = pb + 1)
    (hcLI : I.cL = pb + 5) (hslI : I.sl = pb + 18)
    (hb1 : (hdrOf x).b = 1) (hvk : (hdrOf x).vk = vk) :
    InMapN lay I qa nK nE pl groups arrsX aux hτ' vk x qm qr := by
  have hy := y_cells H hlay hY hyc hyls hyns
  exact ⟨fun j hj => stream_cells H hlay hS (by omega), flag_cell H hP hfl hb1, xs_cells H hlay hX,
    hy.1, hy.2.1, hy.2.2.1, hy.2.2.2, (vk_cells H hP hvkI).trans hvk, cL_cells H hP hcLI,
    sl_cells H hP hslI, md_cells H hlay hMd, sg_cells H hlay hSg, hd_cells H hlay hS hhd,
    fun j hj => by rw [hfl]; exact pub_cells H hP hj⟩

end Assemble

end Lvm.NS
