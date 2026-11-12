-- New for lvm (HAR-RC): the claims of phases 4 and 6 as cells (`CClaim`): the Keccak tables' word
-- and ring claims, `CH`'s output-lane openings and its boundary claims `in_0 = Pad43(s)`,
-- `Y(bits(n − 1)) = h` (BLUEPRINT §4.1, A1), and `KS`'s output-lane openings. Searched for reuse:
-- `LvmChainTable` (`pad43St`: a bit-level `Pad43`, not the lane form `F` claims), `LvmLayoutArith`
-- (`eOfNat_bit`, on the protocol's `E`; restated here on `Lvm.FE`), QL/QSig (`Out1`, `w64`, the
-- `BITS` output form), core `Nat.testBit_*`, `List.zipIdx_map`. The borrow chain and the lane
-- disjointness facts are new.
import LvmQAsmArith2Ring
import LvmQAsmBorrow
import LvmQSigDefs

/-!
# Q_arith: the claims of phases 4 and 6

* `selC z o sel len`: the cells of `selectorPoint sel len` (`z`, `o` `E` cells holding `0`, `1`;
  `selC_vs`).
* `kClaimsC blk ko rg`: `keccakClaims blk ko ring` (word claim, ring claim) as cells
  (`kClaimsC_val`).
* **`chFixedG`** (`CH`'s fixed claims, `chFixedClaims`): the four `Y` openings at `r`; the 25
  boundary claims `in_0 = Pad43(s')` at row 0 (lanes 0–4 from the byte shifts `s'_l << 8`,
  `s'_l >> 56` of the child's `s'` lanes, `K` rows `x + y` / `x + k`, disjoint bits; the constant
  lanes `0`, `0x80 << 56`); the four claims `Y(bits(n' − 1)) = h'`, the point from the `BITS` bits
  of `n'` by a borrow chain (`borrow`: `d_j = b_j + c_j`, `c_{j+1} = c_j·b_j + c_j`, `c_0 = 1`;
  `borrow_vs`: `selectorPoint (n' − 1)`, `n' ≥ 1`). **`chClaims_val`**: with the stream bound
  (`Streamed`) and the `BITS` cells (`SBits`, `NBits`), the cells are
  `(keccakClaims m.chBlock ko ring ++ chFixedClaims p m.chBlock m.chYSlot r v pub).map (.main, ·)`
  for `pub = pubOf vk c Σ` and `m = M3.ofParts p …` (any bus/table parts).
* `ksOutC`: `m.ksOutputClaims rk vks` as cells (`ksOutC_val`); `KS`'s `keccakClaims` is
  `kClaimsC_val` (no rows).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing Lvm.Q1 Lvm.QSig Lvm.Bits

variable {c : Ctx} {M : Mem}

/-! ## Constant points -/

/-- The cells of `selectorPoint sel len` (`z`, `o`: `E` cells holding `0`, `1`). -/
def selC (z o sel len : Nat) : List Cell :=
  (List.range len).map fun b => if (sel >>> b) % 2 = 1 then ec o else ec z

theorem eOfNat_zero_fe : eOfNat 0 = 0 := rfl
theorem eOfNat_one_fe : eOfNat 1 = 1 := rfl

theorem selC_vs {z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1) (sel len : Nat) :
    vs M (selC z o sel len) = selectorPoint sel len := by
  simp only [selC, vs, selectorPoint, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (sel >>> b) with h | h
  · simp only [Function.comp_apply, h, if_neg (by decide : ¬ (0 = 1)), Cell.val_E, hz]
    try exact eOfNat_zero_fe.symm
  · simp only [Function.comp_apply, h, if_true, Cell.val_E, ho]
    try exact eOfNat_one_fe.symm

theorem vs_append (M : Mem) (a b : List Cell) : vs M (a ++ b) = vs M a ++ vs M b := List.map_append

theorem vs_getD (M : Mem) (l : List Cell) {i : Nat} (hi : i < l.length) :
    (l.getD i default).val M = (vs M l).getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa [vs] using hi)]
  simp [vs]

/-! ## The Keccak tables' claims -/

/-- `keccakClaims blk ko ring` as cells: the committed-output word claim and the ring claim. -/
def kClaimsC (blk : Placement) (ko : GkrOut) (rg : RingOut) : List CClaim :=
  [⟨.main, .point blk ko.wordPoint, ko.word⟩, ⟨.main, .ring blk ko.slicePoint rg.cs, rg.target⟩]

theorem kClaimsC_val (blk : Placement) (ko : GkrOut) (rg : RingOut) (ring : FE × (List FE → FE))
    (hr : RingRel M (ko.vals M).slicePoint ring rg) :
    (kClaimsC blk ko rg).map (CClaim.val M) = (keccakClaims blk (ko.vals M) ring).map (.main, ·) := by
  obtain ⟨h1, h2⟩ := hr
  simp only [kClaimsC, keccakClaims, List.map_cons, List.map_nil, CClaim.val, GkrOut.vals, h1, h2, vs]

/-! ## `BITS` outputs -/

theorem or_eq_xor_of {x y : UInt64} (h : ∀ i, x.toNat.testBit i = true → y.toNat.testBit i = false) :
    x ||| y = x ^^^ y := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_or, UInt64.toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_xor]
  have := h i
  cases hx : x.toNat.testBit i <;> cases hy : y.toNat.testBit i <;> simp_all

theorem testBit_shl8 (w : UInt64) (i : Nat) (hi : (w <<< (8 : UInt64)).toNat.testBit i = true) :
    8 ≤ i := by
  rw [UInt64.toNat_shiftLeft, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft] at hi
  simp at hi; omega

theorem testBit_shr56 (w : UInt64) (i : Nat) (hi : (w >>> (56 : UInt64)).toNat.testBit i = true) :
    i < 8 := by
  rw [UInt64.toNat_shiftRight, show (56 : UInt64).toNat % 64 = 56 from rfl, Nat.testBit_shiftRight] at hi
  by_contra hc
  have hlt := w.toNat_lt
  have : w.toNat.testBit (56 + i) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp_all

theorem pad_or0 (w : UInt64) : (0x43 : UInt64) ||| (w <<< 8) = (w <<< 8) ^^^ 0x43 := by
  rw [UInt64.or_comm]
  refine or_eq_xor_of fun i hi => ?_
  have h8 := testBit_shl8 w i hi
  rw [show (0x43 : UInt64).toNat = 0x43 from rfl]
  exact Nat.testBit_lt_two_pow
    (lt_of_lt_of_le (by norm_num : 0x43 < 2 ^ 8) (Nat.pow_le_pow_right (by norm_num) h8))

theorem pad_or1 (a b : UInt64) : (a >>> 56) ||| (b <<< 8) = (a >>> 56) ^^^ (b <<< 8) := by
  refine or_eq_xor_of fun i hi => ?_
  have := testBit_shr56 a i hi
  cases h : (b <<< (8 : UInt64)).toNat.testBit i
  · rfl
  · have := testBit_shl8 b i h; omega

theorem bit_word (w : UInt64) {z : Nat} (hz : z < 64) :
    (BOut.bit z).word w = if w.toNat.testBit z then 1 else 0 := by
  simp only [BOut.word]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have hz' : z.toUInt64.toNat % 64 = z := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  rw [hz', show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
  split_ifs with h <;> simp [Nat.testBit, Nat.shiftRight_eq_div_pow] at h ⊢ <;> omega

/-! ## The child's header lanes in the stream -/

/-- The stream lane of header byte `j` (`headerAt`). -/
def hdrLane (j : Nat) : Nat := headerAt j / 8

theorem headerAt_lane (k : Nat) : headerAt (8 + 8 * k) = 8 * hdrLane (8 + 8 * k) := by
  simp only [hdrLane, headerAt]; omega

/-- The child's `s'` lane `l`, `n'`, `h'` lane `l` (stream lanes `20 + l`, `24`, `25 + l`). -/
def sLane (l : Nat) : Nat := hdrLane (80 + 8 * l)
def nLane : Nat := hdrLane 112
def hLane (l : Nat) : Nat := hdrLane (120 + 8 * l)

theorem sLane_eq (l : Nat) : sLane l = 20 + l := by simp only [sLane, hdrLane, headerAt]; omega
theorem nLane_eq : nLane = 24 := rfl
theorem hLane_eq (l : Nat) : hLane l = 25 + l := by simp only [hLane, hdrLane, headerAt]; omega

/-- **The bits of the child's `n'`** at `nb + j`, `j < n` (Q_sig's `bn + 2 + j`, `SigBits.n_bit`). -/
def NBits (v : Nat → FK) (nb n : Nat) : Prop := ∀ j < n, Out1 v nLane (.bit j) (nb + j)

theorem pub_s {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (hT : 29 ≤ T) (vk c' : Vector UInt8 32) :
    (pubOf vk c' sig).s = (List.range 4).map fun l => M.k (sLane l) := by
  simp only [pubOf]
  refine List.map_congr_left fun l hl => ?_
  have hl' := List.mem_range.mp hl
  rw [hS _ (by rw [sLane_eq]; omega)]
  exact congrArg (kAt sig) (by simp only [sLane, hdrLane, headerAt]; omega)

theorem pub_h {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (hT : 29 ≤ T) (vk c' : Vector UInt8 32) :
    (pubOf vk c' sig).h = (List.range 4).map fun l => M.k (hLane l) := by
  simp only [pubOf]
  refine List.map_congr_left fun l hl => ?_
  have hl' := List.mem_range.mp hl
  rw [hS _ (by rw [hLane_eq]; omega)]
  exact congrArg (kAt sig) (by simp only [hLane, hdrLane, headerAt]; omega)

theorem pub_n {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (hT : 29 ≤ T) (vk c' : Vector UInt8 32) :
    (pubOf vk c' sig).n = (M.k nLane).val.toNat := by
  rw [hS _ (by rw [nLane_eq]; omega)]
  rfl

/-! ## The tape's claims (lvm2 S2; T-V's `tapeClaims`) -/

/-- **The tape's claims as cells** (T-V's `tapeClaims` order): `D̃_l(r) = a_l` (`l < 4`) on `dBlock`, the
ring-switched slices of `D` on `C_main` at `σ ‖ τ ‖ sel(dSel)`, the boundary claims `D̃_l(bits(m)) = h_l`
(`m`'s bits the borrow chain's cells, `h_l` the child's header lanes). -/
def tapeClaimsC (p : Params) (z o : Nat) (oP : P47Out) : List CClaim :=
  ((List.range dLanes).map fun l => ⟨.main, .point (dBlock p) (oP.r ++ selC z o l 2), oP.v.getD l default⟩) ++
  [⟨.main, .ring ⟨p.nuMain, 0⟩ (oP.wire.sigma ++ oP.wire.tau ++ selC z o (dSel p) (dSelBits p)) oP.wire.ring.cs,
    oP.wire.ring.target⟩] ++
  (List.range 4).map fun l => ⟨.main, .point (dBlock p) (oP.mb ++ selC z o l 2), kc (hLane l)⟩

/-! ## `KS`'s output-lane claims -/

/-- `ksYPart` with the point as cells. -/
def ksYPartC (p : Params) (l : Nat) (ptc : List Cell) (z o : Nat) : Placement × List Cell :=
  if l < 14 then (⟨p.ksLog + slotLog, (layout0 p).ks⟩, ptc ++ selC z o (50 + l) slotLog)
  else (⟨p.ksLog, (layout0 p).ksY2 + (l - 14) * 2 ^ p.ksLog⟩, ptc)

theorem ksYPartC_val (p : Params) (l : Nat) (ptc : List Cell) {z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) :
    ((ksYPartC p l ptc z o).1, vs M (ksYPartC p l ptc z o).2) = ksYPart p (layout0 p) l (vs M ptc) := by
  unfold ksYPartC ksYPart
  split_ifs <;> simp [vs_append, selC_vs hz ho]

/-- **`KS`'s output-lane openings** (`ksOutputClaims0`) as cells: `rk` the instance point, `vk` the
25 lanes. -/
def ksOutC (p : Params) (rk vk : List Cell) (z o : Nat) : List CClaim :=
  (List.range 25).map fun l =>
    ⟨.main, .point (ksYPartC p l rk z o).1 (ksYPartC p l rk z o).2, vk.getD l default⟩

/-- **Q_arith_eq, `KS`'s output-lane claims (phase 6)**. -/
theorem ksOutC_val (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)}
    {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool} (rk vk : List Cell) {z o : Nat} (hz : M.e z = 0)
    (ho : M.e o = 1) (hvk : vk.length = 25) :
    (ksOutC p rk vk z o).map (CClaim.val M) =
      (M3.ofParts p bf tb tcl fv fs pck).ksOutputClaims (vs M rk) (vs M vk) := by
  show _ = ksOutputClaims0 p (vs M rk) (vs M vk)
  simp only [ksOutC, ksOutputClaims0, List.map_map]
  refine List.map_congr_left fun l hl => ?_
  have hl' := List.mem_range.mp hl
  have e := ksYPartC_val (M := M) p l rk hz ho
  simp only [Function.comp_apply, CClaim.val, vs_getD M vk (by omega : l < vk.length)]
  rw [← e]

end Lvm.Har
