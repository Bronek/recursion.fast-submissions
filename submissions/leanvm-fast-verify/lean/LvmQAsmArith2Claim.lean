-- New for lvm (HAR-RC): the claims of phases 4 and 6 as cells (`CClaim`): the Keccak tables' word
-- and ring claims, `CH`'s output-lane openings and its boundary claims `in_0 = Pad43(s)`,
-- `Y(bits(n − 1)) = h` (BLUEPRINT §4.1, A1), and `KS`'s output-lane openings. Searched for reuse:
-- `LvmChainTable` (`pad43St`: a bit-level `Pad43`, not the lane form `F` claims), `LvmLayoutArith`
-- (`eOfNat_bit`, on the protocol's `E`; restated here on `Lvm.FE`), QL/QSig (`Out1`, `w64`, the
-- `BITS` output form), core `Nat.testBit_*`, `List.zipIdx_map`. The borrow chain and the lane
-- disjointness facts are new.
import LvmQAsmArith2Ring
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

/-! ## The bits of `n − 1` -/

theorem mod_two_pow_succ_eq_zero (n j : Nat) :
    n % 2 ^ (j + 1) = 0 ↔ (n % 2 ^ j = 0 ∧ n.testBit j = false) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> rw [h] <;> simp

theorem testBit_pred (n j : Nat) (hn : 1 ≤ n) :
    (n - 1).testBit j = (n.testBit j ^^ decide (n % 2 ^ j = 0)) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hP : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdm := Nat.div_add_mod n (2 ^ j)
  have hr := Nat.mod_lt n hP
  generalize n / 2 ^ j = q at hdm
  generalize n % 2 ^ j = r at hdm hr ⊢
  subst hdm
  by_cases h0 : r = 0
  · subst h0
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hn
      · omega⟩
    have e : 2 ^ j * (q' + 1) + 0 - 1 = 2 ^ j * q' + (2 ^ j - 1) := by
      rw [Nat.mul_succ]; omega
    rw [e, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    rcases Nat.mod_two_eq_zero_or_one q' with h | h <;> simp [h, Nat.add_mod]
  · have e : 2 ^ j * q + r - 1 = 2 ^ j * q + (r - 1) := by omega
    rw [e, Nat.mul_add_div hP, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    simp [h0]

/-- The value of bit `j` of `N` (`0`/`1`). -/
def bitE (N j : Nat) : FE := if N.testBit j then 1 else 0

/-- The borrow of `N − 1` into bit `j`: `1` iff bits `0 … j − 1` of `N` are zero. -/
def carryE (N j : Nat) : FE := if N % 2 ^ j = 0 then 1 else 0

theorem fe_two : (1 : FE) + 1 = 0 := CharTwo.add_self_eq_zero 1

theorem carry_succ (N j : Nat) : carryE N (j + 1) = carryE N j * bitE N j + carryE N j := by
  simp only [carryE, bitE]
  by_cases h1 : N % 2 ^ j = 0 <;> by_cases h2 : N.testBit j = true <;>
    simp [h1, h2, mod_two_pow_succ_eq_zero, fe_two]

theorem pred_bit (N j : Nat) (hN : 1 ≤ N) : bitE (N - 1) j = bitE N j + carryE N j := by
  simp only [bitE, carryE, testBit_pred N j hN]
  by_cases h1 : N % 2 ^ j = 0 <;> by_cases h2 : N.testBit j = true <;> simp [h1, h2, fe_two]

/-- The bits `j, j + 1, …` (`k` of them) of `N − 1` from the bits of `N` at `K` cells `nb + j` and the
borrow `cy` into bit `j`. -/
def borrowGo (nb : Nat) : Nat → Nat → Cell → BM (List Cell)
  | _, 0, _ => pure []
  | j, k + 1, cy => do
    let d ← add (kc (nb + j)) cy
    let cy' ← mad cy (kc (nb + j)) cy
    let ds ← borrowGo nb (j + 1) k cy'
    pure (d :: ds)

/-- **The bits `0 … n − 1` of `N − 1`** (`K` cells) from the bits of `N` at `K` cells `nb + j`. -/
def borrow (nb o n : Nat) : BM (List Cell) :=
  match n with
  | 0 => pure []
  | k + 1 => do
    let d0 ← add (kc nb) (ec o)
    let ds ← borrowGo nb 1 k d0
    pure (d0 :: ds)

theorem add_out (a b : Cell) (p : Ptr) : (add a b p).1 = ⟨jn a.ty b.ty, p.at (jn a.ty b.ty)⟩ := rfl
theorem mad_out (a b d : Cell) (p : Ptr) :
    (mad a b d p).1 = ⟨jn (jn a.ty b.ty) d.ty, p.at (jn (jn a.ty b.ty) d.ty)⟩ := rfl

theorem add_val {a b : Cell} {p : Ptr} (h : SegsHold c M p (add a b p).2) :
    (add a b p).1.val M = a.val M + b.val M := by
  have := lin_spec h
  rw [ofK_one, one_mul, ofK_zero, add_zero] at this
  exact this

theorem addK_val {a : Cell} {k' : FK} {p : Ptr} (h : SegsHold c M p (addK a k' p).2) :
    (addK a k' p).1.val M = a.val M + FE.ofK k' := by
  have := lin_spec h
  rw [ofK_zero, zero_mul, add_zero] at this
  exact this

theorem mad_val {a b d : Cell} {p : Ptr} (h : SegsHold c M p (mad a b d p).2) :
    (mad a b d p).1.val M = a.val M * b.val M + d.val M := mulAdd_spec h

theorem borrowGo_vs (N nb : Nat) : ∀ (k j : Nat) (cy : Cell) (p : Ptr), cy.ty = .E →
    cy.val M = carryE N j → (∀ i < k, (kc (nb + j + i)).val M = bitE N (j + i)) → 1 ≤ N →
    SegsHold c M p (borrowGo nb j k cy p).2 →
    vs M (borrowGo nb j k cy p).1 = (List.range k).map fun i => bitE (N - 1) (j + i)
  | 0, _, _, _, _, _, _, _, _ => rfl
  | k + 1, j, cy, p, hty, hcy, hb, hN, h => by
    simp only [borrowGo] at h ⊢
    rw [hold_bind] at h
    obtain ⟨h1, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h2, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h3, -⟩ := h
    have e1 := add_val h1
    have e2 := mad_val h2
    have hb0 := hb 0 (by omega)
    simp only [Nat.add_zero] at hb0
    have ih := borrowGo_vs N nb k (j + 1) _ _ (by rw [mad_out, hty]; rfl)
      (by rw [e2, hcy, hb0, carry_succ]) (fun i hi => by
        rw [show nb + (j + 1) + i = nb + j + (i + 1) by omega, hb (i + 1) (by omega)]
        congr 1; omega) hN h3
    rw [bind_apply, bind_apply, bind_apply, pure_apply]
    simp only [vs, List.map_cons] at ih ⊢
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map, e1, hb0, hcy, ← pred_bit N j hN,
      Nat.add_zero]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1; omega

theorem borrow_vs {N nb o n : Nat} {p : Ptr} (ho : M.e o = 1) (hb : ∀ j < n, (kc (nb + j)).val M = bitE N j) (hN : 1 ≤ N)
    (h : SegsHold c M p (borrow nb o n p).2) :
    vs M (borrow nb o n p).1 = (List.range n).map (bitE (N - 1)) := by
  match n, hb, h with
  | 0, _, _ => rfl
  | k + 1, hb, h =>
    simp only [borrow] at h ⊢
    rw [hold_bind] at h
    obtain ⟨h1, h⟩ := h
    rw [hold_bind] at h
    obtain ⟨h2, -⟩ := h
    have e1 := add_val h1
    have hb0 := hb 0 (by omega)
    simp only [Nat.add_zero] at hb0
    have hc1 : (add (kc nb) (ec o) p).1.val M = carryE N 1 := by
      rw [e1, Cell.val_E, ho, hb0]
      have := carry_succ N 0
      simp only [carryE, pow_zero, Nat.mod_one, if_true, one_mul, Nat.zero_add] at this ⊢
      rw [this, add_comm]
    have ih := borrowGo_vs N nb k 1 _ _ rfl hc1 (fun i hi => by
      rw [show nb + 1 + i = nb + (1 + i) by omega]; exact hb (1 + i) (by omega)) hN h2
    rw [bind_apply, bind_apply, pure_apply]
    simp only [vs, List.map_cons] at ih ⊢
    rw [ih, List.range_succ_eq_map, List.map_cons, List.map_map, e1, Cell.val_E, ho, hb0, pred_bit N 0 hN]
    simp only [carryE, pow_zero, Nat.mod_one, if_true]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    congr 1; omega

/-- `selectorPoint` is the list of bits. -/
theorem selectorPoint_bits (N n : Nat) : selectorPoint N n = (List.range n).map (bitE N) := by
  simp only [selectorPoint]
  refine List.map_congr_left fun b _ => ?_
  unfold bitE
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (N >>> b) with h | h <;> simp [h] <;> rfl

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

/-- **The byte shifts of the child's `s'` lanes** (a `BITS` class like `h'`'s: `shl 8` at `sb + 2l`,
`shr 56` at `sb + 2l + 1`). -/
def SBits (v : Nat → FK) (sb : Nat) : Prop :=
  ∀ l < 4, Out1 v (sLane l) (.shl 8) (sb + 2 * l) ∧ Out1 v (sLane l) (.shr 56) (sb + 2 * l + 1)

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

/-! ## `CH`'s fixed claims -/

/-- `Pad43(s')`'s lanes as cells (lanes 0–4 `K` cells `l`, the constant lane 16 `c80`, zeros `z`). -/
def padCells (l : List Cell) (c80 z : Nat) : List Cell :=
  l ++ List.replicate 11 (ec z) ++ [ec c80] ++ List.replicate 8 (ec z)

theorem addK_out (a : Cell) (k' : FK) (p : Ptr) : (addK a k' p).1 = ⟨a.ty, p.at a.ty⟩ := rfl

theorem fk_val_inj {a b : FK} (h : a.val = b.val) : a = b := by cases a; cases b; cases h; rfl

/-- The `K` lane of a `Pad43` lane: `(x ||| y)` of disjoint words is `x + y` in `K`. -/
theorem padLanes_val {sb : Nat} {s : List FK} (hs : s.length = 4)
    (hsb : ∀ l < 4, M.k (sb + 2 * l) = w64 ((BOut.shl 8).word (s.getD l 0).val) ∧
      M.k (sb + 2 * l + 1) = w64 ((BOut.shr 56).word (s.getD l 0).val))
    {p0 p1 p2 p3 p4 : Ptr}
    (h0 : SegsHold c M p0 (addK (kc sb) ⟨0x43⟩ p0).2) (h1 : SegsHold c M p1 (add (kc (sb + 1)) (kc (sb + 2)) p1).2)
    (h2 : SegsHold c M p2 (add (kc (sb + 3)) (kc (sb + 4)) p2).2)
    (h3 : SegsHold c M p3 (add (kc (sb + 5)) (kc (sb + 6)) p3).2)
    (h4 : SegsHold c M p4 (addK (kc (sb + 7)) ⟨(0x01 : UInt64) <<< 8⟩ p4).2) :
    vs M [(addK (kc sb) ⟨0x43⟩ p0).1, (add (kc (sb + 1)) (kc (sb + 2)) p1).1,
        (add (kc (sb + 3)) (kc (sb + 4)) p2).1, (add (kc (sb + 5)) (kc (sb + 6)) p3).1,
        (addK (kc (sb + 7)) ⟨(0x01 : UInt64) <<< 8⟩ p4).1] =
      ((pad43 s).take 5).map FE.ofK := by
  obtain ⟨a0, b0⟩ := hsb 0 (by omega)
  obtain ⟨a1, b1⟩ := hsb 1 (by omega)
  obtain ⟨a2, b2⟩ := hsb 2 (by omega)
  obtain ⟨a3, b3⟩ := hsb 3 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 2 * 2 = 4 from rfl, show 2 * 3 = 6 from rfl,
    show 4 + 1 = 5 from rfl, show 6 + 1 = 7 from rfl, show 2 + 1 = 3 from rfl] at a0 b0 a1 b1 a2 b2 a3 b3
  have e0 := linK_spec h0
  have e1 := linK_spec h1
  have e2 := linK_spec h2
  have e3 := linK_spec h3
  have e4 := linK_spec h4
  simp only [vs, List.map_cons, List.map_nil, addK_out, add_out, Cell.val, Mem.rd, jn, kc, Ptr.at]
  rw [e0, e1, e2, e3, e4, a0, b0, a1, b1, a2, b2, a3, b3]
  simp only [pad43, List.take, List.cons_append, List.map_cons, List.map_nil, zero_mul, add_zero,
    one_mul]
  refine List.cons_eq_cons.2 ⟨congrArg FE.ofK (fk_val_inj ?_), List.cons_eq_cons.2 ⟨congrArg FE.ofK
    (fk_val_inj ?_), List.cons_eq_cons.2 ⟨congrArg FE.ofK (fk_val_inj ?_), List.cons_eq_cons.2
    ⟨congrArg FE.ofK (fk_val_inj ?_), List.cons_eq_cons.2 ⟨congrArg FE.ofK (fk_val_inj ?_), rfl⟩⟩⟩⟩⟩
  · show (_ <<< (8 : Nat).toUInt64) ^^^ _ = _; rw [pad_or0]; rfl
  · show (_ >>> (56 : Nat).toUInt64) ^^^ (_ <<< (8 : Nat).toUInt64) = _; rw [pad_or1]; rfl
  · show (_ >>> (56 : Nat).toUInt64) ^^^ (_ <<< (8 : Nat).toUInt64) = _; rw [pad_or1]; rfl
  · show (_ >>> (56 : Nat).toUInt64) ^^^ (_ <<< (8 : Nat).toUInt64) = _; rw [pad_or1]; rfl
  · show (_ >>> (56 : Nat).toUInt64) ^^^ _ = _; rw [pad_or1]; rfl

/-- **`Pad43(s')`'s 25 lanes** as cells: lanes 0–4 from the `s'` byte shifts at `sb` (one `K` row
each), the constant lane 16, zeros. -/
def padG (sb z : Nat) : BM (List Cell) := do
  let l0 ← addK (kc sb) ⟨0x43⟩
  let l1 ← add (kc (sb + 1)) (kc (sb + 2))
  let l2 ← add (kc (sb + 3)) (kc (sb + 4))
  let l3 ← add (kc (sb + 5)) (kc (sb + 6))
  let l4 ← addK (kc (sb + 7)) ⟨(0x01 : UInt64) <<< 8⟩
  let c80 ← const .E ⟨(0x80 : UInt64) <<< 56⟩ (ec z)
  pure (padCells [l0, l1, l2, l3, l4] c80.n z)

theorem padG_vs {sb z : Nat} {s : List FK} (hs : s.length = 4) (hz : M.e z = 0)
    (hsb : ∀ l < 4, M.k (sb + 2 * l) = w64 ((BOut.shl 8).word (s.getD l 0).val) ∧
      M.k (sb + 2 * l + 1) = w64 ((BOut.shr 56).word (s.getD l 0).val))
    {p : Ptr} (h : SegsHold c M p (padG sb z p).2) :
    vs M (padG sb z p).1 = (pad43 s).map FE.ofK := by
  simp only [padG] at h ⊢
  rw [hold_bind] at h; obtain ⟨h0, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h1, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h2, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h3, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h4, h⟩ := h
  rw [hold_bind] at h; obtain ⟨h5, -⟩ := h
  have e5 := constE_spec h5
  have hL := padLanes_val hs hsb h0 h1 h2 h3 h4
  simp only [bind_apply, pure_apply, padCells, vs_append]
  rw [hL]
  simp only [vs, List.map_replicate, List.map_cons, List.map_nil, Cell.val_E, hz, const_out]
  simp only [Ptr.at] at e5 ⊢
  rw [e5]
  rw [← List.take_append_drop 5 (pad43 s), List.map_append]
  simp only [List.append_assoc]
  congr 1

/-- A list of claims indexed by `zipIdx`, built from cells, is the claims from the cells' values. -/
theorem zipIdx_cells {α : Type} (cs : List Cell) (xs : List α) (g : α → FE) (hx : vs M cs = xs.map g)
    (mk : Cell → Nat → CClaim) (f : FE → Nat → Com × BlockClaim)
    (hmk : ∀ cc l, CClaim.val M (mk cc l) = f (cc.val M) l) :
    (cs.zipIdx.map fun cl => mk cl.1 cl.2).map (CClaim.val M) = xs.zipIdx.map fun xl => f (g xl.1) xl.2 := by
  rw [List.map_map]
  have e1 : cs.zipIdx.map (CClaim.val M ∘ fun cl => mk cl.1 cl.2) =
      (cs.zipIdx.map (Prod.map (Cell.val M) id)).map (fun xl => f xl.1 xl.2) := by
    rw [List.map_map]
    exact List.map_congr_left fun cl _ => hmk cl.1 cl.2
  rw [e1, ← List.zipIdx_map]
  change ((vs M cs).zipIdx.map _) = _
  rw [hx, List.zipIdx_map, List.map_map]
  rfl

/-- **`CH`'s fixed claims as cells** (`chFixedClaims`): the `Y` openings, the `Pad43` lanes `pc` at
row 0, `h'` at the row `ds` (the bits of `n' − 1`). -/
def fixedC (n ySlot : Nat) (blk : Placement) (z o : Nat) (rc vc ds pc : List Cell) : List CClaim :=
  ((List.range 4).map fun l =>
      ⟨.main, .point blk (rc ++ selC z o (ySlot + l) slotLog), vc.getD l default⟩) ++
    (pc.zipIdx.map fun cl => ⟨.main, .point blk (selC z o 0 n ++ selC z o cl.2 slotLog), cl.1⟩) ++
    (((List.range 4).map fun l => kc (hLane l)).zipIdx.map fun cl =>
      ⟨.main, .point blk (ds ++ selC z o (ySlot + cl.2) slotLog), cl.1⟩)

theorem fixedC_val (p : Params) (blk : Placement) {ySlot z o : Nat} (hz : M.e z = 0) (ho : M.e o = 1)
    (rc vc ds pc : List Cell) (pub : Pub) (hvc : vc.length = 25)
    (hds : vs M ds = selectorPoint (pub.n - 1) p.logN) (hpc : vs M pc = (pad43 pub.s).map FE.ofK)
    (hh : pub.h = (List.range 4).map fun l => M.k (hLane l)) :
    (fixedC p.logN ySlot blk z o rc vc ds pc).map (CClaim.val M) =
      (chFixedClaims p blk ySlot (vs M rc) (vs M vc) pub).map (.main, ·) := by
  simp only [fixedC, chFixedClaims, List.map_append]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
  · rw [List.map_map, List.map_map]
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply, CClaim.val, vs_append, selC_vs hz ho, vs_getD M vc (i := l) (by omega)]
  · have := zipIdx_cells pc (pad43 pub.s) FE.ofK hpc
      (fun cc l => ⟨.main, .point blk (selC z o 0 p.logN ++ selC z o l slotLog), cc⟩)
      (fun x l => (.main, BlockClaim.point blk (selectorPoint 0 p.logN ++ selectorPoint l slotLog) x))
      (fun cc l => by simp only [CClaim.val, vs_append, selC_vs hz ho])
    rw [this, List.map_map]
    rfl
  · have hhv : vs M ((List.range 4).map fun l => kc (hLane l)) = pub.h.map FE.ofK := by
      rw [hh]; simp [vs, List.map_map]
    have := zipIdx_cells _ pub.h FE.ofK hhv
      (fun cc l => ⟨.main, .point blk (ds ++ selC z o (ySlot + l) slotLog), cc⟩)
      (fun x l => (.main, BlockClaim.point blk (selectorPoint (pub.n - 1) p.logN ++
        selectorPoint (ySlot + l) slotLog) x))
      (fun cc l => by simp only [CClaim.val, vs_append, selC_vs hz ho, hds])
    rw [this, List.map_map]
    rfl

/-- **`CH`'s fixed claims, the gadget**: the borrow chain (`n'`'s bits at `nb`) and `Pad43`'s lanes
(`s'`'s byte shifts at `sb`). -/
def chFixedG (n ySlot : Nat) (blk : Placement) (z o sb nb : Nat) (rc vc : List Cell) :
    BM (List CClaim) := do
  let ds ← borrow nb o n
  let pc ← padG sb z
  pure (fixedC n ySlot blk z o rc vc ds pc)

theorem bitE_out1 {v : Nat → FK} {w nb j : Nat} (hj : j < 64) (h : Out1 v w (.bit j) (nb + j)) :
    FE.ofK (v (nb + j)) = bitE (v w).val.toNat j := by
  rw [h, w64, bit_word _ hj, bitE]
  split_ifs <;> rfl

/-- **Q_arith_eq, `CH`'s claims (phase 4)**: the word and ring claims of its Keccak GKR and the fixed
claims (output lanes, boundaries) are the cells' values, for `m = M3.ofParts p …` (any bus/table parts) and the child's
public values `pub = pubOf vk c Σ`. Hypotheses: the stream (`Streamed`, header lanes `< T`), the
`BITS` cells (`SBits`: the byte shifts of `s'`, a class to add; `NBits`: Q_sig's bits of `n'`),
`n' ≥ 1` (`ChildOk`, A1), the ring switch's relation (`RingRel`, `ringGkr_ringAt`). -/
theorem chClaims_val (p : Params) {bf : BusIn → BusOut} {tb : Pub → List TableSpec}
    {tcl : Pub → List (List FE × List FE) → List (Com × BlockClaim)}
    {fv : Pub → List FE → List FE}
    {fs : Pub → List (List FE × List FE) → List FE} {pck : Pub → List (List FE × List FE) → Bool}
    {z o sb nb : Nat} {rc vc : List Cell} {ko : GkrOut} {rg : RingOut} {ring : FE × (List FE → FE)}
    {sig : ByteArray} {T : Nat} {ptr : Ptr} (vk c' : Vector UInt8 32)
    (hS : Streamed M sig T) (hT : 29 ≤ T) (hz : M.e z = 0) (ho : M.e o = 1) (hvc : vc.length = 25)
    (hsb : SBits M.k sb) (hnb : NBits M.k nb p.logN) (hlog : p.logN ≤ 64)
    (hn1 : 1 ≤ (pubOf vk c' sig).n) (hr : RingRel M (ko.vals M).slicePoint ring rg)
    (h : SegsHold c M ptr (chFixedG p.logN 52 (M3.ofParts p bf tb tcl fv fs pck).chBlock z o sb nb rc vc ptr).2) :
    (kClaimsC (M3.ofParts p bf tb tcl fv fs pck).chBlock ko rg ++
        (chFixedG p.logN 52 (M3.ofParts p bf tb tcl fv fs pck).chBlock z o sb nb rc vc ptr).1).map (CClaim.val M) =
      (keccakClaims (M3.ofParts p bf tb tcl fv fs pck).chBlock (ko.vals M) ring ++
        chFixedClaims p (M3.ofParts p bf tb tcl fv fs pck).chBlock (M3.ofParts p bf tb tcl fv fs pck).chYSlot
          (vs M rc) (vs M vc) (pubOf vk c' sig)).map (.main, ·) := by
  rw [List.map_append, List.map_append, kClaimsC_val _ ko rg ring hr]
  congr 1
  simp only [chFixedG] at h ⊢
  rw [hold_bind] at h; obtain ⟨hd, h⟩ := h
  rw [hold_bind] at h; obtain ⟨hp, -⟩ := h
  simp only [bind_apply, pure_apply]
  have hsl : (pubOf vk c' sig).s.length = 4 := by simp [pubOf]
  refine fixedC_val p _ hz ho rc vc _ _ (pubOf vk c' sig) hvc ?_ ?_ (pub_h hS hT vk c')
  · rw [borrow_vs (N := (pubOf vk c' sig).n) ho (fun j hj => ?_) hn1 hd, selectorPoint_bits]
    rw [pub_n hS hT vk c', Cell.val_K]
    exact bitE_out1 (by omega) (hnb j hj)
  · refine padG_vs hsl hz (fun l hl => ?_) hp
    rw [pub_s hS hT vk c']
    obtain ⟨h1, h2⟩ := hsb l hl
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
      Option.getD_some]
    exact ⟨h1, h2⟩

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
