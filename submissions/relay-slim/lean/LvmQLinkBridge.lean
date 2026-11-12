-- New for lvm (WP-11b-QL): from Q_link's lane conditions to the byte-level trace conditions.
-- `wordsBytes`/`ofLE` are the Library's (`RecursionFast.Library.Words`).
import LvmQLinkStream

/-!
# From lanes to bytes: `LaneLink` ⇒ `LinkOk`

* `u64At_eq`: the driver's little-endian word reader is `ofLE` of the eight bytes;
  `answerBits_lanes`: a decoded answer's challenge bits are its first three lanes.
* `wordsBytes_slice`: the bytes of lanes `[a, a + n)` of the stream are `wordsBytes` of the lane
  slice; `slice_eq`: equal lanes give equal slices.
* `posVal_shift`, `posVal_bit`: the driver's positions (`posVal` on the decoded trace) are the
  lanes' bits (`posL`, `ansBit`).
* **`linkOk_of_laneLink`**: with the plan's static stream facts (`StreamOk`, decided per parameter
  set), Q_link's lane conditions make the decoded trace a trace of the schedule;
  **`stream_of_laneLink`**: the stream's first `hashedLen p` bytes are `tagTrace :: traceBytes` of it.
-/

set_option autoImplicit false

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay

/-! ## Words and bytes -/

theorem or_shift_add {acc b k : Nat} (hacc : acc < 2 ^ k) : acc ||| b <<< k = acc + b <<< k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hacc]; omega

theorem or8 (x0 x1 x2 x3 x4 x5 x6 x7 : Nat) (h0 : x0 < 256) (h1 : x1 < 256) (h2 : x2 < 256)
    (h3 : x3 < 256) (h4 : x4 < 256) (h5 : x5 < 256) (h6 : x6 < 256) (_h7 : x7 < 256) :
    (x0 * 2 ^ (8 * 0) ||| x1 * 2 ^ (8 * 1) ||| x2 * 2 ^ (8 * 2) ||| x3 * 2 ^ (8 * 3) ||| x4 * 2 ^ (8 * 4) |||
      x5 * 2 ^ (8 * 5) ||| x6 * 2 ^ (8 * 6) ||| x7 * 2 ^ (8 * 7)) =
    x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * (x7 + 256 * 0))))))) := by
  simp only [← Nat.shiftLeft_eq]
  rw [or_shift_add (k := 8 * 1) (by simp; omega), or_shift_add (k := 8 * 2) (by simp [Nat.shiftLeft_eq]; omega),
    or_shift_add (k := 8 * 3) (by simp [Nat.shiftLeft_eq]; omega),
    or_shift_add (k := 8 * 4) (by simp [Nat.shiftLeft_eq]; omega),
    or_shift_add (k := 8 * 5) (by simp [Nat.shiftLeft_eq]; omega),
    or_shift_add (k := 8 * 6) (by simp [Nat.shiftLeft_eq]; omega),
    or_shift_add (k := 8 * 7) (by simp [Nat.shiftLeft_eq]; omega)]
  simp [Nat.shiftLeft_eq]; omega

theorem toNat_byte_shift (x : UInt8) (i : Nat) (hi : i < 8) :
    (x.toUInt64 <<< (8 * i).toUInt64).toNat = x.toNat * 2 ^ (8 * i) := by
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  have hx := x.toNat_lt
  have h1 : (8 * i).toUInt64.toNat % 64 = 8 * i := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : 8 * i < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  rw [h1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  calc x.toNat * 2 ^ (8 * i) < 256 * 2 ^ (8 * i) := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    _ ≤ 2 ^ 64 := by
        rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)

/-- **The driver's word reader** is the little-endian number of the eight bytes. -/
theorem u64At_eq (b : ByteArray) (o : Nat) :
    u64At b o = ofLE ((List.range 8).map fun i => b.get! (o + i)) := by
  simp only [u64At, UInt64.toNat_or]
  rw [toNat_byte_shift _ 0 (by omega), toNat_byte_shift _ 1 (by omega), toNat_byte_shift _ 2 (by omega),
    toNat_byte_shift _ 3 (by omega), toNat_byte_shift _ 4 (by omega), toNat_byte_shift _ 5 (by omega),
    toNat_byte_shift _ 6 (by omega), toNat_byte_shift _ 7 (by omega)]
  rw [or8 _ _ _ _ _ _ _ _ (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _)
    (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _)]
  simp [List.range_succ, ofLE, Nat.add_zero]

theorem wordsBytes_cons (w : Word) (ws : List Word) : wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws := rfl

theorem wordsBytes_drop (ws : List Word) : ∀ a, (wordsBytes ws).drop (8 * a) = wordsBytes (ws.drop a)
  | 0 => rfl
  | a + 1 => by
    cases ws with
    | nil => simp [wordsBytes]
    | cons w ws =>
      rw [wordsBytes_cons, show 8 * (a + 1) = 8 + 8 * a by ring, ← List.drop_drop,
        List.drop_left' (wordBytes_length w), wordsBytes_drop ws a]
      rfl

theorem wordsBytes_take (ws : List Word) : ∀ n, (wordsBytes ws).take (8 * n) = wordsBytes (ws.take n)
  | 0 => by simp [wordsBytes]
  | n + 1 => by
    cases ws with
    | nil => simp [wordsBytes]
    | cons w ws =>
      rw [wordsBytes_cons, show 8 * (n + 1) = 8 + 8 * n by ring, List.take_add,
        List.take_left' (wordBytes_length w), List.drop_left' (wordBytes_length w), wordsBytes_take ws n]
      rfl

/-- **The bytes of lanes `[a, a + n)`.** -/
theorem wordsBytes_slice (ws : List Word) (a n : Nat) :
    ((wordsBytes ws).drop (8 * a)).take (8 * n) = wordsBytes ((ws.drop a).take n) := by
  rw [wordsBytes_drop, wordsBytes_take]

/-- Equal lanes give equal slices. -/
theorem slice_eq {ws : List Word} {a b n : Nat} (ha : a + n ≤ ws.length) (hb : b + n ≤ ws.length)
    (h : ∀ l < n, lw ws (a + l) = lw ws (b + l)) : (ws.drop a).take n = (ws.drop b).take n := by
  refine List.ext_getElem (by simp; omega) fun l h1 h2 => ?_
  simp only [List.getElem_take, List.getElem_drop]
  have hl : l < n := by simp at h1; omega
  have := h l hl
  have ea : ws.getD (a + l) 0 = ws[a + l] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have eb : ws.getD (b + l) 0 = ws[b + l] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [lw] at this
  rw [ea, eb] at this
  exact BitVec.eq_of_toNat_eq this

theorem lw_of_slice {ws : List Word} {a n l : Nat} (hl : l < n) (h : a + n ≤ ws.length) :
    ((ws.drop a).take n).getD l 0 = ws.getD (a + l) 0 := by
  simp [List.getD_eq_getElem?_getD, hl]

/-! ## The bits of a decoded answer -/

/-- The four lanes of a digest whose bytes are `wordsBytes` of them. -/
theorem u64At_digest {a : Digest} {w : List Word} (hw : w.length = 4) (ha : a.toList = wordsBytes w)
    {k : Nat} (hk : k < 4) : u64At (digestBytes a) (8 * k) = (w.getD k 0).toNat := by
  rw [u64At_eq]
  have hb : ∀ i < 8, (digestBytes a).get! (8 * k + i) = (wordsBytes w).getD (8 * k + i) 0 := by
    intro i hi; rw [get!_bl, bl_digestBytes, ha]
  have e : (List.range 8).map (fun i => (digestBytes a).get! (8 * k + i)) = wordBytes (w.getD k 0) := by
    have hwb := wordsBytes_slice w k 1
    rw [List.take_one, show (w.drop k).head? = some (w.getD k 0) by
      simp [List.getD_eq_getElem?_getD, List.head?_drop, List.getElem?_eq_getElem (by omega : k < w.length)]] at hwb
    simp only [Option.toList_some] at hwb
    rw [show wordsBytes [w.getD k 0] = wordBytes (w.getD k 0) by simp [wordsBytes]] at hwb
    rw [← hwb]
    refine List.ext_getElem (by simp [wordsBytes_length]; omega) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, hb i h1, List.getElem_take, List.getElem_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    · rfl
  rw [e, ofLE_wordBytes]

/-! ## The plan's static stream facts -/

/-- What the bridge needs of the plan, checked entry by entry (decided per parameter set). -/
def entryOk (P : List PE) (e : PE) (i : Nat) : Bool :=
  match e.k with
  | .q0 => i == 0 && e.len == 7
  | .fs st => decide (32 ≤ e.len) && decide (st < i) && decide (1 ≤ i)
  | .leaf => decide (1 ≤ i)
  | .node pe h j lvl cap =>
    e.len == 64 && decide (2 ≤ i) && decide (lvl < h) && decide (j % 8 * h + h ≤ 192) &&
      decide (pe + j / 8 < i) && decide (1 ≤ pe + j / 8) &&
      (match cap with
       | none => true
       | some (ce, co, path) => co % 8 == 0 && decide (path ≤ h) && decide (32 ≤ co) &&
           decide (co + 32 * 2 ^ (h - path) ≤ (P.getD ce default).len) && decide (1 ≤ ce) && decide (ce < i))

/-- Every entry of the plan passes `entryOk`, and every length after `q₀` is a whole number of lanes. -/
def streamOkL (P : List PE) : Bool :=
  (P.tail.all fun e => e.len % 8 == 0) && P.zipIdx.all fun x => entryOk P x.1 x.2

/-- **The plan's static stream facts**: entry by entry, and the hashed length is the entries'. -/
def StreamOk (p : Params) : Prop := streamOkL (plan p) = true ∧ hashedLen p = 1 + slenS (lens p)

theorem streamOk_entry {P : List PE} (h : streamOkL P = true) {i : Nat} (hi : i < P.length) :
    entryOk P (P.getD i default) i = true := by
  simp only [streamOkL, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 (P[i], i) (List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hi]))
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem streamOk_len {P : List PE} (h : streamOkL P = true) {i : Nat} (h1 : 1 ≤ i) (hi : i < P.length) :
    (P.getD i default).len % 8 = 0 := by
  simp only [streamOkL, Bool.and_eq_true, List.all_eq_true] at h
  have hm : P.getD i default ∈ P.tail := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    rcases P with _ | ⟨x, P⟩
    · simp at hi
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      simp
  simpa using h.1 _ hm

/-! ## Offsets -/

section
variable {p : Params}

theorem lens_length (p : Params) : (lens p).length = (plan p).length := by simp [lens]

theorem lens_getD (p : Params) (i : Nat) : (lens p).getD i 0 = ((plan p).getD i default).len := by
  simp only [lens, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (plan p)[i]? <;> rfl

theorem bOff_succ (p : Params) {i : Nat} (hi : i < (plan p).length) :
    bOff p (i + 1) = bOff p i + 40 + ((plan p).getD i default).len := by
  simp only [bOff, slenS]
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [lens_length]; exact hi)]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [← lens_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [lens_length]; exact hi)]
  simp; omega

theorem plan_zero (p : Params) : (plan p).getD 0 default = ⟨.q0, 7⟩ := rfl

theorem plan_one (p : Params) : (plan p).getD 1 default = ⟨.fs 0, seedLen⟩ := rfl

theorem plan_length_ge (p : Params) : 2 ≤ (plan p).length := by simp [plan]

theorem bOff_one (p : Params) : bOff p 1 = 48 := by
  rw [show 1 = 0 + 1 from rfl, bOff_succ p (by have := plan_length_ge p; omega), plan_zero]; rfl

theorem bOff_mod (hS : streamOkL (plan p) = true) : ∀ i, 1 ≤ i → i ≤ (plan p).length → bOff p i % 8 = 0
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => by rw [bOff_one]
  | i + 2, _, hi => by
    rw [bOff_succ p (by omega)]
    have := bOff_mod hS (i + 1) (by omega) (by omega)
    have := streamOk_len hS (i := i + 1) (by omega) (by omega)
    omega

theorem bOff_eq (hS : streamOkL (plan p) = true) {i : Nat} (h1 : 1 ≤ i) (hi : i ≤ (plan p).length) :
    bOff p i = 8 * eLane p i := by
  have := bOff_mod hS i h1 hi; simp only [eLane]; omega

theorem bOff_mono (p : Params) : ∀ {i j : Nat}, i ≤ j → j ≤ (plan p).length → bOff p i ≤ bOff p j
  | i, j, hij, hj => by
    induction j with
    | zero => have : i = 0 := by omega
              subst this; exact le_rfl
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h | h
      · rw [bOff_succ p (by omega)]; have := ih (by omega) (by omega); omega
      · have : i = j + 1 := by omega
        subst this; exact le_rfl

theorem bOff_end (p : Params) : bOff p (plan p).length = 1 + slenS (lens p) := by
  simp only [bOff]; rw [← lens_length, List.take_length]

theorem eLane_succ (hS : streamOkL (plan p) = true) {i : Nat} (h1 : 1 ≤ i) (hi : i < (plan p).length) :
    eLane p (i + 1) = eLane p i + 5 + ((plan p).getD i default).len / 8 := by
  have h8 := streamOk_len hS h1 hi
  have e1 := bOff_eq hS (i := i + 1) (by omega) (by omega)
  have e2 := bOff_eq hS h1 (by omega)
  rw [bOff_succ p hi] at e1
  omega

theorem ansLane_pred (hS : streamOkL (plan p) = true) {i : Nat} (h2 : 2 ≤ i) (hi : i < (plan p).length) :
    ansLane p (i - 1) = eLane p i - 4 := by
  have := eLane_succ hS (i := i - 1) (by omega) (by omega)
  rw [show i - 1 + 1 = i by omega] at this
  simp only [ansLane, show i - 1 ≠ 0 by omega, ite_false]
  omega

end

/-! ## The decoded entries -/

section
variable {p : Params} {ws : List Word}

theorem decode_getD (p : Params) (ws : List Word) {i : Nat} (hi : i < (plan p).length) :
    (decode p ws).getD i dflt = entryAt (wordsBytes ws) (bOff p i) ((plan p).getD i default).len := by
  rw [decode, readEntries_getD _ _ _ _ (by rw [lens_length]; exact hi), lens_getD]; rfl

theorem decode_length (p : Params) (ws : List Word) : (decode p ws).length = (plan p).length := by
  rw [decode, readEntries_length, lens_length]

/-- Entries end inside the hashed length. -/
theorem entry_end (p : Params) {i : Nat} (hi : i < (plan p).length) :
    bOff p i + 40 + ((plan p).getD i default).len ≤ 1 + slenS (lens p) := by
  rw [← bOff_succ p hi, ← bOff_end]; exact bOff_mono p (by omega) le_rfl

theorem bl_qOf (p : Params) (ws : List Word) {i : Nat} (hi : i < (plan p).length) :
    bl (qOf (decode p ws) i) = ((wordsBytes ws).drop (bOff p i + 8)).take ((plan p).getD i default).len := by
  simp only [qOf, decode_getD p ws hi, entryAt]; rfl

theorem aOf_toList (p : Params) (ws : List Word) {i : Nat} (hi : i < (plan p).length)
    (hB : bOff p i + 40 + ((plan p).getD i default).len ≤ (wordsBytes ws).length) :
    (aOf (decode p ws) i).toList = ((wordsBytes ws).drop (bOff p i + 8 + ((plan p).getD i default).len)).take 32 := by
  simp only [aOf, decode_getD p ws hi, entryAt, Vector.toList_ofFn]
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take, List.length_drop]; omega)
    fun x h1 h2 => ?_
  simp only [List.length_ofFn] at h1
  rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some]

theorem qOf_size (p : Params) (ws : List Word) {i : Nat} (hi : i < (plan p).length)
    (hB : bOff p i + 40 + ((plan p).getD i default).len ≤ (wordsBytes ws).length) :
    (qOf (decode p ws) i).size = ((plan p).getD i default).len := by
  rw [size_bl, bl_qOf p ws hi, List.length_take, List.length_drop]; omega

/-- The answer of entry `i` is the four lanes at `ansLane`. -/
theorem aOf_lanes (hS : StreamOk p) (hw : hashedLen p ≤ 8 * ws.length) {i : Nat} (hi : i < (plan p).length) :
    (aOf (decode p ws) i).toList = wordsBytes ((ws.drop (ansLane p i)).take 4) := by
  have hB : bOff p i + 40 + ((plan p).getD i default).len ≤ (wordsBytes ws).length := by
    rw [wordsBytes_length]; have := entry_end p hi; rw [← hS.2] at this; omega
  rw [aOf_toList p ws hi hB, ← wordsBytes_slice]
  congr 2
  by_cases h0 : i = 0
  · subst h0
    simp only [ansLane, ite_true, bOff, List.take_zero, slenS, List.map_nil, List.sum_nil]
    rw [plan_zero]; rfl
  · have := bOff_eq hS.1 (i := i) (by omega) (by omega)
    have h8 := streamOk_len hS.1 (i := i) (by omega) hi
    simp only [ansLane, h0, ite_false]
    omega

/-- The first four lanes of a query of at least 32 bytes (entry `i ≥ 1`). -/
theorem qOf_take32 (hS : StreamOk p) (hw : hashedLen p ≤ 8 * ws.length) {i : Nat} (h1 : 1 ≤ i)
    (hi : i < (plan p).length) (h32 : 32 ≤ ((plan p).getD i default).len) :
    (bl (qOf (decode p ws) i)).take 32 = wordsBytes ((ws.drop (eLane p i + 1)).take 4) := by
  rw [bl_qOf p ws hi, List.take_take, Nat.min_eq_left h32, ← wordsBytes_slice, bOff_eq hS.1 h1 (by omega)]
  congr 2

/-- The lanes 4–7 of a 64-byte query (entry `i ≥ 1`). -/
theorem qOf_drop32 (hS : StreamOk p) (hw : hashedLen p ≤ 8 * ws.length) {i : Nat} (h1 : 1 ≤ i)
    (hi : i < (plan p).length) (h64 : ((plan p).getD i default).len = 64) :
    (bl (qOf (decode p ws) i)).drop 32 = wordsBytes ((ws.drop (eLane p i + 5)).take 4) := by
  have hB : bOff p i + 40 + ((plan p).getD i default).len ≤ (wordsBytes ws).length := by
    rw [wordsBytes_length]; have := entry_end p hi; rw [← hS.2] at this; omega
  rw [bl_qOf p ws hi, h64, List.drop_take, ← wordsBytes_slice, List.drop_drop, bOff_eq hS.1 h1 (by omega)]
  congr 2 <;> omega

/-- A byte of a query (entry `i ≥ 1`) is a byte of the stream. -/
theorem qOf_get (hS : StreamOk p) (hw : hashedLen p ≤ 8 * ws.length) {i : Nat} (h1 : 1 ≤ i)
    (hi : i < (plan p).length) {x : Nat} (hx : x < ((plan p).getD i default).len) :
    (qOf (decode p ws) i).get! x = (wordsBytes ws).getD (8 * eLane p i + 8 + x) 0 := by
  rw [get!_bl, bl_qOf p ws hi, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hx,
    List.getElem?_drop, ← List.getD_eq_getElem?_getD, bOff_eq hS.1 h1 (by omega), Nat.add_assoc]

end

/-! ## Positions -/

theorem lw_lt (ws : List Word) (j : Nat) : lw ws j < 2 ^ 64 := (ws.getD j 0).isLt

theorem testBit_three (u0 u1 u2 : Nat) (h0 : u0 < 2 ^ 64) (h1 : u1 < 2 ^ 64) (n : Nat) :
    (u0 + 2 ^ 64 * u1 + 2 ^ 128 * u2).testBit n =
      (if n < 64 then u0.testBit n else if n < 128 then u1.testBit (n - 64) else u2.testBit (n - 128)) := by
  rw [show u0 + 2 ^ 64 * u1 + 2 ^ 128 * u2 = 2 ^ 64 * (2 ^ 64 * u2 + u1) + u0 by ring,
    Nat.testBit_two_pow_mul_add _ h0]
  split_ifs with ha hb
  · rfl
  · rw [Nat.testBit_two_pow_mul_add _ h1, if_pos (by omega)]
  · rw [Nat.testBit_two_pow_mul_add _ h1, if_neg (by omega)]; congr 1

theorem posVal_bit (tr : Trace) (pe h j lvl : Nat) (hl : lvl < h) :
    (posVal tr pe h j >>> lvl) % 2 = 0 ↔ (answerBits (aOf tr (pe + j / 8))).testBit (j % 8 * h + lvl) = false := by
  have e := Nat.toNat_testBit (posVal tr pe h j) lvl
  rw [← Nat.shiftRight_eq_div_pow] at e
  rw [← e]
  simp only [posVal, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hl, decide_true, Bool.true_and]
  cases (answerBits (aOf tr (pe + j / 8))).testBit (j % 8 * h + lvl) <;> simp

theorem posVal_shift (tr : Trace) (pe h j path : Nat) (hp : path ≤ h) :
    posVal tr pe h j >>> path = (answerBits (aOf tr (pe + j / 8)) >>> (j % 8 * h + path)) % 2 ^ (h - path) := by
  apply Nat.eq_of_testBit_eq; intro t
  simp only [posVal, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.add_assoc]
  congr 1
  simp only [decide_eq_decide]; omega

/-- `posL` is the field of `k` bits from bit `s` of the number whose bits `ansBit` reads. -/
theorem posL_eq (p : Params) (ws : List Word) (A e s : Nat) :
    ∀ k, (∀ n, s ≤ n → n < s + k → ansBit p ws e n = A.testBit n) → posL p ws e s k = (A >>> s) % 2 ^ k
  | 0, _ => by simp [posL, Nat.mod_one]
  | k + 1, hb => by
    have ih := posL_eq p ws A e s k (fun n h1 h2 => hb n h1 (by omega))
    simp only [posL, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero] at ih ⊢
    rw [ih, Nat.mod_pow_succ, hb (s + k) (by omega) (by omega), Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.toNat_testBit]
    cases A.testBit (s + k) <;> simp

section
variable {p : Params} {ws : List Word}

theorem ansLane_bound (hS : StreamOk p) (hw : hashedLen p ≤ 8 * ws.length) {e : Nat} (he : e < (plan p).length) :
    ansLane p e + 4 ≤ ws.length := by
  by_cases h0 : e = 0
  · subst h0
    have := entry_end p (i := 0) he
    rw [← hS.2] at this
    simp only [ansLane, ite_true]
    have : bOff p 0 = 1 := rfl
    rw [plan_zero] at *; simp at *; omega
  · have h8 := streamOk_len hS.1 (i := e) (by omega) he
    have hb := bOff_eq hS.1 (i := e + 1) (by omega) (by omega)
    have := entry_end p he
    rw [← bOff_succ p he, ← hS.2] at this
    have := eLane_succ hS.1 (i := e) (by omega) he
    simp only [ansLane, h0, ite_false]
    omega

/-- **A decoded answer's challenge bits are its first three lanes.** -/
theorem answerBits_lanes (hS : StreamOk p) (hw : hashedLen p ≤ 8 * ws.length) {e : Nat}
    (he : e < (plan p).length) :
    answerBits (aOf (decode p ws) e) =
      lw ws (ansLane p e) + 2 ^ 64 * lw ws (ansLane p e + 1) + 2 ^ 128 * lw ws (ansLane p e + 2) := by
  have hb := ansLane_bound hS hw he
  have hlen : ((ws.drop (ansLane p e)).take 4).length = 4 := by simp; omega
  have ha := aOf_lanes hS hw he
  have u := fun k hk => u64At_digest hlen ha (k := k) hk
  simp only [answerBits]
  rw [show (0 : Nat) = 8 * 0 from rfl, u 0 (by omega), show (8 : Nat) = 8 * 1 from rfl, u 1 (by omega),
    show (16 : Nat) = 8 * 2 from rfl, u 2 (by omega)]
  simp only [lw, lw_of_slice (by omega : 0 < 4) (by omega), lw_of_slice (by omega : 1 < 4) (by omega),
    lw_of_slice (by omega : 2 < 4) (by omega), Nat.add_zero]

theorem testBit_answerBits (hS : StreamOk p) (hw : hashedLen p ≤ 8 * ws.length) {e : Nat}
    (he : e < (plan p).length) {n : Nat} (hn : n < 192) :
    (answerBits (aOf (decode p ws) e)).testBit n = ansBit p ws e n := by
  rw [answerBits_lanes hS hw he, testBit_three _ _ _ (lw_lt _ _) (lw_lt _ _), ansBit]
  split_ifs with h1 h2
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, Nat.add_zero]
  · rw [show n / 64 = 1 by omega, show n % 64 = n - 64 by omega]
  · rw [show n / 64 = 2 by omega, show n % 64 = n - 128 by omega]

end

/-! ## The bridge -/

theorem first16 : enc64 lane0C ++ enc64 lane1C =
    [0x54, 7, 0, 0, 0, 0, 0, 0, 0, 0x6c, 0x76, 0x6d, 0x2f, 0x31, 0, 0] := by decide

section
variable {p : Params} {ws : List Word}

theorem hashedLen_ge (hS : StreamOk p) : 48 ≤ hashedLen p := by
  rw [hS.2]; simp [lens, plan, slenS]; omega

theorem take16 (hS : StreamOk p) (hL : LaneLink p ws) :
    (wordsBytes ws).take 16 = enc64 lane0C ++ enc64 lane1C := by
  have h2 : 2 ≤ ws.length := by have := hL.size; have := hashedLen_ge hS; omega
  have e : ws.take 2 = [ws.getD 0 0, ws.getD 1 0] := by
    rcases ws with _ | ⟨a, _ | ⟨b, ws⟩⟩ <;> simp_all
  rw [show (16 : Nat) = 8 * 2 from rfl, wordsBytes_take, e, ← hL.c0, ← hL.c1]
  rfl

theorem wfAt_of (B : List UInt8) : ∀ (ls : List Nat) (o : Nat),
    (∀ i < ls.length, (B.drop (o + slenS (ls.take i))).take 8 = enc64 (ls.getD i 0)) → WfAt B o ls
  | [], _, _ => trivial
  | len :: ls, o, h => by
    refine ⟨by simpa [slenS] using h 0 (by simp), wfAt_of B ls _ fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simp only [List.take_succ_cons, slenS, List.map_cons, List.sum_cons, List.getD_cons_succ] at this
    simpa [slenS, Nat.add_assoc] using this

theorem drop_take_of_take {l : List UInt8} {a n m : Nat} (h : a + n ≤ m) :
    (l.drop a).take n = ((l.take m).drop a).take n := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

theorem byte0 (hS : StreamOk p) (hL : LaneLink p ws) : (wordsBytes ws).head? = some tagTrace := by
  have h := congrArg List.head? (take16 hS hL)
  rw [first16, List.head?_take] at h
  simpa [tagTrace] using h

theorem wf0 (hS : StreamOk p) (hL : LaneLink p ws) : ((wordsBytes ws).drop 1).take 8 = enc64 7 := by
  rw [drop_take_of_take (m := 16) (by omega), take16 hS hL, first16]; decide

/-- **The stream is the trace it encodes**: its first `hashedLen p` bytes are `tagTrace ::
traceBytes (decode p ws)`. -/
theorem stream_of_laneLink (hS : StreamOk p) (hL : LaneLink p ws) :
    (wordsBytes ws).take (hashedLen p) = tagTrace :: traceBytes (decode p ws) := by
  have hlen : hashedLen p ≤ (wordsBytes ws).length := by rw [wordsBytes_length]; exact hL.size
  have hw : WfAt (wordsBytes ws) 1 (lens p) := by
    refine wfAt_of _ _ _ fun i hi => ?_
    rw [lens_length] at hi
    rw [lens_getD]
    by_cases h0 : i = 0
    · subst h0
      rw [plan_zero]
      simpa [slenS] using wf0 hS hL
    · have e := bOff_eq hS.1 (i := i) (by omega) (by omega)
      simp only [bOff] at e
      rw [e, show (8 : Nat) = 8 * 1 from rfl, wordsBytes_slice]
      have hb := hL.len i (by omega) hi
      have hle : eLane p i < ws.length := by
        have := entry_end p hi; rw [← hS.2] at this
        have := hL.size; have := bOff_eq hS.1 (i := i) (by omega) (by omega); omega
      rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem hle, Option.toList_some]
      show wordBytes _ ++ [] = _
      rw [List.append_nil, wordBytes, ← hb, lw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hle,
        Option.getD_some]
  have ht := take_readEntries (wordsBytes ws) (lens p) 1 hw (by rw [← hS.2]; exact hlen)
  rw [hS.2, List.take_add, List.take_one, byte0 hS hL, Option.toList_some, ht]
  rfl

theorem eLane_bound (hS : StreamOk p) (hL : LaneLink p ws) {i : Nat} (h1 : 1 ≤ i) (hi : i < (plan p).length) :
    8 * eLane p i + 40 + ((plan p).getD i default).len ≤ 8 * ws.length := by
  have := entry_end p hi; rw [← hS.2, bOff_eq hS.1 h1 (by omega)] at this; have := hL.size; omega

/-- **Q_link's lane conditions make the decoded trace a trace of the schedule.** -/
theorem linkOk_of_laneLink (hS : StreamOk p) (hL : LaneLink p ws) : LinkOk p (decode p ws) := by
  refine ⟨decode_length p ws, fun i hi => ?_⟩
  rw [decode_length] at hi
  have hw := hL.size
  have hB : bOff p i + 40 + ((plan p).getD i default).len ≤ (wordsBytes ws).length := by
    rw [wordsBytes_length]; have := entry_end p hi; rw [← hS.2] at this; omega
  have hE := streamOk_entry hS.1 hi
  refine ⟨qOf_size p ws hi hB, ?_⟩
  rcases he : (plan p).getD i default with ⟨k, len⟩
  rw [he] at hE
  cases k with
  | q0 =>
    simp only [entryOk, Bool.and_eq_true, beq_iff_eq] at hE
    obtain ⟨rfl, rfl⟩ := hE
    show qOf (decode p ws) 0 = q0Query
    apply ba_ext
    rw [bl_qOf p ws hi, plan_zero]
    show ((wordsBytes ws).drop 9).take 7 = q0Bytes
    rw [drop_take_of_take (m := 16) (by omega), take16 hS hL, first16]; decide
  | fs st =>
    simp only [entryOk, Bool.and_eq_true, decide_eq_true_eq] at hE
    obtain ⟨⟨h32, hst⟩, h1⟩ := hE
    show (bl (qOf (decode p ws) i)).take 32 = (aOf (decode p ws) st).toList
    rw [qOf_take32 hS hw h1 hi (by rw [he]; exact h32), aOf_lanes hS hw (by omega)]
    congr 1
    have := eLane_bound hS hL h1 hi; rw [he] at this
    exact slice_eq (by omega) (ansLane_bound hS hw (by omega)) (hL.fs i hi st (by rw [he]))
  | leaf => trivial
  | node pe h j lvl cap =>
    simp only [entryOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hE
    obtain ⟨⟨⟨⟨⟨⟨h64, h2⟩, hlvl⟩, h192⟩, hpe⟩, hpe1⟩, hcap⟩ := hE
    subst h64
    have hb8 := eLane_bound hS hL (i := i) (by omega) hi; rw [he] at hb8; simp only at hb8
    have hprev := ansLane_pred hS.1 h2 hi
    have hpb := ansLane_bound hS hw (e := i - 1) (by omega)
    refine ⟨?_, ?_⟩
    · show (if (posVal (decode p ws) pe h j >>> lvl) % 2 = 0 then (bl (qOf (decode p ws) i)).take 32
        else (bl (qOf (decode p ws) i)).drop 32) = (aOf (decode p ws) (i - 1)).toList
      have hbit := posVal_bit (decode p ws) pe h j lvl hlvl
      rw [testBit_answerBits hS hw (by omega) (by omega)] at hbit
      have hn := hL.node i hi pe h j lvl cap (by rw [he])
      rw [aOf_lanes hS hw (by omega), hprev]
      by_cases hab : ansBit p ws (pe + j / 8) (j % 8 * h + lvl)
      · rw [if_neg (by rw [hbit, hab]; decide), qOf_drop32 hS hw (by omega) hi (by rw [he])]
        congr 1
        simp only [hab, ite_true] at hn
        exact slice_eq (by omega) (by omega) hn
      · rw [if_pos (by rw [hbit]; simpa using hab), qOf_take32 hS hw (by omega) hi (by rw [he]; simp)]
        congr 1
        simp only [hab, Bool.false_eq_true, ite_false] at hn
        exact slice_eq (by omega) (by omega) hn
    · rcases cap with _ | ⟨ce, co, path⟩
      · trivial
      · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcap
        obtain ⟨⟨⟨⟨⟨hco8, hph⟩, hco32⟩, hcob⟩, hce1⟩, hcei⟩ := hcap
        show aOf (decode p ws) i =
          Vector.ofFn fun x => (qOf (decode p ws) ce).get! (co + nodeBytes * (posVal (decode p ws) pe h j >>> path) + x.val)
        -- the index
        have hidx : posVal (decode p ws) pe h j >>> path = posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) := by
          rw [posVal_shift _ _ _ _ _ hph]
          symm
          apply posL_eq
          intro n h1 h2
          exact (testBit_answerBits hS hw (e := pe + j / 8) (by omega) (by omega)).symm
        have hidxlt : posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) < 2 ^ (h - path) := by
          rw [← hidx]; exact shiftRight_lt_pow (posVal_lt _ _ _ _) hph
        have hcb := eLane_bound hS hL (i := ce) hce1 (by omega)
        have hlt : nodeBytes * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + 32 ≤ 32 * 2 ^ (h - path) := by
          simp only [nodeBytes]
          have := Nat.mul_le_mul_left 32 (show posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + 1 ≤ 2 ^ (h - path) by omega)
          omega
        apply digest_ext
        rw [aOf_lanes hS hw hi, Vector.toList_ofFn, hidx]
        have hq : (List.ofFn fun x : Fin 32 => (qOf (decode p ws) ce).get!
            (co + nodeBytes * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + x.val)) =
            wordsBytes ((ws.drop (eLane p ce + 1 + co / 8 + 4 * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path))).take 4) := by
          rw [← wordsBytes_slice]
          refine List.ext_getElem (by simp [wordsBytes_length]; omega) fun x h1 h2 => ?_
          simp only [List.length_ofFn] at h1
          have hxb : co + nodeBytes * posL p ws (pe + j / 8) (j % 8 * h + path) (h - path) + x <
              ((plan p).getD ce default).len := by simp only [nodeBytes] at hlt ⊢; omega
          rw [List.getElem_ofFn, qOf_get hS hw hce1 (by omega) hxb, List.getElem_take, List.getElem_drop,
            List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [wordsBytes_length]; simp [nodeBytes] at hlt; omega),
            Option.getD_some]
          congr 1; simp only [nodeBytes]; omega
        rw [hq]
        congr 1
        refine slice_eq (by have := ansLane_bound hS hw (e := i) hi; omega) (by simp [nodeBytes] at hlt; omega) ?_
        intro l hl
        have := hL.cap i hi pe h j lvl ce co path (by rw [he]) l hl
        simp only [ansLane, show i ≠ 0 by omega, ite_false, he]
        exact this

end

end Lvm.QLink
