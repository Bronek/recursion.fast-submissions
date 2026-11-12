-- adapted from rf-k/submissions/flock-recursive/lean/FRXReadDefs.lean@8bff272b (sections
-- "Packed bytes: aligned slices", "First preimages are `ansIdx`", "The tape", "Registers",
-- "The program", "Well formed, cost, size"): `packBytes_getD`, `packBytes_drop8`,
-- `packBytes_take8`, `packBytes_digest_eq4` (from FRXRead), `pre_eq_ansIdx`, `pre_some`,
-- `pre_none`, `entries_getD_q`, `tape_query4`, `ld4IR`, `capPs`, `getIR`, `nodeChkPs`,
-- `childPs`, `nodeBody`, `colIR`, `copyBody`, `copyIR`, `posBody4`, `readIR4`, `wf_lookIR4`,
-- `lookIR4_nw`, `loK_lookIR4` (from FRXRead), `wf_readIR4`, `noLoopT_readIR4`, `outs_readIR4`,
-- `cost_lookIR4`, `cost_readIR4`.
-- New for lvm (WP-13b): the column reads of `C_rec` (BLUEPRINT §6.2 step 4), part 1: the pure
-- first-preimage reading (WP-5's `findA`/`descend`/`leafBytes`/`wordOf`, transcribed), the facts
-- about the tape it uses, the `XIR` program and its cost.
import LvmXLoop

/-!
# The column reads of `C_rec`: the pure reading and the program

`C_rec`'s Merkle tree has `2^15` leaves (positions `p < 2^15`), is binary, and has its cap at
level 7 (`2^7 = 128` cap nodes, carried by π), so 8 levels separate a cap node from a leaf. A
node is the answer of a 64-byte query `left ‖ right`; a leaf digest is the answer of the leaf's
query. A row has 64 `K` words, of which the layout occupies only the last `crOcc = 35` (lane
blocks `0 … 34`; row word `t` is lane block `63 − t`), so a leaf carries those `crOcc` words
(280 bytes, little-endian) and the reader puts `64 − crOcc` zero words in front.

**The reading** (`readRow L cap p`, WP-5's `wordOf` at `ht = 15`, `wd = 64`, `lv = 7` with
`occ 15 64 = crOcc`): from the cap node `cap[p / 2^8]`, 8 times (`n = 7, …, 0`) take the
*first* log entry whose answer is the current digest (`xFindA`); it must be a 64-byte query,
else the position is an erasure; the next digest is its left half when bit `n` of `p` is `0`,
else its right half (`xDescend`). Then the first entry whose answer is the leaf digest (no size
check): the row is `64 − crOcc` zero words followed by the query's first `crOcc` little-endian
8-byte words, missing bytes as zero (`xLeafBytes`, `xRowOf`, `decLE`). A missing entry anywhere
is an erasure: the row of the empty byte string, 64 zero words.

**WP-14's obligation.** The definitions below are WP-5's (branch `lvm/FS`, `LvmCompile.lean`:
`qb`, `dg`, `win`, `findA`, `descend`, `leafBytes`, `rowOf`, `padRow`, `wordOf`), transcribed
under other names at `ht = 15`, `wd = 64`, `lv = 7` with the decoder `decLE`. WP-14 must prove
`readRow L cap p = S.wordOf L ⟨15, 64, 7, cap⟩ p` (`Lvm.FS.Scheme.wordOf`) for WP-5's scheme `S`
with `S.decK = decLE` and `S.occ 15 64 = crOcc`; `readRow_pad` restates `readRow` as `padRow`'s
term, so the proof is by unfolding (`xDescend` against `descend` by induction on the level).

**The program** `readIR bX pL capW wB`: for every `p < 2^15` it writes row word `t < 64` of
position `p` at `wB + 64 p + t` (`64 − crOcc` zero words, then the leaf's first `crOcc` words);
the sorted index at `bX`, `|L|` at tape word `pL`, cap node `c`'s four words at tape word
`capW + 4 c`. Registers `117 … 135` (`crP` … `crAd`); the lookup `lookIR4` uses `64`,
`75 … 116` and the compiler's scratch `4`.

* `readRow_length`, `readRow_erasure`, `readRow_getD`, `readRow_pad`; `crLeafW` (a leaf word as
  the machine copies it) and `crLeafW_readRow` (as a `K` element it is `readRow`'s word
  `64 − crOcc + t`); `crRowW` (a row word as the machine stores it) and `crRowW_readRow`.
* `xFindA_some`, `xFindA_none`: the first preimage is the entry at `ansIdx`; `xDescend_succ`.
* Tape facts: `cr_tape_query` (query words of an entry), `cr_win_getD` (a 32-byte half of a
  64-byte query packs to four of its words).
* `WF`, `NoLoopT` (`safe_readIR`), `outs = 0`, 563 statements; **`cost_readIR`**:
  `14 + 2^15 · 59,964` steps (`cost_crPos = 59,961` per position, `2^30.87` in all).
-/

namespace Lvm.X

open RecursionFast

/-! ## The pure reading (WP-5's, at `ht = 15`, `wd = 64`, `lv = 7`) -/

/-- The bytes of a query (WP-5's `qb`). -/
def xQb (q : ByteArray) : List UInt8 := q.data.toList

/-- The digest of the first 32 bytes of a byte string, zero-padded (WP-5's `dg`). -/
def xDg (b : List UInt8) : Digest := Vector.ofFn fun i => b.getD i 0

/-- The 32-byte window of a query at offset `k` (WP-5's `win`). -/
def xWin (q : ByteArray) (k : ℕ) : Digest := xDg ((xQb q).drop k)

/-- The first entry of the log whose answer is `v` (WP-5's `findA`). -/
def xFindA (L : Log) (v : Digest) : Option (ByteArray × Digest) := L.find? fun e => e.2 = v

/-- Walk down `n` levels from the node `v` towards position `q` (bit `n - 1` of `q` first): the
first entry answering the node must be a 64-byte query; its left half on bit `0`, else its
right (WP-5's `descend`). -/
def xDescend (L : Log) : ℕ → Digest → ℕ → Option Digest
  | 0, v, _ => some v
  | n + 1, v, q => (xFindA L v).bind fun e =>
    if e.1.size = 64 then
      xDescend L n (if q / 2 ^ n % 2 = 0 then xWin e.1 0 else xWin e.1 32) q
    else none

/-- The leaf bytes the log holds under the cap `cap` of `C_rec` at position `p` (`none`: an
erasure); WP-5's `leafBytes L ⟨15, 64, 7, cap⟩ p`. -/
def xLeafBytes (L : Log) (cap : List Digest) (p : ℕ) : Option (List UInt8) :=
  (cap[p % 2 ^ 15 / 2 ^ (15 - 7)]?).bind fun v =>
    (xDescend L (15 - 7) v (p % 2 ^ 15)).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- **The little-endian decoder** of a `K` word: at most 8 bytes, missing bytes zero. -/
def decLE (b : List UInt8) : BF64 := BF64.ofBitVec (toWord (ofLE b))

/-- A row of `w` words from consecutive 8-byte blocks (WP-5's `rowOf`). -/
def xRowOf (dec : List UInt8 → BF64) (w : ℕ) (b : List UInt8) : List BF64 :=
  (List.range w).map fun i => dec ((b.drop (8 * i)).take 8)

/-- **The occupied words of a `C_rec` level-0 row**: a leaf carries the row's last `crOcc` words
(lane blocks `0 … 34`: the 17 stream columns and `σ'`), the reader reads the first `64 − crOcc`
as zero. The record's `recOcc` and the scheme's `occ 15 64`. -/
def crOcc : ℕ := 35

theorem crOcc_le : crOcc ≤ 64 := by decide

/-- **The row the log holds under `C_rec`'s cap at position `p`**: the first-preimage reading,
`64 − crOcc` zero words and then the leaf's first `crOcc` words; an erasure reads as the row of
the empty byte string. WP-14 proves it equal to WP-5's `S.wordOf L ⟨15, 64, 7, cap⟩ p` (with
`S.decK = decLE`, `S.occ 15 64 = crOcc`). -/
def readRow (L : Log) (cap : List Digest) (p : ℕ) : List BF64 :=
  List.replicate (64 - crOcc) 0 ++ xRowOf decLE crOcc ((xLeafBytes L cap p).getD [])

/-- **The word the decoder consumes** (`LvmXDec`'s `wd`): row word `t` at position `p`. -/
def readWd (L : Log) (cap : List Digest) (p t : ℕ) : BF64 := (readRow L cap p).getD t 0

/-! ## Facts about the reading -/

theorem decLE_nil : decLE [] = 0 := rfl

@[simp] theorem readRow_length (L : Log) (cap : List Digest) (p : ℕ) :
    (readRow L cap p).length = 64 := by
  simp [readRow, xRowOf, crOcc]

/-- Word `t < 64` of the row: zero below `64 − crOcc`, else leaf word `t − (64 − crOcc)`. -/
theorem readRow_getD (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 64) :
    (readRow L cap p).getD t 0 = if t < 64 - crOcc then 0 else
      decLE ((((xLeafBytes L cap p).getD []).drop (8 * (t - (64 - crOcc)))).take 8) := by
  have hc := crOcc_le
  rw [List.getD_eq_getElem _ _ (by rw [readRow_length]; exact ht)]
  simp only [readRow, xRowOf]
  rw [List.getElem_append]
  split_ifs with h1 h2 h2
  · simp
  · simp only [List.length_replicate] at h1; omega
  · simp only [List.length_replicate] at h1; omega
  · simp

theorem decLE_zeros : decLE (List.replicate 8 0) = 0 := by decide

/-- **The row is `Scheme.padRow`'s term** at `wd = 64`, `occ = crOcc`: the leaf's bytes after
`8 · (64 − crOcc)` zero bytes, read as 64 words. -/
theorem readRow_pad (L : Log) (cap : List Digest) (p : ℕ) :
    readRow L cap p =
      xRowOf decLE 64 (List.replicate (8 * (64 - crOcc)) 0 ++ (xLeafBytes L cap p).getD []) := by
  have hc := crOcc_le
  apply List.ext_getElem (by simp [xRowOf])
  intro t h1 h2
  have ht : t < 64 := by simpa [xRowOf] using h2
  rw [← List.getD_eq_getElem _ 0 h1, readRow_getD L cap p ht]
  simp only [xRowOf, List.getElem_map, List.getElem_range]
  split_ifs with h
  · rw [List.drop_append_of_le_length (by simp only [List.length_replicate]; omega),
      List.take_append_of_le_length (by simp only [List.length_drop, List.length_replicate]; omega),
      List.drop_replicate, List.take_replicate, Nat.min_eq_left (by omega)]
    exact decLE_zeros.symm
  · have hd : (List.replicate (8 * (64 - crOcc)) (0 : UInt8) ++ (xLeafBytes L cap p).getD []).drop
        (8 * t) = ((xLeafBytes L cap p).getD []).drop (8 * (t - (64 - crOcc))) := by
      rw [List.drop_append, List.drop_replicate, Nat.sub_eq_zero_of_le (by omega),
        List.replicate_zero, List.nil_append, List.length_replicate,
        show 8 * t - 8 * (64 - crOcc) = 8 * (t - (64 - crOcc)) by omega]
    rw [hd]

/-- **An erasure reads as 64 zero words.** -/
theorem readRow_erasure {L : Log} {cap : List Digest} {p : ℕ} (h : xLeafBytes L cap p = none) :
    readRow L cap p = List.replicate 64 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_replicate, ← List.getD_eq_getElem _ 0 h1,
    readRow_getD L cap p (by simpa using h2), h]
  split_ifs
  · rfl
  · simp [decLE_nil]

/-- The first preimage is the entry at `ansIdx`. -/
theorem xFindA_eq_ansIdx (L : Log) (d : Digest) :
    xFindA L d = (ansIdx L d).bind fun k => L[k]? := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [xFindA, ansIdx, List.find?_cons, List.findIdx?_cons] at ih ⊢
    by_cases h : e.2 = d
    · simp [h]
    · simp only [h, decide_false]
      rw [ih]
      cases L.findIdx? (fun e => decide (e.2 = d)) <;> simp

theorem xFindA_some {L : Log} {d : Digest} {k : ℕ} (h : ansIdx L d = some k) :
    ∃ hk : k < L.length, xFindA L d = some L[k] := by
  obtain ⟨hk, -⟩ := ansIdx_lt h
  exact ⟨hk, by rw [xFindA_eq_ansIdx, h, Option.bind_some, List.getElem?_eq_getElem hk]⟩

theorem xFindA_none {L : Log} {d : Digest} (h : ansIdx L d = none) : xFindA L d = none := by
  rw [xFindA_eq_ansIdx, h, Option.bind_none]

/-- **One step down the tree** at level `h + 1`: the first preimage of `d` must be a 64-byte
query; bit `h` of `p` picks its half. -/
def xStep (L : Log) (p h : ℕ) (d : Digest) : Option Digest :=
  (xFindA L d).bind fun e =>
    if e.1.size = 64 then some (if p / 2 ^ h % 2 = 0 then xWin e.1 0 else xWin e.1 32) else none

theorem xDescend_succ (L : Log) (h : ℕ) (d : Digest) (p : ℕ) :
    xDescend L (h + 1) d p = (xStep L p h d).bind fun d' => xDescend L h d' p := by
  simp only [xDescend, xStep, Option.bind_assoc]
  congr 1
  funext e
  split <;> rfl

/-- The reading under a cap node `d0`: 8 steps down to the leaf digest, then the leaf's bytes. -/
def crRd (L : Log) (d0 : Digest) (p : ℕ) : Option (List UInt8) :=
  (xDescend L 8 d0 p).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- On a position of the tree, the leaf bytes are the reading under its cap node. -/
theorem xLeafBytes_eq {L : Log} {cap : List Digest} {p : ℕ} (hp : p < 2 ^ 15)
    (hpc : p / 256 < cap.length) :
    xLeafBytes L cap p = crRd L (cap[p / 256]'hpc) p := by
  unfold xLeafBytes crRd
  rw [Nat.mod_eq_of_lt hp, show (2 : ℕ) ^ (15 - 7) = 256 from rfl, List.getElem?_eq_getElem hpc]
  all_goals rfl

/-! ## Packed bytes: aligned slices (FR's `packBytes_getD`, `…_drop8`, `…_take8`) -/

theorem cr_pk_getD (l : List UInt8) (j : ℕ) :
    (packBytes l).getD j 0 = if 8 * j < l.length then toWord (ofLE ((l.drop (8 * j)).take 8))
      else 0 := by
  by_cases h : 8 * j < l.length
  · rw [if_pos h, List.getD_eq_getElem _ _ (by rw [packBytes_length]; omega)]
    simp [packBytes]
  · rw [if_neg h, List.getD_eq_default _ _ (by rw [packBytes_length]; omega)]

theorem cr_pk_drop8 (l : List UInt8) (a j : ℕ) :
    (packBytes (l.drop (8 * a))).getD j 0 = (packBytes l).getD (a + j) 0 := by
  rw [cr_pk_getD, cr_pk_getD, List.length_drop, List.drop_drop]
  by_cases h : 8 * (a + j) < l.length
  · rw [if_pos (by omega), if_pos h, show 8 * a + 8 * j = 8 * (a + j) by ring]
  · rw [if_neg (by omega), if_neg h]

theorem cr_pk_take8 (l : List UInt8) {n j : ℕ} (hj : j < n) :
    (packBytes (l.take (8 * n))).getD j 0 = (packBytes l).getD j 0 := by
  rw [cr_pk_getD, cr_pk_getD, List.length_take, List.drop_take, List.take_take]
  by_cases h : 8 * j < l.length
  · rw [if_pos (by omega), if_pos h, Nat.min_eq_left (by omega)]
  · rw [if_neg (by omega), if_neg h]

/-- A packed word is the little-endian number of its 8 bytes (zero past the end). -/
theorem cr_pk_getD' (l : List UInt8) (j : ℕ) :
    (packBytes l).getD j 0 = toWord (ofLE ((l.drop (8 * j)).take 8)) := by
  rw [cr_pk_getD]
  split
  · rfl
  · next h =>
    have h' : l.length ≤ 8 * j := by omega
    rw [List.drop_eq_nil_of_le h']; rfl

/-- A digest's four packed words as a list. -/
theorem cr_pk_digest_eq4 (d : Digest) : packBytes d.toList =
    [(packBytes d.toList).getD 0 0, (packBytes d.toList).getD 1 0, (packBytes d.toList).getD 2 0,
      (packBytes d.toList).getD 3 0] := by
  have h := packBytes_digest_length d
  match e : packBytes d.toList, h with
  | [a0, a1, a2, a3], _ => rfl

theorem cr_xDg_toList {b : List UInt8} (h : 32 ≤ b.length) : (xDg b).toList = b.take 32 := by
  apply List.ext_getElem (by simp only [xDg, Vector.toList_ofFn, List.length_ofFn, List.length_take]; omega)
  intro i h1 h2
  have hi : i < 32 := by simpa [xDg] using h1
  have hb : i < b.length := by omega
  simp [xDg, hb]

/-- **A 32-byte window at an aligned offset packs to four of the query's words.** -/
theorem cr_win_getD (q : ByteArray) {a : ℕ} (h : 8 * a + 32 ≤ q.size) {m : ℕ} (hm : m < 4) :
    (packBytes (xWin q (8 * a)).toList).getD m 0 = (packBytes q.data.toList).getD (a + m) 0 := by
  have hl : q.data.toList.length = q.size := Array.length_toList
  rw [xWin, xQb, cr_xDg_toList (b := q.data.toList.drop (8 * a)) (by rw [List.length_drop]; omega),
    show 32 = 8 * 4 from rfl,
    cr_pk_take8 _ hm, cr_pk_drop8]

/-! ## The words the machine stores -/

/-- **Leaf word `t` of a reading** as the machine copies it: packed word `t` of the leaf bytes,
`0` for an erasure. -/
def crLeafW (o : Option (List UInt8)) (t : ℕ) : Word := (packBytes (o.getD [])).getD t 0

theorem crLeafW_none (t : ℕ) : crLeafW none t = 0 := by
  simp [crLeafW, packBytes]

theorem wK_crLeafW (o : Option (List UInt8)) (t : ℕ) :
    wK (crLeafW o t) = decLE (((o.getD []).drop (8 * t)).take 8) := by
  rw [crLeafW, cr_pk_getD']; rfl

/-- **The copied leaf word as a `K` element is the row's word `64 − crOcc + t`.** -/
theorem crLeafW_readRow (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < crOcc) :
    wK (crLeafW (xLeafBytes L cap p) t) = (readRow L cap p).getD (64 - crOcc + t) 0 := by
  have hc := crOcc_le
  rw [wK_crLeafW, readRow_getD L cap p (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

/-- **Row word `t` of a reading** as the machine stores it: `64 − crOcc` zero words, then the
leaf words `0 … crOcc − 1`. -/
def crRowW (o : Option (List UInt8)) (t : ℕ) : Word :=
  if t < 64 - crOcc then 0 else crLeafW o (t - (64 - crOcc))

theorem crRowW_none (t : ℕ) : crRowW none t = 0 := by
  simp [crRowW, crLeafW_none]

/-- **The stored word as a `K` element is the row's word.** -/
theorem crRowW_readRow (L : Log) (cap : List Digest) (p : ℕ) {t : ℕ} (ht : t < 64) :
    wK (crRowW (xLeafBytes L cap p) t) = (readRow L cap p).getD t 0 := by
  rw [readRow_getD L cap p ht, crRowW]
  split_ifs
  · rfl
  · rw [wK_crLeafW]

/-! ## The tape: query words -/

theorem cr_size_toList (q : ByteArray) : q.data.toList.length = q.size := Array.length_toList

theorem cr_len_entries (L : Log) : 5 * L.length ≤ entryOff L L.length := by
  have := length_logEntries L
  rwa [entries_length, ← entryOff_length] at this

/-- The query words of an entry within the log's words. -/
theorem cr_entries_getD_q : ∀ (L : Log) (k : ℕ) (hk : k < L.length) (j : ℕ),
    j < (L[k].1.size + 7) / 8 →
    (L.flatMap fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList).getD
      (entryOff L k + 1 + j) 0 = (packBytes L[k].1.data.toList).getD j 0
  | e :: L, 0, _, j, hj => by
    have hl : (packBytes e.1.data.toList).length = (e.1.size + 7) / 8 := by
      rw [packBytes_length, cr_size_toList]
    simp only [List.getElem_cons_zero] at hj ⊢
    simp only [entryOff, List.take_zero, List.map_nil, List.sum_nil, List.flatMap_cons,
      Nat.zero_add, bytesWords, List.cons_append]
    rw [List.getD_eq_getElem?_getD, Nat.add_comm, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [List.length_append]; omega),
      List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  | e :: L, k + 1, hk, j, hj => by
    have ho : entryOff (e :: L) (k + 1) = qWords e + entryOff L k := by
      simp [entryOff, List.take_succ_cons]
    have ih := cr_entries_getD_q L k (by simp at hk; omega) j hj
    rw [ho, List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right
      (by rw [entry_length]; omega), ← List.getD_eq_getElem?_getD, entry_length]
    simp only [List.getElem_cons_succ]
    rw [← ih]
    congr 1
    omega

/-- **The tape at entry `k`'s query**: word `j < ⌈|q|/8⌉` of `packBytes q`. -/
theorem cr_tape_query {pL : ℕ} (c : Digest) (π : Proof) (L : Log) (hs : 5 + (π.size + 7) / 8 = pL)
    {k : ℕ} (hk : k < L.length) {j : ℕ} (hj : j < (L[k].1.size + 7) / 8) :
    (extractorInput c π L).getD (posE4 pL L k + 1 + j) 0 =
      (packBytes L[k].1.data.toList).getD j 0 := by
  have hl : ((packBytes c.toList ++ [toWord π.size]) ++ packBytes π.data.toList ++
      [toWord L.length]).length = pL + 1 := by
    simp only [List.length_append, packBytes_length, ← WitnessSending.size_eq_length,
      Vector.length_toList, List.length_singleton] <;> omega
  have e2 : extractorInput c π L = ((packBytes c.toList ++ [toWord π.size]) ++
      packBytes π.data.toList ++ [toWord L.length]) ++
      L.flatMap (fun e => bytesWords e.1.data.toList ++ packBytes e.2.toList) := by
    rw [tape_eq, logWords]; simp
  rw [e2, List.getD_eq_getElem?_getD, posE4, show pL + 1 + entryOff L k + 1 + j =
      (pL + 1) + (entryOff L k + 1 + j) by omega, ← hl, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact cr_entries_getD_q L k hk j hj

/-! ## Registers (user registers `117 … 135`) -/

/-- The position `p`. -/ def crP : ℕ := 117
/-- `1` while the walk has found every entry. -/ def crOk : ℕ := 118
/-- The height loop's counter (the current height). -/ def crHc : ℕ := 119
/-- The height count (`8`). -/ def crNH : ℕ := 120
/-- The entry's tape position. -/ def crX : ℕ := 121
/-- The entry's query length. -/ def crQn : ℕ := 122
/-- Scratch (flags, the child's offset). -/ def crB : ℕ := 123
/-- A tape address. -/ def crTA : ℕ := 124
/-- The store address. -/ def crWA : ℕ := 125
/-- `8 t` in the copy. -/ def cr8 : ℕ := 126
/-- The copy's mask. -/ def crMk : ℕ := 127
/-- The copy's counter. -/ def crCw : ℕ := 128
/-- The copy's count (`64 − crOcc`, then `crOcc`). -/ def crNw : ℕ := 129
/-- The position loop's counter. -/ def crCp : ℕ := 130
/-- The position count (`2^15`). -/ def crNp : ℕ := 131
/-- A tape word. -/ def crV : ℕ := 132
/-- Constant scratch. -/ def crK : ℕ := 133
/-- The leaf's query length, `0` if no leaf was found. -/ def crQe : ℕ := 134
/-- A heap address. -/ def crAd : ℕ := 135

/-! ## The program -/

/-- `rQ0 … rQ3 :=` tape words `crTA … crTA + 3` (`crTA` ends at `+ 3`). -/
def crLd4 : XIR :=
  .seq (.input rQ0 crTA) (.seq (.blk [.op .add crTA crTA cOne]) (.seq (.input rQ1 crTA)
    (.seq (.blk [.op .add crTA crTA cOne]) (.seq (.input rQ2 crTA)
      (.seq (.blk [.op .add crTA crTA cOne]) (.input rQ3 crTA))))))

/-- The cap node of position `p`: `crTA := capW + 4 (p >> 8)`. -/
def crCapPs (capW : ℕ) : List Prim :=
  [.const crK 8, .op .shr crB crP crK, .const crK 2, .op .shl crB crB crK,
   .const crK (toWord capW), .op .add crTA crB crK]

/-- After a successful lookup: `crX := X[lo]` (the entry's position), `crQn := |q|`. -/
def crGet (bX : ℕ) : XIR :=
  .seq (.blk [.const crK (toWord bX), .op .add crAd rLo crK]) (.seq (.load crX crAd)
    (.input crQn crX))

/-- `crB := [|q| = 64]` (a node query). -/
def crChkPs : List Prim := [.const crK 64, .op .eq crB crQn crK]

/-- The child at height `h = crHc − 1`: `crTA := X + 1 + 4 · bit_h(p)`. -/
def crChildPs : List Prim :=
  [.op .sub crB crHc cOne, .op .shr crB crP crB, .op .and crB crB cOne, .const crK 2,
   .op .shl crB crB crK, .op .add crTA crX crB, .op .add crTA crTA cOne]

/-- **One step down the tree**: look up the current digest, check that its first preimage is a
64-byte query, load the half picked by bit `h` of `p`; `crOk := 0` on a missing entry or another
length. -/
def crNode (bX pL : ℕ) : XIR :=
  .ite crOk (.seq (lookIR4 bX pL) (.ite rFd (.seq (crGet bX) (.seq (.blk crChkPs)
    (.ite crB (.seq (.blk crChildPs) crLd4) (.blk [.const crOk 0])))) (.blk [.const crOk 0])))
    (.blk [])

/-- **The leaf**: look up the leaf digest; `crQe := |q|` if found (no length check), else `0`. -/
def crLeaf (bX pL : ℕ) : XIR :=
  .seq (.blk [.const crQe 0]) (.ite crOk (.seq (lookIR4 bX pL) (.ite rFd (.seq (crGet bX)
    (.blk [.op .or crQe crQn crQn])) (.blk []))) (.blk []))

/-- One leaf word: `M[crWA] := [8 t < crQe] · tape[crTA]`; advance. -/
def crCopyBody : XIR :=
  .seq (.input crV crTA) (.seq (.blk [.op .ltu crMk cr8 crQe, .const crK 0, .op .sub crMk crK crMk,
    .op .and crV crV crMk]) (.seq (.store crWA crV)
      (.blk [.op .add crWA crWA cOne, .op .add crTA crTA cOne, .const crK 8, .op .add cr8 cr8 crK])))

/-- One zero word: `M[crWA] := crV` (`crV` holds `0`); advance. -/
def crZeroBody : XIR := .seq (.store crWA crV) (.blk [.op .add crWA crWA cOne])

/-- **The row's zero prefix**: `64 − crOcc` zero words from `crWA`. -/
def crZero : XIR :=
  .seq (.blk [.const crV 0, .const crNw (toWord (64 - crOcc))])
    (.loopK crCw crNw (toWord (64 - crOcc)) crZeroBody)

/-- **The copy**: the row's zero prefix, then the leaf's first `crOcc` words from tape word
`X + 1` (`0` past the query). -/
def crCopy : XIR :=
  .seq crZero
    (.seq (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord crOcc)])
      (.loopK crCw crNw (toWord crOcc) crCopyBody))

/-- **One position**: the cap node (from tape word `capW`), 8 steps down, the leaf, its row's
64 words (the zero prefix and the copy), `p += 1`. -/
def crPos (bX pL capW : ℕ) : XIR :=
  .seq (.seq (.blk (crCapPs capW)) crLd4) (.seq (.blk [.const crOk 1, .const crNH (toWord 8)])
    (.seq (.loopK crHc crNH (toWord 8) (crNode bX pL)) (.seq (crLeaf bX pL) (.seq crCopy
      (.blk [.op .add crP crP cOne])))))

/-- **The column reads of `C_rec`**: positions `0 … 2^15 − 1`, row word `t` of position `p` at
`wB + 64 p + t`; the sorted index at `bX`, `|L|` at tape word `pL`, the cap at tape word `capW`. -/
def readIR (bX pL capW wB : ℕ) : XIR :=
  .seq (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (2 ^ 15))])
    (.loopK crCp crNp (toWord (2 ^ 15)) (crPos bX pL capW))

/-! ## Well formed, frames, cost -/

theorem cr_wf_look (bX pL : ℕ) : WF (lookIR4 bX pL) := by
  simp +decide [lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, ceil8Ps, readAt, WF,
    Writes, Prim.dst, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2, rKc,
    rAd, rX, rPa, rKa, rG, rH, rF, cTmp, regs]

/-- `lookIR4` writes only the compiler's scratch, `rA` (`64`) and registers `75 … 116`. -/
theorem cr_look_nw (bX pL : ℕ) {r : ℕ} (h : 117 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) :
    ¬ Writes (lookIR4 bX pL) r := by
  simp [lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, ceil8Ps, readAt, Writes,
    Prim.dst, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2, rKc, rAd,
    rX, rPa, rKa, rG, rH, rF, cTmp]
  omega

theorem cr_loK_look (bX pL : ℕ) : LoK (lookIR4 bX pL) := by
  simp +decide [lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, ceil8Ps, readAt,
    LoK, Prim.dst, regs, rQ0, rQ1, rQ2, rQ3, rLo, rLn, rHf, rMd, rCB, rNB, rFd, rA, rN, rQL, rT2,
    rKc, rAd, rX, rPa, rKa, rG, rH, rF, and_true, List.cons_append, List.nil_append]

theorem wf_readIR (bX pL capW wB : ℕ) : WF (readIR bX pL capW wB) := by
  have h1 := cr_wf_look bX pL
  have h2 : ¬ Writes (lookIR4 bX pL) 130 := cr_look_nw bX pL (by omega)
  have h3 : ¬ Writes (lookIR4 bX pL) 119 := cr_look_nw bX pL (by omega)
  simp +decide [readIR, crPos, crLd4, crCapPs, crGet, crChkPs, crChildPs, crNode, crLeaf,
    crCopyBody, crCopy, crZero, crZeroBody, WF, Writes, Prim.dst, crP, crOk, crHc, crNH, crX, crQn,
    crB, crTA, crWA, cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3,
    cTmp, regs, h1, h2, h3]

/-- **The registers the read writes**: the compiler's scratch, `rA`, `75 … 135`; every other
cell below `regs` is kept (`frame`). -/
theorem readIR_nw (bX pL capW wB : ℕ) {r : ℕ}
    (h : 136 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) : ¬ Writes (readIR bX pL capW wB) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := cr_look_nw bX pL (by omega)
  simp [readIR, crPos, crLd4, crCapPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    crCopy, crZero, crZeroBody, Writes, Prim.dst, hl, crP, crOk, crHc, crNH, crX, crQn, crB, crTA,
    crWA, cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3, cTmp]
  omega

/-- No tape-length loop: the read's loops are all `loopK`. -/
theorem noLoopT_readIR (bX pL capW wB : ℕ) : NoLoopT (readIR bX pL capW wB) := by
  simp [readIR, crPos, crLd4, crGet, crNode, crLeaf, crCopyBody, crCopy, crZero, crZeroBody,
    lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, NoLoopT]

/-- Loop bounds hold on every tape (no `loopT`). -/
theorem safe_readIR (I : Array Word) (t bX pL capW wB : ℕ) : Safe I t (readIR bX pL capW wB) :=
  safe_of_noLoopT (noLoopT_readIR bX pL capW wB)

/-- The compiled statement count (`progCap` is `2^20`). -/
theorem sizeIR_readIR (bX pL capW wB : ℕ) : sizeIR (readIR bX pL capW wB) = 563 := by
  simp only [readIR, crPos, crLd4, crCapPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    crCopy, crZero, crZeroBody, lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR,
    ceil8Ps, readAt, sizeIR, blkSteps, List.length_cons, List.length_nil, List.length_append]
  norm_num

theorem outs_readIR (bX pL capW wB t : ℕ) : outs (readIR bX pL capW wB) t = 0 := by
  simp [readIR, crPos, crLd4, crGet, crNode, crLeaf, crCopyBody, crCopy, crZero, crZeroBody,
    lookIR4, bsBody4, ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, outs]

/-- The lookup's cost (`LvmXModel`'s `cost_lookIR4`, proved again). -/
theorem cr_cost_look (bX pL t : ℕ) : cost (lookIR4 bX pL) t = 6486 := by
  simp only [lookIR4, bsBody4, foundIR4, ansLtIR, cmpTWord, eqTWord, aposIR, ceil8Ps, readAt, cost,
    blkSteps, List.length_append, List.length_cons, List.length_nil]
  norm_num

/-- **One position's cost**: 8 node steps (`8 + 8 · (6,529 + 3)`), the leaf (`6,500`), the row
(`1,163`: the zero prefix `273` and the copy of `crOcc` words), the cap node and the rest. -/
theorem cost_crPos (bX pL capW t : ℕ) : cost (crPos bX pL capW) t = 59961 := by
  have a1 : (toWord 8).toNat = 8 := toNat_toWord (by norm_num)
  have a2 : (toWord crOcc).toNat = 35 := toNat_toWord (by decide)
  have a3 : (toWord (64 - crOcc)).toNat = 29 := toNat_toWord (by decide)
  simp only [crPos, crCapPs, crLd4, crNode, crGet, crChkPs, crChildPs, crLeaf, crCopy, crZero,
    crZeroBody, crCopyBody, cost, cr_cost_look, blkSteps, List.length_cons, List.length_nil, a1, a2,
    a3]
  norm_num

/-- **The read's cost**: `14 + 2^15 · (59,961 + 3) = 1,964,900,366 ≈ 2^30.87` steps, on every
tape. -/
theorem cost_readIR (bX pL capW wB t : ℕ) :
    cost (readIR bX pL capW wB) t = 14 + 2 ^ 15 * (cost (crPos bX pL capW) t + 3) ∧
    cost (readIR bX pL capW wB) t = 1964900366 := by
  have a1 : (toWord (2 ^ 15)).toNat = 2 ^ 15 := toNat_toWord (by norm_num)
  have e : cost (readIR bX pL capW wB) t = 14 + 2 ^ 15 * (cost (crPos bX pL capW) t + 3) := by
    simp only [readIR, cost, blkSteps, List.length_cons, List.length_nil, a1]
    norm_num <;> omega
  exact ⟨e, by rw [e, cost_crPos]; norm_num⟩

end Lvm.X
