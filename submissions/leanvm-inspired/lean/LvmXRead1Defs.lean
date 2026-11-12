-- lvm2 X-REC2 (helper DEC): the column reads of `C_rec`'s level-1 word (tree height 12, 48-word leaves,
-- cap level 7). Adapted from this entry's `LvmXReadDefs.lean` (v1's reads at (15, 64, 7): `xLeafBytes`,
-- `readRow`, `readWd`, `crRd`, `crCapPs`, `crCopy`, `crPos`, `readIR`, their WF/cost); the walk's
-- pieces (`xDescend`, `xFindA`, `crNode`, `crLeaf`, `crCopyBody`, `lookIR4`) are v1's, unchanged.
import LvmXRead2

/-!
# The column reads of `C_rec`'s level 1: the pure reading and the program

The level-1 word's Merkle tree has `2^12` leaves (positions `p < 2^12`), its cap at level 7
(`2^7 = 128` cap nodes, carried by π), so 5 levels separate a cap node from a leaf; a leaf is the
answer of a 384-byte query (48 little-endian `K` words).

**The reading** (`readRow1 L cap p`, WP-5's `wordOf` at `ht = 12`, `wd = 48`, `lv = 7`): from the
cap node `cap[p / 2^5]`, 5 first-preimage steps down (`xDescend`), then the first entry answering
the leaf digest; its query's bytes as 48 little-endian words, missing bytes zero; a missing entry
anywhere is an erasure (48 zero words).

**WP-14's obligation** (as v1's): `readRow1 L cap p = S.wordOf L ⟨12, 48, 7, cap⟩ p` with
`S.decK = decLE`, by unfolding.

**The program** `read1IR bX pL capW wB`: for every `p < 2^12` it writes leaf word `t < 48` of
position `p` at `wB + 48 p + t`; the sorted index at `bX`, `|L|` at tape word `pL`, cap node `c`'s
four words at tape word `capW + 4 c`. Registers as v1's `readIR` (`117 … 135`, the lookup's).
-/

namespace Lvm.X

open RecursionFast

/-! ## The pure reading (WP-5's, at `ht = 12`, `wd = 48`, `lv = 7`) -/

/-- The leaf bytes the log holds under the cap `cap` of `C_rec`'s level 1 at position `p`
(`none`: an erasure); WP-5's `leafBytes L ⟨12, 48, 7, cap⟩ p`. -/
def xLeafBytes1 (L : Log) (cap : List Digest) (p : ℕ) : Option (List UInt8) :=
  (cap[p % 2 ^ 12 / 2 ^ (12 - 7)]?).bind fun v =>
    (xDescend L (12 - 7) v (p % 2 ^ 12)).bind fun d => (xFindA L d).map fun e => xQb e.1

/-- **The row the log holds under the level-1 cap at position `p`**: 48 words; an erasure reads
as the row of the empty byte string. -/
def readRow1 (L : Log) (cap : List Digest) (p : ℕ) : List BF64 :=
  xRowOf decLE 48 ((xLeafBytes1 L cap p).getD [])

/-- **The level-1 word the decoder consumes**: leaf word `t` at position `p`. -/
def readWd1 (L : Log) (cap : List Digest) (p t : ℕ) : BF64 := (readRow1 L cap p).getD t 0

@[simp] theorem readRow1_length (L : Log) (cap : List Digest) (p : ℕ) :
    (readRow1 L cap p).length = 48 := by
  simp [readRow1, xRowOf]

/-! ## The program -/

/-- The cap node of position `p`: `crTA := capW + 4 (p >> 5)`. -/
def cr1CapPs (capW : ℕ) : List Prim :=
  [.const crK 5, .op .shr crB crP crK, .const crK 2, .op .shl crB crB crK,
   .const crK (toWord capW), .op .add crTA crB crK]

/-- **The copy**: the 48 leaf words from tape word `X + 1` (`0` past the query). -/
def cr1Copy : XIR :=
  .seq (.blk [.op .add crTA crX cOne, .const cr8 0, .const crNw (toWord 48)])
    (.loopK crCw crNw (toWord 48) crCopyBody)

/-- **One position**: the cap node, 5 steps down, the leaf, the copy of its 48 words, `p += 1`. -/
def cr1Pos (bX pL capW : ℕ) : XIR :=
  .seq (.seq (.blk (cr1CapPs capW)) crLd4) (.seq (.blk [.const crOk 1, .const crNH (toWord 5)])
    (.seq (.loopK crHc crNH (toWord 5) (crNode bX pL)) (.seq (crLeaf bX pL) (.seq cr1Copy
      (.blk [.op .add crP crP cOne])))))

/-- **The column reads of `C_rec`'s level 1**: positions `0 … 2^12 − 1`, leaf word `t` of
position `p` at `wB + 48 p + t`. -/
def read1IR (bX pL capW wB : ℕ) : XIR :=
  .seq (.blk [.const crP 0, .const crWA (toWord wB), .const crNp (toWord (2 ^ 12))])
    (.loopK crCp crNp (toWord (2 ^ 12)) (cr1Pos bX pL capW))

/-! ## Well formed, frames, cost -/

theorem wf_read1IR (bX pL capW wB : ℕ) : WF (read1IR bX pL capW wB) := by
  have h1 := cr_wf_look bX pL
  have h2 : ¬ Writes (lookIR4 bX pL) 130 := cr_look_nw bX pL (by omega)
  have h3 : ¬ Writes (lookIR4 bX pL) 119 := cr_look_nw bX pL (by omega)
  simp +decide [read1IR, cr1Pos, crLd4, cr1CapPs, crGet, crChkPs, crChildPs, crNode, crLeaf,
    crCopyBody, cr1Copy, WF, Writes, Prim.dst, crP, crOk, crHc, crNH, crX, crQn, crB, crTA, crWA,
    cr8, crMk, crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3, h1, h2, h3]

theorem noLoopT_read1IR (bX pL capW wB : ℕ) : NoLoopT (read1IR bX pL capW wB) := by
  simp [read1IR, cr1Pos, crLd4, crGet, crNode, crLeaf, crCopyBody, cr1Copy, lookIR4, bsBody4,
    ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, NoLoopT]

theorem outs_read1IR (bX pL capW wB t : ℕ) : outs (read1IR bX pL capW wB) t = 0 := by
  simp [read1IR, cr1Pos, crLd4, crGet, crNode, crLeaf, crCopyBody, cr1Copy, lookIR4, bsBody4,
    ansLtIR, cmpTWord, eqTWord, foundIR4, aposIR, readAt, outs]

/-- **The registers the read writes**: the compiler's scratch, `rA`, `75 … 135`. -/
theorem read1IR_nw (bX pL capW wB : ℕ) {r : ℕ}
    (h : 136 ≤ r ∨ (5 ≤ r ∧ r < 64) ∨ (65 ≤ r ∧ r < 75)) : ¬ Writes (read1IR bX pL capW wB) r := by
  have hl : ¬ Writes (lookIR4 bX pL) r := cr_look_nw bX pL (by omega)
  simp [read1IR, cr1Pos, crLd4, cr1CapPs, crGet, crChkPs, crChildPs, crNode, crLeaf, crCopyBody,
    cr1Copy, Writes, Prim.dst, hl, crP, crOk, crHc, crNH, crX, crQn, crB, crTA, crWA, cr8, crMk,
    crCw, crNw, crCp, crNp, crV, crK, crQe, crAd, rQ0, rQ1, rQ2, rQ3, cTmp]
  omega

/-- **One position's cost**: 5 node steps (`8 + 5 · (6,529 + 3)`), the leaf (`6,500`), the copy
(`1,214`), the cap node and the rest. -/
theorem cost_cr1Pos (bX pL capW t : ℕ) : cost (cr1Pos bX pL capW) t = 40416 := by
  have a1 : (toWord 5).toNat = 5 := toNat_toWord (by norm_num)
  have a2 : (toWord 48).toNat = 48 := toNat_toWord (by norm_num)
  simp only [cr1Pos, cr1CapPs, crLd4, crNode, crGet, crChkPs, crChildPs, crLeaf, cr1Copy,
    crCopyBody, cost, cr_cost_look, blkSteps, List.length_cons, List.length_nil, a1, a2]
  norm_num

/-- **The read's exact cost**: `14 + 2^12 · (40,416 + 3) = 165,556,238 ≈ 2^27.30` steps, on every
tape. -/
theorem cost_read1IR (bX pL capW wB t : ℕ) :
    cost (read1IR bX pL capW wB) t = 14 + 2 ^ 12 * (cost (cr1Pos bX pL capW) t + 3) ∧
    cost (read1IR bX pL capW wB) t = 165556238 := by
  have a1 : (toWord (2 ^ 12)).toNat = 2 ^ 12 := toNat_toWord (by norm_num)
  have e : cost (read1IR bX pL capW wB) t = 14 + 2 ^ 12 * (cost (cr1Pos bX pL capW) t + 3) := by
    simp only [read1IR, cost, blkSteps, List.length_cons, List.length_nil, a1]
    norm_num; omega
  exact ⟨e, by rw [e, cost_cr1Pos]; norm_num⟩

/-- **The read's cost** (`2^12` positions). -/
theorem cost_read1IR_le (bX pL capW wB t : ℕ) : cost (read1IR bX pL capW wB) t ≤ 2 ^ 28 := by
  rw [(cost_read1IR bX pL capW wB t).2]; norm_num

end Lvm.X
