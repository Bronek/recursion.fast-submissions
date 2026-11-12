-- New for lvm (WP-13a): the extractor's static layout, read off `V_S`'s schedule (`LvmSchedule`,
-- `LvmDriver`). FR's counterpart is `FRXChainFlock`'s `fsMsgs` (adapted: lvm's FS queries are
-- `st ‖ pending` with no tag, `LvmDriver.fsQuery`).
import LvmDriver

/-!
# The extractor's layout (BLUEPRINT §2, §6.2)

Everything the extractor program needs about an `S` proof and its child's stream, computed from
the parameter record `p` (production: `pX = P20`) by the schedule, so that `V_S`, the circuit and
the extractor read one definition.

* **Fiat–Shamir messages** `fsMsgs p`: per position `p ≥ 1` of the chain the π range `(o, len)` the
  query absorbs (position 1 is the seed: `a₀ ‖ π[8, 5624)`; position `k ≥ 2` the `k − 1`-th FS
  query `st ‖ π[pend, off)`), over the whole schedule as `LvmDriver.driveItems` reads it (an
  opening's rows and siblings are skipped, never absorbed).
* `nChain p`: the chain's targets `0 … nChain − 1` (0 is `q₀`), through the fold samples of
  `C_rec`'s level 1 (lvm2 S4: `openRec` = `ρ`, intro, `α₀` ×6, level 1's cap, level 0's positions,
  `λ`, opening, intro, `α₁` ×4, `f₂`); `alphaPos p j` / `alpha1Pos p j` the positions of `α₀_j` /
  `α₁_j`; `capRec1Off p` the π offset of level 1's cap, `f2Off p` of the final `f₂` (`2^9` `E`
  scalars), `capRecOff p` of `C_rec`'s (level 0's) cap.
* **The child's stream** (`Σ = tagTrace ‖ traceBytes tr`, lanes): `blocks p`, the trace entries
  after the seed as blocks (one query, or an opening of `t` positions); lane offsets follow.
-/

namespace Lvm.X

open RecursionFast Lvm

/-- The extractor's parameter set. -/
abbrev pX : Params := P20

/-! ## The Fiat–Shamir chain -/

/-- The FS messages `(π offset, length)` of the items, from the body offset `off` with the pending
bytes starting at `pend`, exactly as `LvmDriver.driveItems` moves them: a read or a cap advances `off`
(the cap's bytes stay pending), an FS query absorbs `π[pend, off)`, a positions item is `nPosQ` queries
(the first absorbs what is pending, the rest the state alone), and an opening skips its
`t · (row + 32 · path)` bytes, which no query absorbs (`pend := off`). -/
def fsPre (p : Params) : List Item → ℕ → ℕ → List (ℕ × ℕ)
  | [], _, _ => []
  | .read m :: r, off, pend => fsPre p r (off + eBytes * m) pend
  | .cap c _ :: r, off, pend => fsPre p r (off + nodeBytes * 2 ^ c) pend
  | .sample :: r, off, pend => (pend, off - pend) :: fsPre p r off off
  | .positions ref :: r, off, pend =>
      (pend, off - pend) :: (List.replicate ((p.level ref).nPosQ - 1) (off, 0) ++ fsPre p r off off)
  | .opening ref :: r, off, _ =>
      fsPre p r (off + (p.level ref).t * ((p.level ref).row + nodeBytes * (p.level ref).path))
        (off + (p.level ref).t * ((p.level ref).row + nodeBytes * (p.level ref).path))

/-- **The chain's messages**: position `k ≥ 1` absorbs `fsMsgs p` entry `k − 1` (the seed first). -/
def fsMsgs (p : Params) : List (ℕ × ℕ) :=
  (8, headerBytes - 8) :: fsPre p (schedule p) headerBytes headerBytes

/-- The FS queries before `C_rec`'s opening phase. -/
def nPre (p : Params) : ℕ :=
  (fsPre p (((phases p).take 7).flatMap (·.2)) headerBytes headerBytes).length

/-- `C_rec`'s level `j`. -/
def recL (p : Params) (j : ℕ) : Level := p.level ⟨.crec, j⟩

/-- The FS queries of a level's proof of work (`LvmSchedule.grindI`): the separator and the PoW
challenge, none without grinding. -/
def gQs (p : Params) : ℕ := if p.grind = 0 then 0 else 2

/-- **The chain's targets** `0 … nChain p − 1`: `q₀`, the seed, the FS queries before `openRec`,
`openRec`'s first sample (`ρ`), the fold samples of `C_rec`'s level 0 (`α₀`), its proof of work
(separator, PoW challenge; S2J), its positions queries, its `λ`, and the fold samples of level 1
(`α₁`). -/
def nChain (p : Params) : ℕ :=
  nPre p + 4 + (recL p 0).fold + gQs p + (recL p 0).nPosQ + (recL p 1).fold

/-- The chain position of level 0's fold challenge `α_j` (`j < 6`). -/
def alphaPos (p : Params) (j : ℕ) : ℕ := nPre p + 3 + j

/-- The chain position of level 1's fold challenge `α₁_j` (`j < 4`): after level 0's proof of work,
positions queries and `λ`. -/
def alpha1Pos (p : Params) (j : ℕ) : ℕ :=
  nPre p + 4 + (recL p 0).fold + gQs p + (recL p 0).nPosQ + j

/-- The π offset of `C_rec`'s level-1 cap (after level 0's last fold round's 2 scalars; v1's `f₁`
offset). -/
def capRec1Off (p : Params) : ℕ :=
  ((fsMsgs p).getD (nPre p + 2 + (recL p 0).fold) (0, 0)).1 + 2 * eBytes

/-- The π offset of `C_rec`'s final `f₂` (`2^9` `E` scalars, after level 1's last fold round's 2
scalars). -/
def f2Off (p : Params) : ℕ := ((fsMsgs p).getD (nChain p - 1) (0, 0)).1 + 2 * eBytes

/-- The π offset of `C_rec`'s cap (after `C_main`'s, BLUEPRINT §2.1 commit phase). -/
def capRecOff (p : Params) : ℕ := headerBytes + nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap

/-- `openRec` (lvm2 S4 on S2J: two levels of `C_rec`, `g`-bit proofs of work): `ρ`, the WHIR intro
round, level 0's six fold rounds, level 1's cap, level 0's proof of work (separator, nonce, PoW
challenge), positions, `λ`, opening, intro round, level 1's four fold rounds and the final `f₂`
(`2^9` scalars). -/
theorem openRec_head : ((phases pX).getD 7 default).1 = .openRec ∧
    ((phases pX).getD 7 default).2.take 31 =
      [.sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
        .sample, .read 2, .sample, .read 2, .cap 7 ⟨.crec, 1⟩, .sample, .read 1, .sample,
        .positions ⟨.crec, 0⟩, .sample, .opening ⟨.crec, 0⟩, .read 2, .sample, .read 2, .sample,
        .read 2, .sample, .read 2, .sample, .read 2, .read (2 ^ 9)] ∧
    (recL pX 0).nPosQ = 22 ∧ (recL pX 0).t = 170 ∧ (recL pX 0).row = 512 ∧ (recL pX 0).path = 8 ∧
    (recL pX 1).fold = 4 ∧ (recL pX 0).fold = 6 ∧ gQs pX = 2 := by
  decide +kernel

/-- Every chain message is lane-aligned and inside π. -/
def msgOk (p : Params) (m : ℕ × ℕ) : Bool := m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ piSize p

theorem fsMsgs_ok : ((fsMsgs pX).take (nChain pX)).all (msgOk pX) = true := by decide +kernel

/-! ## The child's stream -/

/-- A run of trace entries: one query of class `c` and length `len`, or the openings of `t`
positions (a leaf query of `row` bytes, then `path` node queries of 64 bytes each). -/
inductive Blk where
  | one (c : QClass) (len : ℕ)
  | opn (t row path : ℕ)
  deriving DecidableEq, Repr

/-- The blocks of the items, with `pend` bytes pending (`LvmSchedule.itemQueries`). -/
def itemBlks (p : Params) : List Item → ℕ → List Blk
  | [], _ => []
  | .read m :: r, pend => itemBlks p r (pend + eBytes * m)
  | .cap c _ :: r, pend => itemBlks p r (pend + nodeBytes * 2 ^ c)
  | .sample :: r, pend => .one .fs (32 + pend) :: itemBlks p r 0
  | .positions ref :: r, pend =>
      .one .fs (32 + pend) :: (List.replicate ((p.level ref).nPosQ - 1) (.one .fs 32) ++
        itemBlks p r 0)
  | .opening ref :: r, _ =>
      .opn (p.level ref).t (p.level ref).row (p.level ref).path :: itemBlks p r 0

/-- **The trace after `q₀`**: the seed, then the schedule's blocks. -/
def blocks (p : Params) : List Blk := .one .seed seedLen :: itemBlks p (schedule p) 0

/-- A block's queries `(class, length)`. -/
def Blk.queries : Blk → List (QClass × ℕ)
  | .one c len => [(c, len)]
  | .opn t row path => (List.replicate t ((.leaf, row) :: List.replicate path (.node, 64))).flatten

/-- A block's lanes in the stream (an entry is `|q|`, `q`, the answer). -/
def Blk.lanes : Blk → ℕ
  | .one _ len => 5 + len / 8
  | .opn t row path => t * (5 + row / 8 + 13 * path)

/-- A block's bytes in the reassembled proof (BLUEPRINT §2.2: a seed contributes `header[8..]`, an FS
query its message, an opening its rows and siblings). -/
def Blk.pBytes : Blk → ℕ
  | .one .seed len => len - 32
  | .one .fs len => len - 32
  | .one _ _ => 0
  | .opn t row path => t * (row + 32 * path)

/-- A block's `traceBytes` length: `8 + |q| + 32` per entry. -/
def Blk.trBytes : Blk → ℕ
  | .one _ len => 40 + len
  | .opn t row path => t * (40 + row + 104 * path)

/-- A block's entries. -/
def Blk.count : Blk → ℕ
  | .one _ _ => 1
  | .opn t _ path => t * (1 + path)

/-- A block's query lengths are lane-aligned and at least 32 bytes (`LvmXOut`'s `blkLensOk`). -/
def blkLensOkL : Blk → Bool
  | .one _ len => len % 8 == 0 && 32 ≤ len
  | .opn _ row _ => row % 8 == 0 && 32 ≤ row

/-- The words a query of `len` bytes contributes to the proof (`LvmXOut`'s `pieceLen`). -/
def pieceLenL (len : ℕ) : ℕ :=
  if len = 64 then 4 else if len = 384 ∨ len = 512 then len / 8 else (len - 32) / 8

/-- A block's contribution to the proof in words (`LvmXOut`'s `blkPieceLen`). -/
def blkPieceLenL : Blk → ℕ
  | .one _ len => pieceLenL len
  | .opn t row path => t * (pieceLenL row + path * pieceLenL 64)

/-! Per block, the measures of its output segments (`LvmXTop.segAll`): `segCost`, `segOuts` and
`segSize` (`LvmXSeg`) of `blkPSeg 0 b` and `blkTSeg 0 b` (`LvmXOutSeg`), each `+ 1` for its `cat`
where the measure counts it. -/

/-- `segCost (blkPSeg 0 b) + 1`. -/
def blkPCostL : Blk → ℕ
  | .one .seed len | .one .fs len => 14 + 36 * ((len - 32) / 8) + 1
  | .one _ _ => 1 + 1
  | .opn t row path => 12 + t * (14 + 36 * (row / 8) + (12 + path * (457 + 7)) + 1 + 7) + 1

/-- `segOuts (blkPSeg 0 b)`. -/
def blkPOutsL : Blk → ℕ
  | .one .seed len | .one .fs len => (len - 32) / 8
  | .one _ _ => 0
  | .opn t row path => t * (row / 8 + path * 4)

/-- `segSize (blkPSeg 0 b) + 1`. -/
def blkPSizeL : Blk → ℕ
  | .one .seed _ | .one .fs _ => 50 + 1
  | .one _ _ => 1 + 1
  | .opn _ _ _ => 50 + (399 + 19) + 1 + 19 + 1

/-- `segCost (blkTSeg 0 b) + 1`. -/
def blkTCostL : Blk → ℕ
  | .one _ len => 3 + (14 + 36 * (len / 8 + 4)) + 1 + 1
  | .opn t row path =>
    12 + t * (3 + (14 + 36 * (row / 8 + 4)) + 1 + (12 + path * (3 + (14 + 36 * 12) + 1 + 7)) + 1 + 7) + 1

/-- `segOuts (blkTSeg 0 b)`. -/
def blkTOutsL : Blk → ℕ
  | .one _ len => 1 + (len / 8 + 4)
  | .opn t row path => t * (1 + (row / 8 + 4) + path * (1 + 12))

/-- `segSize (blkTSeg 0 b) + 1`. -/
def blkTSizeL : Blk → ℕ
  | .one _ _ => 3 + 50 + 1 + 1
  | .opn _ _ _ => 3 + 50 + 1 + (3 + 50 + 1 + 19) + 1 + 19 + 1

/-! ## All the static numbers at `P20`, in one kernel evaluation

`layout_P20`, `blocks_tally`, `blocks_sizes` and the chain's facts (`LvmXChainL`: `piSize_eq`,
`msgs_cap`, `msgs_ok`; `LvmXOut`: `blocks_lens`; `LvmXTop`: the segments' measures) all evaluate the schedule, the blocks, the tally or the FS messages at `pX`;
one decision evaluates each of them once (separately they cost 1–3 s of kernel time each). -/

set_option maxRecDepth 100000 in
/-- The layout, the blocks' tallies and sizes, `|π|`, and the FS messages' facts at `P20`. -/
theorem layout_all_P20 :
    (nPre pX = 1294 ∧ nChain pX = 1332 ∧ alphaPos pX 0 = 1297 ∧ capRec1Off pX = 205280 ∧
      capRecOff pX = 13816 ∧ (fsMsgs pX).length = 1481 ∧
      (fsMsgs pX).getD 1331 (0, 0) = (340152, 12336) ∧ alpha1Pos pX 0 = 1328 ∧ f2Off pX = 340200 ∧
      (fsMsgs pX).getD 1302 (0, 0) = (205232, 4144)) ∧
    (1 + ((blocks pX).map Blk.count).sum = qS pX ∧
      47 + ((blocks pX).map Blk.trBytes).sum = (tally pX).trace ∧
      ((blocks pX).map fun b => match b with | .opn t _ _ => t | _ => 0).sum = (tally pX).nLeaf ∧
      ((blocks pX).map fun b => match b with | .opn t _ p => t * p | _ => 0).sum = (tally pX).nNode) ∧
    (6 + ((blocks pX).map Blk.lanes).sum = streamLanes pX ∧
      8 + ((blocks pX).map Blk.pBytes).sum = piSize pX ∧
      (blocks pX).all (fun b => match b with
        | .one _ len => len % 8 == 0 && 32 ≤ len | .opn _ row _ => row % 8 == 0) = true) ∧
    piSize pX = 783192 ∧
    (fsMsgs pX).all (fun m => 32 + m.2 ≤ queryCap) = true ∧
    ((fsMsgs pX).take (nChain pX - 1)).all (fun m =>
      m.1 % 8 == 0 && m.2 % 8 == 0 && m.1 + m.2 ≤ piSize pX && 32 + m.2 ≤ queryCap) = true ∧
    ((blocks pX).all blkLensOkL = true ∧ 8 + 8 * ((blocks pX).map blkPieceLenL).sum = piSize pX) ∧
    ((blocks pX).map blkPCostL).sum = 5517702 ∧ ((blocks pX).map blkTCostL).sum = 6015768 ∧
    ((blocks pX).map blkPOutsL).sum = 97898 ∧ ((blocks pX).map blkTOutsL).sum = 169620 ∧
    ((blocks pX).map blkPSizeL).sum = 77976 ∧ ((blocks pX).map blkTSizeL).sum = 82195 := by
  decide +kernel

/-- **The layout numbers at `P20`** (S4 on S2J, re-decided at every freeze): 1332 targets, `α₀_j` at
positions 1297–1302, level 0's separator and PoW challenge at 1303–1304, its positions queries at
1305–1326, `λ` at 1327, `α₁_j` at 1328–1331; level 1's cap at π byte 205,280 (absorbed by position
1303, the separator), `f₂` at 340,200 (absorbed by position 1332, level 1's separator), `C_rec`'s cap
at byte 13,816. -/
theorem layout_P20 : nPre pX = 1294 ∧ nChain pX = 1332 ∧ alphaPos pX 0 = 1297 ∧
    capRec1Off pX = 205280 ∧ capRecOff pX = 13816 ∧ (fsMsgs pX).length = 1481 ∧
    (fsMsgs pX).getD 1331 (0, 0) = (340152, 12336) ∧ alpha1Pos pX 0 = 1328 ∧ f2Off pX = 340200 ∧
    (fsMsgs pX).getD 1302 (0, 0) = (205232, 4144) :=
  layout_all_P20.1

/-- **The blocks are `V_S`'s queries** (`LvmSchedule.tally`): `qS − 1` entries after `q₀`, the
trace bytes, the leaf and node counts. -/
theorem blocks_tally : 1 + ((blocks pX).map Blk.count).sum = qS pX ∧
    47 + ((blocks pX).map Blk.trBytes).sum = (tally pX).trace ∧
    ((blocks pX).map fun b => match b with | .opn t _ _ => t | _ => 0).sum = (tally pX).nLeaf ∧
    ((blocks pX).map fun b => match b with | .opn t _ p => t * p | _ => 0).sum = (tally pX).nNode :=
  layout_all_P20.2.1

/-- The trace's lanes: `q₀`'s entry ends at lane 6 (with the tag byte), then the blocks fill the
stream exactly (`T = 238,827`); the reassembled proof is `piSize` bytes (header bytes 0–7 are the
constant `'S' ‖ 0⁷`). -/
theorem blocks_sizes : 6 + ((blocks pX).map Blk.lanes).sum = streamLanes pX ∧
    8 + ((blocks pX).map Blk.pBytes).sum = piSize pX ∧
    (blocks pX).all (fun b => match b with
      | .one _ len => len % 8 == 0 && 32 ≤ len | .opn _ row _ => row % 8 == 0) = true :=
  layout_all_P20.2.2.1

end Lvm.X
