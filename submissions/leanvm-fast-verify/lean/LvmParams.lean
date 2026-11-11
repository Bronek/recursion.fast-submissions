/-!
# The lvm parameter record (`P20`, `P8`)

The one parameter record every part of the entry reads: the verifier `V_S`, its schedule
(`LvmSchedule`), the circuit, the extractor and the prover. It is the Lean transcription of
`docs/lvm/ref/params.py` (WP-0, `make`, `P20`, `P8`; BLUEPRINT rev 1.1 §3.1 and §11), field for
field:

* `CH`, the chain table, has `2^logN` rows; Keccak GKR of depth `12` in two segments; 64 slots per
  row (`slotLog = 6`).
* `KS`, the small Keccak table, has `2^ksLog` rows; `BITS` has `2^bitsLog` rows.
* `C_main` has `2^nuMain` words; `C_rec` has `2^nuRec` words, `nuRec = recRowsLog + 5` (32 columns
  of `2^recRowsLog` words, 17 of them the stream).
* WHIR, unique-decoding regime: per queried oracle (`Level`) the fold `ℓ`, the message log `κ`
  after the fold, the rate exponent `R`, the tree height `κ + R`, the cap exponent `c`, the path
  length `height − c`, the query count `t` (`udQueries`) and the leaf row's bytes (level 0: `2^ℓ`
  `K` words of 8 B; later levels `2^ℓ` `E` scalars of 24 B).
* The M3 feedback values `busDepth`, `leafdecReads`, `tableRounds`, `tableEvals` are frozen by
  INT-2 from WP-9's size model of the real M3 instance (`ref/loopir.py` `m3_*`, `params.py`
  `FROZEN`): they shape the bus GKR, the bus phase's one trailing scalar and the table sumcheck.
  The final tables must meet them (`M3.fitsR`, `LvmDecideM3Real`).

Query counts. `t = ⌈sec / −log₂((1 + 2^-R)/2)⌉` in `params.py`, which asserts with exact fractions
that it is the least `t ≥ 1` with `((2^R + 1) / 2^(R+1))^t ≤ 2^-sec`. Here `t` is that least `t`,
found by search on the cleared inequality `(2^R + 1)^t · 2^sec ≤ 2^((R+1) t)` (`udOk`), so no
floating point is involved; `t_P20` below checks the values.
-/

set_option autoImplicit false

namespace Lvm

/-- One queried WHIR oracle (`params.py`, `whir_levels`). -/
structure Level where
  /-- The level's index (0 for the committed word). -/
  level : Nat
  /-- The variables folded at this level, `ℓ`. -/
  fold : Nat
  /-- The message log after the fold, `κ = ν − Σ_{j ≤ i} ℓ_j`. -/
  kappa : Nat
  /-- The rate exponent `R` of the code this level opens (rate `2^-R`). -/
  rate : Nat
  /-- The Merkle tree's height: `κ + R` (the opened code has `2^(κ+R)` positions). -/
  height : Nat
  /-- The cap exponent: the commitment is the `2^cap` nodes of level `cap` of the tree. -/
  cap : Nat
  /-- The siblings on a path from a leaf to the cap: `height − cap`. -/
  path : Nat
  /-- The positions queried (`udQueries`). -/
  t : Nat
  /-- The bytes of one leaf row: `8 · 2^ℓ` at level 0, `24 · 2^ℓ` later. -/
  row : Nat
  deriving Repr, DecidableEq, Inhabited

/-- `((2^R + 1)/2^(R+1))^t ≤ 2^-sec`, cleared of denominators: the per-query escape
`1 − δ = (1 + 2^-R)/2` of the unique-decoding radius `δ = (1 − 2^-R)/2`, to the `t`-th power. -/
def udOk (sec R t : Nat) : Bool := decide ((2 ^ R + 1) ^ t * 2 ^ sec ≤ 2 ^ ((R + 1) * t))

/-- The least `t' ≥ t` with `udOk sec R t'`, searched for at most `fuel` steps. -/
def udSearch : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, t => t
  | fuel + 1, sec, R, t => if udOk sec R t then t else udSearch fuel sec R (t + 1)

/-- **The query count of a level**: the least `t ≥ 1` with `((1 + 2^-R)/2)^t ≤ 2^-sec`
(`params.py`, `ud_queries`). For `R ≥ 1` the escape is at most `3/4`, so `t ≤ 2.41 sec` and the
fuel `4 sec + 1` suffices. -/
def udQueries (sec R : Nat) : Nat := udSearch (4 * sec + 1) sec R 1

/-- The WHIR levels of a word of `2^ν` words (`params.py`, `whir_levels`): from the index `i` and
the message log `k` before the level, per `(ℓ, R, c)`. -/
def mkLevels (sec : Nat) : Nat → Nat → List (Nat × Nat × Nat) → List Level
  | _, _, [] => []
  | i, k, (l, R, c) :: rest =>
    let k' := k - l
    let h := k' + R
    { level := i, fold := l, kappa := k', rate := R, height := h, cap := c, path := h - c,
      t := udQueries sec R, row := if i = 0 then 8 * 2 ^ l else 24 * 2 ^ l } ::
      mkLevels sec (i + 1) k' rest

/-! ## Constants of the protocol (`params.py`, `make`; leanVM) -/

/-- Keccak GKR depth: rounds per segment (leanVM `KECCAK_DEPTH`). -/
def gkrDepth : Nat := 12
/-- Keccak GKR segments: `24 / gkrDepth`. -/
def gkrSegments : Nat := 2
/-- `⌈log₂ gkrSegments⌉` (leanVM `KECCAK_SEGMENT_BITS`). -/
def segmentBits : Nat := 1
/-- Slots per `CH` row, as a log: 64 (leanVM `q_keccak` slot bits). -/
def slotLog : Nat := 6
/-- `CH` slots used: `in` 25, `mid` 25, `Y` 4. -/
def chSlotsUsed : Nat := 54
/-- `C_rec` stream columns: `M_l[i] = Σ[17 i + l]`. -/
def recStreamCols : Nat := 17
/-- `C_rec` columns. -/
def recCols : Nat := 32
/-- Positions drawn from one positions answer (8 bit fields of at most 24 bits). -/
def positionsPerAnswer : Nat := 8
/-- The bus's tuple width as a log (leanVM `BUS_BITS`). -/
def busBits : Nat := 4
/-- Ring-switching stages (leanVM `RING_MAP_SHIFTS`, six challenges). -/
def ringStages : Nat := 6
/-- Bits of a `K` word. -/
def kBits : Nat := 64
/-- Lanes of a Keccak state. -/
def lanes : Nat := 25
/-- `⌈log₂ 25⌉`: the lane point's length. -/
def laneBits : Nat := 5
/-- Instances per GKR pack, as a log (sixteen). -/
def packBits : Nat := 4
/-- Coefficients of the RMFE product polynomial (leanVM `PRODUCT_BITS = 47`). -/
def productBits : Nat := 47
/-- Bit-position variables of a Keccak layer's local sumcheck (`1600 ≤ 2^11`). -/
def localBits : Nat := 11
/-- Bytes of an `E` scalar: three little-endian lanes. -/
def eBytes : Nat := 24
/-- Bytes of a Merkle node (a digest). -/
def nodeBytes : Nat := 32
/-- Bytes of a signature in a proof: `idx u64 ‖ 133 × 32 ‖ 16 × 32`. -/
def sigBytes : Nat := 8 + 133 * 32 + 16 * 32
/-- **The accumulator's variables `D`** (BLUEPRINT §12.2, A23): `Φ` is a multilinear in `D`
variables, the table point's `tableRounds` then the column index's `accLog`
(`Params.accLog = accVars − tableRounds`: 11 at `P20`, 12 at `P8`). The header carries
`acc_in = (pt ∈ E^D, y)`. Re-frozen with the final program (`fitsR` checks `nFix ≤ 2^accLog`). -/
def accVars : Nat := 28
/-- Bytes of the `S` proof header: `'S' pad[7] | b u64 | vk | c_L | s | n u64 | h | σ_leaf |
acc_in` (`acc_in`: `accVars + 1` `E` scalars, `pt` then `y`; A23). -/
def headerBytes : Nat := 8 + 8 + 32 + 32 + 32 + 8 + 32 + sigBytes + eBytes * (accVars + 1)
/-- The header offset of `acc_in` (4,928: right after `σ_leaf`). -/
def offAcc : Nat := 8 + 8 + 32 + 32 + 32 + 8 + 32 + sigBytes

/-- The first query of `V_S`: the seven bytes `"lvm/1\0\0"`. -/
def q0Bytes : List UInt8 := [0x6c, 0x76, 0x6d, 0x2f, 0x31, 0x00, 0x00]

/-! ## The record -/

/-- **The parameter record** (`params.py`, `Params`). -/
structure Params where
  /-- The set's name. -/
  name : String
  /-- `CH` has `2^logN` rows. -/
  logN : Nat
  /-- `KS` has `2^ksLog` rows. -/
  ksLog : Nat
  /-- `BITS` has `2^bitsLog` rows. -/
  bitsLog : Nat
  /-- `C_main` has `2^nuMain` words. -/
  nuMain : Nat
  /-- `C_rec` has 32 columns of `2^recRowsLog` words. -/
  recRowsLog : Nat
  /-- Per-group position escape `2^-secBits`. -/
  secBits : Nat
  /-- `C_main`'s WHIR levels. -/
  mainLevels : List Level
  /-- `C_rec`'s WHIR levels (one). -/
  recLevels : List Level
  /-- The bus grand-product GKR depth (`⌈log₂⌉` of the push leaves; INT-2 freeze). -/
  busDepth : Nat
  /-- Scalars after the bus GKR (WP-9: one, which must be zero). -/
  leafdecReads : Nat
  /-- Rounds of the table sumcheck (the tallest sumcheck table's log-height). -/
  tableRounds : Nat
  /-- Column evaluations sent after the table sumcheck (every column, fixed ones too). -/
  tableEvals : Nat
  /-- The index of the header array `PUB` among the sumcheck tables (A23: its value column is the
  one fixed column outside `Φ`; `pubCheck` evaluates it from the header lanes). -/
  pubTab : Nat
  deriving Repr, Inhabited

namespace Params

/-- `C_rec` has `2^nuRec` words. -/
def nuRec (p : Params) : Nat := p.recRowsLog + 5

/-- `C_main`'s final message log: the last level's `κ`. -/
def mainFinalLog (p : Params) : Nat := (p.mainLevels.getLastD default).kappa

/-- `C_rec`'s final message log. -/
def recFinalLog (p : Params) : Nat := (p.recLevels.getLastD default).kappa

/-- The accumulator's column-index variables `dk = D − tableRounds` (the batching challenges `κ`;
A23). -/
def accLog (p : Params) : Nat := accVars - p.tableRounds

end Params

/-- A parameter set from its free choices (`params.py`, `make`). -/
def mkParams (name : String) (logN secBits recRowsLog nuMain : Nat)
    (mainFolds mainRates mainCaps recFolds recRates recCaps : List Nat) (ksLog bitsLog : Nat)
    (busDepth leafdecReads tableRounds tableEvals pubTab : Nat) : Params where
  name := name
  logN := logN
  ksLog := ksLog
  bitsLog := bitsLog
  nuMain := nuMain
  recRowsLog := recRowsLog
  secBits := secBits
  mainLevels := mkLevels secBits 0 nuMain (mainFolds.zip (mainRates.zip mainCaps))
  recLevels := mkLevels secBits 0 (recRowsLog + 5) (recFolds.zip (recRates.zip recCaps))
  busDepth := busDepth
  leafdecReads := leafdecReads
  tableRounds := tableRounds
  tableEvals := tableEvals
  pubTab := pubTab

/-- **The production set** (BLUEPRINT §3.1; `params.py`, `P20`). The four LoopIR feedback values
are WP-16a2's freeze of the node program's M3 sizes for `P20` (`bus_depth 22, leafdec_reads 1, table_rounds 17,
table_evals 4199`). `PUB` is sumcheck table 127 (84 groups, then input array 43). -/
def P20 : Params :=
  mkParams "P20" 20 129 14 26 [6, 4, 4, 4] [1, 2, 3, 4] [8, 7, 7, 7] [6] [2] [7] 15 13
    22 1 17 4199 127

/-- **The test set** (`params.py`, `P8`): `CH` = 2^9 (leanVM's minimum Keccak batch), 20-bit
query security, `C_rec` 32 × 2^12, caps 2^4. The feedback values are INT-2's freeze for `P8`
(`21, 1, 16, 3879`, WP-16a2); `PUB` is sumcheck table 124 (81 groups, then input array 43). -/
def P8 : Params :=
  mkParams "P8" 9 20 12 23 [6, 4, 4, 4] [1, 2, 3, 4] [4, 4, 4, 4] [6] [2] [4] 13 12
    21 1 16 3879 124

/-! ## Checks against WP-0 (`ref/sizes.md`, Parameters table) -/

/-- The header is 5,624 B: WP-0's 4,928 (`sizes.md`; BLUEPRINT said 4,936) and `acc_in`'s 696 (A23). -/
theorem headerBytes_eq : headerBytes = 5624 := by decide

/-- A23's accumulator: `D = 28`, `acc_in` at byte 4,928; `dk = 11` at `P20`, `12` at `P8`;
`PUB` is sumcheck table 127 at `P20`, 124 at `P8` (after the groups). -/
theorem acc_P20_P8 : accVars = 28 ∧ offAcc = 4928 ∧ P20.accLog = 11 ∧ P8.accLog = 12 ∧
    P20.pubTab = 127 ∧ P8.pubTab = 124 := by decide

/-- The query counts of `P20`: 311, 191, 156, 142 (`C_main`) and 191 (`C_rec`). -/
theorem t_P20 : P20.mainLevels.map Level.t = [311, 191, 156, 142] ∧
    P20.recLevels.map Level.t = [191] := by decide +kernel

/-- The query counts of `P8`: 49, 30, 25, 22 and 30. -/
theorem t_P8 : P8.mainLevels.map Level.t = [49, 30, 25, 22] ∧
    P8.recLevels.map Level.t = [30] := by decide +kernel

/-- A level's geometry `[ℓ, κ, R, height, cap, path, row]`, the columns of `sizes.md`. -/
def Level.shape (L : Level) : List Nat := [L.fold, L.kappa, L.rate, L.height, L.cap, L.path, L.row]

/-- `P20`'s levels: `[ℓ, κ, R, height, cap, path, row]` as in `sizes.md`. -/
theorem levels_P20 :
    P20.mainLevels.map Level.shape =
      [[6, 20, 1, 21, 8, 13, 512], [4, 16, 2, 18, 7, 11, 384], [4, 12, 3, 15, 7, 8, 384],
        [4, 8, 4, 12, 7, 5, 384]] ∧
    P20.recLevels.map Level.shape =
      [[6, 13, 2, 15, 7, 8, 512]] ∧
    P20.mainFinalLog = 8 ∧ P20.recFinalLog = 13 ∧ P20.nuRec = 19 := by decide +kernel

/-- `P8`'s levels, as in `sizes.md`. -/
theorem levels_P8 :
    P8.mainLevels.map Level.shape =
      [[6, 17, 1, 18, 4, 14, 512], [4, 13, 2, 15, 4, 11, 384], [4, 9, 3, 12, 4, 8, 384],
        [4, 5, 4, 9, 4, 5, 384]] ∧
    P8.recLevels.map Level.shape =
      [[6, 11, 2, 13, 4, 9, 512]] ∧
    P8.mainFinalLog = 5 ∧ P8.recFinalLog = 11 ∧ P8.nuRec = 17 := by decide +kernel

/-- Every positions answer carries 8 positions: `8 · height ≤ 192` on every level of both sets. -/
theorem positions_fit :
    (P20.mainLevels ++ P20.recLevels ++ P8.mainLevels ++ P8.recLevels).all
      (fun L => decide (positionsPerAnswer * L.height ≤ 192)) = true := by decide +kernel

end Lvm
