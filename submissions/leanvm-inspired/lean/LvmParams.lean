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
/-- The tape's Keccak GKR depth (lvm2 BLUEPRINT2 §1.2 T2, S2: `Shape { logN, 24 }`, one segment, no
segment bits). -/
def tapeDepth : Nat := 24
/-- Lanes of the digest column `D` (lanes 0–3 of each tape row's output; BLUEPRINT2 §1.1). -/
def dLanes : Nat := 4
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
  /-- The proof-of-work bits on every WHIR level's query group (PI-GRIND; `UdConfig.grind`): `0`
  is no grinding (v1's levels and reading); with `g > 0` each level's `t` is `udQueries (sec − g) R`
  and the level reads a separating challenge, a nonce and a PoW challenge before its positions. -/
  grind : Nat
  /-- `C_main`'s WHIR levels take an out-of-domain sample on every level with a next commitment
  (lvm2 JB-VQP, J1: `C_main` at the Johnson radius, `whirLevelsJ`); `C_rec` stays in unique
  decoding. -/
  mainOod : Bool := false
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

/-- The levels with their query counts replaced by `ts` (none replaced when `ts = []`): the Johnson
regime's counts (JB-DES §1.2) are not `udQueries`. -/
def withT (ls : List Level) (ts : List Nat) : List Level :=
  if ts = [] then ls else List.zipWith (fun L t => { L with t := t }) ls ts

/-- A parameter set from its free choices (`params.py`, `make`). With `grind = g > 0` (PI-GRIND)
every level's query count is `udQueries (secBits − g) R`: the PoW challenge's `g` zero bits take
`2^-g` off each group's escape. -/
def mkParams (name : String) (logN secBits recRowsLog nuMain : Nat)
    (mainFolds mainRates mainCaps recFolds recRates recCaps : List Nat) (ksLog bitsLog : Nat)
    (busDepth leafdecReads tableRounds tableEvals pubTab : Nat) (grind : Nat := 0)
    (mainT : List Nat := []) (mainOod : Bool := false) : Params where
  name := name
  logN := logN
  ksLog := ksLog
  bitsLog := bitsLog
  nuMain := nuMain
  recRowsLog := recRowsLog
  secBits := secBits
  mainLevels := withT (mkLevels (secBits - grind) 0 nuMain (mainFolds.zip (mainRates.zip mainCaps))) mainT
  recLevels := mkLevels (secBits - grind) 0 (recRowsLog + 5) (recFolds.zip (recRates.zip recCaps))
  busDepth := busDepth
  leafdecReads := leafdecReads
  tableRounds := tableRounds
  tableEvals := tableEvals
  pubTab := pubTab
  grind := grind
  mainOod := mainOod

/-- **The production set** (lvm2 JB-VQP, J1: `C_main` at the Johnson radius, `cfgMain24J`'s counts
`230, 115, 77` and OOD samples; `C_rec` unique decoding at `g = 14`) (BLUEPRINT §3.1; lvm2 BLUEPRINT2 §1.4, §2.2: stage S2; FRZ-0's record,
`docs/lvm2/ref/params.py`, `S2P20`). `C_main` has `2^24` words (16 slots of `2^20`: `D` 4, `KS` 2,
`KSY2`/`X` 1, the recursion tables 9) and three WHIR levels `(ℓ, R, c) = (6,1,8) (4,2,7) (4,3,7)`
(`cfgMain24`, final `2^10`); `C_rec` and `KS` as v1. The five LoopIR feedback values are FRZ-1's (T-Q's S2
node program at its fixpoint, `qasm gen`, stage S4 on S2GJ1 with EV-DIET's shared position classes (R5): `21, 1, 16, 2851`, `PUB` table 127). -/
def P20 : Params :=
  mkParams "P20" 20 129 14 24 [6, 4, 4] [1, 2, 3] [8, 7, 7] [6, 4] [2, 3] [7, 7] 15 13
    21 1 16 2851 127 14 [230, 115, 77] true

/-- **The test set** (lvm2 JB-VQP, J1 at P8: Johnson counts `33, 17, 11` at 20-bit security, `g = 4`,
smallest `η` with `ηn ≥ 1`; JB-DES's model) (lvm2 FRZ-0, `S2P8`): the tape has `2^9` rows (leanVM's minimum Keccak batch),
20-bit query security, `C_main` `2^23` with three levels (caps `2^4`, final `2^9`), and, since the
depth-24 tape overflows v1's stream, `C_rec` 32 × 2^13 (`ν = 18`, final `2^12`) and `KS` `2^14`
(FRZ-0 "P8 deviation"). The feedback values are FRZ-1's (stage S4 with EV-DIET (R5): `21, 1, 16, 2522`, `PUB` 108). -/
def P8 : Params :=
  mkParams "P8" 9 20 13 23 [6, 4, 4] [1, 2, 3] [4, 4, 4] [6, 4] [2, 3] [4, 4] 14 12
    21 1 16 2522 108 4 [33, 17, 11] true

/-! ## Test sets with grinding (PI-GRIND; not frozen)

`P20`'s and `P8`'s free choices with `g` PoW bits per WHIR query group (`grind`): the query counts
drop to `udQueries (sec − g) R`, each level reads one more scalar (the nonce) and draws two more
challenges (the separator, the PoW challenge). Not a frozen record: FRZ-1 re-freezes `P20` with
`g = 14` (and the stream, layout and LoopIR feedback values with it). -/

/-- `P20` with `g = 14`: `C_main` `t = 278, 170, 139`, `C_rec` `t = 170` (PI-GRIND §3). -/
def P20G : Params :=
  mkParams "P20G" 20 129 14 24 [6, 4, 4] [1, 2, 3] [8, 7, 7] [6, 4] [2, 3] [7, 7] 15 13
    21 1 16 2851 127 14

/-- `P8` with `g = 4`: the test set of the end-to-end grinding test. -/
def P8G : Params :=
  mkParams "P8G" 9 20 13 23 [6, 4, 4] [1, 2, 3] [4, 4, 4] [6, 4] [2, 3] [4, 4] 14 12
    21 1 16 2522 108 4

/-! ## Checks against WP-0 (`ref/sizes.md`, Parameters table) -/

/-- The header is 5,624 B: WP-0's 4,928 (`sizes.md`; BLUEPRINT said 4,936) and `acc_in`'s 696 (A23). -/
theorem headerBytes_eq : headerBytes = 5624 := by decide

/-- A23's accumulator: `D = 28`, `acc_in` at byte 4,928; `dk = 12` at `P20` and `P8`;
`PUB` is sumcheck table 127 at `P20`, 108 at `P8` (after the groups). -/
theorem acc_P20_P8 : accVars = 28 ∧ offAcc = 4928 ∧ P20.accLog = 12 ∧ P8.accLog = 12 ∧
    P20.pubTab = 127 ∧ P8.pubTab = 108 := by decide

/-- The query counts of `P20`: 230, 115, 77 (`C_main`) and 170, 139 (`C_rec`, S4). -/
theorem t_P20 : P20.mainLevels.map Level.t = [230, 115, 77] ∧
    P20.recLevels.map Level.t = [170, 139] := by decide +kernel

/-- The query counts of `P8`: 33, 17, 11 and 24, 20 (S4). -/
theorem t_P8 : P8.mainLevels.map Level.t = [33, 17, 11] ∧
    P8.recLevels.map Level.t = [24, 20] := by decide +kernel

/-- A level's geometry `[ℓ, κ, R, height, cap, path, row]`, the columns of `sizes.md`. -/
def Level.shape (L : Level) : List Nat := [L.fold, L.kappa, L.rate, L.height, L.cap, L.path, L.row]

/-- `P20`'s levels: `[ℓ, κ, R, height, cap, path, row]` as in lvm2 `ref/sizes.md` (FRZ-0). -/
theorem levels_P20 :
    P20.mainLevels.map Level.shape =
      [[6, 18, 1, 19, 8, 11, 512], [4, 14, 2, 16, 7, 9, 384], [4, 10, 3, 13, 7, 6, 384]] ∧
    P20.recLevels.map Level.shape =
      [[6, 13, 2, 15, 7, 8, 512], [4, 9, 3, 12, 7, 5, 384]] ∧
    P20.mainFinalLog = 10 ∧ P20.recFinalLog = 9 ∧ P20.nuRec = 19 := by decide +kernel

/-- `P8`'s levels, as in lvm2 `ref/sizes.md` (FRZ-0). -/
theorem levels_P8 :
    P8.mainLevels.map Level.shape =
      [[6, 17, 1, 18, 4, 14, 512], [4, 13, 2, 15, 4, 11, 384], [4, 9, 3, 12, 4, 8, 384]] ∧
    P8.recLevels.map Level.shape =
      [[6, 12, 2, 14, 4, 10, 512], [4, 8, 3, 11, 4, 7, 384]] ∧
    P8.mainFinalLog = 9 ∧ P8.recFinalLog = 8 ∧ P8.nuRec = 18 := by decide +kernel

/-- The test sets are the frozen sets but for `t` and `grind` (so they cannot drift apart silently). -/
theorem shapes_G : P20G.mainLevels.map Level.shape = P20.mainLevels.map Level.shape ∧
    P20G.recLevels.map Level.shape = P20.recLevels.map Level.shape ∧
    P8G.mainLevels.map Level.shape = P8.mainLevels.map Level.shape ∧
    P8G.recLevels.map Level.shape = P8.recLevels.map Level.shape ∧
    [P20G.logN, P20G.ksLog, P20G.bitsLog, P20G.nuMain, P20G.recRowsLog, P20G.secBits, P20G.busDepth,
      P20G.leafdecReads, P20G.tableRounds, P20G.tableEvals, P20G.pubTab] =
    [P20.logN, P20.ksLog, P20.bitsLog, P20.nuMain, P20.recRowsLog, P20.secBits, P20.busDepth,
      P20.leafdecReads, P20.tableRounds, P20.tableEvals, P20.pubTab] ∧
    [P8G.logN, P8G.ksLog, P8G.bitsLog, P8G.nuMain, P8G.recRowsLog, P8G.secBits, P8G.busDepth,
      P8G.leafdecReads, P8G.tableRounds, P8G.tableEvals, P8G.pubTab] =
    [P8.logN, P8.ksLog, P8.bitsLog, P8.nuMain, P8.recRowsLog, P8.secBits, P8.busDepth,
      P8.leafdecReads, P8.tableRounds, P8.tableEvals, P8.pubTab] := by
  decide +kernel

/-- The frozen sets grind (lvm2 S2G: PI-GRIND's `g = 14` at `P20`, `g = 4` at `P8`; `refreeze2.py --stage S2G`),
and equal the test sets but for the name. -/
theorem grind_P20_P8 : P20.grind = 14 ∧ P8.grind = 4 := ⟨rfl, rfl⟩

/-- The query counts of `P20G` (`udQueries 115 R`) and `P8G` (`udQueries 16 R`). -/
theorem t_P20G_P8G : P20G.mainLevels.map Level.t = [278, 170, 139] ∧
    P20G.recLevels.map Level.t = [170, 139] ∧ P20G.grind = 14 ∧
    P8G.mainLevels.map Level.t = [39, 24, 20] ∧ P8G.recLevels.map Level.t = [24, 20] ∧ P8G.grind = 4 := by
  decide +kernel

/-- Every positions answer carries 8 positions: `8 · height ≤ 192` on every level of both sets. -/
theorem positions_fit :
    (P20.mainLevels ++ P20.recLevels ++ P8.mainLevels ++ P8.recLevels ++ P20G.mainLevels ++
      P20G.recLevels ++ P8G.mainLevels ++ P8G.recLevels).all
      (fun L => decide (positionsPerAnswer * L.height ≤ 192)) = true := by decide +kernel

end Lvm
