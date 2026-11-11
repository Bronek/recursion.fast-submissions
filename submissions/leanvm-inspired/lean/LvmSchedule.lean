import LvmParams

/-!
# The `S`-proof schedule (BLUEPRINT §2.3; `ref/params.py`, `schedule`, `queries`)

The schedule is the static list of the verifier's items, a function of the parameter record:

* `read m`: the prover sends `m` `E` scalars (24 B each) in the body of π;
* `cap c r`: the prover sends the cap of commitment `r`, its `2^c` nodes of 32 B;
* `sample`: one Fiat–Shamir query `st ‖ pending`, its answer the new state, its lanes 0–2 the
  challenge (an `E` element);
* `positions r`: `⌈t/8⌉` Fiat–Shamir queries (the first absorbs what is pending: the cap or the
  final without grinding, nothing with it), each answer giving 8 positions of `height` bits, low
  first;
* `opening r`: per position a leaf query (the row) and `path` node queries (`left ‖ right`), the
  siblings read from π bottom-up.

It is the single source for `V_S`'s driver (`LvmDriver`), the decision `F` (`LvmDecide`), the
circuit, the extractor and the prover. Every count and size below is computed from it
(`Tally`), and the `decide +kernel` checks at the end are WP-0's frozen numbers (`ref/sizes.md`,
BLUEPRINT §11 A11). The order of the phases and their items is `params.py`'s `schedule`
transcribed item for item (its protocol helpers `sumcheck`, `keccak`, `ring_switch`, `gp_gkr`,
`whir` are `sumcheckI`, `keccakI`, `smp ringStages`, `gpI`, `whirI`); the CH and KS link phases
are WP-0's [model] that WP-8 may change.

**Query classes and lengths** (BLUEPRINT §2.2). `q₀` is 7 bytes, the seed `32 + headerBytes − 8`,
an FS query `32 + pending`, a leaf query the row (512 or 384 B), a node query 64 B. The **length
rule** (`lengthRule`) says that an entry is classified by its length alone.

**Grinding** (PI-GRIND, `Params.grind = g > 0`): each WHIR level has `sample, read 1, sample`
between its cap (or final) and its positions (`grindI`). The first sample (the separator) absorbs
the cap or the final, so an FS query of `32 + 32·2^c` or `32 + 24·2^κ` B; the `read 1` is the
nonce, absorbed by the second sample (the PoW challenge, a 56 B FS query, whose top `g` bits must
be zero); the positions' first query then has nothing pending (32 B). With `g = 0` the schedule is
v1's, item for item.
-/

set_option autoImplicit false

namespace Lvm

/-- The two commitments. -/
inductive Com where
  /-- `C_main`: the chain table and every other table but the stream. -/
  | main
  /-- `C_rec`: the stream columns and `σ'`. -/
  | crec
  deriving DecidableEq, Repr, Inhabited

/-- A queried oracle: a commitment and a WHIR level. -/
structure Ref where
  /-- The commitment. -/
  com : Com
  /-- The level. -/
  lv : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An item of the schedule. -/
inductive Item where
  /-- The prover sends `m` `E` scalars. -/
  | read (m : Nat)
  /-- The prover sends the `2^c` cap nodes of the oracle `r`. -/
  | cap (c : Nat) (r : Ref)
  /-- One Fiat–Shamir challenge. -/
  | sample
  /-- The positions of the oracle `r`. -/
  | positions (r : Ref)
  /-- The openings of the oracle `r` at its positions. -/
  | opening (r : Ref)
  deriving DecidableEq, Repr, Inhabited

/-- The phases of the schedule, in order (`params.py`, `s.at`). -/
inductive Phase where
  | commit | bus | tables | tape | wire | ks | ksLink | openRec | openMain
  deriving DecidableEq, Repr, Inhabited

/-- The levels of a commitment. -/
def Params.levels (p : Params) : Com → List Level
  | .main => p.mainLevels
  | .crec => p.recLevels

/-- The level an oracle reference names. -/
def Params.level (p : Params) (r : Ref) : Level := (p.levels r.com).getD r.lv default

/-! ## Builders (the protocol helpers of `params.py`'s `Sched`) -/

/-- `read m`, nothing when `m = 0` (`Sched.read`). -/
def rd (m : Nat) : List Item := if m = 0 then [] else [.read m]

/-- `n` samples. -/
def smp (n : Nat) : List Item := List.replicate n .sample

/-- A sumcheck of `rounds` rounds with `d` scalars per round (`Sched.sumcheck`). -/
def sumcheckI (rounds d : Nat) : List Item := (List.replicate rounds (rd d ++ [.sample])).flatten

/-- One layer of the Keccak GKR (`Sched.keccak`, the loop body): the product polynomial, its
point, the pack rounds (equality mode, 2 scalars), the local rounds (3 scalars), `t`, `β`. -/
def keccakLayerI (point : Nat) : List Item :=
  List.flatten [rd productBits, smp 1, sumcheckI point 2, sumcheckI localBits 3, rd 3, smp 1]

/-- `verify_keccak` after the caller's 25 lanes (`Sched.keccak`; leanVM `keccak.rs`). -/
def keccakI (logSteps : Nat) : List Item :=
  List.flatten [smp (segmentBits + laneBits), rd 1,
    (List.replicate gkrDepth (keccakLayerI (logSteps - packBits + segmentBits))).flatten,
    sumcheckI slotLog 2, rd 1, sumcheckI packBits 2, sumcheckI slotLog 2, rd kBits]

/-- **The tape's GKR** (lvm2 BLUEPRINT2 §1.2 T2, §2.2; FRZ-0): leanVM's `verify_keccak` with
`Shape { logSteps, 24 }`, one segment: the five lane samples (no segment sample, no committed-output
read), then 24 layers of `logSteps − 4` pack rounds, and no openings. -/
def tapeLayersI (logSteps : Nat) : List Item :=
  smp laneBits ++ (List.replicate tapeDepth (keccakLayerI (logSteps - packBits))).flatten

/-- The layers of the grand-product GKR (`Sched.gp_gkr`; leanVM `gkrLayers`): one level when the
remaining depth is odd, two otherwise; per step a combiner, `point` equality-mode rounds of
`2^step` scalars, the three children's `3 · 2^step` scalars and `step` challenges. -/
def gpLayersI : (fuel layer point : Nat) → List Item
  | 0, _, _ => []
  | fuel + 1, layer, point =>
    if layer = 0 then [] else
      let step := if layer % 2 = 1 then 1 else 2
      List.flatten [smp 1, (List.replicate point (rd (2 ^ step) ++ smp 1)).flatten,
        rd (3 * 2 ^ step), smp step] ++ gpLayersI fuel (layer - step) (point + step)

/-- `verify_gkr_grand_products(depth)`: the two roots, then the layers. -/
def gpI (depth : Nat) : List Item := rd 2 ++ gpLayersI depth depth 0

/-- The tail rounds of the final WHIR level: `n` samples with a round polynomial (2 scalars)
between consecutive ones. -/
def tailI : Nat → List Item
  | 0 => []
  | 1 => [.sample]
  | n + 2 => .sample :: .read 2 :: tailI (n + 1)

/-- A level's proof of work of `g` bits (PI-GRIND; LvmWhirProg `grindPre`, `powCheck`): the
separating challenge, the nonce, the PoW challenge; nothing at `g = 0`. -/
def grindI (g : Nat) : List Item := if g = 0 then [] else [.sample, .read 1, .sample]

/-- One WHIR level (`Sched.whir`, the loop body; leanVM `whirLevels` without OOD; the proof of work
as `grindI g`): fold rounds, the next cap or the final polynomial, the proof of work, positions,
`λ`, openings, the intro round, and on the final level the tail. -/
def levelI (com : Com) (finalLog g : Nat) (L : Level) (next : Option Level) : List Item :=
  List.flatten [(List.replicate L.fold (smp 1 ++ rd 2)).flatten,
    (match next with
      | none => rd (2 ^ finalLog)
      | some N => [.cap N.cap ⟨com, L.level + 1⟩]),
    grindI g,
    [.positions ⟨com, L.level⟩], smp 1, [.opening ⟨com, L.level⟩], rd 2,
    (match next with
      | none => tailI finalLog
      | some _ => [])]

/-- The levels of a WHIR opening. -/
def whirLevelsI (com : Com) (finalLog g : Nat) : List Level → List Item
  | [] => []
  | [L] => levelI com finalLog g L none
  | L :: N :: rest => levelI com finalLog g L (some N) ++ whirLevelsI com finalLog g (N :: rest)

/-- `verify_whir`: the initial round (2 scalars), then the levels (`g` PoW bits each). -/
def whirI (com : Com) (levels : List Level) (finalLog g : Nat) : List Item :=
  rd 2 ++ whirLevelsI com finalLog g levels

/-! ## The schedule -/

/-- **The phases with their items** (`params.py`, `schedule`). The table phase ends with A23's
accumulator fold (BLUEPRINT §12.3, "phase 3b"): `κ` (`accLog` samples), the line polynomial's
`accVars + 1` coefficients, `t`, one zero scalar. lvm2 stage S2 (BLUEPRINT2 §2.2, FRZ-0): v1's `CH`
and `CH` link phases are replaced by the **tape** (T1: the instance point `r`, the 25 output
scalars; T2: the depth-24 GKR) and the **wire** (T3: the wiring sumcheck over the `logN` row
variables and `g_D`; T4: `D`'s slot reduction over the two lane bits, the 64 slices, the ring
switch); T5 sends nothing. -/
def phases (p : Params) : List (Phase × List Item) :=
  [(.commit, [.cap (p.level ⟨.main, 0⟩).cap ⟨.main, 0⟩, .cap (p.level ⟨.crec, 0⟩).cap ⟨.crec, 0⟩]),
   (.bus, List.flatten [smp (busBits + 1), gpI p.busDepth, rd p.leafdecReads]),
   (.tables, List.flatten [smp 1, sumcheckI p.tableRounds 3, rd p.tableEvals,
     smp p.accLog, rd (accVars + 1), smp 1, rd 1]),
   (.tape, List.flatten [smp p.logN, rd lanes, tapeLayersI p.logN]),
   (.wire, List.flatten [sumcheckI p.logN 2, rd 1, sumcheckI 2 2, rd kBits, smp ringStages]),
   (.ks, List.flatten [smp p.ksLog, rd lanes, keccakI p.ksLog, smp ringStages]),
   (.ksLink, List.flatten [smp (p.ksLog + laneBits), sumcheckI p.ksLog 2, rd 4]),
   (.openRec, smp 1 ++ whirI .crec p.recLevels p.recFinalLog p.grind),
   (.openMain, smp 1 ++ whirI .main p.mainLevels p.mainFinalLog p.grind)]

/-- **The schedule**: the items of every phase, in order. -/
def schedule (p : Params) : List Item := (phases p).flatMap (·.2)

/-- Positions queries of an oracle: `⌈t / 8⌉`. -/
def Level.nPosQ (L : Level) : Nat := (L.t + positionsPerAnswer - 1) / positionsPerAnswer

/-- The seed's length: the salt `a₀` and the header from byte 8. -/
def seedLen : Nat := 32 + headerBytes - 8

/-! ## Counting (`params.py`, `queries`, `body_bytes`, `build`) -/

/-- Everything counted in one pass over the items. `trace` is `Σ (8 + |q| + 32)` over the
entries so far (the bytes of `traceBytes`), `words` is `Σ (5 + ⌈|q|/8⌉)` (the extractor output's
words for the trace), `sign` is `Σ (4 + |q|)` (the SIGN request body). -/
structure Tally where
  /-- Message bytes read since the last FS query. -/
  pend : Nat := 0
  /-- Trace entries so far. -/
  entries : Nat := 0
  /-- FS queries. -/
  nFS : Nat := 0
  /-- Positions queries (a subset of the FS queries). -/
  nPos : Nat := 0
  /-- Leaf queries. -/
  nLeaf : Nat := 0
  /-- Node queries. -/
  nNode : Nat := 0
  /-- `E` scalars read. -/
  nScalars : Nat := 0
  /-- Bytes of `traceBytes`. -/
  trace : Nat := 0
  /-- The longest query. -/
  maxQ : Nat := 0
  /-- The distinct FS query lengths, ascending. -/
  fsLens : List Nat := []
  /-- Body bytes: scalars. -/
  bScalars : Nat := 0
  /-- Body bytes: caps. -/
  bCaps : Nat := 0
  /-- Body bytes: rows. -/
  bRows : Nat := 0
  /-- Body bytes: siblings. -/
  bSibs : Nat := 0
  /-- `Σ (4 + |q|)`. -/
  sign : Nat := 0
  /-- `Σ (5 + ⌈|q|/8⌉)`. -/
  words : Nat := 0
  /-- No `opening` follows unabsorbed messages. -/
  pendOk : Bool := true
  deriving Repr, Inhabited

/-- Insert into an ascending list without duplicates. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertSorted x ys

/-- One entry of `n` queries of `len` bytes each. -/
def Tally.entry (s : Tally) (n len : Nat) : Tally :=
  { s with entries := s.entries + n, trace := s.trace + n * (40 + len), maxQ := max s.maxQ len,
           sign := s.sign + n * (4 + len), words := s.words + n * (5 + (len + 7) / 8) }

/-- One FS query absorbing the pending bytes. -/
def Tally.fs (s : Tally) : Tally :=
  let len := 32 + s.pend
  { s.entry 1 len with nFS := s.nFS + 1, pend := 0, fsLens := insertSorted len s.fsLens }

/-- The tally after one item. -/
def Tally.step (p : Params) (s : Tally) : Item → Tally
  | .read m => { s with pend := s.pend + eBytes * m, nScalars := s.nScalars + m,
                        bScalars := s.bScalars + eBytes * m }
  | .cap c _ => { s with pend := s.pend + nodeBytes * 2 ^ c, bCaps := s.bCaps + nodeBytes * 2 ^ c }
  | .sample => s.fs
  | .positions r =>
    let n := (p.level r).nPosQ
    let s := s.fs
    let s := { s.entry (n - 1) 32 with nFS := s.nFS + (n - 1), nPos := s.nPos + n }
    if n ≥ 2 then { s with fsLens := insertSorted 32 s.fsLens } else s
  | .opening r =>
    let L := p.level r
    let s := (s.entry L.t L.row).entry (L.t * L.path) 64
    { s with nLeaf := s.nLeaf + L.t, nNode := s.nNode + L.t * L.path,
             bRows := s.bRows + L.t * L.row, bSibs := s.bSibs + L.t * L.path * nodeBytes,
             pendOk := s.pendOk && s.pend == 0 }

/-- The tally after `q₀` and the seed. -/
def Tally.init : Tally := ((({} : Tally).entry 1 7).entry 1 seedLen)

/-- The tally of a list of items from `s`. -/
def Tally.run (p : Params) (s : Tally) (items : List Item) : Tally := items.foldl (Tally.step p) s

/-- **The tally of the whole schedule.** -/
def tally (p : Params) : Tally := Tally.run p Tally.init (schedule p)

/-- **`qS`**, the oracle queries of `V_S` on every accepting path: `q₀`, the seed, the FS
queries, the leaf and the node queries. -/
def qS (p : Params) : Nat := (tally p).entries

/-- **`piSize`**: header and body (scalars, caps, rows, siblings). -/
def piSize (p : Params) : Nat :=
  let t := tally p
  headerBytes + t.bScalars + t.bCaps + t.bRows + t.bSibs

/-- The hashed length `L = |tagTrace ‖ traceBytes|`. -/
def hashedLen (p : Params) : Nat := 1 + (tally p).trace

/-- **`T`**: the stream's length in lanes, `L / 8` (lane alignment, BLUEPRINT §2.2). -/
def streamLanes (p : Params) : Nat := hashedLen p / 8

/-- The stream capacity of `C_rec`: `17 · 2^recRowsLog` lanes. -/
def streamCap (p : Params) : Nat := recStreamCols * 2 ^ p.recRowsLog

/-- Keccak-256 sponge blocks of the trace digest: `⌊L / 136⌋ + 1`. -/
def spongeBlocks (p : Params) : Nat := hashedLen p / 136 + 1

/-- The signed file (FORMAT.md): `8 + |π| + 8 + |traceBytes| + 8 + 4768`. -/
def fileSize (p : Params) : Nat := 8 + piSize p + 8 + (tally p).trace + 8 + 4768

/-- The extractor's output words for a node (`Extractor.lean:54-60`): `9`, the left child
(`1 + ⌈|π|/8⌉`, `1 + Σ (5 + ⌈|q|/8⌉)`, 597 for the signature) and the right `W` leaf (606). -/
def eOutWords (p : Params) : Nat :=
  9 + ((1 + (piSize p + 7) / 8) + (1 + (tally p).words) + 597) + ((1 + (1 + 48 + 7) / 8) + 1 + 597)

/-- **The length rule** (BLUEPRINT §2.2): every query but `q₀` is a whole number of lanes; no FS
query has the length of a node (64) or a leaf (a row); the seed's length is no other query's. -/
def lengthRule (p : Params) : Bool :=
  let t := tally p
  let rows := (p.mainLevels ++ p.recLevels).map Level.row
  let forbidden := 64 :: rows
  t.pendOk && t.fsLens.all (fun l => l % 8 == 0 && !forbidden.contains l && l != seedLen) &&
    (64 :: rows).all (fun l => l % 8 == 0 && l != seedLen) && seedLen % 8 == 0 &&
    seedLen != 7 && hashedLen p % 8 == 0

/-- The first trace entry of each phase that has one: its index and its byte offset in
`tagTrace ‖ traceBytes` (`sizes.md`, Stream offsets). -/
def phaseFirst (p : Params) : List (Phase × Nat × Nat) :=
  ((phases p).foldl (fun (acc : Tally × List (Phase × Nat × Nat)) ph =>
    let s' := Tally.run p acc.1 ph.2
    (s', if s'.entries > acc.1.entries then acc.2 ++ [(ph.1, acc.1.entries, 1 + acc.1.trace)]
      else acc.2)) (Tally.init, [])).2

/-! ## The query sequence (for tests and offsets; `params.py`, `queries`) -/

/-- The query classes. -/
inductive QClass where
  | q0 | seed | fs | leaf | node
  deriving DecidableEq, Repr, Inhabited

/-- The queries of one item from the pending bytes: their classes and lengths. -/
def itemQueries (p : Params) (pend : Nat) : Item → List (QClass × Nat)
  | .read _ | .cap _ _ => []
  | .sample => [(.fs, 32 + pend)]
  | .positions r => (.fs, 32 + pend) :: List.replicate ((p.level r).nPosQ - 1) (.fs, 32)
  | .opening r =>
    let L := p.level r
    (List.replicate L.t ((.leaf, L.row) :: List.replicate L.path (.node, 64))).flatten

/-- Pending bytes after an item. -/
def pendAfter (pend : Nat) : Item → Nat
  | .read m => pend + eBytes * m
  | .cap c _ => pend + nodeBytes * 2 ^ c
  | _ => 0

/-- **The query sequence** of `V_S` on an accepting path: classes and lengths, in order. -/
def queryList (p : Params) : List (QClass × Nat) :=
  [(.q0, 7), (.seed, seedLen)] ++
    ((schedule p).foldl (fun (acc : Nat × Array (QClass × Nat)) it =>
      (pendAfter acc.1 it, acc.2 ++ (itemQueries p acc.1 it).toArray)) (0, #[])).2.toList

/-! ## Checks against the frozen numbers (lvm2 FRZ-0: `docs/lvm2/ref/sizes.md`, `params.py --check`; exact given the [model] record) -/

set_option maxRecDepth 100000 in
/-- All the `P20` checks below in one kernel check, so that `tally P20` is evaluated once
(BS-1: the eight separate checks took 16 s of kernel time, the two combined 7 s). -/
private theorem checks_P20 : (qS P20 = 9916 ∧ (tally P20).nFS = 1461 ∧ (tally P20).nLeaf = 849 ∧
    (tally P20).nNode = 7604 ∧ (tally P20).nPos = 107 ∧ (tally P20).nScalars = 18106) ∧
    (piSize P20 = 1094248 ∧ (tally P20).bScalars = 434544 ∧
    (tally P20).bCaps = 20480 ∧ (tally P20).bRows = 390272 ∧ (tally P20).bSibs = 243328 ∧
    hashedLen P20 = 1781000 ∧ streamLanes P20 = 222625 ∧ streamCap P20 = 278528 ∧
    spongeBlocks P20 = 13096) ∧
    (fileSize P20 = 2880039 ∧ (tally P20).sign = 1424023 ∧
    eOutWords P20 = 360620 ∧ (tally P20).maxQ = 196688 ∧ seedLen = 5648) ∧
    (lengthRule P20 = true ∧ (tally P20).fsLens =
    [32, 56, 80, 104, 128, 320, 632, 728, 1160, 1184, 1568, 4176, 12320, 24656, 91352, 196688]) ∧
    (phaseFirst P20 =
    [(.bus, 2, 5736), (.tables, 150, 42456), (.tape, 180, 137880), (.wire, 901, 256656),
     (.ks, 929, 261288), (.ksLink, 1272, 319752), (.openRec, 1307, 322992),
     (.openMain, 3071, 788240)]) ∧
    (100 * streamLanes P20 ≤ 95 * streamCap P20 ∧ 100 * qS P20 ≤ 95 * 16384 ∧
    100 * (tally P20).maxQ ≤ 95 * 2 ^ 20 ∧ 100 * spongeBlocks P20 ≤ 95 * 2 ^ P20.recRowsLog) := by
  decide +kernel

/-- All the `P8` checks below in one kernel check, so that `tally P8` is evaluated once. -/
private theorem checks_P8 : (qS P8 = 2711 ∧ (tally P8).nFS = 1059 ∧ (tally P8).nLeaf = 134 ∧
    (tally P8).nNode = 1516 ∧ (tally P8).nPos = 19 ∧ (tally P8).nScalars = 12675 ∧
    piSize P8 = 421952 ∧ hashedLen P8 = 612824 ∧ streamLanes P8 = 76603 ∧
    streamCap P8 = 139264 ∧ (tally P8).maxQ = 98384 ∧ fileSize P8 = 1039567 ∧
    (tally P8).sign = 515227 ∧ eOutWords P8 = 130561) ∧
    (lengthRule P8 = true ∧ (tally P8).fsLens =
    [32, 56, 80, 104, 128, 176, 320, 592, 632, 728, 1056, 1160, 1184, 1568, 12368, 86696, 98384]) := by
  decide +kernel

/-- `P20`: `qS = 9,916` = 1 + 1 + 1,461 FS + 849 leaf + 7,604 node; 107 positions queries;
18,106 scalars. -/
theorem qS_P20 : qS P20 = 9916 ∧ (tally P20).nFS = 1461 ∧ (tally P20).nLeaf = 849 ∧
    (tally P20).nNode = 7604 ∧ (tally P20).nPos = 107 ∧ (tally P20).nScalars = 18106 :=
  checks_P20.1

/-- `P20`: `piSize = 1,094,248` B (scalars 434,544, caps 20,480, rows 390,272, siblings
243,328), `L = 1,781,000`, `T = 222,625` lanes of a capacity of 278,528. -/
theorem sizes_P20 : piSize P20 = 1094248 ∧ (tally P20).bScalars = 434544 ∧
    (tally P20).bCaps = 20480 ∧ (tally P20).bRows = 390272 ∧ (tally P20).bSibs = 243328 ∧
    hashedLen P20 = 1781000 ∧ streamLanes P20 = 222625 ∧ streamCap P20 = 278528 ∧
    spongeBlocks P20 = 13096 :=
  checks_P20.2.1

/-- `P20`: signed file 2,880,039 B, SIGN body 1,424,023 B, `E` output 360,620 words, largest
query 196,688 B, seed 5,648 B. -/
theorem files_P20 : fileSize P20 = 2880039 ∧ (tally P20).sign = 1424023 ∧
    eOutWords P20 = 360620 ∧ (tally P20).maxQ = 196688 ∧ seedLen = 5648 :=
  checks_P20.2.2.1

/-- `P20`: the length rule holds, and the distinct FS lengths are sixteen. -/
theorem lengthRule_P20 : lengthRule P20 = true ∧ (tally P20).fsLens =
    [32, 56, 80, 104, 128, 320, 632, 728, 1160, 1184, 1568, 4176, 12320, 24656, 91352, 196688] :=
  checks_P20.2.2.2.1

/-- `P20`: the first entry of each phase (FRZ-0, "Sizes per phase"). -/
theorem phaseFirst_P20 : phaseFirst P20 =
    [(.bus, 2, 5736), (.tables, 150, 42456), (.tape, 180, 137880), (.wire, 901, 256656),
     (.ks, 929, 261288), (.ksLink, 1272, 319752), (.openRec, 1307, 322992),
     (.openMain, 3071, 788240)] :=
  checks_P20.2.2.2.2.1

/-- `P8`: `qS = 2,711` (1,059 FS, 134 leaf, 1,516 node; 19 positions), 12,675 scalars,
`piSize = 421,952`, `L = 612,824`, `T = 76,603` of 139,264, largest query 98,384. -/
theorem sizes_P8 : qS P8 = 2711 ∧ (tally P8).nFS = 1059 ∧ (tally P8).nLeaf = 134 ∧
    (tally P8).nNode = 1516 ∧ (tally P8).nPos = 19 ∧ (tally P8).nScalars = 12675 ∧
    piSize P8 = 421952 ∧ hashedLen P8 = 612824 ∧ streamLanes P8 = 76603 ∧
    streamCap P8 = 139264 ∧ (tally P8).maxQ = 98384 ∧ fileSize P8 = 1039567 ∧
    (tally P8).sign = 515227 ∧ eOutWords P8 = 130561 :=
  checks_P8.1

/-- `P8`: the length rule and seventeen distinct FS lengths. -/
theorem lengthRule_P8 : lengthRule P8 = true ∧ (tally P8).fsLens =
    [32, 56, 80, 104, 128, 176, 320, 592, 632, 728, 1056, 1160, 1184, 1568, 12368, 86696, 98384] :=
  checks_P8.2

/-- The grinding test sets (PI-GRIND, not frozen): the length rule holds (the separator's FS query
absorbs a cap or a final, the PoW challenge's is 56 B, the positions' first 32 B), and their sizes:
P20G `qS = 9,000`, `piSize = 1,025,800`, `T = 206,193`; P8G `qS = 2,381`, `piSize = 399,840`,
`T = 70,977`. -/
theorem checks_G : lengthRule P20G = true ∧ qS P20G = 9000 ∧ piSize P20G = 1025800 ∧
    streamLanes P20G = 206193 ∧ lengthRule P8G = true ∧ qS P8G = 2381 ∧ piSize P8G = 399840 ∧
    streamLanes P8G = 70977 := by
  decide +kernel

/-- The capacities of BLUEPRINT §3.3 with WP-0's 5 % margin: `T ≤ 0.95 ·` the stream capacity,
`qS ≤ 0.95 · 16384`, the largest query `≤ 0.95 · 2^20`, sponge blocks `≤ 0.95 · 2^recRowsLog`. -/
theorem caps_P20 : 100 * streamLanes P20 ≤ 95 * streamCap P20 ∧ 100 * qS P20 ≤ 95 * 16384 ∧
    100 * (tally P20).maxQ ≤ 95 * 2 ^ 20 ∧ 100 * spongeBlocks P20 ≤ 95 * 2 ^ P20.recRowsLog :=
  checks_P20.2.2.2.2.2

end Lvm
