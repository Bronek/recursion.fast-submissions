import LvmDecideTape
import LvmSchedule

/-!
# The decision `F vk c Σ` (BLUEPRINT §4.6, §5 step 3)

`F` reads the stream `Σ` (LvmDriver's `streamOf`) phase by phase, in the schedule's order
(`LvmSchedule.phases`), and decides:

1. **commit**: the caps of `C_main` and `C_rec` (skipped: the driver checks the openings
   against them);
2. **bus**: `α ∈ E^4`, `β`, the grand-product GKR (`verifyGkrGrandProducts`, leanVM), the count
   root nonzero, the leaf-decomposition scalars (`Params.leafdecReads`; WP-9: one scalar, which
   must be zero), the leaf decomposition (`M3.busFinal`);
3. **tables**: `ξ`, the table sumcheck (leanVM `tablePhase`/`tableSumcheck` on `M3.tables`), then
   (A23, BLUEPRINT §12.4, "phase 3b") `PUB`'s check (`M3.pubCheck`) and the accumulator fold: `κ`,
   the line polynomial `h` (`accVars + 1` coefficients), `t`, one zero scalar; `h(0) = acc_in.y`,
   `h(1) = y_own = Σ_k eq(κ, k)·v_fix[k]`; the folded claim `accOut = (line(t), h(t))` is the
   program's value;
4. **tape** (lvm2 stage S2, BLUEPRINT2 §2.2; `LvmDecideTape.dTape`): the instance point
   `r ∈ E^logN`, the 25 output scalars, the depth-24 Keccak GKR on one segment; it leaves the input
   claim `C_in`;
5. **wire** (`dWire`): the wiring sumcheck, `g_D`, `D`'s slot reduction and ring switch; claims
   (`tapeClaims`): `D̃_l(r) = a_l` (`l < 4`), the ring-switched slices, and the **boundary claims**
   `D̃(bits(n − 1)) = h` (A1). v1's `CH` link is gone (the wiring is the link);
6. **KS**: the same GKR on `2^ksLog` instances; claims: `M3.ksOutputClaims`, the word, the ring;
7. **KS link** ([model], `M3.ksLink`): `ρ, λ`, the shift sumcheck, 4 scalars;
8. **openings**: `C_rec`'s claims batched into its one-level WHIR, then `C_main`'s into its
   three-level WHIR (leanVM `verifyStackedOpening`; WHIR's glue and terminal check of the final, no
   direct check of the opened positions: A20 drops A10's for `C_rec`). `C_main`'s opening takes the
   out-of-domain samples when `p.mainOod` (lvm2 JB-VQP, J1: the Johnson radius); `C_rec`'s none.

`F` accepts iff every check held and the reading ended exactly at the end of `Σ` (so its reading
and the driver's writing follow one schedule) (`decideCore`), and the folded claim holds
(`AccOk (accOutOf Σ)`: the only native evaluation of the fixed columns, one sweep of their closed
forms, `PhiC`). `F` reads no length lane and no FS state: those are the driver's (`Q_link` in the
circuit).
-/

set_option autoImplicit false

namespace Lvm

open DM

/-- The 25 lanes of the first sponge block of `0x43 ‖ d` (`chainStep`'s permutation input,
BLUEPRINT §4.1), from `d`'s four lanes: byte 0 `0x43`, bytes 1–32 `d`, byte 33 `0x01`, byte 135
`0x80`, capacity lanes zero. -/
def pad43 (d : List FK) : List FK :=
  let w (i : Nat) : UInt64 := (d.getD i 0).val
  [⟨(0x43 : UInt64) ||| (w 0 <<< 8)⟩, ⟨(w 0 >>> 56) ||| (w 1 <<< 8)⟩, ⟨(w 1 >>> 56) ||| (w 2 <<< 8)⟩,
    ⟨(w 2 >>> 56) ||| (w 3 <<< 8)⟩, ⟨(w 3 >>> 56) ||| ((0x01 : UInt64) <<< 8)⟩] ++
  List.replicate 11 (0 : FK) ++ [⟨(0x80 : UInt64) <<< 56⟩] ++ List.replicate 8 (0 : FK)

/-- A digest's four lanes. -/
def digestLanes (d : Vector UInt8 32) : List FK :=
  (List.range 4).map fun i => ⟨(List.range 8).foldl (fun w j =>
    w ||| ((d.toArray.getD (8 * i + j) 0).toUInt64 <<< (8 * j).toUInt64)) 0⟩

/-- The public values: the arguments, and the header in `Σ` (the seed query). -/
def pubOf (vk c : Vector UInt8 32) (sig : ByteArray) : Pub where
  vk := digestLanes vk
  c := digestLanes c
  b := (laneAt sig (headerAt 8)).toNat
  cL := (List.range 4).map fun i => kAt sig (headerAt 48 + 8 * i)
  s := (List.range 4).map fun i => kAt sig (headerAt 80 + 8 * i)
  n := (laneAt sig (headerAt 112)).toNat
  h := (List.range 4).map fun i => kAt sig (headerAt 120 + 8 * i)
  sigLeaf := (List.range (sigBytes / 8)).map fun i => kAt sig (headerAt 152 + 8 * i)
  accIn := ⟨(List.range accVars).map fun i => feAt sig (headerAt (offAcc + eBytes * i)),
    feAt sig (headerAt (offAcc + eBytes * accVars))⟩

/-! ## The accumulator (A23, BLUEPRINT §12.2, §12.4) -/

/-- **`Φ̃` natively**: at `pt = (p, κ)` (`p` the first `tableRounds` coordinates),
`Σ_k eq(κ, k)·F̃_k(p.take τ_k)` over `fixCols` (`M3.fixVals`: one sweep of the closed forms; then a
dot product with the `eq(κ, ·)` table, low bit first; columns past `nFix` weigh 0). -/
def PhiC (P : Params) (m : M3) (pub : Pub) (pt : List FE) : FE :=
  dot (eqKernel (pt.drop P.tableRounds)) (m.fixVals pub (pt.take P.tableRounds))

/-- **The accumulator's claim holds**: `Φ̃(a.pt) = a.y`. -/
def AccOk (P : Params) (m : M3) (pub : Pub) (a : Acc) : Bool := PhiC P m pub a.pt == a.y

/-- The line through `a` (at 0) and `b` (at 1), at `t`: `a_i + t·(a_i + b_i)` (characteristic 2). -/
def accLine (a b : List FE) (t : FE) : List FE := List.zipWith (fun x z => x + t * (x + z)) a b

@[simp] theorem length_accLine (a b : List FE) (t : FE) :
    (accLine a b t).length = min a.length b.length := by simp [accLine]

/-- The table point from the tables' evaluations: the longest of their points (each is a prefix
`point.take τ` of the sumcheck point `challenges.reverse`, the last round's challenge first; the
tallest table has `τ = tableRounds`, `fitsR`). -/
def tablePoint (evs : List (List FE × List FE)) : List FE :=
  evs.foldl (fun r e => if r.length < e.1.length then e.1 else r) []

/-- **Phase 3b** (A23): from the tables' evaluations, `PUB`'s check, `κ`, `h`, `t`, the zero scalar;
`h(0) = acc_in.y`, `h(1) = y_own`; the value is the folded claim `(line(t), h(t))` with
`line(0) = acc_in.pt`, `line(1) = r ++ κ`. -/
def accFold (P : Params) (m : M3) (pub : Pub) (evals : List (List FE × List FE)) : DM Acc := do
  require (m.pubCheck pub evals)
  let kappa ← samples P.accLog
  let h ← readEs (accVars + 1)
  let t ← sampleE
  let z ← readE
  let yOwn := dot (eqKernel kappa) (m.fixSent pub evals)
  require (h.headD 0 == pub.accIn.y)
  require (sumE h == yOwn)
  require (z == 0)
  pure ⟨accLine pub.accIn.pt (tablePoint evals ++ kappa) t, polyEval h t⟩

/-- A ring switch whose claim the caller places: its 6 challenges' Frobenius coefficients and
the target `Σ_i g^i Φ(s_i)` (leanVM `ringSwitch` without the weight closure). -/
def ringRaw (s : List FE) : DM (FE × List FE) := do
  let challenges ← samples ringStages
  pure (polyEval (s.map (phiMap · challenges)) gen, ringCoefficients challenges)

/-- The claims of one Keccak table: the word claim and the ring-switched slices on its block. -/
def keccakClaims (blk : Placement) (ko : KeccakOut) (ring : FE × (List FE → FE)) :
    List BlockClaim :=
  [BlockClaim.point blk ko.wordPoint ko.word, ⟨blk, ring.2, ring.1⟩]

/-- `CH`'s output lanes 0–3 on `Y` (slots `ySlot + l`) at the instance point, and the boundary claims
`in_0 = Pad43(s)` at row 0 and `Y(n − 1) = h` (BLUEPRINT §4.1; A1: `n ≥ 1`). -/
def chFixedClaims (p : Params) (blk : Placement) (ySlot : Nat) (r v : List FE) (pub : Pub) :
    List BlockClaim :=
  let slot (l : Nat) := selectorPoint l slotLog
  ((List.range 4).map fun l => BlockClaim.point blk (r ++ slot (ySlot + l)) (v.getD l 0)) ++
  ((pad43 pub.s).zipIdx.map fun (w, l) =>
    BlockClaim.point blk (selectorPoint 0 p.logN ++ slot l) (FE.ofK w)) ++
  (pub.h.zipIdx.map fun (w, l) =>
    BlockClaim.point blk (selectorPoint (pub.n - 1) p.logN ++ slot (ySlot + l)) (FE.ofK w))

/-- **The decision program**: every phase of the schedule, in order; its value is the folded
accumulator (phase 3b). -/
def decideProg (p : Params) (m : M3) (vk c : Vector UInt8 32) : DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  -- 1] commit
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)
  -- 2] bus
  let alphas ← samples busBits
  let beta ← sampleE
  let (countRoot, point, values) ← verifyGkrGrandProducts p.busDepth
  require (countRoot != 0)
  let leafdec ← readEs p.leafdecReads
  let bus := m.busFinal ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
  require bus.ok
  -- 3] tables
  let xi ← sampleE
  let tables := m.tables pub
  let nC := (tables.map (·.nConstraints)).sum
  let xiPowers := powers xi (nC + 3)
  let formPowers := xiPowers.drop nC
  let evals ← tableSumcheck p.tableRounds tables bus.forms (xiPowers.take nC) formPowers
    point (dot formPowers bus.totals)
  let accOut ← accFold p m pub evals
  -- 4] the tape (lvm2 S2, T1–T2)
  let tp ← dTape p.logN
  -- 5] the wire (T3–T4), after A1's range of `n`
  dRange p pub
  let wo ← dWire p pub tp.claim
  -- 6] KS
  let rk ← samples p.ksLog
  let vks ← readEs lanes
  let kko ← verifyKeccak p.ksLog rk vks
  let kring ← ringSwitch kko.slicePoint kko.slices
  let ksClaims := keccakClaims m.ksBlock kko kring
  -- 7] KS link
  let kchal ← samples (p.ksLog + laneBits)
  let kshift ← sumcheck (m.ksShiftTarget kchal) 3 (List.replicate p.ksLog none)
  let kvals ← readEs 4
  let (okK, kLinkClaims) := m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩
  require okK
  -- 8] the openings
  let claims : List (Com × BlockClaim) :=
    bus.claims ++ m.tableClaims pub evals ++ (tapeClaims p tp wo pub ++ ksClaims).map (.main, ·) ++
      m.ksOutputClaims rk vks ++ kLinkClaims
  let on (com : Com) := (claims.filter (·.1 == com)).map (·.2.onStack)
  verifyStackedOpening p.recLevels p.nuRec (on .crec) false p.grind false
  verifyStackedOpening p.mainLevels p.nuMain (on .main) false p.grind p.mainOod
  pure accOut

/-- **`decideCore`**: every check of the decision program held and it read `Σ` to the end
(every check of `F` but the folded claim's, A23). -/
def decideCore (p : Params) (m : M3) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (_, s) := (decideProg p m vk c).runOn sig
  s.ok && s.ent == sig.size && s.msg == 0

/-- **`accOutOf Σ`**: the folded accumulator, a function of the stream (phase 3b's value). -/
def accOutOf (p : Params) (m : M3) (vk c : Vector UInt8 32) (sig : ByteArray) : Acc :=
  ((decideProg p m vk c).runOn sig).1

/-- **`F vk c Σ`**: `decideCore` and the folded claim (`AccOk`), from one run of the program. -/
def decideF (p : Params) (m : M3) (vk c : Vector UInt8 32) (sig : ByteArray) : Bool :=
  let (a, s) := (decideProg p m vk c).runOn sig
  (s.ok && s.ent == sig.size && s.msg == 0) && AccOk p m (pubOf vk c sig) a

/-- **The split** (BLUEPRINT §12.4): `F = decideCore ∧ AccOk (accOutOf Σ)`. -/
theorem decideF_eq (p : Params) (m : M3) (vk c : Vector UInt8 32) (sig : ByteArray) :
    decideF p m vk c sig =
      (decideCore p m vk c sig && AccOk p m (pubOf vk c sig) (accOutOf p m vk c sig)) := by
  unfold decideF decideCore accOutOf
  generalize (decideProg p m vk c).runOn sig = r
  cases r; rfl

end Lvm
