import LvmDecideSumcheck

/-!
# The decision `F`: Keccak by GKR over its rounds, and ring switching

Ported from leanVM `formal/Statement/LeanVmVerifier.lean` (`:1596-1899`; `crates/verifier/src/
keccak.rs`, `ring_switch.rs`, protocol `doc/leanvm/body/c-keccak-gkr.tex`) on the reader `DM`:
the RMFE embedding (`carryless`, `carrylessDivmod`, `rmfeFactor`, `rmfe`), the claims and the
round's linear map (`keccakAlong`, `keccakLinearTranspose`, `keccakInstanceWeights`), a layer
(`keccakPackRounds`, `verifyKeccakLayer`), the openings (`keccakSlotWeights`, `keccakOpen`),
`keccakFirstClaim`, `verifyKeccak`, and ring switching (`phiMap`, `ringWeight`,
`ringCoefficients`, `ringSwitch`). `KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI` are leanVM
`Statement/Keccak.lean:27-41`.

Adaptations (BLUEPRINT §4.1–4.2, §11 A6). A layer's bit-position kernel is split as the Rust
splits it, `eq(local, j) = eq_z[z] · eq_lane[lane]` (`keccak.rs:166-189`; leanVM's Lean uses the
one kernel `eqKernel localPoint`, the same values), and the weight of `j` after `β` is `eq_z[z]`
times a factor of the lane (`along` keeps `z`): about 2,000 fewer `E` products per layer.
Powers `a^(2^k)` are `FE.frob k a` (`k` squarings). the GKR runs on a table of `2^logSteps` instances, a
parameter (`CH`: `logN`, `KS`: `ksLog`); the caller's instance point and its 25 output lanes are
read before it (prover-sent scalars, bound before any lane challenge). `verifyKeccak` returns the
committed-output word claim, the slice point and the 64 slices; the caller turns them into
claims on its table's 64-slot block (`LvmDecide`). Checks record and continue (`require`).
-/

set_option autoImplicit false

namespace Lvm

open DM

/-! ## Constants (`Statement/Keccak.lean:27-41`; `keccak.rs:14-17`) -/

/-- `KECCAK_RC` (`hash.rs:11-36`). -/
def keccakRC : List UInt64 := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- `KECCAK_RHO` (`hash.rs:37-39`): the rotation of lane `x + 5y`. -/
def keccakRho : List Nat :=
  [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

/-- `KECCAK_PI` (`hash.rs:40-49`): where lane `i = x + 5y` lands. -/
def keccakPi (i : Nat) : Nat := i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

/-- The bits of a Keccak state. -/
def keccakBits : Nat := 1600

/-- `EMBED_BITS` (`keccak.rs:16`). -/
def embedBits : Nat := 24

/-- The slot bits of a table's 64-slot block (leanVM `qkeccakSlotBits = ⌈log₂ 50⌉ = 6`). -/
def keccakSlotBits : Nat := slotLog

/-- The RMFE moduli and the bits each holds. -/
def rmfeFactors : List (Nat × Nat) :=
  [(0b10, 1), (0b11, 1), (0b1011, 2), (0b1101, 2), (0b100101, 3), (0b101001, 3), (0b101111, 3)]

/-! ## The embedding (`keccak.rs:22-46`; `LeanVmVerifier.lean:1611-1680`) -/

/-- The loop of `carryless`. -/
def carrylessAux : (fuel a b out : Nat) → Nat
  | 0, _, _, out => out
  | fuel + 1, a, b, out =>
    if b = 0 then out
    else carrylessAux fuel (a <<< 1) (b >>> 1) (if b % 2 = 1 then out ^^^ a else out)

/-- The product of two binary polynomials. -/
def carryless (a b : Nat) : Nat := carrylessAux b a b 0

/-- The loop of `carrylessDivmod`. -/
def carrylessDivmodAux : (fuel f quotient a : Nat) → Nat × Nat
  | 0, _, quotient, a => (quotient, a)
  | fuel + 1, f, quotient, a =>
    if a ≠ 0 ∧ bitLength f ≤ bitLength a then
      let shift := bitLength a - bitLength f
      carrylessDivmodAux fuel f (quotient ||| (1 <<< shift)) (a ^^^ (f <<< shift))
    else (quotient, a)

/-- Quotient and remainder of binary polynomials. -/
def carrylessDivmod (a f : Nat) : Nat × Nat := carrylessDivmodAux (bitLength a + 1) f 0 a

/-- The parity of the set bits. -/
def bitParity (n : Nat) : Nat := ((List.range (bitLength n)).countP fun i => n.testBit i) % 2

/-- The product of the moduli. -/
def rmfeModulus : Nat :=
  match rmfeFactors.map Prod.fst with
  | [] => 0
  | f :: fs => fs.foldl carryless f

/-- One factor's share of `rmfe`: its bits' embeddings and per bit the projection mask. -/
def rmfeFactor (modulus f bits : Nat) : List Nat × List Nat :=
  let cofactor := (carrylessDivmod modulus f).1
  let degree := bitLength f - 1
  let inverse := (((List.range (2 ^ degree)).drop 1).find? fun g =>
    (carrylessDivmod (carryless (carrylessDivmod cofactor f).2 g) f).2 = 1).getD 0
  let lift := (carrylessDivmod (carryless cofactor inverse) modulus).2
  let residues : List Nat := if bits = 1 then [1] else if bits = 2 then [0b11, 0b10]
    else [0b011, 0b010, 0b110]
  let embed := residues.map fun r => (carrylessDivmod (carryless lift r) modulus).2
  let masks := (List.range productBits).foldl (fun masks c =>
    let g := (carrylessDivmod (1 <<< c) f).2
    let atZero := g % 2
    let atOne := bitParity g
    let values : List Nat := if bits = 1 then [if f = 0b10 then atZero else atOne]
      else if bits = 2 then [atZero, atOne] else [atZero, atOne, g >>> 4]
    List.zipWith (fun mask value => mask ||| (value <<< c)) masks values)
    (List.replicate bits 0)
  (embed, masks)

/-- The embedding: sixteen bits in a binary polynomial of degree at most 23, a product of two
embeddings projecting to the AND (`keccak.rs:22-24`). -/
def rmfe : List Nat × List Nat :=
  let (embed, project) := rmfeFactors.foldl (fun (acc : List Nat × List Nat) (f, bits) =>
    let (e, p) := rmfeFactor rmfeModulus f bits
    (acc.1 ++ e, acc.2 ++ p)) ([], [])
  (embed ++ [rmfeModulus], project ++ [1 <<< (productBits - 1)])

/-- `RMFE_EMBED` (`keccak.rs:25-28`). -/
def rmfeEmbed : List Nat := rmfe.1

/-- `RMFE_PROJECT` (`keccak.rs:29-46`). -/
def rmfeProject : List Nat := rmfe.2

/-! ## Claims and the linear map (`keccak.rs:70-113`) -/

/-- `Claim` (`keccak.rs:70-75`): value, instance weights of a pack, point (pack, then segment),
bit-position weights. -/
structure KeccakClaim where
  /-- The claimed value. -/
  value : FE
  /-- The weight of each instance of a pack. -/
  mu : List FE
  /-- The point: a pack index, then a segment index. -/
  point : List FE
  /-- The weight of each bit position. -/
  weights : List FE
  deriving Inhabited

/-- `along(j, k)` (`keccak.rs:77-81`). -/
def keccakAlong (j k : Nat) : Nat :=
  let lane := j / 64
  let z := j % 64
  64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z

/-- `linear_transpose(w)`: the transpose of θ, ρ, π on weight vectors (`keccak.rs:83-101`). -/
def keccakLinearTranspose (w : List FE) : List FE :=
  let w := w.toArray
  let g : Array FE := (List.range 25).foldl (fun g lane => (List.range 64).foldl (fun g z =>
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0)
  let columns : Array FE := ((List.range 5).flatMap fun x => (List.range 64).map fun z =>
    sumE ((List.range 5).map fun y => g.getD (64 * (x + 5 * y) + z) 0)).toArray
  (List.range 25).flatMap fun lane => (List.range 64).map fun z =>
    g.getD (64 * lane + z) 0 + columns.getD (64 * ((lane % 5 + 1) % 5) + z) 0 +
      columns.getD (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0

/-- `instance_weights(s)` (`keccak.rs:103-113`). -/
def keccakInstanceWeights (s : FE) : List FE :=
  let sPowers := powers s embedBits
  rmfeEmbed.map fun e =>
    sumE ((List.range embedBits).filterMap fun b =>
      if e.testBit b then some (sPowers.getD b 0) else none)

/-! ## A layer (`keccak.rs:115-196`) -/

/-- Step 3 of a layer, the pack and the segment (`keccak.rs:152-161`). -/
def keccakPackRounds : List FE → FE → FE → DM (FE × FE × List FE)
  | [], value, scale => pure (value, scale, [])
  | r :: rs, value, scale => do
    let message ← sumcheckRoundPoly 3 value (some r)
    let challenge ← sampleE
    let (value, scale, point) ← keccakPackRounds rs
      ((1 + r + challenge) * polyEval message challenge) (scale * (1 + r + challenge))
    pure (value, scale, challenge :: point)

/-- `verify_layer(transcript, shape, step, claim)` (`keccak.rs:115-196`). -/
def verifyKeccakLayer (logSteps step : Nat) (claim : KeccakClaim) : DM KeccakClaim := do
  let packLog := logSteps - 4
  let product ← readEs productBits
  let projected := sumE ((List.range productBits).map fun c =>
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) =>
      if mask.testBit c then some m else none) * product.getD c 0)
  let segments := eqKernel (claim.point.drop packLog)
  let iota := sumE ((List.range gkrSegments).map fun segment =>
    let constant := keccakRC.getD (gkrDepth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((List.range 64).filterMap fun z =>
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))
  require (projected + iota * sumE claim.mu == claim.value)
  let s ← sampleE
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  let (value, scale, point) ← keccakPackRounds claim.point (polyEval product s) 1
  let (localPoint, value) ← sumcheck value 4 (List.replicate localBits none)
  let t ← readEs 3
  -- `eq(local, j) = eq_z[z] · eq_lane[lane]`, `j = 64 · lane + z` (`keccak.rs:166-189`)
  let eqZ := eqKernelA (localPoint.take 6)
  let eqL := eqKernelA (localPoint.drop 6)
  let w := claim.weights.toArray
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  let weighted := sumE ((List.range 25).map fun l => eqL.getD l 0 *
    sumE ((List.range 64).map fun z => eqZ.getD z 0 * w.getD (64 * l + z) 0))
  require (scale * weighted * (kappa * t0 + (kappa + t1) * t2) == value)
  let beta ← sampleE
  -- `along` keeps `z`: the weight of `j` is `eq_z[z]` times a per-lane factor
  let laneW := ((List.range 25).map fun l => eqL.getD l 0 + beta *
    (eqL.getD (keccakAlong (64 * l) 4 / 64) 0 + beta * eqL.getD (keccakAlong (64 * l) 3 / 64) 0)).toArray
  let weights := (List.range keccakBits).map fun j => eqZ.getD (j % 64) 0 * laneW.getD (j / 64) 0
  pure ⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose weights⟩

/-- The layers, `step` from `0` to `gkrDepth − 1` (`keccak.rs:264-267`). -/
def keccakLayers (logSteps : Nat) : List Nat → KeccakClaim → DM KeccakClaim
  | [], claim => pure claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayer logSteps step claim
    keccakLayers logSteps steps claim

/-! ## Openings (`keccak.rs:198-294`) -/

/-- The weights of `open` on each `(slot, z)` (`keccak.rs:208-221`). -/
def keccakSlotWeights (logSteps : Nat) (claim : KeccakClaim) (first count : Nat) :
    List (List FE) :=
  let segments := eqKernel (claim.point.drop (logSteps - 4))
  let weights := claim.weights.toArray
  let rows : Array (Array FE) := (List.range count).foldl (fun rows segment =>
    (List.range keccakBits).foldl (fun rows j =>
      rows.modify (25 * (first + segment) + j / 64) fun row =>
        row.setIfInBounds (j % 64) (segments.getD segment 0 * weights.getD j 0)) rows)
    (Array.replicate (2 ^ keccakSlotBits) (Array.replicate 64 0))
  rows.toList.map Array.toList

/-- `open(transcript, shape, claim, first, count, value)` (`keccak.rs:198-223`). -/
def keccakOpen (logSteps : Nat) (claim : KeccakClaim) (first count : Nat) (value : FE) :
    DM (List FE × List FE × FE) := do
  let (slot, value) ← sumcheck value 3 (List.replicate keccakSlotBits none)
  let rows := slot.foldl (fun rows challenge =>
    (List.range (rows.length / 2)).map fun i =>
      List.zipWith (fun lo hi => lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) (keccakSlotWeights logSteps claim first count)
  pure (slot, rows.headD [], value)

/-- The first claim of `verify_keccak` (`keccak.rs:247-263`). -/
def keccakFirstClaim (inst segment lanePoint output : List FE) (committed : FE) : KeccakClaim :=
  let lanes := eqKernel lanePoint
  let weights := (List.range keccakBits).map fun j => lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))
  let last := (eqKernel segment).getD (gkrSegments - 1) 0 * dot (lanes.take 25) output
  ⟨committed + last, eqKernel (inst.take 4), inst.drop 4 ++ segment, weights⟩

/-- What `verify_keccak` leaves: the committed outputs as a word claim (its point over the
block's `logSteps + 6` variables, its value), the slice point and the 64 slices. -/
structure KeccakOut where
  /-- The point of the committed-output word claim. -/
  wordPoint : List FE
  /-- Its value. -/
  word : FE
  /-- The point of the 64 slice claims. -/
  slicePoint : List FE
  /-- The slices. -/
  slices : List FE

/-- `verify_keccak(transcript, shape, instance, output)` (`keccak.rs:225-294`), on a table of
`2^logSteps` instances. -/
def verifyKeccak (logSteps : Nat) (inst output : List FE) : DM KeccakOut := do
  let packLog := logSteps - 4
  let rLow := inst.take 4
  let segment ← samples segmentBits
  let lanePoint ← samples laneBits
  let committed ← readE
  let first := keccakFirstClaim inst segment lanePoint output committed
  let claim ← keccakLayers logSteps (List.range gkrDepth) first
  let (slot, weights, value) ← keccakOpen logSteps first 1 (gkrSegments - 1) committed
  let word ← readE
  require (weights.headD 0 * word == value)
  let (low, value) ← sumcheck claim.value 3 (List.replicate 4 none)
  let (slot', weights', value) ← keccakOpen logSteps claim 0 gkrSegments value
  let slices ← readEs kBits
  require (multilinearEval claim.mu low * dot weights' slices == value)
  pure ⟨rLow ++ inst.drop 4 ++ slot, word, low ++ claim.point.take packLog ++ slot', slices⟩

/-! ## Ring switching (`ring_switch.rs`; `LeanVmVerifier.lean:1866-1899`) -/

/-- `RING_MAP_SHIFTS` (`ring_switch.rs:9`). -/
def ringMapShifts : List Nat := [32, 16, 8, 4, 2, 1]

/-- `ring_map(value, challenges)` (`ring_switch.rs:11-17`). -/
def phiMap (value : FE) (challenges : List FE) : FE :=
  (List.zip challenges ringMapShifts).foldl
    (fun value (challenge, shift) => value + challenge * FE.frob shift value) value

/-- `ring_weight(r, r_prime, coefficients)`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`
(`ring_switch.rs:19-34`). -/
def ringWeight (r rPrime coefficients : List FE) : FE :=
  (coefficients.foldl (fun (acc : FE × List FE) c =>
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (value, challenge) => product * (1 + value + challenge)) c
    (acc.1 + product, acc.2.map FE.sq)) (0, r)).1

/-- The Frobenius coefficients of the drawn map (`ring_switch.rs:42-50`). -/
def ringCoefficients (challenges : List FE) : List FE :=
  (List.range kBits).map fun k =>
    ((List.zip challenges ringMapShifts).filter fun (_, s) => k &&& s ≠ 0).foldl
      (fun acc (f, s) => acc * FE.frob (k % s) f) 1

/-- `ring_switch(point, s, transcript)` (`ring_switch.rs:36-54`): the target `Σ_i g^i Φ(s_i)`
and the weight `W(u) = Φ(eq(point, u))` over the opening point. -/
def ringSwitch (point s : List FE) : DM (FE × (List FE → FE)) := do
  let challenges ← samples ringStages
  let coefficients := ringCoefficients challenges
  let target := polyEval (s.map (phiMap · challenges)) gen
  pure (target, fun rPrime => ringWeight point rPrime coefficients)

end Lvm
