import LvmDecideSumcheck

/-!
# The decision `F`: WHIR in the unique-decoding regime, and the stacked opening

Ported from leanVM `formal/Statement/LeanVmVerifier.lean` (`:1380-1571`; `crates/verifier/src/
whir.rs`, `lib.rs:122-139`, Annex B), on the reader `DM`: `subspaceRoots`, `inducedWeight`,
`GluedClaim`, `WhirState`, `foldRounds`, `tailRounds`, `glue`, the level loop `whirLevels`,
`verifyWhir`, `verifyStackedOpening`.

Deviations (BLUEPRINT §1, §3.1, §11 A10, A11; WP-0):
* **No OOD, no grinding.** A non-final level's next commitment is a cap (`2^c` nodes, skipped
  here: the driver checks every opening against it), with no out-of-domain sample, value or
  intro round; no proof-of-work nonce.
* **Positions** are 8 per FS answer (`positionsR`), not leanVM's `192 / depth` per sample.
* **Parameters** are the record's (`Level`), not leanVM's Johnson ladder and query table.
* **Rows** are read from `Σ` in place: a level-0 row is `2^ℓ` `K` words, word `t` the code of
  lane block `63 − t` (leanVM's `row.reverse.map ofK`), and its fold is
  `Σ_k eq(α, k) · word[2^ℓ − 1 − k]` (`foldRow0`); a later row is `2^ℓ` `E` scalars (`ext_row`),
  folded by `foldRowE`. leanVM's `enforcedSum` is `Σ_q w_q · fold_q`.
* **`C_rec`'s final in the clear** (A10; unused since A20, `direct = false` in `F`): with `direct`, the final level also checks every opened
  position `q` directly, `fold_q = Enc(f₁)(x_q)`, `Enc` the novel-basis (LCH) encoding of the
  residual `f₁` on `span(x^0 … x^(height−1))`, computed by one additive NTT (`lchEncode`),
  pruned to the blocks that hold a queried position (`lchEncodeAt`, about 57% of the
  butterflies at `P20`). This is the agreement the extractor's set `A` is built on (BLUEPRINT §6.2).
-/

set_option autoImplicit false

namespace Lvm

open DM

/-! ## Subspace polynomials (`whir.rs:92-126`) -/

/-- The layers of `subspace_roots` (`whir.rs:96-102`). -/
def subspaceRootsAux : Nat → FE → List FE → List FE
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value => FE.sq value + last * value with
    | [] => []
    | root :: rest => root :: subspaceRootsAux n root rest

/-- `subspace_roots(log_n)`: `1`, then `W_i(x^i)` for `i = 1 … log_n` (`whir.rs:92-104`). -/
def subspaceRoots (logN : Nat) : List FE :=
  1 :: subspaceRootsAux logN 1 ((List.range logN).map fun i => eOfNat (2 ^ (i + 1)))

/-- `induced_weight(message_log, queries, query_weights, point)`:
`Σ_q w_q Π_k (1 + p_k (1 + Ŵ_k(x_q)))` (`whir.rs:106-126`). -/
def inducedWeight (messageLog : Nat) (queries : List Nat) (queryWeights point : List FE) : FE :=
  let roots := subspaceRoots messageLog
  let inverses := roots.map fun value => if value == 0 then 0 else value⁻¹
  (List.zip queryWeights queries).foldl (fun total (weight, query) =>
    let product := point.zipIdx.foldl (fun (acc : FE × FE) (challenge, coordinate) =>
      (acc.1 * (1 + challenge * (1 + acc.2 * inverses.getD coordinate 0)),
        FE.sq acc.2 + roots.getD coordinate 0 * acc.2)) (weight, eOfNat query)
    total + product.1) 0

/-! ## The novel-basis encoding by one additive NTT (Lin–Chung–Han) -/

/-- `Ŵ_i(x^j)` for `i < n`, `j < m`, as `K` words: `W_0(X) = X`,
`W_{i+1} = W_i^2 + W_i(x^i) W_i`, `Ŵ_i = W_i / W_i(x^i)` (the normalisation of
`subspace_roots`/`induced_weight`). Row `i`, column `j`. -/
def normSubspaceTable (n m : Nat) : Array (Array FK) := Id.run do
  let mut layer : Array FK := (Array.range m).map fun j => (FK.x ^ j)
  let mut out : Array (Array FK) := #[]
  for i in [0:n] do
    let wi := layer.getD i 0
    let inv := wi⁻¹
    out := out.push (layer.map (· * inv))
    layer := layer.map fun v => FK.sq v + wi * v
  return out

/-- `Ŵ_i(β)` for `β = Σ_j bit_j(β) x^j`, by `F₂`-linearity from a row of `normSubspaceTable`. -/
def whatAt (row : Array FK) (beta : Nat) (m : Nat) : FK := Id.run do
  let mut acc : FK := 0
  for j in [0:m] do
    if (beta >>> j) % 2 = 1 then acc := acc + row.getD j 0
  return acc

/-- **The novel-basis encoding** of `2^k` coefficients `a` (`a_v` the coefficient of
`X_v = Π_i Ŵ_i^{v_i}`) at the `2^(k+c)` points `x_q = Σ_j bit_j(q) x^j`, `q < 2^(k+c)`: per coset
`β = q >> k << k`, the LCH butterflies `lo = a_j + Ŵ_i(β') a_{j+h}`, `hi = lo + a_{j+h}`
(`Ŵ_i` is constant `Ŵ_i(β')` on the coset `β' + span(x^0 … x^(i−1))` and grows by `1` across
`x^i`). Value `q` of the result is `Enc(a)(x_q)`. -/
def lchEncode (a : Array FE) (k c : Nat) : Array FE := Id.run do
  let m := k + c
  let tbl := normSubspaceTable k m
  let mut out : Array FE := Array.emptyWithCapacity (2 ^ m)
  for coset in [0:2 ^ c] do
    let mut A := a
    for lvl in [0:k] do
      let i := k - 1 - lvl
      let h := 2 ^ i
      let row := tbl.getD i #[]
      for blk in [0:2 ^ lvl] do
        let o := blk * (2 * h)
        let cst := whatAt row ((coset <<< k) ||| o) m
        for jj in [0:h] do
          let x := A.getD (o + jj) 0
          let y := A.getD (o + jj + h) 0
          let lo := x + FE.smulBase cst y
          A := (A.set! (o + jj) lo).set! (o + jj + h) (lo + y)
    out := out ++ A
  return out

/-- The distinct values of a list, ascending. -/
def dedupSorted (l : List Nat) : List Nat :=
  (l.mergeSort (· ≤ ·)).foldr (fun x acc => match acc with
    | y :: _ => if x = y then acc else x :: acc
    | [] => [x]) []

/-- **`lchEncode` at the positions `qs` only**: the same butterflies, restricted per coset and
level to the blocks that contain a queried position (a block's inputs are its parent block's
outputs, so the parent is always computed). The values `Enc(a)(x_q)`, in the order of `qs`. -/
def lchEncodeAt (a : Array FE) (k c : Nat) (qs : List Nat) : List FE := Id.run do
  let m := k + c
  let tbl := normSubspaceTable k m
  let mask := 2 ^ k - 1
  let mut vals : Array FE := Array.replicate (2 ^ m) 0
  for coset in [0:2 ^ c] do
    let loc := (qs.filter fun q => q >>> k == coset).map (· &&& mask)
    if loc.isEmpty then continue
    let mut A := a
    for lvl in [0:k] do
      let i := k - 1 - lvl
      let h := 2 ^ i
      let row := tbl.getD i #[]
      for blk in dedupSorted (loc.map (· >>> (i + 1))) do
        let o := blk * (2 * h)
        let cst := whatAt row ((coset <<< k) ||| o) m
        for jj in [0:h] do
          let x := A.getD (o + jj) 0
          let y := A.getD (o + jj + h) 0
          let lo := x + FE.smulBase cst y
          A := (A.set! (o + jj) lo).set! (o + jj + h) (lo + y)
    for q in loc do
      vals := vals.set! ((coset <<< k) ||| q) (A.getD q 0)
  return qs.map fun q => vals.getD q 0

/-! ## Row folds -/

/-- The fold of a level-0 row of `w` `K` words at byte `o` of `Σ`:
`Σ_k eq[k] · word[w − 1 − k]`. -/
def foldRow0 (sig : ByteArray) (eq : Array FE) (o w : Nat) : FE := Id.run do
  let mut acc : FE := 0
  for k in [0:w] do
    acc := acc + FE.smulBase (kAt sig (o + 8 * (w - 1 - k))) (eq.getD k 0)
  return acc

/-- The fold of a later row of `w` `E` scalars at byte `o`: `Σ_k eq[k] · row[k]` (`ext_row`). -/
def foldRowE (sig : ByteArray) (eq : Array FE) (o w : Nat) : FE := Id.run do
  let mut acc : FE := 0
  for k in [0:w] do
    acc := acc + feAt sig (o + 24 * k) * eq.getD k 0
  return acc

/-! ## The level loop (`whir.rs:158-264`) -/

/-- A claim glued into the running sumcheck and the weight it owes (`whir.rs:130-139`). -/
structure GluedClaim where
  /-- The power of `λ` it was glued with. -/
  scalar : FE
  /-- The fold challenges before its level. -/
  foldStart : Nat
  /-- Its weight at the terminal point, over the level's message coordinates. -/
  weightAt : List FE → FE

/-- The running state of `verify_whir`. -/
structure WhirState where
  /-- The running sumcheck's quadratic. -/
  runningQuad : List FE
  /-- Every fold challenge so far. -/
  folds : List FE
  /-- The glued claims so far. -/
  glued : List GluedClaim

/-- A level's fold rounds (`whir.rs:159-165`). -/
def foldRounds : Nat → WhirState → List FE → DM (WhirState × List FE)
  | 0, s, levelFolds => pure (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← sampleE
    let quad ← sumcheckRoundPoly 3 (polyEval s.runningQuad challenge) none
    foldRounds n { s with runningQuad := quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- The final level's tail rounds (`whir.rs:237-246`); none fails. -/
def tailRounds : Nat → List FE → DM (List FE × FE)
  | 0, _ => do require false; pure ([], 0)
  | n + 1, quad => do
    let challenge ← sampleE
    let target := polyEval quad challenge
    if n = 0 then pure ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRounds n quad
      pure (challenge :: rest, target)

/-- Glue a level's pending claims with powers of `λ` (`whir.rs:221-232`). -/
def glue (lam : FE) (state : WhirState) (pending : List (List FE × (List FE → FE))) : WhirState :=
  (pending.foldl (fun (acc : WhirState × FE) (intro, weightAt) =>
    let scalar := acc.2 * lam
    let state := acc.1
    ({ state with
        runningQuad := List.zipWith (fun q i => q + scalar * i) state.runningQuad intro,
        glued := state.glued ++ [⟨scalar, state.folds.length, weightAt⟩] }, scalar)) (state, 1)).1

/-- Every opened position agrees with the encoding of the residual (`direct`, A10). -/
def directFinal (residual : List FE) (L : Level) (queries : List Nat) (folds : List FE) : Bool :=
  (List.zip (lchEncodeAt residual.toArray L.kappa L.rate queries) folds).all fun (e, f) => e == f

/-- **One level of the UD WHIR and every level after it** (`whir.rs:158-262`). -/
def whirLevels (logN laneFolds : Nat) (evaluateBasis : List FE → FE) (direct : Bool) :
    List Level → WhirState → DM Unit
  | [], _ => require false
  | L :: rest, s => do
    let (s, levelFolds) ← foldRounds L.fold s []
    let messageLog := logN - s.folds.length
    let residual ← match rest with
      | [] => readEs (2 ^ messageLog)
      | N :: _ => do skip (nodeBytes * 2 ^ N.cap); pure []
    let queries ← positionsR L
    let lam ← sampleE
    let queryWeights := powers lam queries.length
    let rowOffs ← openingR L
    let sig ← read
    let eq := eqKernelA levelFolds
    let folds := rowOffs.map fun o =>
      if L.level = 0 then foldRow0 sig eq o (2 ^ L.fold) else foldRowE sig eq o (2 ^ L.fold)
    let enforced := dot queryWeights folds
    let intro ← sumcheckRoundPoly 3 enforced none
    let s := glue lam s [(intro, fun x => inducedWeight messageLog queries queryWeights x)]
    match rest with
    | [] => do
      if direct then require (directFinal residual L queries folds)
      let (tailFolds, target) ← tailRounds messageLog s.runningQuad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim =>
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      require (terminal == target)
    | _ :: _ => whirLevels logN laneFolds evaluateBasis direct rest s

/-- `verify_whir(…, log_n, …, target, root, evaluate_basis)` on the record's levels
(`whir.rs:141-265`). -/
def verifyWhir (levels : List Level) (logN : Nat) (target : FE) (evaluateBasis : List FE → FE)
    (direct : Bool) : DM Unit := do
  let quad ← sumcheckRoundPoly 3 target none
  whirLevels logN ((levels.head?.map (·.fold)).getD 0) evaluateBasis direct levels ⟨quad, [], []⟩

/-- **`verify_stacked_opening`**: the claims batched with powers of one challenge into one WHIR
opening (`lib.rs:122-139`). -/
def verifyStackedOpening (levels : List Level) (stackLog : Nat) (claims : List StackClaim)
    (direct : Bool) : DM Unit := do
  let scales := powers (← sampleE) claims.length
  verifyWhir levels stackLog (dot scales (claims.map (·.2)))
    (fun point => dot scales (claims.map fun c => c.1 point)) direct

end Lvm
