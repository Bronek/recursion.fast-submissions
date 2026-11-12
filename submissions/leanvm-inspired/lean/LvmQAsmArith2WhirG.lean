-- New for lvm (HAR-WH): Q_arith phases 8–9 (the stacked WHIR openings of `C_rec` and `C_main`): the
-- stream layout of one opening, `F`'s values as pure functions of the stream, and the level gadgets
-- (rounds, glue, row folds with the enforced sum, column weights, constants, the final weight sum),
-- wiring QA2's gadgets (`LvmQWhir*`).
import LvmQAsmHarBase
import LvmQWhirClaim
import LvmQWhirFinal
import LvmQWhirBatch
import LvmQRingWeight

/-!
# Phases 8–9: layout, `F`'s values, level gadgets

**Layout** (lanes; `F` reads position `8V` at byte `8V + 40`, so a scalar read at position `8V` is
lanes `V + 5, V + 6, V + 7`). One stacked opening at position `8U`: the batching challenge at lane
`U + 5`; `verifyWhir`'s first polynomial at position `8(U + 9)` (lanes `U + 14`, `U + 17`); the
levels from lane `U + 15`. A level from lane `V` (`lvLanes`): fold round `j` at `V + 15 j`
(challenge `+5`, polynomial `+14`, `+17`); the final residual (`2^κ` scalars) or the next cap; the
positions (`⌈t/8⌉` answers); `λ` at `V3 + 5`; the openings from `V4` (row `q` at lane
`V4 + 1 + oStr·q`); the intro polynomial at position `8 V5`; the final level's tail rounds from
`V6`. `chLanes`: every fold and tail challenge in `F`'s order; `stackEndL`: the end lane.

**`F`'s values** (`frQ`, `frC`, `tlT`, `qsAt`): the running quadratic after fold rounds, the fold
challenges, the final target of the tail rounds, the positions of a level: functions of the stream
and the position (the run lemmas are in `LvmQAsmArith2WhirF`).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-! ## Layout -/

/-- A level's opening stride in lanes: one leaf entry (`40 + row` bytes) and `path` node entries. -/
def oStr (L : Level) : Nat := (40 + L.row + 104 * L.path) / 8

/-- The lanes of a level. -/
structure LvLanes where
  /-- After the fold rounds. -/
  V1 : Nat
  /-- The positions' first answer (after the residual or the next cap, the OOD items, the grinding). -/
  V2 : Nat
  /-- After the positions. -/
  V3 : Nat
  /-- After `λ`: the rows start at `V4 + 1`. -/
  V4 : Nat
  /-- After the openings. -/
  V5 : Nat
  /-- After the intro polynomial. -/
  V6 : Nat
  /-- After the residual (final level) or the next level's cap. -/
  Vc : Nat
  /-- After the OOD items (JB-L §3: `κ` samples, the answer, the intro polynomial; `= Vc` without). -/
  Vo : Nat

/-- The lanes of level `L` from lane `V` (`nxt`: the next level, `none` for the final level; `g`: the
PoW bits, PI-GRIND: with `g > 0` the separator (9 lanes), the nonce (3), the PoW challenge (9) before
the positions; `ood`: the OOD items after a next cap, JB-L §3). -/
def lvLanes (g : Nat) (ood : Bool) (L : Level) (nxt : Option Level) (V : Nat) : LvLanes :=
  let V1 := V + 15 * L.fold
  let Vc := match nxt with
    | none => V1 + 3 * 2 ^ L.kappa
    | some N => V1 + 4 * 2 ^ N.cap
  let Vo := if ood && nxt.isSome then Vc + 9 * L.kappa + 9 else Vc
  let V2 := if g = 0 then Vo else Vo + 21
  let V3 := V2 + 9 * ((L.t + positionsPerAnswer - 1) / positionsPerAnswer)
  let V4 := V3 + 9
  let V5 := V4 + oStr L * L.t
  ⟨V1, V2, V3, V4, V5, V5 + 6, Vc, Vo⟩

/-- The lanes of the fold and tail challenges of the levels from lane `V`, in `F`'s order. -/
def chLanes (g : Nat) (ood : Bool) : List Level → Nat → List Nat
  | [], _ => []
  | L :: rest, V =>
    (List.range L.fold).map (fun j => V + 15 * j + 5) ++
    match rest with
    | [] => (List.range L.kappa).map (fun j => (lvLanes g ood L none V).V6 + 15 * j + 5)
    | N :: rest' => chLanes g ood (N :: rest') (lvLanes g ood L (some N) V).V6

/-- The lanes of the levels' positions queries (`8 V2`). -/
def posLanes (g : Nat) (ood : Bool) : List Level → Nat → List Nat
  | [], _ => []
  | L :: rest, V =>
    match rest with
    | [] => [(lvLanes g ood L none V).V2]
    | N :: rest' => (lvLanes g ood L (some N) V).V2 :: posLanes g ood (N :: rest') (lvLanes g ood L (some N) V).V6

/-- The lane after the levels from lane `V` (the final level ends with a challenge). -/
def stackEndL (g : Nat) (ood : Bool) : List Level → Nat → Nat
  | [], V => V
  | L :: rest, V =>
    match rest with
    | [] => (lvLanes g ood L none V).V6 + 15 * (L.kappa - 1) + 9
    | N :: rest' => stackEndL g ood (N :: rest') (lvLanes g ood L (some N) V).V6

/-! ## `F`'s values -/

/-- The running quadratic after `n` fold rounds from position `P` (bytes). -/
def frQ (sig : ByteArray) : Nat → Nat → List FE → List FE
  | _, 0, q => q
  | P, n + 1, q => frQ sig (P + 120) n
      [feAt sig (P + 112), polyEval q (feAt sig (P + 40)) + feAt sig (P + 136), feAt sig (P + 136)]

/-- The challenges of `n` rounds from position `P`. -/
def frC (sig : ByteArray) (P n : Nat) : List FE := (List.range n).map fun j => feAt sig (P + 120 * j + 40)

/-- The final target of `n ≥ 1` tail rounds from position `P`. -/
def tlT (sig : ByteArray) : Nat → Nat → List FE → FE
  | _, 0, _ => 0
  | P, 1, q => polyEval q (feAt sig (P + 40))
  | P, n + 2, q => tlT sig (P + 120) (n + 1)
      [feAt sig (P + 112), polyEval q (feAt sig (P + 40)) + feAt sig (P + 136), feAt sig (P + 136)]

/-- The positions `F` draws for level `L` at position `P`. -/
def qsAt (sig : ByteArray) (P : Nat) (L : Level) : List Nat := (positionsR L sig ⟨P, 0, true⟩).1

/-! ## Gadgets -/

/-- The scalar in lanes `v, v + 1, v + 2` (`F`'s `feAt sig (8 v)`). -/
def ldEW (v : Nat) : BM Cell := loadE (kc v) (kc (v + 1)) (kc (v + 2))

/-- `polyEval [q₀, q₁, q₂] c = q₀ + c (q₁ + c q₂)`. -/
def pev (q : Cell × Cell × Cell) (c : Cell) : BM Cell := do
  let t ← mulAdd .E c q.2.2 q.2.1
  mulAdd .E c t q.1

/-- The round polynomial `F` reads at position `8 v` with the running claim `cl`:
`(a₀, cl + a₂, a₂)` (`sumcheckRoundPoly 3 cl none`). -/
def rdQ (v : Nat) (cl : Cell) : BM (Cell × Cell × Cell) := do
  let a0 ← ldEW (v + 5)
  let a2 ← ldEW (v + 8)
  let q1 ← add cl a2
  pure (a0, q1, a2)

/-- `n` fold rounds from lane `V`: round `j`'s challenge is the `E` cell `pc + f + j`; the running
quadratic after them. -/
def roundsG (pc : Nat) : Nat → Nat → Nat → Cell × Cell × Cell → BM (Cell × Cell × Cell)
  | _, _, 0, q => pure q
  | f, V, n + 1, q => do
    let cl ← pev q (ec (pc + f))
    let q' ← rdQ (V + 9) cl
    roundsG pc (f + 1) (V + 15) n q'

/-- `n ≥ 1` tail rounds from lane `V` (challenges `pc + f + j`); the final target. -/
def tailG (pc : Nat) : Nat → Nat → Nat → Cell × Cell × Cell → BM Cell
  | _, _, 0, _ => pure (ec 0)
  | f, _, 1, q => pev q (ec (pc + f))
  | f, V, n + 2, q => do
    let cl ← pev q (ec (pc + f))
    let q' ← rdQ (V + 9) cl
    tailG pc (f + 1) (V + 15) (n + 1) q'

/-- The glue of one level: `q + λ·i`. -/
def glueG (lam : Cell) (q i : Cell × Cell × Cell) : BM (Cell × Cell × Cell) := do
  let a ← mulAdd .E lam i.1 q.1
  let b ← mulAdd .E lam i.2.1 q.2.1
  let d ← mulAdd .E lam i.2.2 q.2.2
  pure (a, b, d)

/-- The row folds of a level's positions `[q₀, t)` in chunks of `2^a` positions (`as`): word or
scalar `k` of row `q` at lane `lb + k + S q` / `lb + 3k + S q`, the `eq` table at `er` (reversed at
level 0), each chunk dotted with the query weights at `lp + q`; the enforced sum. -/
def foldsG (lvl0 : Bool) (l lb S er lp t : Nat) (z : Cell) : Nat → List Nat → BM Cell
  | _, [] => pure z
  | q₀, a :: as => do
    let fc ← if lvl0 then rowFold0 l a (lb + S * q₀) S er else rowFoldE l a (lb + S * q₀) S er
    let d ← dotG a (min (2 ^ a) (t - q₀)) (lp + q₀) 1 (fc 0).n 1
    let rest ← foldsG lvl0 l lb S er lp t z (q₀ + 2 ^ a) as
    add d rest

/-- The column weight of a level over its positions `[q₀, t)` in chunks `as` (QA2's `colWeight`;
weights at `lp + q`, positions at the `K` cells `xb + q`, point at `ptb + k`, roots/inverses at the
`K` cells `rb + k`, `ib + k`, coordinate chunks `cs`, zero cells `z`, `zk`). -/
def colWG (cs : List Nat) (ptb ib rb lp xb t : Nat) (z : Cell) (zk : Nat) : Nat → List Nat → BM Cell
  | _, [] => pure z
  | q₀, a :: as => do
    let w ← colWeight a (min (2 ^ a) (t - q₀)) cs ptb ib rb (lp + q₀) (xb + q₀) z.n zk
    let rest ← colWG cs ptb ib rb lp xb t z zk (q₀ + 2 ^ a) as
    add w rest

/-- Contiguous `K` cells holding the constants `vs` (`const` rows from the `K` cell `g`). -/
def kconsts (g : Cell) : List FK → BM Unit
  | [] => pure ()
  | v :: vs => do
    let _ ← const .K v g
    kconsts g vs

/-- The roots of `subspaceRoots m`, then their inverses, as `K` constants (`2m` cells from the
pointer: roots at `+k`, inverses at `+m+k`). -/
def iwConsts (m : Nat) (g : Cell) : BM Unit := do
  kconsts g ((List.range m).map fun k => ((iwRoots m).getD k 0).c₀)
  kconsts g ((List.range m).map fun k => ((iwInvs m).getD k 0).c₀)

/-- The final weight `w + Σ_i λ_i W_i` (left to right, `F`'s `glued.foldl`). -/
def wsumG : Cell → List (Cell × Cell) → BM Cell
  | w, [] => pure w
  | w, (lam, W) :: gl => do
    let w' ← mulAdd .E lam W w
    wsumG w' gl

/-- `acc · Π_j (1 + a_j + b_j)` (the OOD weight `eq(z, x)`, `eqEval`, char 2) over the pairs `ab`
(`zc` a zero cell). -/
def eqZG (zc : Cell) : List (Cell × Cell) → Cell → BM Cell
  | [], acc => pure acc
  | (a, b) :: ab, acc => do
    let s ← lin .E 1 1 a b
    let acc' ← mulAdd .E acc s zc
    eqZG zc ab acc'

/-- Copies of `cells` at consecutive `E` cells from the returned one. -/
def copiesG (cells : List Cell) : BM Nat := do
  let p ← getPtr
  let _ ← seqAll (cells.map copy)
  pure p.e

/-- The scalars at the lanes `ls` (`ldEW`) at consecutive `E` cells from the returned one. -/
def preloadG (ls : List Nat) : BM Nat := do
  let p ← getPtr
  let _ ← seqAll (ls.map ldEW)
  pure p.e

end Lvm.Har
