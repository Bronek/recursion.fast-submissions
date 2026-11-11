-- New for lvm (HAR-WH): the levels of one stacked WHIR opening as one gadget (`levelsG`, the
-- circuit's `whirLevels`) and its static checks (`lvOk`).
import LvmQAsmArith2WhirG

/-!
# The levels of a stacked opening

`levelsG C pc zc oc g zk bas Ls i f V q gl` is `F`'s `whirLevels` on the levels `Ls` (level `i` of the
opening, `f` fold challenges before it, first lane `V`, running quadratic `q`, glued claims `gl` as
`(λ, W)` cells): per level the fold rounds (`roundsG`), `λ`, its powers, the fold `eq` table
(reversed at level 0), the row folds and the enforced sum (`foldsG`), the intro polynomial and the
glue, the roots/inverses and the column weight (`colWG`); at the final level the tail rounds, the
residual's evaluation (`mleFold`), the weight `basis + Σ λ_i W_i` (`wsumG`) and the terminal check
under the gate `g`. All fold and tail challenges are the `E` cells `pc + k` (`chLanes`' order).

`lvOk C T Ls i f V` is the static side: message logs, row strides, position chunks covering `t`,
coordinate chunks covering `κ`, lanes below `T`, final `κ ≥ 1`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build

/-- The static configuration of one stacked opening. -/
structure SCfg where
  /-- The WHIR levels. -/
  levels : List Level
  /-- The stack's variables. -/
  nu : Nat
  /-- The first lane: the opening starts at position `8 U`. -/
  U : Nat
  /-- Level `i`'s positions are the `K` cells `pb i + j`. -/
  pb : Nat → Nat
  /-- Level `i`'s position chunks (logs). -/
  pch : Nat → List Nat
  /-- Level `i`'s coordinate chunks for its column weight (logs, `Σ 2^c = κ`). -/
  cch : Nat → List Nat

/-- `Σ 2^a`. -/
def pw (as : List Nat) : Nat := (as.map (2 ^ ·)).sum

/-- **One level up to its column weight**: the fold rounds, `λ` and its powers, the fold `eq`
table, the row folds and the enforced sum, the intro polynomial and the glue, the roots/inverses
and the column weight; the running quadratic after the glue, `λ`, `W`. -/
def lvPre (C : SCfg) (pc : Nat) (zc oc g : Cell) (zk : Nat) (L : Level) (nxt : Option Level)
    (i f V : Nat) (q : Cell × Cell × Cell) : BM ((Cell × Cell × Cell) × Cell × Cell) := do
  let ll := lvLanes L nxt V
  let q ← roundsG pc f V L.fold q
  let lam ← ldEW (ll.V3 + 5)
  let lp ← pows (Nat.clog 2 (pw (C.pch i))) lam oc zc
  let er ← eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold
  let enf ← foldsG (decide (L.level = 0)) L.fold (ll.V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i)
  let it ← rdQ ll.V5 enf
  let q ← glueG lam q it
  let cp ← getPtr
  iwConsts L.kappa g
  let W ← colWG (C.cch i) (pc + (f + L.fold)) (cp.k + L.kappa) cp.k lp (C.pb i) L.t zc zk 0 (C.pch i)
  pure (q, lam, W)

/-- **The levels from level `i`** (see the module doc). -/
def levelsG (C : SCfg) (pc : Nat) (zc oc g : Cell) (zk : Nat) (bas : Cell) :
    List Level → Nat → Nat → Nat → Cell × Cell × Cell → List (Cell × Cell) → BM Unit
  | [], _, _, _, _, _ => pure ()
  | L :: rest, i, f, V, q, gl => do
    let r ← lvPre C pc zc oc g zk L rest.head? i f V q
    match rest with
    | [] => do
      let ll := lvLanes L none V
      let tgt ← tailG pc (f + L.fold) ll.V6 L.kappa r.1
      let mle ← mleFold L.kappa (ll.V1 + 5) (fun j => ec (pc + (f + L.fold) + j))
      let w ← wsumG bas (gl ++ [(r.2.1, r.2.2)])
      terminalCheck w mle tgt g
    | N :: rest' =>
      levelsG C pc zc oc g zk bas (N :: rest') (i + 1) (f + L.fold) (lvLanes L (some N) V).V6 r.1
        (gl ++ [(r.2.1, r.2.2)])

/-- **The static checks of the levels from level `i`.** -/
def lvOk (C : SCfg) (T : Nat) : List Level → Nat → Nat → Nat → Bool
  | [], _, _, _ => false
  | L :: rest, i, f, V =>
    let ll := lvLanes L rest.head? V
    decide (f + L.fold + L.kappa = C.nu) && decide (L.row % 8 = 0) && decide (1 ≤ L.t) &&
    decide (L.t ≤ pw (C.pch i)) &&
    (List.range (C.pch i).length).all (fun k => decide (pw ((C.pch i).take k) < L.t)) &&
    decide (csum (C.cch i) = L.kappa) &&
    decide (ll.V4 + 1 + oStr L * (L.t - 1) + 3 * 2 ^ L.fold + 2 < T) &&
    decide (ll.V6 + 15 * (L.kappa - 1) + 8 < T) &&
    match rest with
    | [] => decide (1 ≤ L.kappa)
    | N :: rest' => lvOk C T (N :: rest') (i + 1) (f + L.fold) ll.V6

/-- The values of the challenge cells: `F`'s point (`s.folds ++ tailFolds` at the end). -/
def ptv (M : Mem) (pc ν : Nat) : List FE := (List.range ν).map fun k => M.e (pc + k)

end Lvm.Har
