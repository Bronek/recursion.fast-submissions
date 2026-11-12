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

`lvOk C T Ls i f V` is the static side: message logs, row strides, at level 0 a fold `ℓ ≥ 1` and a
leaf of at most `2^ℓ` words, position chunks covering `t`, coordinate chunks covering `κ`, lanes
below `T`, final `κ ≥ 1`. (At `ℓ = 0` the reversed table is the existing one-cell table, so the
window would not start after the level's zero cells; no shipped level folds 0 variables.)

A level-0 leaf of `w < 2^ℓ` words (the stack's occupied lanes, `Level.row = 8w`) is folded against a
window of the reversed `eq` table followed by `2^ℓ − w` zero cells (`lvPre`), so that the loop keeps
its `2^ℓ` iterations and word `k` meets `eq[w − 1 − k]`, `F`'s `foldRow0` of `w` words.
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
  /-- The PoW bits per level (PI-GRIND; `0`: no grinding). -/
  g : Nat
  /-- The OOD items after each next cap (JB-L §3; J1: `C_main`). -/
  ood : Bool
  /-- Level `i`'s PoW field: the `K` cell `pw i` holds lane 2 of its PoW challenge's answer below `2^(64−g)`
  (a `BITS` field, `powSpec`). -/
  pw : Nat → Nat

/-- `Σ 2^a`. -/
def pw (as : List Nat) : Nat := (as.map (2 ^ ·)).sum

/-- The PoW check of level `i` (PI-GRIND): lane 2 of the PoW challenge's answer (lane `V2 − 2`) equals
the `BITS` field `pw i` (gated); nothing without grinding. -/
def powG (C : SCfg) (V2 i : Nat) (g : Cell) : BM Unit :=
  if C.g = 0 then pure () else assertEq (kc (V2 - 2)) (kc (C.pw i)) g

/-- **One level up to its column weight**: the fold rounds, `λ` and its powers, the fold `eq` table,
the row folds and the enforced sum, the intro polynomial; with the OOD items (`C.ood`, a next level),
the OOD point (`κ` loads), its answer and intro polynomial, `λ²`, and the glue `q + λ·intro_ood + λ²·intro`
(else `q + λ·intro`); the roots/inverses and the column weight; the OOD weight `eq(z, ·)` at the point's
suffix; with grinding (`C.g ≠ 0`), the PoW check: lane 2 of the PoW answer equals the `BITS` field `pw i`
(gated). The running quadratic after the glue and the glued `(scalar, weight)` cells. -/
def lvPre (C : SCfg) (pc : Nat) (zc oc g : Cell) (zk : Nat) (L : Level) (nxt : Option Level)
    (i f V : Nat) (q : Cell × Cell × Cell) : BM ((Cell × Cell × Cell) × List (Cell × Cell)) := do
  let ll := lvLanes C.g C.ood L nxt V
  let q ← roundsG pc f V L.fold q
  let lam ← ldEW (ll.V3 + 5)
  let lp ← pows (Nat.clog 2 (pw (C.pch i))) lam oc zc
  let er0 ← eqTab (fun j => ec (pc + f + j)) zc oc (decide (L.level = 0)) L.fold
  -- A level-0 leaf of `w < 2^ℓ` words (the stack's occupied lanes) is folded by the window `er0 + z`
  -- of the reversed table and the `z = 2^ℓ − w` zero cells after it: word `k < w` meets
  -- `eq[w − 1 − k]`, and the `z` lanes the loop reads past the leaf meet zero cells.
  let er ← if L.level = 0 ∧ L.row / 8 < 2 ^ L.fold then do
      let _ ← seqAll ((List.range (2 ^ L.fold - L.row / 8)).map fun _ => lin .E 0 0 zc zc)
      pure (er0 + (2 ^ L.fold - L.row / 8))
    else pure er0
  let enf ← foldsG (decide (L.level = 0)) L.fold (ll.V4 + 1) (oStr L) er lp L.t zc 0 (C.pch i)
  let it ← rdQ ll.V5 enf
  let cp ← getPtr
  iwConsts L.kappa g
  let W ← colWG (C.cch i) (pc + (f + L.fold)) (cp.k + L.kappa) cp.k lp (C.pb i) L.t zc zk 0 (C.pch i)
  powG C ll.V2 i g
  if C.ood && nxt.isSome then do
    let zb ← preloadG ((List.range L.kappa).map fun j => ll.Vc + 9 * j + 5)
    let y ← ldEW (ll.Vc + 9 * L.kappa + 5)
    let io ← rdQ (ll.Vc + 9 * L.kappa + 3) y
    let lam2 ← mulAdd .E lam lam zc
    let q ← glueG lam q io
    let q ← glueG lam2 q it
    let Wo ← eqZG zc ((List.range L.kappa).map fun j => (ec (zb + j), ec (pc + (f + L.fold) + j))) oc
    pure (q, [(lam, Wo), (lam2, W)])
  else do
    let q ← glueG lam q it
    pure (q, [(lam, W)])

/-- **The levels from level `i`** (see the module doc). -/
def levelsG (C : SCfg) (pc : Nat) (zc oc g : Cell) (zk : Nat) (bas : Cell) :
    List Level → Nat → Nat → Nat → Cell × Cell × Cell → List (Cell × Cell) → BM Unit
  | [], _, _, _, _, _ => pure ()
  | L :: rest, i, f, V, q, gl => do
    let r ← lvPre C pc zc oc g zk L rest.head? i f V q
    match rest with
    | [] => do
      let ll := lvLanes C.g C.ood L none V
      let tgt ← tailG pc (f + L.fold) ll.V6 L.kappa r.1
      let mle ← mleFold L.kappa (ll.V1 + 5) (fun j => ec (pc + (f + L.fold) + j))
      let w ← wsumG bas (gl ++ r.2)
      terminalCheck w mle tgt g
    | N :: rest' =>
      levelsG C pc zc oc g zk bas (N :: rest') (i + 1) (f + L.fold) (lvLanes C.g C.ood L (some N) V).V6 r.1
        (gl ++ r.2)

/-- **The static checks of the levels from level `i`.** -/
def lvOk (C : SCfg) (T : Nat) : List Level → Nat → Nat → Nat → Bool
  | [], _, _, _ => false
  | L :: rest, i, f, V =>
    let ll := lvLanes C.g C.ood L rest.head? V
    decide (f + L.fold + L.kappa = C.nu) && decide (L.row % 8 = 0) &&
    decide (L.level ≠ 0 ∨ (0 < L.fold ∧ L.row / 8 ≤ 2 ^ L.fold)) && decide (1 ≤ L.t) &&
    decide (L.t ≤ pw (C.pch i)) &&
    (List.range (C.pch i).length).all (fun k => decide (pw ((C.pch i).take k) < L.t)) &&
    decide (csum (C.cch i) = L.kappa) &&
    decide (ll.V4 + 1 + oStr L * (L.t - 1) + 3 * 2 ^ L.fold + 2 < T) &&
    decide (ll.V6 + 15 * (L.kappa - 1) + 8 < T) && decide (1 ≤ L.kappa) && decide (C.g ≤ 64) &&
    match rest with
    | [] => true
    | N :: rest' => lvOk C T (N :: rest') (i + 1) (f + L.fold) ll.V6

/-- The values of the challenge cells: `F`'s point (`s.folds ++ tailFolds` at the end). -/
def ptv (M : Mem) (pc ν : Nat) : List FE := (List.range ν).map fun k => M.e (pc + k)

end Lvm.Har
