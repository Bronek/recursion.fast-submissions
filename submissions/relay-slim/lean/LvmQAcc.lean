-- New for lvm (AC-Q): the gadget Q_acc (BLUEPRINT §12.5, A23) and what its rows and assertions give.
import LvmQAccHdr

/-!
# Q_acc

Inputs (`AccIn`): the lane `L` of phase 3b's start position in the child's stream (`P = 8 L`: the
evaluations item is still pending there), the table gadget's cells (the table point `rc`, `PUB`'s
point `ppt` and value-column evaluation `pv`, the `fixCols` evaluations `fx`, all of the child),
the current proof's `PUB` cells from `pb` (lane 0 = the node flag `b`, the gate; lanes `1 … 4` = `vk`;
lanes `615 …` = `acc_in`). The child's `κ'`, `h'`, `t'`, zero scalar and header lanes are stream loads.

**`qacc A`**: (4) `pv = Σ_i eq(ppt, i)·L'_i` over the child's `PUB` lanes; (1) `y' = Σ_k eq(κ', k)·fx_k`;
(2) `h'₀ = acc_in'.y`, `Σ_j h'_j = y'`; `h'(t')` by Horner; the line point `acc_in'.pt_i + t'(acc_in'.pt_i
+ b_i)` with `b = rc ++ κ'`; (3) both equal to the current `acc_in` (`PUB`), the zero scalar is `0`.
Every assertion is gated by `b`. Nothing evaluates a fixed column.

**`qacc_facts`**: with the gate on and the stream bound, the six equations (`AccFacts`).
-/

set_option autoImplicit false

namespace Lvm.QAcc

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.QSig Lvm.Q1

/-- Q_acc's inputs. -/
structure AccIn where
  /-- The lane of phase 3b's start position (`P = 8 L`). -/
  L : Nat
  /-- The batching challenges `κ'` (`Params.accLog`). -/
  dk : Nat
  /-- The low coordinates of `κ'`'s split `eq` table (`la ≤ dk`). -/
  la : Nat
  /-- `PUB`'s log-height (its point's coordinates). -/
  τp : Nat
  /-- The current proof's `PUB` cell `0`. -/
  pb : Nat
  /-- The child's table point (`tablePoint`'s cells). -/
  rc : List Cell
  /-- The child's `PUB` table point. -/
  ppt : List Cell
  /-- The child's `PUB` value-column evaluation. -/
  pv : Cell
  /-- The child's `fixCols` evaluations, in `fixSent`'s order. -/
  fx : List Cell

namespace AccIn

variable (A : AccIn)

/-- `κ'_i`'s lane (answer of entry `i` from `P`). -/
def kap (i : Nat) : Nat := A.L + 5 + 9 * i
/-- The lane of `h'`'s position. -/
def h0 : Nat := A.L + 9 * A.dk
/-- `h'_j`'s lane. -/
def hL (j : Nat) : Nat := A.h0 + 5 + 3 * j
/-- `t'`'s lane. -/
def tL : Nat := A.h0 + 3 * (accVars + 1) + 5
/-- The lane of the zero scalar's position (phase 4's start is `8 z0 + 24`). -/
def z0 : Nat := A.h0 + 3 * (accVars + 1) + 9
/-- The zero scalar's lane. -/
def zL : Nat := A.z0 + 5
/-- The line's coordinate `b_i` (`rc`, then `κ'` from `kb`). -/
def bC (kb i : Nat) : Cell := (A.rc ++ (List.range A.dk).map fun j => ec (kb + j)).getD i (ec 0)
/-- `PUB`'s point as a function. -/
def pp (i : Nat) : Cell := A.ppt.getD i (ec 0)

end AccIn

/-- The child's `acc_in'` scalar `j` (stream lanes from `11 + 615`). -/
def accLane (j : Nat) : Nat := 626 + 3 * j

/-- **Q_acc** (BLUEPRINT §12.5). -/
def qacc (A : AccIn) : BM Unit := do
  let g := kc A.pb
  let zo ← consts A.pb
  let kb ← ldEsB ((List.range A.dk).map A.kap)
  let sP ← qpub A.pp zo.1 zo.2 A.τp 11 (A.pb + 1) pubLanes
  assertEqE A.pv sP g
  let y ← qyown kb A.la A.dk zo.1 zo.2 A.fx
  let hb ← ldEsB ((List.range (accVars + 1)).map A.hL)
  let ab ← ldEsB ((List.range (accVars + 1)).map accLane)
  assertEqE (ec hb) (ec (ab + accVars)) g
  let sh ← macChain ((List.range (accVars + 1)).map fun j => (zo.2, ec (hb + j))) zo.1
  assertEqE sh y g
  let t ← ldE A.tL
  let hv ← horner ((List.range (accVars + 1)).map fun j => ec (hb + j)) t zo.1
  let pts ← linePts ((List.range accVars).map fun i => (ec (ab + i), A.bC kb i)) t
  let pc ← ldEsB ((List.range (accVars + 1)).map fun j => A.pb + 615 + 3 * j)
  let _ ← assertEqs ((List.range accVars).map fun i => (pts.getD i default, ec (pc + i))) g
  assertEqE hv (ec (pc + accVars)) g
  let zz ← ldE A.zL
  assert0 zz g

/-- The current proof's `acc_in` from its `PUB` cells (three lanes per scalar). -/
def accC (M : Mem) (pb : Nat) : Acc :=
  ⟨(List.range accVars).map fun i => ⟨M.k (pb + 615 + 3 * i), M.k (pb + 615 + 3 * i + 1), M.k (pb + 615 + 3 * i + 2)⟩,
    ⟨M.k (pb + 615 + 3 * accVars), M.k (pb + 615 + 3 * accVars + 1), M.k (pb + 615 + 3 * accVars + 2)⟩⟩

/-- **What Q_acc's rows and assertions give** (gate on), on the stream view `v = feAt Σ`. -/
structure AccFacts (A : AccIn) (M : Mem) (sig : ByteArray) : Prop where
  /-- (4) The child's `PUB` evaluation is its lanes' extension at `PUB`'s point. -/
  pub : A.pv.val M = ∑ i ∈ Finset.range pubLanes,
    eqW ((List.range A.τp).map fun i => (A.pp i).val M) i * FE.ofK (pubLane M 11 (A.pb + 1) i)
  /-- (2) `h'₀ = acc_in'.y`. -/
  h0 : feAt sig (8 * A.hL 0) = feAt sig (8 * accLane accVars)
  /-- (2) `Σ_j h'_j = y' = Σ_k eq(κ', k)·fx_k`. -/
  sum : ((List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j)).sum =
    ∑ k ∈ Finset.range A.fx.length,
      eqW ((List.range A.dk).map fun i => feAt sig (8 * A.kap i)) k * (A.fx.getD k default).val M
  /-- (3) The line point is the current `acc_in.pt`. -/
  line : ∀ i < accVars, feAt sig (8 * accLane i) + feAt sig (8 * A.tL) *
      (feAt sig (8 * accLane i) + ((A.rc.map (Cell.val M) ++
        (List.range A.dk).map fun j => feAt sig (8 * A.kap j)).getD i 0)) = (accC M A.pb).pt.getD i 0
  /-- (3) `h'(t')` is the current `acc_in.y`. -/
  y : polyEval ((List.range (accVars + 1)).map fun j => feAt sig (8 * A.hL j)) (feAt sig (8 * A.tL)) =
    (accC M A.pb).y
  /-- The zero scalar. -/
  zero : feAt sig (8 * A.zL) = 0


end Lvm.QAcc
