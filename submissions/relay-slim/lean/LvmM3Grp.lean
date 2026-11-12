-- new for lvm (WP-9b): WP-9's grouping of the LoopIR pieces (BLUEPRINT §4 as WP-9 refined it), as a
-- computable function (no Mathlib) the native verifier, the prover's table dump and the kernel
-- checks (`LvmM3Check.grpOkB`) share.
import LvmM3LoopTab

/-!
# The groups of a LoopIR program

`autoGroups Q`: for each piece shape (in order of first appearance), its pieces sorted largest
first (stable), cut by the binary decomposition of the shape's total rows, highest bit first: each
group of `2^k` rows takes pieces from the front until they fill it. Piece heights are powers of
two sorted descending, so every prefix sum is a multiple of the next piece's height and the cuts
are exact: no padding row, every member aligned. Nothing about it is assumed: `grpOkB Q
(autoGroups Q) = true` is checked by `decide` on the concrete program.
-/

namespace Lvm.M3

open Lvm.Loop

/-- Members `(piece, log-height)` taken from the front while the offset is below `size`: the taken
ones at their offsets from `off`, and the rest. -/
def takeTo : List (Nat × Nat) → Nat → Nat → List (Nat × Nat) × List (Nat × Nat)
  | [], _, _ => ([], [])
  | (n, h) :: rest, off, size =>
    if off < size then
      let r := takeTo rest (off + 2 ^ h) size
      ((n, off) :: r.1, r.2)
    else ([], (n, h) :: rest)

/-- Groups of shape `σ` of log-heights `ks` (in order), filled from the members `ms`. -/
def cutGroups (σ : Loop.Shape) : List Nat → List (Nat × Nat) → List Grp
  | [], _ => []
  | k :: ks, ms =>
    let r := takeTo ms 0 (2 ^ k)
    ⟨σ, k, r.1⟩ :: cutGroups σ ks r.2

/-- The set bits of `T < 2^64`, highest first. -/
def bitsDesc (T : Nat) : List Nat := (List.range 64).reverse.filter fun k => T.testBit k

/-- Insert into a list sorted by decreasing `key` after the entries of equal key (stable). -/
def insDesc {α : Type} (key : α → Nat) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if key a > key b then a :: b :: l else b :: insDesc key a l

/-- Stable insertion sort by decreasing `key` (structural: the kernel reduces it; `mergeSort` is
well-founded recursion and does not reduce in the kernel). -/
def sortDesc {α : Type} (key : α → Nat) (l : List α) : List α := l.foldl (fun acc a => insDesc key a acc) []

/-- The distinct entries of a list, in order of first appearance (structural). -/
def dedup {α : Type} [BEq α] (l : List α) : List α := l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []

/-- **WP-9's grouping**: per shape, the pieces largest first, cut by the binary decomposition of
the shape's rows. -/
def autoGroups (Q : Program) : List Grp :=
  let info := Q.pieces.zipIdx.map fun pn => (pn.1.shape, pn.2, Q.height pn.1)
  let shapes := dedup (info.map (·.1))
  shapes.flatMap fun σ =>
    let ms := (sortDesc (·.2) ((info.filter fun i => i.1 == σ).map (·.2))).map
      fun m => (m.1, m.2)
    cutGroups σ (bitsDesc (ms.map fun m => 2 ^ m.2).sum) ms

end Lvm.M3
