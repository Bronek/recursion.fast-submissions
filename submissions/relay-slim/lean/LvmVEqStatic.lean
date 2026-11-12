-- New for lvm (WP-14a): the static facts of P20's schedule the simulation needs, decided once.
import LvmVEqStream
import LvmReplay

/-!
# P20's schedule meets the static check

`stA_P20`: every Fiat–Shamir query of `schedule P20` is within `queryCap`, nothing is pending at an
opening or at the end, the caps come in `idxS` order (each oracle once), and every opening's level
geometry is P20's commitment table, its positions of the commitment's height. One kernel
evaluation over the items (`LvmReplay.P20_eq` gives the levels as literals): `stI` is `stA` on
the items' atoms (`stA_atomsOf`), a read of `m` scalars one step instead of `m` atoms (WP-16b).
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm

/-- `stA` over the `ps` atoms of a positions item, then `k`. -/
def stPos (h : ℕ) : ℕ → ℕ → List ℕ → (ℕ → List ℕ → Bool) → Bool
  | 0, pend, hs, k => k pend hs
  | n + 1, pend, hs, k => decide (32 + pend ≤ queryCap) && stPos h n 0 (h :: hs) k

/-- **`stA` on the items** (`stA_atomsOf`). -/
def stI (p : Params) : List Item → ℕ → List Ref → List ℕ → Bool
  | [], pend, _, _ => pend == 0
  | .read m :: its, pend, cr, hs => stI p its (pend + eBytes * m) cr hs
  | .cap c r :: its, pend, cr, hs =>
    (idxS r == cr.length) && !(cr.contains r) && stI p its (pend + nodeBytes * 2 ^ c) (cr ++ [r]) hs
  | .sample :: its, pend, cr, hs => decide (32 + pend ≤ queryCap) && stI p its 0 cr hs
  | .positions r :: its, pend, cr, _ =>
    stPos (p.level r).height (p.level r).nPosQ pend [] fun pend hs => stI p its pend cr hs
  | .opening r :: its, pend, cr, hs =>
    (pend == 0) && cr.contains r && geomOk p r && hs.all (· == (shpS (idxS r)).1) && stI p its 0 cr hs

theorem stA_reads (p : Params) (as : List Atom) (cr : List Ref) (hs : List ℕ) :
    ∀ (m pend : ℕ), stA p (List.replicate m .rd ++ as) pend cr hs = stA p as (pend + eBytes * m) cr hs
  | 0, pend => rfl
  | m + 1, pend => by
    rw [List.replicate_succ, List.cons_append, stA, stA_reads p as cr hs m, Nat.mul_succ]
    congr 1
    omega

theorem stA_pos (p : Params) (as : List Atom) (cr : List Ref) (h : ℕ) :
    ∀ (n rem pend : ℕ) (hs : List ℕ), stA p (posAtoms h n rem ++ as) pend cr hs =
      stPos h n pend hs fun pend hs => stA p as pend cr hs
  | 0, _, _, _ => rfl
  | n + 1, rem, pend, hs => by
    rw [posAtoms, List.cons_append, stA, stA_pos p as cr h n, stPos]

theorem stA_atomsOf (p : Params) : ∀ (its : List Item) (pend : ℕ) (cr : List Ref) (hs : List ℕ),
    stA p (atomsOf p its) pend cr hs = stI p its pend cr hs
  | [], _, _, _ => rfl
  | it :: its, pend, cr, hs => by
    rw [atomsOf_cons]
    cases it with
    | read m => rw [itemAtoms, stA_reads, stI, stA_atomsOf p its]
    | cap c r => rw [itemAtoms, List.singleton_append, stA, stI, stA_atomsOf p its]
    | sample => rw [itemAtoms, List.singleton_append, stA, stI, stA_atomsOf p its]
    | positions r =>
      rw [itemAtoms, List.cons_append, stA, stA_pos, stI]
      congr 1
      funext pend hs
      exact stA_atomsOf p its pend cr hs
    | opening r => rw [itemAtoms, List.singleton_append, stA, stI, stA_atomsOf p its]

set_option maxRecDepth 200000 in
/-- **The static check at P20.** -/
theorem stA_P20 : stA P20 (atomsOf P20 (schedule P20)) 0 [] [] = true := by
  rw [stA_atomsOf, Lvm.Replay.P20_eq]; decide +kernel

end Lvm.VEq
