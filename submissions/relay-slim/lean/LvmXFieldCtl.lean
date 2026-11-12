-- New for lvm (WP-3): the controls of `LvmXField` (the pattern of `flock-recursive` `FRXFieldCtl`),
-- kept off `Solution`'s import closure.
import LvmXField

namespace Lvm.X

open RecursionFast

/-! ## Controls (kernel-checked)

Programs that read their operands from the tape into registers `64 …`, run one routine and output
the result, run by the contract's interpreter (`XProg.run`) with `260` memory words. The expected
values come from an independent schoolbook reference (`logs/ref/kat.py` in the WP-3 worktree:
`GF(2)[x]` products reduced by `x^64 + x^4 + x^3 + x + 1`, `E` products reduced by
`y^4 = y^2 + y`, `y^3 = y + 1`).

* Positive: `mulK`, `mulE`, `mulEK`, `sqE`, `invE` give the reference values (the `invE` value
  `A⁻¹` is checked in the reference by `A⁻¹ · A = 1`).
* **The measured step counts**: a program that is only `mulK` (`mulE`) halts with `260 + 8 + 13`
  (`260 + 8 + 97`) fuel and not with one step less (`8` is the prologue): the `steps_mulK`
  (`steps_mulE`) counts, run by the contract's interpreter.
* Negative: with the reduction constant cell overwritten (a program that is not `WF`), `mulE` does
  not give the product: the invariant is needed.
-/

namespace Controls

/-- Read `n` tape words into registers `base …`. -/
def readN (base : ℕ) : ℕ → XIR
  | 0 => .blk []
  | k + 1 => .seq (readN base k) (.seq (.blk [.const 120 (BitVec.ofNat 64 k)]) (.input (base + k)
      120))

/-- Output registers `base … base + n − 1`. -/
def outN (base : ℕ) : ℕ → XIR
  | 0 => .blk []
  | k + 1 => .seq (outN base k) (.out (base + k))

/-- Read `m` words into `64 …`, run `op`, output `n` words from `64 + m`. -/
def prog (m n : ℕ) (op : XIR) : XIR := .seq (readN 64 m) (.seq op (outN (64 + m) n))

/-- The reference operands `A` (3 words), `B` (3 words). -/
def tAB : List Word := [0xA506930D4C964C45, 0x90F951932C91BA42, 0xB7C1CADCD6C6C5C0,
  0x78A2D30DB964C965, 0xA9464DE6BA35C042, 0x51B3B7755F85F016]

/-- `A`, then the `K` scalar `k`. -/
def tAk : List Word := [0xA506930D4C964C45, 0x90F951932C91BA42, 0xB7C1CADCD6C6C5C0,
  0x8F4642982E159731]

/-- `A₀`, `B₀`. -/
def tK : List Word := [0xA506930D4C964C45, 0x78A2D30DB964C965]

theorem mulK_kat : (toProg 260 0 (prog 2 1 (mulK 66 64 65))).run tK 400 =
    some [0x6A576BC370420283] := by decide +kernel

theorem mulE_kat : (toProg 260 0 (prog 6 3 (mulE 70 64 67))).run tAB 500 =
    some [0x2CFF639A3D939239, 0xADCE52F7C1B184EA, 0xEBC2228030592823] := by decide +kernel

theorem mulEK_kat : (toProg 260 0 (prog 4 3 (mulEK 68 64 67))).run tAk 500 =
    some [0xE0906033597B03E5, 0xEA9A1383B30FCFC9, 0x87B075085A3903AC] := by decide +kernel

theorem sqE_kat : (toProg 260 0 (prog 3 3 (sqE 67 64))).run tAB.toArray.toList 500 =
    some [0xBDFB40CECB271720, 0xE7D4200826BA3C2A, 0x388360D3C8E3F703] := by decide +kernel

theorem invE_kat : (toProg 260 0 (prog 3 3 (invE 67 64))).run tAB 2000 =
    some [0x0B3E9AFE70C2F029, 0xBBB1438A13A23E95, 0xD0E7E43169A21907] := by decide +kernel

theorem mulK_alone : (toProg 260 0 (mulK 66 64 65)).run [] (260 + 8 + 13) = some [] ∧
    (toProg 260 0 (mulK 66 64 65)).run [] (260 + 8 + 12) = none := by decide +kernel

theorem mulE_alone : (toProg 260 0 (mulE 70 64 67)).run [] (260 + 8 + 97) = some [] ∧
    (toProg 260 0 (mulE 70 64 67)).run [] (260 + 8 + 96) = none := by decide +kernel

theorem mulE_bad_const : (toProg 260 0 (.seq (.blk [.const cRed 0x1D])
    (prog 6 3 (mulE 70 64 67)))).run tAB 500 ≠
      some [0x2CFF639A3D939239, 0xADCE52F7C1B184EA, 0xEBC2228030592823] := by decide +kernel

end Controls

end Lvm.X
