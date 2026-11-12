-- WP-13b: the decoder's phases on the machine (new composition, on the model of
-- rf-k/submissions/flock-recursive/lean/FRXDec4F0.lean@8bff272b: `Enc` of the next level by the forward
-- butterflies, the agreement scan, interpolation, the butterflies per row; FR's ladder of levels is one level
-- here).
import LvmXNtt5
import LvmXInterp4
import LvmXCopy
import LvmXDecBr

/-!
# The decoder's phases: `Enc₀(f₁)`, the inverse NTT of the 64 rows

**Workspace** `[dB, dB + 2^21)` (below `memX = 2^25`): basis table `tbB = dB` (225 words), `eq`
table `qB = dB + 256` (192), the flag `okB = dB + 512`, the weights `wbB = dB + 2^13` and the
`E` row `ebB = dB + 2^14` (2^13 each), the agreement list `agB = dB + 2^15` (2^15), `Enc₀(f₁)`'s
coordinates `encB = dB + 2^16` (3·2^15), the interpolated rows `oB = dB + 2^19` (2^19), the
message `mB = dB + 2^20` (2^19). The inputs (word `wB`, `α` at `aB`, `f₁` at `fB`) lie outside.

* `encC c`: `f₁`'s coordinate `c` (`fB + 3v + c`, `v < 2^13`) zero-padded to `2^15`, then the
  forward NTT (`fwdIR 15`): `encC_sem`, `Enc` over `K` of the coordinate at every position.
* `bflyAll`: the inverse NTT (`bflyIR 13`) on each of the 64 rows at `oB` (`bflyAll_sem`).
* `okIR`: the flag `[2^13 ≤ |A|]` in `rOk` and at `okB`.

Registers `251 … 255`.
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM

/-! ## Layout and registers -/

/-- The basis table. -/ def tbB (dB : ℕ) : ℕ := dB
/-- The `eq(α, ·)` table. -/ def qB (dB : ℕ) : ℕ := dB + 256
/-- The success flag. -/ def okB (dB : ℕ) : ℕ := dB + 512
/-- The interpolation weights. -/ def wbB (dB : ℕ) : ℕ := dB + 2 ^ 13
/-- The interpolation's `E` row. -/ def ebB (dB : ℕ) : ℕ := dB + 2 ^ 14
/-- The agreement list. -/ def agB (dB : ℕ) : ℕ := dB + 2 ^ 15
/-- `Enc₀(f₁)`'s coordinates. -/ def encB (dB : ℕ) : ℕ := dB + 2 ^ 16
/-- The interpolated rows (leaf-word order). -/ def oB (dB : ℕ) : ℕ := dB + 2 ^ 19
/-- **The decoded message** (`2^19` words, natural order). -/ def mB (dB : ℕ) : ℕ := dB + 2 ^ 20

/-- The flag. -/ def rOk : ℕ := 251
/-- The row index. -/ def zT : ℕ := 252
/-- Scratch. -/ def zK : ℕ := 253
/-- The row loop's counter. -/ def zC : ℕ := 254
/-- Its count. -/ def zN : ℕ := 255

/-! ## The programs -/

/-- **`Enc₀(f₁)`'s coordinate `c`** at `encB + c·2^15`: copy, zero padding, forward NTT. -/
def encC (dB fB c : ℕ) : XIR :=
  .seq (mcpIR (2 ^ 13) (fB + c) 3 (encB dB + c * 2 ^ 15))
    (.seq (zeroIR (2 ^ 15 - 2 ^ 13) (encB dB + c * 2 ^ 15 + 2 ^ 13))
      (.seq (.blk [.const rA0 (toWord (encB dB + c * 2 ^ 15))]) (fwdIR 15 (tbB dB))))

/-- The three coordinates. -/
def encIR (dB fB : ℕ) : XIR := .seq (encC dB fB 0) (.seq (encC dB fB 1) (encC dB fB 2))

/-- One row `t`: `rA0 := oB + t·2^13`, the inverse NTT, `t += 1`. -/
def bflyRow (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 13)), .op .mul rA0 zT zK, .const zK (toWord (oB dB)),
      .op .add rA0 rA0 zK]) (.seq (bflyIR 13 (tbB dB)) (.blk [.op .add zT zT cOne]))

/-- **The inverse NTT of the 64 rows.** -/
def bflyAll (dB : ℕ) : XIR :=
  .seq (.blk [.const zT 0, .const zN 64]) (.loopK zC zN 64 (bflyRow dB))

/-- **The flag** `rOk := [2^13 ≤ cnt]`, stored at `okB`. -/
def okIR (dB : ℕ) : XIR :=
  .seq (.blk [.const zK (toWord (2 ^ 13)), .op .ltu rOk gCnt zK, .op .xor rOk rOk cOne,
    .const zK (toWord (okB dB))]) (.store zK rOk)

/-- **The decoding proper** (on success): interpolation on the first `2^13` listed positions,
the inverse NTT per row, the reorder into the message. -/
def decTail (dB wB : ℕ) : XIR :=
  .seq (baryIR (2 ^ 13) 64 (agB dB) (wbB dB) (ebB dB) wB 64 (oB dB))
    (.seq (bflyAll dB) (rowsIR (oB dB) (mB dB)))

/-! ## Costs -/

theorem cost_encC (dB fB c t : ℕ) : cost (encC dB fB c) t = 90522053 := by
  simp only [encC, cost, cost_mcpIR _ _ _ _ _ (show 2 ^ 13 < 2 ^ 64 by norm_num),
    cost_zeroIR _ _ _ (show 2 ^ 15 - 2 ^ 13 < 2 ^ 64 by norm_num), cost_fwdIR_15, blkSteps,
    List.length_cons, List.length_nil]
  norm_num

theorem cost_bflyAll (dB t : ℕ) : cost (bflyAll dB) t = 1250709900 := by
  simp only [bflyAll, bflyRow, cost, cost_bflyIR_13, blkSteps, List.length_cons, List.length_nil]
  norm_num

end Lvm.X
