-- new for lvm (WP-9b): the Boolean layout checks on WP-10's toy program (non-vacuity and kernel cost).
import LvmM3Check
import LvmM3CheckIn
import LvmM3Grp
import LvmLoopToy

/-!
# The layout checks on the toy program

WP-10's toy (`LvmLoopToy.toy`: 7 blocks, 25 `K` inputs): `autoGroups` groups its pieces, the input
arrays `[0, 16)`, `[16, 24)`, `[24, 25)` tile its inputs, and every check is decided by the kernel.
-/

namespace Lvm.M3

open Lvm.Loop

/-- The toy's input arrays: 16 + 8 + 1 `K` cells (value and finalize columns of `C_main`). -/
def toyArrs : List InArr :=
  [⟨.K, 4, 0, 1, [(false, 0)], (false, 16), none⟩, ⟨.K, 3, 16, 1, [(false, 32)], (false, 40), none⟩,
    ⟨.K, 0, 24, 1, [(false, 48)], (false, 49), none⟩]

theorem toy_grpOk : grpOkB toy (autoGroups toy) = true := by decide +kernel

theorem toy_inOk : inOkB toy toyArrs = true := by decide +kernel

theorem toy_hyps : GrpOk toy (autoGroups toy) ∧ InOk toy toyArrs :=
  ⟨grpOk_of_B toy_grpOk, inOk_of_B toy_inOk⟩

/-- A check fails where it should: one input cell missing. -/
theorem toy_inOk_short : inOkB toy toyArrs.dropLast = false := by decide +kernel

/-- A strided layout (WP-15b's `X_l`/digest shape): a contiguous array `[0, 8)`, then a bundle of
three stride-3 arrays of 4 rows over `[8, 20)`, then `[20, 24)`, `[24, 25)`. -/
def toyArrsS : List InArr :=
  [⟨.K, 3, 0, 1, [(false, 0)], (false, 8), none⟩,
    ⟨.K, 2, 8, 3, [(false, 16)], (false, 20), none⟩, ⟨.K, 2, 9, 3, [(false, 24)], (false, 28), none⟩,
    ⟨.K, 2, 10, 3, [(false, 32)], (false, 36), none⟩,
    ⟨.K, 2, 20, 1, [(false, 40)], (false, 44), none⟩, ⟨.K, 0, 24, 1, [(false, 48)], (false, 49), none⟩]

theorem toy_inOkS : InOk toy toyArrsS := inOk_of_B (by decide +kernel)

/-- A misaligned bundle fails: the second stride-3 array one cell off. -/
theorem toy_inOkS_bad :
    inOkB toy (toyArrsS.set 2 ⟨.K, 2, 11, 3, [(false, 24)], (false, 28), none⟩) = false := by
  decide +kernel

theorem toy_layOk : layOkB ⟨26, 19⟩ (toyArrs.map InArr.tab) = true := by decide +kernel

end Lvm.M3

namespace Lvm.M3

open Lvm.Loop

/-- The toy's tables (groups at a dummy placement, input arrays): the tables' check holds. -/
theorem toy_tabsOk :
    tabsOkB (lvmTabs toy (fun _ _ ↦ (false, 0)) (autoGroups toy) toyArrs []) = true := by
  decide +kernel

end Lvm.M3
