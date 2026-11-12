-- New for lvm (WP-16a): `V_S` at P20/P8 on the node program's tables (replaces INT-2's placeholders
-- `M3.tabsP20 = M3.tabsP8 = fun _ => []`, which lived in `LvmVerifierS`).
import LvmVerifierS
import LvmQAsmData20
import LvmQAsmData8
import LvmQAsmProg
import LvmVFastQ

/-!
# `V_S` with the node program's tables

`M3.tabsP20 = QAsm.tabs cfg20 (cacheG Q20) data20` (INT-2's form `fun pub => lvmTabsC C20 pl groups
(arrsOf pub) aux`, `C20 = cacheG Q20` a top-level constant built once), `VS20` the frozen `V_S` on them (`VSL`). The `P8` constants are in `LvmQAsmV8` (outside
the badge's import closure: every closed constant there is evaluated at each start of the verifier).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast Lvm.QAsm

/-- The `P20` node program (V-PERF: built by `VF.QF`, linear time; a closed constant is evaluated at
every start of the compiled verifier). -/
def M3.Q20 : Loop.Program := VF.QF cfg20
/-- **`M3.Q20` is the node program** (V-PERF; rewrite with it where `M3.Q20` was unfolded to `QAsm.Q`). -/
theorem M3.Q20_eq : M3.Q20 = QAsm.Q cfg20 := VF.QF_eq cfg20

/-- The `P20` node program's cache (INT-2's `C20`), built once (HAR-SPEED: `VF.cacheGF`, linear time). -/
def M3.G20 : M3.PG := VF.cacheGF M3.Q20
/-- **`M3.G20` is the node program's cache** (rewrite with it where `M3.G20` was unfolded to `cacheG`). -/
theorem M3.G20_eq : M3.G20 = M3.cacheG M3.Q20 := VF.cacheGF_eq _

/-- **The lvm tables at `P20`**: the node program's (WP-16a). -/
def M3.tabsP20 : Pub → List M3.Tab := QAsm.tabs cfg20 M3.G20 data20

/-- `V_S` at `P20`. -/
def VS20 (vk c : Digest) (π : Proof) : OProg Bool := VSL P20 M3.tabsP20 vk c π

end Lvm
