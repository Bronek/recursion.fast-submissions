-- New for lvm (WP-16a; split out of `LvmQAsmV` by WP-16a2): `V_S` at the test set `P8`. Kept out of
-- `Solution`'s import closure, whose closed constants the compiled verifier evaluates at every start.
import LvmQAsmV

/-!
# `V_S` at `P8`

`M3.Q8`, `M3.G8` (V-PERF/HAR-SPEED's linear-time builders), `M3.tabsP8 = QAsm.tabs cfg8 M3.G8 data8`,
`VS8` (the frozen `V_S` on them).
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast Lvm.QAsm

/-- The `P8` node program. -/
def M3.Q8 : Loop.Program := VF.QF cfg8

/-- **`M3.Q8` is the node program.** -/
theorem M3.Q8_eq : M3.Q8 = QAsm.Q cfg8 := VF.QF_eq cfg8

/-- The `P8` node program's cache. -/
def M3.G8 : M3.PG := VF.cacheGF M3.Q8

/-- **`M3.G8` is the node program's cache.** -/
theorem M3.G8_eq : M3.G8 = M3.cacheG M3.Q8 := VF.cacheGF_eq _

/-- **The lvm tables at `P8`.** -/
def M3.tabsP8 : Pub → List M3.Tab := QAsm.tabs cfg8 M3.G8 data8

/-- `V_S` at `P8`. -/
def VS8 (vk c : Digest) (π : Proof) : OProg Bool := VSL P8 M3.tabsP8 vk c π

end Lvm
