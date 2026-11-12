import LvmDriver
import LvmDecide
import LvmDecideM3Real
import LvmLoopMleFast

/-!
# `V_S`: the `S` branch of the verifier (BLUEPRINT §1, §5)

`V_S p m vk c π : OProg Bool`: the native checks of the header (`parseOk`, no query on a
rejection), then the driver over the schedule (`drive`), whose last step is the decision
`F vk c Σ` (`decideF`) on the stream it recorded. `p` is the parameter record, `m` the M3
instance (`LvmDecideM3`). WP-14's `V` dispatches on `π[0]`: `'S'` here, everything else to the
Library's witness sending (A18).

**The frozen `V_S`** (INT-2) is `VSL p tabs = VS p (M3.real p tabs)`: WP-9's bus and tables
(`LvmDecideM3Real`) on the layout and links of A17, `tabs` the lvm tables of the final program
(`fun pub => LvmM3LoopTab.lvmTabs Q pl groups (arrsOf pub) aux`), the record meeting
`M3.fitsR p (tabs pub)`. Build them with `M3.lvmTabsC C` (`LvmLoopMleFast`; `C = M3.cacheG Q` a
top-level constant, built once): the same tables (`lvmTabsC_eq`), the fixed-column closed forms read
from the cache (WP-9's `lvmTabs` evaluates them in time (program size) × (members)). `VS20`/`VS8` (`LvmQAsmV`, WP-16a) fix the record and
the tables `M3.tabsP20`/`M3.tabsP8` of the assembled node program.
-/

set_option autoImplicit false

namespace Lvm

open RecursionFast

/-- **`V_S`**: parse, then drive the schedule and decide. -/
def VS (p : Params) (m : M3) (vk c : Digest) (π : Proof) : OProg Bool :=
  if parseOk p vk c π then drive p π (decideF p m vk c) else .ret false

/-- **The lvm `V_S`**: `V_S` with the real M3 instance of the tables `tabs`. -/
def VSL (p : Params) (tabs : Pub → List M3.Tab) (vk c : Digest) (π : Proof) : OProg Bool :=
  VS p (M3.real p tabs) vk c π

-- `M3.tabsP20`, `M3.tabsP8`, `VS20`, `VS8`: `LvmQAsmV` (WP-16a, the node program's tables).

/-- A rejected header asks no query. -/
theorem VS_reject {p : Params} {m : M3} {vk c : Digest} {π : Proof} (h : parseOk p vk c π = false) :
    VS p m vk c π = .ret false := by
  simp [VS, h]

end Lvm
