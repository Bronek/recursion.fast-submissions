-- New for lvm (WP-14a): obligation O5b, WP-14's `OpenS.refines`, for the frozen V_S at P20.
import LvmVEqMain
import LvmVEqFolPS

/-!
# O5b: V_S ⇒ S.V

**`refines_VSL`**: for lvm tables `tabs` whose shapes fit the record P20 (`fitsR`, for every header's
public values), whenever the frozen `V_S = VSL P20 tabs` accepts a proof on a log, so does WP-5's
compiled verifier of WP-14's `P_S = PSWith (midS tabs)` (`schemeS`). This is the `refines` field of
`Lvm.T.OpenS` (lvm/ASM `LvmSubmissionS`) with `VS := VSL P20 tabs`, `mid := midS tabs`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm

/-- **O5b.** -/
theorem refines_VSL (tabs : Pub → List M3.Tab) (hfit : ∀ pub, M3.fitsR P20 (tabs pub) = true)
    (hw : ∀ x, ∀ t ∈ M3.sumcheckTabs (tabs (pubX x)), 0 < t.w) :
    ∀ (vk : Digest) (L : Log) (c : Digest) (π : RecursionFast.Proof), Lvm.T.isS π = true →
      (VSL P20 tabs vk c π).runLog L = some true →
      ((Lvm.ASM.schemeS vk (Lvm.ASM.PSWith (midS tabs))).V c π).runLog L = some true :=
  refines_logF tabs hfit hw (fol_PS tabs hfit)

end Lvm.VEq
