-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/Spine/Slots.lean` (formal rev 40f877dc) as `LvmSpineSlots` for lvm (WP-2): the question to the stack only.
/-
  LeanVM.Protocol.Spine.Slots

  The question the protocol asks the stack at the end.
-/

import LvmSpineErrors
import LvmSpineSeams

/-! lvm (WP-2): cut, as ArkLib's typed front (`ToArkLib.Typed.Commit`, `Typed.Schedule`): every
slot and its errors (`busSlot`, `busErrors`, `tableSlot`, `tableErrors`, `pubTree`, `pubRoles`,
`pubSlot`, `pubErrors`, `ringErrors`, `busErrors_bounded`) and the typed `stackQuestion`
(a `Typed.Question`). The errors those slots charge are carried, challenge by challenge, by the
verifier-program specifications instead (`abError`, `roundError`, `lambdaError`, `unitError`,
`xiError` in `LvmFrontBusSpec`, `LvmFrontBusGkr`, `LvmFrontBusPhase`, `LvmFrontTableArk`). Kept:
the check on the stack's answer, and the opened seam, restated without `Typed.Question.rel` as
the set on which the stack's answer to the final claim's weight passes the check (the source's
`(stackQuestion I).rel (Seam.done I)` with `Seam.done` true). -/

/-!
# The question to the stack

The protocol ends with one question to the stack: the final weighted claim's weight, accepted
when the answer is the claim's value. `Seam.opened` is what the opening must reach for the
question to pass: the final claim holds of the stack.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters

section

variable (I : M3Instance)

/-- The check on the stack's answer to a claim's weight: the answer is the claim's value. -/
def stackCheck (c : WeightedClaim I) (a : E) : Bool := decide (a = c.value)

/-- The check is the equality. -/
theorem stackCheck_iff (c : WeightedClaim I) (a : E) : stackCheck I c a = true ↔ a = c.value :=
  decide_eq_true_iff

/-- Before the question: the stack's answer to the final claim's weight passes the check. -/
def Seam.opened : Set ((WeightedClaim I × ∀ i, TheOracle I i) × Unit) :=
  {p | stackCheck I p.1.1 (p.1.1.weight.pair (algebraMap K E) (theStack p.1.2).values) = true}

/-- The opened seam is the final claim holding of the stack. -/
theorem Seam.opened_iff (c : WeightedClaim I) (o : ∀ i, TheOracle I i) (w : Unit) :
    ((c, o), w) ∈ Seam.opened I ↔ c.Holds (theStack o) :=
  stackCheck_iff I c _

end
end LeanVM.Protocol
