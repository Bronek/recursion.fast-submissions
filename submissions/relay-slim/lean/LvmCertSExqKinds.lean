-- WP-14d (EXQ). New for lvm: the event kinds of a run against the schedule's items, and the
-- middle phases' shape obligation `MidFollows` (WP-14a proves it for `midS` from its `Fol`; WP-14d
-- consumes it for O5c). Light on purpose (schedule + verifier language only), so that both sides
-- import it.
import LvmSchedule
import LvmDslProg

/-!
# Event kinds and the middle phases' shape

* `kindOf e`: a read, a sample, or anything else;
* `itemKinds its`: the kinds the schedule's items stand for (`read m` is `m` reads, `sample` one
  sample; caps, positions and openings are `other`, unused here);
* `midItems`: the items of the middle phases at P20 (bus, tables, `CH`, `CH` link, `KS`, `KS`
  link; reads and samples only);
* **`MidFollows mid`**: every accepted run of `mid x` has exactly the kinds of `midItems`.
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Protocol.Compile

/-- The kind of an event. -/
inductive EvK where
  | read
  | sample
  | other
  deriving DecidableEq, Repr

/-- The kind of an event: a read, a sample, or anything else. -/
def kindOf : Ev → EvK
  | .read _ => .read
  | .sample _ => .sample
  | _ => .other

/-- The kinds the schedule's items stand for. -/
def itemKinds : List Item → List EvK
  | [] => []
  | .read m :: its => List.replicate m .read ++ itemKinds its
  | .sample :: its => .sample :: itemKinds its
  | _ :: its => .other :: itemKinds its

/-- The items of the middle phases at P20 (bus, tables, `CH`, `CH` link, `KS`, `KS` link). -/
def midItems : List Item := (((phases P20).drop 1).take 6).flatMap (·.2)

/-- **The middle phases' shape**: every accepted run of `mid x` has the kinds of `midItems`. -/
def MidFollows {α : Type} (mid : List UInt8 → VerifierProgram α) : Prop :=
  ∀ x l a, (mid x).after l = some (.ret a) → l.map kindOf = itemKinds midItems

end Lvm.ASM
