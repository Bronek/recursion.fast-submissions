-- WP-5 (FS), reconciled at the PB merge (INT-1, BLUEPRINT §11 A15). This module only re-exports
-- WP-2's canonical definitions: `LeanVM.Parameters.K`/`E` (`LvmFields`), `instFintypeK`
-- (`LvmFieldFacts`), `VerifierProgram`, `bind` (`LvmDsl`) and `Word`, `WellShaped`, `Ev`, `commits`,
-- `answer`, `after`, `Reachable`, `Boundary`, `grindBits`, `esc`, `Cert` (`LvmDslProg`). The FS
-- compiler's modules import this one; nothing is declared here.
import LvmDslProg
import LvmFieldFacts
import RecursionFast.Contract.Relation
