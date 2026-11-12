-- Ported from leanVM `formal/lean_vm/LeanVM/Protocol/EndToEnd/Front/BusTable.lean` (formal rev 40f877dc) as `LvmFrontBusTable` for lvm (WP-2).
/-
  LeanVM.Protocol.EndToEnd.Front.BusTable

  The bus phase followed by the table sumcheck, specified from the commitment's doom to the table
  seam on the wire, and the commitment's doom as the bus phase's.
-/


import LvmBTableClaims
import LvmFrontTablePhase
import LvmFrontCommitDoom

/-! lvm (WP-2): over a table list `tables` with `htw : ∀ t ∈ tables, 0 < t.width` (see
`LvmFrontTablePhase`). Cut: the section `LeanIsa` (`candsOf`, `candsL`, `candsL_mem`,
`candsOf_ncard`, `exists_pushBlock`, `rows_of_mem_pushBlocks`, `verifierLayout_injective`,
`commitDoom_hdoom`): the commitment's doom at the leanISA instance and layout (`leanIsaInstance`,
`verifierLayout`, `Complete.BusLayout`, `EndToEnd.Candidates`), a leanISA seam; an instantiation
supplies its own `HDoom cands (Seam.commit I) input` at the bus phase's start. -/

/-!
# The bus phase and the table sumcheck

`busTableSpec` composes `busThenSpec` with `tablePhaseSpec` for the program's
`do let bus ← verifyBusBalance computedBytecodeValue layout; tablePhase layout bus`, from the commitment's doom
(`Seam.commit` on the candidates) to the table seam on the wire (`TablePost`). It needs the table phase's
identities (`TableFid`) for every read of the right shape.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier
open scoped NNReal ENNReal

section

variable (I : M3Instance) (hI : Bus.Conditions I) (cands : Word → Set (∀ i, TheOracle I i))
  (input : I.Stmt) (tables : List Table) (layout : Verifier.Layout) {εmax : ℝ≥0∞}

/-- What a read of the bus phase of the right shape is. -/
def BusWit.Shaped (w : BusWit) : Prop :=
  w.point.length = I.μBus ∧ w.values.length = 3 ∧ w.memory.length = 3

instance (w : BusWit) : Decidable (w.Shaped I) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The bus phase, then the table sumcheck**: from the commitment's doom to the table seam on
the wire. -/
noncomputable def busTableSpec (colOf : I.ColumnId → ℕ)
    (fid : ∀ w : BusWit, w.Shaped I → TableFid tables I hI input layout colOf w)
    (htw : ∀ t ∈ tables, 0 < t.width) (hd : I.d ≤ 2)
    {L₀ : ℕ} (hfin : ∀ W, (cands W).Finite) (hcard : ∀ W, (cands W).ncard ≤ L₀)
    (hμ : I.μBus ≠ 0)
    (hdepth : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = I.μBus)
    (hab : abError I L₀ < 1) (he4 : roundError L₀ 4 ≤ εmax)
    (hT : interpLead L₀ 2 (lambdaError L₀) ≤ εmax) (hlam : lambdaError L₀ + 0 ≤ εmax)
    {T : ℝ≥0∞} (he3 : roundError L₀ 3 + T ≤ εmax) (hTf : T ≤ εmax)
    (hxi : xiError I L₀ + sumcheckLead (List.replicate (layout.tableLogHeights.foldl max 0) none)
      T ≤ εmax) :
    Spec ((verifyBusBalance tables computedBytecodeValue layout).bind (tablePhaseClaims tables layout))
      (HDoom cands (Seam.commit I) input)
      (TablePost I cands input colOf) εmax (abError I L₀ + 0) T :=
  busThenSpec I hI cands input tables layout hxi
    (fun w ↦ if hw : w.Shaped I then
      tablePhaseSpec tables I hI cands input layout colOf w (fid w hw) htw hd hfin hcard he3 hTf
    else specOfFalse fun _ hp ↦ hw ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    hfin hcard hμ hdepth hab he4 hT hlam

end
end LeanVM.Protocol.EndToEnd.Front
