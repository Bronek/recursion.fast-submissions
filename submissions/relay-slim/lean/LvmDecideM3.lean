import LvmDecideKeccak
import LvmDecideWhir
import LvmSchedule

/-!
# The decision `F`: the interface to the M3 instance (bus, tables, links, layout, LoopIR)

`F` (`LvmDecide`) runs the protocol pieces whose shape BLUEPRINT §4 fixes and leanVM implements
(sumchecks, the two Keccak GKRs, ring switching, the bus GKR, the table sumcheck, the WHIR
openings). What the arithmetisation decides is behind this interface, `M3`, filled by the
packages that own it:

* `chBlock`, `ksBlock`: where the two Keccak tables' 64-slot blocks sit in `C_main` (BLUEPRINT
  §11 A7; WP-14's layout);
* `busFinal`: the bus leaf decomposition (WP-9): from the bus challenges, the GKR point and the
  three trees' values there, and the leaf-decomposition scalars, the check, the column claims,
  each table's form per side and the three sides' totals (leanVM `verifyBusBalance`'s pure part,
  `LeanVmVerifier.lean:1237-1305`);
* `tables`, `tableClaims`: the tables of the table sumcheck and the column claims their
  evaluations make on the commitments (WP-9: every column, fixed ones too, is an evaluation the
  prover sends, leanVM's derived columns; the committed ones become claims);
* `fixVals`, `fixSent`, `pubCheck` (A23, BLUEPRINT §12): the fixed columns `fixCols` (every fixed
  column but `PUB`'s value column) are not checked one by one: their sent evaluations are batched
  into the accumulator (`fixSent`, `κ`), whose folded claim `V` checks with one sweep of their
  closed forms (`fixVals`, `PhiC`); `PUB`'s value column is checked against the header
  (`pubCheck`);
* `chShiftTarget`, `chSc2Target`, `chLink`, `ksShiftTarget`, `ksLink`: the `CH` and `KS` links
  (WP-8, BLUEPRINT §11 A17);
* `ksOutputClaims`: the openings of `KS`'s 25 output lanes (A6, A7).

**The instance** (INT-2, frozen): `M3.real p tabs` (`LvmDecideM3Real`), WP-9's bus and tables on
the layout and links of `M3.ofParts` (`LvmDecideV0`). `V_S` is `VS p (M3.real p tabs)`
(`LvmVerifierS`). The concrete parts of `F` (Keccak GKRs, ring switching, WHIR, the `CH` boundary
claims) are not behind the interface.
-/

set_option autoImplicit false

namespace Lvm

/-- **An accumulator** (A23, BLUEPRINT §12.2): the claim `Φ̃(pt) = y` on the fixed multilinear `Φ`
in `accVars` variables (`pt` = the table point's `tableRounds` coordinates, then `κ`). -/
structure Acc where
  /-- The point (`accVars` coordinates). -/
  pt : List FE
  /-- The claimed value. -/
  y : FE
  deriving Inhabited

/-- The public values `F` has: the arguments `vk`, `c`, and the header in the stream (the seed
query). Digests are four lanes; `σ_leaf` is its 597 lanes (`idx`, 133 chain values, 16
siblings). The child-header checks of the circuit (A2, A3: `vk' = vk`, the statement equation,
`b' = 0 ⇒ c_L' = 0 ∧ σ_leaf' = 0`, `b' = 1 ⇒ σ_leaf' = σ_leaf`) read them. -/
structure Pub where
  /-- The public key (`V`'s argument). -/
  vk : List FK
  /-- The statement (`V`'s argument). -/
  c : List FK
  /-- The flag (0 leaf, 1 node): the gate of the circuit's assertions. -/
  b : Nat
  /-- The left child's statement. -/
  cL : List FK
  /-- The chain start's four lanes. -/
  s : List FK
  /-- The chain length. -/
  n : Nat
  /-- The chain end's four lanes. -/
  h : List FK
  /-- `σ_leaf`'s 597 lanes. -/
  sigLeaf : List FK
  /-- The incoming accumulator `acc_in` (A23; header bytes `[4928, 5624)`). -/
  accIn : Acc
  deriving Inhabited

/-- The header lanes of `PUB` (A23): 702 = 615 + 87. -/
def pubLanes : Nat := 615 + 3 * (accVars + 1)

theorem pubLanes_eq : pubLanes = 702 := by decide

/-- An `E` scalar's three lanes `c₀, c₁, c₂` (its 24 header bytes). -/
def FE.lanes (e : FE) : List FK := [e.c₀, e.c₁, e.c₂]

/-- **The header's lanes from byte 8** (`PUB`'s values, BLUEPRINT A19, A23): `b`, `vk`, `c_L`, `s`,
`n`, `h`, `σ_leaf` (615 lanes), then `acc_in`'s `pt` and `y` (87 lanes, three per scalar). -/
def Pub.hdrLanes (P : Pub) : List FK :=
  [⟨P.b.toUInt64⟩] ++ P.vk ++ P.cL ++ P.s ++ [⟨P.n.toUInt64⟩] ++ P.h ++ P.sigLeaf ++
    (P.accIn.pt ++ [P.accIn.y]).flatMap FE.lanes

/-- The bus phase's values for the leaf decomposition. -/
structure BusIn where
  /-- The tuple-batching challenges (`busBits`). -/
  alphas : List FE
  /-- The fingerprint shift. -/
  beta : FE
  /-- The count tree's root. -/
  countRoot : FE
  /-- The GKR point. -/
  point : List FE
  /-- The push, pull and count trees' values at the point. -/
  values : List FE
  /-- The leaf-decomposition scalars. -/
  leafdec : List FE
  /-- The header's public values. -/
  pub : Pub

/-- What the leaf decomposition gives (leanVM `BusResult`). -/
structure BusOut where
  /-- The decomposition's check. -/
  ok : Bool
  /-- Column claims on the commitments. -/
  claims : List (Com × BlockClaim)
  /-- Each table's form per side (push, pull, count). -/
  forms : List (List Form)
  /-- The three sides' totals. -/
  totals : List FE

/-- The `CH` link phase's values (WP-0's [model]: `ρ, λ, ζ`, the shift sumcheck, the 64 slices of
`in`, a ring switch, a two-round sumcheck, the 64 slices of `Y`, a ring switch, 5 lane
challenges). A ring switch is its target and its Frobenius coefficients (`ringCoefficients`);
the claim it makes is the link's to place. -/
structure ChLinkIn where
  /-- `ρ, λ, ζ`: `logN + 9` challenges. -/
  chal : List FE
  /-- The shift sumcheck's point and final claim. -/
  shift : List FE × FE
  /-- The 64 slices of `in`. -/
  inSlices : List FE
  /-- The first ring switch: target and coefficients. -/
  ringIn : FE × List FE
  /-- The two-round sumcheck's point and final claim. -/
  sc2 : List FE × FE
  /-- The 64 slices of `Y`. -/
  ySlices : List FE
  /-- The second ring switch. -/
  ringY : FE × List FE
  /-- The constant-lane challenges. -/
  constLanes : List FE
  /-- The `CH` GKR's instance point. -/
  inst : List FE
  /-- The 25 output lanes sent before the GKR. -/
  lanesOut : List FE
  /-- The header's public values. -/
  pub : Pub

/-- The `KS` link phase's values (WP-0's [model]). -/
structure KsLinkIn where
  /-- `ρ, λ`: `ksLog + 5` challenges. -/
  chal : List FE
  /-- The shift sumcheck's point and final claim. -/
  shift : List FE × FE
  /-- The four scalars `Y^l(ρ'), in^l(ρ), M^l, X^l`. -/
  vals : List FE
  /-- The `KS` GKR's instance point. -/
  inst : List FE
  /-- The header's public values. -/
  pub : Pub

/-- **The M3 instance as `F` sees it.** -/
structure M3 where
  /-- `CH`'s 64-slot block in `C_main` (`logN + 6` variables; slot `s` = the high 6 bits). -/
  chBlock : Placement
  /-- `KS`'s 64-slot block in `C_main` (`ksLog + 6` variables). -/
  ksBlock : Placement
  /-- The first of `CH`'s four `Y` slots (`in` is slots 0–24, `mid` 25–49); 4-aligned. -/
  chYSlot : Nat
  /-- The bus leaf decomposition. -/
  busFinal : BusIn → BusOut
  /-- The tables of the table sumcheck (their widths sum to `Params.tableEvals`); the public values
  may enter fixed columns' closed forms (WP-9b's PUB array), not the tables' shapes. -/
  tables : Pub → List TableSpec
  /-- The column claims of the tables' evaluations (each table's point and values). -/
  tableClaims : Pub → List (List FE × List FE) → List (Com × BlockClaim)
  /-- **The fixed columns' closed forms** (A23): at a point `p ∈ E^tableRounds`, the extension of
  each column of `fixCols` (table order, then column order; every fixed column but `PUB`'s value
  column) at `p.take τ` of its table. `Φ`'s columns: `PhiC` dots them with `eq(κ, ·)`. -/
  fixVals : Pub → List FE → List FE
  /-- The sent evaluations of `fixCols`, in `fixVals`' order, from the tables' evaluations. -/
  fixSent : Pub → List (List FE × List FE) → List FE
  /-- The check of `PUB`'s value-column evaluation against the header lanes (`pubEval`). -/
  pubCheck : Pub → List (List FE × List FE) → Bool
  /-- The shift sumcheck's claim from `ρ, λ, ζ`. -/
  chShiftTarget : List FE → FE
  /-- The two-round sumcheck's claim from `ρ, λ, ζ`, the shift sumcheck and the `in` slices. -/
  chSc2Target : List FE → List FE × FE → List FE → FE
  /-- The `CH` link's final checks and claims. -/
  chLink : ChLinkIn → Bool × List (Com × BlockClaim)
  /-- The openings of `KS`'s 25 output lanes at the instance point. -/
  ksOutputClaims : List FE → List FE → List (Com × BlockClaim)
  /-- The `KS` shift sumcheck's claim from `ρ, λ`. -/
  ksShiftTarget : List FE → FE
  /-- The `KS` link's final checks and claims. -/
  ksLink : KsLinkIn → Bool × List (Com × BlockClaim)

end Lvm
