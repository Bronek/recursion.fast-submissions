import LvmDecideM3
import LvmSchedule

/-!
# The decision `F`: the layout and the links of the M3 instance (`M3.ofParts`)

The layout and the `CH`/`KS` links of WP-15a's protocol (`docs/lvm/stages/WP-15a.md`), normative
since WP-8 proved them (BLUEPRINT §11 A17). `M3.ofParts p bus tables claims check` is the M3
instance with these and the given bus and table parts; the instance of `V_S` is
`M3.real p tabs = M3.ofParts p (busFinalR …) …` (`LvmDecideM3Real`, WP-9, INT-2). The earlier
null instance `M3.v0` (no flush, no table constraint) is gone (INT-2).

**Layout** (offsets in `K` words; `layout0`).
* `P20` (`ν_main = logN + 6`): `CH` block at 0 (`in` slots 0–24, `mid` 25–49, `Y` lanes 0–3 at
  slots 52–55, a 4-aligned subcube); `KS` block at `50 · 2^logN` (`CH` slots 50–51; `KS` `in`
  0–24, `mid` 25–49, `Y` lanes 0–13 at `KS` slots 50–63); `KS` `Y` lanes `14 + c` at
  `56 · 2^logN + c · 2^ksLog`; `X_l` at `56 · 2^logN + 2^(ksLog+4) + l · 2^recRowsLog`.
* `P8` (larger `C_main`): `KS` block at 0, `CH` block at `2^(ksLog+6)`, `KS` `Y` lanes 14–24 at
  `2^(ksLog+7) + c · 2^ksLog`, `X_l` at `2^(ksLog+7) + 2^(ksLog+4) + l · 2^recRowsLog`.
* `C_rec`: column `c` at `c · 2^recRowsLog`: `M_l` (`l < 17`) columns 0–16, `σ'` column 17.

**`CH` link** (`chal = ρ (logN) ‖ λ (3) ‖ ζ (6)`; `ω(l, p) = eq(λ, l) · eq(ζ, p)`, `l < 8`,
`p < 64`). `Pad43` sends bit `q` of `Y` lane `m` to bit `q + 8` of `in` lane `m` (`q ≤ 55`) or bit
`q − 56` of lane `m + 1`: `W(m, q) = ω(m, q + 8)` or `ω(m + 1, q − 56)`; the constant bits are
`C = Σ_{p<8} ω(0, p) bit_p(0x43) + ω(4, 8)`. One sumcheck over the row `k` of
`S(ρ, k) g(k) + Eq'(ρ, k) h_Y(k)` with claim `C (1 + eq(ρ, 1^logN))`, where
`S(ρ, k) = Σ_{i ≤ N−2} eq(ρ, i) [k = i + 1]` (the non-cyclic shift, `shiftEval`) and
`Eq'(ρ, k) = eq(ρ, k) + eq(ρ, 1^n) eq(1^n, k)` (row `N − 1` masked). Its final `f₁` at `ρ'`
becomes, with the 64 `in` slices at `(ρ', λ, 0, 0, 0)`, the claim
`f₁ + S(ρ, ρ') Σ_p eq(ζ, p) inS_p` of a two-round sumcheck over the `Y` lane `m`, ending at `μ`
with `f₂ = Eq'(ρ, ρ') Σ_q W̃(μ, q) yS_q`, the `Y` slices at `(ρ', μ, 1, 0, 1, 1)` (slot `52 + m`).
Claims: the two ring switches at those points, and the constant lanes `in_l = c_l`
(`l = 8 … 24`; `c_16 = 0x80 << 56`) at `(ρ', slot l)`.

**`KS` link** (`kchal = ρ (ksLog) ‖ λ (5)`; `ω_l = eq(λ, l)`). For every row,
`in_i[l] = cont_i Y_{i−1}[l] + [l < 17] Msg_l[i]` (`cont_0 = 0`). One sumcheck with claim `0` of
`Sc(ρ, k) Y_ω(k) + eq(ρ, k) (in_ω(k) + Msg_ω(k))`, `Sc(ρ, k) = eq(ρ, k + 1) cont_{k+1}`,
`Msg_l(x) = (1 + x_r) M_l(x_lo) + x_r X_l(x_lo)` (`x_r` the coordinate `recRowsLog`); at `ρ'` the
four scalars `Y_ω, in_ω, M_ω, X_ω` and the check `f = Sc(ρ, ρ') Y_ω + eq(ρ, ρ')(in_ω + (1 + ρ'_r)
M_ω + ρ'_r X_ω)`. `cont` is 1 on the trace rows `1 … B − 1` (`B = spongeBlocks`) and on rows
1–31 of the WOTS leaf group (`KS` rows from `2^recRowsLog`: 399 chain steps, 32 leaf rows, 16 path
rows, `leafStmt`, `nodeStmt`). `Sc(ρ, ρ')` is summed over the `cont` rows from two `eq` tables.
-/

set_option autoImplicit false

namespace Lvm

/-- Offsets in `C_main` (in `K` words) of the v0 layout. -/
structure Layout0 where
  /-- `CH`'s block. -/
  ch : Nat
  /-- `KS`'s block. -/
  ks : Nat
  /-- `KS`'s `Y` lanes 14–24. -/
  ksY2 : Nat
  /-- The `X` message columns. -/
  x : Nat

/-- The v0 layout of a parameter set. -/
def layout0 (p : Params) : Layout0 :=
  if p.nuMain = p.logN + slotLog then
    ⟨0, 50 * 2 ^ p.logN, 56 * 2 ^ p.logN, 56 * 2 ^ p.logN + 2 ^ (p.ksLog + 4)⟩
  else
    ⟨2 ^ (p.ksLog + slotLog), 0, 2 ^ (p.ksLog + slotLog + 1),
      2 ^ (p.ksLog + slotLog + 1) + 2 ^ (p.ksLog + 4)⟩

/-- `eq(x, 1^n)`. -/
def eqOnes (x : List FE) : FE := prodE x

/-- `S(x, y) = Σ_{i ≤ N−2} eq(x, i) eq(y, i + 1)`, little-endian: the carry stops at bit `j`. -/
def shiftEval (x y : List FE) : FE :=
  let n := x.length
  sumE ((List.range n).map fun j =>
    prodE ((List.range j).map fun t => x.getD t 0 * (1 + y.getD t 0)) *
      ((1 + x.getD j 0) * y.getD j 0) *
      prodE ((List.range (n - j - 1)).map fun u =>
        1 + x.getD (j + 1 + u) 0 + y.getD (j + 1 + u) 0))

/-- `Eq'(x, y) = eq(x, y) + eq(x, 1^n) eq(1^n, y)`: `eq` with the last row masked. -/
def eqMasked (x y : List FE) : FE := eqEval x y + eqOnes x * eqOnes y

/-- A claim made of several point claims on one commitment of `nu` variables:
`Σ_j c_j · [block_j's extension at z_j]`, as one weight on the whole cube. -/
def sumClaim (nu : Nat) (parts : List (FE × Placement × List FE)) (value : FE) : BlockClaim :=
  ⟨⟨nu, 0⟩, fun x => sumE (parts.map fun (c, blk, z) =>
    c * blk.eqAbove x * eqEval z (x.take blk.variableCount)), value⟩

/-! ## The `CH` link -/

/-- The split of the `CH` link's challenges: `ρ`, `λ`, `ζ`. -/
def chSplit (p : Params) (chal : List FE) : List FE × List FE × List FE :=
  (chal.take p.logN, (chal.drop p.logN).take 3, chal.drop (p.logN + 3))

/-- `ω(l, p)` as a table: row `l < 8`, column `p < 64`. -/
def omegaCH (lam zeta : List FE) : Array (Array FE) :=
  let eL := eqKernelA lam
  let eZ := eqKernelA zeta
  eL.map fun a => eZ.map (a * ·)

/-- `W(m, q)`, the weight of bit `q` of `Y` lane `m` through `Pad43`. -/
def padWeight (om : Array (Array FE)) (m q : Nat) : FE :=
  if q ≤ 55 then (om.getD m #[]).getD (q + 8) 0 else (om.getD (m + 1) #[]).getD (q - 56) 0

/-- The constant bits of `Pad43`'s lanes 0–7: `0x43` in byte 0, `0x01` in byte 33. -/
def padConst (om : Array (Array FE)) : FE :=
  sumE ((List.range 8).filterMap fun p =>
    if (0x43 : Nat).testBit p then some ((om.getD 0 #[]).getD p 0) else none) +
    (om.getD 4 #[]).getD 8 0

/-- The shift sumcheck's claim `C (1 + eq(ρ, 1^logN))`. -/
def chShiftTarget0 (p : Params) (chal : List FE) : FE :=
  let (rho, lam, zeta) := chSplit p chal
  padConst (omegaCH lam zeta) * (1 + eqOnes rho)

/-- The two-round sumcheck's claim `f₁ + S(ρ, ρ') Σ_p eq(ζ, p) inS_p`. -/
def chSc2Target0 (p : Params) (chal : List FE) (shift : List FE × FE) (inS : List FE) : FE :=
  let (rho, _, zeta) := chSplit p chal
  shift.2 + shiftEval rho shift.1 * dot (eqKernel zeta) inS

/-- The `CH` link's check and claims. -/
def chLink0 (p : Params) (blk : Placement) (ySlot : Nat) (i : ChLinkIn) : Bool × List (Com × BlockClaim) :=
  let (rho, lam, zeta) := chSplit p i.chal
  let om := omegaCH lam zeta
  let rho' := i.shift.1
  let mu := i.sc2.1
  let eMu := eqKernel mu
  let wt (q : Nat) : FE := sumE ((List.range 4).map fun m => eMu.getD m 0 * padWeight om m q)
  let ok := i.sc2.2 == eqMasked rho rho' * sumE ((List.range 64).map fun q => wt q * i.ySlices.getD q 0)
  let inPt := rho' ++ lam ++ [0, 0, 0]
  let yPt := rho' ++ mu ++ selectorPoint (ySlot >>> 2) (slotLog - 2)
  let ring (pt : List FE) (r : FE × List FE) : BlockClaim := ⟨blk, fun x => ringWeight pt x r.2, r.1⟩
  let consts := (List.range 17).map fun j =>
    let l := 8 + j
    BlockClaim.point blk (rho' ++ selectorPoint l slotLog)
      (FE.ofK (if l = 16 then ⟨(0x80 : UInt64) <<< 56⟩ else 0))
  (ok, ([ring inPt i.ringIn, ring yPt i.ringY] ++ consts).map (.main, ·))

/-! ## The `KS` link -/

/-- `KS`'s `Y` lane `l` as a placement (`ksLog` variables, or the block's slot). -/
def ksYPart (p : Params) (L : Layout0) (l : Nat) (pt : List FE) : Placement × List FE :=
  if l < 14 then (⟨p.ksLog + slotLog, L.ks⟩, pt ++ selectorPoint (50 + l) slotLog)
  else (⟨p.ksLog, L.ksY2 + (l - 14) * 2 ^ p.ksLog⟩, pt)

/-- The rows where `cont = 1`: the trace's continuation rows and rows 1–31 of the WOTS leaf. -/
def contRows (p : Params) : List Nat :=
  (List.range (spongeBlocks p - 1)).map (· + 1) ++
    (List.range 31).map (2 ^ p.recRowsLog + 399 + 1 + ·)

/-- `Sc(ρ, ρ') = Σ_{i : cont_i = 1} eq(ρ, i) eq(ρ', i − 1)`, summed over the rows. -/
def contShiftRef (p : Params) (rho rho' : List FE) : FE :=
  let e := eqKernelA rho
  let e' := eqKernelA rho'
  (contRows p).foldl (fun acc i => acc + e.getD i 0 * e'.getD (i - 1) 0) 0

/-- One level of `preCFV` (`Q1.preStep`). -/
def preStepV (x0 y0 : FE) (h : Bool) (r : FE × FE × FE) : FE × FE × FE :=
  let E1 := if h then r.2.1 + r.2.2 else r.2.1
  ((1 + y0) * x0 * E1 + y0 * (1 + x0) * r.1,
   (1 + y0) * (1 + x0) * E1 + y0 * x0 * r.2.1,
   (if h then y0 * x0 else (1 + y0) * (1 + x0)) * r.2.2)

/-- The shift prefix sums in closed form (`Q1.preCF`; `Q1.preCF_eq`). -/
def preCFV : List FE → List FE → Nat → FE × FE × FE
  | x0 :: x, y0 :: y, H => preStepV x0 y0 (H % 2 = 1) (preCFV x y (H / 2))
  | _, _, H => (FE.ofK (if H % 2 = 0 then 0 else 1), FE.ofK (if H % 2 = 0 then 0 else 1), 1)

/-- `contShiftRef` from three prefix sums (`Q1.contShift_fast`) when the shapes allow it. -/
def contShift (p : Params) (rho rho' : List FE) : FE :=
  if rho.length = p.ksLog ∧ rho'.length = p.ksLog ∧ 1 ≤ spongeBlocks p ∧ spongeBlocks p ≤ 2 ^ p.ksLog ∧
      2 ^ p.recRowsLog + 431 ≤ 2 ^ p.ksLog then
    (preCFV rho rho' (spongeBlocks p - 1)).1 + (preCFV rho rho' (2 ^ p.recRowsLog + 399 + 31)).1 +
      (preCFV rho rho' (2 ^ p.recRowsLog + 399)).1
  else contShiftRef p rho rho'

/-- The `KS` link's check and claims. -/
def ksLink0 (p : Params) (i : KsLinkIn) : Bool × List (Com × BlockClaim) :=
  let L := layout0 p
  let rho := i.chal.take p.ksLog
  let om := eqKernel (i.chal.drop p.ksLog)
  let rho' := i.shift.1
  let lo := rho'.take p.recRowsLog
  let xr := rho'.getD p.recRowsLog 0
  let y := i.vals.getD 0 0
  let inv := i.vals.getD 1 0
  let mv := i.vals.getD 2 0
  let xv := i.vals.getD 3 0
  let ok := i.shift.2 == contShift p rho rho' * y + eqEval rho rho' * (inv + (1 + xr) * mv + xr * xv)
  let lanes25 := List.range 25
  let lanes17 := List.range 17
  let yC := sumClaim p.nuMain (lanes25.map fun l =>
    let (b, z) := ksYPart p L l rho'
    (om.getD l 0, b, z)) y
  let inC := sumClaim p.nuMain (lanes25.map fun l =>
    (om.getD l 0, (⟨p.ksLog + slotLog, L.ks⟩ : Placement), rho' ++ selectorPoint l slotLog)) inv
  let mC := sumClaim p.nuRec (lanes17.map fun l =>
    (om.getD l 0, (⟨p.recRowsLog, l * 2 ^ p.recRowsLog⟩ : Placement), lo)) mv
  let xC := sumClaim p.nuMain (lanes17.map fun l =>
    (om.getD l 0, (⟨p.recRowsLog, L.x + l * 2 ^ p.recRowsLog⟩ : Placement), lo)) xv
  (ok, [(.main, yC), (.main, inC), (.crec, mC), (.main, xC)])

/-- The openings of `KS`'s 25 output lanes at the instance point, in lane order. -/
def ksOutputClaims0 (p : Params) (rk v : List FE) : List (Com × BlockClaim) :=
  (List.range 25).map fun l =>
    let (b, z) := ksYPart p (layout0 p) l rk
    (.main, BlockClaim.point b z (v.getD l 0))

/-! ## The instance -/

/-- **The M3 instance from its bus and table parts**: the v0 layout and WP-15a's links (A17),
`busFinal`, `tables`, `tableClaims`, `fixVals`, `fixSent`, `pubCheck` given (A23). -/
def M3.ofParts (p : Params) (busFinal : BusIn → BusOut) (tables : Pub → List TableSpec)
    (tableClaims : Pub → List (List FE × List FE) → List (Com × BlockClaim))
    (fixVals : Pub → List FE → List FE) (fixSent : Pub → List (List FE × List FE) → List FE)
    (pubCheck : Pub → List (List FE × List FE) → Bool) : M3 :=
  let L := layout0 p
  let ch : Placement := ⟨p.logN + slotLog, L.ch⟩
  { chBlock := ch
    ksBlock := ⟨p.ksLog + slotLog, L.ks⟩
    chYSlot := 52
    busFinal := busFinal
    tables := tables
    tableClaims := tableClaims
    fixVals := fixVals
    fixSent := fixSent
    pubCheck := pubCheck
    chShiftTarget := chShiftTarget0 p
    chSc2Target := chSc2Target0 p
    chLink := chLink0 p ch 52
    ksOutputClaims := ksOutputClaims0 p
    ksShiftTarget := fun _ => 0
    ksLink := ksLink0 p }

end Lvm
