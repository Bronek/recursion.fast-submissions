-- New for lvm2 (T-Q): the S2 wiring gadget (BLUEPRINT2 T3–T4, T-W's `wireChProg`). Reuses v1's
-- template gadgets (`gLaneForm`, `gEqTab`, `gDot`, `scGadget`, `ringG`); the closed forms are T-K's
-- circuit twins (`msEvalA`, `thrEvalA`, `LvmWireKernel`).
import LvmQKeccakGkr
import LvmQRingG
import LvmWireKernel

/-!
# The wiring gadget (`wireGadget`, S2)

`F`'s chain wiring phase (T-W's `wireChProg 20 2 0 s n claim`, FRZ-0's CHwire items in order) on the
tape's input claim (`TapeOut.cv`: `value, μ[16], κ, point[P+1], B[25], a[6], flip[7]`):

1. **`preW`** (straight): the `eq` table of `a`; `ω_j` at the positions the phase reads
   (`wPos`: `0, 1, 6` and `8 … 264` and `1087`) as `laneForm B (eq(a, · + z))`, the weights being
   `Lᵀ(eq(a) ⊗ B)` (`keccakLinearTranspose`); `ι(0) = Π(1 + ρ_k)·μ_0`; `thrEvalA ρ μ bits(m)`;
   `padDot ω s = Σ_{p<256} ω_{8+p}·s_p + c43Dot ω`; the target
   `value + ι(0)·padDot + c43Dot·(thr + ι(0))` (`wireTarget`).
2. **The wiring sumcheck** (`scGadget 5 2`, 20 rounds of 2 scalars).
3. **`postW`**: `g_D` and the gated check `b·(final + msEvalA ρ μ σ bits(m) 1 · g_D) = 0`.
4. **`D`'s slot reduction** (`scGadget 1 2`, 2 rounds) and **`slotW`**: the 64 slices, the slot
   weights `W_z(τ) = Σ_{o<4} eq(τ, o)·ω_{8+64o+z}` and the gated check
   `b·(final' + Σ_z W_z·slice_z) = 0`.
5. **The ring switch** of the slices (`ringG`).

Lanes from the first message lane `qw` (FRZ-0): round `k` at `qw + 15k`, `g_D` at `qw + 300`, the
slot rounds at `qw + 303`, the slices at `qw + 333 + 3z`, the ring challenges at `qw + 525 + 9i`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Har Lvm.Loop.QRing

/-! ## The positions of `ω` the phase reads -/

/-- `0, 1, 6` (`0x43`), `8 … 264` (`D`'s 256 bits and the `0x01` at 264), `1087` (`0x80`). -/
def wPos : List Nat := [0, 1, 6] ++ (List.range 257).map (· + 8) ++ [1087]

/-- The index of `ω_{8+p}` in `wPos` (`p ≤ 256`). -/
def wIx (p : Nat) : Nat := 3 + p

/-- `ω_j = laneForm B (s ↦ eq(a, (j mod 64 + s) mod 64)) (j / 64)` (`eZ` the `eq` table of `a`). -/
def gOmega (z : Src) (B eZ : List Src) (j : Nat) : TB Src :=
  gLaneForm z B (fun s => eZ.getD ((j % 64 + s) % 64) default) (j / 64)

/-! ## `thrTailA` and `msTailA` as rows -/

/-- One bit of `thrTailA` (`q₁, q₂` the higher bits', `r` = `ρ_k`, `b` = `t`'s bit):
`q₁ + (1 + b)·r·d`, `q₂ + b·(1 + r)·d` with `d = q₁ + q₂`. -/
def gThrStep (z r b : Src) (q : Src × Src) : TB (Src × Src) :=
  gAdd q.1 q.2 >>= fun d => gMul b r z >>= fun t => gAdd r t >>= fun u => gMul u d q.1 >>= fun n1 =>
  gAdd b t >>= fun w => gMul w d q.2 >>= fun n2 => pure (n1, n2)

/-- `thrTailA ρ tb` from the top bit down (`one` a `1`, `z` a `0`). -/
def gThrTail (z one : Src) : List Src → List Src → TB (Src × Src)
  | r :: ρ, b :: tb => gThrTail z one ρ tb >>= fun q => gThrStep z r b q
  | _, _ => pure (one, z)

/-- `ltE tb4 e` for `e ≤ 16`, all at once: the prefix sums of the `eq` table of `tb4`
(`lt e = Σ_{j<e} eq(tb4, j)`, `lt 0 = 0`). -/
def gLtTab (z one : Src) (tb4 : List Src) : TB (List Src) :=
  gEqTab z [one] tb4 >>= fun e =>
  mapTB (fun k => gSum z (e.take k)) (List.range 17)

/-- **`thrEvalA ρ μ tb`** (`lt` from `gLtTab` on `tb[0..4)`). -/
def gThr (z one : Src) (ρ μ tb lt : List Src) : TB Src :=
  gThrTail z one ρ (tb.drop 4) >>= fun q =>
  gSum z μ >>= fun sm =>
  gDot z ((List.range 16).map fun d => (μ.getD d default, lt.getD d default)) >>= fun L =>
  gAdd q.1 q.2 >>= fun d => gMul sm q.1 z >>= fun x => gMul d L x

/-- The four entries `(c, s) = 00, 01, 10, 11`. -/
abbrev Q4 := Src × Src × Src × Src

/-- `msStep a r t q` for a known bit `t` (`α = (1+a)(1+r)`, `β = a r`, `γ = (1+a) r`, `δ = a(1+r)`). -/
def gMsStep (z : Src) (al be ga de : Src) (t : Bool) (q : Q4) : TB Q4 :=
  let (q00, q01, q10, q11) := q
  if t then
    gDot z [(al, q00), (be, q00)] >>= fun f00 => gDot z [(al, q00), (be, q01)] >>= fun f01 =>
    gDot z [(ga, q00), (de, q10)] >>= fun f10 => gDot z [(ga, q01), (de, q10)] >>= fun f11 =>
    pure (f00, f01, f10, f11)
  else
    gDot z [(al, q00), (be, q01)] >>= fun f00 => gDot z [(al, q01), (be, q01)] >>= fun f01 =>
    gDot z [(ga, q01), (de, q10)] >>= fun f10 => gDot z [(ga, q01), (de, q11)] >>= fun f11 =>
    pure (f00, f01, f10, f11)

/-- `f₀ + b·(f₁ + f₀)`. -/
def gMix (b f1 f0 : Src) : TB Src := gAdd f1 f0 >>= fun d => gMul b d f0

/-- **`msStepA a r b q`**. -/
def gMsStepA (z a r b : Src) (q : Q4) : TB Q4 :=
  gMul a r z >>= fun ar => gAdd a r >>= fun s => gAdd s ar >>= fun al0 => gOne al0 >>= fun al =>
  gAdd r ar >>= fun ga => gAdd a ar >>= fun de =>
  gMsStep z al ar ga de true q >>= fun f1 => gMsStep z al ar ga de false q >>= fun f0 =>
  gMix b f1.1 f0.1 >>= fun n00 => gMix b f1.2.1 f0.2.1 >>= fun n01 =>
  gMix b f1.2.2.1 f0.2.2.1 >>= fun n10 => gMix b f1.2.2.2 f0.2.2.2 >>= fun n11 =>
  pure (n00, n01, n10, n11)

/-- `msTailA σ ρ tb` from the top bit down. -/
def gMsTail (z one : Src) : List Src → List Src → List Src → TB Q4
  | a :: σ, r :: ρ, b :: tb => gMsTail z one σ ρ tb >>= fun q => gMsStepA z a r b q
  | _, _, _ => pure (one, z, z, z)

/-- **`msEvalA ρ μ σ tb 1`** (`|σ| = |tb| = |ρ| + 4`; `lt` from `gLtTab` on `tb[0..4)`). -/
def gMs (z one : Src) (ρ μ σ tb lt : List Src) : TB Src :=
  gMsTail z one (σ.drop 4) (ρ.take (σ.length - 4)) (tb.drop 4) >>= fun q =>
  gEqTab z [one] (σ.take 4) >>= fun e4 =>
  mapTB (fun d => gMul (e4.getD d default) (μ.getD ((d + 1) % 16) default) z) (List.range 16) >>= fun A =>
  gSum z (A.take 15) >>= fun sA =>
  gDot z ((List.range 15).map fun d => (A.getD d default, lt.getD (d + 1) default)) >>= fun L =>
  gMul sA q.1 z >>= fun x1 => gMul (A.getD 15 default) q.2.2.1 x1 >>= fun x2 =>
  gAdd q.2.1 q.1 >>= fun d => gMul d L x2

/-- `eq(ρ, 0) = Π_k (1 + ρ_k)`, from `acc`. -/
def gEq0 (z : Src) : Src → List Src → TB Src
  | acc, [] => pure acc
  | acc, r :: rs => gOne r >>= fun r1 => gMul acc r1 z >>= fun acc' => gEq0 z acc' rs

/-! ## The blocks -/

/-- What `preW` exports. -/
structure PreW where
  /-- Zero and one. -/
  z : Src
  one : Src
  /-- `ω` at `wPos`. -/
  om : List Src
  /-- The `lt` table of `m`'s low four bits. -/
  lt : List Src
  /-- The wiring sumcheck's claim. -/
  target : Src

/-- **The target block** (`cv` the input claim's cells, `mb` `m`'s 20 bits (`E`), `sb` `s`'s 256 bits
(`K`), `P + 1 = |ρ|`). -/
def preW (P : Nat) (cv : Nat → Src) (mb sb : List Src) (b : Src) : TB PreW :=
  let value := cv 0
  let mu := (List.range 16).map fun i => cv (1 + i)
  let rho := (List.range (P + 1)).map fun i => cv (18 + i)
  let B := (List.range 25).map fun l => cv (19 + P + l)
  let a := (List.range 6).map fun i => cv (44 + P + i)
  gZero b >>= fun z => gOne z >>= fun one =>
  gEqTab z [one] a >>= fun eZ =>
  mapTB (gOmega z B eZ) wPos >>= fun om =>
  gEq0 z one rho >>= fun e0 =>
  gMul e0 (mu.getD 0 default) z >>= fun io0 =>
  gLtTab z one (mb.take 4) >>= fun lt =>
  gThr z one rho mu mb lt >>= fun thr =>
  gSum z [om.getD 0 default, om.getD 1 default, om.getD 2 default, om.getD 259 default,
    om.getD 260 default] >>= fun c43 =>
  gDot c43 ((List.range 256).map fun p => (om.getD (wIx p) default, sb.getD p default)) >>= fun pd =>
  gAdd thr io0 >>= fun ti => gMul c43 ti value >>= fun t1 => gMul io0 pd t1 >>= fun tgt =>
  pure ⟨z, one, om, lt, tgt⟩

/-- **The final check** `b·(final + msEvalA ρ μ σ bits(m) 1 · g_D) = 0`, `g_D` at lane `qg`. -/
def postW (P qg : Nat) (cv : Nat → Src) (mb σ lt : List Src) (z one final b : Src) : TB Src :=
  let mu := (List.range 16).map fun i => cv (1 + i)
  let rho := (List.range (P + 1)).map fun i => cv (18 + i)
  gLoad qg [] >>= fun g =>
  gMs z one rho mu σ mb lt >>= fun ms =>
  gMul ms g final >>= fun e => gAssert e b >>= fun _ => pure g

/-- **The slot check** `b·(final' + Σ_z W_z(τ)·slice_z) = 0`, the slices at lanes `qs + 3z`. -/
def slotW (qs : Nat) (om τ : List Src) (z one final b : Src) : TB Unit :=
  mapTB (fun k => gLoad (qs + 3 * k) []) (List.range 64) >>= fun sl =>
  gEqTab z [one] τ >>= fun et =>
  mapTB (fun zz => gDot z ((List.range 4).map fun o => (et.getD o default, om.getD (wIx (64 * o + zz)) default)))
    (List.range 64) >>= fun W =>
  gDot final ((List.range 64).map fun zz => (W.getD zz default, sl.getD zz default)) >>= fun e =>
  gAssert e b

/-- The gadget's outputs. -/
structure WireOut where
  /-- The wiring point `σ` (20 cells). -/
  sigma : List Cell
  /-- `g_D`. -/
  gD : Cell
  /-- The slot point `τ` (2 cells). -/
  tau : List Cell
  /-- The ring switch of `D`'s slices. -/
  ring : RingOut

/-- The wiring phase's lanes (FRZ-0's CHwire). -/
def wireEnd (P qw : Nat) : Nat := qw + 15 * (P + 5) + 225 + 54

/-- **`F`'s `wireChProg 20 2 0 s n claim`** (`w = P + 5` rounds), its first message lane `qw`, the input
claim's cells `cv`, `m`'s bits `mb` (`E`, `P + 5` of them), `s`'s bits `sb` (`K`, 256), the gate `b`,
`zE` an `E` zero cell. -/
def wireGadget (P qw : Nat) (cv : Nat → Cell) (mb sb : List Cell) (b : Cell) (zE : Nat) : BM WireOut :=
  let w := P + 5
  let D := Nat.log2 (2 * w - 1)
  let G := preW P (fun j => gkS (cv j)) (mb.map gkS) (sb.map gkS) (gkS b) 0
  loop [] (tplOf G.2) >>= fun pre =>
  scGadget D 2 qw .plain (G.1.target.gkCell pre) >>= fun sc =>
  let σ := (List.range w).map fun i => sc.cell 2 i
  let H := postW P (qw + 15 * w) (fun j => gkS (cv j)) (mb.map gkS) (σ.map gkS)
    (G.1.lt.map (Src.gkOut pre)) (G.1.z.gkOut pre) (G.1.one.gkOut pre) (gkS (sc.cell 5 (w - 1))) (gkS b) 0
  loop [] (tplOf H.2) >>= fun post =>
  scGadget 1 2 (qw + 15 * w + 3) .plain (H.1.gkCell post) >>= fun sl =>
  let τ := (List.range 2).map fun i => sl.cell 2 i
  loop [] (tplOf (slotW (qw + 15 * w + 33) (G.1.om.map (Src.gkOut pre)) (τ.map gkS) (G.1.z.gkOut pre)
    (G.1.one.gkOut pre) (gkS (sl.cell 5 1)) (gkS b) 0).2) >>= fun _ =>
  ringG (qw + 15 * w + 225) (qw + 15 * w + 33) zE >>= fun rg =>
  pure ⟨σ, H.1.gkCell post, τ, rg⟩

end Lvm.Q1
