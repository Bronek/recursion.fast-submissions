-- New for lvm (WP-8): V_S phases 4–7 composed under `Spec.bind'` (BLUEPRINT §3.2, §4.1–4.2), and the
-- table relations they consume tied to `chain_of_CH` and the sponge digests.
import LvmSpongeTableLink

/-!
# The `CH` and `KS` phases, composed

* `CHRel`: the `CH` table's constraints (the region, the tied output lanes `0 … 3`, the link
  bitwise, the constant lanes); **`chain_of_CHRel`**: with the two boundary claims (A1) and
  `1 ≤ n ≤ 2^h`, they prove `chainEnd s n = hd`.
* `KSRel`: the `KS` table's constraints (the region, all 25 output lanes tied, the sponge link);
  **`spongeRel_of_KSRel`**: they are `SpongeRel` (`LvmSpongeTable`), whence the digests.
* **`chPhaseSpec`** (V_S phases 4–5: `callerSpec` then `chLinkSpec`), **`ksPhaseSpec`** (6–7:
  `callerSpec` then `ksLinkSpec`), **`kgSpec`** (4–7): from doom of the relations and `R` to doom of
  every claim the phases leave for the openings, and `R`. Each phase's claims are carried by the
  next phase's `R`; the leads chain as the calculus requires (a phase's follower lead is the next
  phase's lead, the groups that straddle two phases bounded by the `hring…` hypotheses).
-/

set_option autoImplicit false

namespace Lvm.KG

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr
open LeanVM.Protocol.EndToEnd.Front Finset
open scoped ENNReal

/-! ## The relations -/

/-- **`CH`'s constraints** on its 64-slot block (`Y` lanes at slots `ys … ys + 3`). -/
structure CHRel (h ys : ℕ) (col : ℕ → K) : Prop where
  /-- The middle state is twelve rounds of the input on every row. -/
  region : RegionValid h col
  /-- The output lanes `0 … 3` are the permutation's on every row. -/
  out : OutRel h 4 col (chY h ys col)
  /-- The link on lanes `0 … 7`, bitwise. -/
  bits : LinkBits h ys col
  /-- The constant lanes `8 … 24`. -/
  consts : ConstLanes h col

/-- **`CH` proves the chain**: its constraints and the two boundary claims (`in_0 = Pad43(s)`,
`Y_{n−1} = hd`). -/
theorem chain_of_CHRel {h ys : ℕ} {col : ℕ → K} {s hd : RecursionFast.Digest} {n : ℕ}
    (hn : 1 ≤ n) (hN : n ≤ 2 ^ h) (H : CHRel h ys col)
    (hfirst : inState h col 0 0 = pad43St (digestBits s))
    (hlast : ∀ m < 4, col (n - 1 + 2 ^ h * (ys + m)) =
      K.ofLane (RecursionFast.Keccak.blockLane hd.toArray m)) :
    RecursionFast.chainEnd s n = hd :=
  chain_of_CH h ys col hn hN
    ⟨fun x hx m hm ↦ H.out m hm x hx, link_of_bits h ys col H.bits H.consts, hfirst, hlast⟩

/-- `KS`'s output lanes as a row-by-lane table. -/
def ksYRow (hk y2 : ℕ) (main ks : ℕ → K) (i l : ℕ) : K := ksY hk y2 main ks l i

/-- **`KS`'s constraints** (V_S's layout: `Y` lanes `0 … 13` in the block, `14 … 24` at `y2`). -/
structure KSRel (hk r y2 : ℕ) (rows : List ℕ) (main ks : ℕ → K) (M X : ℕ → ℕ → K) : Prop where
  /-- The middle state is twelve rounds of the input on every row. -/
  region : RegionValid hk ks
  /-- All 25 output lanes are the permutation's on every row. -/
  out : OutRel hk 25 ks (ksY hk y2 main ks)
  /-- The sponge link. -/
  link : SpongeLink hk rows ks (ksYRow hk y2 main ks) (ksMsg r M X)

/-- **`KS`'s constraints are a sponge table** (`SpongeRel`, whence `traceDigest_of_KS`,
`wotsLeaf_of_KS`, `wotsStep_of_KS`, `sigNode_of_KS`, …), `cont i = [i ∈ rows]`. -/
theorem spongeRel_of_KSRel {hk r y2 : ℕ} {rows : List ℕ} {main ks : ℕ → K} {M X : ℕ → ℕ → K}
    (H : KSRel hk r y2 rows main ks M X) (h0 : 0 ∉ rows) :
    SpongeRel hk ks (ksYRow hk y2 main ks) (ksMsg r M X) (fun i ↦ decide (i ∈ rows)) where
  out i hi l hl := H.out l hl i hi
  link i hi l hl := by simpa using H.link i hi l hl
  cont0 := by simpa using h0

/-! ## The phases composed -/

variable {β : Type} {C : List Ev → Set β} [Finite β] {L₀ : ℕ} {εmax T : ℝ≥0∞}

/-- The claims a Keccak phase with caller claims leaves (`CallerPost` without the lengths). -/
def CallerClaims (h nt : ℕ) (qk : ℕ → K) (Y : ℕ → ℕ → K)
    (co : List E × List E × (List ColumnClaim × List E × List E) × (E × (List E → E))) : Prop :=
  RingColTrue h qk co.2.2.2 ∧ (∀ c ∈ co.2.2.1.1, colTrue h qk c) ∧ TiedTrue h nt Y co.1 co.2.1

/-- The claims the `CH` link leaves. -/
def ChLinkClaims (h : ℕ) (col : ℕ → K) (lo : ChLinkOut) : Prop :=
  RingColTrue h col lo.ringIn ∧ RingColTrue h col lo.ringY ∧ ConstClaims h col lo.shift.1

/-- **V_S phases 4–5**: the `CH` Keccak phase with caller claims, then the `CH` link. -/
noncomputable def chPhaseSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (P ys : ℕ)
    (hys : ys % 4 = 0) (hys' : ys / 4 < 16) (col : β → ℕ → K) (R : β → Prop)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hr0 : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + 0 ≤ εmax)
    (hrT : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + T ≤ εmax)
    (hrL : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) +
      (((P + 4 + 9 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) ≤ εmax) :
    Spec (callerProg (P + 4) >>= fun co ↦ chLinkProg (P + 4) ys >>= fun lo ↦
        VerifierProgram.ret (co, lo))
      (Doomed C (fun q ↦ CHRel (P + 4) ys (col q) ∧ R q))
      (fun out hist ↦ (out.1.1.length = P + 4 ∧ out.1.2.1.length = 25 ∧
        out.2.shift.1.length = P + 4) ∧
        Doomed C (fun q ↦ CallerClaims (P + 4) 4 (col q) (chY (P + 4) ys (col q))
          out.1 ∧ ChLinkClaims (P + 4) (col q) out.2 ∧ R q) hist)
      εmax (((P + 4 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  ((callerSpec hst hcard P 4 (by norm_num) col (fun q ↦ chY (P + 4) ys (col q))
      (fun q ↦ LinkBits (P + 4) ys (col q) ∧ ConstLanes (P + 4) (col q) ∧ R q) h46 hrL).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, ho, hb, hc, hR⟩ ↦ ⟨⟨hv, ho, hb, hc⟩, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun co ↦
  if hco : co.1.length = P + 4 ∧ co.2.1.length = 25 then
    ((chLinkSpec hst hcard (P + 4) ys hys hys' col
        (fun q ↦ CallerClaims (P + 4) 4 (col q) (chY (P + 4) ys (col q)) co ∧ R q) h2 hr0 hrT).mono
      (fun _ hd ↦ Doomed.mono hd.2.2 fun q ⟨hb, hc, ⟨hring, hcol, htied⟩, hR⟩ ↦
        ⟨hring, hcol, htied, hb, hc, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun lo ↦
    (Spec.ret (co, lo)).mono
      (fun _ hd ↦ ⟨⟨hco.1, hco.2, hd.1⟩,
        Doomed.mono hd.2 fun _ ⟨hcl, ⟨hin, hy, hcc⟩, hR⟩ ↦ ⟨hin, hy, hcc, hcl, hR⟩⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hco ⟨hd.1, hd.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The claims the `KS` link leaves. -/
def KsLinkClaims (hk r : ℕ) (ks : ℕ → K) (Y M X : ℕ → ℕ → K)
    (lo : List E × (List E × E) × List E) : Prop :=
  KsClaims hk r ks Y M X (lo.1.drop hk) lo.2.1.1 lo.2.2

/-- **V_S phases 6–7**: the `KS` Keccak phase with all 25 lanes tied, then the sponge link. -/
noncomputable def ksPhaseSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (Pk r y2 : ℕ)
    (hkr : Pk + 4 = r + 1) (rows : List ℕ) (hnd : rows.Nodup)
    (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ (Pk + 4)) (main ks : β → ℕ → K) (M X : β → ℕ → ℕ → K)
    (R : β → Prop) (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hT : T ≤ εmax)
    (hrL : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) +
      (((Pk + 4 + 5 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) ≤ εmax) :
    Spec (callerProg (Pk + 4) >>= fun co ↦ ksLinkProg (Pk + 4) r rows >>= fun lo ↦
        VerifierProgram.ret (co, lo))
      (Doomed C (fun q ↦ KSRel (Pk + 4) r y2 rows (main q) (ks q) (M q) (X q) ∧ R q))
      (fun out hist ↦ (out.1.1.length = Pk + 4 ∧ out.1.2.1.length = 25 ∧
        out.2.2.1.1.length = Pk + 4) ∧ Doomed C (fun q ↦
        CallerClaims (Pk + 4) 25 (ks q) (ksY (Pk + 4) y2 (main q) (ks q)) out.1 ∧
        KsLinkClaims (Pk + 4) r (ks q) (ksYRow (Pk + 4) y2 (main q) (ks q)) (M q) (X q) out.2 ∧
          R q) hist)
      εmax (((Pk + 4 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  ((callerSpec hst hcard Pk 25 le_rfl ks (fun q ↦ ksY (Pk + 4) y2 (main q) (ks q))
      (fun q ↦ SpongeLink (Pk + 4) rows (ks q) (ksYRow (Pk + 4) y2 (main q) (ks q))
        (ksMsg r (M q) (X q)) ∧ R q) h46 hrL).mono
    (fun _ hd ↦ Doomed.mono hd fun q ⟨hv, ho, hl, hR⟩ ↦ ⟨⟨hv, ho, hl⟩, hR⟩)
    (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun co ↦
  if hco : co.1.length = Pk + 4 ∧ co.2.1.length = 25 then
    ((ksLinkSpec hst hcard (Pk + 4) r hkr rows hnd hrows ks
        (fun q ↦ ksYRow (Pk + 4) y2 (main q) (ks q)) M X
        (fun q ↦ CallerClaims (Pk + 4) 25 (ks q) (ksY (Pk + 4) y2 (main q) (ks q)) co ∧ R q)
        h2 hT).mono
      (fun _ hd ↦ Doomed.mono hd.2.2 fun _ ⟨hl, ⟨hring, hcol, htied⟩, hR⟩ ↦
        ⟨hring, hcol, htied, hl, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun lo ↦
    (Spec.ret (co, lo)).mono
      (fun _ hd ↦ ⟨⟨hco.1, hco.2, hd.1⟩, Doomed.mono hd.2 fun _ ⟨hcl, hk, hR⟩ ↦ ⟨hk, hcl, hR⟩⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hco ⟨hd.1, hd.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **V_S phases 4–7**: `CH` (Keccak with caller claims, link), then `KS` (Keccak with all lanes
tied, sponge link), from doom of both tables' relations and `R` to doom of every claim they leave
and `R`. -/
noncomputable def kgSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀) (P ys Pk r y2 : ℕ)
    (hys : ys % 4 = 0) (hys' : ys / 4 < 16) (hkr : Pk + 4 = r + 1) (rows : List ℕ)
    (hnd : rows.Nodup) (hrows : ∀ i ∈ rows, 1 ≤ i ∧ i < 2 ^ (Pk + 4))
    (col main ks : β → ℕ → K) (M X : β → ℕ → ℕ → K) (R : β → Prop)
    (h46 : (L₀ : ℝ≥0∞) * errE 46 ≤ εmax) (h2 : (L₀ : ℝ≥0∞) * errE 2 + 0 ≤ εmax)
    (hr0 : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) + 0 ≤ εmax)
    (hrK : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) +
      (((Pk + 4 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) ≤ εmax)
    (hrL : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) +
      (((P + 4 + 9 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) ≤ εmax)
    (hrKL : (∑ _i ∈ range 6, (L₀ : ℝ≥0∞) * errE 1) +
      (((Pk + 4 + 5 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) ≤ εmax) (hT : T ≤ εmax) :
    Spec ((callerProg (P + 4) >>= fun co ↦ chLinkProg (P + 4) ys >>= fun lo ↦
          VerifierProgram.ret (co, lo)) >>= fun ch ↦
        (callerProg (Pk + 4) >>= fun co ↦ ksLinkProg (Pk + 4) r rows >>= fun lo ↦
          VerifierProgram.ret (co, lo)) >>= fun kso ↦ VerifierProgram.ret (ch, kso))
      (Doomed C (fun q ↦ CHRel (P + 4) ys (col q) ∧
        KSRel (Pk + 4) r y2 rows (main q) (ks q) (M q) (X q) ∧ R q))
      (fun out hist ↦ ((out.1.1.1.length = P + 4 ∧ out.1.1.2.1.length = 25 ∧
          out.1.2.shift.1.length = P + 4) ∧ (out.2.1.1.length = Pk + 4 ∧
          out.2.1.2.1.length = 25 ∧ out.2.2.2.1.1.length = Pk + 4)) ∧ Doomed C (fun q ↦
        (CallerClaims (P + 4) 4 (col q) (chY (P + 4) ys (col q)) out.1.1 ∧
          ChLinkClaims (P + 4) (col q) out.1.2) ∧
        (CallerClaims (Pk + 4) 25 (ks q) (ksY (Pk + 4) y2 (main q) (ks q)) out.2.1 ∧
          KsLinkClaims (Pk + 4) r (ks q) (ksYRow (Pk + 4) y2 (main q) (ks q)) (M q) (X q)
            out.2.2) ∧ R q) hist)
      εmax (((P + 4 : ℕ) : ℝ≥0∞) * (L₀ * errE 1) + 0) T :=
  (chPhaseSpec hst hcard P ys hys hys' col
      (fun q ↦ KSRel (Pk + 4) r y2 rows (main q) (ks q) (M q) (X q) ∧ R q) h46 h2 hr0 hrK
      hrL).bind' fun ch ↦
  if hch : ch.1.1.length = P + 4 ∧ ch.1.2.1.length = 25 ∧ ch.2.shift.1.length = P + 4 then
    ((ksPhaseSpec hst hcard Pk r y2 hkr rows hnd hrows main ks M X
        (fun q ↦ (CallerClaims (P + 4) 4 (col q) (chY (P + 4) ys (col q)) ch.1 ∧
          ChLinkClaims (P + 4) (col q) ch.2) ∧ R q) h46 h2 hT hrKL).mono
      (fun _ hd ↦ Doomed.mono hd.2 fun _ ⟨hk, hc, hR⟩ ↦ ⟨hc.1, hc.2, hk, hR⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl).bind' fun kso ↦
    (Spec.ret (ch, kso)).mono
      (fun _ hd ↦ ⟨⟨hch, hd.1⟩, Doomed.mono hd.2 fun _ ⟨hc, hk, hR⟩ ↦ ⟨hk.1, hk.2, hc, hR⟩⟩)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ hd ↦ hch hd.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Lvm.KG
