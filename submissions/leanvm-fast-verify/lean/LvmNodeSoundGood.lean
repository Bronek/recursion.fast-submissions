-- WP-14c (NodeSound, O10). New for lvm: the good candidate pair `GoodN` (agreed with WP-14 for O6:
-- `Good := GoodN`) and its chain half (`chain_of_goodN`, from WP-8's `chain_of_CHRel`).
import LvmNodeSound
import LvmM3MidCert
import LvmKeccakCallerPhases

/-!
# The good candidate pair

**`GoodN T hτ x (qm, qr)`** = `Gb ∧ Gk` (the shape of WP-14's O6 glue `midSpecOf`):

* `Gb`: the M3 instance of the statement's tables `T x` holds on the stack of the pair
  (WP-9b `midBusTableSpecS`'s precondition: `M3Holds (inst lay26 (T x) _) () (stackOf lay26 qm qr)`;
  O6 takes `T x := sumcheckTabs (tabs (pubX x))`);
* `Gk`: `CH`'s relation on its block (`CHRel 20 52`), `KS`'s (`KSRel 15 14 y2 (contRows P20)`), and
  the chain's boundary claims `Bnd x qm` (`in_0 = Pad43(s)`, `Y_{n−1} = h`, `s, n, h` from the
  header), in `kgSpec`'s argument order.

**The accessors** (V_S's P20 layout, WP-14a `LvmVEqMid`: `chBlk = ⟨26, 0⟩`, `ksBlk = ⟨21, 50·2^20⟩`,
`ksY2Off = 56·2^20`, `xOff = 56·2^20 + 2^19`; the stream columns `M_l` at `C_rec` words
`l·2^14 + i`): `colM qm` (the `CH` block is all of `C_main`), `ksCol qm`, `msgM qr i l`, `msgX qm i l`.

**`chain_of_goodN`**: a header that `okS` accepts and a good pair give `chainEnd s n = h`.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.ASM Lvm.M3 Lvm.KG LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakGkr

/-! ## The accessors -/

/-- Word `i` of a committed column (`0` past it). -/
def wd {n : ℕ} (q : Column n) (i : ℕ) : K := q.values.getD i 0

/-- `CH`'s block: all of `C_main` (64 slots of `2^20` rows). -/
def colM (qm : Column 26) : ℕ → K := wd qm

/-- `KS`'s block: `C_main` words from `50·2^20`. -/
def ksCol (qm : Column 26) (i : ℕ) : K := wd qm (50 * 2 ^ 20 + i)

/-- `KS`'s output lanes `14 … 24`: `C_main` from `56·2^20`. -/
def ksY2 : ℕ := 56 * 2 ^ 20

/-- The stream's message lanes (`KS` rows `< 2^14`): `C_rec` column `l`, row `i`. -/
def msgM (qr : Column 19) (i l : ℕ) : K := wd qr (l * 2 ^ 14 + i)

/-- The `X` message lanes (`KS` rows `≥ 2^14`): `C_main` from `56·2^20 + 2^19`, column `l`, row `i`. -/
def msgX (qm : Column 26) (i l : ℕ) : K := wd qm (ksY2 + 2 ^ 19 + l * 2 ^ 14 + i)

/-! ## The good pair -/

/-- **The chain's boundary claims** (V_S's `chFixedClaims`, in `chain_of_CHRel`'s form). -/
def Bnd (x : List UInt8) (qm : Column 26) : Prop :=
  inState 20 (colM qm) 0 0 = pad43St (digestBits (hdrOf x).s) ∧
  ∀ m < 4, colM qm ((hdrOf x).n - 1 + 2 ^ 20 * (52 + m)) =
    K.ofLane (RecursionFast.Keccak.blockLane (hdrOf x).h.toArray m)

/-- **The Keccak half** of a good pair (`kgSpec`'s relations, then the boundary claims). -/
def GoodK (x : List UInt8) (p : Column 26 × Column 19) : Prop :=
  CHRel 20 52 (colM p.1) ∧
  KSRel 15 14 ksY2 (contRows P20) (colM p.1) (ksCol p.1) (msgM p.2) (msgX p.1) ∧ Bnd x p.1

/-- **The bus/table half** of a good pair (WP-9b `midBusTableSpecS`'s precondition). -/
def GoodB (T : List UInt8 → List Tab) (hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ) (x : List UInt8)
    (p : Column 26 × Column 19) : Prop :=
  M3Holds (inst lay26 (T x) (hτ x)) () (stackOf lay26 p.1 p.2)

/-- **The good candidate pair** (O6's `Good`, O10's hypothesis). -/
def GoodN (T : List UInt8 → List Tab) (hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ) : GoodRel :=
  fun x qm qr ↦ GoodB T hτ x (qm, qr) ∧ GoodK x (qm, qr)

/-! ## The chain -/

/-- `okS`'s length bounds. -/
theorem okS_n {vk c : RecursionFast.Digest} {x : List UInt8} (hok : okS vk c x = true) :
    1 ≤ (hdrOf x).n ∧ (hdrOf x).n ≤ 2 ^ 20 := by
  unfold okS at hok
  generalize hdrOf x = hd at hok ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  exact ⟨hok.1.1.2, hok.1.2⟩

/-- **The chain of a good pair** (WP-8 `chain_of_CHRel`). -/
theorem chain_of_goodK {vk c : RecursionFast.Digest} {x : List UInt8} {p : Column 26 × Column 19}
    (hok : okS vk c x = true) (hG : GoodK x p) :
    chainEnd (hdrOf x).s (hdrOf x).n = (hdrOf x).h :=
  chain_of_CHRel (okS_n hok).1 (okS_n hok).2 hG.1 hG.2.2.1 hG.2.2.2

/-- The chain half of `NodeSound` for `GoodN`. -/
theorem chain_of_goodN {T : List UInt8 → List Tab} {hτ : ∀ x, ∀ t ∈ T x, t.τ ≤ lay26.μ}
    {vk c : RecursionFast.Digest} {x : List UInt8} {qm : Column 26} {qr : Column 19}
    (hok : okS vk c x = true) (hG : GoodN T hτ x qm qr) :
    chainEnd (hdrOf x).s (hdrOf x).n = (hdrOf x).h :=
  chain_of_goodK hok hG.2

end Lvm.NS
