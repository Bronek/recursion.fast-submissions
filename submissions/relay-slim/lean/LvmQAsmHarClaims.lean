-- New for lvm (HAR): phase 8–9's claim list as cells, in `decideProg`'s order (`claimsOf`): the table
-- claims, the Keccak and fixed claims of `CH`, the Keccak claims of `KS`, the `CH` link's, `KS`'s outputs,
-- the `KS` link's.
import LvmQAsmHarBase

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop

/-- **The claims as cells** in `claimsOf`'s order (lvm2 S2; `bus.claims = []` for the lvm instance). -/
def claimsC (tabCs tapeCs ksCs ksOut clK : List CClaim) : List CClaim :=
  tabCs ++ (tapeCs ++ ksCs) ++ ksOut ++ clK

/-- **The cells' claims are `F`'s** given each part's equation. -/
theorem claimsC_val (M : Mem) (p : Params) (m : M3) (pub : Pub) (bus : BusOut)
    (evals : List (List FE × List FE)) (tp : TapeRes) (wo : WireOut) (rk vks : List FE) (kko : KeccakOut)
    (kring : FE × (List FE → FE)) (kLinkClaims : List (Com × BlockClaim)) {tabCs tapeCs ksCs ksOut clK : List CClaim}
    (hbus : bus.claims = []) (htab : tabCs.map (CClaim.val M) = m.tableClaims pub evals)
    (htape : tapeCs.map (CClaim.val M) = (tapeClaims p tp wo pub).map (.main, ·))
    (hks : ksCs.map (CClaim.val M) = (keccakClaims m.ksBlock kko kring).map (.main, ·))
    (hko : ksOut.map (CClaim.val M) = m.ksOutputClaims rk vks)
    (hkl : clK.map (CClaim.val M) = kLinkClaims) :
    (claimsC tabCs tapeCs ksCs ksOut clK).map (CClaim.val M) =
      claimsOf p m pub bus evals tp wo rk vks kko kring kLinkClaims := by
  simp only [claimsC, claimsOf, List.map_append, htab, htape, hks, hko, hkl, hbus, List.nil_append]

end Lvm.Har
