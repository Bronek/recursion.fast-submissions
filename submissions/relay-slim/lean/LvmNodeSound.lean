-- WP-14c (NodeSound, O10). New for lvm: the contract-level half of `NodeSound`
-- (`LvmCertS.NodeSound`): the witness of an accepted `S` header is in the relation once the chain
-- holds and the left child is accepted; the left child `⟨reassemble tr', tr', σ'⟩` is accepted once
-- its trace is a trace of the schedule, its header passes `V_S`'s native checks, `V_S`'s decision on
-- its stream holds and its signature verifies. The pattern (dispatch on the flag, right leaf through
-- `V_encode`, left child through replay) follows FR's `FRSoundness4Node` assembly
-- (rf-k/submissions/flock-recursive/lean@kk/base); the statements are new.
import LvmCertS
import LvmReplay
import LvmXSpec

/-!
# `NodeSound` from its two halves

**The child** `childS q` of a `C_rec` candidate `q` (O10's `child`) is WP-13a's left child of the
words `wOfCol q` (`Xwit`'s): the trace `tr' = readTraceL (laneOf w)` read off the stream lanes
(lane `u` at word `crecIdx u`), the proof `reassemble pX tr'` (WP-11b-QL's; `= reassembleL tr'` by
`reassemble_readTraceL`), the signature `sigOfF (sigCol w)` of column 17.

* **`accV_right`**: the right `W` leaf `⟨encode (leaf s n), [], σ_leaf⟩` is accepted under
  `leafStmt h n` when `n ≤ chainCap`, `chainEnd s n = h` and `σ_leaf` signs `traceDigest []`.
* **`accV_reassemble`**: `⟨reassemble p tr, tr, σ⟩` is accepted under `c_L` by `V_S p m` when
  `LinkOk p tr` (Q_link), `parseOk p vk c_L (reassemble p tr)` (Q_sig's `ChildOk` with the `PUB`
  header), `decideF p m vk c_L Σ = true` (Q_arith) and `SigOk vk (traceDigest tr) σ` (Q_sig); the
  plan's static facts (`PlanOk`, at most `qVlvm` entries, every query within `queryCap`) are decided.
* **`nodeSound_of`**: `NodeSound VS vk Good child` from the chain (`b = 0, 1`) and the left child's
  acceptance (`b = 1`).
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.ASM Lvm.Replay
open RecursionFast.WitnessSending (encode)

/-! ## The child -/

/-- The words of a `C_rec` candidate (the decoder's `wOut` of its values). -/
def wOfCol (q : LeanVM.Protocol.Column 19) (i : ℕ) : Word := BF64.toBitVec (q.values.getD i 0)

/-- **The left child of the words `w`** (WP-13a's `Xwit` child, with WP-11b-QL's `reassemble`). -/
def childW (w : ℕ → Word) : Signed :=
  ⟨reassemble Lvm.X.pX (Lvm.X.readTraceL (Lvm.X.laneOf w)), Lvm.X.readTraceL (Lvm.X.laneOf w),
    Lvm.X.sigOfF (Lvm.X.sigCol w)⟩

/-- **O10's `child`**: the left child of a `C_rec` candidate. -/
def childS (q : LeanVM.Protocol.Column 19) : Signed := childW (wOfCol q)

/-- `childS` is the left child of WP-13a's node witness (`Xwit_eq_replay`). -/
theorem xwit_childW (π : Proof) (w : ℕ → Word) :
    Lvm.X.Xwit π w = .node (Lvm.X.hdD π 6) (leafStmt (Lvm.X.hdD π 15) (Lvm.X.pw π 14).toNat) (childW w)
      ⟨encode (.leaf (Lvm.X.hdD π 10) (Lvm.X.pw π 14).toNat), [], Lvm.X.sigOfF fun j => Lvm.X.pw π (19 + j)⟩ :=
  Lvm.X.Xwit_eq_replay π w

/-! ## The right leaf -/

/-- **The right `W` leaf is accepted.** -/
theorem accV_right (VS : SProg) (vk : Digest) {s h : Digest} {n : ℕ} (sig : Sig) (hn : n ≤ chainCap)
    (hch : chainEnd s n = h) (hsig : SigOk vk (traceDigest []) sig = true) :
    accV VS vk (leafStmt h n) ⟨encode (.leaf s n), [], sig⟩ = true := by
  have hR : Rel (accV VS vk) (leafStmt h n) (.leaf s n) := ⟨hn, by rw [hch]⟩
  simp only [accV, accWith, SigOkF_eq, traceDigestF_eq, hsig, V_encode VS hR,
    WitnessSending.size_encode_leaf]
  simp [OProg.runSeq, qVlvm]

/-! ## The left child -/

/-- The first byte of a reassembled proof is `'S'`. -/
theorem isS_reassemble (p : Params) (tr : Trace) : isS (reassemble p tr) = true := by
  rfl

/-- **The left child is accepted** (replay, BLUEPRINT §4.6): `V_S` asks exactly its trace and
returns its decision on the stream. -/
theorem accV_reassemble (p : Params) (m : M3) (vk cL : Digest) (tr : Trace) (σ : Sig)
    (hP : PlanOk p) (hq : (plan p).length ≤ qVlvm)
    (hcap : ∀ i < (plan p).length, ((plan p).getD i default).len ≤ queryCap)
    (hpi : piSize p < 2 ^ 64) (hL : LinkOk p tr)
    (hparse : parseOk p vk cL (reassemble p tr) = true)
    (hdec : decideF p m vk cL (traceBytesB tr) = true)
    (hsig : SigOk vk (traceDigest tr) σ = true) :
    accV (VS p m) vk cL ⟨reassemble p tr, tr, σ⟩ = true := by
  have hsize : (reassemble p tr).size = piSize p := by
    simp only [parseOk, Bool.and_eq_true, beq_iff_eq] at hparse
    exact hparse.1.1.1
  have hrun := VS_replay p m vk cL hP tr hL hparse
  rw [hdec] at hrun
  obtain ⟨hn, hG⟩ := hL
  simp only [accV, accWith, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨by rw [hsize]; exact hpi, by rw [hn]; exact hq⟩, fun e he => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hGi := (hG i hi).1
    have hq1 : (qOf tr i) = tr[i].1 := by
      simp [qOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rw [← hq1, hGi]
    exact hcap i (hn ▸ hi)
  · rw [SigOkF_eq, traceDigestF_eq]; exact hsig
  · rw [V_S _ _ _ _ (isS_reassemble p tr)]; exact hrun

/-! ## `NodeSound` -/

/-- **`NodeSound` from its halves**: the chain for both flags, and the left child's acceptance for
`b = 1`. -/
theorem nodeSound_of {VS : SProg} {vk : Digest} {Good : GoodRel}
    {child : LeanVM.Protocol.Column 19 → Signed}
    (hchain : ∀ c x qm qr, okS vk c x = true → Good x qm qr →
      chainEnd (hdrOf x).s (hdrOf x).n = (hdrOf x).h)
    (hleft : ∀ c x qm qr, okS vk c x = true → (hdrOf x).b = 1 → Good x qm qr →
      accV VS vk (hdrOf x).cL (child qr) = true) :
    NodeSound VS vk Good child := by
  intro c x qm qr hok hG
  have hch := hchain c x qm qr hok hG
  have hl := fun h1 => hleft c x qm qr hok h1 hG
  have hok' := hok
  unfold okS at hok'
  unfold witOf
  generalize hdrOf x = hd at hok' hch hl ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok'
  obtain ⟨⟨⟨⟨hb, -⟩, -⟩, hnc⟩, hrest⟩ := hok'
  by_cases h0 : hd.b = 0
  · simp only [h0, if_true, decide_eq_true_eq] at hrest ⊢
    exact ⟨hnc, by rw [hrest, hch]⟩
  · have h1 : hd.b = 1 := hb.resolve_left h0
    simp only [h0, if_false, Bool.and_eq_true, decide_eq_true_eq] at hrest ⊢
    exact ⟨hrest.1, hl h1, accV_right VS vk _ hnc hch hrest.2⟩

end Lvm.NS
