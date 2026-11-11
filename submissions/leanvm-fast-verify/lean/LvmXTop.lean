-- New for lvm (WP-13a), after FR's `FRXDec4F0` (`ext4IRWith`, `DecOk4`, `computes4`, `E4X`) and
-- `FRXSpec` (`E`, `Eout`, `InDomE`; rf-k/submissions/flock-recursive/lean@kk/base): lvm's SNARK branch,
-- the extractor program `extX`, its specification `EX` and `Computes`.
import LvmXNodeIR
import LvmXSearch
import LvmXDecCost
import LvmXRead2

/-!
# The extractor program and `Computes` (BLUEPRINT §6.2, §6.3)

`extX = extWith piSize decX` (`LvmXComputes`: `'S'` and `|π| = piSize` → `decX`, `'S'` and another size
→ nothing, else the `W` copy). The SNARK branch `decX` reads the flag `b` (π word 1):

* `b = 0`: `leafIR` outputs `witWords (leaf s n)` (π words 10–14);
* `b ≠ 0`: `nodeIR`: the log index (`idxIR4`, WP-3), the chain scan (`chainL`), the column reads of
  `C_rec` (`readIR`, WP-13b), `α` and `f₁` copied to the decoder's inputs, the decoder (`decIR`,
  WP-13b), and if it succeeded the node output (`outIR`).

Heap layout (all below `memX = 2^25`): the decoder's (`decLay_example`: `aB = 2^19`, `fB = aB + 64`,
`wB = 2^20`, `dB = 2^22`, message at `dB + 2^20`), the chain's at `2^24`, the stream buffer at
`2^24 + 2^16`; the log index at `memX`.

**`decOk_decX`**, **`computesX`**: `Computes extX (EX A) fuel` with the declared fuel
`fuel t = 2^46 + 2^13 t` (`LvmXComputes.fuel`); `extX_caps`: within the budget and `progCap`.
-/

namespace Lvm.X

open RecursionFast Lvm

/-! ## Layout -/

/-- The log's tape word on an `S` proof. -/
def pLX : ℕ := posL (piSize pX)
/-- The decoder's workspace. -/
def dBX : ℕ := 2 ^ 22
/-- The read word. -/
def wBX : ℕ := 2 ^ 20
/-- `α`. -/
def aBX : ℕ := 2 ^ 19
/-- `f₁`. -/
def fBX : ℕ := 2 ^ 19 + 64
/-- The tape word of `C_rec`'s cap. -/
def capWX : ℕ := 5 + capRecOff pX / 8
/-- The tape word of `f₁`. -/
def f1WX : ℕ := 5 + f1Off pX / 8

theorem layoutX : pLX = 147529 ∧ capWX = 1732 ∧ f1WX = 26271 ∧ f1Off pX % 8 = 0 ∧
    alphaPos pX 0 = 1035 := by
  refine ⟨?_, ?_, ?_, ?_, layout_P20.2.2.1⟩
  · rw [pLX, piSize_eq]; rfl
  · rw [capWX, layout_P20.2.2.2.2.1]
  · rw [f1WX, layout_P20.2.2.2.1]
  · rw [layout_P20.2.2.2.1]

/-! ## The SNARK branch -/

/-- The flag register. -/
def rBb : ℕ := 130

/-- **The leaf output**: tag `0`, the chain start (π words 10–13), the length (π word 14). -/
def leafIR : XIR := .seq (emitIR (toWord 0)) (tcpIR 15 5)

/-- `α_j` (answer words 0–2 of chain position `alphaPos j`) to `aB + 3j`. -/
def acpIR : XIR :=
  .seq (mcpIR 3 (ansB + 4 * alphaPos pX 0) 1 aBX) (.seq (mcpIR 3 (ansB + 4 * alphaPos pX 1) 1 (aBX + 3))
  (.seq (mcpIR 3 (ansB + 4 * alphaPos pX 2) 1 (aBX + 6)) (.seq (mcpIR 3 (ansB + 4 * alphaPos pX 3) 1 (aBX + 9))
  (.seq (mcpIR 3 (ansB + 4 * alphaPos pX 4) 1 (aBX + 12)) (mcpIR 3 (ansB + 4 * alphaPos pX 5) 1 (aBX + 15))))))

/-- After the decoder: the node output if it succeeded. -/
def okXIR : XIR :=
  .seq (.blk [.const eA (toWord (okB dBX))]) (.seq (.load eW eA) (.ite eW (outIR (mB dBX)) (.blk [])))

/-- **The node branch.** -/
def nodeIR : XIR :=
  .seq (idxIR4 memX pLX) (.seq chainL (.seq (readIR memX pLX capWX wBX) (.seq acpIR
    (.seq (thcpIR f1WX fBX (3 * 2 ^ 13)) (.seq (decIR dBX wBX aBX fBX) okXIR)))))

/-- **The SNARK branch**: by the flag `b` (tape word 6). -/
def decX : XIR := .seq (readAt rBb 6) (.ite rBb nodeIR leafIR)

/-- **The extractor program.** -/
def extX : XProg := extWith (piSize pX) decX

/-! ## Well formed, no `loopT` but the index's and the chain's, output, size, cost -/

theorem wf_leafIR : WF leafIR := ⟨wf_emitIR _, wf_tcpIR _ _⟩

theorem wf_acpIR : WF acpIR := by
  simp only [acpIR, WF]; exact ⟨wf_mcpIR .., wf_mcpIR .., wf_mcpIR .., wf_mcpIR .., wf_mcpIR .., wf_mcpIR ..⟩

theorem wf_outIR (m : ℕ) : WF (outIR m) := by
  simp only [outIR, WF]
  refine ⟨wf_emitIR _, wf_tcpIR _ _, wf_leafStmtIR _ _, wf_emitIR _, wf_copyIR _, ?_, wf_segIR _ _ _ (by
    have := segs_ok.2.2.2; omega), wf_segIR _ _ _ (by have := segs_ok.2.1; omega), ?_,
    wf_segIR _ _ _ (by decide), wf_emitIR _, wf_emitIR _, wf_tcpIR _ _, wf_emitIR _, wf_tcpIR _ _⟩ <;>
  simp +decide [setR, WF, Prim.dst, oR, oKF, oBd]

theorem wf_okXIR : WF okXIR := by
  refine ⟨by simp +decide [WF, Prim.dst, eA], show 4 ≤ eW by decide, wf_outIR _, by simp [WF]⟩

theorem wf_nodeIR : WF nodeIR :=
  ⟨wf_idxIR4 _ _, wf_chainIR _ _ _ wf_sdL (nw_sdL _ (by decide) (by decide) (by decide)),
    wf_readIR _ _ _ _, wf_acpIR, wf_thcpIR _ _ _, wf_decIR _ _ _ _, wf_okXIR⟩

theorem wf_decX : WF decX := by
  refine ⟨?_, wf_nodeIR, wf_leafIR⟩
  simp +decide [readAt, WF, Prim.dst, rA, rBb]

theorem noLoopT_tcpIR (a n : ℕ) : NoLoopT (tcpIR a n) := by simp [tcpIR, tcpBody, NoLoopT]
theorem noLoopT_emitIR (w : Word) : NoLoopT (emitIR w) := by simp [emitIR, NoLoopT]
theorem noLoopT_copyIR (m : ℕ) : NoLoopT (copyIR m) := by simp [copyIR, copyBody, NoLoopT]
theorem noLoopT_thcpIR (a d n : ℕ) : NoLoopT (thcpIR a d n) := by simp [thcpIR, thcpBody, NoLoopT]
theorem noLoopT_setR (R : ℕ) : NoLoopT (setR R) := trivial

theorem noLoopT_outIR (m : ℕ) : NoLoopT (outIR m) :=
  ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _, noLoopT_leafStmtIR _ _, noLoopT_emitIR _, noLoopT_copyIR _,
    noLoopT_setR _, noLoopT_segIR _ _ _, noLoopT_segIR _ _ _, noLoopT_setR _, noLoopT_segIR _ _ _,
    noLoopT_emitIR _, noLoopT_emitIR _, noLoopT_tcpIR _ _, noLoopT_emitIR _, noLoopT_tcpIR _ _⟩

theorem noLoopT_acpIR : NoLoopT acpIR :=
  ⟨noLoopT_mcpIR .., noLoopT_mcpIR .., noLoopT_mcpIR .., noLoopT_mcpIR .., noLoopT_mcpIR ..,
    noLoopT_mcpIR ..⟩

theorem noLoopT_okXIR : NoLoopT okXIR := ⟨trivial, trivial, noLoopT_outIR _, trivial⟩

theorem noLoopT_sdL : NoLoopT sdL := ⟨trivial, trivial⟩

/-- **The SNARK branch's loop bounds** on every domain tape of an `S` proof. -/
theorem safe_decX (c : Digest) (π : Proof) (L : Log) (hs : π.size = piSize pX)
    (hq : ∀ e ∈ L, e.1.size < 2 ^ 64) (ht : (extractorInput c π L).length ≤ 2 ^ 64) :
    Safe (extractorInput c π L).toArray (extractorInput c π L).length decX := by
  have hpz : piSize pX < 2 ^ 64 := by rw [piSize_eq]; norm_num
  refine .seq (safe_of_noLoopT (by simp [readAt, NoLoopT])) (.ite ?_ (safe_of_noLoopT
    ⟨noLoopT_emitIR _, noLoopT_tcpIR _ _⟩))
  refine .seq ((decOk_idx hpz).safe c π L hs hq ht) (.seq ?_ (.seq (safe_of_noLoopT (noLoopT_readIR ..))
    (.seq (safe_of_noLoopT noLoopT_acpIR) (.seq (safe_of_noLoopT (noLoopT_thcpIR ..))
      (.seq (safe_of_noLoopT (noLoopT_decIR ..)) (safe_of_noLoopT noLoopT_okXIR))))))
  exact safe_chainIR c π L (hs_posL hs) hq ht _ _ noLoopT_sdL wf_sdL
    (nw_sdL _ (by decide) (by decide) (by decide))

/-! ## Cost -/

theorem cost_tcpIR (a n t : ℕ) (hn : n < 2 ^ 64) : cost (tcpIR a n) t = 12 + n * 8 := by
  simp only [tcpIR, tcpBody, cost, blkSteps, List.length_cons, List.length_nil, toNat_toWord hn]
  norm_num; ring

theorem cost_copyIR (m t : ℕ) : cost (copyIR m) t = 12 + nCp * 31 := by
  simp only [copyIR, copyBody, cpAddrPs, cost, blkSteps, List.length_cons, List.length_nil,
    toNat_toWord (show nCp < 2 ^ 64 by simp only [nCp]; norm_num)]
  norm_num
  omega

/-! The output segments' costs, outputs and sizes, block by block: a block's segment's measures do
not depend on its lane (`segPC_u`, …) and are `LvmXLayout`'s closed forms (`segPC`, …) whose sums
over the blocks `layout_all_P20` decides with the other numbers at `P20` (three decisions on the
segments cost 2–3 s of kernel time each). -/

private theorem segPC (b : Blk) : segCost (blkPSeg 0 b) + 1 = blkPCostL b := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segPO (b : Blk) : segOuts (blkPSeg 0 b) = blkPOutsL b := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segPS (b : Blk) : segSize (blkPSeg 0 b) + 1 = blkPSizeL b := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segTC (b : Blk) : segCost (blkTSeg 0 b) + 1 = blkTCostL b := by
  cases b with
  | one c len => rfl
  | opn t row path => rfl
private theorem segTO (b : Blk) : segOuts (blkTSeg 0 b) = blkTOutsL b := by
  cases b with
  | one c len => rfl
  | opn t row path => rfl
private theorem segTS (b : Blk) : segSize (blkTSeg 0 b) + 1 = blkTSizeL b := by
  cases b with
  | one c len => rfl
  | opn t row path => rfl

private theorem segPC_u (u : ℕ) (b : Blk) : segCost (blkPSeg u b) = segCost (blkPSeg 0 b) := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segPO_u (u : ℕ) (b : Blk) : segOuts (blkPSeg u b) = segOuts (blkPSeg 0 b) := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segPS_u (u : ℕ) (b : Blk) : segSize (blkPSeg u b) = segSize (blkPSeg 0 b) := by
  cases b with
  | one c len => cases c <;> rfl
  | opn t row path => rfl
private theorem segTC_u (u : ℕ) (b : Blk) : segCost (blkTSeg u b) = segCost (blkTSeg 0 b) := by
  cases b <;> rfl
private theorem segTO_u (u : ℕ) (b : Blk) : segOuts (blkTSeg u b) = segOuts (blkTSeg 0 b) := by
  cases b <;> rfl
private theorem segTS_u (u : ℕ) (b : Blk) : segSize (blkTSeg u b) = segSize (blkTSeg 0 b) := by
  cases b <;> rfl

private theorem segPCs : ∀ (u : ℕ) (bs : List Blk), segCost (blkPSegs u bs) = (bs.map blkPCostL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkPSegs, segCost, segPCs _ bs, segPC_u, List.map_cons, List.sum_cons, ← segPC b]; omega
private theorem segPOs : ∀ (u : ℕ) (bs : List Blk), segOuts (blkPSegs u bs) = (bs.map blkPOutsL).sum
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkPSegs, segOuts, segPOs _ bs, segPO_u, List.map_cons, List.sum_cons, ← segPO b]
private theorem segPSs : ∀ (u : ℕ) (bs : List Blk), segSize (blkPSegs u bs) = (bs.map blkPSizeL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkPSegs, segSize, segPSs _ bs, segPS_u, List.map_cons, List.sum_cons, ← segPS b]; omega
private theorem segTCs : ∀ (u : ℕ) (bs : List Blk), segCost (blkTSegs u bs) = (bs.map blkTCostL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkTSegs, segCost, segTCs _ bs, segTC_u, List.map_cons, List.sum_cons, ← segTC b]; omega
private theorem segTOs : ∀ (u : ℕ) (bs : List Blk), segOuts (blkTSegs u bs) = (bs.map blkTOutsL).sum
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkTSegs, segOuts, segTOs _ bs, segTO_u, List.map_cons, List.sum_cons, ← segTO b]
private theorem segTSs : ∀ (u : ℕ) (bs : List Blk), segSize (blkTSegs u bs) = (bs.map blkTSizeL).sum + 1
  | _, [] => rfl
  | u, b :: bs => by
    rw [blkTSegs, segSize, segTSs _ bs, segTS_u, List.map_cons, List.sum_cons, ← segTS b]; omega

private theorem segAll : (segCost pSegL = 8444342 ∧ segCost trSegL = 8877123 ∧
      segCost (.cp 0 597) = 21506) ∧
    (segOuts pSegL = 147524 ∧ segOuts trSegL = 250045 ∧ segOuts (.cp 0 597) = 597) ∧
    (segSize pSegL = 64160 ∧ segSize trSegL = 67390 ∧ segSize (.cp 0 597) = 50) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := layout_all_P20.2.2.2.2.2.2.2
  refine ⟨⟨?_, ?_, rfl⟩, ⟨?_, ?_, rfl⟩, ⟨?_, ?_, rfl⟩⟩
  · rw [pSegL, segCost, segCost, segPCs, h1]
  · rw [trSegL, segCost, segCost, segCost, segCost, segCost, segCost, segCost, segTCs, h2]; rfl
  · rw [pSegL, segOuts, segOuts, segPOs, h3]
  · rw [trSegL, segOuts, segOuts, segOuts, segOuts, segOuts, segOuts, segOuts, segTOs, h4]; rfl
  · rw [pSegL, segSize, segSize, segPSs, h5]
  · rw [trSegL, segSize, segSize, segSize, segSize, segSize, segSize, segSize, segTSs, h6]; rfl

theorem segCosts : segCost pSegL = 8444342 ∧ segCost trSegL = 8877123 ∧ segCost (.cp 0 597) = 21506 :=
  segAll.1

/-- **The node output's cost.** -/
theorem cost_outIR (m t : ℕ) : cost (outIR m) t ≤ 26100000 := by
  have h1 := cost_segIR apC pSegL 0 t
  have h2 := cost_segIR apC trSegL 0 t
  have h3 := cost_segIR apC (.cp 0 597) 0 t
  rw [segCosts.1] at h1; rw [segCosts.2.1] at h2; rw [segCosts.2.2] at h3
  simp only [outIR, cost, emitIR, setR, blkSteps, List.length_cons, List.length_nil,
    cost_tcpIR _ _ t (show 4 < 2 ^ 64 by norm_num), cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num),
    cost_tcpIR _ _ t (show 597 < 2 ^ 64 by norm_num), cost_leafStmtIR, cost_copyIR, nCp]
  norm_num
  omega

theorem cost_acpIR (t : ℕ) : cost acpIR t = 335 := by
  simp only [acpIR, cost, cost_mcpIR _ _ _ _ t (show 3 < 2 ^ 64 by norm_num)]

theorem cost_sdL (t : ℕ) : cost sdL t = 8 := by
  simp only [sdL, cost, blkSteps, List.length_cons, List.length_nil]; norm_num

theorem chTabL_len : chTabL.length = 4168 := by rw [chTabL_length, nChain_eq]

/-- **The SNARK branch's cost**: the fixed `≈ 2^37.95` (decoder) plus `≈ 2,547` steps a word. -/
theorem cost_decX (t : ℕ) : cost decX t ≤ 2 ^ 39 + t / 5 * 11895 + t * 168 := by
  have hO := cost_outIR (mB dBX) t
  have hC := cost_chainIR (posL (piSize pX)) (nChain pX) t chTabL sdL
  rw [chTabL_len, cost_sdL] at hC
  have hR := (cost_readIR memX pLX capWX wBX t).2
  simp only [decX, nodeIR, okXIR, leafIR, readAt, cost, blkSteps, List.length_cons, List.length_nil,
    cost_idxIR4, show chainL = chainIR (posL (piSize pX)) (nChain pX) chTabL sdL from rfl, hC, hR,
    cost_acpIR, cost_thcpIR _ _ _ t (show 3 * 2 ^ 13 < 2 ^ 64 by norm_num), cost_decIR,
    cost_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), emitIR]
  norm_num
  omega

/-! ## Output, size -/

theorem outs_tcpIR (a n t : ℕ) (hn : n < 2 ^ 64) : outs (tcpIR a n) t = n := by
  simp [tcpIR, tcpBody, outs, toNat_toWord hn]

theorem segOutsV : segOuts pSegL = 147524 ∧ segOuts trSegL = 250045 ∧ segOuts (.cp 0 597) = 597 :=
  segAll.2.1

theorem outs_outIR (m t : ℕ) : outs (outIR m) t ≤ 398781 := by
  have h1 := outs_segIR apC pSegL 0 t
  have h2 := outs_segIR apC trSegL 0 t
  have h3 := outs_segIR apC (.cp 0 597) 0 t
  rw [segOutsV.1] at h1; rw [segOutsV.2.1] at h2; rw [segOutsV.2.2] at h3
  simp only [outIR, outs, emitIR, setR, outs_tcpIR _ _ t (show 4 < 2 ^ 64 by norm_num),
    outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), outs_tcpIR _ _ t (show 597 < 2 ^ 64 by norm_num),
    outs_leafStmtIR, copyIR, copyBody, Nat.zero_add, Nat.add_zero]
  simp [outs] at *
  omega

theorem outs_decX (t : ℕ) : outs decX t ≤ outCap := by
  have h := outs_outIR (mB dBX) t
  simp only [decX, nodeIR, okXIR, leafIR, readAt, outs, outs_idxIR4, outs_readIR, outs_decIR,
    emitIR, outs_tcpIR _ _ t (show 5 < 2 ^ 64 by norm_num), show chainL = chainIR (posL (piSize pX))
      (nChain pX) chTabL sdL from rfl, outs_chainIR (posL (piSize pX)) (nChain pX) t chTabL
      (show outs sdL t = 0 by simp [sdL, outs])]
  simp [acpIR, outs_mcpIR, thcpIR, thcpBody, outs, outCap] at *
  omega

theorem segSizes : segSize pSegL = 64160 ∧ segSize trSegL = 67390 ∧ segSize (.cp 0 597) = 50 :=
  segAll.2.2

theorem sizeIR_idxX : sizeIR (idxIR4 memX pLX) = 294 := by decide +kernel

/-! `sizeIR`'s equations as propositional rewrites (not `rfl` lemmas): `simp` rewrites with them by
`congrArg` instead of casting the goal, a cast that made the kernel evaluate `sizeIR decX` (the
chain table included) on both sides (8 s). -/
private theorem szBlk (ps : List Prim) : sizeIR (.blk ps) = blkSteps ps.length := by rw [sizeIR]
private theorem szLoad (d a : ℕ) : sizeIR (.load d a) = 1 := by rw [sizeIR]
private theorem szStore (a s : ℕ) : sizeIR (.store a s) = 5 := by rw [sizeIR]
private theorem szInput (d a : ℕ) : sizeIR (.input d a) = 1 := by rw [sizeIR]
private theorem szOut (s : ℕ) : sizeIR (.out s) = 1 := by rw [sizeIR]
private theorem szSeq (p q : XIR) : sizeIR (.seq p q) = sizeIR p + sizeIR q + 1 := by rw [sizeIR]
private theorem szIte (c : ℕ) (p q : XIR) : sizeIR (.ite c p q) = sizeIR p + sizeIR q + 1 := by
  rw [sizeIR]

theorem sizeIR_decX : sizeIR decX ≤ 2 ^ 19 := by
  simp only [decX, nodeIR, okXIR, leafIR, outIR, readAt, emitIR, setR, acpIR, szBlk, szLoad, szStore,
    szInput, szOut, szSeq, szIte, blkSteps,
    List.length_cons, List.length_nil, sizeIR_idxX, show chainL = chainIR (posL (piSize pX))
      (nChain pX) chTabL sdL from rfl, sizeIR_chainIR, chTabL_len, sizeIR_readIR, sizeIR_decIR,
    sizeIR_leafStmtIR, sizeIR_segIR, segSizes.1, segSizes.2.1, segSizes.2.2]
  simp [tcpIR, tcpBody, copyIR, copyBody, cpAddrPs, thcpIR, thcpBody, mcpIR, mcpLoop, mcpBody, sdL,
    sizeIR, blkSteps]

/-! ## `DecOk` and `Computes` -/

/-- **The SNARK branch meets `DecOk`** (`LvmXComputes`). -/
theorem decOk_decX : DecOk (piSize pX) decX where
  pz_lt := by rw [piSize_eq]; norm_num
  wf := wf_decX
  safe := fun c π L hs hq ht => safe_decX c π L hs hq ht
  cost := fun t => by
    have := cost_decX t
    simp only [decBudget, fuelBase, fuelPerWord]
    omega
  outs := outs_decX
  size := sizeIR_decX

/-! ## The extractor specification and `Computes` -/

/-- **The contract's `Computes` domain** (FR `InDomE`). -/
def InDomE (c : Digest) (π : Proof) (L : Log) : Prop :=
  π.size ≤ 8 * outCap ∧ (∀ e ∈ L, e.1.size < 2 ^ 64) ∧ (extractorInput c π L).length ≤ 2 ^ 64

instance (c : Digest) (π : Proof) (L : Log) : Decidable (InDomE c π L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The in-domain extractor**: the program's decoded denotation (a total computable function). -/
def EdX : Digest → Proof → Log → Option Wit := Eden memX mpwX (extIRWith (piSize pX) decX)

/-- The leaf witness an `S` proof with `b = 0` carries: `(s, n)` from its header. -/
def leafW (π : Proof) : Wit := .leaf (hdD π 10) (pw π 14).toNat

/-- **The extractor outside the domain** (FR B-15): a `W` proof decoded, an `S` leaf's witness, an
`S` node searched under the key it carries (`vk`, π words 2–5), any other `S` nothing. -/
def EoutX (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (_L : Log) : Option Wit :=
  if π.data[0]? = some 0x53 then
    (if π.size = piSize pX then (if pw π 1 = 0 then some (leafW π) else search A (hdD π 2) c) else none)
  else WitnessSending.decode π

/-- **The extractor specification** `E`: `EdX` on the domain, `EoutX A` outside (`A`: the
certificate's `S.acc`). -/
def EX (A : Digest → Digest → Signed → Bool) (c : Digest) (π : Proof) (L : Log) : Option Wit :=
  if InDomE c π L then EdX c π L else EoutX A c π L

/-- **`Computes extX (EX A) fuel`** with the declared fuel `2^46 + 2^13 t`, for every `A`. -/
theorem computesX (A : Digest → Digest → Signed → Bool) : Computes extX (EX A) fuel :=
  fun c π L h1 h2 h3 => by
    obtain ⟨o, ho, hl, hd⟩ := computesWith decOk_decX c π L h1 h2 h3
    exact ⟨o, ho, hl, hd.trans (if_pos ⟨h1, h2, h3⟩).symm⟩

/-- The certificate's caps on the extractor: the fuel within `B`, the program within `progCap`. -/
theorem extX_caps : (∀ t, fuel t ≤ extractorBudget t) ∧ extX.body.size ≤ progCap :=
  ⟨fuel_le_budget, size_extWith decOk_decX.size⟩

end Lvm.X
