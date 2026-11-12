-- WP-14c (NodeSound, O10), helper H1. New for lvm: the header bridge `HdrBridge`
-- (`LvmNodeSoundLeft`): Q_sig's `ChildOk` on the stream's header lanes, with the `PUB` cells, is
-- `V_S`'s native `parseOk` on the reassembled child. Byte/lane conversions reuse WP-11b-QL's
-- `LvmQLinkBridge`/`LvmQLinkSound` (`bl_qOf`, `bOff_one`, `byte_of_lane`, `u64At_eq`) and the
-- Library's `ofLE_enc64`.
import LvmNodeSoundLeft

/-!
# The header bridge

`π' = reassemble P20 (decode P20 ws)` is `'S' 0^7 ‖` the entries' contributions; the seed's
contribution is its query from byte `32`, i.e. the stream's bytes from `88` (lane `11`). So π's
header byte `8 + j` is stream byte `88 + j` (`reassemble_byte`), π's header lane `k` is stream lane
`11 + k`, which `hhd` says is Q_sig's cell `I.hd + k`. Its size is `piSize P20` on every trace of
the schedule: the contributions' lengths are static (`clen`, decided with the node lengths `64`).

**`hdrBridge : HdrBridge`**.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.T Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig Lvm.Wots Lvm.Bits

/-! ## The size of a reassembled trace of the schedule -/

/-- The length of an entry's contribution, statically (node queries are 64 bytes). -/
def clen (e : PE) : ℕ :=
  match e.k with
  | .q0 => 0
  | .leaf => e.len
  | _ => e.len - 32

/-- A node entry's query is 64 bytes. -/
def nodeLenOk (e : PE) : Bool :=
  match e.k with
  | .node .. => e.len == 64
  | _ => true

/-- **The static facts at P20**: node queries of 64 bytes, and `8 + Σ clen = piSize` (the plan's
one-pass decision, `LvmPlanP20`). -/
theorem plan_static_P20 :
    ((plan P20).all nodeLenOk && (8 + ((plan P20).map clen).sum == 783192)) = true := by
  have hc : clen = Lvm.PlanChk.clenC := by
    funext e
    rcases e with ⟨k, len⟩
    cases k <;> rfl
  have hn : (plan P20).all nodeLenOk = true := List.all_eq_true.mpr fun e he => by
    rcases e with ⟨k, len⟩
    cases k with
    | node pe h j lvl cap =>
      simp only [nodeLenOk, beq_iff_eq]
      exact Lvm.PlanChk.node_P20 _ he pe h j lvl cap rfl
    | _ => rfl
  rw [hn, hc, Lvm.PlanChk.clen_P20]
  rfl

theorem contrib_length {tr : Trace} {i : ℕ} {e : PE} (hG : Good tr i e) (hn : nodeLenOk e = true) :
    (contrib tr i e).length = clen e := by
  obtain ⟨hs, -⟩ := hG
  rcases e with ⟨k, len⟩
  cases k with
  | q0 => rfl
  | fs st => simp [contrib, clen, List.length_drop, ← size_bl, hs]
  | leaf => simp [contrib, clen, ← size_bl, hs]
  | node pe h j lvl cap =>
    simp only [nodeLenOk, beq_iff_eq] at hn
    simp only [contrib, clen]
    split <;> simp [List.length_drop, List.length_take, ← size_bl, hs, hn]

theorem sum_range_getD (P : List PE) (f : PE → ℕ) :
    ((List.range P.length).map fun k => f (P.getD k default)).sum = (P.map f).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem bodyFrom_length {p : Params} {tr : Trace} (hL : LinkOk p tr)
    (hn : ∀ e ∈ plan p, nodeLenOk e = true) :
    (bodyFrom tr (plan p) 0).length = ((plan p).map clen).sum := by
  obtain ⟨hlen, hG⟩ := hL
  rw [bodyFrom, List.length_flatMap, Nat.sub_zero, ← List.range_eq_range', ← sum_range_getD]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.mp hk
  refine contrib_length (hG k (by rw [hlen]; exact hk')) (hn _ ?_)
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']

theorem size_reassemble_P20 {tr : Trace} (hL : LinkOk P20 tr) :
    (reassemble P20 tr).size = piSize P20 := by
  have hs := plan_static_P20
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hs
  rw [size_bl, bl_reassemble, List.length_append, bodyFrom_length hL hs.1, sizes_P20.1, ← hs.2,
    show hdr8.length = 8 from rfl]

/-! ## The header bytes are the stream's -/

section Bytes

variable {ws : List Word}

theorem plan_one_len : ((plan P20).getD 1 default).len = 5648 := rfl

theorem two_le_plan : 2 ≤ (plan P20).length := plan_length_ge P20

/-- **π's header byte `8 + j` is stream byte `88 + j`.** -/
theorem reassemble_byte (hsz : hashedLen P20 ≤ 8 * ws.length) {j : ℕ} (hj : j < 5616) :
    (reassemble P20 (decode P20 ws)).get! (8 + j) = (wordsBytes ws).getD (88 + j) 0 := by
  have hW : 5704 ≤ (wordsBytes ws).length := by
    rw [wordsBytes_length]; rw [sizes_P20.2.2.2.2.2.1] at hsz; omega
  have h2 := two_le_plan
  have hb : bodyFrom (decode P20 ws) (plan P20) 0 =
      [] ++ ((bl (qOf (decode P20 ws) 1)).drop 32 ++ bodyFrom (decode P20 ws) (plan P20) 2) := by
    rw [bodyFrom_cons _ _ (i := 0) (by omega), bodyFrom_cons _ _ (i := 1) (by omega)]; rfl
  have hq : bl (qOf (decode P20 ws) 1) = ((wordsBytes ws).drop 56).take 5648 := by
    rw [bl_qOf P20 ws (by omega), plan_one_len, bOff_one]
  rw [get!_bl, bl_reassemble, hb, List.nil_append, hq, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp [hdr8]), show 8 + j - hdr8.length = j by simp [hdr8],
    List.getElem?_append_left (by simp; omega), List.getElem?_drop, List.getElem?_take,
    if_pos (by omega), List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    show 56 + (32 + j) = 88 + j by omega]

/-- Byte `t` of π's header lane `k` is byte `t` of stream lane `11 + k`. -/
theorem reassemble_lane (hsz : hashedLen P20 ≤ 8 * ws.length) {k t : ℕ} (hk : k < 615) (ht : t < 8) :
    (reassemble P20 (decode P20 ws)).get! (8 + 8 * k + t) = byteW (laneK ws (11 + k)).val t := by
  rw [Nat.add_assoc, reassemble_byte hsz (by omega), show 88 + (8 * k + t) = 8 * (11 + k) + t by omega,
    byte_of_lane ws _ _ ht, byteW_toNat _ ht, laneK_val, RecursionFast.toUInt8_mod]

end Bytes

/-! ## Header fields from lanes -/

section Fields

variable {π : ByteArray} {V : ℕ → UInt64}

theorem u64At_of (hB : ∀ k < 615, ∀ t < 8, π.get! (8 + 8 * k + t) = byteW (V k) t) {k : ℕ} (hk : k < 615) :
    u64At π (8 + 8 * k) = (V k).toNat := by
  rw [u64At_eq]
  have e : (List.range 8).map (fun i => π.get! (8 + 8 * k + i)) = enc64 (V k).toNat := by
    refine List.ext_getElem (by simp [enc64]) fun i h1 _ => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, hB k hk i h1, byteW_toNat _ h1]
    simp only [enc64, List.getElem_ofFn]
  rw [e, ofLE_enc64, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]

theorem digestAt_of (hB : ∀ k < 615, ∀ t < 8, π.get! (8 + 8 * k + t) = byteW (V k) t) {k : ℕ}
    (hk : k + 4 ≤ 615) : digestAt π (8 + 8 * k) = digOfW fun l => V (k + l) := by
  refine Vector.ext fun i hi => ?_
  rw [digOfW_get _ hi]
  simp only [digestAt, Vector.getElem_ofFn]
  rw [show 8 + 8 * k + i = 8 + 8 * (k + i / 8) + i % 8 by omega, hB _ (by omega) _ (Nat.mod_lt _ (by omega))]

theorem zeroBytes_of {b : ByteArray} : ∀ {o n : ℕ}, (∀ i < n, b.get! (o + i) = 0) → zeroBytes b o n = true
  | _, 0, _ => rfl
  | o, n + 1, h => by
    simp only [zeroBytes, Bool.and_eq_true, beq_iff_eq]
    exact ⟨by simpa using h 0 (by omega), zeroBytes_of fun i hi => by
      rw [show o + 1 + i = o + (i + 1) by omega]; exact h (i + 1) (by omega)⟩

end Fields

/-! ## The bridge -/

theorem byteW_zero (t : ℕ) : byteW 0 t = 0 := by simp [byteW]

theorem reassemble_get0 (p : Params) (tr : Trace) : (reassemble p tr).get! 0 = 0x53 := by
  rw [get!_bl, bl_reassemble]; rfl

theorem reassemble_get_hdr (p : Params) (tr : Trace) {i : ℕ} (h1 : 1 ≤ i) (h8 : i < 8) :
    (reassemble p tr).get! i = 0 := by
  rw [get!_bl, bl_reassemble, List.getD_append _ _ _ _ (by simp [hdr8]; omega)]
  interval_cases i <;> rfl

theorem digAt_congr {v : ℕ → FK} {a b : ℕ} (h : ∀ l < 4, v (a + l) = v (b + l)) :
    digAt v a = digAt v b := by
  simp only [digAt]
  refine Vector.ext fun i hi => ?_
  rw [digOfW_get _ hi, digOfW_get _ hi, h _ (by omega)]

/-- **`parseOk` from the header lanes** (any proof `π` of the right size and prefix whose header
lane `k` is the cell `I.hd + k`). -/
theorem parseOk_of_lanes {π : ByteArray} {M : Mem} {I : SigIn} {vk cL : RecursionFast.Digest} {σl : Sig}
    (hsize : π.size = piSize P20) (h0 : π.get! 0 = 0x53) (hz : ∀ i, 1 ≤ i → i < 8 → π.get! i = 0)
    (hB : ∀ k < 615, ∀ t < 8, π.get! (8 + 8 * k + t) = byteW (M.k (I.hd + k)).val t)
    (hchild : ChildOk I M.k) (hln : I.ln = 20) (hvk : digAt M.k I.vk = vk) (hcL : digAt M.k I.cL = cL)
    (hsl : sigAt' M.k I.sl = σl) (hσl : SigOk vk (traceDigest []) σl = true) :
    parseOk P20 vk cL π = true := by
  have hdig : ∀ k, k + 4 ≤ 615 → digestAt π (8 + 8 * k) = digAt M.k (I.hd + k) := by
    intro k hk
    rw [digestAt_of hB hk, digAt]
    congr 1; funext l; rw [Nat.add_assoc]
  have hu : ∀ k < 615, u64At π (8 + 8 * k) = (M.k (I.hd + k)).val.toNat := fun k hk => u64At_of hB hk
  have hsig : sigAt π offSig = sigAt' M.k (I.hd + 18) := by
    simp only [sigAt, sigAt', offSig]
    rw [Sig.mk.injEq]
    refine ⟨hu 18 (by omega), ?_, ?_⟩
    · refine List.map_congr_left fun j hj => ?_
      have hj' := List.mem_range.mp hj
      simp only [wotsLen] at hj'
      rw [show 152 + 8 + 32 * j = 8 + 8 * (19 + 4 * j) by omega, hdig _ (by omega)]
      congr 1; omega
    · refine List.map_congr_left fun j hj => ?_
      have hj' := List.mem_range.mp hj
      simp only [sigHeight] at hj'
      rw [show 152 + 8 + 32 * wotsLen + 32 * j = 8 + 8 * (551 + 4 * j) by simp only [wotsLen]; omega,
        hdig _ (by omega)]
      congr 1; omega
  have hH : Header.ofProof π = ⟨(M.k I.hd).val.toNat, digAt M.k (I.hd + 1), digAt M.k (I.hd + 5),
      digAt M.k (I.hd + 9), (M.k (I.hd + 13)).val.toNat, digAt M.k (I.hd + 14),
      sigAt' M.k (I.hd + 18)⟩ := by
    simp only [Header.ofProof]
    rw [show offB = 8 + 8 * 0 from rfl, hu 0 (by omega), show offVk = 8 + 8 * 1 from rfl, hdig 1 (by omega),
      show offCL = 8 + 8 * 5 from rfl, hdig 5 (by omega), show offS = 8 + 8 * 9 from rfl, hdig 9 (by omega),
      show offN = 8 + 8 * 13 from rfl, hu 13 (by omega), show offH = 8 + 8 * 14 from rfl,
      hdig 14 (by omega), hsig, Nat.add_zero]
  have hz17 : zeroBytes π 1 7 = true := zeroBytes_of fun i hi => hz _ (by omega) (by omega)
  obtain ⟨hb, hvk', hn1, hnL, h0c, h1c, hst⟩ := hchild
  rw [hln] at hnL
  simp only [parseOk, hsize, hH, h0, hz17, Header.stmt, Header.leaf, leafStmtF_eq,
    nodeStmtF_eq, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  rw [← hcL, hst]
  refine ⟨⟨⟨⟨⟨hb, hvk'.trans hvk⟩, hn1⟩, hnL⟩, hnL⟩, ?_⟩
  rcases hb with hb | hb
  · obtain ⟨hz5, hzl⟩ := h0c hb
    have zb : zeroBytes π offSig sigBytes = true := zeroBytes_of fun i hi => by
      simp only [sigBytes] at hi
      rw [show offSig + i = 8 + 8 * (18 + i / 8) + i % 8 by simp only [offSig]; omega,
        hB _ (by omega) _ (Nat.mod_lt _ (by omega)), show I.hd + (18 + i / 8) = I.hd + 18 + i / 8 by omega,
        hzl _ (by omega)]
      exact byteW_zero _
    simp only [hb, ↓reduceIte, hz5, zb, Bool.and_eq_true, beq_iff_eq, and_true]
    rfl
  · have hl := h1c hb
    have hs : sigAt' M.k (I.hd + 18) = sigAt' M.k I.sl := by
      simp only [sigAt']
      rw [Sig.mk.injEq]
      have h00 := hl 0 (by omega)
      simp only [Nat.add_zero] at h00
      refine ⟨by rw [h00], ?_, ?_⟩
      · refine List.map_congr_left fun j hj => digAt_congr fun l hl4 => ?_
        have hj' := List.mem_range.mp hj
        simp only [wotsLen] at hj'
        rw [show I.hd + 18 + 1 + 4 * j + l = I.hd + 18 + (1 + 4 * j + l) by omega,
          show I.sl + 1 + 4 * j + l = I.sl + (1 + 4 * j + l) by omega]
        exact hl _ (by omega)
      · refine List.map_congr_left fun j hj => digAt_congr fun l hl4 => ?_
        have hj' := List.mem_range.mp hj
        simp only [sigHeight] at hj'
        rw [show I.hd + 18 + 533 + 4 * j + l = I.hd + 18 + (533 + 4 * j + l) by omega,
          show I.sl + 533 + 4 * j + l = I.sl + (533 + 4 * j + l) by omega]
        exact hl _ (by omega)
    simp only [hb, one_ne_zero, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, true_and, hs, hsl,
      SigOkF_eq, traceDigestF_eq, hσl]

/-- **The header bridge.** -/
theorem hdrBridge : HdrBridge := by
  intro M I ws vk cL σl hlink hsz hhd hchild hln hvk hcL hsl hσl
  refine parseOk_of_lanes (size_reassemble_P20 hlink) (reassemble_get0 _ _)
    (fun i h1 h8 => reassemble_get_hdr _ _ h1 h8) (fun k hk t ht => ?_) hchild hln hvk hcL hsl hσl
  rw [reassemble_lane hsz hk ht, hhd k hk]

end Lvm.NS
