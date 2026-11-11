-- WP-14c (NodeSound, O10), helper H3. New for lvm: what `KS` gives `NodeSound`, from a good pair's
-- `KSRel` (WP-8 `spongeRel_of_KSRel`, `traceDigest_of_KS`, `row_perm`, `oneRow_perm`): the trace
-- digest of the child's stream, digest cells, and Q_sig's `SigKSin` (WP-12, A19).
import LvmNodeSoundLeft
import LvmNodeSoundGood
import LvmQLinkMain

/-!
# `KS` for `NodeSound`

`Yq qm` are `KS`'s output lanes (row `i`, lane `l`), `Mq qm qr` its message lanes (`C_rec`'s
stream columns below row `2^14`, `C_main`'s `X` columns above), on a good pair's `C_main`/`C_rec`.

* **`traceDigest_of_goodK`**: with Q_link's `LaneLink` and the stream's padding (`PadOkB`, both
  from `qlink_sound`), row `B − 1` (`B = spongeBlocks P20`) of `KS` outputs the trace digest of
  the child's decoded trace (the stream's lane `17 i + l` is message lane `l` of row `i`).
* **`digAt_of_cells`**: four `K` cells holding a row's output lanes 0–3 read as its digest.
* **`sigKSin_of_goodK`**: with the `X` message cells and the digest cells Q_sig names holding
  `KS`'s values (rows `2^14 + r`: steps `r < 399`, the key leaf `399 … 430`, path `431 … 446`,
  `leafStmt` 447, `nodeStmt` 448), Q_sig's `KS` hypothesis `SigKSin` holds.
-/

set_option autoImplicit false

namespace Lvm.NS

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig Lvm.KG
open LeanVM.Parameters LeanVM.Protocol

/-- `KS`'s output lanes on a good pair's `C_main`. -/
abbrev Yq (qm : Column 26) : ℕ → ℕ → K := ksYRow 15 ksY2 (colM qm) (ksCol qm)

/-- `KS`'s message lanes on a good pair. -/
abbrev Mq (qm : Column 26) (qr : Column 19) : ℕ → ℕ → K := ksMsg 14 (msgM qr) (msgX qm)

/-- The `cont` rows at `P20`: the trace rows `1 … B − 1` and the key leaf's rows `1 … 31`. -/
theorem mem_contRows {i : ℕ} : i ∈ contRows P20 ↔ (1 ≤ i ∧ i < 14709) ∨ (16784 ≤ i ∧ i < 16815) := by
  have hB : spongeBlocks P20 = 14709 := sizes_P20.2.2.2.2.2.2.2.2
  have hr : P20.recRowsLog = 14 := rfl
  simp only [contRows, List.mem_append, List.mem_map, List.mem_range, hB, hr, Nat.reducePow]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> omega
  · rintro (h | h)
    · exact Or.inl ⟨i - 1, by omega, by omega⟩
    · exact Or.inr ⟨i - 16784, by omega, by omega⟩

/-! ## The stream's bytes are `KS`'s message bytes -/

/-- **Byte `p` of the child's stream is byte `p mod 136` of `KS` row `p / 136`** (below row `2^14`). -/
theorem msgBytes_eq_stream (qm : Column 26) (qr : Column 19) {p : ℕ} (hp : p / 136 < 2 ^ 14) :
    Lvm.KG.msgBytes (Mq qm qr) (p / 136) (p % 136) =
      (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).getD p 0 := by
  have hq : p % 136 < 136 := Nat.mod_lt _ (by norm_num)
  have hl : p % 136 / 8 < 17 := by omega
  have hb : p % 136 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have e1 : p = 8 * (17 * (p / 136) + p % 136 / 8) + p % 136 % 8 := by omega
  have hu : 17 * (p / 136) + p % 136 / 8 < 17 * 2 ^ 14 := by omega
  have hc : Lvm.X.crecIdx (17 * (p / 136) + p % 136 / 8) = p % 136 / 8 * 2 ^ 14 + p / 136 := by
    unfold Lvm.X.crecIdx; omega
  conv_rhs => rw [e1]
  rw [byte_of_lane _ _ _ hb, toUInt8_mod]
  simp only [Lvm.KG.msgBytes, Mq, ksMsg, if_pos hp, msgM, wd, lw, wsOf]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu, Option.map_some,
    Option.getD_some, Lvm.X.laneOf, hc, wOfCol]
  exact Lvm.Wots.byteW_toNat _ hb

/-! ## The trace digest -/

/-- QL's padding and `KS`'s are the same function. -/
theorem padAt_eq (L p : ℕ) : Lvm.QLink.padAt L p = Lvm.KSponge.padAt L p := rfl

theorem nBlk_eq (L : ℕ) : Lvm.QLink.nBlk L = Lvm.KSponge.nBlk L := rfl

/-- **QL's static stream facts at `P20`** (QL's decision `Lvm.QLink.streamOk_P20`; WP-16b: decided once). -/
theorem streamOk_P20 : StreamOk P20 := Lvm.QLink.streamOk_P20

/-- **`KS` outputs the child's trace digest** at row `B − 1`. -/
theorem traceDigest_of_goodK {x : List UInt8} {qm : Column 26} {qr : Column 19}
    (hG : GoodK x (qm, qr)) (hL : LaneLink P20 (wsOf (Lvm.X.laneOf (wOfCol qr))))
    (hpad : PadOkB (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))) (hashedLen P20)) :
    Lvm.KSponge.stDigest (yState (Yq qm) (spongeBlocks P20 - 1)) =
      traceDigest (decode P20 (wsOf (Lvm.X.laneOf (wOfCol qr)))) := by
  have H := spongeRel_of_KSRel hG.2.1 (by rw [mem_contRows]; omega)
  have hS := stream_of_laneLink streamOk_P20 hL
  have hsz : hashedLen P20 ≤ (wordsBytes (wsOf (Lvm.X.laneOf (wOfCol qr)))).length := by
    rw [wordsBytes_length]; exact hL.size
  have hhl : hashedLen P20 = 2000352 := sizes_P20.2.2.2.2.2.1
  rw [sizes_P20.2.2.2.2.2.2.2.2]
  generalize hashedLen P20 = L at hS hsz hpad hhl
  have hnb : Lvm.KSponge.nBlk L = 14709 := by rw [hhl]; rfl
  rw [← hnb]
  refine traceDigest_of_KS 15 (ksCol qm) (Yq qm) (Mq qm qr) _ H L (by rw [hnb]; norm_num)
    (fun i h1 h2 => by rw [hnb] at h2; simp only [decide_eq_true_eq, mem_contRows]; omega) ?_ _ ?_
  · intro p h1 h2
    rw [hnb] at h2
    have h2' : p < 136 * 14709 := h2
    have := msgBytes_eq_stream qm qr (p := p) (by omega)
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl, this, ← padAt_eq]
    exact hpad p h1 (by rw [nBlk_eq, hnb]; omega)
  · rw [← hS]
    refine List.ext_getElem (by rw [Lvm.KSponge.streamOf_length, List.length_take]; omega) fun p h1 h2 => ?_
    have hp : p < L := by rw [Lvm.KSponge.streamOf_length] at h1; exact h1
    simp only [Lvm.KSponge.streamOf, List.getElem_ofFn, List.getElem_take]
    rw [show p / RecursionFast.Keccak.rate = p / 136 from rfl,
      show p % RecursionFast.Keccak.rate = p % 136 from rfl,
      msgBytes_eq_stream qm qr (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]

/-! ## Digest cells -/

/-- **Four cells holding a row's output lanes 0–3 are its digest.** -/
theorem digAt_of_cells {v : ℕ → FK} {a : ℕ} {Yt : ℕ → ℕ → K} {i : ℕ}
    (h : ∀ l < 4, v (a + l) = FK.ofBF64 (Yt i l)) :
    digAt v a = Lvm.KSponge.stDigest (yState Yt i) := by
  apply Vector.ext
  intro e he
  rw [digAt, Lvm.Wots.digOfW_get _ he, Lvm.KSponge.stDigest_getElem _ he]
  simp only [yState, Vector.getElem_ofFn]
  rw [h _ (by omega)]
  rfl

/-! ## `SigKSin` -/

/-- A row above `2^14` absorbs the `X` cells. -/
theorem xorMsg_cells {qm : Column 26} {qr : Column 19} {v : ℕ → FK} {f : ℕ → ℕ} {r : ℕ}
    (h : ∀ l < 17, v (f l) = FK.ofBF64 (msgX qm r l)) (a : RecursionFast.Keccak.State) :
    Lvm.KSponge.xorMsg a (Lvm.Wots.laneByte (lanesW v f)) =
      Lvm.KSponge.xorMsg a (Lvm.KG.msgBytes (Mq qm qr) (2 ^ 14 + r)) := by
  have e : Lvm.KSponge.rateArr (Lvm.Wots.laneByte (lanesW v f)) =
      Lvm.KSponge.rateArr (Lvm.KG.msgBytes (Mq qm qr) (2 ^ 14 + r)) := by
    unfold Lvm.KSponge.rateArr
    congr 1
    funext j
    have hj : j.val < 136 := j.2
    simp only [Lvm.Wots.laneByte, lanesW, Lvm.KG.msgBytes, Mq, ksMsg,
      if_neg (show ¬ 2 ^ 14 + r < 2 ^ 14 by omega), Nat.add_sub_cancel_left]
    rw [h _ (by omega)]
    rfl
  simp only [Lvm.KSponge.xorMsg, e]

/-- **Q_sig's `KS` hypothesis from a good pair** (rows `2^14 + r`). -/
theorem sigKSin_of_goodK {x : List UInt8} {qm : Column 26} {qr : Column 19} {I : SigIn} {v : ℕ → FK}
    (hG : GoodK x (qm, qr))
    (hx : ∀ r < 449, ∀ l < 17, v (I.xs + 17 * r + l) = FK.ofBF64 (msgX qm r l))
    (hys : ∀ r < 399, ∀ l < 4, v (I.ys + 4 * r + l) = FK.ofBF64 (Yq qm (2 ^ 14 + r) l))
    (hyc : ∀ t ≤ 16, ∀ l < 4, v (I.yc + 4 * t + l) = FK.ofBF64 (Yq qm (2 ^ 14 + 430 + t) l))
    (hyls : ∀ l < 4, v (I.yls + l) = FK.ofBF64 (Yq qm (2 ^ 14 + 447) l))
    (hyns : ∀ l < 4, v (I.yns + l) = FK.ofBF64 (Yq qm (2 ^ 14 + 448) l)) :
    SigKSin I v := by
  have H := spongeRel_of_KSRel hG.2.1 (by rw [mem_contRows]; omega)
  have hrow : ∀ r < 449, 2 ^ 14 + r < 2 ^ 15 := fun r hr => by omega
  have hcF : ∀ r, r < 449 → ¬ (400 ≤ r ∧ r ≤ 430) →
      decide (2 ^ 14 + r ∈ contRows P20) = false := fun r h1 h2 => by
    simp only [decide_eq_false_iff_not, mem_contRows]; omega
  have hcT : ∀ r, 400 ≤ r → r ≤ 430 → decide (2 ^ 14 + r ∈ contRows P20) = true := fun r h1 h2 => by
    simp only [decide_eq_true_eq, mem_contRows]; omega
  -- a one-block row
  have one : ∀ r < 449, ¬ (400 ≤ r ∧ r ≤ 430) → ∀ y, (∀ l < 4, v (y + l) = FK.ofBF64 (Yq qm (2 ^ 14 + r) l)) →
      OneHash v (fun l => I.xs + 17 * r + l) y := fun r hr hn y hy =>
    ⟨yState (Yq qm) (2 ^ 14 + r), by
      rw [xorMsg_cells (qm := qm) (qr := qr) (r := r) (fun l hl => hx r hr l hl)]
      exact oneRow_perm 15 (ksCol qm) (Yq qm) (Mq qm qr) _ H (hrow r hr) (hcF r hr hn),
      digAt_of_cells hy⟩
  refine ⟨fun r hr => one r (by omega) (by omega) _ (hys r hr), ?_, fun t ht => ?_,
    one 447 (by omega) (by omega) _ hyls, one 448 (by omega) (by omega) _ hyns⟩
  · -- the key leaf: rows `2^14 + 399 … 2^14 + 430`
    refine ⟨fun u => prevState (Yq qm) (fun i ↦ decide (i ∈ contRows P20)) (2 ^ 14 + (399 + u)),
      fun u => yState (Yq qm) (2 ^ 14 + (399 + u)), ?_, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · simp only [prevState, Nat.add_zero, hcF 399 (by omega) (by omega)]; rfl
    · rw [xorMsg_cells (qm := qm) (qr := qr) (r := 399 + u) (fun l hl => hx _ (by omega) l hl)]
      exact row_perm 15 (ksCol qm) (Yq qm) (Mq qm qr) _ H (hrow _ (by omega))
    · simp only [prevState, hcT (399 + (u + 1)) (by omega) (by omega), if_true]
      congr 1
    · refine digAt_of_cells fun l hl => ?_
      have := hyc 0 (by omega) l hl
      simpa using this
  · -- path node `t`: row `2^14 + 431 + t`
    refine one (431 + t) (by omega) (by omega) _ fun l hl => ?_
    have := hyc (t + 1) (by omega) l hl
    rw [show 2 ^ 14 + 430 + (t + 1) = 2 ^ 14 + (431 + t) by omega] at this
    exact this

end Lvm.NS
