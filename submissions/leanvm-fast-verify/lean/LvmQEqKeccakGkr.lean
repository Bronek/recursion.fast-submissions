import LvmQKeccakGkr
import LvmQEqKeccakLayer
import LvmQEqKeccakAlg4

/-!
# QA1: Q_arith_eq for the whole Keccak GKR verifier (`gkr_spec`)

**`F` side.** `verifyKeccak_run`: `F`'s `verifyKeccak` on any state is `vkSpec (feAt Σ)` from the
position `ent + msg` (the segment and lane challenges, `committed`, the 12 layers
(`keccakLayers_run`, `layersSpec`), the committed open, `word`, the 4-round instance sumcheck, the
input open, the 64 slices and the two `require`s); `layersSpec_chain`/`layersSpec_ok`: the layers as
the chain `kChain` (layer `k` at `p + k·L`) and their checks.

**Circuit side** (`gkrGadget`, `LvmQKeccakGkr`): per block a spec (`cst_spec`, `preTB_spec` with
`rep_first`, `layers_spec` (induction over the iterations with `layer_spec`), `fin1TB_spec`,
`rot_spec`, `fin2TB_spec`, the sumcheck gadgets by `sc_spec_plain`), then **`gkr_spec`**: with the
stream bound to the input lanes (`Streamed`), the gadget's outputs are `F`'s `KeccakOut`, `F`'s
position after is the gadget's last lane, and with the gate `1` `F`'s flag after is "the flag
before and every assertion of the gadget". New code.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-! ## `F`'s `verifyKeccak` on a view -/

/-- `n` challenges from position `p` (one FS entry of 72 bytes each). -/
def sampAt (v : Nat → FE) (p n : Nat) : List FE := (List.range n).map fun k => v (p + 40 + 72 * k)

theorem gk_samples_succ (n : Nat) :
    samples (n + 1) = (sampleE >>= fun x => samples n >>= fun xs => pure (x :: xs)) := rfl

theorem gk_samples_run (sig : ByteArray) : ∀ (n : Nat) (s : RS) (p : Nat), s.ent + s.msg = p →
    samples (n + 1) sig s = (sampAt (feAt sig) p (n + 1), ⟨p + 72 * (n + 1), 0, s.ok⟩)
  | 0, s, p, hs => by
    have e1 : s.ent + 40 + s.msg = p + 40 + 72 * 0 := by omega
    have e2 : s.ent + 72 + s.msg = p + 72 * (0 + 1) := by omega
    show ([feAt sig (s.ent + 40 + s.msg)], (⟨s.ent + 72 + s.msg, 0, s.ok⟩ : RS)) = _
    rw [e1, e2]; rfl
  | n + 1, s, p, hs => by
    rw [gk_samples_succ, bind_run, sampleE_run, bind_run,
      gk_samples_run sig n _ (p + 72) (by simp only [] <;> omega), pure_run]
    have e1 : s.ent + 40 + s.msg = p + 40 + 72 * 0 := by omega
    have e2 : p + 72 + 72 * (n + 1) = p + 72 * (n + 1 + 1) := by omega
    rw [e1, e2]
    congr 1
    rw [sampAt, sampAt, List.range_succ_eq_map (n := n + 1), List.map_cons, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply]
    congr 1
    omega

theorem gk_readE_run (sig : ByteArray) (s : RS) (p : Nat) (hs : s.ent + s.msg = p) :
    readE sig s = (feAt sig (p + 40), ⟨s.ent, s.msg + 24, s.ok⟩) := by
  rw [readE_run, show s.ent + 40 + s.msg = p + 40 by omega]

theorem keccakLayers_cons (logSteps step : Nat) (steps : List Nat) (claim : KeccakClaim) :
    keccakLayers logSteps (step :: steps) claim =
      (verifyKeccakLayer logSteps step claim >>= fun c => keccakLayers logSteps steps c) := rfl

theorem layersSpec_cons (v : Nat → FE) (logSteps step : Nat) (steps : List Nat) (claim : KeccakClaim)
    (p : Nat) (ok : Bool) :
    layersSpec v logSteps (step :: steps) claim p ok =
      layersSpec v logSteps steps (layerSpec v logSteps step claim p).claim (layerSpec v logSteps step claim p).pos
        ((layerSpec v logSteps step claim p).ok2 && ((layerSpec v logSteps step claim p).ok1 && ok)) := by
  rw [layersSpec]

/-- **`keccakLayers` on a view**: `layersSpec` from `ent + msg`, the checks threaded. -/
theorem keccakLayers_run (sig : ByteArray) (logSteps : Nat) : ∀ (steps : List Nat) (claim : KeccakClaim)
    (_ : claim.point ≠ []) (s : RS),
    keccakLayers logSteps steps claim sig s =
      ((layersSpec (feAt sig) logSteps steps claim (s.ent + s.msg) s.ok).1,
        if steps = [] then s else
          ⟨(layersSpec (feAt sig) logSteps steps claim (s.ent + s.msg) s.ok).2.1, 0,
            (layersSpec (feAt sig) logSteps steps claim (s.ent + s.msg) s.ok).2.2⟩)
  | [], claim, _, s => rfl
  | step :: steps, claim, hpt, s => by
    rw [keccakLayers_cons, bind_run, verifyKeccakLayer_run sig logSteps step claim hpt, layersSpec_cons]
    have hpt' : (layerSpec (feAt sig) logSteps step claim (s.ent + s.msg)).claim.point ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [layerSpec_point_length, List.length_nil] at this
      exact hpt (List.length_eq_zero_iff.mp this)
    generalize layerSpec (feAt sig) logSteps step claim (s.ent + s.msg) = L at hpt' ⊢
    rw [keccakLayers_run sig logSteps steps L.claim hpt']
    simp only [Nat.add_zero, if_neg (List.cons_ne_nil step steps)]
    cases steps with
    | nil => rfl
    | cons _ _ => simp only [if_neg (List.cons_ne_nil _ _)]

/-! ## Positions -/

theorem gk_packSpec_pos (v : Nat → FE) : ∀ (pt : List FE) (value scale : FE) (p : Nat),
    (packSpec v pt value scale p).2.2.2 = p + 120 * pt.length
  | [], _, _, p => by simp [packSpec]
  | r :: rs, value, scale, p => by
    simp only [packSpec, List.length_cons]
    rw [gk_packSpec_pos v rs]
    omega

/-- A layer moves the position by `2928 + 120·|point|` bytes. -/
theorem gk_layerSpec_pos (v : Nat → FE) (logSteps step : Nat) (claim : KeccakClaim) (p : Nat) :
    (layerSpec v logSteps step claim p).pos = p + (2928 + 120 * claim.point.length) := by
  show (packSpec v claim.point _ 1 (p + 72 + 24 * productBits)).2.2.2 + localBits * roundLen 4 + 72 + 24 * 3 = _
  rw [gk_packSpec_pos]
  simp only [productBits, localBits, roundLen]
  omega

/-! ## The claims along the layers -/

/-- `F`'s claim after `k` layers from `C₀`, layer `k` at `p + k·L`. -/
def kChain (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L : Nat) : Nat → KeccakClaim
  | 0 => C₀
  | k + 1 => (layerSpec v ls k (kChain v ls C₀ p L k) (p + k * L)).claim

/-- Layer `k` of the chain. -/
def kLayer (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L k : Nat) : LayerOut :=
  layerSpec v ls k (kChain v ls C₀ p L k) (p + k * L)

theorem kChain_point (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L : Nat) :
    ∀ k, (kChain v ls C₀ p L k).point.length = C₀.point.length
  | 0 => rfl
  | k + 1 => by
    show (layerSpec v ls k (kChain v ls C₀ p L k) (p + k * L)).claim.point.length = _
    rw [layerSpec_point_length, kChain_point v ls C₀ p L k]

theorem layersSpec_chain (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p : Nat) :
    ∀ (n j : Nat) (ok : Bool),
      layersSpec v ls (List.range' j n) (kChain v ls C₀ p (2928 + 120 * C₀.point.length) j)
          (p + j * (2928 + 120 * C₀.point.length)) ok =
        (kChain v ls C₀ p (2928 + 120 * C₀.point.length) (j + n),
          p + (j + n) * (2928 + 120 * C₀.point.length),
          (layersSpec v ls (List.range' j n) (kChain v ls C₀ p (2928 + 120 * C₀.point.length) j)
            (p + j * (2928 + 120 * C₀.point.length)) ok).2.2)
  | 0, j, ok => by simp [layersSpec]
  | n + 1, j, ok => by
    rw [List.range'_succ, layersSpec_cons]
    have hpos : (layerSpec v ls j (kChain v ls C₀ p (2928 + 120 * C₀.point.length) j)
        (p + j * (2928 + 120 * C₀.point.length))).pos = p + (j + 1) * (2928 + 120 * C₀.point.length) := by
      rw [gk_layerSpec_pos, kChain_point]; ring
    have hc : (layerSpec v ls j (kChain v ls C₀ p (2928 + 120 * C₀.point.length) j)
        (p + j * (2928 + 120 * C₀.point.length))).claim = kChain v ls C₀ p (2928 + 120 * C₀.point.length) (j + 1) :=
      rfl
    rw [hpos, hc, layersSpec_chain v ls C₀ p n (j + 1), show j + 1 + n = j + (n + 1) by omega]

/-- The checks of the layers: all hold iff each layer's two hold (and the flag before). -/
theorem layersSpec_ok (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L : Nat)
    (hL : ∀ k, (kLayer v ls C₀ p L k).pos = p + (k + 1) * L) :
    ∀ (n j : Nat) (ok : Bool),
      (layersSpec v ls (List.range' j n) (kChain v ls C₀ p L j) (p + j * L) ok).2.2 = true ↔
        ok = true ∧ ∀ k < n, (kLayer v ls C₀ p L (j + k)).ok1 = true ∧ (kLayer v ls C₀ p L (j + k)).ok2 = true
  | 0, j, ok => by simp [layersSpec]
  | n + 1, j, ok => by
    rw [List.range'_succ, layersSpec_cons]
    have hpos := hL j
    simp only [kLayer] at hpos
    rw [hpos, show (layerSpec v ls j (kChain v ls C₀ p L j) (p + j * L)).claim = kChain v ls C₀ p L (j + 1) from rfl,
      layersSpec_ok v ls C₀ p L hL n (j + 1)]
    simp only [Bool.and_eq_true]
    constructor
    · rintro ⟨⟨h2, h1, hok⟩, hk⟩
      refine ⟨hok, fun k hk' => ?_⟩
      rcases k with _ | k
      · exact ⟨h1, h2⟩
      · have := hk k (by omega); rwa [show j + 1 + k = j + (k + 1) by omega] at this
    · rintro ⟨hok, hk⟩
      refine ⟨⟨(hk 0 (by omega)).2, (hk 0 (by omega)).1, hok⟩, fun k hk' => ?_⟩
      rw [show j + 1 + k = j + (k + 1) by omega]
      exact hk (k + 1) (by omega)

/-! ## The whole GKR -/

/-- **`verifyKeccak` on a view** from position `p`, the flag `ok₀` before: the outputs, the flag
after, the entry offset after (the message bytes after are the `64` slices'). -/
def vkSpec (v : Nat → FE) (ls : Nat) (inst output : List FE) (p : Nat) (ok₀ : Bool) :
    KeccakOut × Bool × Nat :=
  let segment := sampAt v p segmentBits
  let lanePoint := sampAt v (p + 72) laneBits
  let committed := v (p + 472)
  let first := keccakFirstClaim inst segment lanePoint output committed
  let L := layersSpec v ls (List.range gkrDepth) first (p + 456) ok₀
  let o1 := openSpec v ls first 1 (gkrSegments - 1) committed L.2.1
  let word := v (L.2.1 + 760)
  let lw := scSpec v 3 (L.2.1 + 744) L.1.value (List.replicate 4 none)
  let o2 := openSpec v ls L.1 0 gkrSegments lw.2 (L.2.1 + 1224)
  let slices := scalarsAt v (L.2.1 + 1984) kBits
  (⟨inst.take 4 ++ inst.drop 4 ++ o1.1, word, lw.1 ++ L.1.point.take (ls - 4) ++ o2.1, slices⟩,
    (multilinearEval L.1.mu lw.1 * dot o2.2.1 slices == o2.2.2) &&
      ((o1.2.1.headD 0 * word == o1.2.2) && L.2.2),
    L.2.1 + 1944)

theorem verifyKeccak_eq (ls : Nat) (inst output : List FE) :
    verifyKeccak ls inst output =
      (samples segmentBits >>= fun segment => samples laneBits >>= fun lanePoint => readE >>= fun committed =>
        keccakLayers ls (List.range gkrDepth) (keccakFirstClaim inst segment lanePoint output committed) >>=
          fun claim =>
        keccakOpen ls (keccakFirstClaim inst segment lanePoint output committed) 1 (gkrSegments - 1) committed >>=
          fun o1 =>
        readE >>= fun word => require (o1.2.1.headD 0 * word == o1.2.2) >>= fun _ =>
        sumcheck claim.value 3 (List.replicate 4 none) >>= fun lw =>
        keccakOpen ls claim 0 gkrSegments lw.2 >>= fun o2 =>
        readEs kBits >>= fun slices =>
        require (multilinearEval claim.mu lw.1 * dot o2.2.1 slices == o2.2.2) >>= fun _ =>
        pure ⟨inst.take 4 ++ inst.drop 4 ++ o1.1, word, lw.1 ++ claim.point.take (ls - 4) ++ o2.1, slices⟩) := rfl

/-- **`F`'s `verifyKeccak` is `vkSpec`** on the stream's scalars from `ent + msg`. -/
theorem verifyKeccak_run (sig : ByteArray) (ls : Nat) (inst output : List FE) (s : RS) (p : Nat)
    (hs : s.ent + s.msg = p) :
    verifyKeccak ls inst output sig s =
      ((vkSpec (feAt sig) ls inst output p s.ok).1,
        ⟨(vkSpec (feAt sig) ls inst output p s.ok).2.2, 24 * kBits, (vkSpec (feAt sig) ls inst output p s.ok).2.1⟩) := by
  dsimp only [vkSpec]
  rw [verifyKeccak_eq, show segmentBits = 0 + 1 from rfl, show laneBits = 4 + 1 from rfl,
    bind_run, gk_samples_run sig 0 s p hs, bind_run,
    gk_samples_run sig 4 _ (p + 72) (by simp only [] <;> omega), bind_run,
    gk_readE_run sig _ (p + 432) (by simp only [] <;> omega), bind_run]
  dsimp only
  have e1 : p + 72 * (0 + 1) = p + 72 := by omega
  have e2 : p + 72 + 72 * (4 + 1) = p + 432 := by omega
  have e3 : p + 432 + (0 + 24) = p + 456 := by omega
  rw [e1, e2, show p + 432 + 40 = p + 472 by omega]
  generalize hF : keccakFirstClaim inst (sampAt (feAt sig) p (0 + 1)) (sampAt (feAt sig) (p + 72) (4 + 1)) output
    (feAt sig (p + 472)) = first
  have hpt : first.point ≠ [] := by
    rw [← hF]; simp [keccakFirstClaim, sampAt]
  rw [keccakLayers_run sig ls _ first hpt, if_neg (by decide), bind_run, keccakOpen_run, bind_run]
  dsimp only
  rw [e3]
  generalize layersSpec (feAt sig) ls (List.range gkrDepth) first (p + 456) s.ok = L
  rw [gk_readE_run sig _ (L.2.1 + 720) (by simp only [keccakSlotBits, slotLog, roundLen] <;> omega), bind_run,
    require_run, bind_run]
  dsimp only
  rw [sumcheck_run sig 3 (by norm_num), bind_run]
  dsimp only
  rw [keccakOpen_run, bind_run]
  dsimp only
  rw [readEs_run, bind_run, require_run, pure_run]
  dsimp only
  simp only [scState_replicate _ _ (show 0 < 4 by decide), keccakSlotBits, slotLog, roundLen, Nat.add_zero,
    Nat.zero_add]
  done


/-! ## Operands across blocks -/

theorem gk_iterXv_fix (M : Mem) (o : LoopOut) (jf : Nat) (τ : Ty) (b : Nat) :
    iterXv M o jf (.ext ⟨τ, b, []⟩) = M.rd τ b := by
  simp only [iterXv, Src.toOpd, Opd.val_abs, Addr.at]
  rfl

theorem gk_iterXv_gkS (M : Mem) (o : LoopOut) (jf : Nat) (c : Cell) : iterXv M o jf (gkS c) = c.val M :=
  gk_iterXv_fix M o jf c.ty c.n

/-- An operand a straight block exports: one of its rows, or a fixed cell. -/
def Fx (s : Src) : Prop := (∃ n, s = .loc n) ∨ ∃ τ b, s = .ext ⟨τ, b, []⟩

theorem gkOut_val (M : Mem) (o o' : LoopOut) (jf : Nat) (V : Nat → FE) {s : Src} (hs : Fx s) :
    (s.gkOut o).valF (iterXv M o' jf) V = s.valF (iterXv M o 0) (iterF M o 0) := by
  rcases hs with ⟨n, rfl⟩ | ⟨τ, b, rfl⟩
  · exact gk_iterXv_fix M o' jf _ _
  · show iterXv M o' jf (Src.ext ⟨τ, b, []⟩) = iterXv M o 0 (Src.ext ⟨τ, b, []⟩)
    rw [gk_iterXv_fix, gk_iterXv_fix]

theorem gkCell_val (M : Mem) (o : LoopOut) {s : Src} (hs : Fx s) :
    (s.gkCell o).val M = s.valF (iterXv M o 0) (iterF M o 0) := by
  rcases hs with ⟨n, rfl⟩ | ⟨τ, b, rfl⟩
  · rfl
  · exact (gk_iterXv_fix M o 0 τ b).symm

theorem fx_emit (i : Ins) (n : Nat) : Fx (emit i n).1 := Or.inl ⟨n, rfl⟩

theorem fx_mapTB {α : Type} {f : α → TB Src} (hf : ∀ a n, Fx (f a n).1) :
    ∀ (as : List α) (n : Nat), ∀ x ∈ (mapTB f as n).1, Fx x
  | [], _, x, hx => by simp [mapTB, tb_pure] at hx
  | a :: as, n, x, hx => by
    simp only [mapTB, tb_bind, tb_pure, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hf a n
    · exact fx_mapTB hf as _ x hx

theorem fx_gEqTab (z : Src) : ∀ (pt tab : List Src) (n : Nat), (∀ x ∈ tab, Fx x) →
    ∀ x ∈ (gEqTab z tab pt n).1, Fx x
  | [], tab, n, h => by simpa [gEqTab, tb_pure] using h
  | r :: rs, tab, n, h => by
    simp only [gEqTab, tb_bind]
    refine fx_gEqTab z rs _ _ (fun x hx => ?_)
    simp only [gEqStep, tb_bind, tb_pure, List.mem_append] at hx
    rcases hx with hx | hx
    · exact fx_mapTB (fun _ _ => fx_emit _ _) _ _ x hx
    · exact fx_mapTB (fun _ _ => fx_emit _ _) _ _ x hx

/-! ## The relocated layer template -/

theorem relocS_valF (xv : Src → FE) (V : Nat → FE) (q cst : Nat) (s : Src) :
    (relocS q cst s).valF xv V = s.valF (fun s' => xv (relocS q cst s')) V := by
  rcases s with k | k | ⟨τ, b, st⟩
  · rfl
  · rfl
  · rcases st with _ | ⟨s, _ | ⟨s', st⟩⟩
    · rfl
    · show (relocS q cst (.ext ⟨τ, b, [s]⟩)).valF xv V = xv (relocS q cst (.ext ⟨τ, b, [s]⟩))
      simp only [relocS]; split_ifs <;> rfl
    · rfl

theorem evalF_reloc (xv : Src → FE) (V : Nat → FE) (q cst : Nat) (i : Ins) :
    (relocI q cst i).evalF xv V = i.evalF (fun s => xv (relocS q cst s)) V := by
  unfold Ins.evalF relocI
  simp only [getD_map_default (relocS q cst) rfl, relocS_valF]

theorem reloc_getD (q cst : Nat) (δ : List Ins) (k : Nat) :
    (δ.map (relocI q cst)).getD k default = relocI q cst (δ.getD k default) :=
  getD_map_default (relocI q cst) rfl δ k

theorem thold_reloc {xv : Src → FE} {V : Nat → FE} {n q cst : Nat} {δ : List Ins}
    (h : THold xv V n (δ.map (relocI q cst))) : THold (fun s => xv (relocS q cst s)) V n δ := by
  intro k hk ha
  have := h k (by simpa using hk) (by rw [reloc_getD]; exact ha)
  rw [this, reloc_getD, evalF_reloc]

theorem tassert_reloc {xv : Src → FE} {V : Nat → FE} {q cst : Nat} {δ : List Ins} :
    TAssert xv V (δ.map (relocI q cst)) ↔ TAssert (fun s => xv (relocS q cst s)) V δ := by
  have e : ∀ k o, ((δ.map (relocI q cst)).getD k default).args.getD o default =
      relocS q cst ((δ.getD k default).args.getD o default) := by
    intro k o; rw [reloc_getD]; exact getD_map_default (relocS q cst) rfl _ _
  constructor
  · intro h k hk ha
    have := h k (by simpa using hk) (by rw [reloc_getD]; exact ha)
    rw [e, e, relocS_valF, relocS_valF] at this
    exact this
  · intro h k hk ha
    rw [reloc_getD] at ha
    rw [e, e, relocS_valF, relocS_valF]
    exact h k (by simpa using hk) ha

/-! ## Write counts -/

theorem ltw_tplOf (τ : Ty) (δ : List Ins) :
    ltw τ (tplOf δ) = (δ.map fun i => Row.w τ ⟨i.op, i.ty, []⟩).sum := by
  simp only [ltw, tplOf, List.map_map]; rfl

theorem lrank_tplOf (τ : Ty) (δ : List Ins) (t : Nat) :
    lrank τ (tplOf δ) t = ((δ.take t).map fun i => Row.w τ ⟨i.op, i.ty, []⟩).sum := by
  simp only [lrank, tplOf, ← List.map_take, List.map_map]; rfl

theorem ltw_reloc (τ : Ty) (q cst : Nat) (δ : List Ins) : ltw τ (tplOf (δ.map (relocI q cst))) = ltw τ (tplOf δ) := by
  rw [ltw_tplOf, ltw_tplOf, List.map_map]; rfl

theorem lrank_reloc (τ : Ty) (q cst : Nat) (δ : List Ins) (t : Nat) :
    lrank τ (tplOf (δ.map (relocI q cst))) t = lrank τ (tplOf δ) t := by
  rw [lrank_tplOf, lrank_tplOf, ← List.map_take, List.map_map]; rfl

theorem sum_ones {δ : List Ins} {τ : Ty} (h : ∀ i ∈ δ, Row.w τ ⟨i.op, i.ty, []⟩ = 1) :
    (δ.map fun i => Row.w τ ⟨i.op, i.ty, []⟩).sum = δ.length := by
  induction δ with
  | nil => rfl
  | cons i δ ih =>
    rw [List.map_cons, List.sum_cons, h i (by simp), ih (fun j hj => h j (by simp [hj])), List.length_cons]
    omega

theorem lrank_ones {δ : List Ins} {τ : Ty} (h : ∀ i ∈ δ, Row.w τ ⟨i.op, i.ty, []⟩ = 1) {t : Nat}
    (ht : t ≤ δ.length) : lrank τ (tplOf δ) t = t := by
  rw [lrank_tplOf, sum_ones (fun i hi => h i (List.mem_of_mem_take hi)), List.length_take]; omega

theorem ltw_ones {δ : List Ins} {τ : Ty} (h : ∀ i ∈ δ, Row.w τ ⟨i.op, i.ty, []⟩ = 1) :
    ltw τ (tplOf δ) = δ.length := by
  rw [ltw_tplOf, sum_ones h]

theorem lrank_append_le (τ : Ty) (A B : List Ins) {t : Nat} (ht : t ≤ A.length) :
    lrank τ (tplOf (A ++ B)) t = lrank τ (tplOf A) t := by
  rw [lrank_tplOf, lrank_tplOf, List.take_append_of_le_length ht]

/-- The rows from `cb` on each write one `E` cell: their ranks are consecutive up to the end. -/
theorem lrank_suffix {δ : List Ins} {cb C : Nat} (hl : δ.length = cb + C)
    (h : ∀ i ∈ δ.drop cb, Row.w .E ⟨i.op, i.ty, []⟩ = 1) {j : Nat} (hj : j ≤ C) :
    lrank .E (tplOf δ) (cb + j) + C = ltw .E (tplOf δ) + j := by
  have hδ : δ = δ.take cb ++ δ.drop cb := (List.take_append_drop cb δ).symm
  have hd : (δ.drop cb).length = C := by rw [List.length_drop]; omega
  have ht : (δ.take cb).length = cb := by rw [List.length_take]; omega
  rw [lrank_tplOf, ltw_tplOf, hδ, List.take_append, ht, show cb + j - cb = j by omega,
    List.take_of_length_le (by omega : (δ.take cb).length ≤ cb + j), List.map_append, List.map_append,
    List.sum_append, List.sum_append, sum_ones h, sum_ones (fun i hi => h i (List.mem_of_mem_take hi)),
    List.length_take, hd]
  omega

/-! ## Loop blocks -/

theorem gk_adv_loop (p : Ptr) (dims : List Nat) (tpl : List LRow) :
    p.adv (loop dims tpl p).2 = ⟨p.k + ltw .K tpl * 2 ^ dims.sum, p.e + ltw .E tpl * 2 ^ dims.sum⟩ := by
  rw [loop_apply]
  simp only [Ptr.adv, segsW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Seg.w,
    mkLoop_tw]
  rfl

theorem gk_loop_fst (dims : List Nat) (tpl : List LRow) (p : Ptr) : (loop dims tpl p).1 = ⟨p, dims, tpl⟩ := rfl

/-- **The assertions of a loop block**, iteration by iteration. -/
theorem segsAssert_loop_iff {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr} :
    SegsAssert M p (loop dims (tplOf ins) p).2 ↔
      ∀ jf < 2 ^ dims.sum, TAssert (iterXv M (loop dims (tplOf ins) p).1 jf)
        (iterF M (loop dims (tplOf ins) p).1 jf) ins := by
  constructor
  · intro h jf hjf; exact tassert_of_loop h hjf
  · intro h
    simp only [loop_apply, SegsAssert, and_true]
    intro jf hjf t ht
    have hjf' : jf < 2 ^ dims.sum := by simpa [Block.size, Block.lsize, mkLoop] using hjf
    have hlen : t < ins.length := by simpa [mkLoop, tplOf] using ht
    have hA := h jf hjf'
    rw [show mkLoop p dims (tplOf ins) = LoopOut.blk ⟨p, dims, tplOf ins⟩ from rfl,
      show p = (⟨p, dims, tplOf ins⟩ : LoopOut).p from rfl, loop_assert_iff]
    have harg : ∀ k, LoopOut.arg M ⟨p, dims, tplOf ins⟩ jf t k =
        ((ins.getD t default).args.getD k default).valF (iterXv M ⟨p, dims, tplOf ins⟩ jf)
          (iterF M ⟨p, dims, tplOf ins⟩ jf) := by
      intro k
      simp only [LoopOut.arg]
      show (((tplOf ins).getD t default).args.getD k default).val M _ jf = _
      rw [tplOf_getD ins hlen, Ins.toLRow, getD_map_default Src.toOpd rfl]
      cases ((ins.getD t default).args.getD k default) with
      | loc k' => rw [Src.toOpd, Opd.val_cur M _ hjf']; rfl
      | prev k' => rfl
      | ext a => rfl
    have hop : ((⟨p, dims, tplOf ins⟩ : LoopOut).tpl.getD t default).op = (ins.getD t default).op := by
      show ((tplOf ins).getD t default).op = _
      rw [tplOf_getD ins hlen]; rfl
    unfold LAssert
    rw [hop]
    by_cases ha : (ins.getD t default).op = .assert0
    · rw [ha]; simp only [harg]; exact hA t hlen ha
    · split
      · rename_i heq; exact absurd heq ha
      all_goals trivial

theorem prologueSegs_assert (M : Mem) (init : Nat → Cell) :
    ∀ (p : Ptr) (t : Nat) (tpl : List LRow), SegsAssert M p (prologueSegs init t tpl)
  | _, _, [] => trivial
  | p, t, r :: rs => by
    simp only [prologueSegs]
    rw [segsAssert_append]
    refine ⟨?_, prologueSegs_assert M init _ _ rs⟩
    unfold prologueRow
    split
    · trivial
    · exact ⟨trivial, trivial⟩

/-- A sumcheck gadget asserts nothing. -/
theorem sc_asserts (M : Mem) (p : Ptr) (D d q : Nat) (claim : Cell) :
    SegsAssert M p (scGadget D d q .plain claim p).2 := by
  rw [scGadget, loopP_apply, segsAssert_append]
  refine ⟨prologueSegs_assert M _ p 0 _, ?_⟩
  have := (segsAssert_loop_iff (M := M) (dims := [D]) (ins := scTpl d q .plain)
    (p := p.adv (prologueSegs (fun _ => claim) 0 (tplOf (scTpl d q .plain))))).mpr
    (fun jf _ k hk ha => absurd ha (roundIns_noA d q _ .plain _ (by
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)))
  simpa [loop_apply] using this

/-! ## No assertions -/

/-- The instructions assert nothing. -/
def GNoA (δ : List Ins) : Prop := ∀ k < δ.length, (δ.getD k default).op ≠ .assert0

theorem tassert_noA {xv : Src → FE} {V : Nat → FE} {δ : List Ins} (h : GNoA δ) : TAssert xv V δ :=
  fun k hk ha => absurd ha (h k hk)

theorem gnoA_append {δ₁ δ₂ : List Ins} (h₁ : GNoA δ₁) (h₂ : GNoA δ₂) : GNoA (δ₁ ++ δ₂) := by
  intro k hk
  by_cases hk1 : k < δ₁.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk1, ← List.getD_eq_getElem?_getD]
    exact h₁ k hk1
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD]
    exact h₂ _ (by simp at hk; omega)

theorem gnoA_bind {α β : Type} (m : TB α) (f : α → TB β) (n : Nat) (h₁ : GNoA (m n).2)
    (h₂ : GNoA (f (m n).1 (n + (m n).2.length)).2) : GNoA ((m >>= f) n).2 := by
  rw [tb_bind]; exact gnoA_append h₁ h₂

theorem gnoA_pure {α : Type} (a : α) (n : Nat) : GNoA ((pure a : TB α) n).2 := fun k hk => by simp [tb_pure] at hk

theorem gnoA_emit {i : Ins} (n : Nat) (h : i.op ≠ .assert0) : GNoA (emit i n).2 := by
  intro k hk
  simp only [emit, List.length_singleton] at hk
  rw [show k = 0 by omega]; exact h

theorem gnoA_mul (a b d : Src) (n : Nat) : GNoA (gMul a b d n).2 := gnoA_emit n (by simp [mulI])
theorem gnoA_lin (k k' : FK) (a b : Src) (n : Nat) : GNoA (gLin k k' a b n).2 := gnoA_emit n (by simp [linI])
theorem gnoA_zero (a : Src) (n : Nat) : GNoA (gZero a n).2 := gnoA_emit n (by simp [linI])
theorem gnoA_one (a : Src) (n : Nat) : GNoA (gOne a n).2 := gnoA_emit n (by simp [linI])
theorem gnoA_load (q : Nat) (str : List Nat) (n : Nat) : GNoA (gLoad q str n).2 := gnoA_emit n (by simp [loadI])

theorem gnoA_mapTB {α : Type} {f : α → TB Src} (hf : ∀ a n, GNoA (f a n).2) :
    ∀ (as : List α) (n : Nat), GNoA (mapTB f as n).2
  | [], n => gnoA_pure _ n
  | a :: as, n => gnoA_bind _ _ n (hf a n) (gnoA_bind _ _ _ (gnoA_mapTB hf as _) (gnoA_pure _ _))

theorem gnoA_gSum : ∀ (s : Src) (cs : List Src) (n : Nat), GNoA (gSum s cs n).2
  | s, [], n => gnoA_pure _ n
  | s, c :: cs, n => gnoA_bind _ _ n (gnoA_lin _ _ _ _ _) (gnoA_gSum _ cs _)

theorem gnoA_gDot : ∀ (acc : Src) (cds : List (Src × Src)) (n : Nat), GNoA (gDot acc cds n).2
  | acc, [], n => gnoA_pure _ n
  | acc, cd :: rest, n => gnoA_bind _ _ n (gnoA_mul _ _ _ _) (gnoA_gDot _ rest _)

theorem gnoA_gEqTab (z : Src) : ∀ (pt tab : List Src) (n : Nat), GNoA (gEqTab z tab pt n).2
  | [], tab, n => gnoA_pure _ n
  | r :: rs, tab, n => gnoA_bind _ _ n
      (gnoA_bind _ _ n (gnoA_lin _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_mul _ _ _ _) _ _)
        (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_mul _ _ _ _) _ _) (gnoA_pure _ _))))
      (gnoA_gEqTab z rs _ _)

theorem gnoA_gSumMap (z : Src) (k : Nat) {f : Nat → TB Src} (hf : ∀ c n, GNoA (f c n).2) (n : Nat) :
    GNoA (gSumMap z k f n).2 := gnoA_bind _ _ n (gnoA_mapTB hf _ _) (gnoA_gSum _ _ _)

theorem gnoA_gLaneForm (z : Src) (B : List Src) (R : Nat → Src) (l n : Nat) : GNoA (gLaneForm z B R l n).2 :=
  gnoA_bind _ _ n (gnoA_mul _ _ _ _) (gnoA_bind _ _ _ (gnoA_gDot _ _ _) (gnoA_gDot _ _ _))

theorem gnoA_gFoldPairs (z r1 r : Src) : ∀ (l : List Src) (n : Nat), GNoA (gFoldPairs z r1 r l n).2
  | a :: b :: rest, n => gnoA_bind _ _ n (gnoA_mul _ _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
      (gnoA_bind _ _ _ (gnoA_gFoldPairs z r1 r rest _) (gnoA_pure _ _)))
  | [], n => gnoA_pure _ n
  | [_], n => gnoA_pure _ n

theorem gnoA_gMle (z : Src) : ∀ (cur pt : List Src) (n : Nat), GNoA (gMle z cur pt n).2
  | cur, [], n => gnoA_pure _ n
  | cur, r :: rs, n => gnoA_bind _ _ n (gnoA_lin _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_gFoldPairs _ _ _ _ _)
      (gnoA_gMle z _ rs _))

/-! ## `mapTB` of single rows -/

theorem mapTB_emit {α : Type} (g : α → Ins) : ∀ (as : List α) (n : Nat),
    mapTB (fun a => emit (g a)) as n = ((List.range as.length).map fun i => Src.loc (n + i), as.map g)
  | [], n => rfl
  | a :: as, n => by
    simp only [mapTB, tb_bind, tb_pure, mapTB_emit g as, List.length_cons, List.map_cons, List.append_nil]
    refine Prod.ext ?_ rfl
    simp only [emit, List.length_singleton, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 1
    omega


/-! ## List facts -/

theorem gk_getD_app_left {A B : List FE} {i : Nat} (h : i < A.length) : (A ++ B).getD i 0 = A.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gk_getD_app_right (A B : List FE) {i k : Nat} (hk : A.length ≤ k) (hi : k - A.length = i) :
    (A ++ B).getD k 0 = B.getD i 0 := by
  subst hi; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hk]

theorem gk_range_map_getD (l : List FE) : (List.range l.length).map (fun j => l.getD j 0) = l := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

theorem gk_take_range_map (f : Nat → FE) {n N : Nat} (h : n ≤ N) :
    ((List.range N).map f).take n = (List.range n).map f := by
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

theorem gk_drop_range_map (f : Nat → FE) (n N : Nat) :
    ((List.range N).map f).drop n = (List.range (N - n)).map fun i => f (n + i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_drop, List.getElem_map, List.getElem_range]

theorem gk_sum_eqKernel_aux : ∀ (pt t : List FE),
    (pt.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) t).sum = t.sum
  | [], t => rfl
  | r :: rs, t => by
    rw [List.foldl_cons, gk_sum_eqKernel_aux rs, List.sum_append, List.sum_map_mul_right,
      List.sum_map_mul_right, ← mul_add, add_assoc, FE_add_self, add_zero, mul_one]
    simp

/-- The `eq` table sums to one. -/
theorem gk_sumE_eqKernel (pt : List FE) : sumE (eqKernel pt) = 1 := by
  rw [sumE_eq_sum, eqKernel, gk_sum_eqKernel_aux]; simp

theorem gk_dot_eq_sum {l r : List FE} {n : Nat} (hl : l.length = n) (hr : r.length = n) :
    dot l r = ((List.range n).map fun z => l.getD z 0 * r.getD z 0).sum := by
  have hz : List.zipWith (· * ·) l r = (List.range n).map fun z => l.getD z 0 * r.getD z 0 := by
    apply List.ext_getElem
    · simp [hl, hr]
    · intro i h1 h2
      simp only [List.length_zipWith, hl, hr, min_self] at h1
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ h1),
        List.getElem?_eq_getElem (hr ▸ h1)]
  unfold dot
  rw [hz, foldl_add, zero_add]

theorem gk_eqKernel_one (s : FE) : eqKernel [s] = [1 + s, s] := by
  simp [eqKernel]

/-! ## The first claim's carried values -/

/-- The carried values of the first claim, in the copy rows' order. -/
def carV (v0 : FE) (mu instP : List FE) (seg : FE) (lanes fl : List FE) : List FE :=
  [v0] ++ mu ++ [1] ++ instP ++ [seg] ++ lanes.take 25 ++ List.replicate 6 0 ++ fl

theorem firstW_congr {l l' : List FE} (h : ∀ i < 25, l.getD i 0 = l'.getD i 0) : firstW l = firstW l' := by
  unfold firstW
  refine List.map_congr_left fun j hj => ?_
  rw [h (j / 64) (by simp [keccakBits] at hj; omega)]

theorem gk_getD_skip (A B : List FE) {m : Nat} (hA : A.length = m) (k : Nat) :
    (A ++ B).getD (m + k) 0 = B.getD k 0 := by
  subst hA; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

section carV

variable (v0 : FE) (mu iP : List FE) (s : FE) (la fl : List FE)

theorem carV_eq : carV v0 mu iP s la fl =
    [v0] ++ (mu ++ ([1] ++ (iP ++ ([s] ++ (la.take 25 ++ (List.replicate 6 0 ++ fl)))))) := by
  simp only [carV, List.append_assoc]

theorem carV_mu (hmu : mu.length = 16) {i : Nat} (hi : i < 16) :
    (carV v0 mu iP s la fl).getD (1 + i) 0 = mu.getD i 0 := by
  rw [carV_eq, gk_getD_skip [v0] _ (m := 1) rfl, gk_getD_app_left (by omega)]

theorem carV_kappa (hmu : mu.length = 16) : (carV v0 mu iP s la fl).getD 17 0 = 1 := by
  rw [carV_eq, show 17 = 1 + (16 + 0) from rfl, gk_getD_skip [v0] _ (m := 1) rfl, gk_getD_skip mu _ hmu]; rfl

theorem carV_pt (hmu : mu.length = 16) {P : Nat} (hiP : iP.length = P) {i : Nat} (hi : i < P) :
    (carV v0 mu iP s la fl).getD (18 + i) 0 = iP.getD i 0 := by
  rw [carV_eq, show 18 + i = 1 + (16 + (1 + i)) by omega, gk_getD_skip [v0] _ (m := 1) rfl, gk_getD_skip mu _ hmu,
    gk_getD_skip [1] _ (m := 1) rfl, gk_getD_app_left (by omega)]

theorem carV_seg (hmu : mu.length = 16) {P : Nat} (hiP : iP.length = P) :
    (carV v0 mu iP s la fl).getD (18 + P) 0 = s := by
  rw [carV_eq, show 18 + P = 1 + (16 + (1 + (P + 0))) by omega, gk_getD_skip [v0] _ (m := 1) rfl,
    gk_getD_skip mu _ hmu, gk_getD_skip [1] _ (m := 1) rfl, gk_getD_skip iP _ hiP]; rfl

theorem carV_B (hmu : mu.length = 16) {P : Nat} (hiP : iP.length = P) (hla : 25 ≤ la.length) {l : Nat}
    (hl : l < 25) : (carV v0 mu iP s la fl).getD (19 + P + l) 0 = la.getD l 0 := by
  rw [carV_eq, show 19 + P + l = 1 + (16 + (1 + (P + (1 + l)))) by omega, gk_getD_skip [v0] _ (m := 1) rfl,
    gk_getD_skip mu _ hmu, gk_getD_skip [1] _ (m := 1) rfl, gk_getD_skip iP _ hiP, gk_getD_skip [s] _ (m := 1) rfl,
    gk_getD_app_left (by rw [List.length_take]; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hl]

theorem carV_fl (hmu : mu.length = 16) {P : Nat} (hiP : iP.length = P) (hla : 25 ≤ la.length) {i : Nat} :
    (carV v0 mu iP s la fl).getD (50 + P + i) 0 = fl.getD i 0 := by
  rw [carV_eq, show 50 + P + i = 1 + (16 + (1 + (P + (1 + (25 + (6 + i)))))) by omega,
    gk_getD_skip [v0] _ (m := 1) rfl, gk_getD_skip mu _ hmu, gk_getD_skip [1] _ (m := 1) rfl, gk_getD_skip iP _ hiP,
    gk_getD_skip [s] _ (m := 1) rfl, gk_getD_skip (la.take 25) _ (by rw [List.length_take]; omega),
    gk_getD_skip (List.replicate 6 0) _ (by simp)]

end carV

theorem keccakFirstClaim_weights (inst seg lp out : List FE) (com : FE) :
    (keccakFirstClaim inst seg lp out com).weights = firstW (eqKernel lp) := by
  simp only [keccakFirstClaim, firstW]

theorem rep_first_value {instV lp out : List FE} (hlp : lp.length = 5) (hout : out.length = 25)
    (seg com : FE) :
    com + seg * ((List.range 25).map fun l => (eqKernel lp).getD l 0 * out.getD l 0).sum =
      (keccakFirstClaim instV [seg] lp out com).value := by
  have hL : (eqKernel lp).length = 32 := by rw [eqKernel_length, hlp]; rfl
  show _ = com + (eqKernel [seg]).getD (gkrSegments - 1) 0 * dot ((eqKernel lp).take 25) out
  rw [gk_eqKernel_one, gk_dot_eq_sum (by rw [List.length_take, hL]; rfl) hout]
  simp only [gkrSegments, show 2 - 1 = 1 from rfl, List.getD_cons_succ, List.getD_cons_zero]
  refine congrArg (fun x => com + seg * x) (congrArg List.sum (List.map_congr_left fun l hl => ?_))
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.mem_range.mp hl]

/-- **The first claim** (`keccakFirstClaim`) is represented by its carried values. -/
theorem rep_first (P : Nat) {instV lp out fl : List FE} (hinst : instV.length = P + 4) (hlp : lp.length = 5)
    (hout : out.length = 25)
    (hfl : ∀ i < 7, fl.getD i 0 = (eqKernel lp).getD 0 0 * FE.ofK (FK.x ^ iotaPos i)) (seg com : FE) :
    Rep P (fun j => (carV (com + seg * ((List.range 25).map fun l => (eqKernel lp).getD l 0 * out.getD l 0).sum)
        (eqKernel (instV.take 4)) (instV.drop 4) seg (eqKernel lp) fl).getD j 0)
      (keccakFirstClaim instV [seg] lp out com) true := by
  have hL : (eqKernel lp).length = 32 := by rw [eqKernel_length, hlp]; rfl
  have hmu : (eqKernel (instV.take 4)).length = 16 := by
    rw [eqKernel_length, List.length_take, hinst]; rfl
  have hiP : (instV.drop 4).length = P := by rw [List.length_drop, hinst]; omega
  have hla : 25 ≤ (eqKernel lp).length := by omega
  have hB : ∀ l < 25, (repB P fun j => (carV (com + seg * ((List.range 25).map fun l =>
      (eqKernel lp).getD l 0 * out.getD l 0).sum) (eqKernel (instV.take 4)) (instV.drop 4) seg
        (eqKernel lp) fl).getD j 0).getD l 0 = (eqKernel lp).getD l 0 := by
    intro l hl
    simp only [repB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
      Option.getD_some]
    rw [← List.getD_eq_getElem?_getD, carV_B _ _ _ _ _ _ hmu hiP hla hl, List.getD_eq_getElem?_getD]
  refine ⟨rep_first_value (instV := instV) hlp hout seg com, ?_, ?_, ?_, ?_, ?_⟩
  · show _ = eqKernel (instV.take 4)
    conv_rhs => rw [← gk_range_map_getD (eqKernel (instV.take 4)), hmu]
    exact List.map_congr_left fun i hi => carV_mu _ _ _ _ _ _ hmu (List.mem_range.mp hi)
  · show _ = sumE (eqKernel (instV.take 4))
    rw [gk_sumE_eqKernel, carV_kappa _ _ _ _ _ _ hmu]
  · show _ = instV.drop 4 ++ [seg]
    rw [List.range_succ (n := P), List.map_append, List.map_singleton, carV_seg _ _ _ _ _ _ hmu hiP]
    congr 1
    conv_rhs => rw [← gk_range_map_getD (instV.drop 4), hiP]
    exact List.map_congr_left fun i hi => carV_pt _ _ _ _ _ _ hmu hiP (List.mem_range.mp hi)
  · rw [if_pos rfl, keccakFirstClaim_weights]
    exact firstW_congr fun i hi => (hB i hi).symm
  · intro i hi
    rw [if_pos rfl, carV_fl _ _ _ _ _ _ hmu hiP hla, hfl i hi, hB 0 (by decide)]


/-! ## Peeling a template program -/

theorem tb_peel {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β)
    (h : THold xv V n ((m >>= f) n).2) :
    THold xv V n (m n).2 ∧ THold xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 ∧
      ((m >>= f) n).1 = (f (m n).1 (n + (m n).2.length)).1 :=
  ⟨((thold_bind m f).mp h).1, ((thold_bind m f).mp h).2, rfl⟩

theorem gk_eqTab_one {xv : Src → FE} {V : Nat → FE} {z one : Src} (hz : z.valF xv V = 0)
    (h1 : one.valF xv V = 1) (pt : List Src) (n : Nat) (h : THold xv V n (gEqTab z [one] pt n).2) :
    vals xv V (gEqTab z [one] pt n).1 = eqKernel (vals xv V pt) := by
  rw [vals, gEqTab_spec hz pt [one] n h, List.map_singleton, h1]; rfl

/-! ## The first-claim block -/

/-- The values of the lane challenges' `eq` table. -/
def lanePt (u : Nat → FE) (qs : Nat) : List FE := (List.range 5).map fun k => u (qs + 9 * (k + 1))

/-- **The first-claim block**: its exports and the carried values (`carV`). -/
theorem preTB_spec {xv : Src → FE} {V : Nat → FE} {P qs : Nat} {inst out : Nat → Src} {b : Src}
    {u : Nat → FE} (hu : ∀ m ≤ qs + 54, lv xv [] m = u m) (hinst : ∀ i, Fx (inst i)) {n : Nat}
    (h : THold xv V n (preTB P qs inst out b n).2) :
    (preTB P qs inst out b n).1.com.valF xv V = u (qs + 54) ∧ Fx (preTB P qs inst out b n).1.com ∧
    (preTB P qs inst out b n).1.seg.valF xv V = u qs ∧ Fx (preTB P qs inst out b n).1.seg ∧
    vals xv V (preTB P qs inst out b n).1.lanes = eqKernel (lanePt u qs) ∧
    (∀ x ∈ (preTB P qs inst out b n).1.lanes, Fx x) ∧
    (preTB P qs inst out b n).1.carried.length = 57 + P ∧ (∀ x ∈ (preTB P qs inst out b n).1.carried, Fx x) ∧
    vals xv V (preTB P qs inst out b n).1.carried =
      carV (u (qs + 54) + u qs * ((List.range 25).map fun l =>
          (eqKernel (lanePt u qs)).getD l 0 * ((List.range 25).map fun l => (out l).valF xv V).getD l 0).sum)
        (eqKernel (((List.range (P + 4)).map fun i => (inst i).valF xv V).take 4))
        (((List.range (P + 4)).map fun i => (inst i).valF xv V).drop 4) (u qs) (eqKernel (lanePt u qs))
        ((List.range 7).map fun i => (eqKernel (lanePt u qs)).getD 0 0 * FE.ofK (FK.x ^ iotaPos i)) := by
  unfold preTB at h ⊢
  -- z, one
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ez := gZero_spec h1; have fz : Fx (gZero b n).1 := fx_emit _ _
  generalize (gZero b n).1 = z at h ez fz ⊢; generalize n + (gZero b n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eo := gOne_spec h2; have fo : Fx (gOne z n1).1 := fx_emit _ _
  rw [ez, add_zero] at eo
  generalize (gOne z n1).1 = one at h eo fo ⊢; generalize n1 + (gOne z n1).2.length = n2 at h ⊢
  -- the loads
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have es := gLoad_lv h3; have fs : Fx (gLoad qs [] n2).1 := fx_emit _ _
  rw [hu qs (by omega)] at es
  generalize (gLoad qs [] n2).1 = seg at h es fs ⊢; generalize n2 + (gLoad qs [] n2).2.length = n3 at h ⊢
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have elp : vals xv V (mapTB (fun k => gLoad (qs + 9 * (k + 1)) []) (List.range 5) n3).1 = lanePt u qs :=
    forall₂_map_eq (mapTB_spec_mem (P := fun k v => v = u (qs + 9 * (k + 1))) _
      (fun k hk m hm => by rw [gLoad_lv hm, hu _ (by have := List.mem_range.mp hk; omega)]) _ h4)
  generalize (mapTB (fun k => gLoad (qs + 9 * (k + 1)) []) (List.range 5) n3).1 = lp at h elp ⊢
  generalize n3 + (mapTB (fun k => gLoad (qs + 9 * (k + 1)) []) (List.range 5) n3).2.length = n4 at h ⊢
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ec := gLoad_lv h5; have fc : Fx (gLoad (qs + 54) [] n4).1 := fx_emit _ _
  rw [hu _ le_rfl] at ec
  generalize (gLoad (qs + 54) [] n4).1 = com at h ec fc ⊢; generalize n4 + (gLoad (qs + 54) [] n4).2.length = n5 at h ⊢
  -- the lanes
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have el := gk_eqTab_one ez eo lp n5 h6
  have fl := fx_gEqTab z lp [one] n5 (by simpa using fo)
  rw [elp] at el
  generalize (gEqTab z [one] lp n5).1 = lanes at h el fl ⊢; generalize n5 + (gEqTab z [one] lp n5).2.length = n6 at h ⊢
  have hll : lanes.length = 32 := by
    have := congrArg List.length el; rw [List.length_map, eqKernel_length] at this; simpa [lanePt] using this
  -- the value
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ed := gDot_spec _ _ _ h7
  generalize (gDot z ((List.range 25).map fun l => (lanes.getD l default, out l)) n6).1 = dt at h ed ⊢
  generalize n6 + (gDot z ((List.range 25).map fun l => (lanes.getD l default, out l)) n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ev := gMul_spec h8; have fv : Fx (gMul seg dt com n7).1 := fx_emit _ _
  generalize (gMul seg dt com n7).1 = v0 at h ev fv ⊢; generalize n7 + (gMul seg dt com n7).2.length = n8 at h ⊢
  -- `μ`
  obtain ⟨h9, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have em := gk_eqTab_one ez eo ((List.range 4).map inst) n8 h9
  have fm := fx_gEqTab z ((List.range 4).map inst) [one] n8 (by simpa using fo)
  generalize (gEqTab z [one] ((List.range 4).map inst) n8).1 = mu at h em fm ⊢
  generalize n8 + (gEqTab z [one] ((List.range 4).map inst) n8).2.length = n9 at h ⊢
  -- the flips
  obtain ⟨h10, -, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ef : vals xv V (mapTB (fun i => gScale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n9).1 =
      (List.range 7).map fun i => (eqKernel (lanePt u qs)).getD 0 0 * FE.ofK (FK.x ^ iotaPos i) :=
    forall₂_map_eq (mapTB_spec_mem (P := fun i v => v = (eqKernel (lanePt u qs)).getD 0 0 * FE.ofK (FK.x ^ iotaPos i))
      _ (fun i _ m hm => by rw [gScale_spec hm, getD_vals _ (by omega), el, mul_comm]) _ h10)
  have ffl : ∀ x ∈ (mapTB (fun i => gScale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n9).1,
      Fx x := fx_mapTB (fun _ _ => fx_emit _ _) _ _
  have hfl : (mapTB (fun i => gScale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n9).1.length = 7 := by
    rw [mapTB_length]; rfl
  generalize (mapTB (fun i => gScale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n9).1 = fls
    at ef ffl hfl ⊢
  rw [tb_pure]
  have hmu : mu.length = 16 := by
    have := congrArg List.length em; rw [List.length_map, eqKernel_length] at this; simpa using this
  refine ⟨ec, fc, es, fs, el, fl, ?_, ?_, ?_⟩
  · simp [hmu, hll, hfl]; omega
  · intro x hx
    simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hx
    rcases hx with (((((((rfl | hx) | rfl) | ⟨i, -, rfl⟩) | rfl) | hx) | hx) | hx)
    · exact fv
    · exact fm x hx
    · exact fo
    · exact hinst _
    · exact fs
    · exact fl x (List.mem_of_mem_take hx)
    · rw [List.eq_of_mem_replicate hx]; exact fz
    · exact ffl x hx
  · simp only [vals, List.map_append, List.map_cons, List.map_nil, List.map_take, List.map_replicate] at em el ef ⊢
    rw [em, el, ef, ev, ed, eo, ez, es, ec, gk_take_range_map _ (by omega : 4 ≤ P + 4), gk_drop_range_map]
    simp only [carV, List.map_map, Function.comp_def, show P + 4 - 4 = P by omega]
    have hs : (List.map (fun x => (lanes.getD x default).valF xv V * (out x).valF xv V) (List.range 25)).sum =
        (List.map (fun l => (eqKernel (lanePt u qs)).getD l 0 *
          ((List.range 25).map fun l => (out l).valF xv V).getD l 0) (List.range 25)).sum := by
      refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
      have hl' := List.mem_range.mp hl
      rw [getD_vals _ (by omega), vals, el]
      simp [List.getD_eq_getElem?_getD, hl']
    rw [hs, zero_add, add_comm (u qs * _)]


/-! ## Assertions of template programs -/

theorem tassert_bind_noA {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β)
    (hm : GNoA (m n).2) :
    TAssert xv V ((m >>= f) n).2 ↔ TAssert xv V (f (m n).1 (n + (m n).2.length)).2 := by
  rw [tassert_bind]; exact ⟨fun h => h.2, fun h => ⟨tassert_noA hm, h⟩⟩

theorem gAssert_iff {xv : Src → FE} {V : Nat → FE} {n : Nat} {a g : Src} :
    TAssert xv V (gAssert a g n).2 ↔ g.valF xv V * a.valF xv V = 0 := by
  refine ⟨gAssert_spec, fun h k hk _ => ?_⟩
  simp only [gAssert, emitA, List.length_singleton] at hk
  rw [show k = 0 by omega]; exact h

/-! ## `multilinearEval` -/

theorem gFoldPairs_spec {xv : Src → FE} {V : Nat → FE} {z r1 r : Src} (hz : z.valF xv V = 0)
    (h1 : r1.valF xv V = 1 + r.valF xv V) : ∀ (l : List Src) (n : Nat), THold xv V n (gFoldPairs z r1 r l n).2 →
      vals xv V (gFoldPairs z r1 r l n).1 = foldPairs (r.valF xv V) (vals xv V l)
  | a :: b :: rest, n, h => by
    simp only [gFoldPairs] at h ⊢
    obtain ⟨g1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
    obtain ⟨g2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
    obtain ⟨g3, -, e⟩ := tb_peel _ _ h; rw [e]; clear e
    rw [tb_pure]
    simp only [vals, List.map_cons, foldPairs] at g3 ⊢
    rw [gMul_spec g2, gMul_spec g1, hz, add_zero, h1, ← vals, gFoldPairs_spec hz h1 rest _ g3]
  | [], _, _ => rfl
  | [_], _, _ => rfl

theorem gMle_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) :
    ∀ (pt cur : List Src) (n : Nat), THold xv V n (gMle z cur pt n).2 →
      (gMle z cur pt n).1.valF xv V = multilinearEval (vals xv V cur) (vals xv V pt)
  | [], cur, n, _ => by
    simp only [gMle, tb_pure, multilinearEval, vals, List.map_nil, List.foldl_nil]
    cases cur <;> simp [hz]
  | r :: rs, cur, n, h => by
    simp only [gMle] at h ⊢
    obtain ⟨g1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
    obtain ⟨g2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
    rw [gMle_spec hz rs _ _ h, gFoldPairs_spec hz (gOne_spec g1) cur _ g2]
    simp only [multilinearEval, vals, List.map_cons, List.foldl_cons]

/-! ## The first opening block -/

/-- **The first opening block**: its exports and its check. -/
theorem fin1TB_spec {xv : Src → FE} {V : Nat → FE} {qO : Nat} {b : Src} {slot1 slot3 aF : List Src}
    {seg val1 : Src} {lanes : List Src} {u : Nat → FE}
    (hu : ∀ m, qO + 90 ≤ m → m ≤ qO + 432 → lv xv [] m = u m) (hlanes : 25 ≤ lanes.length)
    (hs1 : slot1.length = 6) {n : Nat} (h : THold xv V n (fin1TB qO b slot1 slot3 aF seg val1 lanes n).2) :
    (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.z.valF xv V = 0 ∧
    Fx (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.z ∧
    (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.word.valF xv V = u (qO + 90) ∧
    Fx (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.word ∧
    (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.sl.length = 128 ∧
    (∀ x ∈ (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.sl, Fx x) ∧
    (∀ k < 128, ((fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.sl.getD k default).valF xv V =
      u (qO + 243 + 3 * (k % 64))) ∧
    vals xv V (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.e3 = eqKernel (vals xv V slot3) ∧
    (∀ x ∈ (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.e3, Fx x) ∧
    vals xv V (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.ea = eqKernel (vals xv V aF) ∧
    (∀ x ∈ (fin1TB qO b slot1 slot3 aF seg val1 lanes n).1.ea, Fx x) ∧
    (TAssert xv V (fin1TB qO b slot1 slot3 aF seg val1 lanes n).2 ↔
      b.valF xv V * (((List.range 25).map fun l => (eqKernel (vals xv V slot1)).getD (25 + l) 0 *
        (vals xv V lanes).getD l 0).sum * (1 + seg.valF xv V) * u (qO + 90) + val1.valF xv V) = 0) := by
  unfold fin1TB at h ⊢
  -- the slices
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_mapTB (fun _ _ => gnoA_load _ _ _) _ _)]
  clear e
  have esl : ∀ k < 128, ((mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).1.getD k
      default).valF xv V = u (qO + 243 + 3 * (k % 64)) := by
    have := forall₂_map_eq (mapTB_spec_mem (P := fun k v => v = u (qO + 243 + 3 * (k % 64))) _
      (fun k hk m hm => by
        rw [gLoad_lv hm, hu _ (by omega) (by have := Nat.mod_lt k (show 0 < 64 by omega); omega)]) _ h1)
    intro k hk
    rw [getD_vals _ (by rw [mapTB_length]; simpa using hk), vals, this]
    simp [List.getD_eq_getElem?_getD, hk]
  have fsl : ∀ x ∈ (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).1, Fx x :=
    fx_mapTB (fun _ _ => fx_emit _ _) _ _
  have lsl : (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).1.length = 128 := by
    rw [mapTB_length]; rfl
  generalize (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).1 = sl at h esl fsl lsl ⊢
  generalize n + (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) n).2.length = n1 at h ⊢
  -- z, one, the word
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_zero _ _)]; clear e
  have ez := gZero_spec h2; have fz : Fx (gZero b n1).1 := fx_emit _ _
  generalize (gZero b n1).1 = z at h ez fz ⊢; generalize n1 + (gZero b n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_one _ _)]; clear e
  have eo := gOne_spec h3; have fo : Fx (gOne z n2).1 := fx_emit _ _
  rw [ez, add_zero] at eo
  generalize (gOne z n2).1 = one at h eo fo ⊢; generalize n2 + (gOne z n2).2.length = n3 at h ⊢
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_load _ _ _)]; clear e
  have ew := gLoad_lv h4; have fw : Fx (gLoad (qO + 90) [] n3).1 := fx_emit _ _
  rw [hu _ le_rfl (by omega)] at ew
  generalize (gLoad (qO + 90) [] n3).1 = word at h ew fw ⊢; generalize n3 + (gLoad (qO + 90) [] n3).2.length = n4 at h ⊢
  -- the committed check
  obtain ⟨h5, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_gEqTab _ _ _ _)]; clear e
  have e1 := gk_eqTab_one ez eo slot1 n4 h5
  generalize (gEqTab z [one] slot1 n4).1 = t1 at h e1 ⊢; generalize n4 + (gEqTab z [one] slot1 n4).2.length = n5 at h ⊢
  have ht1 : t1.length = 64 := by
    have := congrArg List.length e1; rw [List.length_map, eqKernel_length, List.length_map, hs1] at this; simpa using this
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_gDot _ _ _)]; clear e
  have ewc := gDot_spec _ _ _ h6
  generalize (gDot z ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)) n5).1 = wc
    at h ewc ⊢
  generalize n5 + (gDot z ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)) n5).2.length
    = n6 at h ⊢
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_one _ _)]; clear e
  have ef := gOne_spec h7
  generalize (gOne seg n6).1 = f at h ef ⊢; generalize n6 + (gOne seg n6).2.length = n7 at h ⊢
  obtain ⟨h8, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_mul _ _ _ _)]; clear e
  have eww := gMul_spec h8
  generalize (gMul wc f z n7).1 = w at h eww ⊢; generalize n7 + (gMul wc f z n7).2.length = n8 at h ⊢
  obtain ⟨h9, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_mul _ _ _ _)]; clear e
  have et := gMul_spec h9
  generalize (gMul w word val1 n8).1 = t at h et ⊢; generalize n8 + (gMul w word val1 n8).2.length = n9 at h ⊢
  obtain ⟨-, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind, gAssert_iff]; clear e
  generalize n9 + (gAssert t b n9).2.length = n10 at h ⊢
  -- the two tables
  obtain ⟨h11, h, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_gEqTab _ _ _ _)]; clear e
  have e3 := gk_eqTab_one ez eo slot3 n10 h11
  have f3 := fx_gEqTab z slot3 [one] n10 (by simpa using fo)
  generalize (gEqTab z [one] slot3 n10).1 = t3 at h e3 f3 ⊢
  generalize n10 + (gEqTab z [one] slot3 n10).2.length = n11 at h ⊢
  obtain ⟨h12, -, e⟩ := tb_peel _ _ h; rw [e, tassert_bind_noA _ _ (gnoA_gEqTab _ _ _ _)]; clear e
  have ea := gk_eqTab_one ez eo aF n11 h12
  have fa := fx_gEqTab z aF [one] n11 (by simpa using fo)
  generalize (gEqTab z [one] aF n11).1 = ta at ea fa ⊢
  rw [tb_pure]
  refine ⟨ez, fz, ew, fw, lsl, fsl, esl, e3, f3, ea, fa, ?_⟩
  rw [and_iff_left (tassert_noA (fun k hk => by simp at hk)), et, eww, ef, ewc, ez, add_zero, zero_add]
  have hs : ((List.map (fun cd => cd.1.valF xv V * cd.2.valF xv V)
      ((List.range 25).map fun l => (t1.getD (25 + l) default, lanes.getD l default)))).sum =
      ((List.range 25).map fun l => (eqKernel (vals xv V slot1)).getD (25 + l) 0 * (vals xv V lanes).getD l 0).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    have hl' := List.mem_range.mp hl
    simp only [Function.comp_apply]
    rw [getD_vals _ (by omega), getD_vals _ (by omega), e1]
  rw [hs, ew]


/-! ## The input check block -/

theorem fin2_lane {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {B : List Src} (hB : 25 ≤ B.length)
    (R : Nat → Src) {e3 : List Src} {x x1 : Src} (hx1 : x1.valF xv V = 1 + x.valF xv V) {l : Nat} (hl : l < 25)
    (m : Nat) (h : THold xv V m ((gLaneForm z B R l >>= fun lf => gMul (e3.getD l default) x1 z >>= fun u =>
      gMul (e3.getD (25 + l) default) x u >>= fun u' => gMul u' lf z) m).2) :
    ((gLaneForm z B R l >>= fun lf => gMul (e3.getD l default) x1 z >>= fun u =>
      gMul (e3.getD (25 + l) default) x u >>= fun u' => gMul u' lf z) m).1.valF xv V =
      ((e3.getD (25 + l) default).valF xv V * x.valF xv V + (e3.getD l default).valF xv V * (1 + x.valF xv V)) *
        laneForm (vals xv V B) (fun s => (R s).valF xv V) l := by
  obtain ⟨g1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have el := gLaneForm_spec hz hB R hl m g1
  obtain ⟨g2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  obtain ⟨g3, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  rw [gMul_spec h, gMul_spec g3, gMul_spec g2, el, hz, add_zero, add_zero, hx1]

theorem gnoA_fin2_lane (z : Src) (B : List Src) (R : Nat → Src) (e3 : List Src) (x x1 : Src) (l m : Nat) :
    GNoA ((gLaneForm z B R l >>= fun lf => gMul (e3.getD l default) x1 z >>= fun u =>
      gMul (e3.getD (25 + l) default) x u >>= fun u' => gMul u' lf z) m).2 :=
  gnoA_bind _ _ _ (gnoA_gLaneForm _ _ _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_mul _ _ _ _) (gnoA_mul _ _ _ _)))

/-- **The input check block**: its assertion. -/
theorem fin2TB_spec {xv : Src → FE} {V : Nat → FE} {b z : Src} {B : List Src} {R : Nat → Src} {e3 : List Src}
    {x : Src} {mu low : List Src} {val3 : Src} (hz : z.valF xv V = 0) (hB : 25 ≤ B.length) (he3 : 50 ≤ e3.length)
    {n : Nat} (h : THold xv V n (fin2TB b z B R e3 x mu low val3 n).2) :
    TAssert xv V (fin2TB b z B R e3 x mu low val3 n).2 ↔
      b.valF xv V * (multilinearEval (vals xv V mu) (vals xv V low) *
        ((List.range 25).map fun l => ((vals xv V e3).getD (25 + l) 0 * x.valF xv V +
          (vals xv V e3).getD l 0 * (1 + x.valF xv V)) * laneForm (vals xv V B) (fun s => (R s).valF xv V) l).sum +
        val3.valF xv V) = 0 := by
  unfold fin2TB at h ⊢
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_one _ _)]; clear e
  have ex := gOne_spec h1
  generalize (gOne x n).1 = x1 at h ex ⊢; generalize n + (gOne x n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h
  rw [tassert_bind_noA _ _ (gnoA_gSumMap _ _ (fun c m => gnoA_fin2_lane z B R e3 x x1 c m) _)]; clear e
  have et := gSumMap_spec' hz (F := fun l => ((vals xv V e3).getD (25 + l) 0 * x.valF xv V +
      (vals xv V e3).getD l 0 * (1 + x.valF xv V)) * laneForm (vals xv V B) (fun s => (R s).valF xv V) l)
    (fun l hl m hm => by
      rw [fin2_lane hz hB R ex hl m hm, getD_vals _ (by omega), getD_vals _ (by omega)]) n1 h2
  generalize (gSumMap z 25 _ n1).1 = tot at h et ⊢
  generalize n1 + (gSumMap z 25 _ n1).2.length = n2 at h ⊢
  obtain ⟨h3, h, e⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_gMle _ _ _ _)]; clear e
  have em := gMle_spec hz low mu n2 h3
  generalize (gMle z mu low n2).1 = mle at h em ⊢; generalize n2 + (gMle z mu low n2).2.length = n3 at h ⊢
  obtain ⟨h4, -, e⟩ := tb_peel _ _ h; rw [tassert_bind_noA _ _ (gnoA_mul _ _ _ _), gAssert_iff]; clear e
  rw [gMul_spec h4, em, et]

/-! ## The rotated sums -/

theorem evalF_mulI (xv : Src → FE) (V : Nat → FE) (a b d : Src) :
    (mulI a b d).evalF xv V = a.valF xv V * b.valF xv V + d.valF xv V := rfl

/-- **The rotation block**: iteration `i`'s last row is `Σ_w A(w)·cell(sb + w + i)`. -/
theorem rot_spec {c : Ctx} {M : Mem} {p : Ptr} {ea : List Src} {sb : Nat} {z : Src}
    (h : SegsHold c M p (loop [6] (tplOf (rotIns ea sb z)) p).2) {A : Nat → FE}
    (hA : ∀ w < 64, ∀ jf, (ea.getD w default).valF (iterXv M (loop [6] (tplOf (rotIns ea sb z)) p).1 jf)
      (iterF M (loop [6] (tplOf (rotIns ea sb z)) p).1 jf) = A w)
    (hz : ∀ jf, z.valF (iterXv M (loop [6] (tplOf (rotIns ea sb z)) p).1 jf)
      (iterF M (loop [6] (tplOf (rotIns ea sb z)) p).1 jf) = 0) {i : Nat} (hi : i < 64) :
    iterF M (loop [6] (tplOf (rotIns ea sb z)) p).1 i 63 =
      ((List.range 64).map fun w => A w * M.rd .E (sb + w + 1 * i)).sum := by
  have hH := thold_of_loop h (jf := i) (by simpa using hi)
  have hg : ∀ w < 64, (rotIns ea sb z).getD w default =
      mulI (ea.getD w default) (.ext ⟨.E, sb + w, [1]⟩) (if w = 0 then z else .loc (w - 1)) := by
    intro w hw; simp [rotIns, List.getD_eq_getElem?_getD, hw]
  have hx : ∀ w, iterXv M (loop [6] (tplOf (rotIns ea sb z)) p).1 i (.ext ⟨.E, sb + w, [1]⟩) =
      M.rd .E (sb + w + 1 * i) := fun w => iterXv_ext1 M _ rfl (by simpa using hi) _ _ _
  have key : ∀ w < 64, iterF M (loop [6] (tplOf (rotIns ea sb z)) p).1 i w =
      ((List.range (w + 1)).map fun w' => A w' * M.rd .E (sb + w' + 1 * i)).sum := by
    intro w
    induction w with
    | zero =>
      intro _
      have := hH 0 (by simp [rotIns]) (by rw [hg 0 (by omega)]; exact Or.inl rfl)
      rw [Nat.zero_add, hg 0 (by omega), evalF_mulI, if_pos rfl, hA 0 (by omega), hz, add_zero] at this
      rw [this]
      show A 0 * iterXv M _ i (.ext ⟨.E, sb + 0, [1]⟩) = _
      rw [hx]
      simp
    | succ w ih =>
      intro hw
      have := hH (w + 1) (by simp [rotIns]; omega) (by rw [hg _ hw]; exact Or.inl rfl)
      rw [Nat.zero_add, hg _ hw, evalF_mulI, if_neg (Nat.succ_ne_zero w), hA _ hw] at this
      rw [this, List.range_succ (n := w + 1), List.map_append, List.sum_append]
      show A (w + 1) * iterXv M _ i (.ext ⟨.E, sb + (w + 1), [1]⟩) + iterF M _ i (w + 1 - 1) = _
      rw [hx, Nat.add_sub_cancel, ih (by omega)]
      simp [add_comm]
  exact key 63 (by omega)

/-! ## The constants block -/

theorem cstI_ty (b : Src) (t : Nat) : (cstI b t).ty = .K := by unfold cstI; split <;> rfl

theorem cstI_op (b : Src) (t : Nat) : ∃ k k', (cstI b t).op = .lin k k' := by
  unfold cstI; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem cstIns_w (b : Src) : ∀ i ∈ cstIns b, Row.w .K ⟨i.op, i.ty, []⟩ = 1 := by
  intro i hi
  simp only [cstIns, List.mem_map, List.mem_range] at hi
  obtain ⟨t, -, rfl⟩ := hi
  obtain ⟨k, k', hk⟩ := cstI_op b t
  simp [Row.w, Row.writes, hk, cstI_ty]

/-- **The constants block**: cell `p.k + t` holds constant `t % 16` of iteration `t / 16`. -/
theorem cst_spec {c : Ctx} {M : Mem} {p : Ptr} {bc : Cell}
    (h : SegsHold c M p (loop [] (tplOf (cstIns (gkS bc))) p).2) {t : Nat} (ht : t < 256) :
    FE.ofK (M.k (p.k + t)) = if t % 16 = 15 then (if t / 16 < 12 then bc.val M else 0)
      else FE.ofK (cstK (t / 16) (t % 16)) := by
  have hH := thold_of_loop h (jf := 0) (by simp)
  have hg : (cstIns (gkS bc)).getD t default = cstI (gkS bc) t := by
    simp [cstIns, List.getD_eq_getElem?_getD, ht]
  have := hH t (by simp [cstIns]; omega) (by rw [hg]; obtain ⟨k, k', hk⟩ := cstI_op (gkS bc) t; exact Or.inr (Or.inl ⟨k, k', hk⟩))
  rw [Nat.zero_add, hg] at this
  have hc : iterF M (loop [] (tplOf (cstIns (gkS bc))) p).1 0 t = FE.ofK (M.k (p.k + t)) := by
    rw [gk_loop_fst]
    show Cell.val M (LoopOut.cell ⟨p, [], tplOf (cstIns (gkS bc))⟩ t 0) = _
    have hty : ((tplOf (cstIns (gkS bc))).getD t default).ty = .K := by
      rw [tplOf_getD _ (by simp [cstIns]; omega), hg]; exact cstI_ty _ _
    simp only [LoopOut.cell, hty, Cell.val, Ptr.at,
      lrank_ones (δ := cstIns (gkS bc)) (cstIns_w _) (show t ≤ (cstIns (gkS bc)).length by simp [cstIns]; omega),
      Nat.mul_zero, Nat.add_zero]
    rfl
  rw [← hc, this]
  have hb : (gkS bc).valF (iterXv M (loop [] (tplOf (cstIns (gkS bc))) p).1 0)
      (iterF M (loop [] (tplOf (cstIns (gkS bc))) p).1 0) = bc.val M := gk_iterXv_gkS M _ 0 bc
  unfold cstI
  split_ifs with h1 h2
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_zero, zero_mul, add_zero]
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_one, one_mul, add_zero, FE_add_self,
      ofK_zero]
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_one, one_mul, FE_add_self, zero_add]

theorem ofK_rcK (rc : UInt64) (i : Nat) : FE.ofK (rcK rc i) = rcBit rc i := by
  unfold rcK rcBit; split_ifs <;> rfl


/-! ## The layers -/

theorem rep_congr {P : Nat} {cv cv' : Nat → FE} {C : KeccakClaim} {f : Bool} (h : Rep P cv C f)
    (e : ∀ j < 57 + P, cv j = cv' j) : Rep P cv' C f := by
  have hB : repB P cv = repB P cv' := List.map_congr_left fun l hl => e _ (by simp at hl; omega)
  have hA : repA P cv = repA P cv' := List.map_congr_left fun l hl => e _ (by simp at hl; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← e 0 (by omega)]; exact h.value
  · rw [← h.mu]; exact (List.map_congr_left fun i hi => e _ (by simp at hi; omega)).symm
  · rw [← e 17 (by omega)]; exact h.kappa
  · rw [← h.point]; exact (List.map_congr_left fun i hi => e _ (by simp at hi; omega)).symm
  · rw [h.weights, hB, hA]
  · intro i hi; rw [← e _ (by omega), h.flips i hi, hB, hA]

/-- A relocated row's type (stated once, so that no proof leaves `relocI`/`toLRow` to the kernel's
unfolding, which would unfold the template `layIns P` first). -/
theorem relocI_toLRow_ty (q cst : Nat) (i : Ins) : (relocI q cst i).toLRow.ty = i.ty := rfl

theorem relocS_k (P q cst j : Nat) : relocS q cst ((lay0 P).k j) = .ext ⟨.K, cst + (0 + j), [16]⟩ := by
  simp [LCfg.k, lay0, relocS]

/-- The carried claim of the layer loop at iteration `k`: the copy rows before the loop (`k = 0`),
the copy rows of iteration `k − 1`. -/
def layCv (M : Mem) (o : LoopOut) (C cb : Nat) : Nat → Nat → FE
  | 0, j => M.e (o.p.e - C + j)
  | k + 1, j => (o.cell (cb + j) k).val M

/-- **The layer loop** (12 layers of `F`'s `verifyKeccakLayer`, 4 dummies): from the first claim
in the `C` cells before it, the copy rows of iteration 11 represent `F`'s claim after the 12
layers; with the gate `1`, its assertions hold iff all of `F`'s 24 layer checks do. -/
theorem layers_spec {c : Ctx} {M : Mem} {pL : Ptr} {P q cst : Nat} {sig : ByteArray} {T : Nat}
    (hP : layOk P = true) (h : SegsHold c M pL (loop [4] (layTpl P q cst) pL).2)
    (hS : Streamed M sig T) (hT : q + 12 * (lay0 P).str + 2 ≤ T) (hq : 5 ≤ q) {β : FE}
    (hcst : ∀ jf < 16, ∀ j < 16, FE.ofK (M.k (cst + (16 * jf + j))) =
      if j = 15 then (if jf < 12 then β else 0) else FE.ofK (cstK jf j))
    {C0 : KeccakClaim} (hpe : 57 + P ≤ pL.e)
    (h0 : Rep P (fun j => M.e (pL.e - (57 + P) + j)) C0 true) :
    Rep P (fun j => ((loop [4] (layTpl P q cst) pL).1.cell (cbOf P + j) 11).val M)
      (kChain (feAt sig) (P + 4) C0 (8 * q - 40) (8 * (lay0 P).str) 12) false ∧
    (β = 1 → (SegsAssert M pL (loop [4] (layTpl P q cst) pL).2 ↔
      ∀ k < 12, (kLayer (feAt sig) (P + 4) C0 (8 * q - 40) (8 * (lay0 P).str) k).ok1 = true ∧
        (kLayer (feAt sig) (P + 4) C0 (8 * q - 40) (8 * (lay0 P).str) k).ok2 = true)) := by
  have hok := hP
  simp only [layOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨hlen, hgate⟩, hsuf⟩ := hok
  have hcb : (lay0 P).cb + (lay0 P).C = (layerTB (lay0 P) 0).2.length := by
    show cbOf P + (57 + P) = (layIns P).length; rw [hlen]
  have hw : ∀ i ∈ (layIns P).drop (cbOf P), Row.w .E ⟨i.op, i.ty, []⟩ = 1 := by
    intro i hi
    have := hsuf i hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    obtain ⟨h1, h2⟩ := this
    have hwr : Row.writes ⟨i.op, i.ty, []⟩ = some .E := by
      unfold Row.writes; cases hop : i.op <;> simp_all
    simp [Row.w, hwr]
  have hrank : ∀ j ≤ 57 + P, lrank .E (layTpl P q cst) (cbOf P + j) + (57 + P) = ltw .E (layTpl P q cst) + j := by
    intro j hj; rw [layTpl, lrank_reloc, ltw_reloc]; exact lrank_suffix hlen hw hj
  have hty : ∀ j < 57 + P, ((layTpl P q cst).getD (cbOf P + j) default).ty = .E := by
    intro j hj
    rw [layTpl, tplOf_getD _ (by rw [List.length_map, hlen]; omega), reloc_getD, relocI_toLRow_ty]
    have hm : (layIns P).getD (cbOf P + j) default ∈ (layIns P).drop (cbOf P) := by
      rw [show (layIns P).getD (cbOf P + j) default = ((layIns P).drop (cbOf P)).getD j default by
        simp [List.getD_eq_getElem?_getD]]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]; exact List.getElem_mem _
    exact (hsuf _ hm).1
  -- the loop's iterations
  have hO : (loop [4] (layTpl P q cst) pL).1 = ⟨pL, [4], layTpl P q cst⟩ := rfl
  have hdims : (⟨pL, [4], layTpl P q cst⟩ : LoopOut).dims = [4] := rfl
  rw [hO]
  have hH : ∀ jf < 16, THold (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ jf (relocS q cst s))
      (iterF M ⟨pL, [4], layTpl P q cst⟩ jf) 0 (layIns P) := by
    intro jf hjf
    have := thold_of_loop (dims := [4]) (ins := (layIns P).map (relocI q cst)) (p := pL) h (jf := jf) (by simpa using hjf)
    exact thold_reloc this
  have hk : ∀ jf < 16, ∀ j < 16, (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ jf (relocS q cst s)) ((lay0 P).k j) =
      FE.ofK (M.k (cst + (16 * jf + j))) := by
    intro jf hjf j _
    show iterXv M _ jf (relocS q cst ((lay0 P).k j)) = _
    rw [relocS_k P, iterXv_ext1 M _ hdims (by simpa using hjf)]
    show FE.ofK (M.k _) = _
    congr 2; omega
  have hstr : (lay0 P).str ≠ 16 := by simp only [lay0, LCfg.str]; omega
  have hv : ∀ jf < 12, ∀ m < (lay0 P).q + (lay0 P).str,
      lv (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ jf (relocS q cst s)) [(lay0 P).str] m =
        feAt sig (8 * m + 8 * (q + (lay0 P).str * jf)) := by
    intro jf hjf m hm
    have hm' : m < (lay0 P).str := by simpa [lay0] using hm
    have e : ∀ m', (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ jf (relocS q cst s)) (.ext ⟨.K, m', [(lay0 P).str]⟩) =
        FE.ofK (M.k (q + m' + (lay0 P).str * jf)) := by
      intro m'
      show iterXv M _ jf (relocS q cst (.ext ⟨.K, m', [(lay0 P).str]⟩)) = _
      simp only [relocS, if_neg hstr]
      rw [iterXv_ext1 M _ hdims (by omega)]
      rfl
    unfold lv
    rw [e, e, e, show q + (m + 1) + (lay0 P).str * jf = q + m + (lay0 P).str * jf + 1 by omega,
      show q + (m + 2) + (lay0 P).str * jf = q + m + (lay0 P).str * jf + 2 by omega,
      load_feAt hS (by have : (lay0 P).str * jf ≤ (lay0 P).str * 11 := Nat.mul_le_mul_left _ (by omega); omega)]
    congr 1; ring
  have hpv : ∀ jf < 16, ∀ j < 57 + P, (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ jf (relocS q cst s)) ((lay0 P).pv j) =
      layCv M ⟨pL, [4], layTpl P q cst⟩ (57 + P) (cbOf P) jf j := by
    intro jf hjf j hj
    show (Opd.prev (cbOf P + j)).val M _ jf = _
    rw [Opd.val_prev M _ (by simpa using hjf)]
    have hty' := hty j hj
    have hr := hrank j hj.le
    rcases jf with _ | jf
    · show M.rd ((layTpl P q cst).getD (cbOf P + j) default).ty _ = M.e (pL.e - (57 + P) + j)
      rw [hty']
      show M.e (pL.e + lrank .E (layTpl P q cst) (cbOf P + j) - ltw .E (layTpl P q cst) + ltw .E (layTpl P q cst) * 0) = _
      generalize lrank .E (layTpl P q cst) (cbOf P + j) = a at hr ⊢
      generalize ltw .E (layTpl P q cst) = w at hr ⊢
      rw [show pL.e + a - w + w * 0 = pL.e - (57 + P) + j by omega]
    · show _ = (LoopOut.cell ⟨pL, [4], layTpl P q cst⟩ (cbOf P + j) jf).val M
      rw [LoopOut.cell_val]
      show M.rd ((layTpl P q cst).getD (cbOf P + j) default).ty _ = M.rd ((layTpl P q cst).getD (cbOf P + j) default).ty _
      rw [hty']
      show M.e (pL.e + lrank .E (layTpl P q cst) (cbOf P + j) - ltw .E (layTpl P q cst) + ltw .E (layTpl P q cst) * (jf + 1)) =
        M.e (pL.e + lrank .E (layTpl P q cst) (cbOf P + j) + ltw .E (layTpl P q cst) * jf)
      generalize lrank .E (layTpl P q cst) (cbOf P + j) = a at hr ⊢
      generalize ltw .E (layTpl P q cst) = w at hr ⊢
      rw [show pL.e + a - w + w * (jf + 1) = pL.e + a + w * jf by rw [Nat.mul_succ]; omega]
  have hrc : ∀ k < 12, ∀ i < 7,
      (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ k (relocS q cst s)) ((lay0 P).k i) =
        rcBit (keccakRC.getD (gkrDepth * 1 - k - 1) 0) i ∧
      (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ k (relocS q cst s)) ((lay0 P).k (7 + i)) =
        rcBit (keccakRC.getD (gkrDepth * 2 - k - 1) 0) i := by
    intro k hk' i hi
    rw [hk k (by omega) i (by omega), hk k (by omega) (7 + i) (by omega), hcst k (by omega) i (by omega),
      hcst k (by omega) (7 + i) (by omega), if_neg (by omega), if_neg (by omega), ← ofK_rcK, ← ofK_rcK]
    simp only [cstK, if_neg (show ¬ 12 ≤ k by omega), if_pos hi, if_neg (show ¬ 7 + i < 7 by omega),
      if_pos (show 7 + i < 14 by omega), show 7 + i - 7 = i by omega]
    constructor <;> trivial
  have hfst : ∀ k < 12, (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ k (relocS q cst s)) ((lay0 P).k 14) =
      if (k == 0) = true then 1 else 0 := by
    intro k hk'
    rw [hk k (by omega) 14 (by omega), hcst k (by omega) 14 (by omega), if_neg (by omega)]
    simp only [cstK, if_neg (show ¬ 12 ≤ k by omega), if_neg (show ¬ 14 < 7 by omega),
      if_neg (show ¬ 14 < 14 by omega)]
    cases k <;> simp <;> rfl
  have hp : ∀ k < 12, 8 * q - 40 + k * (8 * (lay0 P).str) + 40 = 8 * (lay0 P).q + 8 * (q + (lay0 P).str * k) := by
    intro k _; simp only [lay0]; rw [Nat.mul_comm k]; ring_nf; omega
  have hrep : ∀ k ≤ 12, Rep P (layCv M ⟨pL, [4], layTpl P q cst⟩ (57 + P) (cbOf P) k)
      (kChain (feAt sig) (P + 4) C0 (8 * q - 40) (8 * (lay0 P).str) k) (k == 0) := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk'
      have hR := rep_congr (ih (by omega)) (fun j hj => (hpv k (by omega) j hj).symm)
      exact (layer_spec (c := lay0 P) (hH k (by omega)) hcb hR (step := k) (by show k < 12; omega)
        (hrc k (by omega)) (hfst k (by omega)) (hv k (by omega)) (hp k (by omega))).1
  refine ⟨hrep 12 le_rfl, fun hβ => ?_⟩
  have hL : ∀ k < 12, _ := fun k hk' => layer_spec (c := lay0 P) (hH k (by omega)) hcb
    (rep_congr (hrep k (by omega)) (fun j hj => (hpv k (by omega) j hj).symm)) (step := k) (by show k < 12; omega)
    (hrc k (by omega)) (hfst k (by omega)) (hv k (by omega)) (hp k (by omega))
  have hgate0 : ∀ jf < 16, 12 ≤ jf → TAssert (fun s => iterXv M ⟨pL, [4], layTpl P q cst⟩ jf (relocS q cst s))
      (iterF M ⟨pL, [4], layTpl P q cst⟩ jf) (layIns P) := by
    intro jf hjf h12 t ht ha
    have hm : (layIns P).getD t default ∈ layIns P := by
      rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
    have hg := hgate _ hm
    simp only [ha, bne_self_eq_false, Bool.false_or, beq_iff_eq] at hg
    rw [hg]
    show (fun s => iterXv M _ jf (relocS q cst s)) ((lay0 P).k 15) * _ = 0
    rw [hk jf hjf 15 (by omega), hcst jf hjf 15 (by omega), if_pos rfl, if_neg (by omega), zero_mul]
  change SegsAssert M pL (loop [4] (tplOf ((layIns P).map (relocI q cst))) pL).2 ↔ _
  rw [segsAssert_loop_iff]
  simp only [tassert_reloc]
  constructor
  · intro hA k hk'
    exact (hL k hk').2.2.1 (hA k (by simpa using (show k < 16 by omega)))
      (by rw [show iterXv M _ k (relocS q cst ((lay0 P).k 15)) = _ from hk k (by omega) 15 (by omega),
        hcst k (by omega) 15 (by omega), if_pos rfl, if_pos hk', hβ])
  · intro hok jf hjf
    have hjf' : jf < 16 := by simpa using hjf
    by_cases hj : jf < 12
    · exact (hL jf hj).2.2.2 (hok jf hj).1 (hok jf hj).2
    · exact hgate0 jf hjf' (by omega)

/-! ## Small facts for the assembly -/

theorem gk_scSpec_length (v : Nat → FE) (count : Nat) : ∀ (p : Nat) (claim : FE) (es : List (Option FE)),
    (scSpec v count p claim es).1.length = es.length
  | _, _, [] => rfl
  | p, claim, e :: es => by simp [scSpec, gk_scSpec_length v count _ _ es]

/-- A plain sumcheck gadget's challenges and final claim are `F`'s (`sc_spec_plain`, as lists). -/
theorem gk_sc_lists {c : Ctx} {M : Mem} {p : Ptr} {D q R : Nat} {claim : Cell} {sig : ByteArray} {T : Nat}
    (hR : R ≤ 2 ^ D) (hR1 : 1 ≤ R) (hq : 5 ≤ q) (hS : Streamed M sig T)
    (hT : q + roundLanes 3 * R + 3 * 2 + 3 ≤ T) (h : SegsHold c M p (scGadget D 2 q .plain claim p).2) :
    (scSpec (feAt sig) 3 (8 * q - 40) (claim.val M) (List.replicate R none)).1 =
        (List.range R).map (fun i => ((scGadget D 2 q .plain claim p).1.cell 2 i).val M) ∧
    (scSpec (feAt sig) 3 (8 * q - 40) (claim.val M) (List.replicate R none)).2 =
        ((scGadget D 2 q .plain claim p).1.cell 5 (R - 1)).val M := by
  have hs := sc_spec_plain (d := 2) (R := R) (by omega) (scTpl_ok_2 q) hR hq hS hT h
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem
    · rw [gk_scSpec_length]; simp
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h2
      rw [List.getElem_map, List.getElem_range, (hs i h2).1, List.getD_eq_getElem _ _ h1]
  · have := (hs (R - 1) (by omega)).2
    rw [show R - 1 + 1 = R by omega, List.take_of_length_le (by simp)] at this
    exact this.symm

theorem gk_headD (l : List FE) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem gk_rho_lt (m : Nat) : rho m < 64 := by
  have h : ∀ x ∈ keccakRho, x < 64 := by decide
  unfold rho
  by_cases hm : m < keccakRho.length
  · rw [List.getD_eq_getElem _ _ hm]; exact h _ (List.getElem_mem hm)
  · rw [List.getD_eq_default _ _ (by omega)]; omega

theorem gk_laneForm_congr (B : List FE) {R R' : Nat → FE} (h : ∀ s < 64, R s = R' s) (l : Nat) :
    laneForm B R l = laneForm B R' l := by
  unfold laneForm
  rw [h _ (gk_rho_lt _)]
  have e1 : ∀ i, R (rho i) = R' (rho i) := fun i => h _ (gk_rho_lt i)
  have e2 : ∀ i, R ((rho i + 1) % 64) = R' ((rho i + 1) % 64) := fun i => h _ (Nat.mod_lt _ (by omega))
  simp only [e1, e2]

/-- The rotation block's sums are `rotSum` (`s = −i mod 64`). -/
theorem rot_reindex (A S : Nat → FE) {s : Nat} (hs : s < 64) :
    ((List.range 64).map fun w => A w * S ((w + (64 - s) % 64) % 64)).sum =
      sumE ((List.range 64).map fun z => S z * A ((z + s) % 64)) := by
  rw [← sumE_eq_sum, sumE_range, sumE_range]
  symm
  refine Finset.sum_nbij' (fun z => (z + s) % 64) (fun w => (w + (64 - s) % 64) % 64) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp only [Finset.mem_range]; omega
  · intro a _; simp only [Finset.mem_range]; omega
  · intro a ha; simp only [Finset.mem_range] at ha; omega
  · intro a ha; simp only [Finset.mem_range] at ha; omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    rw [show ((a + s) % 64 + (64 - s) % 64) % 64 = a by omega, mul_comm]

theorem gnoA_map {α : Type} (f : α → Ins) (l : List α) (h : ∀ a, (f a).op ≠ .assert0) : GNoA (l.map f) := by
  intro k hk
  rw [List.getD_eq_getElem _ _ hk, List.getElem_map]; exact h _

theorem gnoA_preTB (P qs : Nat) (inst out : Nat → Src) (b : Src) (n : Nat) : GNoA (preTB P qs inst out b n).2 := by
  unfold preTB
  exact gnoA_bind _ _ _ (gnoA_zero _ _) (gnoA_bind _ _ _ (gnoA_one _ _) (gnoA_bind _ _ _ (gnoA_load _ _ _)
    (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_load _ _ _) _ _) (gnoA_bind _ _ _ (gnoA_load _ _ _)
    (gnoA_bind _ _ _ (gnoA_gEqTab _ _ _ _) (gnoA_bind _ _ _ (gnoA_gDot _ _ _) (gnoA_bind _ _ _ (gnoA_mul _ _ _ _)
    (gnoA_bind _ _ _ (gnoA_gEqTab _ _ _ _) (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_lin _ _ _ _ _) _ _)
    (gnoA_pure _ _))))))))))

/-! ## The layers of `vkSpec` as the chain -/

theorem vk_layers (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p : Nat) (ok : Bool) :
    (layersSpec v ls (List.range gkrDepth) C₀ p ok).1 = kChain v ls C₀ p (2928 + 120 * C₀.point.length) 12 ∧
    (layersSpec v ls (List.range gkrDepth) C₀ p ok).2.1 = p + 12 * (2928 + 120 * C₀.point.length) ∧
    ((layersSpec v ls (List.range gkrDepth) C₀ p ok).2.2 = true ↔ ok = true ∧
      ∀ k < 12, (kLayer v ls C₀ p (2928 + 120 * C₀.point.length) k).ok1 = true ∧
        (kLayer v ls C₀ p (2928 + 120 * C₀.point.length) k).ok2 = true) := by
  have hr : List.range gkrDepth = List.range' 0 12 := by rw [List.range_eq_range']; rfl
  have h1 := layersSpec_chain v ls C₀ p 12 0 ok
  have h2 := layersSpec_ok v ls C₀ p (2928 + 120 * C₀.point.length)
    (fun k => by rw [kLayer, gk_layerSpec_pos, kChain_point]; ring) 12 0 ok
  simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h1 h2
  rw [hr]
  exact ⟨congrArg Prod.fst h1, congrArg (fun x => x.2.1) h1, h2⟩


theorem gkS_valF (M : Mem) (o : LoopOut) (jf : Nat) (V : Nat → FE) (c : Cell) :
    (gkS c).valF (iterXv M o jf) V = c.val M := gk_iterXv_gkS M o jf c

theorem firstClaim_point_length {instV seg lp outV : List FE} {com : FE} {P : Nat} (h : instV.length = P + 4)
    (hs : seg.length = 1) : (keccakFirstClaim instV seg lp outV com).point.length = P + 1 := by
  show (instV.drop 4 ++ seg).length = P + 1
  rw [List.length_append, List.length_drop, h, hs]; omega

theorem gk_bind_fst {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := rfl

theorem gk_getPtr (p : Ptr) : getPtr p = (p, []) := rfl

/-! The same three equations as proof-producing `simp` rules: as `rfl` lemmas `simp` applies them
definitionally and leaves the kernel to re-derive each step by unfolding `>>=` (it then compares
the gadget's blocks and unfolds the layer template; 30 s). Stated with a proof that is not `rfl`,
`simp` cites them and the kernel only instantiates them. -/

theorem gk_bind_fst_eq {α β : Type} (m : BM α) (f : α → BM β) (p : Ptr) :
    ((m >>= f) p).1 = (f (m p).1 (p.adv (m p).2)).1 := (gk_bind_fst m f p).trans rfl

theorem gk_getPtr_eq (p : Ptr) : getPtr p = (p, []) := (gk_getPtr p).trans rfl

theorem gk_pure_apply_eq {α : Type} (x : α) (p : Ptr) : (pure x : BM α) p = (x, []) := (pure_apply x p).trans rfl

theorem gk_lv_fix {M : Mem} {sig : ByteArray} {T : Nat} (hS : Streamed M sig T) (o : LoopOut) (jf m : Nat)
    (hm : m + 2 < T) : lv (iterXv M o jf) [] m = feAt sig (8 * m) := by
  unfold lv; rw [gk_iterXv_fix, gk_iterXv_fix, gk_iterXv_fix]; exact load_feAt hS hm

theorem gk_fx_gkS (c : Cell) : Fx (gkS c) := Or.inr ⟨c.ty, c.n, rfl⟩

theorem cpIns_w (l : List Src) : ∀ i ∈ cpIns l, Row.w .E ⟨i.op, i.ty, []⟩ = 1 := by
  intro i hi
  simp only [cpIns, List.mem_map] at hi
  obtain ⟨a, -, rfl⟩ := hi
  rfl

/-- The copy block: copy `j` is in cell `p.e + j` and holds the carried value `j`. -/
theorem cp_spec {c : Ctx} {M : Mem} {p : Ptr} {l : List Src} {o : LoopOut}
    (h : SegsHold c M p (loop [] (tplOf (cpIns (l.map (Src.gkOut o)))) p).2) (hl : ∀ x ∈ l, Fx x) {j : Nat}
    (hj : j < l.length) : M.e (p.e + j) = (vals (iterXv M o 0) (iterF M o 0) l).getD j 0 := by
  have hH := thold_of_loop h (jf := 0) (by simp)
  have hg : (cpIns (l.map (Src.gkOut o))).getD j default = linI 0 0 ((l.getD j default).gkOut o)
      ((l.getD j default).gkOut o) := by
    simp [cpIns, List.getD_eq_getElem?_getD, hj, List.getD_eq_getElem _ _ hj]
  have := hH j (by simp [cpIns]; omega) (by rw [hg]; exact Or.inr (Or.inl ⟨0, 0, rfl⟩))
  rw [Nat.zero_add, hg] at this
  simp only [Ins.evalF, linI, List.getD_cons_zero, List.getD_cons_succ, ofK_zero, zero_mul, add_zero] at this
  have hc : iterF M (loop [] (tplOf (cpIns (l.map (Src.gkOut o)))) p).1 0 j = M.e (p.e + j) := by
    rw [gk_loop_fst]
    show Cell.val M (LoopOut.cell ⟨p, [], tplOf (cpIns (l.map (Src.gkOut o)))⟩ j 0) = _
    have hty : ((tplOf (cpIns (l.map (Src.gkOut o)))).getD j default).ty = .E := by
      rw [tplOf_getD _ (by simp [cpIns]; omega), hg]; rfl
    simp only [LoopOut.cell, hty, Cell.val, Ptr.at,
      lrank_ones (δ := cpIns (l.map (Src.gkOut o))) (cpIns_w _) (show j ≤ (cpIns (l.map (Src.gkOut o))).length by
        simp [cpIns]; omega), Nat.mul_zero, Nat.add_zero]
    rfl
  rw [← hc, this, ← getD_vals _ hj, gkOut_val M o _ 0 _ (hl _ (by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj))]

/-! ## `F`'s `verifyKeccak` in the gadget's coordinates -/

section vk

variable (v : Nat → FE) (P qs : Nat) (instV outV : List FE)

/-- `F`'s first claim, the segment challenge at lane `qs`. -/
def vkC0 : KeccakClaim :=
  keccakFirstClaim instV [v (8 * qs)] ((List.range 5).map fun k => v (8 * (qs + 9 * (k + 1)))) outV (v (8 * (qs + 54)))

/-- `F`'s claim after the 12 layers. -/
def vkCf : KeccakClaim := kChain v (P + 4) (vkC0 v qs instV outV) (8 * (qs + 57) - 40) (8 * (lay0 P).str) 12

/-- `F`'s committed open. -/
def vkO1 : List FE × List FE × FE :=
  openSpec v (P + 4) (vkC0 v qs instV outV) 1 1 (v (8 * (qs + 54))) (8 * gkrQO P qs - 40)

/-- `F`'s instance sumcheck. -/
def vkLw : List FE × FE :=
  scSpec v 3 (8 * (gkrQO P qs + 93) - 40) (vkCf v P qs instV outV).value (List.replicate 4 none)

/-- `F`'s input open. -/
def vkO2 : List FE × List FE × FE :=
  openSpec v (P + 4) (vkCf v P qs instV outV) 0 2 (vkLw v P qs instV outV).2 (8 * (gkrQO P qs + 153) - 40)

/-- `F`'s slices. -/
def vkSl : List FE := (List.range 64).map fun k => v (8 * (gkrQO P qs + 243 + 3 * k))

end vk

/-- **`vkSpec` in the gadget's coordinates** (first FS answer at lane `qs`): outputs, position, checks. -/
theorem vk_facts (v : Nat → FE) (P qs : Nat) (instV outV : List FE) (ok : Bool) (hq : 5 ≤ qs)
    (hinst : instV.length = P + 4) :
    (vkSpec v (P + 4) instV outV (8 * qs - 40) ok).1 =
      ⟨instV.take 4 ++ instV.drop 4 ++ (vkO1 v P qs instV outV).1, v (8 * (gkrQO P qs + 90)),
        (vkLw v P qs instV outV).1 ++ (vkCf v P qs instV outV).point.take P ++ (vkO2 v P qs instV outV).1,
        vkSl v P qs⟩ ∧
    (vkSpec v (P + 4) instV outV (8 * qs - 40) ok).2.2 + 24 * kBits = 8 * gkrEnd P qs - 40 ∧
    ((vkSpec v (P + 4) instV outV (8 * qs - 40) ok).2.1 = true ↔
      (multilinearEval (vkCf v P qs instV outV).mu (vkLw v P qs instV outV).1 *
          dot (vkO2 v P qs instV outV).2.1 (vkSl v P qs) == (vkO2 v P qs instV outV).2.2) = true ∧
        ((vkO1 v P qs instV outV).2.1.headD 0 * v (8 * (gkrQO P qs + 90)) == (vkO1 v P qs instV outV).2.2) = true ∧
        ok = true ∧ ∀ k < 12,
          (kLayer v (P + 4) (vkC0 v qs instV outV) (8 * (qs + 57) - 40) (8 * (lay0 P).str) k).ok1 = true ∧
          (kLayer v (P + 4) (vkC0 v qs instV outV) (8 * (qs + 57) - 40) (8 * (lay0 P).str) k).ok2 = true) := by
  have hpl := firstClaim_point_length (seg := [v (8 * qs)]) (lp := (List.range 5).map fun k => v (8 * (qs + 9 * (k + 1))))
    (outV := outV) (com := v (8 * (qs + 54))) hinst rfl
  have e1 : sampAt v (8 * qs - 40) segmentBits = [v (8 * qs)] := by
    simp only [sampAt, segmentBits, List.range_one, List.map_cons, List.map_nil]; congr 2; omega
  have e2 : sampAt v (8 * qs - 40 + 72) laneBits = (List.range 5).map fun k => v (8 * (qs + 9 * (k + 1))) := by
    simp only [sampAt, laneBits]; exact List.map_congr_left fun k _ => by congr 1; omega
  have e3 : v (8 * qs - 40 + 472) = v (8 * (qs + 54)) := by congr 1; omega
  have hL := vk_layers v (P + 4) (vkC0 v qs instV outV) (8 * qs - 40 + 456) ok
  rw [show (vkC0 v qs instV outV).point.length = P + 1 from hpl, show 8 * qs - 40 + 456 = 8 * (qs + 57) - 40 by omega,
    show 2928 + 120 * (P + 1) = 8 * (lay0 P).str by simp only [lay0, LCfg.str]; ring] at hL
  have hpL : 8 * (qs + 57) - 40 + 12 * (8 * (lay0 P).str) = 8 * gkrQO P qs - 40 := by
    simp only [gkrQO]; omega
  rw [hpL] at hL
  simp only [vkSpec, e1, e2, e3]
  rw [show 8 * qs - 40 + 456 = 8 * (qs + 57) - 40 by omega,
    show keccakFirstClaim instV [v (8 * qs)] ((List.range 5).map fun k => v (8 * (qs + 9 * (k + 1)))) outV
      (v (8 * (qs + 54))) = vkC0 v qs instV outV from rfl, hL.1, hL.2.1]
  simp only [show 8 * gkrQO P qs - 40 + 760 = 8 * (gkrQO P qs + 90) by omega,
    show 8 * gkrQO P qs - 40 + 744 = 8 * (gkrQO P qs + 93) - 40 by omega,
    show 8 * gkrQO P qs - 40 + 1224 = 8 * (gkrQO P qs + 153) - 40 by omega,
    show P + 4 - 4 = P by omega, kBits, gkrSegments, show 2 - 1 = 1 from rfl,
    show kChain v (P + 4) (vkC0 v qs instV outV) (8 * (qs + 57) - 40) (8 * (lay0 P).str) 12 = vkCf v P qs instV outV
      from rfl,
    show openSpec v (P + 4) (vkC0 v qs instV outV) 1 1 (v (8 * (qs + 54))) (8 * gkrQO P qs - 40) =
      vkO1 v P qs instV outV from rfl,
    show scSpec v 3 (8 * (gkrQO P qs + 93) - 40) (vkCf v P qs instV outV).value (List.replicate 4 none) =
      vkLw v P qs instV outV from rfl,
    show openSpec v (P + 4) (vkCf v P qs instV outV) 0 2 (vkLw v P qs instV outV).2 (8 * (gkrQO P qs + 153) - 40) =
      vkO2 v P qs instV outV from rfl,
    show scalarsAt v (8 * gkrQO P qs - 40 + 1984) 64 = vkSl v P qs by
      simp only [scalarsAt, vkSl]; funext; exact List.map_congr_left fun k _ => by congr 1; omega]
  refine ⟨trivial, by simp only [gkrEnd]; omega, ?_⟩
  rw [Bool.and_eq_true, Bool.and_eq_true, hL.2.2]

/-! ## The two opening checks -/

theorem gk_fe_beq (x y : FE) : (x == y) = true ↔ x = y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  show ((a0 == b0 && a1 == b1) && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem gk_add_eq_zero (x y : FE) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x + (y + y) := by rw [FE_add_self, add_zero]
      _ = (x + y) + y := by ring
      _ = y := by rw [h, zero_add]
  · intro h; rw [h, FE_add_self]

/-- `F`'s committed-open weight: `Σ_l eq(slot, 25 + l)·(1 + seg)·lanes_l`. -/
theorem vk_c1 (v : Nat → FE) (P qs : Nat) (instV outV : List FE) (hinst : instV.length = P + 4) :
    (vkO1 v P qs instV outV).2.1.headD 0 =
      ((List.range 25).map fun l => eqAt (vkO1 v P qs instV outV).1 (25 + l) *
        (eqKernel ((List.range 5).map fun k => v (8 * (qs + 9 * (k + 1))))).getD l 0).sum * (1 + v (8 * qs)) := by
  have hs : (vkO1 v P qs instV outV).1.length = 6 := by
    simp only [vkO1, openSpec]; rw [gk_scSpec_length]; rfl
  rw [gk_headD]
  show ((foldAllE (vkO1 v P qs instV outV).1 (keccakSlotWeights (P + 4) (vkC0 v qs instV outV) 1 1)).headD []).getD 0 0 = _
  rw [open_committed_first (P + 4) (vkC0 v qs instV outV) _ (keccakFirstClaim_weights _ _ _ _ _) hs]
  have hd : (vkC0 v qs instV outV).point.drop (P + 4 - 4) = [v (8 * qs)] := by
    show (instV.drop 4 ++ [v (8 * qs)]).drop (P + 4 - 4) = _
    rw [List.drop_append, List.drop_drop, show 4 + (P + 4 - 4) = instV.length by omega, List.drop_length,
      List.nil_append, List.length_drop, show P + 4 - 4 - (instV.length - 4) = 0 by omega, List.drop_zero]
  rw [hd, gk_eqKernel_one, sumE_eq_sum, ← List.sum_map_mul_right]
  simp only [List.getD_cons_zero]
  try exact congrArg List.sum (List.map_congr_left fun l _ => by ring)

/-- The input open's sum over the two segments, per lane. -/
theorem sum2_lanes (e : Nat → FE) (x : FE) (lf : Nat → FE) :
    sumE ((List.range 2).map fun s => sumE ((List.range 25).map fun l => e (25 * s + l) * [1 + x, x].getD s 0 * lf l)) =
      ((List.range 25).map fun l => (e (25 + l) * x + e l * (1 + x)) * lf l).sum := by
  rw [sumE_range, ← sumE_eq_sum, sumE_range, Finset.sum_range_succ, Finset.sum_range_one, sumE_range, sumE_range,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  ring

/-! ## The first opening block's slices -/

theorem fin1_sl (qO : Nat) (b : Src) (slot1 slot3 aF : List Src) (seg val1 : Src) (lanes : List Src) :
    (fin1TB qO b slot1 slot3 aF seg val1 lanes 0).1.sl = (List.range 128).map (fun i => Src.loc (0 + i)) ∧
    (fin1TB qO b slot1 slot3 aF seg val1 lanes 0).2 =
      (List.range 128).map (fun k => loadI (qO + 243 + 3 * (k % 64)) []) ++
        ((fin1TB qO b slot1 slot3 aF seg val1 lanes 0).2.drop 128) := by
  have e := mapTB_emit (fun k => loadI (qO + 243 + 3 * (k % 64)) []) (List.range 128) 0
  have h1 : (fin1TB qO b slot1 slot3 aF seg val1 lanes 0).1.sl =
      (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) 0).1 := rfl
  have h2 : (fin1TB qO b slot1 slot3 aF seg val1 lanes 0).2 =
      (mapTB (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) (List.range 128) 0).2 ++ _ := rfl
  rw [show (fun k => gLoad (qO + 243 + 3 * (k % 64)) []) = fun k => emit (loadI (qO + 243 + 3 * (k % 64)) []) from rfl,
    e] at h1 h2
  refine ⟨by rw [h1]; simp, ?_⟩
  rw [h2]
  congr 1

theorem gk_getD_insApp {A B : List Ins} {k : Nat} (h : k < A.length) : (A ++ B).getD k default = A.getD k default := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- A cell of a straight block whose first rows are loads: row `k` is `E` cell `p.e + k`. -/
theorem f1_cell (M : Mem) (p : Ptr) {δ L : List Ins} (hδ : δ = L ++ δ.drop L.length)
    (hL : ∀ i ∈ L, i.ty = .E ∧ i.op = .loadE) {k : Nat} (hk : k < L.length) :
    iterF M ⟨p, [], tplOf δ⟩ 0 k = M.e (p.e + k) := by
  have hw : ∀ i ∈ L, Row.w .E ⟨i.op, i.ty, []⟩ = 1 := by
    intro i hi; obtain ⟨h1, h2⟩ := hL i hi; simp [Row.w, Row.writes, h1, h2]
  have hlr : lrank .E (tplOf δ) k = k := by
    rw [hδ, lrank_append_le _ _ _ hk.le, lrank_ones hw hk.le]
  have hty : ((tplOf δ).getD k default).ty = .E := by
    have hk' : k < δ.length := by rw [hδ, List.length_append]; omega
    rw [tplOf_getD _ hk']
    show (δ.getD k default).ty = _
    rw [hδ, gk_getD_insApp hk]
    exact (hL _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)).1
  show Cell.val M (LoopOut.cell ⟨p, [], tplOf δ⟩ k 0) = _
  simp only [LoopOut.cell, hty, hlr, Cell.val, Ptr.at, Nat.mul_zero, Nat.add_zero]
  rfl

/-! ## `openSpec`'s components (stated by `simp`, never by unfolding in a big context) -/

theorem openSpec_fst (v : Nat → FE) (ls : Nat) (claim : KeccakClaim) (first count : Nat) (value : FE) (p : Nat) :
    (openSpec v ls claim first count value p).1 = (scSpec v 3 p value (List.replicate 6 none)).1 := by
  simp only [openSpec, keccakSlotBits, slotLog]

theorem openSpec_snd2 (v : Nat → FE) (ls : Nat) (claim : KeccakClaim) (first count : Nat) (value : FE) (p : Nat) :
    (openSpec v ls claim first count value p).2.2 = (scSpec v 3 p value (List.replicate 6 none)).2 := by
  simp only [openSpec, keccakSlotBits, slotLog]

theorem openSpec_snd1 (v : Nat → FE) (ls : Nat) (claim : KeccakClaim) (first count : Nat) (value : FE) (p : Nat) :
    (openSpec v ls claim first count value p).2.1 =
      (foldAllE (openSpec v ls claim first count value p).1 (keccakSlotWeights ls claim first count)).headD [] := by
  simp only [openSpec, keccakSlotBits, slotLog]; rfl

/-! ## The assembly -/

theorem gk_vals_gkS (M : Mem) (o : LoopOut) (jf : Nat) (V : Nat → FE) (f : Nat → Cell) (l : List Nat) :
    vals (iterXv M o jf) V (l.map fun i => gkS (f i)) = l.map fun i => (f i).val M := by
  simp only [vals, List.map_map, Function.comp_def, gkS_valF]

set_option maxHeartbeats 400000 in
/-- **The gadget's blocks, assembled**: its output cells are `F`'s values (`vkO1`, `vkLw`, `vkCf`,
`vkO2`, `vkSl`) and, with the gate `1`, its assertions hold iff `F`'s two opening checks and the 24
layer checks do. (The proof unfolds the whole gadget once: 211 k heartbeats.) -/
theorem gkr_core {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → Cell} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T)
    (hT : gkrEnd P qs ≤ T) (h : SegsHold c M p (gkrGadget P qs inst out b p).2) :
    (gkrGadget P qs inst out b p).1.vals M =
      ⟨((List.range (P + 4)).map fun i => (inst i).val M).take 4 ++
          ((List.range (P + 4)).map fun i => (inst i).val M).drop 4 ++
          (vkO1 (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).1,
        feAt sig (8 * (gkrQO P qs + 90)),
        (vkLw (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).1 ++
          (vkCf (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).point.take P ++
          (vkO2 (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).1,
        vkSl (feAt sig) P qs⟩ ∧
    (b.val M = 1 → (SegsAssert M p (gkrGadget P qs inst out b p).2 ↔
      (multilinearEval (vkCf (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).mu
          (vkLw (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).1 *
          dot (vkO2 (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).2.1 (vkSl (feAt sig) P qs) ==
        (vkO2 (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).2.2) = true ∧
      ((vkO1 (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).2.1.headD 0 * feAt sig (8 * (gkrQO P qs + 90)) ==
        (vkO1 (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)).2.2) = true ∧
      ∀ k < 12,
        (kLayer (feAt sig) (P + 4) (vkC0 (feAt sig) qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)) (8 * (qs + 57) - 40) (8 * (lay0 P).str) k).ok1 = true ∧
        (kLayer (feAt sig) (P + 4) (vkC0 (feAt sig) qs ((List.range (P + 4)).map fun i => (inst i).val M)
            ((List.range 25).map fun l => (out l).val M)) (8 * (qs + 57) - 40) (8 * (lay0 P).str) k).ok2 = true)) := by
  generalize hinstV : ((List.range (P + 4)).map fun i => (inst i).val M) = instV
  generalize houtV : ((List.range 25).map fun l => (out l).val M) = outV
  have hTq : gkrQO P qs + 435 ≤ T := hT
  have hstr : (lay0 P).str = 366 + 15 * (P + 1) := rfl
  have hqO : gkrQO P qs = qs + 57 + 12 * (lay0 P).str := rfl
  simp only [gkrGadget, hold_bind, assert_bind, gk_bind_fst_eq, gk_pure_apply_eq, gk_getPtr_eq, Ptr.adv_nil] at h ⊢
  obtain ⟨-, hK, hPre, hCp, hLay, hS1, hS2, hS3, hF1, hRot, hF2, -⟩ := h
  -- the constants
  have hcst : ∀ jf < 16, ∀ j < 16, FE.ofK (M.k (p.k + (16 * jf + j))) =
      if j = 15 then (if jf < 12 then b.val M else 0) else FE.ofK (cstK jf j) := by
    intro jf hjf j hj
    rw [cst_spec hK (t := 16 * jf + j) (by omega), show (16 * jf + j) % 16 = j by omega,
      show (16 * jf + j) / 16 = jf by omega]
  have hAK : SegsAssert M p (loop [] (tplOf (cstIns (gkS b))) p).2 :=
    segsAssert_loop_iff.mpr fun _ _ => tassert_noA (gnoA_map _ _ fun t => by
      obtain ⟨k, k', hk⟩ := cstI_op (gkS b) t; rw [hk]; exact Lvm.Loop.Op.noConfusion)
  generalize p.adv (loop [] (tplOf (cstIns (gkS b))) p).2 = p1 at hPre hCp hLay hS1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the first claim
  have hpre0 := thold_of_loop hPre (jf := 0) (by simp)
  rw [gk_loop_fst] at hpre0
  obtain ⟨ec, fc, es, fs, el, fl, lc, fcar, ecar⟩ := preTB_spec (u := fun m => feAt sig (8 * m))
    (fun m hm => gk_lv_fix hS _ 0 m (by omega)) (fun i => gk_fx_gkS (inst i)) hpre0
  have hAPre := (segsAssert_loop_iff (M := M) (dims := []) (p := p1)).mpr fun _ _ => tassert_noA (gnoA_preTB P qs
    (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0)
  simp only [gkS_valF, hinstV, houtV] at ecar
  set preT := preTB P qs (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0 with hpreT
  simp only [gk_loop_fst] at hCp hLay hS1 hS2 hS3 hF1 hRot hF2 ⊢
  generalize p1.adv (loop [] (tplOf preT.2) p1).2 = p2 at hCp hLay hS1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the copies
  have hcopy : ∀ j < 57 + P, M.e (p2.e + j) =
      (vals (iterXv M ⟨p1, [], tplOf preT.2⟩ 0) (iterF M ⟨p1, [], tplOf preT.2⟩ 0) preT.1.carried).getD j 0 :=
    fun j hj => cp_spec hCp fcar (by rw [lc]; exact hj)
  set cpL := cpIns (preT.1.carried.map (Src.gkOut ⟨p1, [], tplOf preT.2⟩)) with hcpL
  have hp3 : (p2.adv (loop [] (tplOf cpL) p2).2).e = p2.e + (57 + P) := by
    rw [gk_adv_loop, ltw_ones (cpIns_w _)]; simp [cpL, cpIns, lc]
  have hACp : SegsAssert M p2 (loop [] (tplOf cpL) p2).2 :=
    segsAssert_loop_iff.mpr fun _ _ => tassert_noA (gnoA_map _ _ fun _ => by simp [linI])
  generalize p2.adv (loop [] (tplOf cpL) p2).2 = p3 at hp3 hLay hS1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the first claim, carried
  have hfl : ∀ i < 7, ((List.range 7).map fun i => (eqKernel (lanePt (fun m => feAt sig (8 * m)) qs)).getD 0 0 *
      FE.ofK (FK.x ^ iotaPos i)).getD i 0 =
      (eqKernel (lanePt (fun m => feAt sig (8 * m)) qs)).getD 0 0 * FE.ofK (FK.x ^ iotaPos i) := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hi]
  have hr := rep_first P (instV := instV) (lp := lanePt (fun m => feAt sig (8 * m)) qs) (out := outV)
    (by rw [← hinstV]; simp) (by simp [lanePt]) (by rw [← houtV]; simp) hfl (feAt sig (8 * qs))
    (feAt sig (8 * (qs + 54)))
  have h0 : Rep P (fun j => M.e (p3.e - (57 + P) + j)) (vkC0 (feAt sig) qs instV outV) true :=
    rep_congr hr fun j hj => by
      rw [hp3, show p2.e + (57 + P) - (57 + P) + j = p2.e + j by omega, hcopy j hj, ecar]
  -- the layers
  obtain ⟨hrep, hlayA⟩ := layers_spec (C0 := vkC0 (feAt sig) qs instV outV) hP hLay hS
    (by rw [hqO] at hTq; omega) (by omega) hcst (by omega) h0
  simp only [gk_loop_fst] at hrep
  generalize p3.adv (loop [4] (layTpl P (qs + 57) p.k) p3).2 = p4 at hS1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the committed open's sumcheck
  have hcl1 : (preT.1.com.gkCell ⟨p1, [], tplOf preT.2⟩).val M = feAt sig (8 * (qs + 54)) := by
    rw [gkCell_val M _ fc, ec]
  obtain ⟨hc1, hv1⟩ := gk_sc_lists (D := 3) (R := 6) (by norm_num) (by norm_num) (by omega) hS
    (by simp only [roundLanes]; omega) hS1
  rw [hcl1] at hc1 hv1
  generalize p4.adv (scGadget 3 2 (gkrQO P qs) .plain (preT.1.com.gkCell ⟨p1, [], tplOf preT.2⟩) p4).2 = p5
    at hS2 hS3 hF1 hRot hF2 ⊢
  generalize (scGadget 3 2 (gkrQO P qs) .plain (preT.1.com.gkCell ⟨p1, [], tplOf preT.2⟩) p4).1 = sc1
    at hc1 hv1 hS2 hS3 hF1 hRot hF2 ⊢
  -- the instance sumcheck
  have hcl2 : ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P) 11).val M =
      (vkCf (feAt sig) P qs instV outV).value := hrep.value
  obtain ⟨hc2, hv2⟩ := gk_sc_lists (D := 2) (R := 4) (by norm_num) (by norm_num) (by omega) hS
    (by simp only [roundLanes]; omega) hS2
  rw [hcl2] at hc2 hv2
  generalize p5.adv (scGadget 2 2 (gkrQO P qs + 93) .plain ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell
    (cbOf P) 11) p5).2 = p6 at hS3 hF1 hRot hF2 ⊢
  generalize (scGadget 2 2 (gkrQO P qs + 93) .plain ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell
    (cbOf P) 11) p5).1 = sc2 at hc2 hv2 hS3 hF1 hRot hF2 ⊢
  -- the input open's sumcheck
  obtain ⟨hc3, hv3⟩ := gk_sc_lists (D := 3) (R := 6) (by norm_num) (by norm_num) (by omega) hS
    (by simp only [roundLanes]; omega) hS3
  rw [show 4 - 1 = 3 from rfl] at hv2
  rw [← hv2] at hc3 hv3
  generalize p6.adv (scGadget 3 2 (gkrQO P qs + 153) .plain (sc2.cell 5 3) p6).2 = p7 at hF1 hRot hF2 ⊢
  generalize (scGadget 3 2 (gkrQO P qs + 153) .plain (sc2.cell 5 3) p6).1 = sc3 at hc3 hv3 hF1 hRot hF2 ⊢
  -- the first opening block
  set G := fin1TB (gkrQO P qs) (gkS b) (List.map (fun i => gkS (sc1.cell 2 i)) (List.range 6))
    (List.map (fun i => gkS (sc3.cell 2 i)) (List.range 6))
    (List.map (fun i => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 44 + P + i) 11))
      (List.range 6))
    (Src.gkOut ⟨p1, [], tplOf preT.2⟩ preT.1.seg) (gkS (sc1.cell 5 5))
    (List.map (Src.gkOut ⟨p1, [], tplOf preT.2⟩) preT.1.lanes) 0 with hG
  have hll : preT.1.lanes.length = 32 := by
    have := congrArg List.length el; simp only [vals, List.length_map, eqKernel_length, lanePt, List.length_range] at this
    simpa using this
  have hf10 := thold_of_loop hF1 (jf := 0) (by simp)
  rw [gk_loop_fst] at hf10
  obtain ⟨ez, fz, ew, fw, lsl, fsl, esl, e3, f3, ea, fa, hA1⟩ := fin1TB_spec (u := fun m => feAt sig (8 * m))
    (fun m _ h2 => gk_lv_fix hS _ 0 m (by omega)) (by simp [hll]) (by simp) hf10
  obtain ⟨hsl1, hsl2⟩ := fin1_sl (gkrQO P qs) (gkS b) (List.map (fun i => gkS (sc1.cell 2 i)) (List.range 6))
    (List.map (fun i => gkS (sc3.cell 2 i)) (List.range 6))
    (List.map (fun i => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 44 + P + i) 11))
      (List.range 6))
    (Src.gkOut ⟨p1, [], tplOf preT.2⟩ preT.1.seg) (gkS (sc1.cell 5 5))
    (List.map (Src.gkOut ⟨p1, [], tplOf preT.2⟩) preT.1.lanes)
  rw [← hG] at hsl1 hsl2
  have hslc : ∀ k < 128, M.e (p7.e + k) = feAt sig (8 * (gkrQO P qs + 243 + 3 * (k % 64))) := by
    intro k hk
    have := esl k hk
    rw [hsl1, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range, Nat.zero_add] at this
    rw [← f1_cell M p7 hsl2 (fun i hi => by simp at hi; obtain ⟨a, -, rfl⟩ := hi; exact ⟨rfl, rfl⟩)
      (by simpa using hk)]
    exact this
  generalize p7.adv (loop [] (tplOf G.2) p7).2 = p8 at hRot hF2 ⊢
  -- the carried values after the layers
  set cv : Nat → FE := fun j => ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + j) 11).val M with hcv
  have hcvA : vals (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0)
      (List.map (fun i => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 44 + P + i) 11))
        (List.range 6)) = repA P cv := by
    simp only [vals, List.map_map, repA]
    refine List.map_congr_left fun i _ => ?_
    -- `rw`, not `simp`: as a definitional step the kernel unfolds `Src.valF` before `∘` (6 s)
    rw [Function.comp_apply]
    simp only [gkS_valF, hcv]
    rw [show cbOf P + 44 + P + i = cbOf P + (44 + P + i) by omega]
  -- the rotation block
  set rotT := tplOf (rotIns (List.map (Src.gkOut ⟨p7, [], tplOf G.2⟩) G.1.ea) p7.e (Src.gkOut ⟨p7, [], tplOf G.2⟩ G.1.z))
    with hrotT
  have hea64 : G.1.ea.length = 64 := by
    have := congrArg List.length ea
    simp only [vals, List.length_map, eqKernel_length, List.length_range] at this
    simpa using this
  have hrot : ∀ i < 64, iterF M ⟨p8, [6], rotT⟩ i 63 =
      ((List.range 64).map fun w => eqAt (repA P cv) w * M.rd .E (p7.e + w + 1 * i)).sum := by
    intro i hi
    have := rot_spec hRot (A := fun w => eqAt (repA P cv) w)
      (fun w hw jf => by
        rw [getD_map_default (Src.gkOut _) rfl, gkOut_val M _ _ jf _ (fa _ (by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)), getD_vals _ (by omega), ea, hcvA]; rfl)
      (fun jf => by rw [gkOut_val M _ _ jf _ fz, ez]) hi
    rw [gk_loop_fst] at this
    exact this
  have hR : ∀ s < 64, iterF M ⟨p8, [6], rotT⟩ ((64 - s) % 64) 63 =
      rotSum (fun z => (vkSl (feAt sig) P qs).getD z 0) (eqAt (repA P cv)) s := by
    intro s hs
    rw [hrot _ (Nat.mod_lt _ (by omega))]
    rw [show ((List.range 64).map fun w => eqAt (repA P cv) w * M.rd .E (p7.e + w + 1 * ((64 - s) % 64))) =
        (List.range 64).map fun w => eqAt (repA P cv) w *
          feAt sig (8 * (gkrQO P qs + 243 + 3 * ((w + (64 - s) % 64) % 64))) from
      List.map_congr_left fun w hw => by
        have hw' := List.mem_range.mp hw
        show _ * M.e _ = _
        rw [show p7.e + w + 1 * ((64 - s) % 64) = p7.e + (w + (64 - s) % 64) by ring, hslc _ (by omega)]]
    rw [rot_reindex (eqAt (repA P cv)) (fun z => feAt sig (8 * (gkrQO P qs + 243 + 3 * z))) hs, rotSum]
    exact congrArg sumE (List.map_congr_left fun z hz => by
      simp [vkSl, List.getD_eq_getElem?_getD, List.mem_range.mp hz])
  generalize p8.adv (loop [6] rotT p8).2 = p9 at hF2 ⊢
  -- the input check block
  have hf20 := thold_of_loop hF2 (jf := 0) (by simp)
  rw [gk_loop_fst] at hf20
  have he3 : G.1.e3.length = 64 := by
    have := congrArg List.length e3
    simp only [vals, List.length_map, eqKernel_length, List.length_range] at this
    simpa using this
  have hA2 := fin2TB_spec (by rw [gkOut_val M _ _ 0 _ fz, ez]) (by simp) (by simp [he3]) hf20
  -- `F`'s values as cells
  rw [show (6 : Nat) - 1 = 5 from rfl] at hv1 hv3
  have hO1 : (vkO1 (feAt sig) P qs instV outV).1 = (List.range 6).map fun i => (sc1.cell 2 i).val M := by
    rw [vkO1, openSpec_fst]; exact hc1
  have hO1v : (vkO1 (feAt sig) P qs instV outV).2.2 = (sc1.cell 5 5).val M := by
    rw [vkO1, openSpec_snd2]; exact hv1
  have hLw1 : (vkLw (feAt sig) P qs instV outV).1 = (List.range 4).map fun i => (sc2.cell 2 i).val M := hc2
  have hO2 : (vkO2 (feAt sig) P qs instV outV).1 = (List.range 6).map fun i => (sc3.cell 2 i).val M := by
    rw [vkO2, openSpec_fst]; exact hc3
  have hO2v : (vkO2 (feAt sig) P qs instV outV).2.2 = (sc3.cell 5 5).val M := by
    rw [vkO2, openSpec_snd2]; exact hv3
  have hcf : kChain (feAt sig) (P + 4) (vkC0 (feAt sig) qs instV outV) (8 * (qs + 57) - 40) (8 * (lay0 P).str) 12 =
      vkCf (feAt sig) P qs instV outV := rfl
  rw [hcf] at hrep
  have hpt := hrep.point
  refine ⟨?_, fun hb => ?_⟩
  · -- the outputs
    simp only [GkrOut.vals, KeccakOut.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.take_append_drop, hO1, List.map_append, List.map_map, List.map_map, ← hinstV]; rfl
    · rw [gkCell_val M _ fw]; exact ew
    · rw [List.map_append, List.map_append, hLw1, hO2, ← hpt, gk_take_range_map _ (by omega : P ≤ P + 1)]
      simp only [List.map_map, Function.comp_def, hcv]
      rw [show (fun i => ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 18 + i) 11).val M) =
          fun i => ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + (18 + i)) 11).val M from
        funext fun i => by rw [show cbOf P + 18 + i = cbOf P + (18 + i) by omega]]
    · simp only [List.map_map, Function.comp_def, vkSl]
      refine List.map_congr_left fun k hk => ?_
      have hk' := List.mem_range.mp hk
      have lsl' : G.1.sl.length = 128 := lsl
      rw [gkCell_val M _ (fsl _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)), esl k (by omega),
        Nat.mod_eq_of_lt hk']
  · -- the assertions
    -- the first opening block: `F`'s committed check
    have hs1V : vals (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0)
        (List.map (fun i => gkS (sc1.cell 2 i)) (List.range 6)) = (vkO1 (feAt sig) P qs instV outV).1 := by
      rw [hO1]; simp only [vals, List.map_map, Function.comp_def, gkS_valF]
    have hlV : vals (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0)
        (List.map (Src.gkOut ⟨p1, [], tplOf preT.2⟩) preT.1.lanes) = eqKernel (lanePt (fun m => feAt sig (8 * m)) qs) := by
      rw [← el]; simp only [vals, List.map_map]
      exact List.map_congr_left fun x hx => gkOut_val M _ _ 0 _ (fl x hx)
    have hsgV : (Src.gkOut ⟨p1, [], tplOf preT.2⟩ preT.1.seg).valF (iterXv M ⟨p7, [], tplOf G.2⟩ 0)
        (iterF M ⟨p7, [], tplOf G.2⟩ 0) = feAt sig (8 * qs) := by rw [gkOut_val M _ _ 0 _ fs, es]
    have hAf1 : SegsAssert M p7 (loop [] (tplOf G.2) p7).2 ↔
        ((vkO1 (feAt sig) P qs instV outV).2.1.headD 0 * feAt sig (8 * (gkrQO P qs + 90)) ==
          (vkO1 (feAt sig) P qs instV outV).2.2) = true := by
      rw [segsAssert_loop_iff]
      have e : (∀ jf < 2 ^ ([] : List Nat).sum, TAssert (iterXv M (loop [] (tplOf G.2) p7).1 jf)
          (iterF M (loop [] (tplOf G.2) p7).1 jf) G.2) ↔
          TAssert (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0) G.2 :=
        ⟨fun h => h 0 (by simp), fun h jf hjf => by rw [show jf = 0 by simpa using hjf]; exact h⟩
      rw [e, hA1, gkS_valF, hb, one_mul, hs1V, hlV, hsgV, gk_fe_beq,
        vk_c1 _ _ _ _ _ (by rw [← hinstV]; simp), hO1v, gkS_valF, gk_add_eq_zero]
      simp only [eqAt, lanePt]
    -- the input check block: `F`'s input check
    have hhw : (vkCf (feAt sig) P qs instV outV).weights =
        keccakLinearTranspose (prodW (eqAt (repA P cv)) (repB P cv)) := by
      rw [hrep.weights]; rfl
    have hdrop : (vkCf (feAt sig) P qs instV outV).point.drop (P + 4 - 4) = [cv (18 + P)] := by
      rw [← hpt, show P + 4 - 4 = P by omega, gk_drop_range_map]
      simp
    have hdot : dot (vkO2 (feAt sig) P qs instV outV).2.1 (vkSl (feAt sig) P qs) =
        ((List.range 25).map fun l => (eqAt (vkO2 (feAt sig) P qs instV outV).1 (25 + l) * cv (18 + P) +
          eqAt (vkO2 (feAt sig) P qs instV outV).1 l * (1 + cv (18 + P))) *
          laneForm (repB P cv) (rotSum (fun z => (vkSl (feAt sig) P qs).getD z 0) (eqAt (repA P cv))) l).sum := by
      have hs6 : (vkO2 (feAt sig) P qs instV outV).1.length = 6 := by rw [hO2]; simp
      have hsl : (vkSl (feAt sig) P qs).length = 64 := by simp [vkSl]
      rw [vkO2, openSpec_snd1, ← vkO2,
        open_input_lt (P + 4) _ _ _ hhw hs6 hsl, hdrop, gk_eqKernel_one, sum2_lanes]
    have hlf : ∀ l, laneForm (repB P cv) (fun s => (gkS ((⟨p8, [6], rotT⟩ : LoopOut).cell 63 ((64 - s) % 64))).valF
        (iterXv M ⟨p9, [], tplOf (fin2TB (gkS b) (Src.gkOut ⟨p7, [], tplOf G.2⟩ G.1.z)
          (List.map (fun l => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 19 + P + l) 11))
            (List.range 25))
          (fun s => gkS ((⟨p8, [6], rotT⟩ : LoopOut).cell 63 ((64 - s) % 64)))
          (List.map (Src.gkOut ⟨p7, [], tplOf G.2⟩) G.1.e3)
          (gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 18 + P) 11))
          (List.map (fun i => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 1 + i) 11))
            (List.range 16))
          (List.map (fun i => gkS (sc2.cell 2 i)) (List.range 4)) (gkS (sc3.cell 5 5)) 0).2⟩ 0)
        (iterF M ⟨p9, [], tplOf (fin2TB (gkS b) (Src.gkOut ⟨p7, [], tplOf G.2⟩ G.1.z)
          (List.map (fun l => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 19 + P + l) 11))
            (List.range 25))
          (fun s => gkS ((⟨p8, [6], rotT⟩ : LoopOut).cell 63 ((64 - s) % 64)))
          (List.map (Src.gkOut ⟨p7, [], tplOf G.2⟩) G.1.e3)
          (gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 18 + P) 11))
          (List.map (fun i => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 1 + i) 11))
            (List.range 16))
          (List.map (fun i => gkS (sc2.cell 2 i)) (List.range 4)) (gkS (sc3.cell 5 5)) 0).2⟩ 0)) l =
        laneForm (repB P cv) (rotSum (fun z => (vkSl (feAt sig) P qs).getD z 0) (eqAt (repA P cv))) l :=
      fun l => gk_laneForm_congr _ (fun s hs => by rw [gkS_valF]; exact hR s hs) l
    have hBV : ∀ (o : LoopOut) (V : Nat → FE), vals (iterXv M o 0) V
        (List.map (fun l => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 19 + P + l) 11))
          (List.range 25)) = repB P cv := by
      intro o V
      rw [gk_vals_gkS]; simp only [repB, hcv]
      exact List.map_congr_left fun l _ => by rw [show cbOf P + 19 + P + l = cbOf P + (19 + P + l) by omega]
    have hmuV : ∀ (o : LoopOut) (V : Nat → FE), vals (iterXv M o 0) V
        (List.map (fun i => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 1 + i) 11))
          (List.range 16)) = (vkCf (feAt sig) P qs instV outV).mu := by
      intro o V
      rw [gk_vals_gkS, ← hrep.mu]; simp only [hcv]
      exact List.map_congr_left fun i _ => by rw [show cbOf P + 1 + i = cbOf P + (1 + i) by omega]
    have he3V : ∀ (o : LoopOut) (V : Nat → FE), vals (iterXv M o 0) V (List.map (Src.gkOut ⟨p7, [], tplOf G.2⟩) G.1.e3) =
        eqKernel (vkO2 (feAt sig) P qs instV outV).1 := by
      intro o V
      have : vals (iterXv M ⟨p7, [], tplOf G.2⟩ 0) (iterF M ⟨p7, [], tplOf G.2⟩ 0)
          (List.map (fun i => gkS (sc3.cell 2 i)) (List.range 6)) = (vkO2 (feAt sig) P qs instV outV).1 := by
        rw [gk_vals_gkS, hO2]
      rw [← this, ← e3]; simp only [vals, List.map_map]
      exact List.map_congr_left fun x hx => gkOut_val M _ _ 0 _ (f3 x hx)
    have hxV : ∀ (o : LoopOut) (V : Nat → FE),
        (gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 18 + P) 11)).valF (iterXv M o 0) V =
          cv (18 + P) := by
      intro o V; rw [gkS_valF, hcv]; simp only []; rw [show cbOf P + 18 + P = cbOf P + (18 + P) by omega]
    have hAf2 : SegsAssert M p9 (loop [] (tplOf (fin2TB (gkS b) (Src.gkOut ⟨p7, [], tplOf G.2⟩ G.1.z)
          (List.map (fun l => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 19 + P + l) 11))
            (List.range 25))
          (fun s => gkS ((⟨p8, [6], rotT⟩ : LoopOut).cell 63 ((64 - s) % 64)))
          (List.map (Src.gkOut ⟨p7, [], tplOf G.2⟩) G.1.e3)
          (gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 18 + P) 11))
          (List.map (fun i => gkS ((⟨p3, [4], layTpl P (qs + 57) p.k⟩ : LoopOut).cell (cbOf P + 1 + i) 11))
            (List.range 16))
          (List.map (fun i => gkS (sc2.cell 2 i)) (List.range 4)) (gkS (sc3.cell 5 5)) 0).2) p9).2 ↔
        (multilinearEval (vkCf (feAt sig) P qs instV outV).mu (vkLw (feAt sig) P qs instV outV).1 *
          dot (vkO2 (feAt sig) P qs instV outV).2.1 (vkSl (feAt sig) P qs) ==
          (vkO2 (feAt sig) P qs instV outV).2.2) = true := by
      rw [segsAssert_loop_iff]
      have e : ∀ (ins : List Ins), (∀ jf < 2 ^ ([] : List Nat).sum, TAssert (iterXv M (loop [] (tplOf ins) p9).1 jf)
          (iterF M (loop [] (tplOf ins) p9).1 jf) ins) ↔
          TAssert (iterXv M ⟨p9, [], tplOf ins⟩ 0) (iterF M ⟨p9, [], tplOf ins⟩ 0) ins :=
        fun _ => ⟨fun h => h 0 (by simp), fun h jf hjf => by rw [show jf = 0 by simpa using hjf]; exact h⟩
      rw [e, hA2, gkS_valF, hb, one_mul, hmuV, hBV, he3V, hxV, gkS_valF, ← hO2v, gk_vals_gkS, ← hLw1, gk_fe_beq,
        hdot, gk_add_eq_zero]
      simp only [hlf, eqAt]
    have hArot : SegsAssert M p8 (loop [6] rotT p8).2 :=
      segsAssert_loop_iff.mpr fun _ _ => tassert_noA (gnoA_map _ _ fun w => by simp [mulI])
    constructor
    · rintro ⟨-, -, -, -, hL, -, -, -, h1, -, h2, -⟩
      exact ⟨hAf2.mp h2, hAf1.mp h1, (hlayA hb).mp hL⟩
    · rintro ⟨h2, h1, hL⟩
      exact ⟨trivial, hAK, hAPre, hACp, (hlayA hb).mpr hL, sc_asserts _ _ _ _ _ _, sc_asserts _ _ _ _ _ _,
        sc_asserts _ _ _ _ _ _, hAf1.mpr h1, hArot, hAf2.mpr h2, trivial⟩

/-- **Q_arith_eq of `F`'s `verifyKeccak`** (`logSteps = P + 4`): in any memory where the gadget's rows
hold and the input lanes are the stream (`Streamed`), with the caller's instance point and output
lanes in the cells `inst`, `out`: the gadget's output cells are `F`'s `KeccakOut`, `F`'s position
after is the gadget's last lane, and with the gate `1` `F`'s flag after holds iff the flag before
does and every assertion of the gadget holds. -/
theorem gkr_spec {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → Cell} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T)
    (hT : gkrEnd P qs ≤ T) (h : SegsHold c M p (gkrGadget P qs inst out b p).2) (s : RS)
    (hs : s.ent + s.msg = 8 * qs - 40) :
    (verifyKeccak (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).1 = (gkrGadget P qs inst out b p).1.vals M ∧
    (verifyKeccak (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.ent +
      (verifyKeccak (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.msg = 8 * gkrEnd P qs - 40 ∧
    (b.val M = 1 →
      ((verifyKeccak (P + 4) ((List.range (P + 4)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.ok = true ↔
        s.ok = true ∧ SegsAssert M p (gkrGadget P qs inst out b p).2)) := by
  have hinstL : ((List.range (P + 4)).map fun i => (inst i).val M).length = P + 4 := by simp
  obtain ⟨hout1, hpos, hok⟩ := vk_facts (feAt sig) P qs ((List.range (P + 4)).map fun i => (inst i).val M)
    ((List.range 25).map fun l => (out l).val M) s.ok hq hinstL
  obtain ⟨hc1, hc2⟩ := gkr_core hP hq hS hT h
  rw [verifyKeccak_run sig (P + 4) _ _ s (8 * qs - 40) hs]
  refine ⟨hout1.trans hc1.symm, hpos, fun hb => (hok.trans ?_)⟩
  rw [hc2 hb]
  exact ⟨fun ⟨h2, h1, ho, hl⟩ => ⟨ho, h2, h1, hl⟩, fun ⟨ho, h2, h1, hl⟩ => ⟨h2, h1, ho, hl⟩⟩


/-! ## The shapes: `P20`'s `CH` (`logSteps = 20`) and `KS` (`15`), `P8`'s (`9`, `13`) -/

/-- `P20`'s `CH` GKR (`logSteps = 20`). -/
example {c : Ctx} {M : Mem} {p : Ptr} {qs : Nat} {inst out : Nat → Cell} {b : Cell} {sig : ByteArray} {T : Nat} :=
  @gkr_spec c M p 16 qs inst out b sig T layOk_16

/-- `P20`'s `KS` GKR (`logSteps = 15`). -/
example {c : Ctx} {M : Mem} {p : Ptr} {qs : Nat} {inst out : Nat → Cell} {b : Cell} {sig : ByteArray} {T : Nat} :=
  @gkr_spec c M p 11 qs inst out b sig T layOk_11

/-- `P8`'s two GKRs (`logSteps = 9`, `13`). -/
example {c : Ctx} {M : Mem} {p : Ptr} {qs : Nat} {inst out : Nat → Cell} {b : Cell} {sig : ByteArray} {T : Nat} :=
  @gkr_spec c M p 5 qs inst out b sig T layOk_5

example {c : Ctx} {M : Mem} {p : Ptr} {qs : Nat} {inst out : Nat → Cell} {b : Cell} {sig : ByteArray} {T : Nat} :=
  @gkr_spec c M p 9 qs inst out b sig T layOk_9

end Lvm.Q1
