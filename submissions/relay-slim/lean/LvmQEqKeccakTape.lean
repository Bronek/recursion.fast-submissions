-- New for lvm2 (T-Q): Q_arith_eq for the tape's layer loops (S2, BLUEPRINT2 T2). The layer proof is
-- v1's (`layer_coreI`, `LvmQEqKeccakLayer`); the block proof is v1's `layers_spec` (`LvmQEqKeccakGkr`)
-- generalised to a block of `2^d` real layers starting at layer `j0`.
import LvmQEqKeccakGkr
import LvmDecideTape

/-!
# The tape's layers (`layerT_spec`, `layersT_spec`)

**`F` side.** `tChain v ls C₀ p L j0 k`: the claim after `k` tape layers from `C₀`, layer `k` (the
tape's layer `j0 + k`, `ι` term `iotaT (j0 + k)` = `RC[23 − step]`'s bits, one segment) read at
position `p + k·L` (`layerSpecI`). `tChain_add`: the chain from `j0` continued by the chain from
`j0 + n` at its end, so two blocks compose.

**Circuit side.** `layerT_spec`: one iteration of v1's layer template whose two constant slots both
hold `RC[23 − step]`'s bits computes the tape layer (`(1 + σ)·ι + σ·ι = ι`). `layersT_spec`: a loop
`[d]` of the template whose constants are `cstKT (j0 + jf)` carries `tChain … j0 (2^d)`; with the gate
`1`, its assertions hold iff every layer's two checks do.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build DM

/-! ## `F`'s tape layers on a view -/

/-- The tape's `ι` term at layer `step`: `RC[23 − step]`'s bits of the weights. -/
def iotaT (step : Nat) (C : KeccakClaim) : FE := iotaF (keccakRC.getD (tapeDepth - step - 1) 0) C.weights

/-- `F`'s claim after `k` tape layers from `C₀` (layer `k` is the tape's layer `j0 + k`, at
`p + k·L`). -/
def tChain (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L j0 : Nat) : Nat → KeccakClaim
  | 0 => C₀
  | k + 1 => (layerSpecI v ls (iotaT (j0 + k)) (tChain v ls C₀ p L j0 k) (p + k * L)).claim

/-- Layer `k` of the chain. -/
def tLayer (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L j0 k : Nat) : LayerOut :=
  layerSpecI v ls (iotaT (j0 + k)) (tChain v ls C₀ p L j0 k) (p + k * L)

/-- Two consecutive runs of the chain are one. -/
theorem tChain_add (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L j0 n : Nat) :
    ∀ k, tChain v ls C₀ p L j0 (n + k) =
      tChain v ls (tChain v ls C₀ p L j0 n) (p + n * L) L (j0 + n) k
  | 0 => rfl
  | k + 1 => by
    show (layerSpecI v ls (iotaT (j0 + (n + k))) (tChain v ls C₀ p L j0 (n + k)) (p + (n + k) * L)).claim =
      (layerSpecI v ls (iotaT (j0 + n + k)) (tChain v ls (tChain v ls C₀ p L j0 n) (p + n * L) L (j0 + n) k)
        (p + n * L + k * L)).claim
    rw [tChain_add v ls C₀ p L j0 n k, show j0 + (n + k) = j0 + n + k by omega,
      show p + (n + k) * L = p + n * L + k * L by ring]

theorem tLayer_add (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L j0 n k : Nat) :
    tLayer v ls C₀ p L j0 (n + k) = tLayer v ls (tChain v ls C₀ p L j0 n) (p + n * L) L (j0 + n) k := by
  unfold tLayer
  rw [tChain_add, show j0 + (n + k) = j0 + n + k by omega, show p + (n + k) * L = p + n * L + k * L by ring]

/-! ## One tape layer -/

/-- **One tape layer** (Q_arith_eq of the tape's `verifyKeccakLayerS Shape.tape`, as `layerSpecI` with
`iotaT step`): v1's template with `RC[23 − step]` in both constant slots. -/
theorem layerT_spec {c : LCfg} {xv : Src → FE} {V : Nat → FE} (hH : THold xv V 0 (layerTB c 0).2)
    (hcb : c.cb + c.C = (layerTB c 0).2.length)
    {C : KeccakClaim} {first : Bool} (hR : Rep c.P (fun j => xv (c.pv j)) C first)
    {step : Nat} (hstep : step < tapeDepth)
    (hrc : ∀ i < 7, xv (c.k i) = rcBit (keccakRC.getD (tapeDepth - step - 1) 0) i ∧
      xv (c.k (7 + i)) = rcBit (keccakRC.getD (tapeDepth - step - 1) 0) i)
    (hfirst : xv (c.k 14) = if first then 1 else 0)
    {v : Nat → FE} {off p : Nat} (hv : ∀ m < c.q + c.str, lv xv [c.str] m = v (8 * m + off))
    (hp : p + 40 = 8 * c.q + off) :
    Rep c.P (fun j => V (c.cb + j)) (layerSpecI v (c.P + 4) (iotaT step) C p).claim false ∧
    (layerSpecI v (c.P + 4) (iotaT step) C p).pos = p + 8 * c.str ∧
    (TAssert xv V (layerTB c 0).2 → xv (c.k 15) = 1 →
      (layerSpecI v (c.P + 4) (iotaT step) C p).ok1 = true ∧
        (layerSpecI v (c.P + 4) (iotaT step) C p).ok2 = true) ∧
    ((layerSpecI v (c.P + 4) (iotaT step) C p).ok1 = true →
      (layerSpecI v (c.P + 4) (iotaT step) C p).ok2 = true → TAssert xv V (layerTB c 0).2) := by
  have hm : keccakRC.getD (tapeDepth - step - 1) 0 ∈ keccakRC :=
    rc_mem (by simp only [tapeDepth] at hstep ⊢; omega)
  refine layer_coreI (inv_start hH) hcb hR hm hm ?_ hrc hfirst hv hp
  rw [iotaT, add_mul, one_mul, add_assoc, FE_add_self, add_zero]

/-! ## A block of tape layers -/

/-- **A block of `2^d` tape layers** (the loop `[d]` of the relocated template, constants
`cstKT (j0 + jf)` with the gate `β` in slot `15`): from the claim `C₀` (tape layer `j0`) in the `C`
cells before it, the copy rows of the last iteration represent `F`'s claim after the block; with the
gate `1`, its assertions hold iff every layer's two checks do. -/
theorem layersT_spec {c : Ctx} {M : Mem} {pL : Ptr} {P q cst d j0 : Nat} {sig : ByteArray} {T : Nat}
    (hP : layOk P = true) (h : SegsHold c M pL (loop [d] (layTpl P q cst) pL).2)
    (hS : Streamed M sig T) (hT : q + 2 ^ d * (lay0 P).str + 2 ≤ T) (hq : 5 ≤ q)
    (hj : j0 + 2 ^ d ≤ tapeDepth) {β : FE}
    (hcst : ∀ jf < 2 ^ d, ∀ j < 16, FE.ofK (M.k (cst + (16 * jf + j))) =
      if j = 15 then β else FE.ofK (cstKT (j0 + jf) j))
    {C0 : KeccakClaim} (hpe : 57 + P ≤ pL.e) (h0 : Rep P (fun j => M.e (pL.e - (57 + P) + j)) C0 (j0 == 0)) :
    Rep P (fun j => ((loop [d] (layTpl P q cst) pL).1.cell (cbOf P + j) (2 ^ d - 1)).val M)
      (tChain (feAt sig) (P + 4) C0 (8 * q - 40) (8 * (lay0 P).str) j0 (2 ^ d)) false ∧
    (β = 1 → (SegsAssert M pL (loop [d] (layTpl P q cst) pL).2 ↔
      ∀ k < 2 ^ d, (tLayer (feAt sig) (P + 4) C0 (8 * q - 40) (8 * (lay0 P).str) j0 k).ok1 = true ∧
        (tLayer (feAt sig) (P + 4) C0 (8 * q - 40) (8 * (lay0 P).str) j0 k).ok2 = true)) := by
  have hok := hP
  simp only [layOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨hlen, -⟩, hsuf⟩ := hok
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
  have hO : (loop [d] (layTpl P q cst) pL).1 = ⟨pL, [d], layTpl P q cst⟩ := rfl
  have hdims : (⟨pL, [d], layTpl P q cst⟩ : LoopOut).dims = [d] := rfl
  rw [hO]
  have hH : ∀ jf < 2 ^ d, THold (fun s => iterXv M ⟨pL, [d], layTpl P q cst⟩ jf (relocS q cst s))
      (iterF M ⟨pL, [d], layTpl P q cst⟩ jf) 0 (layIns P) := by
    intro jf hjf
    have := thold_of_loop (dims := [d]) (ins := (layIns P).map (relocI q cst)) (p := pL) h (jf := jf) (by simpa using hjf)
    exact thold_reloc this
  have hk : ∀ jf < 2 ^ d, ∀ j < 16, (fun s => iterXv M ⟨pL, [d], layTpl P q cst⟩ jf (relocS q cst s)) ((lay0 P).k j) =
      FE.ofK (M.k (cst + (16 * jf + j))) := by
    intro jf hjf j _
    show iterXv M _ jf (relocS q cst ((lay0 P).k j)) = _
    rw [relocS_k P, iterXv_ext1 M _ hdims (by simpa using hjf)]
    show FE.ofK (M.k _) = _
    congr 2; omega
  have hstr : (lay0 P).str ≠ 16 := by simp only [lay0, LCfg.str]; omega
  have hv : ∀ jf < 2 ^ d, ∀ m < (lay0 P).q + (lay0 P).str,
      lv (fun s => iterXv M ⟨pL, [d], layTpl P q cst⟩ jf (relocS q cst s)) [(lay0 P).str] m =
        feAt sig (8 * m + 8 * (q + (lay0 P).str * jf)) := by
    intro jf hjf m hm
    have hm' : m < (lay0 P).str := by simpa [lay0] using hm
    have e : ∀ m', (fun s => iterXv M ⟨pL, [d], layTpl P q cst⟩ jf (relocS q cst s)) (.ext ⟨.K, m', [(lay0 P).str]⟩) =
        FE.ofK (M.k (q + m' + (lay0 P).str * jf)) := by
      intro m'
      show iterXv M _ jf (relocS q cst (.ext ⟨.K, m', [(lay0 P).str]⟩)) = _
      simp only [relocS, if_neg hstr]
      rw [iterXv_ext1 M _ hdims (by omega)]
      rfl
    unfold lv
    rw [e, e, e, show q + (m + 1) + (lay0 P).str * jf = q + m + (lay0 P).str * jf + 1 by omega,
      show q + (m + 2) + (lay0 P).str * jf = q + m + (lay0 P).str * jf + 2 by omega,
      load_feAt hS (by
        have : (lay0 P).str * jf + (lay0 P).str ≤ 2 ^ d * (lay0 P).str := by
          rw [Nat.mul_comm (2 ^ d)]; exact (Nat.mul_succ _ _).symm ▸ Nat.mul_le_mul_left _ hjf
        omega)]
    congr 1; ring
  have hpv : ∀ jf < 2 ^ d, ∀ j < 57 + P, (fun s => iterXv M ⟨pL, [d], layTpl P q cst⟩ jf (relocS q cst s)) ((lay0 P).pv j) =
      layCv M ⟨pL, [d], layTpl P q cst⟩ (57 + P) (cbOf P) jf j := by
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
    · show _ = (LoopOut.cell ⟨pL, [d], layTpl P q cst⟩ (cbOf P + j) jf).val M
      rw [LoopOut.cell_val]
      show M.rd ((layTpl P q cst).getD (cbOf P + j) default).ty _ = M.rd ((layTpl P q cst).getD (cbOf P + j) default).ty _
      rw [hty']
      show M.e (pL.e + lrank .E (layTpl P q cst) (cbOf P + j) - ltw .E (layTpl P q cst) + ltw .E (layTpl P q cst) * (jf + 1)) =
        M.e (pL.e + lrank .E (layTpl P q cst) (cbOf P + j) + ltw .E (layTpl P q cst) * jf)
      generalize lrank .E (layTpl P q cst) (cbOf P + j) = a at hr ⊢
      generalize ltw .E (layTpl P q cst) = w at hr ⊢
      rw [show pL.e + a - w + w * (jf + 1) = pL.e + a + w * jf by rw [Nat.mul_succ]; omega]
  have hrc : ∀ k < 2 ^ d, ∀ i < 7,
      (fun s => iterXv M ⟨pL, [d], layTpl P q cst⟩ k (relocS q cst s)) ((lay0 P).k i) =
        rcBit (keccakRC.getD (tapeDepth - (j0 + k) - 1) 0) i ∧
      (fun s => iterXv M ⟨pL, [d], layTpl P q cst⟩ k (relocS q cst s)) ((lay0 P).k (7 + i)) =
        rcBit (keccakRC.getD (tapeDepth - (j0 + k) - 1) 0) i := by
    intro k hk' i hi
    rw [hk k hk' i (by omega), hk k hk' (7 + i) (by omega), hcst k hk' i (by omega),
      hcst k hk' (7 + i) (by omega), if_neg (by omega), if_neg (by omega), ← ofK_rcK]
    simp only [cstKT, if_neg (show ¬ tapeDepth ≤ j0 + k by omega), if_pos hi, if_neg (show ¬ 7 + i < 7 by omega),
      if_pos (show 7 + i < 14 by omega), show 7 + i - 7 = i by omega]
    constructor <;> trivial
  have hfst : ∀ k < 2 ^ d, (fun s => iterXv M ⟨pL, [d], layTpl P q cst⟩ k (relocS q cst s)) ((lay0 P).k 14) =
      if (j0 + k == 0) = true then 1 else 0 := by
    intro k hk'
    rw [hk k hk' 14 (by omega), hcst k hk' 14 (by omega), if_neg (by omega)]
    simp only [cstKT, if_neg (show ¬ tapeDepth ≤ j0 + k by omega), if_neg (show ¬ 14 < 7 by omega),
      if_neg (show ¬ 14 < 14 by omega)]
    rcases Nat.eq_zero_or_pos (j0 + k) with h0 | h0
    · obtain ⟨rfl, rfl⟩ : j0 = 0 ∧ k = 0 := by omega
      rfl
    · rw [if_neg (by omega), if_neg (by rw [beq_iff_eq]; omega)]; rfl
  have hp : ∀ k < 2 ^ d, 8 * q - 40 + k * (8 * (lay0 P).str) + 40 = 8 * (lay0 P).q + 8 * (q + (lay0 P).str * k) := by
    intro k _; simp only [lay0]; rw [Nat.mul_comm k]; ring_nf; omega
  have hrep : ∀ k ≤ 2 ^ d, Rep P (layCv M ⟨pL, [d], layTpl P q cst⟩ (57 + P) (cbOf P) k)
      (tChain (feAt sig) (P + 4) C0 (8 * q - 40) (8 * (lay0 P).str) j0 k) (j0 + k == 0) := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk'
      have hR := rep_congr (ih (by omega)) (fun j hj => (hpv k (by omega) j hj).symm)
      have := (layerT_spec (c := lay0 P) (hH k (by omega)) hcb hR (step := j0 + k) (by omega)
        (hrc k (by omega)) (hfst k (by omega)) (hv k (by omega)) (hp k (by omega))).1
      rw [show (j0 + (k + 1) == 0) = false by simp]
      exact this
  have hd1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  refine ⟨?_, fun hβ => ?_⟩
  · have := hrep (2 ^ d) le_rfl
    rw [show (j0 + 2 ^ d == 0) = false by rw [beq_eq_false_iff_ne]; omega] at this
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ d = m + 1 := ⟨2 ^ d - 1, by omega⟩
    rw [hm] at this ⊢
    exact this
  have hL : ∀ k < 2 ^ d, _ := fun k hk' => layerT_spec (c := lay0 P) (hH k hk') hcb
    (rep_congr (hrep k (by omega)) (fun j hj => (hpv k hk' j hj).symm)) (step := j0 + k) (by omega)
    (hrc k hk') (hfst k hk') (hv k hk') (hp k hk')
  change SegsAssert M pL (loop [d] (tplOf ((layIns P).map (relocI q cst))) pL).2 ↔ _
  rw [segsAssert_loop_iff]
  simp only [tassert_reloc]
  constructor
  · intro hA k hk'
    exact (hL k hk').2.2.1 (hA k (by simpa using hk'))
      (by rw [show iterXv M _ k (relocS q cst ((lay0 P).k 15)) = _ from hk k hk' 15 (by omega),
        hcst k hk' 15 (by omega), if_pos rfl, hβ])
  · intro hok jf hjf
    have hjf' : jf < 2 ^ d := by simpa using hjf
    exact (hL jf hjf').2.2.2 (hok jf hjf').1 (hok jf hjf').2

/-! ## The tape's constants -/

theorem cstIT_ty (b : Src) (t : Nat) : (cstIT b t).ty = .K := by unfold cstIT; split <;> rfl

theorem cstIT_op (b : Src) (t : Nat) : ∃ k k', (cstIT b t).op = .lin k k' := by
  unfold cstIT; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem cstInsT_w (b : Src) : ∀ i ∈ cstInsT b, Row.w .K ⟨i.op, i.ty, []⟩ = 1 := by
  intro i hi
  simp only [cstInsT, List.mem_map, List.mem_range] at hi
  obtain ⟨t, -, rfl⟩ := hi
  obtain ⟨k, k', hk⟩ := cstIT_op b t
  simp [Row.w, Row.writes, hk, cstIT_ty]

/-- **The tape's constants block**: cell `p.k + t` holds constant `t % 16` of layer `t / 16`, the
gate `b` in slot `15`. -/
theorem cstT_spec {c : Ctx} {M : Mem} {p : Ptr} {bc : Cell}
    (h : SegsHold c M p (loop [] (tplOf (cstInsT (gkS bc))) p).2) {t : Nat} (ht : t < 16 * tapeDepth) :
    FE.ofK (M.k (p.k + t)) = if t % 16 = 15 then bc.val M else FE.ofK (cstKT (t / 16) (t % 16)) := by
  have hH := thold_of_loop h (jf := 0) (by simp)
  have hg : (cstInsT (gkS bc)).getD t default = cstIT (gkS bc) t := by
    simp [cstInsT, List.getD_eq_getElem?_getD, ht]
  have := hH t (by simp [cstInsT]; omega)
    (by rw [hg]; obtain ⟨k, k', hk⟩ := cstIT_op (gkS bc) t; exact Or.inr (Or.inl ⟨k, k', hk⟩))
  rw [Nat.zero_add, hg] at this
  have hc : iterF M (loop [] (tplOf (cstInsT (gkS bc))) p).1 0 t = FE.ofK (M.k (p.k + t)) := by
    rw [gk_loop_fst]
    show Cell.val M (LoopOut.cell ⟨p, [], tplOf (cstInsT (gkS bc))⟩ t 0) = _
    have hty : ((tplOf (cstInsT (gkS bc))).getD t default).ty = .K := by
      rw [tplOf_getD _ (by simp [cstInsT]; omega), hg]; exact cstIT_ty _ _
    simp only [LoopOut.cell, hty, Cell.val, Ptr.at,
      lrank_ones (δ := cstInsT (gkS bc)) (cstInsT_w _) (show t ≤ (cstInsT (gkS bc)).length by simp [cstInsT]; omega),
      Nat.mul_zero, Nat.add_zero]
    rfl
  rw [← hc, this]
  have hb : (gkS bc).valF (iterXv M (loop [] (tplOf (cstInsT (gkS bc))) p).1 0)
      (iterF M (loop [] (tplOf (cstInsT (gkS bc))) p).1 0) = bc.val M := gk_iterXv_gkS M _ 0 bc
  unfold cstIT
  split_ifs with h1
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_zero, zero_mul, add_zero]
  · simp only [Ins.evalF, List.getD_cons_zero, List.getD_cons_succ, hb, ofK_one, one_mul, FE_add_self, zero_add]

/-! ## The tape's first claim -/

/-- `F`'s first tape claim (`tapeFirstClaim`, over `FE`): `Σ_{l<25} lanes_l·output_l`,
`eq(inst[0..4))`, the point `inst[4..)`, the weights `lanes ⊗ x^z`. -/
def tapeFirstF (instV lp outV : List FE) : KeccakClaim :=
  ⟨dot ((eqKernel lp).take 25) outV, eqKernel (instV.take 4), instV.drop 4, firstW (eqKernel lp)⟩

theorem tapeFirstF_weights (instV lp outV : List FE) :
    (tapeFirstF instV lp outV).weights = firstW (eqKernel lp) := by
  simp only [tapeFirstF]

/-- The carried values of the tape's first claim (`carV` with the point's last coordinate in the
segment's place). -/
def carVT (v0 : FE) (mu instP lanes fl : List FE) : List FE :=
  [v0] ++ mu ++ [1] ++ instP ++ lanes.take 25 ++ List.replicate 6 0 ++ fl

theorem carVT_eq {P : Nat} (v0 : FE) (mu iP la fl : List FE) (hiP : iP.length = P + 1) :
    carVT v0 mu iP la fl = carV v0 mu (iP.take P) (iP.getD P 0) la fl := by
  have : iP = iP.take P ++ [iP.getD P 0] := by
    conv_lhs => rw [← List.take_append_drop P iP]
    congr 1
    apply List.ext_getElem (by simp [hiP])
    intro i h1 h2
    simp only [List.length_singleton, Nat.lt_one_iff] at h2
    subst h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show P < iP.length by omega)]
  unfold carVT carV
  conv_lhs => rw [this]
  simp only [List.append_assoc]

/-- The lanes' `eq` table, the challenges at lanes `qs + 9 k`. -/
def lanePtT (u : Nat → FE) (qs : Nat) : List FE := (List.range 5).map fun k => u (qs + 9 * k)

/-- **The tape's first claim** is represented by its carried values. -/
theorem rep_firstT (P : Nat) {instV lp out fl : List FE} (hinst : instV.length = P + 5) (hlp : lp.length = 5)
    (hout : out.length = 25)
    (hfl : ∀ i < 7, fl.getD i 0 = (eqKernel lp).getD 0 0 * FE.ofK (FK.x ^ iotaPos i)) :
    Rep P (fun j => (carVT (((List.range 25).map fun l => (eqKernel lp).getD l 0 * out.getD l 0).sum)
        (eqKernel (instV.take 4)) (instV.drop 4) (eqKernel lp) fl).getD j 0)
      (tapeFirstF instV lp out) true := by
  have hL : (eqKernel lp).length = 32 := by rw [eqKernel_length, hlp]; rfl
  have hmu : (eqKernel (instV.take 4)).length = 16 := by
    rw [eqKernel_length, List.length_take, hinst]; rfl
  have hiP1 : (instV.drop 4).length = P + 1 := by rw [List.length_drop, hinst]; omega
  have hiP : ((instV.drop 4).take P).length = P := by rw [List.length_take, hiP1]; omega
  have hla : 25 ≤ (eqKernel lp).length := by omega
  rw [carVT_eq _ _ _ _ _ hiP1]
  generalize hcv : carV (((List.range 25).map fun l => (eqKernel lp).getD l 0 * out.getD l 0).sum)
    (eqKernel (instV.take 4)) ((instV.drop 4).take P) ((instV.drop 4).getD P 0) (eqKernel lp) fl = cv
  have hB : ∀ l < 25, (repB P fun j => cv.getD j 0).getD l 0 = (eqKernel lp).getD l 0 := by
    intro l hl
    simp only [repB, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, Option.map_some,
      Option.getD_some]
    rw [← List.getD_eq_getElem?_getD, ← hcv, carV_B _ _ _ _ _ _ hmu hiP hla hl, List.getD_eq_getElem?_getD]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show cv.getD 0 0 = dot ((eqKernel lp).take 25) out
    rw [← hcv, show ∀ (a : FE) b c d e f, (carV a b c d e f).getD 0 0 = a from fun _ _ _ _ _ _ => rfl,
      gk_dot_eq_sum (by rw [List.length_take, hL]; rfl) hout]
    refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, List.mem_range.mp hl]
  · show (List.range 16).map (fun i => cv.getD (1 + i) 0) = eqKernel (instV.take 4)
    conv_rhs => rw [← gk_range_map_getD (eqKernel (instV.take 4)), hmu]
    exact List.map_congr_left fun i hi => by rw [← hcv]; exact carV_mu _ _ _ _ _ _ hmu (List.mem_range.mp hi)
  · show cv.getD 17 0 = sumE (eqKernel (instV.take 4))
    rw [gk_sumE_eqKernel, ← hcv, carV_kappa _ _ _ _ _ _ hmu]
  · show (List.range (P + 1)).map (fun i => cv.getD (18 + i) 0) = instV.drop 4
    conv_rhs => rw [← gk_range_map_getD (instV.drop 4), hiP1]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [← hcv]
    rcases Nat.lt_or_ge i P with h | h
    · rw [carV_pt _ _ _ _ _ _ hmu hiP h]; simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]
    · obtain rfl : i = P := by omega
      rw [carV_seg _ _ _ _ _ _ hmu hiP]
  · rw [if_pos rfl, tapeFirstF_weights]
    exact firstW_congr fun i hi => (hB i hi).symm
  · intro i hi
    show cv.getD (50 + P + i) 0 = _
    rw [if_pos rfl, hB 0 (by decide), ← hcv, carV_fl _ _ _ _ _ _ hmu hiP hla, hfl i hi]

theorem fx_gDot : ∀ (acc : Src) (cds : List (Src × Src)) (n : Nat), Fx acc → Fx (gDot acc cds n).1
  | _, [], _, h => h
  | acc, cd :: rest, n, _ => by
    simp only [gDot, tb_bind]
    exact fx_gDot _ rest _ (fx_emit _ _)

/-- **The tape's first-claim block**: its lanes and the carried values (`carVT`). -/
theorem preTBT_spec {xv : Src → FE} {V : Nat → FE} {P qs : Nat} {inst out : Nat → Src} {b : Src}
    {u : Nat → FE} (hu : ∀ m ≤ qs + 36, lv xv [] m = u m) (hinst : ∀ i, Fx (inst i)) {n : Nat}
    (h : THold xv V n (preTBT P qs inst out b n).2) :
    vals xv V (preTBT P qs inst out b n).1.lanes = eqKernel (lanePtT u qs) ∧
    (∀ x ∈ (preTBT P qs inst out b n).1.lanes, Fx x) ∧
    (preTBT P qs inst out b n).1.carried.length = 57 + P ∧ (∀ x ∈ (preTBT P qs inst out b n).1.carried, Fx x) ∧
    vals xv V (preTBT P qs inst out b n).1.carried =
      carVT (((List.range 25).map fun l =>
          (eqKernel (lanePtT u qs)).getD l 0 * ((List.range 25).map fun l => (out l).valF xv V).getD l 0).sum)
        (eqKernel (((List.range (P + 5)).map fun i => (inst i).valF xv V).take 4))
        (((List.range (P + 5)).map fun i => (inst i).valF xv V).drop 4) (eqKernel (lanePtT u qs))
        ((List.range 7).map fun i => (eqKernel (lanePtT u qs)).getD 0 0 * FE.ofK (FK.x ^ iotaPos i)) := by
  unfold preTBT at h ⊢
  -- z, one
  obtain ⟨h1, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ez := gZero_spec h1; have fz : Fx (gZero b n).1 := fx_emit _ _
  generalize (gZero b n).1 = z at h ez fz ⊢; generalize n + (gZero b n).2.length = n1 at h ⊢
  obtain ⟨h2, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have eo := gOne_spec h2; have fo : Fx (gOne z n1).1 := fx_emit _ _
  rw [ez, add_zero] at eo
  generalize (gOne z n1).1 = one at h eo fo ⊢; generalize n1 + (gOne z n1).2.length = n2 at h ⊢
  -- the lane challenges
  obtain ⟨h4, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have elp : vals xv V (mapTB (fun k => gLoad (qs + 9 * k) []) (List.range 5) n2).1 = lanePtT u qs :=
    forall₂_map_eq (mapTB_spec_mem (P := fun k v => v = u (qs + 9 * k)) _
      (fun k hk m hm => by rw [gLoad_lv hm, hu _ (by have := List.mem_range.mp hk; omega)]) _ h4)
  generalize (mapTB (fun k => gLoad (qs + 9 * k) []) (List.range 5) n2).1 = lp at h elp ⊢
  generalize n2 + (mapTB (fun k => gLoad (qs + 9 * k) []) (List.range 5) n2).2.length = n4 at h ⊢
  -- the lanes
  obtain ⟨h6, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have el := gk_eqTab_one ez eo lp n4 h6
  have fl := fx_gEqTab z lp [one] n4 (by simpa using fo)
  rw [elp] at el
  generalize (gEqTab z [one] lp n4).1 = lanes at h el fl ⊢; generalize n4 + (gEqTab z [one] lp n4).2.length = n6 at h ⊢
  have hll : lanes.length = 32 := by
    have := congrArg List.length el; rw [List.length_map, eqKernel_length] at this; simpa [lanePtT] using this
  -- the value
  obtain ⟨h7, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ed := gDot_spec _ _ _ h7
  have fv : Fx (gDot z ((List.range 25).map fun l => (lanes.getD l default, out l)) n6).1 := fx_gDot _ _ _ fz
  generalize (gDot z ((List.range 25).map fun l => (lanes.getD l default, out l)) n6).1 = v0 at h ed fv ⊢
  generalize n6 + (gDot z ((List.range 25).map fun l => (lanes.getD l default, out l)) n6).2.length = n8 at h ⊢
  -- `μ`
  obtain ⟨h9, h, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have em := gk_eqTab_one ez eo ((List.range 4).map inst) n8 h9
  have fm := fx_gEqTab z ((List.range 4).map inst) [one] n8 (by simpa using fo)
  generalize (gEqTab z [one] ((List.range 4).map inst) n8).1 = mu at h em fm ⊢
  generalize n8 + (gEqTab z [one] ((List.range 4).map inst) n8).2.length = n9 at h ⊢
  -- the flips
  obtain ⟨h10, -, e⟩ := tb_peel _ _ h; rw [e]; clear e
  have ef : vals xv V (mapTB (fun i => gScale (FK.x ^ iotaPos i) (lanes.getD 0 default)) (List.range 7) n9).1 =
      (List.range 7).map fun i => (eqKernel (lanePtT u qs)).getD 0 0 * FE.ofK (FK.x ^ iotaPos i) :=
    forall₂_map_eq (mapTB_spec_mem (P := fun i v => v = (eqKernel (lanePtT u qs)).getD 0 0 * FE.ofK (FK.x ^ iotaPos i))
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
  refine ⟨el, fl, ?_, ?_, ?_⟩
  · simp [hmu, hll, hfl]; omega
  · intro x hx
    simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hx
    rcases hx with ((((((rfl | hx) | rfl) | ⟨i, -, rfl⟩) | hx) | hx) | hx)
    · exact fv
    · exact fm x hx
    · exact fo
    · exact hinst _
    · exact fl x (List.mem_of_mem_take hx)
    · rw [List.eq_of_mem_replicate hx]; exact fz
    · exact ffl x hx
  · simp only [vals, List.map_append, List.map_cons, List.map_nil, List.map_take, List.map_replicate] at em el ef ⊢
    rw [em, el, ef, ed, eo, ez, gk_take_range_map _ (by omega : 4 ≤ P + 5), gk_drop_range_map]
    simp only [carVT, List.map_map, Function.comp_def, show P + 5 - 4 = P + 1 by omega]
    have hs : (List.map (fun x => (lanes.getD x default).valF xv V * (out x).valF xv V) (List.range 25)).sum =
        (List.map (fun l => (eqKernel (lanePtT u qs)).getD l 0 *
          ((List.range 25).map fun l => (out l).valF xv V).getD l 0) (List.range 25)).sum := by
      refine congrArg List.sum (List.map_congr_left fun l hl => ?_)
      have hl' := List.mem_range.mp hl
      rw [getD_vals _ (by omega), vals, el]
      simp [List.getD_eq_getElem?_getD, hl']
    rw [hs, zero_add]

theorem gnoA_preTBT (P qs : Nat) (inst out : Nat → Src) (b : Src) (n : Nat) : GNoA (preTBT P qs inst out b n).2 := by
  unfold preTBT
  exact gnoA_bind _ _ _ (gnoA_zero _ _) (gnoA_bind _ _ _ (gnoA_one _ _)
    (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_load _ _ _) _ _)
    (gnoA_bind _ _ _ (gnoA_gEqTab _ _ _ _) (gnoA_bind _ _ _ (gnoA_gDot _ _ _)
    (gnoA_bind _ _ _ (gnoA_gEqTab _ _ _ _) (gnoA_bind _ _ _ (gnoA_mapTB (fun _ _ => gnoA_lin _ _ _ _ _) _ _)
    (gnoA_pure _ _)))))))

/-- A layer iteration writes at least its `C` carried cells. -/
theorem lay_ltw {P : Nat} (hP : layOk P = true) {q cst : Nat} : 57 + P ≤ ltw .E (layTpl P q cst) := by
  have hok := hP
  simp only [layOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨hlen, -⟩, hsuf⟩ := hok
  have hw : ∀ i ∈ (layIns P).drop (cbOf P), Row.w .E ⟨i.op, i.ty, []⟩ = 1 := by
    intro i hi
    have := hsuf i hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    obtain ⟨h1, h2⟩ := this
    have hwr : Row.writes ⟨i.op, i.ty, []⟩ = some .E := by
      unfold Row.writes; cases hop : i.op <;> simp_all
    simp [Row.w, hwr]
  have hr0 : lrank .E (layTpl P q cst) (cbOf P + 0) + (57 + P) = ltw .E (layTpl P q cst) + 0 := by
    rw [layTpl, lrank_reloc, ltw_reloc]; exact lrank_suffix hlen hw (by omega)
  omega

/-- The copy rows of a layer loop's last iteration are the `C` cells before the pointer after it. -/
theorem lay_last_cell {M : Mem} {P : Nat} (hP : layOk P = true) (pL : Ptr) (q cst d : Nat) {j : Nat}
    (hj : j < 57 + P) :
    ((⟨pL, [d], layTpl P q cst⟩ : LoopOut).cell (cbOf P + j) (2 ^ d - 1)).val M =
      M.e ((pL.adv (loop [d] (layTpl P q cst) pL).2).e - (57 + P) + j) := by
  have hok := hP
  simp only [layOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨⟨hlen, -⟩, hsuf⟩ := hok
  have hw : ∀ i ∈ (layIns P).drop (cbOf P), Row.w .E ⟨i.op, i.ty, []⟩ = 1 := by
    intro i hi
    have := hsuf i hi
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    obtain ⟨h1, h2⟩ := this
    have hwr : Row.writes ⟨i.op, i.ty, []⟩ = some .E := by
      unfold Row.writes; cases hop : i.op <;> simp_all
    simp [Row.w, hwr]
  have hr : lrank .E (layTpl P q cst) (cbOf P + j) + (57 + P) = ltw .E (layTpl P q cst) + j := by
    rw [layTpl, lrank_reloc, ltw_reloc]; exact lrank_suffix hlen hw hj.le
  have hty : ((layTpl P q cst).getD (cbOf P + j) default).ty = .E := by
    rw [layTpl, tplOf_getD _ (by rw [List.length_map, hlen]; omega), reloc_getD, relocI_toLRow_ty]
    have hm : (layIns P).getD (cbOf P + j) default ∈ (layIns P).drop (cbOf P) := by
      rw [show (layIns P).getD (cbOf P + j) default = ((layIns P).drop (cbOf P)).getD j default by
        simp [List.getD_eq_getElem?_getD]]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]; exact List.getElem_mem _
    exact (hsuf _ hm).1
  have hcell : (⟨pL, [d], layTpl P q cst⟩ : LoopOut).cell (cbOf P + j) (2 ^ d - 1) =
      ⟨.E, pL.e + lrank .E (layTpl P q cst) (cbOf P + j) + ltw .E (layTpl P q cst) * (2 ^ d - 1)⟩ := by
    simp only [LoopOut.cell, hty, Ptr.at]
  rw [hcell, gk_adv_loop]
  show M.e _ = M.e _
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have e1 : ([d] : List Nat).sum = d := by simp
  rw [e1]
  have hw0 := lay_ltw hP (q := q) (cst := cst)
  generalize lrank .E (layTpl P q cst) (cbOf P + j) = a at hr ⊢
  generalize ltw .E (layTpl P q cst) = w at hr hw0 ⊢
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ d = m + 1 := ⟨2 ^ d - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel]
  congr 1
  dsimp only
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- **The tape gadget** (Q_arith_eq of T-G's `tapeGkr (P + 5) inst output`, read as `tChain` from
`tapeFirstF`): in any memory where its rows hold and the input lanes are the stream, the carried
cells of the last layer represent `F`'s claim after the 24 layers; with the gate `1`, the gadget's
assertions hold iff every layer's two checks do. -/
theorem tape_core {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → Cell} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T)
    (hT : tapeEnd P qs + 2 ≤ T) (h : SegsHold c M p (tapeGadget P qs inst out b p).2) :
    Rep P (fun j => ((tapeGadget P qs inst out b p).1.cv j).val M)
      (tChain (feAt sig) (P + 4) (tapeFirstF ((List.range (P + 5)).map fun i => (inst i).val M)
          (lanePtT (fun m => feAt sig (8 * m)) qs) ((List.range 25).map fun l => (out l).val M))
        (8 * tapeQ qs - 40) (8 * (lay0 P).str) 0 tapeDepth) false ∧
    (b.val M = 1 → (SegsAssert M p (tapeGadget P qs inst out b p).2 ↔
      ∀ k < tapeDepth,
        (tLayer (feAt sig) (P + 4) (tapeFirstF ((List.range (P + 5)).map fun i => (inst i).val M)
          (lanePtT (fun m => feAt sig (8 * m)) qs) ((List.range 25).map fun l => (out l).val M))
          (8 * tapeQ qs - 40) (8 * (lay0 P).str) 0 k).ok1 = true ∧
        (tLayer (feAt sig) (P + 4) (tapeFirstF ((List.range (P + 5)).map fun i => (inst i).val M)
          (lanePtT (fun m => feAt sig (8 * m)) qs) ((List.range 25).map fun l => (out l).val M))
          (8 * tapeQ qs - 40) (8 * (lay0 P).str) 0 k).ok2 = true)) := by
  generalize hinstV : ((List.range (P + 5)).map fun i => (inst i).val M) = instV
  generalize houtV : ((List.range 25).map fun l => (out l).val M) = outV
  have hstr : (lay0 P).str = 366 + 15 * (P + 1) := rfl
  have hTe : tapeEnd P qs = qs + 45 + 24 * (lay0 P).str := rfl
  simp only [tapeGadget, hold_bind, assert_bind, gk_bind_fst_eq, gk_pure_apply_eq, gk_getPtr_eq, Ptr.adv_nil] at h ⊢
  obtain ⟨-, hK, hPre, hCp, hL1, hL2, -⟩ := h
  -- the constants
  have hcst1 : ∀ jf < 2 ^ 4, ∀ j < 16, FE.ofK (M.k (p.k + (16 * jf + j))) =
      if j = 15 then b.val M else FE.ofK (cstKT (0 + jf) j) := by
    intro jf hjf j hj
    rw [cstT_spec hK (t := 16 * jf + j) (by simp only [tapeDepth]; omega), show (16 * jf + j) % 16 = j by omega,
      show (16 * jf + j) / 16 = 0 + jf by omega]
  have hcst2 : ∀ jf < 2 ^ 3, ∀ j < 16, FE.ofK (M.k (p.k + 16 * 16 + (16 * jf + j))) =
      if j = 15 then b.val M else FE.ofK (cstKT (16 + jf) j) := by
    intro jf hjf j hj
    rw [show p.k + 16 * 16 + (16 * jf + j) = p.k + (16 * (16 + jf) + j) by omega,
      cstT_spec hK (t := 16 * (16 + jf) + j) (by simp only [tapeDepth]; omega),
      show (16 * (16 + jf) + j) % 16 = j by omega, show (16 * (16 + jf) + j) / 16 = 16 + jf by omega]
  have hAK : SegsAssert M p (loop [] (tplOf (cstInsT (gkS b))) p).2 :=
    segsAssert_loop_iff.mpr fun _ _ => tassert_noA (gnoA_map _ _ fun t => by
      obtain ⟨k, k', hk⟩ := cstIT_op (gkS b) t; rw [hk]; exact Lvm.Loop.Op.noConfusion)
  generalize p.adv (loop [] (tplOf (cstInsT (gkS b))) p).2 = p1 at hPre hCp hL1 hL2 ⊢
  -- the first claim
  have hpre0 := thold_of_loop hPre (jf := 0) (by simp)
  rw [gk_loop_fst] at hpre0
  obtain ⟨el, fl, lc, fcar, ecar⟩ := preTBT_spec (u := fun m => feAt sig (8 * m))
    (fun m hm => gk_lv_fix hS _ 0 m (by simp only [tapeEnd, tapeQ] at hT; omega)) (fun i => gk_fx_gkS (inst i)) hpre0
  have hAPre := (segsAssert_loop_iff (M := M) (dims := []) (p := p1)).mpr fun _ _ => tassert_noA (gnoA_preTBT P qs
    (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0)
  simp only [gkS_valF, hinstV, houtV] at ecar
  set preT := preTBT P qs (fun i => gkS (inst i)) (fun l => gkS (out l)) (gkS b) 0 with hpreT
  simp only [gk_loop_fst] at hCp hL1 hL2 ⊢
  generalize p1.adv (loop [] (tplOf preT.2) p1).2 = p2 at hCp hL1 hL2 ⊢
  -- the copies
  have hcopy : ∀ j < 57 + P, M.e (p2.e + j) =
      (vals (iterXv M ⟨p1, [], tplOf preT.2⟩ 0) (iterF M ⟨p1, [], tplOf preT.2⟩ 0) preT.1.carried).getD j 0 :=
    fun j hj => cp_spec hCp fcar (by rw [lc]; exact hj)
  set cpL := cpIns (preT.1.carried.map (Src.gkOut ⟨p1, [], tplOf preT.2⟩)) with hcpL
  have hp3 : (p2.adv (loop [] (tplOf cpL) p2).2).e = p2.e + (57 + P) := by
    rw [gk_adv_loop, ltw_ones (cpIns_w _)]; simp [cpL, cpIns, lc]
  have hACp : SegsAssert M p2 (loop [] (tplOf cpL) p2).2 :=
    segsAssert_loop_iff.mpr fun _ _ => tassert_noA (gnoA_map _ _ fun _ => by simp [linI])
  generalize p2.adv (loop [] (tplOf cpL) p2).2 = p3 at hp3 hL1 hL2 ⊢
  -- the first claim, carried
  have hfl : ∀ i < 7, ((List.range 7).map fun i => (eqKernel (lanePtT (fun m => feAt sig (8 * m)) qs)).getD 0 0 *
      FE.ofK (FK.x ^ iotaPos i)).getD i 0 =
      (eqKernel (lanePtT (fun m => feAt sig (8 * m)) qs)).getD 0 0 * FE.ofK (FK.x ^ iotaPos i) := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hi]
  have hr := rep_firstT P (instV := instV) (lp := lanePtT (fun m => feAt sig (8 * m)) qs) (out := outV)
    (by rw [← hinstV]; simp) (by simp [lanePtT]) (by rw [← houtV]; simp) hfl
  set C0 := tapeFirstF instV (lanePtT (fun m => feAt sig (8 * m)) qs) outV with hC0
  have h0 : Rep P (fun j => M.e (p3.e - (57 + P) + j)) C0 (0 == 0) :=
    rep_congr hr fun j hj => by
      rw [hp3, show p2.e + (57 + P) - (57 + P) + j = p2.e + j by omega, hcopy j hj, ecar]
  -- the first block of layers (0 … 15)
  obtain ⟨hrep1, hA1⟩ := layersT_spec (d := 4) (j0 := 0) (C0 := C0) hP hL1 hS
    (by simp only [tapeEnd, tapeQ, tapeDepth, Nat.reducePow] at hT ⊢; omega) (by simp only [tapeQ]; omega) (by simp [tapeDepth]) hcst1
    (by omega) h0
  simp only [gk_loop_fst] at hrep1
  have hp4 : ∀ j < 57 + P, _ := fun j (hj : j < 57 + P) => lay_last_cell (M := M) hP p3 (tapeQ qs) p.k 4 hj
  generalize hp4e : p3.adv (loop [4] (layTpl P (tapeQ qs) p.k) p3).2 = p4 at hL2 hp4 ⊢
  -- the second block (16 … 23)
  have hL : 8 * tapeQ qs - 40 + 16 * (8 * (lay0 P).str) = 8 * (tapeQ qs + 16 * (lay0 P).str) - 40 := by
    simp only [tapeQ]; omega
  have h0' : Rep P (fun j => M.e (p4.e - (57 + P) + j))
      (tChain (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (8 * (lay0 P).str) 0 16) (16 == 0) :=
    rep_congr hrep1 fun j hj => hp4 j hj
  obtain ⟨hrep2, hA2⟩ := layersT_spec (d := 3) (j0 := 16) hP hL2 hS
    (by simp only [tapeEnd, tapeQ, tapeDepth, Nat.reducePow] at hT ⊢; omega) (by simp only [tapeQ]; omega) (by simp [tapeDepth]) hcst2
    (by
      rw [← hp4e, gk_adv_loop]
      have := lay_ltw (q := tapeQ qs) (cst := p.k) hP
      have : ltw .E (layTpl P (tapeQ qs) p.k) ≤ ltw .E (layTpl P (tapeQ qs) p.k) * 2 ^ ([4] : List Nat).sum :=
        Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
      dsimp only
      omega)
    h0'
  simp only [gk_loop_fst] at hrep2
  have e24 : ∀ k, tChain (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (8 * (lay0 P).str) 0 (16 + k) =
      tChain (feAt sig) (P + 4) (tChain (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (8 * (lay0 P).str) 0 16)
        (8 * (tapeQ qs + 16 * (lay0 P).str) - 40) (8 * (lay0 P).str) 16 k := by
    intro k; rw [tChain_add, hL]
  have l24 : ∀ k, tLayer (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (8 * (lay0 P).str) 0 (16 + k) =
      tLayer (feAt sig) (P + 4) (tChain (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (8 * (lay0 P).str) 0 16)
        (8 * (tapeQ qs + 16 * (lay0 P).str) - 40) (8 * (lay0 P).str) 16 k := by
    intro k; rw [tLayer_add, hL]
  refine ⟨?_, fun hb => ?_⟩
  · rw [show tapeDepth = 16 + 2 ^ 3 from rfl, e24]
    exact hrep2
  · rw [← hp4e] at hA2 ⊢
    constructor
    · rintro ⟨-, -, -, -, h1, h2, -⟩
      intro k hk
      rcases Nat.lt_or_ge k 16 with hk1 | hk1
      · exact (hA1 hb).mp h1 k hk1
      · obtain ⟨k', rfl⟩ : ∃ k', k = 16 + k' := ⟨k - 16, by omega⟩
        rw [l24]
        exact (hA2 hb).mp h2 k' (by simp only [tapeDepth] at hk; omega)
    · intro hall
      refine ⟨trivial, hAK, hAPre, hACp, (hA1 hb).mpr fun k hk => hall k (by simp only [tapeDepth]; omega),
        (hA2 hb).mpr fun k hk => ?_, trivial⟩
      rw [← l24]
      exact hall (16 + k) (by simp only [tapeDepth]; omega)

/-! ## `F`'s tape (T-V's `tapeGkrF`) on a view -/

/-- The `ι` term of T-V's generic layer `verifyKeccakLayerG depth segs logSteps step`. -/
def iotaG (depth segs logSteps step : Nat) (claim : KeccakClaim) : FE :=
  sumE ((List.range segs).map fun segment =>
    let constant := keccakRC.getD (depth * (segment + 1) - step - 1) 0
    (eqKernel (claim.point.drop (logSteps - 4))).getD segment 0 * sumE ((List.range 64).filterMap fun z =>
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))

/-- **T-V's generic layer on a view** (`verifyKeccakLayer_run`'s proof, `ι` as `iotaG`). -/
theorem verifyKeccakLayerG_run (sig : ByteArray) (depth segs logSteps step : Nat) (claim : KeccakClaim)
    (hpt : claim.point ≠ []) (s : RS) :
    verifyKeccakLayerG depth segs logSteps step claim sig s =
      ((layerSpecI (feAt sig) logSteps (iotaG depth segs logSteps step) claim (s.ent + s.msg)).claim,
        ⟨(layerSpecI (feAt sig) logSteps (iotaG depth segs logSteps step) claim (s.ent + s.msg)).pos, 0,
          (layerSpecI (feAt sig) logSteps (iotaG depth segs logSteps step) claim (s.ent + s.msg)).ok2 &&
            ((layerSpecI (feAt sig) logSteps (iotaG depth segs logSteps step) claim (s.ent + s.msg)).ok1 &&
              s.ok)⟩) := by
  simp only [verifyKeccakLayerG, rd_bind_run, rd_pure_run, readEs_run, rd_require_run, rd_sampleE_run,
    packRounds_run sig, sumcheck_run sig 4 (by norm_num), if_neg hpt]
  have r1 : ∀ a b : Nat, a + 40 + (b + 24 * productBits) = a + b + 40 + 24 * productBits := by
    intro a b; omega
  have r2 : ∀ a b : Nat, a + 72 + (b + 24 * productBits) = a + b + 72 + 24 * productBits := by
    intro a b; omega
  simp only [scState_replicate _ _ (show 0 < localBits by decide), layerSpecI, Nat.add_zero, Nat.zero_add]
  rw [r1, r2]
  rfl

/-- With one segment of depth 24 and the point of `P + 1` coordinates (`logSteps = P + 5`), the generic
layer's `ι` is the tape's. -/
theorem iotaG_tape {P step : Nat} {C : KeccakClaim} (hpt : C.point.length = P + 1) :
    iotaG tapeDepth 1 (P + 5) step C = iotaT step C := by
  unfold iotaG iotaT iotaF
  rw [show P + 5 - 4 = P + 1 by omega, List.drop_eq_nil_of_le (by omega)]
  simp [eqKernel, sumE, tapeDepth]

theorem layerSpecI_pos (v : Nat → FE) (ls : Nat) (io : KeccakClaim → FE) (C : KeccakClaim) (p : Nat) :
    (layerSpecI v ls io C p).pos = p + (2928 + 120 * C.point.length) := by
  show (packSpec v C.point _ 1 (p + 72 + 24 * productBits)).2.2.2 + localBits * roundLen 4 + 72 + 24 * 3 = _
  rw [packSpec_pos]
  simp only [productBits, localBits, roundLen]
  omega

theorem layerSpecI_point (v : Nat → FE) (ls : Nat) (io : KeccakClaim → FE) (C : KeccakClaim) (p : Nat) :
    (layerSpecI v ls io C p).claim.point.length = C.point.length := packSpec_length v _ _ _ _

theorem tChain_point (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L j0 : Nat) :
    ∀ k, (tChain v ls C₀ p L j0 k).point.length = C₀.point.length
  | 0 => rfl
  | k + 1 => by
    show (layerSpecI v ls (iotaT (j0 + k)) (tChain v ls C₀ p L j0 k) (p + k * L)).claim.point.length = _
    rw [layerSpecI_point, tChain_point v ls C₀ p L j0 k]

/-- The tape layers' checks from layer `j`, `k` of them. -/
def tOk (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L j : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => ((tLayer v ls C₀ p L 0 j).ok2 && (tLayer v ls C₀ p L 0 j).ok1) && tOk v ls C₀ p L (j + 1) k

theorem tOk_iff (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L : Nat) :
    ∀ (k j : Nat), tOk v ls C₀ p L j k = true ↔
      ∀ i < k, (tLayer v ls C₀ p L 0 (j + i)).ok1 = true ∧ (tLayer v ls C₀ p L 0 (j + i)).ok2 = true
  | 0, j => by simp [tOk]
  | k + 1, j => by
    rw [tOk, Bool.and_eq_true, Bool.and_eq_true, tOk_iff v ls C₀ p L k (j + 1)]
    constructor
    · rintro ⟨⟨h2, h1⟩, h⟩ i hi
      rcases i with _ | i
      · exact ⟨h1, h2⟩
      · rw [show j + (i + 1) = j + 1 + i by omega]; exact h i (by omega)
    · intro h
      refine ⟨⟨(h 0 (by omega)).2, (h 0 (by omega)).1⟩, fun i hi => ?_⟩
      rw [show j + 1 + i = j + (i + 1) by omega]; exact h (i + 1) (by omega)

theorem layerSpecI_congr (v : Nat → FE) (ls ls' : Nat) {io io' : KeccakClaim → FE} (C : KeccakClaim) (p : Nat)
    (h : io C = io' C) : layerSpecI v ls io C p = layerSpecI v ls' io' C p := by
  unfold layerSpecI; rw [h]

theorem tLayer_eq (v : Nat → FE) (ls ls' : Nat) (C₀ : KeccakClaim) (p L j : Nat) :
    tLayer v ls C₀ p L 0 j = layerSpecI v ls' (iotaT j) (tChain v ls C₀ p L 0 j) (p + j * L) := by
  unfold tLayer; rw [Nat.zero_add]; exact layerSpecI_congr _ _ _ _ _ rfl

theorem tChain_succ (v : Nat → FE) (ls ls' : Nat) (C₀ : KeccakClaim) (p L j : Nat) :
    tChain v ls C₀ p L 0 (j + 1) = (layerSpecI v ls' (iotaT j) (tChain v ls C₀ p L 0 j) (p + j * L)).claim := by
  show (layerSpecI v ls (iotaT (0 + j)) _ _).claim = _
  rw [Nat.zero_add, layerSpecI_congr v ls ls' _ _ rfl]

theorem tLayer_pos (v : Nat → FE) (ls : Nat) (C₀ : KeccakClaim) (p L j : Nat) :
    (tLayer v ls C₀ p L 0 j).pos = p + j * L + (2928 + 120 * C₀.point.length) := by
  unfold tLayer; rw [layerSpecI_pos, tChain_point]

/-- **T-V's tape layers on a view**: from layer `j` at position `p + j·L` (`L = 2928 + 120 (P + 1)`),
`k ≥ 1` layers give `tChain … (j + k)`, the position `p + (j + k)·L`, and the flag `ok && tOk`. -/
theorem keccakLayersG_run (sig : ByteArray) (P : Nat) (C₀ : KeccakClaim) (hC : C₀.point.length = P + 1)
    (p : Nat) : ∀ (k j : Nat) (s : RS), s.ent + s.msg = p + j * (2928 + 120 * (P + 1)) → 0 < k →
      keccakLayersG tapeDepth 1 (P + 5) (List.range' j k)
          (tChain (feAt sig) (P + 4) C₀ p (2928 + 120 * (P + 1)) 0 j) sig s =
        (tChain (feAt sig) (P + 4) C₀ p (2928 + 120 * (P + 1)) 0 (j + k),
          ⟨p + (j + k) * (2928 + 120 * (P + 1)), 0,
            s.ok && tOk (feAt sig) (P + 4) C₀ p (2928 + 120 * (P + 1)) j k⟩) := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
    intro j s hs _
    have hpl := tChain_point (feAt sig) (P + 4) C₀ p (2928 + 120 * (P + 1)) 0 j
    have hpt : (tChain (feAt sig) (P + 4) C₀ p (2928 + 120 * (P + 1)) 0 j).point ≠ [] := by
      rw [← List.length_pos_iff, hpl, hC]; omega
    rw [List.range'_succ]
    show (verifyKeccakLayerG tapeDepth 1 (P + 5) j _ >>= fun c => keccakLayersG tapeDepth 1 (P + 5) _ c) sig s = _
    rw [rd_bind_run, verifyKeccakLayerG_run sig _ _ _ _ _ hpt,
      layerSpecI_congr _ (P + 5) (P + 5) _ _ (iotaG_tape (hpl.trans hC)), hs,
      ← tChain_succ _ (P + 4) (P + 5), ← tLayer_eq _ (P + 4) (P + 5), tLayer_pos, hC]
    dsimp only
    rcases k with _ | k
    · simp only [List.range'_zero]
      show (tChain (feAt sig) (P + 4) C₀ p (2928 + 120 * (P + 1)) 0 (j + 1), _) = _
      simp only [tOk, Bool.and_true]
      refine Prod.ext rfl ?_
      show (⟨_, 0, _⟩ : RS) = ⟨_, 0, _⟩
      rw [RS.mk.injEq]
      refine ⟨by ring, rfl, ?_⟩
      cases s.ok <;> simp [Bool.and_comm]
    · rw [ih (j + 1) _ (by simp only []; ring) (by omega)]
      show (_, (⟨_, 0, _⟩ : RS)) = (_, ⟨_, 0, _⟩)
      rw [show j + 1 + (k + 1) = j + (k + 1 + 1) by omega]
      refine Prod.ext rfl ?_
      show (⟨_, 0, _⟩ : RS) = ⟨_, 0, _⟩
      rw [RS.mk.injEq]
      refine ⟨rfl, rfl, ?_⟩
      simp only [tOk]
      cases (tLayer (feAt sig) (P + 4) C₀ p (2928 + 120 * (P + 1)) 0 j).ok1 <;>
        cases (tLayer (feAt sig) (P + 4) C₀ p (2928 + 120 * (P + 1)) 0 j).ok2 <;> cases s.ok <;> simp

theorem tapeFirstClaimF_eq (inst lp out : List FE) : tapeFirstClaimF inst lp out = tapeFirstF inst lp out := by
  simp only [tapeFirstClaimF, tapeFirstF, firstW]

theorem lanePtT_sampAt (sig : ByteArray) {qs : Nat} (hq : 5 ≤ qs) :
    sampAt (feAt sig) (8 * qs - 40) 5 = lanePtT (fun m => feAt sig (8 * m)) qs := by
  simp only [sampAt, lanePtT]
  refine List.map_congr_left fun k _ => congrArg _ (by omega)

/-- **T-V's `tapeGkrF` on a view, replayed by the tape gadget**: from the lane challenges' position
`8 qs − 40` with the caller's instance point and output scalars in the cells `inst`, `out`, `F`'s input
claim is represented by the gadget's last copy rows, `F`'s position after is the gadget's last lane
(`tapeEnd`, the wire's first message), and with the gate `1` `F`'s flag after holds iff the flag before
does and every assertion of the gadget holds. -/
theorem tape_spec {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → Cell} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T)
    (hT : tapeEnd P qs + 2 ≤ T) (h : SegsHold c M p (tapeGadget P qs inst out b p).2) (s : RS)
    (hs : s.ent + s.msg = 8 * qs - 40) :
    (tapeGkrF (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).1.1 = lanePtT (fun m => feAt sig (8 * m)) qs ∧
    Rep P (fun j => ((tapeGadget P qs inst out b p).1.cv j).val M)
      (tapeGkrF (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).1.2 false ∧
    (tapeGkrF (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.ent = 8 * tapeEnd P qs - 40 ∧
    (tapeGkrF (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.msg = 0 ∧
    (b.val M = 1 →
      ((tapeGkrF (P + 5) ((List.range (P + 5)).map fun i => (inst i).val M)
        ((List.range 25).map fun l => (out l).val M) sig s).2.ok = true ↔
        s.ok = true ∧ SegsAssert M p (tapeGadget P qs inst out b p).2)) := by
  generalize hinstV : ((List.range (P + 5)).map fun i => (inst i).val M) = instV
  generalize houtV : ((List.range 25).map fun l => (out l).val M) = outV
  obtain ⟨hrep, hA⟩ := tape_core hP hq hS hT h
  rw [hinstV, houtV] at hrep hA
  have hL : 8 * (lay0 P).str = 2928 + 120 * (P + 1) := by simp only [lay0, LCfg.str]; ring
  have hq0 : 8 * tapeQ qs - 40 = 8 * qs - 40 + 72 * 5 := by simp only [tapeQ]; omega
  rw [hL] at hrep hA
  set C0 := tapeFirstF instV (lanePtT (fun m => feAt sig (8 * m)) qs) outV with hC0
  have hC0p : C0.point.length = P + 1 := by
    simp only [hC0, tapeFirstF, List.length_drop, ← hinstV, List.length_map, List.length_range]; omega
  have hrun := keccakLayersG_run sig P C0 hC0p (8 * tapeQ qs - 40) 24 0
    ⟨8 * tapeQ qs - 40, 0, s.ok⟩ (by simp) (by omega)
  simp only [List.range'_eq_map_range, Nat.zero_add, List.map_id', Nat.zero_mul, Nat.add_zero] at hrun
  have e1 : samples laneBits sig s = (lanePtT (fun m => feAt sig (8 * m)) qs, ⟨8 * tapeQ qs - 40, 0, s.ok⟩) := by
    rw [show laneBits = 4 + 1 from rfl, gk_samples_run sig 4 s _ hs, lanePtT_sampAt sig hq, hq0]
  have hrun' : keccakLayersG tapeDepth 1 (P + 5) (List.range tapeDepth) C0 sig ⟨8 * tapeQ qs - 40, 0, s.ok⟩ =
      (tChain (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (2928 + 120 * (P + 1)) 0 24,
        ⟨8 * tapeQ qs - 40 + 24 * (2928 + 120 * (P + 1)), 0,
          s.ok && tOk (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (2928 + 120 * (P + 1)) 0 24⟩) := by
    rw [show tapeDepth = 24 from rfl]
    exact hrun
  have hrunF : tapeGkrF (P + 5) instV outV sig s =
      ((lanePtT (fun m => feAt sig (8 * m)) qs, tChain (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40)
          (2928 + 120 * (P + 1)) 0 24),
        ⟨8 * tapeQ qs - 40 + 24 * (2928 + 120 * (P + 1)), 0,
          s.ok && tOk (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (2928 + 120 * (P + 1)) 0 24⟩) := by
    show (samples laneBits >>= fun lanePt => keccakLayersG tapeDepth 1 (P + 5) (List.range tapeDepth)
      (tapeFirstClaimF instV lanePt outV) >>= fun claim => pure (lanePt, claim)) sig s = _
    rw [rd_bind_run, e1]
    dsimp only
    rw [tapeFirstClaimF_eq, ← hC0, rd_bind_run, hrun', rd_pure_run]
  rw [hrunF]
  refine ⟨rfl, hrep, ?_, rfl, fun hb => ?_⟩
  · show 8 * tapeQ qs - 40 + 24 * (2928 + 120 * (P + 1)) = 8 * tapeEnd P qs - 40
    simp only [tapeEnd, tapeQ, tapeDepth, lay0, LCfg.str]; omega
  · show (s.ok && tOk (feAt sig) (P + 4) C0 (8 * tapeQ qs - 40) (2928 + 120 * (P + 1)) 0 24) = true ↔ _
    rw [Bool.and_eq_true, tOk_iff, hA hb]
    simp only [Nat.zero_add, show tapeDepth = 24 from rfl]

/-- **T-V's tape phase `dTape` on a view** (`logN = P + 5`): `r` (the `P + 5` challenges from position `P0`) and
the 25 scalars after them are the caller's cells `inst`, `out` (the assembly loads them from those stream
lanes), the tape gadget's lane challenges follow (`8 qs − 40 = P0 + 72 (P + 5) + 600`); then `F`'s input claim
is represented by the gadget's last copy rows, `F`'s position after is the wire's first message, and with the
gate `1` `F`'s flag holds iff the flag before and the gadget's assertions do. -/
theorem dTape_spec {c : Ctx} {M : Mem} {p : Ptr} {P qs : Nat} {inst out : Nat → Cell} {b : Cell}
    {sig : ByteArray} {T : Nat} (hP : layOk P = true) (hq : 5 ≤ qs) (hS : Streamed M sig T)
    (hT : tapeEnd P qs + 2 ≤ T) (h : SegsHold c M p (tapeGadget P qs inst out b p).2) (s : RS) {P0 : Nat}
    (hs : s.ent + s.msg = P0)
    (hinst : ((List.range (P + 5)).map fun i => (inst i).val M) = sampAt (feAt sig) P0 (P + 5))
    (hout : ((List.range 25).map fun l => (out l).val M) = scalarsAt (feAt sig) (P0 + 72 * (P + 5) + 40) 25)
    (hqs : 8 * qs - 40 = P0 + 72 * (P + 5) + 600) :
    (dTape (P + 5) sig s).1.r = (List.range (P + 5)).map (fun i => (inst i).val M) ∧
    (dTape (P + 5) sig s).1.v = (List.range 25).map (fun l => (out l).val M) ∧
    (dTape (P + 5) sig s).1.lanePt = lanePtT (fun m => feAt sig (8 * m)) qs ∧
    Rep P (fun j => ((tapeGadget P qs inst out b p).1.cv j).val M) (dTape (P + 5) sig s).1.claim false ∧
    (dTape (P + 5) sig s).2.ent = 8 * tapeEnd P qs - 40 ∧ (dTape (P + 5) sig s).2.msg = 0 ∧
    (b.val M = 1 → ((dTape (P + 5) sig s).2.ok = true ↔
      s.ok = true ∧ SegsAssert M p (tapeGadget P qs inst out b p).2)) := by
  have e1 : samples (P + 5) sig s = (sampAt (feAt sig) P0 (P + 5), ⟨P0 + 72 * (P + 5), 0, s.ok⟩) := by
    rw [show P + 5 = (P + 4) + 1 from rfl, gk_samples_run sig (P + 4) s P0 hs]
  have e2 : readEs lanes sig (⟨P0 + 72 * (P + 5), 0, s.ok⟩ : RS) =
      (scalarsAt (feAt sig) (P0 + 72 * (P + 5) + 40) 25, ⟨P0 + 72 * (P + 5), 600, s.ok⟩) := by
    rw [readEs_run]; rfl
  obtain ⟨t1, t2, t3, t4, t5⟩ := tape_spec hP hq hS hT h ⟨P0 + 72 * (P + 5), 600, s.ok⟩ (by
    show P0 + 72 * (P + 5) + 600 = _; omega)
  rw [hinst, hout] at t1 t2 t3 t4 t5 ⊢
  have hrun : dTape (P + 5) sig s = (⟨sampAt (feAt sig) P0 (P + 5), scalarsAt (feAt sig) (P0 + 72 * (P + 5) + 40) 25,
      (tapeGkrF (P + 5) (sampAt (feAt sig) P0 (P + 5)) (scalarsAt (feAt sig) (P0 + 72 * (P + 5) + 40) 25) sig
        ⟨P0 + 72 * (P + 5), 600, s.ok⟩).1.1,
      (tapeGkrF (P + 5) (sampAt (feAt sig) P0 (P + 5)) (scalarsAt (feAt sig) (P0 + 72 * (P + 5) + 40) 25) sig
        ⟨P0 + 72 * (P + 5), 600, s.ok⟩).1.2⟩,
      (tapeGkrF (P + 5) (sampAt (feAt sig) P0 (P + 5)) (scalarsAt (feAt sig) (P0 + 72 * (P + 5) + 40) 25) sig
        ⟨P0 + 72 * (P + 5), 600, s.ok⟩).2) := by
    unfold dTape
    rw [rd_bind_run, e1]
    dsimp only
    rw [rd_bind_run, e2]
    dsimp only
    rw [rd_bind_run, rd_pure_run]
  rw [hrun]
  dsimp only
  exact ⟨rfl, rfl, t1, t2, t3, t4, t5⟩

end Lvm.Q1
