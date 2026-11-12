-- adapted from rf-k/submissions/flock-recursive/lean/FRXLag.lean@8bff272b (section G6_FRXBaryTop:
-- `sBody_sem`, `BaryLay`, `cell_ne`, `sValM`, `sLoop_sem`, `baryIR_sem`, `baryIR_interp`) for lvm
-- (WP-13b): FR's two-word `F` re-targeted to `K = BF64`; FR's `alphaIR` call for `D(s)` is replaced
-- by the target index word itself (`ptK s`), FR's `djIR` table by the list `J` (`ptK J_t`).
import LvmXInterp3

/-!
# The barycentric interpolation on the machine (3): one target, the target loop, `baryIR_sem`

* `sBody_sem`: one target `s₀`: `out[c][s₀] = (ℓ = 0 ? y_c(s₀) : ℓ Σ_t y_c(J_t) E[t])`;
* `sLoop_sem`: every target `s < k`;
* **`baryIR_sem`**: the whole program, `out[c][s] = baryValK Jl k s y_c`, hence (`baryValK_eq`)
  **`baryIR_interp`**: `out[c][s] = interpF ptK Jl.toFinset y_c s`; `baryIR_lvm` at lvm's sizes
  (`k = 2^13`, `C = cs = 64`).
-/

namespace Lvm.X

open RecursionFast Finset Lvm.Nb

attribute [local irreducible] entryK storeM runPrims

/-! ## One target -/

/-- **One target `s₀`**: the `C` output cells of `s₀`, `bS := s₀ + 1`; the heap outside the `E`
row and those cells is kept. -/
theorem sBody_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb wb eb cb cs ob s0 : ℕ} {x : ℕ → ℕ}
    (hk : k < 2 ^ 64) (hC : C < 2 ^ 64) (hs0 : s0 < k)
    (hjb : regs ≤ jb) (hwb : regs ≤ wb) (heb : regs ≤ eb) (hcb : regs ≤ cb) (hob : regs ≤ ob)
    (hjb2 : jb + k < 2 ^ 64) (hwb2 : wb + k < 2 ^ 64) (heb2 : eb + k < 2 ^ 64)
    (hcb2 : ∀ t < k, ∀ c < C, cb + cs * x t + c < 2 ^ 64)
    (hcs2 : ∀ c < C, cb + cs * s0 + c < 2 ^ 64)
    (hob2 : ob + k * C < 2 ^ 64) (hsz : ob + k * C ≤ s.M.size) (hszE : eb + k ≤ s.M.size)
    (hjE : jb + k ≤ eb ∨ eb + k ≤ jb) (hwE : wb + k ≤ eb ∨ eb + k ≤ wb)
    (hOJ : ob + k * C ≤ jb ∨ jb + k ≤ ob) (hOE : ob + k * C ≤ eb ∨ eb + k ≤ ob)
    (hOY : ∀ c < C, ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
      (ob + k * C ≤ cb + cs * j + c ∨ cb + cs * j + c < ob) ∧
      (eb + k ≤ cb + cs * j + c ∨ cb + cs * j + c < eb))
    (hS : rd s.M bS = toWord s0) (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ c < C, rdK (semXIR I (sBody k C jb wb eb cb cs ob) s).M (ob + k * c + s0) =
      (if ∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t)) = 0 then rdK s.M (cb + cs * s0 + c)
       else (∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t))) *
        ∑ t ∈ range k, rdK s.M (cb + cs * x t + c) *
          (rdK s.M (wb + t) * (ptK s0 + rdK s.M (jb + t))⁻¹))) ∧
    rd (semXIR I (sBody k C jb wb eb cb cs ob) s).M bS = toWord (s0 + 1) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → (∀ c < C, y ≠ ob + k * c + s0) →
      rd (semXIR I (sBody k C jb wb eb cb cs ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (sBody k C jb wb eb cb cs ob) s).M := by
  have hs := hM.1
  rw [sBody]
  simp only [semXIR_seq]
  -- `fDs := ptK s₀`, `ℓ := 1`, `t := 0`, `bN2 := k`
  have r0 : rd (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M fDs = toWord s0 ∧
      rdK (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M fLp = 1 ∧
      rd (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M bT = toWord 0 ∧
      rd (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M bN2 = toWord k ∧
      rd (semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
        .const bN2 (toWord k)]) s).M bS = toWord s0 := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run, rdK]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs))
      only [rd_set_self, rd_set_ne, hS, or_self_eval] <;> rfl
  have H0 := hframe I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
    .const bN2 (toWord k)]) s (by simp [Lo, Prim.dst, regs, fDs, fLp, bT, bN2])
  have hM0 := inv_sem I (P := .blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
    .const bN2 (toWord k)]) (s := s) (by simp [WF, Prim.dst, fDs, fLp, bT, bN2]) hM
  have z0 := size_sem I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
    .const bN2 (toWord k)]) s
  generalize semXIR I (.blk [.op .or fDs bS bS, .const fLp 1, .const bT 0,
    .const bN2 (toWord k)]) s = q0 at r0 H0 hM0 z0
  -- the `E` row and `ℓ`
  obtain ⟨e1, e2, e3, e4, hM1⟩ := eLoop_sem I q0 hM0 (k := k) (jb := jb) (wb := wb) (eb := eb)
    (ds := ptK s0) hk hjb hwb heb hjb2 hwb2 heb2 (by rw [z0]; exact hszE) hjE hwE r0.2.2.2.1
    r0.2.2.1 (rdK_toWord r0.1) r0.2.1
  have nw_e : ¬ Writes (eBody jb wb eb) bS := by
    simp [eBody, addr1Ps, Writes, Prim.dst, bnw_mulK, bnw_invK, bA, bK, fX, fDd, fLp, fIv, fEt,
      bT, bS, cTmp]
  have r1 : rd (semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) q0).M bS = toWord s0 :=
    (e4 bS (by decide) (by decide) (by decide) nw_e).trans r0.2.2.2.2
  have z1 := size_sem I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) q0
  generalize semXIR I (.loopK bC2 bN2 (toWord k) (eBody jb wb eb)) q0 = q1 at e1 e2 e3 e4 hM1 z1 r1
  have hjt : ∀ t < k, rdK q0.M (jb + t) = rdK s.M (jb + t) := fun t _ =>
    rdK_congrB (H0 (jb + t) (by simp only [regs] at hjb ⊢; omega))
  have hL1 : rdK q1.M fLp = ∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t)) := by
    rw [e2]
    exact Finset.prod_congr rfl fun t ht => by rw [hjt t (Finset.mem_range.1 ht)]
  -- the flag, `c := 0`, `bN2 := C`
  have hs1 := hM1.1
  have r2 : rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
        .const bN2 (toWord C)]) q1).M bN2 = toWord C ∧
      rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
        .const bN2 (toWord C)]) q1).M bCi = toWord 0 ∧
      rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
        .const bN2 (toWord C)]) q1).M bS = toWord s0 ∧
      rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
        .const bN2 (toWord C)]) q1).M fLp = rd q1.M fLp := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs1))
      only [rd_set_self, rd_set_ne, r1] <;> rfl
  have r2z : rd (semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
      .const bN2 (toWord C)]) q1).M bZ = bW (decide (rdK q1.M fLp = 0)) := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs1))
      only [rd_set_self, rd_set_ne]
    rw [eq_bW]
    congr 1
    exact decide_eq_decide.mpr (wK_eq_zero _).symm
  have H2 := hframe I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
    .const bN2 (toWord C)]) q1 (by simp [Lo, Prim.dst, regs, bK, bZ, bCi, bN2])
  have hM2 := inv_sem I (P := .blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
    .const bN2 (toWord C)]) (s := q1) (by simp [WF, Prim.dst, bK, bZ, bCi, bN2]) hM1
  have z2 := size_sem I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
    .const bN2 (toWord C)]) q1
  generalize semXIR I (.blk [.const bK 0, .op .eq bZ fLp bK, .const bCi 0,
    .const bN2 (toWord C)]) q1 = q2 at r2 r2z H2 hM2 z2
  -- the heap of `q2` is `s`'s off the `E` row
  have Hq2 : ∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → rd q2.M y = rd s.M y := fun y hy hy2 =>
    (H2 y hy).trans ((e3 y hy hy2).trans (H0 y hy))
  have hE2 : ∀ t < k, rdK q2.M (eb + t) =
      rdK s.M (wb + t) * (ptK s0 + rdK s.M (jb + t))⁻¹ := fun t ht => by
    rw [rdK_congrB (H2 (eb + t) (by simp only [regs] at heb ⊢; omega)), e1 t ht,
      rdK_congrB (H0 (wb + t) (by simp only [regs] at hwb ⊢; omega)), hjt t ht]
  -- the coordinates
  obtain ⟨c1, c2, c3, hM3⟩ := cLoop_sem I q2 hM2 (k := k) (C := C) (jb := jb) (eb := eb) (cb := cb)
    (cs := cs) (ob := ob) (s0 := s0) (x := x) (lp := rdK q1.M fLp) hk hC hjb heb hcb hob hjb2
    heb2 hcb2 hcs2 hs0 hob2 (by rw [z2, z1, z0]; exact hsz) hOJ hOE
    (fun c hc j hj => (hOY c hc j hj).1) r2.1 r2.2.1 r2.2.2.1 (rdK_congrB r2.2.2.2) r2z
    (fun t ht => by
      rw [Hq2 _ (by simp only [regs] at hjb ⊢; omega) (by rcases hjE with h | h <;> omega),
        hJ t ht])
  have nw_c : ¬ Writes (cBody k jb eb cb cs ob) bS := by
    simp [cBody, aBody, yIR, addrPs, addr1Ps, Writes, Prim.dst, bnw_mulK, bA, bK, bJ, fY, fX, fPr,
      fAc, bT, bN3, bC3, bCi, cTmp, bS]
  have r3 : rd (semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) q2).M bS =
      toWord s0 :=
    (c3 bS (by decide) (by decide) (by decide) nw_c).trans r2.2.2.1
  generalize semXIR I (.loopK bC2 bN2 (toWord C) (cBody k jb eb cb cs ob)) q2 = q3
    at c1 c2 c3 hM3 r3
  -- `s₀ += 1`
  obtain ⟨i1, i2, hM4⟩ := bInc_sem I q3 hM3 (r := bS) (x := s0) (by decide) (by decide) r3
  refine ⟨fun c hc => ?_, i1, fun y hy hy2 hy3 => ?_, hM4⟩
  · rw [rdK_congrB (i2 (ob + k * c + s0) (by simp only [regs] at hob; simp only [bS]; omega)),
      c1 c hc, hL1]
    have hy' : ∀ j, j ∈ (List.range k).map x ∨ j = s0 →
        rdK q2.M (cb + cs * j + c) = rdK s.M (cb + cs * j + c) := fun j hj =>
      rdK_congrB (Hq2 _ (by simp only [regs] at hcb ⊢; omega)
        (by rcases (hOY c hc j hj).2 with h | h <;> omega))
    split_ifs
    · exact hy' s0 (.inr rfl)
    · refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
      have ht' := Finset.mem_range.1 ht
      rw [hy' (x t) (.inl (List.mem_map.2 ⟨t, List.mem_range.2 ht', rfl⟩)), hE2 t ht']
  · rw [i2 y (by simp only [regs] at hy; simp only [bS]; omega), c2 y hy hy3, Hq2 y hy hy2]

/-! ## The layout and the target loop -/

/-- **The interpolation's layout** on a memory of `sz` words: the list `J` (`k` words at `jb`),
the tables `W` and `E` (`k` words at `wb`, `eb`), the output (`k·C` words at `ob`; coordinate `c`
of target `s` at `ob + k·c + s`) and the column store (`y_c(j)` at `cb + cs·j + c` for
`j < 2^15`, `c < C ≤ cs`: inside `[cb, cb + cs·2^15)`). All lie above the registers and below
`2^64`; the written regions `W`, `E`, `O` lie inside the memory and are disjoint from each other
and from `J` and the column store (`J` and the store are only read and may overlap). -/
structure BaryLay (k C jb wb eb cb cs ob sz : ℕ) : Prop where
  kN : k ≤ 2 ^ 15
  cC : C ≤ cs
  rJ : regs ≤ jb
  rW : regs ≤ wb
  rE : regs ≤ eb
  rO : regs ≤ ob
  rY : regs ≤ cb
  tJ : jb + k < 2 ^ 64
  tW : wb + k < 2 ^ 64
  tE : eb + k < 2 ^ 64
  tO : ob + k * C < 2 ^ 64
  tY : cb + cs * 2 ^ 15 < 2 ^ 64
  zW : wb + k ≤ sz
  zE : eb + k ≤ sz
  zO : ob + k * C ≤ sz
  dJW : jb + k ≤ wb ∨ wb + k ≤ jb
  dJE : jb + k ≤ eb ∨ eb + k ≤ jb
  dJO : jb + k ≤ ob ∨ ob + k * C ≤ jb
  dWE : wb + k ≤ eb ∨ eb + k ≤ wb
  dWO : wb + k ≤ ob ∨ ob + k * C ≤ wb
  dEO : eb + k ≤ ob ∨ ob + k * C ≤ eb
  dYW : cb + cs * 2 ^ 15 ≤ wb ∨ wb + k ≤ cb
  dYE : cb + cs * 2 ^ 15 ≤ eb ∨ eb + k ≤ cb
  dYO : cb + cs * 2 ^ 15 ≤ ob ∨ ob + k * C ≤ cb

/-- The value of target `s₀`, coordinate `c`, on the heap `M` (the list `J`, the table `W` and
the column store). -/
def sValK (M : Mem) (k jb wb cb cs : ℕ) (x : ℕ → ℕ) (s0 c : ℕ) : BF64 :=
  if ∏ t ∈ range k, (ptK s0 + rdK M (jb + t)) = 0 then rdK M (cb + cs * s0 + c)
  else (∏ t ∈ range k, (ptK s0 + rdK M (jb + t))) *
    ∑ t ∈ range k, rdK M (cb + cs * x t + c) * (rdK M (wb + t) * (ptK s0 + rdK M (jb + t))⁻¹)

/-- **The target loop**: `out[c][s] = sValK s c` for every `s < k`, `c < C`; the heap outside
the `E` row and the output rows is kept. -/
theorem sLoop_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb wb eb cb cs ob : ℕ} {x : ℕ → ℕ} (hL : BaryLay k C jb wb eb cb cs ob s.M.size)
    (hJn : ∀ t < k, x t < 2 ^ 15) (hN : rd s.M bN1 = toWord k) (hS : rd s.M bS = toWord 0)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (x t)) :
    (∀ s0 < k, ∀ c < C, rdK (semXIR I (.loopK bC1 bN1 (toWord k)
        (sBody k C jb wb eb cb cs ob)) s).M (ob + k * c + s0) =
      sValK s.M k jb wb cb cs x s0 c) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → (y < ob ∨ ob + k * C ≤ y) →
      rd (semXIR I (.loopK bC1 bN1 (toWord k) (sBody k C jb wb eb cb cs ob)) s).M y =
        rd s.M y) ∧
    Inv (semXIR I (.loopK bC1 bN1 (toWord k) (sBody k C jb wb eb cb cs ob)) s).M := by
  obtain ⟨hkN, hcC, rJ, rW, rE, rO, rY, tJ, tW, tE, tO, tY, zW, zE, zO, dJW, dJE, dJO, dWE, dWO,
    dEO, dYW, dYE, dYO⟩ := hL
  have hk64 : k < 2 ^ 64 := by omega
  have hC64 : C < 2 ^ 64 := by omega
  have hcol : ∀ j' < 2 ^ 15, ∀ c < C, cb + cs * j' + c < cb + cs * 2 ^ 15 := fun j' hj' c hc => by
    have := ycell_lt hj' (show c < cs by omega); omega
  let Q : ℕ → St → Prop := fun j st => Inv st.M ∧ st.M.size = s.M.size ∧ rd st.M bS = toWord j ∧
    (∀ s0 < j, ∀ c < C, rdK st.M (ob + k * c + s0) = sValK s.M k jb wb cb cs x s0 c) ∧
    (∀ y, regs ≤ y → (y < eb ∨ eb + k ≤ y) → (y < ob ∨ ob + k * C ≤ y) → rd st.M y = rd s.M y)
  have ef : ∀ i, i ≠ bC1 → i ≠ cTmp → rd (entryK bC1 bN1 (toWord k) s.M) i = rd s.M i :=
    fun i a b => entryK_frame _ (Ne.symm a) (Ne.symm b)
  have h := loopK_run I (c := bC1) (n := bN1) (K := k) (sBody k C jb wb eb cb cs ob) Q s hM
    (by decide) (by decide) (by decide) hN hk64 ⟨inv_entryK hM (by decide), size_entryK .., by
        rw [ef _ (by decide) (by decide), hS],
      fun s0 hs0 => absurd hs0 (Nat.not_lt_zero _),
      fun y hy _ _ => ef y (by simp only [regs, bC1] at hy ⊢; omega)
        (by simp only [regs, cTmp] at hy ⊢; omega)⟩ ?_
  · exact ⟨h.2.2.2.1, h.2.2.2.2, h.1⟩
  · rintro j st hj ⟨hM', hz, hS', hV, hH⟩
    simp only [regs] at rJ rW rE rO rY
    obtain ⟨b1, b2, b3, hM2⟩ := sBody_sem I st hM' (k := k) (C := C) (jb := jb) (wb := wb)
      (eb := eb) (cb := cb) (cs := cs) (ob := ob) (s0 := j) (x := x) hk64 hC64 hj
      (by simp only [regs]; omega) (by simp only [regs]; omega) (by simp only [regs]; omega)
      (by simp only [regs]; omega) (by simp only [regs]; omega) tJ tW tE
      (fun t ht c hc => by have := hcol _ (hJn t ht) c hc; omega)
      (fun c hc => by have := hcol j (by omega) c hc; omega)
      tO (by rw [hz]; exact zO) (by rw [hz]; exact zE) dJE dWE dJO.symm dEO.symm
      (fun c hc j' hj' => by
        have h' : j' < 2 ^ 15 := by
          rcases hj' with h' | rfl
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h'; exact hJn t (List.mem_range.1 ht)
          · omega
        have := hcol j' h' c hc
        exact ⟨by rcases dYO with h | h <;> omega, by rcases dYE with h | h <;> omega⟩) hS'
      (fun t ht => by
        rw [hH _ (by simp only [regs]; omega) (by rcases dJE with h | h <;> omega)
          (by rcases dJO with h | h <;> omega), hJ t ht])
    refine ⟨inv_decS hM2 (by decide), by rw [size_decS, size_sem, hz],
      by rw [rd_decS (by decide), b2], fun s0 hs0 c hc => ?_, fun y hy hy2 hy3 => ?_⟩
    · have hlt := out_ltB (k := k) hc (show s0 < k by omega)
      rw [rdK_congrB (rd_decS (by simp only [bC1]; omega) _)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs0 with hs0 | rfl
      · have hne : ∀ c' < C, ob + k * c + s0 ≠ ob + k * c' + j := fun c' _ => by
          have := cellB_ne (k := k) (c := c) (c' := c') (show s0 < k by omega) hj (by omega)
          omega
        rw [rdK_congrB (b3 _ (by simp only [regs]; omega) (by rcases dEO with h | h <;> omega) hne),
          hV s0 hs0 c hc]
      · rw [b1 c hc, sValK]
        have hcl : ∀ j' < 2 ^ 15, rdK st.M (cb + cs * j' + c) = rdK s.M (cb + cs * j' + c) :=
          fun j' hj' => rdK_congrB (hH _ (by simp only [regs]; omega)
            (by have := hcol j' hj' c hc; rcases dYE with h | h <;> omega)
            (by have := hcol j' hj' c hc; rcases dYO with h | h <;> omega))
        have hjt : ∀ t < k, rdK st.M (jb + t) = rdK s.M (jb + t) := fun t ht =>
          rdK_congrB (hH _ (by simp only [regs]; omega) (by rcases dJE with h | h <;> omega)
            (by rcases dJO with h | h <;> omega))
        have hwt : ∀ t < k, rdK st.M (wb + t) = rdK s.M (wb + t) := fun t ht =>
          rdK_congrB (hH _ (by simp only [regs]; omega) (by rcases dWE with h | h <;> omega)
            (by rcases dWO with h | h <;> omega))
        have hP : ∏ t ∈ range k, (ptK s0 + rdK st.M (jb + t)) =
            ∏ t ∈ range k, (ptK s0 + rdK s.M (jb + t)) :=
          Finset.prod_congr rfl fun t ht => by rw [hjt t (Finset.mem_range.1 ht)]
        rw [hP, hcl s0 (by omega)]
        split_ifs
        · rfl
        · refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
          have ht' := Finset.mem_range.1 ht
          rw [hcl _ (hJn t ht'), hwt t ht', hjt t ht']
    · rw [rd_decS (by simp only [bC1, regs] at hy ⊢; omega)]
      rw [b3 y hy hy2 (fun c' hc' => by have := out_ltB (k := k) hc' hj; omega), hH y hy hy2 hy3]

/-! ## The whole program -/

/-- **The interpolation on the machine**: for the list `Jl` at `jb` (`k` entries below `2^15`)
and the column store at `cb`, `out[c][s] = baryValK Jl k s y_c` for every target `s < k` and
coordinate `c < C`, with `y_c(j)` the store's element `cb + cs·j + c`; the heap outside `W`, `E`
and the output rows is kept. -/
theorem baryIR_sem (I : Array Word) (s : St) (hM : Inv s.M)
    {k C jb wb eb cb cs ob : ℕ} {Jl : List ℕ} (hL : BaryLay k C jb wb eb cb cs ob s.M.size)
    (hJn : ∀ t < k, Jl.getD t 0 < 2 ^ 15)
    (hJ : ∀ t < k, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    (∀ s0 < k, ∀ c < C, rdK (semXIR I (baryIR k C jb wb eb cb cs ob) s).M (ob + k * c + s0) =
        baryValK Jl k s0 (fun j => rdK s.M (cb + cs * j + c))) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + k ≤ y) → (y < eb ∨ eb + k ≤ y) →
      (y < ob ∨ ob + k * C ≤ y) → rd (semXIR I (baryIR k C jb wb eb cb cs ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (baryIR k C jb wb eb cb cs ob) s).M := by
  have hL' := hL
  obtain ⟨hkN, hcC, rJ, rW, rE, rO, rY, tJ, tW, tE, tO, tY, zW, zE, zO, dJW, dJE, dJO, dWE, dWO,
    dEO, dYW, dYE, dYO⟩ := hL'
  have hk64 : k < 2 ^ 64 := by omega
  simp only [regs] at rJ rW rE rO rY
  rw [baryIR]
  simp only [semXIR_seq]
  -- `W`
  obtain ⟨w1, w2, hM1⟩ := wtIR_sem I s hM (k := k) (jb := jb) (wb := wb) (G := djK Jl) hk64
    (by simp only [regs]; omega) (by simp only [regs]; omega) tJ tW zW dJW
    (fun m hm => rdK_toWord (hJ m hm))
  have z1 := size_sem I (wtIR k jb wb) s
  generalize semXIR I (wtIR k jb wb) s = q1 at w1 w2 hM1 z1
  -- `s := 0`, `bN1 := k`
  have hs1 := hM1.1
  have p : rd (semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1).M bS = toWord 0 ∧
      rd (semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1).M bN1 = toWord k := by
    rw [sem_blk]
    simp only [runPrims, List.foldl, Prim.run]
    refine ⟨?_, ?_⟩ <;>
    simp (disch := first | decide |
      ((try simp only [size_set]); exact lt_of_lt_of_le (by decide) hs1))
      only [rd_set_self, rd_set_ne] <;> rfl
  have p3 : ∀ i, i ≠ bS → i ≠ bN1 →
      rd (semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1).M i = rd q1.M i :=
    fun i h1 h2 => by
      rw [sem_blk]
      exact rd_runPrims_of_not_writes (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro p (rfl | rfl) <;> simp only [Prim.dst] <;> omega) _
  have hM2 := inv_sem I (P := .blk [.const bS 0, .const bN1 (toWord k)]) (s := q1)
    (by simp [WF, Prim.dst, bS, bN1]) hM1
  have z2 := size_sem I (.blk [.const bS 0, .const bN1 (toWord k)]) q1
  generalize semXIR I (.blk [.const bS 0, .const bN1 (toWord k)]) q1 = q2 at p p3 hM2 z2
  have H2 : ∀ y, regs ≤ y → (y < wb ∨ wb + k ≤ y) → rd q2.M y = rd s.M y := fun y hy hy2 =>
    (p3 y (by simp only [regs, bS] at hy ⊢; omega) (by simp only [regs, bN1] at hy ⊢; omega)).trans
      (w2 y hy hy2)
  have hL2 : BaryLay k C jb wb eb cb cs ob q2.M.size := by rw [z2, z1]; exact hL
  obtain ⟨l1, l2, hM3⟩ := sLoop_sem I q2 hM2 (x := fun t => Jl.getD t 0) hL2 hJn p.2 p.1
    (fun t ht => by
      rw [H2 _ (by simp only [regs]; omega) (by rcases dJW with h | h <;> omega), hJ t ht])
  refine ⟨fun s0 hs0 c hc => ?_, fun y hy hy1 hy2 hy3 => ?_, hM3⟩
  · rw [l1 s0 hs0 c hc, sValK, baryValK]
    have hcl : ∀ j < 2 ^ 15, rdK q2.M (cb + cs * j + c) = rdK s.M (cb + cs * j + c) := fun j hj =>
      rdK_congrB (H2 _ (by simp only [regs]; omega)
        (by have := ycell_lt hj (show c < cs by omega); rcases dYW with h | h <;> omega))
    have hd : ∀ t < k, rdK q2.M (jb + t) = djK Jl t := fun t ht =>
      (rdK_congrB (H2 _ (by simp only [regs]; omega) (by rcases dJW with h | h <;> omega))).trans
        (rdK_toWord (hJ t ht))
    have hw : ∀ t < k, rdK q2.M (wb + t) = wgtK Jl k t := fun t ht =>
      (rdK_congrB (p3 _ (by simp only [bS]; omega) (by simp only [bN1]; omega))).trans (w1 t ht)
    have hP : ∏ t ∈ range k, (ptK s0 + rdK q2.M (jb + t)) = ellK Jl k s0 :=
      Finset.prod_congr rfl fun t ht => by rw [hd t (Finset.mem_range.1 ht)]
    rw [hP, hcl s0 (by omega)]
    by_cases h0 : ellK Jl k s0 = 0
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
      refine congrArg (_ * ·) (Finset.sum_congr rfl fun t ht => ?_)
      have ht' := Finset.mem_range.1 ht
      rw [hcl _ (hJn t ht'), hw t ht', hd t ht', eAtK]
  · rw [l2 y hy hy2 hy3, H2 y hy hy1]

/-- **The interpolation computed**: with `k = |Jl|`, `Jl` without repeats and below `2^15`,
every `out[c][s]` is `interpF ptK J y_c s` (`J = Jl.toFinset`, `y_c(j)` the element at
`cb + cs·j + c`). -/
theorem baryIR_interp (I : Array Word) (s : St) (hM : Inv s.M)
    {C jb wb eb cb cs ob : ℕ} {Jl : List ℕ}
    (hL : BaryLay Jl.length C jb wb eb cb cs ob s.M.size) (hnd : Jl.Nodup)
    (hJn : ∀ j ∈ Jl, j < 2 ^ 15)
    (hJ : ∀ t < Jl.length, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    ∀ s0 < Jl.length, ∀ c < C,
      rdK (semXIR I (baryIR Jl.length C jb wb eb cb cs ob) s).M (ob + Jl.length * c + s0) =
      interpF ptK Jl.toFinset (fun j => rdK s.M (cb + cs * j + c)) s0 := by
  have hget : ∀ t < Jl.length, Jl.getD t 0 < 2 ^ 15 := fun t ht => by
    rw [List.getD_eq_getElem _ _ ht]; exact hJn _ (List.getElem_mem ht)
  intro s0 hs0 c hc
  rw [(baryIR_sem I s hM hL hget hJ).1 s0 hs0 c hc]
  exact baryValK_eq hnd hJn (by have := hL.kN; omega) _

/-- **lvm's instance** (`k = 2^13` positions, `C = 64` rows, the word `wd` at `wB + 64·q + t`):
row `t` of the output (at `ob + 2^13·t`) is the interpolation of the read word's leaf word `t` on
`J`, at the points `ptK s`, `s < 2^13`; the heap outside `W`, `E` and the output is kept. -/
theorem baryIR_lvm (I : Array Word) (s : St) (hM : Inv s.M) {jb wb eb wB ob : ℕ} {Jl : List ℕ}
    (hlen : Jl.length = 2 ^ 13) (hnd : Jl.Nodup) (hJn : ∀ j ∈ Jl, j < 2 ^ 15)
    (hL : BaryLay (2 ^ 13) 64 jb wb eb wB 64 ob s.M.size)
    (hJ : ∀ t < 2 ^ 13, rd s.M (jb + t) = toWord (Jl.getD t 0)) :
    (∀ s0 < 2 ^ 13, ∀ t < 64,
      rdK (semXIR I (baryIR (2 ^ 13) 64 jb wb eb wB 64 ob) s).M (ob + 2 ^ 13 * t + s0) =
      interpF ptK Jl.toFinset (fun j => rdK s.M (wB + 64 * j + t)) s0) ∧
    (∀ y, regs ≤ y → (y < wb ∨ wb + 2 ^ 13 ≤ y) → (y < eb ∨ eb + 2 ^ 13 ≤ y) →
      (y < ob ∨ ob + 2 ^ 13 * 64 ≤ y) →
      rd (semXIR I (baryIR (2 ^ 13) 64 jb wb eb wB 64 ob) s).M y = rd s.M y) ∧
    Inv (semXIR I (baryIR (2 ^ 13) 64 jb wb eb wB 64 ob) s).M := by
  have hget : ∀ t < 2 ^ 13, Jl.getD t 0 < 2 ^ 15 := fun t ht => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hJn _ (List.getElem_mem _)
  have hb := baryIR_sem I s hM hL hget hJ
  refine ⟨fun s0 hs0 t ht => ?_, hb.2.1, hb.2.2⟩
  rw [hb.1 s0 hs0 t ht, ← hlen]
  exact baryValK_eq hnd hJn (by omega) _

end Lvm.X
