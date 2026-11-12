-- New for lvm (HAR-BT): phase 3's block weights (`eqW` of the GKR point above each stacked block:
-- per level a low `eq` table, QA2's `eqTab`, times a high part computed once per prefix), the
-- leaf-form constants, one static block's merged push/pull value (`dG`), the per-table folds and term.
-- Searched QA2 (`LvmQWhirBatch.eqTab`, reused), WP-9b (`LvmM3FidBus`: the same weights over `E`).
import LvmQAsmArith2TabG

/-!
# Weights, constants, blocks

* `eqWG fs x`: `eqW` of the factor cells (`(1 + ζ_i, ζ_i)`) at `x`, one row per coordinate.
* `bwG … κ q`: `eqW (ζ.drop κ) q` = (table entry of the low `s` bits) · (high part, from the list
  `hi` or computed); correct for any static choice of tables and high parts (`bwG_sound`).
* `tkG`: `F = fp₀ + fp₁`, `F·β`, `F·eqα_i`, `γ_r = eqα₂(fp₀ x + fp₁)`, `eqα₂ fp₀`, `eqα₂ fp₁`, and per
  separator `F(β + eqα₀ sep)` (read) / `+ eqα₂ fp₀` (seed).
* `dG b`: `fp₀ · push_b + fp₁ · pull_b` at the evaluations (`dG_sound`, = `dval_eq`'s right side).
* `ppFoldG`, `cFoldG`, `termG`: a table's term `ξ^{cur}·H + Σ_pp w·D + fp₂ Σ_c w·x_c`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.M3 Lvm.Loop Lvm.Loop.Build

/-! ## `eqW` from factor cells -/

/-- `eqW` of the factor cells `(1 + ζ_i, ζ_i)` at `x`. -/
def eqWG (z o : Cell) : List (Cell × Cell) → Nat → BM Cell
  | [], _ => pure o
  | f :: fs, x => do
    let r ← eqWG z o fs (x / 2)
    mulAdd .E (if x % 2 = 1 then f.2 else f.1) r z

/-- The factor cells of a point: `(1 + ζ_i, ζ_i)`. -/
def facG : List Cell → BM (List (Cell × Cell))
  | [] => pure []
  | c :: cs => do
    let f0 ← lin .E 0 1 c c
    let fs ← facG cs
    pure ((f0, c) :: fs)

/-- Factor cells are `(1 + ζ_i, ζ_i)`. -/
def FacOk (M : Mem) (fs : List (Cell × Cell)) : Prop := ∀ f ∈ fs, f.1.val M = 1 + f.2.val M

section
variable {c : Ctx} {M : Mem} {z o : Cell}

theorem one_add_eq_sub (a : FE) : 1 + a = 1 - a := by rw [sub_eq_add_neg, CharTwo.neg_eq]

theorem eqWG_sound (hz : z.val M = 0) (ho : o.val M = 1) :
    ∀ (fs : List (Cell × Cell)) (x : Nat), FacOk M fs →
      SoundG c M (eqWG z o fs x) fun r => r.val M = Loop.eqW (fs.map (·.2.val M)) x
  | [], _, _ => soundG_pure (by rw [ho]; rfl)
  | f :: fs, x, hf => soundG_bind (eqWG_sound hz ho fs (x / 2) fun g hg => hf g (List.mem_cons_of_mem _ hg))
      fun r hr => soundG_mono (soundG_aspec (QB.aspec_mulAdd .E _ r z)) fun y hy => by
        rw [hy.1, hr, hz, add_zero, List.map_cons, Loop.eqW]
        split
        · rfl
        · rw [hf f List.mem_cons_self, one_add_eq_sub]

theorem facG_sound : ∀ cs : List Cell, SoundG c M (facG cs) fun fs => fs.map (·.2) = cs ∧ FacOk M fs
  | [] => soundG_pure ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: cs => soundG_bind (soundG_aspec (QB.aspec_lin .E 0 1 x x)) fun f0 hf0 =>
      soundG_bind (facG_sound cs) fun fs hfs => soundG_pure ⟨by simp [hfs.1], fun f hf => by
        rcases List.mem_cons.mp hf with rfl | hf
        · rw [hf0.1, ofK_zero, ofK_one, zero_mul, add_zero, add_comm]
        · exact hfs.2 f hf⟩

end

/-! ## Block weights -/

/-- The low `eq` table of level `κ` with `s` coordinates (QA2's `eqTab`). -/
def lvlG (z o : Cell) (zeta : List Cell) (κ s : Nat) : BM Nat :=
  eqTab (fun i => zeta.getD (κ + i) z) z o false s

/-- The tables of a static list of levels: `(κ, s, base)`. -/
def lvlsG (z o : Cell) (zeta : List Cell) : List (Nat × Nat) → BM (List (Nat × Nat × Nat))
  | [] => pure []
  | (κ, s) :: ls => do
    let b ← lvlG z o zeta κ s
    let r ← lvlsG z o zeta ls
    pure ((κ, s, b) :: r)

/-- High parts `eqW (ζ.drop l) h` of a static list of prefixes. -/
def hisG (z o : Cell) (facs : List (Cell × Cell)) : List (Nat × Nat) → BM (List ((Nat × Nat) × Cell))
  | [] => pure []
  | (l, h) :: ks => do
    let x ← eqWG z o (facs.drop l) h
    let r ← hisG z o facs ks
    pure (((l, h), x) :: r)

/-- A high part: from the list, else computed. -/
def hiG (z o : Cell) (facs : List (Cell × Cell)) (hi : List ((Nat × Nat) × Cell)) (l h : Nat) : BM Cell :=
  match hi.find? (fun e => decide (e.1 = (l, h))) with
  | some e => pure e.2
  | none => eqWG z o (facs.drop l) h

/-- **The weight `eqW (ζ.drop κ) q`** of a block at level `κ`, prefix `q` (`D` coordinates). -/
def bwG (z o : Cell) (facs : List (Cell × Cell)) (lt : List (Nat × Nat × Nat))
    (hi : List ((Nat × Nat) × Cell)) (D κ q : Nat) : BM Cell :=
  match lt.find? (fun e => decide (e.1 = κ ∧ e.2.1 ≠ 0 ∧ κ + e.2.1 ≤ D)) with
  | some e => do
    let h ← hiG z o facs hi (κ + e.2.1) (q / 2 ^ e.2.1)
    mulAdd .E h (ec (e.2.2 + q % 2 ^ e.2.1)) z
  | none => hiG z o facs hi κ q

/-- The low point of level `κ` with `s` coordinates. -/
def lowPt (ζ : List FE) (κ s : Nat) : List FE := (List.range s).map fun i => ζ.getD (κ + i) 0

/-- What the level tables hold. -/
def LvlOk (M : Mem) (ζ : List FE) (lt : List (Nat × Nat × Nat)) : Prop :=
  ∀ e ∈ lt, ∀ x < 2 ^ e.2.1, M.e (e.2.2 + x) = Loop.eqW (lowPt ζ e.1 e.2.1) x

/-- What the high parts hold. -/
def HiOk (M : Mem) (ζ : List FE) (hi : List ((Nat × Nat) × Cell)) : Prop :=
  ∀ e ∈ hi, e.2.val M = Loop.eqW (ζ.drop e.1.1) e.1.2

theorem lowPt_eq {ζ : List FE} {κ s : Nat} (h : κ + s ≤ ζ.length) : lowPt ζ κ s = (ζ.drop κ).take s := by
  apply List.ext_getElem
  · simp [lowPt]; omega
  · intro i h1 h2
    simp only [lowPt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    rw [List.getD_eq_getElem _ _ (by simp [lowPt] at h1; omega)]

theorem eqW_split {ζ : List FE} {κ s : Nat} (h : κ + s ≤ ζ.length) (q : Nat) :
    Loop.eqW (ζ.drop κ) q = Loop.eqW (lowPt ζ κ s) (q % 2 ^ s) * Loop.eqW (ζ.drop (κ + s)) (q / 2 ^ s) := by
  have hl : (lowPt ζ κ s).length = s := by simp [lowPt]
  rw [show ζ.drop κ = lowPt ζ κ s ++ ζ.drop (κ + s) by
    rw [lowPt_eq h, ← List.drop_drop, List.take_append_drop], Build.eqW_append, hl]

section
variable {c : Ctx} {M : Mem} {z o : Cell}

theorem facs_drop {facs : List (Cell × Cell)} {ζ : List FE} (hf : (facs.map (·.2)).map (·.val M) = ζ)
    (l : Nat) : (facs.drop l).map (·.2.val M) = ζ.drop l := by
  rw [← hf, List.map_map, List.map_drop]; rfl

theorem facOk_drop {facs : List (Cell × Cell)} (hf : FacOk M facs) (l : Nat) : FacOk M (facs.drop l) :=
  fun f h => hf f (List.mem_of_mem_drop h)

theorem hisG_sound (hz : z.val M = 0) (ho : o.val M = 1) {facs : List (Cell × Cell)} {ζ : List FE}
    (hf1 : (facs.map (·.2)).map (·.val M) = ζ) (hf2 : FacOk M facs) :
    ∀ ks : List (Nat × Nat), SoundG c M (hisG z o facs ks) fun hi => HiOk M ζ hi
  | [] => soundG_pure fun _ h => absurd h List.not_mem_nil
  | (l, h) :: ks => soundG_bind (eqWG_sound hz ho _ h (facOk_drop hf2 l)) fun x hx =>
      soundG_bind (hisG_sound hz ho hf1 hf2 ks) fun r hr => soundG_pure fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · rw [hx, facs_drop hf1]
        · exact hr e he

theorem hiG_sound (hz : z.val M = 0) (ho : o.val M = 1) {facs : List (Cell × Cell)} {ζ : List FE}
    (hf1 : (facs.map (·.2)).map (·.val M) = ζ) (hf2 : FacOk M facs) {hi : List ((Nat × Nat) × Cell)}
    (hhi : HiOk M ζ hi) (l h : Nat) :
    SoundG c M (hiG z o facs hi l h) fun r => r.val M = Loop.eqW (ζ.drop l) h := by
  unfold hiG
  split
  · rename_i e he
    have h1 := List.find?_some he
    have h2 := List.mem_of_find?_eq_some he
    simp only [decide_eq_true_eq] at h1
    refine soundG_pure ?_
    rw [hhi e h2, h1]
  · exact soundG_mono (eqWG_sound hz ho _ h (facOk_drop hf2 l)) fun r hr => by rw [hr, facs_drop hf1]

/-- **A block weight.** -/
theorem bwG_sound (hz : z.val M = 0) (ho : o.val M = 1) {facs : List (Cell × Cell)} {ζ : List FE}
    (hf1 : (facs.map (·.2)).map (·.val M) = ζ) (hf2 : FacOk M facs) {hi : List ((Nat × Nat) × Cell)}
    (hhi : HiOk M ζ hi) {lt : List (Nat × Nat × Nat)} (hlt : LvlOk M ζ lt) {D : Nat} (hD : D = ζ.length)
    (κ q : Nat) :
    SoundG c M (bwG z o facs lt hi D κ q) fun r => r.val M = Loop.eqW (ζ.drop κ) q := by
  unfold bwG
  split
  · rename_i e he
    have h1 := List.find?_some he
    have h2 := List.mem_of_find?_eq_some he
    simp only [decide_eq_true_eq] at h1
    refine soundG_bind (hiG_sound hz ho hf1 hf2 hhi _ _) fun h hh =>
      soundG_mono (soundG_aspec (QB.aspec_mulAdd .E h _ z)) fun r hr => ?_
    rw [hr.1, hh, hz, add_zero, Cell.val_E, hlt e h2 _ (Nat.mod_lt _ (by positivity)), h1.1,
      eqW_split (s := e.2.1) (by rw [← hD]; exact h1.2.2) q, mul_comm]
  · exact hiG_sound hz ho hf1 hf2 hhi κ q

end

section
variable {c : Ctx} {M : Mem} {z o : Cell}

theorem lvlsG_sound (hz : z.val M = 0) (hzE : z.ty = .E) (hoE : o.ty = .E) (ho : o.val M = 1)
    {zeta : List Cell} (hzeE : ∀ x ∈ zeta, x.ty = .E) {ζ : List FE} (hζ : vs M zeta = ζ) :
    ∀ ls : List (Nat × Nat), SoundG c M (lvlsG z o zeta ls) fun lt => LvlOk M ζ lt
  | [] => soundG_pure fun _ h => absurd h List.not_mem_nil
  | (κ, s) :: ls => by
    refine soundG_bind (Φ := fun b => ∀ x < 2 ^ s, M.e (b + x) = Loop.eqW (lowPt ζ κ s) x)
      (fun p hH _ => ?_) fun b hb => soundG_bind (lvlsG_sound hz hzE hoE ho hzeE hζ ls) fun r hr =>
        soundG_pure fun e he => by
          rcases List.mem_cons.mp he with rfl | he
          · exact hb
          · exact hr e he
    have hal : ∀ i, (zeta.getD (κ + i) z).ty = .E := fun i => by
      rw [List.getD_eq_getElem?_getD]
      cases h : zeta[κ + i]? with
      | none => exact hzE
      | some x => exact hzeE x (List.mem_of_getElem? h)
    have hone : M.e o.n = 1 := by rw [← ho]; rcases o with ⟨τ, n⟩; simp at hoE; subst hoE; rfl
    have hlen : (lowPt ζ κ s).length = s := by simp [lowPt]
    have hv : ∀ i < (lowPt ζ κ s).length, (zeta.getD (κ + i) z).val M = (lowPt ζ κ s).getD i 0 := by
      intro i hi
      rw [List.getD_eq_getElem (lowPt ζ κ s) 0 hi]
      rw [hlen] at hi
      simp only [lowPt, List.getElem_map, List.getElem_range, ← hζ, vs]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases zeta[κ + i]? <;> simp [hz]
    have := eqTab_eq (fun i => zeta.getD (κ + i) z) z o false (lowPt ζ κ s) (p := p)
      (by rw [hlen]; exact hH) hz hal hone hv
    intro x hx
    have h2 := this x (by rw [hlen]; exact hx)
    simp only [Bool.false_eq_true, ite_false] at h2
    rw [show lvlG z o zeta κ s p = eqTab (fun i => zeta.getD (κ + i) z) z o false s p from rfl]
    rw [hlen] at h2
    rw [h2, eqKernelA_getD _ _ (by rw [hlen]; exact hx)]

end

/-! ## Leaf constants -/

/-- The leaf-form constants of the table phase. -/
structure TK where
  /-- `fp₀ + fp₁`. -/
  F : Cell
  /-- `F·β`. -/
  fb : Cell
  /-- `F·eqα_i`. -/
  fa : List Cell
  /-- `eqα₂ (fp₀ x + fp₁)`. -/
  gr : Cell
  /-- `eqα₂ fp₀`. -/
  gs0 : Cell
  /-- `eqα₂ fp₁`. -/
  gs1 : Cell
  /-- Per separator: `F(β + eqα₀ sep)` and that `+ eqα₂ fp₀`. -/
  cs : List (FK × Cell × Cell)

/-- `F·eqα_i`, `i < n` (`eqα_i` at `E` cell `eb + i`). -/
def faG (z F : Cell) (eb : Nat) : Nat → BM (List Cell)
  | 0 => pure []
  | n + 1 => do
    let l ← faG z F eb n
    let x ← mulAdd .E F (ec (eb + n)) z
    pure (l ++ [x])

/-- The per-separator constants. -/
def csG (fb fa0 gs0 : Cell) : List FK → BM (List (FK × Cell × Cell))
  | [] => pure []
  | k :: ks => do
    let cr ← lin .E k 0 fb fa0
    let cs ← lin .E 1 0 cr gs0
    let r ← csG fb fa0 gs0 ks
    pure ((k, cr, cs) :: r)

/-- **The constants** (`eqα_i` at `E` cell `eb + i`, `i < n`). -/
def tkG (z fp0 fp1 be : Cell) (eb n : Nat) (seps : List FK) : BM TK := do
  let F ← lin .E 1 0 fp0 fp1
  let fb ← mulAdd .E F be z
  let fa ← faG z F eb n
  let t ← lin .E FK.x 0 fp1 fp0
  let gr ← mulAdd .E (ec (eb + 2)) t z
  let gs0 ← mulAdd .E (ec (eb + 2)) fp0 z
  let gs1 ← mulAdd .E (ec (eb + 2)) fp1 z
  let cs ← csG fb (fa.getD 0 z) gs0 seps
  pure ⟨F, fb, fa, gr, gs0, gs1, cs⟩

/-- What the constants hold. -/
def TKOk (M : Mem) (z : Cell) (K : TK) (fp0 fp1 β : FE) (eqα : List FE) : Prop :=
  (∀ i, (K.fa.getD i z).val M = (fp0 + fp1) * eqα.getD i 0) ∧ K.fb.val M = (fp0 + fp1) * β ∧
    K.gr.val M = eqα.getD 2 0 * (fp0 * FE.ofK FK.x + fp1) ∧ K.gs0.val M = eqα.getD 2 0 * fp0 ∧
    K.gs1.val M = eqα.getD 2 0 * fp1 ∧
    ∀ e ∈ K.cs, e.2.1.val M = (fp0 + fp1) * (β + eqα.getD 0 0 * FE.ofK e.1) ∧
      e.2.2.val M = e.2.1.val M + eqα.getD 2 0 * fp0

section
variable {c : Ctx} {M : Mem} {z : Cell}

theorem faG_sound (hz : z.val M = 0) (F : Cell) (eb : Nat) : ∀ n,
    SoundG c M (faG z F eb n) fun l => l.length = n ∧ ∀ i < n, (l.getD i z).val M = F.val M * M.e (eb + i)
  | 0 => soundG_pure ⟨rfl, fun i h => absurd h (by omega)⟩
  | n + 1 => soundG_bind (faG_sound hz F eb n) fun l hl =>
      soundG_bind (soundG_aspec (QB.aspec_mulAdd .E F (ec (eb + n)) z)) fun x hx =>
        soundG_pure ⟨by simp [hl.1], fun i hi => by
          rcases Nat.lt_or_ge i n with h | h
          · rw [List.getD_append _ _ _ _ (by omega)]; exact hl.2 i h
          · obtain rfl : i = n := by omega
            rw [List.getD_append_right _ _ _ _ (by omega), hl.1, Nat.sub_self, List.getD_cons_zero,
              hx.1, hz, add_zero]; rfl⟩

theorem csG_sound (fb fa0 gs0 : Cell) : ∀ ks : List FK,
    SoundG c M (csG fb fa0 gs0 ks) fun cs => ∀ e ∈ cs,
      e.2.1.val M = fb.val M + FE.ofK e.1 * fa0.val M ∧ e.2.2.val M = e.2.1.val M + gs0.val M
  | [] => soundG_pure fun _ h => absurd h List.not_mem_nil
  | k :: ks => soundG_bind (soundG_aspec (QB.aspec_lin .E k 0 fb fa0)) fun cr hcr =>
      soundG_bind (soundG_aspec (QB.aspec_lin .E 1 0 cr gs0)) fun cs hcs =>
        soundG_bind (csG_sound fb fa0 gs0 ks) fun r hr => soundG_pure fun e he => by
          rcases List.mem_cons.mp he with rfl | he
          · refine ⟨?_, ?_⟩
            · rw [hcr.1, ofK_zero, add_zero]
            · rw [hcs.1, ofK_one, ofK_zero, one_mul, add_zero]
          · exact hr e he

theorem tkG_sound (hz : z.val M = 0) (fp0 fp1 be : Cell) (eb n : Nat) (seps : List FK)
    {eqα : List FE} (hlen : eqα.length = n) (hn : 2 < n) (hα : ∀ i < n, M.e (eb + i) = eqα.getD i 0) :
    SoundG c M (tkG z fp0 fp1 be eb n seps) fun K =>
      TKOk M z K (fp0.val M) (fp1.val M) (be.val M) eqα := by
  unfold tkG
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E 1 0 fp0 fp1)) fun F hF => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E F be z)) fun fb hfb => ?_
  refine soundG_bind (faG_sound hz F eb n) fun fa hfa => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_lin .E FK.x 0 fp1 fp0)) fun t ht => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (ec (eb + 2)) t z)) fun gr hgr => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (ec (eb + 2)) fp0 z)) fun gs0 hgs0 => ?_
  refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (ec (eb + 2)) fp1 z)) fun gs1 hgs1 => ?_
  refine soundG_bind (csG_sound fb (fa.getD 0 z) gs0 seps) fun cs hcs => soundG_pure ?_
  have hFv : F.val M = fp0.val M + fp1.val M := by rw [hF.1, ofK_one, ofK_zero, one_mul, add_zero]
  have hfa' : ∀ i, (fa.getD i z).val M = (fp0.val M + fp1.val M) * eqα.getD i 0 := by
    intro i
    rcases Nat.lt_or_ge i n with h | h
    · rw [hfa.2 i h, hα i h, hFv]
    · rw [List.getD_eq_default _ _ (by rw [hfa.1]; exact h), hz,
        List.getD_eq_default _ _ (by rw [hlen]; exact h), mul_zero]
  have he2 : M.e (eb + 2) = eqα.getD 2 0 := hα 2 hn
  refine ⟨hfa', by rw [hfb.1, hFv, hz, add_zero], ?_, ?_, ?_, fun e he => ?_⟩
  · rw [hgr.1, Cell.val_E, he2, ht.1, hz, add_zero, ofK_zero, add_zero]; ring
  · rw [hgs0.1, Cell.val_E, he2, hz, add_zero]
  · rw [hgs1.1, Cell.val_E, he2, hz, add_zero]
  · obtain ⟨h1, h2⟩ := hcs e he
    refine ⟨?_, ?_⟩
    · rw [h1, hfb.1, hz, add_zero, hFv, hfa' 0]; ring
    · rw [h2, hgs0.1, Cell.val_E, he2, hz, add_zero]

end

/-! ## A static block's merged push/pull value -/

/-- The separator constant of a block (from the list, else computed). -/
def csepG (z : Cell) (K : TK) (sep : FK) (rd : Bool) : BM Cell :=
  match K.cs.find? (fun e => decide (e.1 = sep)) with
  | some e => pure (if rd then e.2.1 else e.2.2)
  | none => do
    let cr ← lin .E sep 0 K.fb (K.fa.getD 0 z)
    if rd then pure cr else lin .E 1 0 cr K.gs0

/-- `acc + Σ_l F·eqα_{3+l}·P_l`. -/
def limbsG (z : Cell) (ev sc : Nat → Cell) (K : TK) : List (CPoly × Nat) → Cell → BM Cell
  | [], acc => pure acc
  | x :: rest, acc => polyAccS z ev sc (K.fa.getD (3 + x.2) z) acc x.1 >>= limbsG z ev sc K rest

/-- **`fp₀ · push_b + fp₁ · pull_b`** at the evaluations. -/
def dG (z : Cell) (ev sc : Nat → Cell) (K : TK) (b : SBlk) : BM Cell := do
  let c0 ← csepG z K b.key.sep b.rd
  let c1 ← polyAccS z ev sc (K.fa.getD 1 z) c0 b.key.addr
  let c2 ← limbsG z ev sc K b.key.val.zipIdx c1
  mulAdd .E (if b.rd then K.gr else K.gs1) (ev b.col) c2

/-- The polynomials of a block's key. -/
def keyPolys (k : Key) : List CPoly := k.addr :: k.val

/-- Suffix-sum cells are right if a polynomial is geometric. -/
def ScOk (M : Mem) (sc : Nat → Cell) (col : Nat → FE) (P : CPoly) : Prop :=
  (geoMatch P).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k

section
variable {c : Ctx} {M : Mem} {z : Cell} {ev sc : Nat → Cell} {col : Nat → FE}
  {K : TK} {fp0 fp1 β : FE} {eqα : List FE}

theorem csepG_sound (hz : z.val M = 0) (hK : TKOk M z K fp0 fp1 β eqα) (sep : FK) (rd : Bool) :
    SoundG c M (csepG z K sep rd) fun r => r.val M =
      (fp0 + fp1) * (β + eqα.getD 0 0 * FE.ofK sep) + (if rd then 0 else eqα.getD 2 0 * fp0) := by
  obtain ⟨hfa, hfb, -, hgs0, -, hcs⟩ := hK
  unfold csepG
  split
  · rename_i e he
    have h1 := List.find?_some he
    have h2 := hcs e (List.mem_of_find?_eq_some he)
    simp only [decide_eq_true_eq] at h1
    refine soundG_pure ?_
    rw [← h1]
    cases rd
    · simp only [Bool.false_eq_true, ite_false]; rw [h2.2, h2.1]
    · simp only [ite_true, add_zero]; exact h2.1
  · refine soundG_bind (soundG_aspec (QB.aspec_lin .E sep 0 K.fb (K.fa.getD 0 z))) fun cr hcr => ?_
    have hcv : cr.val M = (fp0 + fp1) * (β + eqα.getD 0 0 * FE.ofK sep) := by
      rw [hcr.1, hfb, hfa, ofK_zero, add_zero]; ring
    cases rd
    · exact soundG_mono (soundG_aspec (QB.aspec_lin .E 1 0 cr K.gs0)) fun r hr => by
        rw [hr.1, hcv, hgs0, ofK_one, ofK_zero, one_mul, add_zero]; rfl
    · exact soundG_pure (by rw [hcv]; simp)

theorem limbsG_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (hK : TKOk M z K fp0 fp1 β eqα) :
    ∀ (L : List (CPoly × Nat)) (acc : Cell), (∀ x ∈ L, ScOk M sc col x.1) →
      SoundG c M (limbsG z ev sc K L acc) fun r => r.val M =
        acc.val M + sumE (L.map fun x => (fp0 + fp1) * eqα.getD (3 + x.2) 0 * CPoly.evalE col x.1)
  | [], acc, _ => soundG_pure (by rw [List.map_nil, sumE_nil, add_zero])
  | x :: rest, acc, hsc => soundG_bind (polyAccS_sound hz hev _ acc x.1 (hsc x List.mem_cons_self))
      fun a ha => soundG_mono (limbsG_sound hz hev hK rest a fun y hy => hsc y (List.mem_cons_of_mem _ hy))
        fun r hr => by rw [hr, ha, hK.1, List.map_cons, sumE_cons]; ring

theorem dG_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (hK : TKOk M z K fp0 fp1 β eqα)
    (b : SBlk) (hsc : ∀ P ∈ keyPolys b.key, ScOk M sc col P) :
    SoundG c M (dG z ev sc K b) fun r => r.val M =
      fp0 * (fPush eqα β b).form.value col + fp1 * (fPull eqα β b).form.value col := by
  rw [dval_eq eqα β fp0 fp1 b col]
  unfold dG
  refine soundG_bind (csepG_sound hz hK b.key.sep b.rd) fun c0 hc0 => ?_
  refine soundG_bind (polyAccS_sound hz hev _ c0 b.key.addr (hsc _ List.mem_cons_self)) fun c1 hc1 => ?_
  refine soundG_bind (limbsG_sound hz hev hK b.key.val.zipIdx c1 fun x hx =>
    hsc _ (List.mem_cons_of_mem _ (by
      obtain ⟨h1, h2⟩ := List.mem_zipIdx' hx
      rw [h2]; exact List.getElem_mem _))) fun c2 hc2 => ?_
  refine soundG_mono (soundG_aspec (QB.aspec_mulAdd .E _ (ev b.col) c2)) fun r hr => ?_
  rw [hr.1, hc2, hc1, hc0, hK.1, hev]
  have hl : sumE (b.key.val.zipIdx.map fun x => (fp0 + fp1) * eqα.getD (3 + x.2) 0 * CPoly.evalE col x.1) =
      (fp0 + fp1) * limbsV eqα col b.key.val := by
    rw [limbsV, ← sumE_map_mul]
    exact congrArg sumE (List.map_congr_left fun x _ => by ring)
  rw [hl]
  cases hb : b.rd
  · simp only [Bool.false_eq_true, ite_false, hK.2.2.2.2.1]; ring
  · simp only [ite_true, hK.2.2.1]; ring

end

/-! ## A table's term -/

/-- `acc + Σ w · D_b` over a table's stacked push/pull blocks with their weight cells. -/
def ppFoldG (z : Cell) (ev sc : Nat → Cell) (K : TK) : List ((SBlk × Nat) × Cell) → Cell → BM Cell
  | [], acc => pure acc
  | x :: rest, acc => do
    let d ← dG z ev sc K x.1.1
    let a ← mulAdd .E x.2 d acc
    ppFoldG z ev sc K rest a

/-- `acc + Σ w · x_c` over a table's stacked count blocks. -/
def cFoldG (ev : Nat → Cell) : List (((Nat × Nat × Nat) × Nat) × Cell) → Cell → BM Cell
  | [], acc => pure acc
  | x :: rest, acc => do
    let a ← mulAdd .E x.2 (ev x.1.1.2.2) acc
    cFoldG ev rest a

/-- The key polynomials of a table's push/pull blocks and its constraints. -/
def tPolys (cons : List CPoly) (Lpp : List ((SBlk × Nat) × Cell)) : List CPoly :=
  cons ++ Lpp.flatMap fun x => keyPolys x.1.1.key

/-- Whether a table needs suffix-sum cells. -/
def needS (cons : List CPoly) (Lpp : List ((SBlk × Nat) × Cell)) : Bool :=
  (tPolys cons Lpp).any fun P => (geoMatch P).isSome

/-- The suffix-sum cells of a table, if it needs them. -/
def scG (z : Cell) (ev : List Cell) (b : Bool) : BM (List Cell) :=
  if b then sufG z (fun i => ev.getD i z) 64 else pure []

/-- **A table's term**: `X · H + Σ_pp w·D + fp₂ · Σ_c w·x_c` (`H` the constraints' Horner sum). -/
def termG (z xi X fp2 : Cell) (K : TK) (cons : List CPoly) (ev : List Cell)
    (Lpp : List ((SBlk × Nat) × Cell)) (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) : BM Cell := do
  let sc ← scG z ev (needS cons Lpp)
  let H ← hornerC z (fun i => ev.getD i z) (fun k => sc.getD k z) xi cons
  let sm ← mulAdd .E X H z
  let a ← ppFoldG z (fun i => ev.getD i z) (fun k => sc.getD k z) K Lpp sm
  let cc ← cFoldG (fun i => ev.getD i z) Lc z
  mulAdd .E fp2 cc a

section
variable {c : Ctx} {M : Mem} {z : Cell} {ev sc : Nat → Cell} {col : Nat → FE}
  {K : TK} {fp0 fp1 β : FE} {eqα : List FE}

theorem ppFoldG_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (hK : TKOk M z K fp0 fp1 β eqα) :
    ∀ (L : List ((SBlk × Nat) × Cell)) (acc : Cell), (∀ x ∈ L, ∀ P ∈ keyPolys x.1.1.key, ScOk M sc col P) →
      SoundG c M (ppFoldG z ev sc K L acc) fun r => r.val M = acc.val M + sumE (L.map fun x =>
        x.2.val M * (fp0 * (fPush eqα β x.1.1).form.value col + fp1 * (fPull eqα β x.1.1).form.value col))
  | [], acc, _ => soundG_pure (by rw [List.map_nil, sumE_nil, add_zero])
  | x :: rest, acc, hsc => soundG_bind (dG_sound hz hev hK x.1.1 (hsc x List.mem_cons_self)) fun d hd =>
      soundG_bind (soundG_aspec (QB.aspec_mulAdd .E x.2 d acc)) fun a ha =>
        soundG_mono (ppFoldG_sound hz hev hK rest a fun y hy => hsc y (List.mem_cons_of_mem _ hy))
          fun r hr => by rw [hr, ha.1, hd, List.map_cons, sumE_cons]; ring

theorem cFoldG_sound (hev : ∀ i, (ev i).val M = col i) :
    ∀ (L : List (((Nat × Nat × Nat) × Nat) × Cell)) (acc : Cell),
      SoundG c M (cFoldG ev L acc) fun r => r.val M = acc.val M + sumE (L.map fun x => x.2.val M * col x.1.1.2.2)
  | [], acc => soundG_pure (by rw [List.map_nil, sumE_nil, add_zero])
  | x :: rest, acc => soundG_bind (soundG_aspec (QB.aspec_mulAdd .E x.2 (ev x.1.1.2.2) acc)) fun a ha =>
      soundG_mono (cFoldG_sound hev rest a) fun r hr => by
        rw [hr, ha.1, hev, List.map_cons, sumE_cons]; ring

theorem termG_sound (hz : z.val M = 0) (hzE : z.ty = .E) (hK : TKOk M z K fp0 fp1 β eqα)
    (xi X fp2 : Cell) (cons : List CPoly) (ev : List Cell) (Lpp : List ((SBlk × Nat) × Cell))
    (Lc : List (((Nat × Nat × Nat) × Nat) × Cell)) :
    SoundG c M (termG z xi X fp2 K cons ev Lpp Lc) fun r =>
      r.val M = X.val M * polyEval (cons.map (CPoly.evalE ((vs M ev).getD · 0))) (xi.val M) +
        sumE (Lpp.map fun x => x.2.val M * (fp0 * (fPush eqα β x.1.1).form.value ((vs M ev).getD · 0) +
          fp1 * (fPull eqα β x.1.1).form.value ((vs M ev).getD · 0))) +
        fp2.val M * sumE (Lc.map fun x => x.2.val M * (vs M ev).getD x.1.1.2.2 0) := by
  have hev : ∀ i, (ev.getD i z).val M = (vs M ev).getD i 0 := by
    intro i
    simp only [vs, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases ev[i]? <;> simp [hz]
  unfold termG
  refine soundG_bind (Φ := fun (sc : List Cell) => ∀ P ∈ tPolys cons Lpp, ScOk M (fun k => sc.getD k z)
      ((vs M ev).getD · 0) P) ?_ fun sc hsc => ?_
  · unfold scG
    split
    · exact soundG_mono (sufG_sound hev hz 64 le_rfl) fun l hl P _ _ k hk => by
        rcases Nat.lt_or_ge k 64 with h | h
        · have := hl.2 k h; simpa using this
        · obtain rfl : k = 64 := by omega
          show (l.getD 64 z).val M = _
          rw [List.getD_eq_default _ _ (by rw [hl.1]), hz, Sv_64]
    · rename_i hn
      refine soundG_pure fun P hP hg => absurd ?_ hn
      unfold needS; rw [List.any_eq_true]; exact ⟨P, hP, hg⟩
  · refine soundG_bind (hornerC_sound hz hev xi cons fun C hC => hsc C (List.mem_append_left _ hC))
      fun H hH => ?_
    refine soundG_bind (soundG_aspec (QB.aspec_mulAdd .E X H z)) fun sm hsm => ?_
    refine soundG_bind (ppFoldG_sound hz hev hK Lpp sm fun x hx P hP => hsc P
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hx, hP⟩))) fun a ha => ?_
    refine soundG_bind (cFoldG_sound hev Lc z) fun cc hcc => ?_
    refine soundG_mono (soundG_aspec (QB.aspec_mulAdd .E fp2 cc a)) fun r hr => ?_
    rw [hr.1, hcc, ha, hsm.1, hH, hz]; ring

end

end Lvm.Har
