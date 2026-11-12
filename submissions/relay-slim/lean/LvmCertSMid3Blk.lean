-- WP-16b (CERT). New for lvm (O6, the semantic link): WP-14a's block claims (`LvmVEqMid.BClaim`)
-- on the stack of their commitment, read as sums over their block (after WP-2's `sum_placed`,
-- `LvmRingFidelity`), and the multiaffinity of their stack weights (after WP-7's
-- `isMultiaffine_eqEval`, `LvmWhirWeights`).
import LvmVEqMid
import LvmRingFidelity
import LvmWhirWeights
import LvmNodeSoundGood

/-!
# Block claims on the stack

* `eqAbove_boolPoint`: an aligned placement's weight above its window, at a cube point, is the
  block's indicator;
* **`holds_onStack`**: `c.onStack` holds of a commitment `q` iff the weight paired with the block's
  cells is the value; **`holds_point`**: for a point claim, iff the block's extension (`eqAt`) at the
  point is the value;
* **`isMultiaffine_onStack`**: the stack weight of a block claim whose weight is multiaffine on the
  block's variables is multiaffine on the commitment's; `isMultiaffine_eqEvalN`: `eq_eval(z, ·)` is
  multiaffine on any number of coordinates;
* `claimsS`, `HoldsC`, **`holdsC_of_assembleS`**: `assembleS`'s two stack lists hold on `(qr, qm)`
  iff every assembled claim holds on its commitment;
* the link's vocabulary: `TabRet` / `KgRet` (facts of every return of the table phase / of the
  Keccak phases), `BndS` (WP-14c's boundary claims when `n ≤ 2^20`), `KcS` (`kgSpecS`'s claims at
  P20 with WP-14c's accessors; lvm2 S2: the tape's claims in place of `CH`'s).
-/

set_option autoImplicit false

namespace Lvm.ASM

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.KeccakGkr LeanVM.Protocol.Whir.Sound
open Lvm.VEq Finset

/-! ## Block sums -/

/-- **An aligned placement's weight above its window** at a cube point is the block's indicator. -/
theorem eqAbove_boolPoint {v off μ x : ℕ} (hfit : off + 2 ^ v ≤ 2 ^ μ) (hx : x < 2 ^ μ) :
    ({ variableCount := v, index := off } : VPlacement).eqAbove (boolPoint μ x) =
      if x / 2 ^ v = off / 2 ^ v then 1 else 0 := by
  have hv : v ≤ μ := by
    have : 2 ^ v ≤ 2 ^ μ := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hpow : 2 ^ μ = 2 ^ v * 2 ^ (μ - v) := by rw [← pow_add, Nat.add_sub_cancel' hv]
  have hoff : off / 2 ^ v < 2 ^ (μ - v) :=
    Nat.div_lt_of_lt_mul (by rw [← hpow]; have := Nat.two_pow_pos v; omega)
  have hxv : x / 2 ^ v < 2 ^ (μ - v) := Nat.div_lt_of_lt_mul (by rw [← hpow]; exact hx)
  simp only [LeanVM.Protocol.Verifier.Placement.eqAbove, length_boolPoint, selectorPoint_eq_boolPoint,
    Nat.shiftRight_eq_div_pow, drop_boolPoint]
  rw [Complete.eqEval_boolPoint_boolPoint _ _ _ hoff hxv]
  by_cases h : x / 2 ^ v = off / 2 ^ v
  · simp [h]
  · simp [h, Ne.symm h]

/-- **A sum over the stack weighted by an aligned placement and a weight of the window** is the
sum over the block. -/
theorem sum_block {v off μ : ℕ} (hal : 2 ^ v ∣ off) (hfit : off + 2 ^ v ≤ 2 ^ μ)
    (w : List E → E) (q : Column μ) :
    ∑ x : Fin (2 ^ μ), ({ variableCount := v, index := off } : VPlacement).eqAbove (boolPoint μ x) *
        w ((boolPoint μ x).take v) * ofK (q.values.getD x 0) =
      ∑ n ∈ range (2 ^ v), w (boolPoint v n) * ofK (q.values.getD (off + n) 0) := by
  have hv : v ≤ μ := by
    have : 2 ^ v ≤ 2 ^ μ := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  obtain ⟨t, rfl⟩ := hal
  have hpos := Nat.two_pow_pos v
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ ({ variableCount := v, index := 2 ^ v * t } :
      VPlacement).eqAbove (boolPoint μ x) * w ((boolPoint μ x).take v) * ofK (q.values.getD x 0))]
  have hsub : Finset.Ico (2 ^ v * t) (2 ^ v * t + 2 ^ v) ⊆ range (2 ^ μ) := fun x hx ↦ by
    simp only [Finset.mem_Ico] at hx
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_subset hsub fun x hx hn ↦ ?_, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn' := Finset.mem_range.mp hn
    rw [eqAbove_boolPoint hfit (by omega), Nat.mul_add_div hpos, Nat.div_eq_of_lt hn', add_zero,
      Nat.mul_div_cancel_left _ hpos, take_boolPoint μ v _ hv, ← boolPoint_mod v (2 ^ v * t + n),
      Nat.mul_add_mod, Nat.mod_eq_of_lt hn']
    simp
  · have hx := Finset.mem_range.mp hx
    rw [eqAbove_boolPoint hfit hx, Nat.mul_div_cancel_left _ hpos]
    suffices hne : x / 2 ^ v ≠ t by simp [hne]
    intro he
    refine hn (Finset.mem_Ico.mpr ⟨?_, ?_⟩)
    · rw [← he]; exact Nat.mul_div_le x _
    · have := Nat.lt_mul_div_succ x hpos
      rw [he, mul_add, mul_one] at this
      exact this

/-- **A block claim on the stack of its commitment** is the weight paired with the block. -/
theorem holds_onStack {μ : ℕ} (c : BClaim) (hal : 2 ^ c.block.variableCount ∣ c.block.index)
    (hfit : c.block.index + 2 ^ c.block.variableCount ≤ 2 ^ μ) (q : Column μ) :
    StackClaim.Holds μ c.onStack q ↔
      ∑ n ∈ range (2 ^ c.block.variableCount), c.weight (boolPoint c.block.variableCount n) *
        ofK (q.values.getD (c.block.index + n) 0) = c.value := by
  obtain ⟨⟨v, off⟩, w, val⟩ := c
  unfold StackClaim.Holds BClaim.onStack
  exact Eq.congr_left (sum_block hal hfit w q)

/-- **A point claim on a block** is the block's extension (`eqAt`) at the point. -/
theorem holds_point {μ v off : ℕ} (hal : 2 ^ v ∣ off) (hfit : off + 2 ^ v ≤ 2 ^ μ) (z : List E)
    (hz : z.length = v) (val : E) (q : Column μ) :
    StackClaim.Holds μ (BClaim.point ⟨v, off⟩ z val).onStack q ↔
      ∑ n ∈ range (2 ^ v), eqAt z n * ofK (q.values.getD (off + n) 0) = val := by
  subst hz
  rw [holds_onStack _ hal hfit]
  refine Eq.congr_left (Finset.sum_congr rfl fun n _ ↦ ?_)
  change LeanVM.Protocol.Verifier.eqEval z (boolPoint z.length n) * _ = _
  rw [eqEval_boolPoint_eqAt]
  rfl

/-! ## Multiaffine stack weights -/

theorem length_set' (l : List E) (k : ℕ) (X : E) : (l.set k X).length = l.length := List.length_set

/-- A product whose factors depend on disjoint sets of coordinates is multiaffine. -/
theorem isMultiaffine_mul {n : ℕ} {F G : List E → E} (hF : IsMultiaffine n F)
    (hG : IsMultiaffine n G)
    (hd : ∀ l : List E, l.length = n → ∀ k < n,
      (∀ X, F (l.set k X) = F l) ∨ (∀ X, G (l.set k X) = G l)) :
    IsMultiaffine n fun l ↦ F l * G l := by
  intro l hl k hk X
  show F (l.set k X) * G (l.set k X) = (1 - X) * (F (l.set k 0) * G (l.set k 0)) +
    X * (F (l.set k 1) * G (l.set k 1))
  rcases hd l hl k hk with h | h
  · rw [h X, h 0, h 1, hG l hl k hk X]; ring
  · rw [h X, h 0, h 1, hF l hl k hk X]; ring

/-- A function of the first `m ≤ n` coordinates, multiaffine there, is multiaffine on `n`. -/
theorem isMultiaffine_take {m n : ℕ} {Φ : List E → E} (hΦ : IsMultiaffine m Φ) (hmn : m ≤ n) :
    IsMultiaffine n fun l ↦ Φ (l.take m) := by
  intro l hl k hk X
  by_cases hkm : k < m
  · simp only [List.take_set]
    exact hΦ _ (by simp [hl]; omega) k hkm X
  · simp only [List.take_set_of_le (by omega : m ≤ k)]
    ring

/-- A function of the coordinates from `v`, multiaffine there, is multiaffine on `n`. -/
theorem isMultiaffine_drop {v n : ℕ} {Φ : List E → E} (hΦ : IsMultiaffine (n - v) Φ) :
    IsMultiaffine n fun l ↦ Φ (l.drop v) := by
  intro l hl k hk X
  by_cases hkv : k < v
  · simp only [List.drop_set_of_lt hkv]
    ring
  · have e : ∀ Y, (l.set k Y).drop v = (l.drop v).set (k - v) Y := fun Y ↦ by
      rw [List.drop_set, if_neg (by omega)]
    simp only [e]
    exact hΦ _ (by simp [hl]) (k - v) (by omega) X

/-- **`eq_eval(z, ·)` is multiaffine on any number of coordinates** (the zip truncates). -/
theorem isMultiaffine_eqEvalN (z : List E) (n : ℕ) :
    IsMultiaffine n (LeanVM.Protocol.Verifier.eqEval z) := by
  suffices h : ∀ (z l : List E) (k : ℕ), k < l.length → ∀ X : E,
      (List.zipWith (fun x z ↦ 1 + x + z) z (l.set k X)).prod =
        (1 - X) * (List.zipWith (fun x z ↦ 1 + x + z) z (l.set k 0)).prod +
          X * (List.zipWith (fun x z ↦ 1 + x + z) z (l.set k 1)).prod by
    intro l hl k hk X
    simp only [eqEval_eq_list_prod]
    exact h z l k (hl ▸ hk) X
  intro z
  induction z with
  | nil => intro l k _ X; simp
  | cons a z ih =>
    intro l k hk X
    cases l with
    | nil => simp at hk
    | cons b l =>
      cases k with
      | zero => simp only [List.set_cons_zero, List.zipWith_cons_cons, List.prod_cons]; ring
      | succ k =>
        simp only [List.set_cons_succ, List.zipWith_cons_cons, List.prod_cons]
        rw [ih l k (by simpa using hk) X]
        ring

/-- **A block claim's stack weight** is multiaffine on `n` coordinates when its weight is on the
block's `v ≤ n`. -/
theorem isMultiaffine_onStack {n : ℕ} (c : BClaim) (hv : c.block.variableCount ≤ n)
    (hw : IsMultiaffine c.block.variableCount c.weight) : IsMultiaffine n c.onStack.1 := by
  obtain ⟨⟨v, off⟩, w, val⟩ := c
  simp only at hv hw
  have hA : IsMultiaffine n fun l ↦ LeanVM.Protocol.Verifier.eqEval (LeanVM.Protocol.Verifier.selectorPoint (off >>> v) (n - v)) (l.drop v) :=
    isMultiaffine_drop (isMultiaffine_eqEvalN _ _)
  have hW : IsMultiaffine n fun l ↦ w (l.take v) := isMultiaffine_take hw hv
  have hm := isMultiaffine_mul hA hW fun l hl k hk ↦ by
    by_cases hkv : k < v
    · left; intro X; simp only [List.drop_set_of_lt hkv]
    · right; intro X; simp only [List.take_set_of_le (by omega : v ≤ k)]
  intro l hl k hk X
  have h := hm l hl k hk X
  simp only [BClaim.onStack, LeanVM.Protocol.Verifier.Placement.eqAbove, length_set', hl]
  exact h

/-! ## The assembled claims, per commitment -/

/-- The claims of `assembleS` before the split by commitment (lvm2 S2: the tape's claims in place
of `CH`'s and the `CH` link's). -/
def claimsS (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim) (kg : KgOut) :
    List (Com × BClaim) :=
  tableClaimsE T cl ++
    (tapeClaimsE kg.1 pub ++ keccakClaimsE ksBlk kg.2.1).map (.main, ·) ++
    ksOutputClaimsE kg.2.1.1 kg.2.1.2.1 ++
    ksLinkClaimsE kg.2.2.1 kg.2.2.2.1 kg.2.2.2.2

theorem assembleS_eq (T : List Lvm.M3.Tab) (pub : Lvm.Pub) (cl : List ColumnClaim) (kg : KgOut) :
    assembleS T pub cl kg = (((claimsS T pub cl kg).filter (·.1 == .crec)).map (·.2.onStack),
      ((claimsS T pub cl kg).filter (·.1 == .main)).map (·.2.onStack)) := rfl

/-- An assembled claim holds on its commitment. -/
def HoldsC (qm : Column CMain.nu20) (qr : Column 19) (e : Com × BClaim) : Prop :=
  match e.1 with
  | .crec => StackClaim.Holds 19 e.2.onStack qr
  | .main => StackClaim.Holds CMain.nu20 e.2.onStack qm

/-- **`assembleS`'s two lists hold** on `(qr, qm)`: every assembled claim holds on its commitment. -/
theorem holdsC_of_assembleS {T : List Lvm.M3.Tab} {pub : Lvm.Pub} {cl : List ColumnClaim}
    {kg : KgOut} {qm : Column CMain.nu20} {qr : Column 19}
    (h1 : ∀ c ∈ (assembleS T pub cl kg).1, StackClaim.Holds 19 c qr)
    (h2 : ∀ c ∈ (assembleS T pub cl kg).2, StackClaim.Holds CMain.nu20 c qm) :
    ∀ e ∈ claimsS T pub cl kg, HoldsC qm qr e := by
  rw [assembleS_eq] at h1 h2
  intro e he
  obtain ⟨com, b⟩ := e
  cases com with
  | crec => exact h1 _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨he, rfl⟩, rfl⟩)
  | main => exact h2 _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨he, rfl⟩, rfl⟩)

/-- The main-commitment claims of a mapped list. -/
theorem holdsC_main {qm : Column CMain.nu20} {qr : Column 19} {l : List BClaim}
    (h : ∀ e ∈ l.map (Com.main, ·), HoldsC qm qr e) : ∀ b ∈ l, StackClaim.Holds CMain.nu20 b.onStack qm :=
  fun b hb ↦ h _ (List.mem_map.mpr ⟨b, hb, rfl⟩)

/-! ## The link's vocabulary -/

open Lvm.NS (colM ksCol ksY2 msgM msgX Bnd) in
/-- **The chain's boundary claims, when the chain fits `CH`** (`n ≤ 2^20`, which `okS` ensures):
`V_S`'s boundary claims read row `(n − 1) mod 2^20`, so they say nothing of `Bnd` beyond it. -/
def BndS (x : List UInt8) (qm : Column CMain.nu20) : Prop := (hdrOf x).n ≤ 2 ^ 20 → Bnd x qm

/-- **Facts of every return of the table phase** (`lbusTableCheckProg T μ`): a claim on column
`(j, i)` has table `j`'s height coordinates; there are at most `Σ w` claims. -/
def TabRet (T : List Lvm.M3.Tab) (cl : List ColumnClaim) : Prop :=
  (∀ c ∈ cl, ∀ j i, Lvm.M3.colLoc T c.column = some (j, i) →
    c.point.length = (T[j]?.map (·.τ)).getD 0) ∧ cl.length ≤ (T.map (·.w)).sum

/-- **Facts of every return of V_S phases 4–7** (`kgProgS s n`, lvm2 S2): the lengths of `r` and
the 25 scalars, the multiaffinity of the tape's ring weight; for `KS`: the lengths of the points,
the Keccak column claims (on `q_keccak`, at most one, on the block's coordinates), the ring
weight's multiaffinity. -/
def KgRet (k : KgOut) : Prop :=
  (k.1.1.length = 20 ∧ k.1.2.1.length = 25 ∧ ∀ n, IsMultiaffine n k.1.2.2.2.d.ring.2) ∧
  (k.2.1.1.length = 15 ∧ k.2.1.2.1.length = 25 ∧
    (∀ c ∈ k.2.1.2.2.1.1, c.column = qkeccak ∧ c.point.length = 21) ∧ k.2.1.2.2.1.1.length ≤ 1 ∧
    (∀ n, IsMultiaffine n k.2.1.2.2.2.2) ∧
    k.2.2.1.length = 20 ∧ k.2.2.2.1.1.length = 15)

open Lvm.KG in
open Lvm.NS (colM dD ksCol ksY2 msgM msgX) in
/-- **The claims V_S phases 4–7 leave** (`kgSpecS`'s post at P20: the tape's ring claim on `C_main`
(`h = 18`) and the tied digest lanes `D̃_l(r) = a_l`; `KS`'s claims at `Pk = 11`, `r = 14`) on a
pair, with WP-14c's accessors (`GoodK`'s). -/
def KcS (k : KgOut) (p : Column CMain.nu20 × Column 19) : Prop :=
  (RingColTrue 18 (colM p.1) k.1.2.2.2.d.ring ∧ TiedD 20 (dD p.1) k.1.1 k.1.2.1) ∧
  (CallerClaims 15 25 (ksCol p.1) (ksY 15 ksY2 (colM p.1) (ksCol p.1)) k.2.1 ∧
    KsLinkClaims 15 14 (ksCol p.1) (ksYRow 15 ksY2 (colM p.1) (ksCol p.1)) (msgM p.2) (msgX p.1)
      k.2.2)

end Lvm.ASM
