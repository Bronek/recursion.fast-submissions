-- new for lvm (WP-9). Built on WP-2's port of leanVM `Protocol/Spine/Instance` (`M3Instance`,
-- `M3Holds`) and its stacking lemmas (`LvmCpMultilinear`: `slice`, `evalMle_append_boolVec`,
-- the proof pattern of leanVM `Protocol/Stack.lean`'s `readWith_slice`).
import LvmSpineInstance
import LvmM3Tab
import LvmBusILookup
import LvmFieldCorrect

/-!
# The lvm M3 instance: tables of committed and fixed columns, memory flushes, two commitments

BLUEPRINT §4 (as WP-10 refined it) on WP-2's `M3Instance`:

* **Tables** (`Tab`): a log-height `τ`, columns (`ColSrc`), degree-2 constraints, and the
  table's *reads* and *seeds* of the two lookup memories. Every lvm table is one of these:
  a LoopIR piece (`LvmM3Loop`), an input array (stream lanes, digests, bit fields), `BITS`, or a
  column group with no constraint and no flush (`CH`, `KS`, which the Keccak GKRs own).
* **Columns.** A column is *committed* (an aligned block of `2^τ` words at offset `off` of `C_main`
  or `C_rec`) or *fixed* (verifier-known: cell `x` is `f x`; `ev` is its multilinear extension
  in closed form, for the native verifier). A fixed column is a *derived* column of the
  `M3Instance` (`derived`, constant in the stack): its claims are never opened, the verifier
  evaluates them (leanVM's derived columns, there the Keccak output lanes).
* **Two commitments, one stack.** The instance's stack has `nuMain + 1` variables: `C_main` is
  its low half, `C_rec` sits at `2^nuMain` (zero above `2^nuRec`). A committed column is the
  slice of the stack at its aligned offset (`liftAt`): a claim on it is a claim on one of the
  two commitments, at the same point.
* **Polynomials** (`CPoly`): computable monomial lists over column indices (coefficients in
  `Lvm.FK`), mapped to Mathlib's `MvPolynomial (Fin w) K` (`toMv`) for the instance and
  evaluated natively over `FE` by the verifier. An index past the width reads `0`.
* **Messages** (`Key.vec`): sixteen coordinates `⟨sep, addr, cnt, value limbs, 0, …⟩`. A read with
  count column `c` pulls `⟨k, c⟩` and pushes `⟨k, g·c⟩`; a seed with finalize column `f` pushes
  `⟨k, 1⟩` and pulls `⟨k, f⟩` (leanVM §6.2; WP-10's seeds and finalizes of result cells). The
  read count columns are the instance's count columns. No boundary block, no padding row
  (`rows = 2^τ`), no public line, no Keccak region: the Keccak GKRs and links are their own
  phases (WP-8).
-/

namespace Lvm.M3

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

/-! ## Polynomials over column indices -/

namespace CPoly

/-- A column variable of `MvPolynomial (Fin w) K`, `0` past the width. -/
noncomputable def xv (w i : ℕ) : MvPolynomial (Fin w) K :=
  if h : i < w then MvPolynomial.X ⟨i, h⟩ else 0

/-- The polynomial as a Mathlib polynomial in `w` variables. -/
noncomputable def toMv (w : ℕ) (P : CPoly) : MvPolynomial (Fin w) K :=
  (P.map fun m ↦ MvPolynomial.C (FK.toBF64 m.1) * (m.2.map (xv w)).prod).sum

/-- The value at a row of `K` values. -/
def evalB (v : ℕ → K) (P : CPoly) : K := (P.map fun m ↦ FK.toBF64 m.1 * (m.2.map v).prod).sum

/-- The row a `Fin w`-indexed row gives the indices, `0` past the width. -/
def ext {w : ℕ} (r : Fin w → K) (i : ℕ) : K := if h : i < w then r ⟨i, h⟩ else 0

theorem eval_xv {w : ℕ} (r : Fin w → K) (i : ℕ) : MvPolynomial.eval r (xv w i) = ext r i := by
  unfold xv ext; split <;> simp

theorem eval_toMv {w : ℕ} (r : Fin w → K) (P : CPoly) :
    MvPolynomial.eval r (toMv w P) = evalB (ext r) P := by
  unfold toMv evalB
  induction P with
  | nil => simp
  | cons m P ih =>
    rw [List.map_cons, List.sum_cons, map_add, ih, List.map_cons, List.sum_cons, map_mul,
      MvPolynomial.eval_C, map_list_prod, List.map_map]
    congr 2
    exact congrArg List.prod (List.map_congr_left fun i _ ↦ eval_xv r i)

theorem totalDegree_toMv {w : ℕ} {P : CPoly} {d : ℕ} (h : ∀ m ∈ P, m.2.length ≤ d) :
    (toMv w P).totalDegree ≤ d := by
  unfold toMv
  induction P with
  | nil => simp
  | cons m P ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ (ih fun m' hm' ↦ h m'
      (List.mem_cons_of_mem _ hm')))
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_list_prod _).trans ?_
    have hle : ∀ x ∈ m.2.map (xv w), x.totalDegree ≤ 1 := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      unfold xv; split
      · exact (MvPolynomial.totalDegree_X _).le
      · simp
    calc ((m.2.map (xv w)).map MvPolynomial.totalDegree).sum
        ≤ ((m.2.map (xv w)).map fun _ ↦ 1).sum := List.sum_le_sum fun x hx ↦ hle x hx
      _ = m.2.length := by
          rw [List.map_map, show ((fun _ ↦ 1) ∘ xv w) = fun _ ↦ (1 : ℕ) from rfl]; simp
      _ ≤ d := h m (List.mem_cons_self ..)

end CPoly

/-! ## Messages -/

/-- The sixteen coordinates of the message with key `k` and count `cnt`: separator, address,
count, value limbs, then zeros. -/
noncomputable def Key.vec (w : ℕ) (k : Key) (cnt : CPoly) : Vector (MvPolynomial (Fin w) K) 16 :=
  Vector.ofFn fun i ↦
    if i.val = 0 then MvPolynomial.C (FK.toBF64 k.sep)
    else if i.val = 1 then k.addr.toMv w
    else if i.val = 2 then cnt.toMv w
    else (k.val.getD (i.val - 3) []).toMv w

/-! ## Tables -/

namespace Tab

variable (t : Tab)

/-- The read's pull: count = the count column. -/
noncomputable def readVec (r : Key × ℕ) : Vector (MvPolynomial (Fin t.w) K) 16 :=
  r.1.vec t.w (CPoly.var r.2)

/-- The read's push: count = `g` times the count column. -/
noncomputable def bumpVec (r : Key × ℕ) : Vector (MvPolynomial (Fin t.w) K) 16 :=
  r.1.vec t.w [(FK.x, [r.2])]

/-- The seed's push: count `1`. -/
noncomputable def seedVec (s : Key × ℕ) : Vector (MvPolynomial (Fin t.w) K) 16 :=
  s.1.vec t.w (CPoly.const 1)

/-- The seed's finalize pull: count = the finalize column. -/
noncomputable def finVec (s : Key × ℕ) : Vector (MvPolynomial (Fin t.w) K) 16 :=
  s.1.vec t.w (CPoly.var s.2)

/-- The flushes, in order: the reads' pulls, their pushes, the seeds, the finalizes. -/
noncomputable def flushes : List (Side × Vector (MvPolynomial (Fin t.w) K) 16) :=
  t.reads.map (fun r ↦ (Side.pull, t.readVec r)) ++ t.reads.map (fun r ↦ (Side.push, t.bumpVec r)) ++
    t.seeds.map (fun s ↦ (Side.push, t.seedVec s)) ++ t.seeds.map (fun s ↦ (Side.pull, t.finVec s))

end Tab

/-! ## The stack: `C_main` and `C_rec` -/

/-- The commitment sizes: `C_main` has `2^nuMain` words, `C_rec` `2^nuRec ≤ 2^nuMain`. -/
structure Lay where
  /-- `log₂` of `C_main`'s words. -/
  nuMain : ℕ
  /-- `log₂` of `C_rec`'s words. -/
  nuRec : ℕ

/-- The stack's variables: `C_main`, then the bit that selects `C_rec`. -/
abbrev Lay.μ (L : Lay) : ℕ := L.nuMain + 1

/-- A column's cell offset on the stack (`0` for a fixed column, whose reading is unused). -/
def stackOff (L : Lay) (t : Tab) (i : ℕ) : ℕ :=
  match t.cols[i]? with
  | some (.com rec off) => off + if rec then 2 ^ L.nuMain else 0
  | _ => 0

/-- Whether a column's block is aligned inside its commitment. -/
def Aligned (L : Lay) (t : Tab) (i : ℕ) : Prop :=
  match t.cols[i]? with
  | some (.com rec off) => 2 ^ t.τ ∣ off ∧ off + 2 ^ t.τ ≤ 2 ^ (if rec then L.nuRec else L.nuMain) ∧
      L.nuRec ≤ L.nuMain
  | _ => True

/-- **The layout facts** (decidable): every committed column is an aligned block inside its
commitment, and `C_rec` is no larger than `C_main`. Under them a column's lift (`liftAt`) is its
block, and a claim on the column is the claim on its commitment at the same point (the native
verifier's `BlockClaim.point ⟨τ, off⟩`); without them `selOf` reads slice `0`. -/
def LayOk (L : Lay) (tabs : List Tab) : Prop := ∀ t ∈ tabs, ∀ i < t.w, Aligned L t i

/-- The high index of a column's slice (`0` if its offset is not aligned on the stack). -/
def selOf (L : Lay) (t : Tab) (hτ : t.τ ≤ L.μ) (i : ℕ) : Fin (2 ^ (L.μ - t.τ)) :=
  if h : 2 ^ t.τ ∣ stackOff L t i ∧ stackOff L t i + 2 ^ t.τ ≤ 2 ^ L.μ then
    ⟨stackOff L t i / 2 ^ t.τ, by
      obtain ⟨⟨k, hk⟩, hle⟩ := h
      have hp : 0 < 2 ^ t.τ := Nat.two_pow_pos _
      rw [hk, Nat.mul_div_cancel_left _ hp]
      have h2 : 2 ^ L.μ = 2 ^ t.τ * 2 ^ (L.μ - t.τ) := by rw [← pow_add, Nat.add_sub_cancel' hτ]
      rw [hk, h2] at hle
      have : 2 ^ t.τ * (k + 1) ≤ 2 ^ t.τ * 2 ^ (L.μ - t.τ) := by rw [mul_add, mul_one]; exact hle
      have := Nat.le_of_mul_le_mul_left this hp
      omega⟩
  else 0

/-- The point of the stack a point of a column of height `2^τ` at high index `sel` lifts to. -/
def liftAt {μ τ : ℕ} (h : τ ≤ μ) (sel : Fin (2 ^ (μ - τ))) (z : Vector E τ) : Vector E μ :=
  Vector.cast (Nat.add_sub_cancel' h) (z ++ (boolVec sel : Vector E (μ - τ)))

/-- Reading through the lift is the slice at `sel`. -/
theorem readWith_liftAt {μ : ℕ} {ι : Type} {κ : ι → ℕ} (h : ∀ c, κ c ≤ μ)
    (sel : (c : ι) → Fin (2 ^ (μ - κ c))) (q : Column μ) (c : ι) :
    (Layout.readWith (fun c ↦ liftAt (h c) (sel c)) q c).values =
      slice (Vector.cast (congrArg (2 ^ ·) (Nat.add_sub_cancel' (h c)).symm) q.values) (sel c) := by
  apply Vector.ext
  intro x hx
  simp only [Layout.readWith, liftAt, Vector.getElem_ofFn, boolVec_append, boolVec_cast,
    slice, Vector.getElem_cast]
  rw [boolIndex_boolVec]
  rfl

/-- **The reading law of the lift**: a slice's extension at `z` is the stack's at the lifted
point. -/
theorem read_eval_liftAt {μ : ℕ} {ι : Type} {κ : ι → ℕ} (h : ∀ c, κ c ≤ μ)
    (sel : (c : ι) → Fin (2 ^ (μ - κ c))) (q : Column μ) (c : ι) (z : Vector E (κ c)) :
    eval₂Mle (Layout.readWith (fun c ↦ liftAt (h c) (sel c)) q c).values (algebraMap K E) z =
      eval₂Mle q.values (algebraMap K E) (liftAt (h c) (sel c) z) := by
  rw [readWith_liftAt h sel q c, liftAt]
  have e := Nat.add_sub_cancel' (h c)
  rw [← eval₂Mle_cast (algebraMap K E) e.symm q.values, Vector.cast_cast, Vector.cast_rfl]
  rw [eval₂Mle, eval₂Mle, slice_map, evalMle_append_boolVec]

/-- The layout of a list of tables on the stack. -/
def layout (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) :
    Layout L.μ (Σ j : Fin tabs.length, Fin (tabs.get j).w) (fun c ↦ (tabs.get c.1).τ) where
  extend c := liftAt (hτ _ (List.get_mem _ _)) (selOf L (tabs.get c.1) (hτ _ (List.get_mem _ _)) c.2)
  -- elaborated without the expected type, then closed syntactically (with it, unifying the
  -- `sel` metavariable unfolds `eval₂Mle` to `Array.mapM` and fails for seconds)
  read_eval q c z := by
    have h := read_eval_liftAt (ι := Σ j : Fin tabs.length, Fin (tabs.get j).w)
      (κ := fun c ↦ (tabs.get c.1).τ) (fun c ↦ hτ _ (List.get_mem _ c.1))
      (fun c ↦ selOf L (tabs.get c.1) (hτ _ (List.get_mem _ _)) c.2) q c z
    exact h

/-! ## The instance -/

/-- The fixed column `f` as a column of height `2^τ`. -/
def fixedColumn (τ : ℕ) (f : ℕ → FK) : Column τ := ⟨Vector.ofFn fun x ↦ FK.toBF64 (f x)⟩

/-- **The lvm M3 instance** of a list of tables on the two commitments. -/
@[reducible] noncomputable def inst (L : Lay) (tabs : List Tab) (hτ : ∀ t ∈ tabs, t.τ ≤ L.μ) : M3Instance where
  ntab := tabs.length
  τ j := (tabs.get j).τ
  width j := (tabs.get j).w
  Stmt := Unit
  constraints j := (tabs.get j).cons.map (CPoly.toMv _)
  flushes j := (tabs.get j).flushes
  d := 2
  constraints_degree j C hC := by
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hC
    exact CPoly.totalDegree_toMv ((tabs.get j).deg.1 P hP)
  flushes_degree j f hf k := by
    have hkey : ∀ (key : Key), key.Deg2 → ∀ (cnt : CPoly), cnt.Deg2 →
        ((key.vec (tabs.get j).w cnt).get k).totalDegree ≤ 2 := by
      intro key hk cnt hc
      simp only [Key.vec, Vector.get_ofFn]
      split
      · simp
      split
      · exact CPoly.totalDegree_toMv hk.1
      split
      · exact CPoly.totalDegree_toMv hc
      · rcases Nat.lt_or_ge (k.val - 3) key.val.length with hl | hl
        · rw [List.getD_eq_getElem _ _ hl]
          exact CPoly.totalDegree_toMv (hk.2 _ (List.getElem_mem hl))
        · rw [List.getD_eq_default _ _ hl]; simp [CPoly.toMv]
    have hvar : ∀ i, CPoly.Deg2 (CPoly.var i) := fun i m hm ↦ by
      simp [CPoly.var] at hm; subst hm; simp
    have hgx : ∀ i, CPoly.Deg2 [(FK.x, [i])] := fun i m hm ↦ by
      simp at hm; subst hm; simp
    have hc1 : CPoly.Deg2 (CPoly.const 1) := fun m hm ↦ by
      simp [CPoly.const] at hm; subst hm; simp
    simp only [Tab.flushes, List.mem_append, List.mem_map] at hf
    rcases hf with (((⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨s, hs, rfl⟩) | ⟨s, hs, rfl⟩)
    · exact hkey _ ((tabs.get j).deg.2.1 r hr) _ (hvar _)
    · exact hkey _ ((tabs.get j).deg.2.1 r hr) _ (hgx _)
    · exact hkey _ ((tabs.get j).deg.2.2 s hs) _ hc1
    · exact hkey _ ((tabs.get j).deg.2.2 s hs) _ (hvar _)
  counts j := (tabs.get j).counts
  rows j := 2 ^ (tabs.get j).τ
  rows_le _ := le_rfl
  padRow _ _ := 0
  boundary := []
  μ := L.μ
  layout := layout L tabs hτ
  derived c := ((tabs.get c.1).fixedOf c.2).map fun f _ ↦ fixedColumn _ f
  nLines := 0
  publicLines _ := #v[]
  keccak := none

end Lvm.M3
