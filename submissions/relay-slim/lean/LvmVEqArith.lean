-- New for lvm (WP-14a, H0): the native verifier arithmetic of LvmDecideBase (over `FE`) is LvmVCore's
-- (over `E`) through `FE.toExt3`. Reuses WP-9b's scalar and list transport lemmas (LvmM3FidNative:
-- `tE_*`, `getD_map_tE`, `map_eqKernel`, `tE_eOfNat`, `map_selectorPoint`, `tE_eqEval`, `formE`,
-- `value_formE`).
import LvmM3FidNative

/-!
# The native verifier arithmetic over `E`

One transport lemma per arithmetic function of `LvmDecideBase` into its `LvmVCore` twin:
`FE.toExt3 (Lvm.f args) = V.f (mapped args)` for a scalar value and
`(Lvm.f args).map FE.toExt3 = V.f (mapped args)` for a list, lists mapped by `List.map FE.toExt3`,
natural-number arguments unchanged. Placements map by `plE`, forms by WP-9b's `M3.formE`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol
open Lvm.M3 (tE_add tE_mul tE_zero tE_one tE_foldl_add tE_foldl_mul formE)

/-! ## Lists -/

/-- `zipWith` commutes with a map that carries `g` to `g'`. -/
theorem map_zipWith_of {α β : Type} {f : α → β} {g : α → α → α} {g' : β → β → β}
    (h : ∀ x y, f (g x y) = g' (f x) (f y)) (a b : List α) :
    (List.zipWith g a b).map f = List.zipWith g' (a.map f) (b.map f) := by
  induction a generalizing b with
  | nil => rfl
  | cons x a ih => cases b with
    | nil => rfl
    | cons y b => simp only [List.zipWith_cons_cons, List.map_cons, h, ih]

theorem getD_map_toExt3 (l : List FE) (n : ℕ) : (l.map FE.toExt3).getD n 0 = FE.toExt3 (l.getD n 0) :=
  Lvm.M3.getD_map_tE l n

theorem map_toExt3_take (l : List FE) (n : ℕ) : (l.take n).map FE.toExt3 = (l.map FE.toExt3).take n :=
  List.map_take

theorem map_toExt3_drop (l : List FE) (n : ℕ) : (l.drop n).map FE.toExt3 = (l.map FE.toExt3).drop n :=
  List.map_drop

theorem zipIdx_map_toExt3 (l : List FE) :
    (l.map FE.toExt3).zipIdx = l.zipIdx.map (Prod.map FE.toExt3 id) :=
  List.zipIdx_map

theorem toExt3_headD (l : List FE) : FE.toExt3 (l.headD 0) = (l.map FE.toExt3).headD 0 := by
  cases l <;> simp

/-! ## Scalars -/

theorem toExt3_eOfNat (n : ℕ) : FE.toExt3 (Lvm.eOfNat n) = Verifier.eOfNat n := Lvm.M3.tE_eOfNat n

theorem toExt3_gen : FE.toExt3 Lvm.gen = Verifier.gen := toExt3_eOfNat 2

theorem kToNat_toBF64 (a : FK) : Verifier.kToNat (FK.toBF64 a) = Lvm.kToNat a := rfl

theorem bitLength_eq (n : ℕ) : Lvm.bitLength n = Verifier.bitLength n := rfl

theorem log2Ceil_eq (n : ℕ) : Lvm.log2Ceil n = Verifier.log2Ceil n := rfl

theorem toExt3_gpow (i : ℕ) : FE.toExt3 (Lvm.gpow i) = Verifier.gpow i := by
  rw [Lvm.gpow, FE.toExt3_npow, toExt3_gen]; rfl

theorem toExt3_frob (k : ℕ) (a : FE) : FE.toExt3 (FE.frob k a) = FE.toExt3 a ^ (2 ^ k) := by
  rw [FE.frob_eq_pow, FE.toExt3_npow]

theorem toExt3_sq_eq_pow (a : FE) : FE.toExt3 (FE.sq a) = FE.toExt3 a ^ 2 := by
  rw [FE.toExt3_sq, pow_two]

theorem toExt3_sumE (l : List FE) : FE.toExt3 (Lvm.sumE l) = Verifier.sumE (l.map FE.toExt3) :=
  Lvm.M3.tE_sumE l

theorem toExt3_prodE (l : List FE) : FE.toExt3 (Lvm.prodE l) = Verifier.prodE (l.map FE.toExt3) := by
  rw [Lvm.prodE, tE_foldl_mul, tE_one]; rfl

theorem map_powersFrom (acc base : FE) (n : ℕ) :
    (Lvm.powersFrom acc base n).map FE.toExt3 =
      Verifier.powersFrom (FE.toExt3 acc) (FE.toExt3 base) n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp only [Lvm.powersFrom, Verifier.powersFrom, List.map_cons, ih, tE_mul]

theorem map_powers (base : FE) (n : ℕ) :
    (Lvm.powers base n).map FE.toExt3 = Verifier.powers (FE.toExt3 base) n := by
  rw [Lvm.powers, map_powersFrom, tE_one]; rfl

/-! ## Equality kernels and multilinear evaluation -/

theorem map_eqKernel (p : List FE) :
    (Lvm.eqKernel p).map FE.toExt3 = Verifier.eqKernel (p.map FE.toExt3) :=
  Lvm.M3.map_eqKernel p

/-- The array kernel is the list kernel. -/
theorem eqKernelA_toList (p : List FE) : (Lvm.eqKernelA p).toList = Lvm.eqKernel p := by
  unfold Lvm.eqKernelA Lvm.eqKernel
  suffices h : ∀ out : Array FE,
      (p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) out).toList =
        p.foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) out.toList from h #[1]
  induction p with
  | nil => intro out; rfl
  | cons r p ih =>
    intro out
    simp only [List.foldl_cons, ih, Array.toList_append, Array.toList_map]

theorem getD_eqKernelA (p : List FE) (i : ℕ) : (Lvm.eqKernelA p).getD i 0 = (Lvm.eqKernel p).getD i 0 := by
  rw [← eqKernelA_toList, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem map_foldPairs (r : FE) : ∀ l : List FE,
    (Lvm.foldPairs r l).map FE.toExt3 = Verifier.foldPairs (FE.toExt3 r) (l.map FE.toExt3)
  | a :: b :: rest => by
    simp only [Lvm.foldPairs, Verifier.foldPairs, List.map_cons, map_foldPairs r rest, tE_add, tE_mul,
      tE_one]
  | [_] => rfl
  | [] => rfl

theorem toExt3_multilinearEval (mle point : List FE) :
    FE.toExt3 (Lvm.multilinearEval mle point) =
      Verifier.multilinearEval (mle.map FE.toExt3) (point.map FE.toExt3) := by
  unfold Lvm.multilinearEval Verifier.multilinearEval
  rw [toExt3_headD]
  congr 1
  induction point generalizing mle with
  | nil => rfl
  | cons r point ih => simp only [List.foldl_cons, List.map_cons, ih, map_foldPairs]

theorem toExt3_eqEval (a b : List FE) :
    FE.toExt3 (Lvm.eqEval a b) = Verifier.eqEval (a.map FE.toExt3) (b.map FE.toExt3) :=
  Lvm.M3.tE_eqEval a b

theorem toExt3_dot (a b : List FE) :
    FE.toExt3 (Lvm.dot a b) = Verifier.dot (a.map FE.toExt3) (b.map FE.toExt3) := by
  unfold Lvm.dot Verifier.dot
  rw [tE_foldl_add, tE_zero, map_zipWith_of tE_mul]

theorem toExt3_paddingWeight (point : List FE) (n : ℕ) :
    FE.toExt3 (Lvm.paddingWeight point n) = Verifier.paddingWeight (point.map FE.toExt3) n := by
  unfold Lvm.paddingWeight Verifier.paddingWeight
  rw [tE_mul, tE_add, tE_one, toExt3_eOfNat, List.length_map, zipIdx_map_toExt3]
  congr 1
  generalize point.zipIdx = l
  suffices h : ∀ acc : FE, FE.toExt3 (l.foldl (fun pad (r, k) =>
      let b := Lvm.eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) acc) = (l.map (Prod.map FE.toExt3 id)).foldl (fun pad (r, k) =>
      let b := Verifier.eOfNat ((n >>> k) % 2)
      (1 + b) * r + (1 + b + r) * pad) (FE.toExt3 acc) by rw [h, tE_one]
  induction l with
  | nil => intro acc; rfl
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, ih, Prod.map_fst, Prod.map_snd, id_eq, tE_add, tE_mul, tE_one,
      toExt3_eOfNat]

theorem toExt3_indexMleFrom (gp : FE) (l : List FE) (acc : FE) :
    FE.toExt3 (Lvm.indexMleFrom gp l acc) =
      Verifier.indexMleFrom (FE.toExt3 gp) (l.map FE.toExt3) (FE.toExt3 acc) := by
  induction l generalizing gp acc with
  | nil => rfl
  | cons r l ih =>
    simp only [Lvm.indexMleFrom, Verifier.indexMleFrom, List.map_cons, ih, FE.toExt3_npow, tE_mul, tE_add,
      tE_one]

theorem toExt3_indexMle (point : List FE) :
    FE.toExt3 (Lvm.indexMle point) = Verifier.indexMle (point.map FE.toExt3) := by
  rw [Lvm.indexMle, toExt3_indexMleFrom, toExt3_gen, tE_one]; rfl

theorem toExt3_polyEval (cs : List FE) (x : FE) :
    FE.toExt3 (Lvm.polyEval cs x) = Verifier.polyEval (cs.map FE.toExt3) (FE.toExt3 x) := by
  unfold Lvm.polyEval Verifier.polyEval
  induction cs with
  | nil => exact tE_zero
  | cons c cs ih => simp only [List.foldr_cons, List.map_cons, tE_add, tE_mul, ih]

theorem map_selectorPoint (s len : ℕ) :
    (Lvm.selectorPoint s len).map FE.toExt3 = Verifier.selectorPoint s len :=
  Lvm.M3.map_selectorPoint s len

/-! ## Placements -/

/-- A native placement as the verifier's. -/
def plE : Lvm.Placement → Verifier.Placement := fun p ↦ ⟨p.variableCount, p.index⟩

theorem map_stackPoint (p : Lvm.Placement) (point : List FE) (stackLog : ℕ) :
    (p.stackPoint point stackLog).map FE.toExt3 = (plE p).stackPoint (point.map FE.toExt3) stackLog := by
  simp only [Lvm.Placement.stackPoint, Verifier.Placement.stackPoint, plE, List.map_append, map_selectorPoint]

theorem toExt3_eqAbove (p : Lvm.Placement) (point : List FE) :
    FE.toExt3 (p.eqAbove point) = (plE p).eqAbove (point.map FE.toExt3) := by
  unfold Lvm.Placement.eqAbove Verifier.Placement.eqAbove
  rw [toExt3_eqEval, map_selectorPoint, List.map_drop, List.length_map]; rfl

/-! ## Forms (`M3.formE` maps a form's coefficients) -/

/-- A native term list over `E`. -/
def termsE (ts : List (List ℕ × FE)) : List (List ℕ × E) := ts.map fun t ↦ (t.1, FE.toExt3 t.2)

theorem formE_terms (f : Lvm.Form) : (formE f).terms = termsE f.terms := rfl

theorem termsE_addTerm (ts : List (List ℕ × FE)) (m : List ℕ) (c : FE) :
    termsE (Lvm.addTerm ts m c) = Verifier.addTerm (termsE ts) m (FE.toExt3 c) := by
  induction ts with
  | nil => simp [termsE, Lvm.addTerm, Verifier.addTerm]
  | cons t ts ih =>
    obtain ⟨m', c'⟩ := t
    by_cases h : m' = m
    · simp [termsE, Lvm.addTerm, Verifier.addTerm, h]
    · simp only [termsE] at ih
      simp [termsE, Lvm.addTerm, Verifier.addTerm, h, ih]

theorem formE_addScaled (f other : Lvm.Form) (w : FE) :
    formE (f.addScaled other w) = (formE f).addScaled (formE other) (FE.toExt3 w) := by
  suffices h : ∀ ts acc : List (List ℕ × FE),
      termsE (ts.foldl (fun acc t ↦ Lvm.addTerm acc t.1 (w * t.2)) acc) =
        (termsE ts).foldl (fun acc t ↦ Verifier.addTerm acc t.1 (FE.toExt3 w * t.2)) (termsE acc) from
    congrArg Verifier.Form.mk (h other.terms f.terms)
  intro ts
  induction ts with
  | nil => intro acc; rfl
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons, ih, termsE_addTerm, tE_mul]
    rfl

theorem toExt3_value (f : Lvm.Form) (col : ℕ → FE) :
    FE.toExt3 (f.value col) = (formE f).evaluate fun i ↦ FE.toExt3 (col i) :=
  Lvm.M3.value_formE f col

theorem formE_const (v : FE) : formE (Lvm.Form.const v) = Verifier.Form.const (FE.toExt3 v) := rfl

theorem formE_col (i e : ℕ) : formE (Lvm.Form.col i e) = Verifier.Form.col i e := by
  simp [formE, Lvm.Form.col, Verifier.Form.col, toExt3_gpow]

end Lvm.VEq
