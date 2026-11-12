-- New for lvm2 (V-LEV2): further fast twins of `V_S` at `P20`, after `LvmVFast` (kept separate from it).
import LvmVFast
import LvmSelfEval

/-!
# V-LEV2: the shipped `V_S` with further fast twins

Each lever is a fast twin with its equality lemma; the chain ends in **`VS20G_eq : VS20G = VS20F`**, and
`Solution` ships `VS20G`.

* **L5, the openings' table claims by run.** `eq(z, x.take τ)` once per table (`SClaim`, `decideProgS_eq`).
* **C, the leaves' MLE by 64-row blocks** (`mleKB_eq`): an `eq` table over the low coordinates, one `E × K`
  dot per block.
* **B, non-uniform leaves.** A group column whose template rows have several stride lists went through
  `boxMulM` per row (a closure, a stride-list lookup and a box product, ≈ 1 µs a row). `nuOf` stores, once per
  (piece, column), the distinct stride lists and each row's class (`classes_spec`); per check, one `boxEval` per
  class, the rows' values `coef_i · B[class i]` in an array, and `mleE` (`nuMle_eq`, `pieceEvalGN_eq`,
  `grpEvalGN_eq`).
-/

set_option autoImplicit false

namespace Lvm.VF

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.QLink Lvm.QSig Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.SigBits Lvm.QAsm

/-! ## C: the leaves' MLE by 64-row blocks

`mleK` halves the whole array (`n/2` `E × K` then `≈ n/2` `E × E` products and an array per layer). Here an
`eq` table over the first `k ≤ 6` coordinates is built once, each block of `2^k` rows is one `E × K` dot with
it, and only the `2^(|r|-k)` block values are halved (`mleKB_eq`, from `mleF_split` and `mle_eq_sum`). -/

theorem mleF_split : ∀ (rl rh : List FE) (f : Nat → FE),
    mleF (rl ++ rh) f = mleF rh (fun j => mleF rl (fun i => f (j * 2 ^ rl.length + i)))
  | [], rh, f => by simp [mleF]
  | r :: rs, rh, f => by
    have h1 : mleF (r :: rs ++ rh) f = mleF (rs ++ rh) (fun x => f (2 * x) + r * (f (2 * x + 1) - f (2 * x))) := by
      rw [mleF_lin]; rfl
    rw [h1, mleF_split rs rh]
    congr 1
    funext j
    have h2 : mleF (r :: rs) (fun i => f (j * 2 ^ (r :: rs).length + i)) =
        mleF rs (fun x => f (j * 2 ^ (r :: rs).length + 2 * x) + r *
          (f (j * 2 ^ (r :: rs).length + (2 * x + 1)) - f (j * 2 ^ (r :: rs).length + 2 * x))) := by
      rw [mleF_lin]; rfl
    rw [h2]
    congr 1
    funext i
    have e1 : 2 * (j * 2 ^ rs.length + i) = j * 2 ^ (r :: rs).length + 2 * i := by
      simp only [List.length_cons, Nat.pow_succ]; ring
    have e2 : 2 * (j * 2 ^ rs.length + i) + 1 = j * 2 ^ (r :: rs).length + (2 * i + 1) := by
      simp only [List.length_cons, Nat.pow_succ]; ring
    rw [e2, e1]

theorem list_sum_range (f : Nat → FE) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]
    simp

theorem mleF_sum (r : List FE) (f : Nat → FE) :
    mleF r f = ∑ x ∈ Finset.range (2 ^ r.length), eqW r x * f x := by
  rw [mleF_eq, mle_eq_sum]

/-- **The MLE of `K` leaves by 64-row blocks** (at least 8 blocks; else `mleK`). -/
def mleKB (r : List FE) (A : Array FK) : FE :=
  if r.length < 9 then mleK r A else
  let E := (eqKernel (r.take 6)).toArray
  let idx := List.range (2 ^ 6)
  let blocks := Array.ofFn (n := 2 ^ (r.length - 6)) fun j =>
    idx.foldl (fun acc i => acc + FE.smulBase (A.getD (j.val * 2 ^ 6 + i) 0) (E.getD i 0)) 0
  mleE (r.drop 6) blocks

theorem foldl_add_map (g : Nat → FE) (l : List Nat) : l.foldl (fun acc i => acc + g i) 0 = (l.map g).sum := by
  rw [← List.foldl_map (f := g) (g := (· + ·)), foldl_add_sum, zero_add]

theorem mleKB_eq (r : List FE) (A : Array FK) : mleKB r A = mleF r (fun i => FE.ofK (A.getD i 0)) := by
  unfold mleKB
  split
  · exact mleK_eq r A
  · rename_i hr
    have hk : (r.take 6).length = 6 := by simp; omega
    dsimp only
    conv_rhs => rw [← List.take_append_drop 6 r, mleF_split, hk]
    rw [mleE_eq]
    refine mleF_congr _ _ _ fun j hj => ?_
    have hj' : j < 2 ^ (r.length - 6) := by simpa using hj
    rw [getD_ofFn _ _ _ _ hj', foldl_add_map, mleF_sum, hk, list_sum_range]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < 2 ^ (r.take 6).length := by rw [hk]; exact Finset.mem_range.mp hi
    rw [FE.smulBase_eq_mul, toArray_getD (eqKernel (r.take 6)), Q1.eqKernel_getD _ hi', mul_comm]

/-- `leafMle` with `mleKB`. -/
def leafMleB (L : Leaves) (r : List FE) : FE :=
  match L.k with
  | some A => mleKB r A
  | none => mleE r L.e

theorem leafMleB_eq (L : Leaves) (hk : L.k = kLeaves L.e) (r : List FE) : leafMleB L r = leafMle L r := by
  rw [leafMle_eq L hk]
  unfold leafMleB
  split
  · rename_i A hA
    rw [mleKB_eq]
    exact mleF_congr r _ _ fun i _ => kLeaves_spec L.e A (hk ▸ hA) i
  · exact mleE_eq r L.e

/-- `pieceEvalGL` with `leafMleB`. -/
def pieceEvalGLB (L : Option Leaves) (u : Option (List Nat)) (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  match L with
  | none => pieceEvalGU u G pe c r
  | some lv =>
    let bc := G.C.bc pe.p.blk
    let rI := r.drop bc.B.lsize
    if rI.length ≤ lv.a then
      match c, u with
      | .res, some s0 | .arg _, some s0 => boxMul (leafMleB lv rI) bc.B.dims s0 (r.take bc.B.lsize)
      | .k, _ | .k', _ => leafMleB lv rI
      | _, _ => pieceEvalGU u G pe c r
    else pieceEvalGU u G pe c r

theorem pieceEvalGLB_eq (L : Option Leaves) (u : Option (List Nat)) (G : PG) (pe : M3.PE) (c : FCol) (r : List FE)
    (hL : ∀ lv, L = some lv → lv = leavesOf G pe c) : pieceEvalGLB L u G pe c r = pieceEvalGL L u G pe c r := by
  cases L with
  | none => rfl
  | some lv =>
    obtain rfl := hL lv rfl
    have hb : ∀ r', leafMleB (leavesOf G pe c) r' = leafMle (leavesOf G pe c) r' := leafMleB_eq _ rfl
    simp only [pieceEvalGLB, pieceEvalGL, hb]
    split <;> cases c <;> cases u <;> rfl

/-! ## B: leaves for the non-uniform stride columns -/

theorem classes_spec (L : List (List Nat)) (i : Nat) (hi : i < L.length) :
    (L.map L.eraseDups.idxOf).toArray.getD i 0 < L.eraseDups.length ∧
      L.eraseDups.toArray.getD ((L.map L.eraseDups.idxOf).toArray.getD i 0) [] = L[i] := by
  rw [getD_map_toArray _ _ _ _ hi]
  have hm : L[i] ∈ L.eraseDups := List.mem_eraseDups.mpr (List.getElem_mem hi)
  have hlt := List.idxOf_lt_length_of_mem hm
  refine ⟨hlt, ?_⟩
  rw [toArray_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    List.getElem_idxOf hlt]

/-- A non-uniform column's rows: stride classes, each row's class, the coefficients (and their `K` limbs). -/
structure NU where
  /-- The template rows' log-count. -/
  a : Nat
  /-- The distinct stride lists. -/
  cls : Array (List Nat)
  /-- Each row's class. -/
  ix : Array Nat
  /-- The coefficients. -/
  e : Array FE
  /-- Their `K` limbs, when every coefficient is in `K`. -/
  k : Option (Array FK)

/-- The classes of piece entry `pe`, column `c`. -/
def nuOf (G : PG) (pe : M3.PE) (c : FCol) : NU :=
  let bc := G.C.bc pe.p.blk
  let L := (List.range (2 ^ pe.p.a)).map fun i => stridesOf bc c (pe.ts.getD i 0)
  let e := (leavesOf G pe c).e
  ⟨pe.p.a, L.eraseDups.toArray, (L.map L.eraseDups.idxOf).toArray, e, kLeaves e⟩

theorem nuOf_a (G : PG) (pe : M3.PE) (c : FCol) : (nuOf G pe c).a = pe.p.a := rfl

/-- **The column's MLE from its classes**: one box product per class, then an array MLE. -/
def nuMle (nu : NU) (dims : List Nat) (rI rJ : List FE) : FE :=
  let B := nu.cls.map fun s => boxEval dims s rJ
  if nu.cls.size = 1 then
    -- one class: the coefficients' MLE times the one box value
    (match nu.k with
     | some A => mleKB rI A
     | none => mleE rI nu.e) * B.getD 0 0
  else
  match nu.k with
  | some A => mleE rI (Array.ofFn (n := 2 ^ nu.a) fun i =>
      FE.smulBase (A.getD i.val 0) (B.getD (nu.ix.getD i.val 0) 0))
  | none => mleE rI (Array.ofFn (n := 2 ^ nu.a) fun i => nu.e.getD i.val 0 * B.getD (nu.ix.getD i.val 0) 0)

theorem nuMle_eq (G : PG) (pe : M3.PE) (c : FCol) (rI rJ : List FE) (h : rI.length ≤ pe.p.a)
    (hd : (G.C.bc pe.p.blk).B.dims ≠ []) :
    nuMle (nuOf G pe c) (G.C.bc pe.p.blk).B.dims rI rJ =
      mleF rI fun i => boxMul (coefF (G.C.bc pe.p.blk) pe c i) (G.C.bc pe.p.blk).B.dims
        (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2 rJ := by
  -- the row value at `i < 2^a`
  have hrow : ∀ i < 2 ^ pe.p.a,
      ((nuOf G pe c).cls.map fun s => boxEval (G.C.bc pe.p.blk).B.dims s rJ).getD ((nuOf G pe c).ix.getD i 0) 0 =
        boxEval (G.C.bc pe.p.blk).B.dims (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2 rJ := by
    intro i hi
    have hL : i < ((List.range (2 ^ pe.p.a)).map fun i => stridesOf (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).length := by
      simpa using hi
    obtain ⟨hlt, hcls⟩ := classes_spec _ i hL
    simp only [nuOf]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem (by simpa using hlt),
      Option.map_some, Option.getD_some]
    have h2 := hcls
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hlt), Option.getD_some] at h2
    rw [h2]
    simp [stridesOf_eq]
  have hcoef' : ∀ i < 2 ^ pe.p.a, (leavesOf G pe c).e.getD i 0 = coefF (G.C.bc pe.p.blk) pe c i := by
    intro i hi
    simp only [leavesOf]
    rw [getD_ofFn _ _ _ _ hi]
  have hcoef : ∀ i < 2 ^ pe.p.a, (nuOf G pe c).e.getD i 0 = coefF (G.C.bc pe.p.blk) pe c i := hcoef'
  have hbox : ∀ (x : FE) (s : List Nat), boxMul x (G.C.bc pe.p.blk).B.dims s rJ =
      x * boxEval (G.C.bc pe.p.blk).B.dims s rJ := by
    intro x s
    cases hdm : (G.C.bc pe.p.blk).B.dims with
    | nil => exact absurd hdm hd
    | cons d ds => rfl
  unfold nuMle
  split
  · -- one class: every row's strides are the class's
    rename_i h1
    have hix : ∀ i < 2 ^ pe.p.a, (nuOf G pe c).ix.getD i 0 = 0 := by
      intro i hi
      have hL : i < ((List.range (2 ^ pe.p.a)).map fun i => stridesOf (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).length := by
        simpa using hi
      have hlt := (classes_spec _ i hL).1
      have : ((List.range (2 ^ pe.p.a)).map fun i => stridesOf (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).eraseDups.length = 1 := by
        simpa [nuOf] using h1
      simp only [nuOf]; omega
    have hB : ∀ i < 2 ^ pe.p.a,
        boxEval (G.C.bc pe.p.blk).B.dims (colAffineF (G.C.bc pe.p.blk) c (pe.ts.getD i 0)).2 rJ =
          ((nuOf G pe c).cls.map fun s => boxEval (G.C.bc pe.p.blk).B.dims s rJ).getD 0 0 := by
      intro i hi; rw [← hrow i hi, hix i hi]
    have hm : (match (nuOf G pe c).k with
        | some A => mleKB rI A
        | none => mleE rI (nuOf G pe c).e) = mleF rI (coefF (G.C.bc pe.p.blk) pe c) := by
      split
      · rename_i A hA
        rw [mleKB_eq]
        refine mleF_congr rI _ _ fun i hi => ?_
        have hi' : i < 2 ^ pe.p.a := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) h)
        rw [kLeaves_spec _ A hA i, hcoef' i hi']
      · rw [mleE_eq]
        refine mleF_congr rI _ _ fun i hi => ?_
        have hi' : i < 2 ^ pe.p.a := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) h)
        exact hcoef i hi'
    rw [hm, ← mleF_mul]
    refine mleF_congr rI _ _ fun i hi => ?_
    have hi' : i < 2 ^ pe.p.a := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) h)
    rw [hbox, hB i hi']
  · split
    · rename_i A hA
      rw [mleE_eq]
      refine mleF_congr rI _ _ fun i hi => ?_
      have hi' : i < 2 ^ pe.p.a := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) h)
      rw [getD_ofFn _ _ _ _ (by rw [nuOf_a]; exact hi'), FE.smulBase_eq_mul, kLeaves_spec _ A hA i,
        hcoef' i hi', hrow i hi', hbox]
    · rw [mleE_eq]
      refine mleF_congr rI _ _ fun i hi => ?_
      have hi' : i < 2 ^ pe.p.a := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) h)
      rw [getD_ofFn _ _ _ _ (by rw [nuOf_a]; exact hi'), hcoef i hi', hrow i hi', hbox]

/-- `pieceEvalGLB` with the classes `N` (= `nuOf G pe c` when present) of a non-uniform column. -/
def pieceEvalGN (N : Option NU) (L : Option Leaves) (u : Option (List Nat)) (G : PG) (pe : M3.PE) (c : FCol)
    (r : List FE) : FE :=
  match N with
  | none => pieceEvalGLB L u G pe c r
  | some nu =>
    let bc := G.C.bc pe.p.blk
    match c with
    | .res | .arg _ =>
      if (r.drop bc.B.lsize).length ≤ nu.a ∧ bc.B.dims ≠ [] then
        nuMle nu bc.B.dims (r.drop bc.B.lsize) (r.take bc.B.lsize)
      else pieceEvalGLB L u G pe c r
    | _ => pieceEvalGLB L u G pe c r

theorem pieceEvalGN_eq (N : Option NU) (L : Option Leaves) (u : Option (List Nat)) (G : PG) (pe : M3.PE)
    (c : FCol) (r : List FE) (hN : ∀ nu, N = some nu → nu = nuOf G pe c)
    (hL : ∀ lv, L = some lv → lv = leavesOf G pe c) (hu : ∀ s0, u = some s0 → unifS G pe c = some s0) :
    pieceEvalGN N L u G pe c r = pieceEvalG G pe c r := by
  have base : pieceEvalGLB L u G pe c r = pieceEvalG G pe c r := by
    rw [pieceEvalGLB_eq L u G pe c r hL, pieceEvalGL_eq L u G pe c r hL, pieceEvalGU_eq G pe c r u hu]
  cases N with
  | none => exact base
  | some nu =>
    obtain rfl := hN nu rfl
    cases c with
    | res =>
      simp only [pieceEvalGN]
      split
      · rename_i h
        rw [nuMle_eq G pe .res _ _ h.1 h.2]
        rfl
      · exact base
    | arg o =>
      simp only [pieceEvalGN]
      split
      · rename_i h
        rw [nuMle_eq G pe (.arg o) _ _ h.1 h.2]
        rfl
      · exact base
    | k => exact base
    | k' => exact base
    | F => exact base

/-- Whether a column takes the class path: `res`/`arg` with 1–8 stride classes (one class: `unifS` refused it
only for its row-0 padding check). -/
def keepNU (c : FCol) (nu : NU) : Bool :=
  (match c with
   | .res | .arg _ => true
   | _ => false) && 1 ≤ nu.cls.size && nu.cls.size ≤ 8

/-- Per piece, the classes of its non-uniform `res`/`arg` columns, built once. -/
def nuT (G : PG) : Array (List (FCol × NU)) :=
  G.pes.map fun pe => pe.p.shape.fcols.filterMap fun c =>
    if keepNU c (nuOf G pe c) then some (c, nuOf G pe c) else none

/-- The classes of piece `n`, column `c`. -/
def nuH (NT : Array (List (FCol × NU))) (n : Nat) (c : FCol) : Option NU :=
  ((NT.getD n []).find? (fun x => x.1 == c)).map (·.2)

theorem nuH_spec (G : PG) (n : Nat) (c : FCol) (nu : NU) (h : nuH (nuT G) n c = some nu) :
    nu = nuOf G (G.pe n) c := by
  unfold nuH at h
  cases hx : (((nuT G).getD n []).find? (fun x => x.1 == c)) with
  | none => rw [hx] at h; simp at h
  | some x =>
    rw [hx] at h
    simp only [Option.map_some] at h
    obtain rfl := Option.some.inj h
    have hm := List.mem_of_find?_eq_some hx
    have hc : x.1 = c := by simpa using List.find?_some hx
    by_cases hn : n < G.pes.size
    · have hU : (nuT G).getD n [] = G.pes[n].p.shape.fcols.filterMap fun c =>
          if keepNU c (nuOf G G.pes[n] c) then some (c, nuOf G G.pes[n] c) else none := by
        simp [nuT, Array.getD_eq_getD_getElem?, hn]
      rw [hU] at hm
      obtain ⟨c', -, hc'⟩ := List.mem_filterMap.mp hm
      cases hk : keepNU c' (nuOf G G.pes[n] c') <;> simp only [hk] at hc'
      · simp at hc'
      · simp only [if_true, Option.some.injEq] at hc'
        subst hc'
        simp only at hc; subst hc
        have hpe : G.pe n = G.pes[n] := by unfold PG.pe; rw [dif_pos hn]
        rw [hpe]
    · have hU : (nuT G).getD n [] = [] := by
        simp [nuT, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using Nat.le_of_not_lt hn)]
      rw [hU] at hm; simp at hm

/-- `pieceFixEvalGL` with the classes. -/
def pieceFixEvalGN (NT : Array (List (FCol × NU))) (LT : Array (List (FCol × Leaves)))
    (U : Array (List (FCol × Option (List Nat)))) (n : Nat) (G : PG) (pe : M3.PE) (c : FCol) (r : List FE) : FE :=
  match c with
  | .F => fixFEvalG G pe.p r
  | c => pieceEvalGN (nuH NT n c) (leafH LT n c) (unifH U n c) G pe c r

/-- **`grpEvalG` with the classes, the leaves and the uniform-stride hints.** -/
def grpEvalGN (NT : Array (List (FCol × NU))) (LT : Array (List (FCol × Leaves)))
    (U : Array (List (FCol × Option (List Nat)))) (G : PG) (g : Grp) (c : FCol) (r : List FE) : FE :=
  (g.mem.map fun (n, off) ↦
    let pe := G.pe n
    let h := heightF G.C pe.p
    eqSel (off >>> h) (r.drop h) * pieceFixEvalGN NT LT U n G pe c (r.take h)).foldl (· + ·) 0

theorem grpEvalGN_eq (G : PG) (g : Grp) : grpEvalGN (nuT G) (leafT G) (unifT G) G g = grpEvalG G g := by
  funext c r
  unfold grpEvalGN grpEvalG
  refine congrArg (List.foldl (· + ·) 0) ?_
  apply List.map_congr_left
  rintro ⟨n, off⟩ -
  have hp : ∀ r', pieceFixEvalGN (nuT G) (leafT G) (unifT G) n G (G.pe n) c r' = pieceFixEvalG G (G.pe n) c r' := by
    intro r'
    cases c <;> simp only [pieceFixEvalGN, pieceFixEvalG] <;>
      exact pieceEvalGN_eq _ _ _ G _ _ r' (nuH_spec G n _) (leafH_spec G n _) (unifH_spec G n _)
  simp only [hp]

/-! ## L5: the openings' table claims grouped by their point

A table's column claims share the table's point `z`: their weights on the stack are
`eqAbove(block) · eq(z, x.take τ)`, and the second factor is computed once per table (`SClaim.run`) instead of
once per column. `decideProgS` is `decideProgB` with the openings on these runs (`decideProgS_eq`). -/

/-- A stacked claim, or a table's column claims on one commitment: `(τ, z, [(offset, value)])`. -/
inductive SClaim where
  /-- A single claim. -/
  | one (c : StackClaim)
  /-- Column claims at one point `z` over `τ` variables, at the given offsets. -/
  | run (κ : Nat) (z : List FE) (bs : List (Nat × FE))

/-- The claims a run stands for. -/
def SClaim.flat : SClaim → List StackClaim
  | .one c => [c]
  | .run κ z bs => bs.map fun b => (BlockClaim.point ⟨κ, b.1⟩ z b.2).onStack

/-- The claims' weights at `x`, `eq(z, x.take τ)` once per run. -/
def SClaim.wts (x : List FE) : SClaim → List FE
  | .one c => [c.1 x]
  | .run κ z bs =>
    let E := eqEval z (x.take κ)
    bs.map fun b => (⟨κ, b.1⟩ : Placement).eqAbove x * E

theorem SClaim.wts_eq (x : List FE) (s : SClaim) : s.wts x = s.flat.map (·.1 x) := by
  cases s with
  | one c => rfl
  | run κ z bs =>
    simp only [SClaim.wts, SClaim.flat, List.map_map]
    rfl

open DM in
/-- `verifyStackedOpening` on runs. -/
def verifyStackedOpeningS (levels : List Level) (stackLog : Nat) (cs : List SClaim) (direct : Bool) (g : Nat)
    (ood : Bool) : DM Unit := do
  let claims := cs.flatMap SClaim.flat
  let scales := powers (← sampleE) claims.length
  verifyWhir levels stackLog (dot scales (claims.map (·.2)))
    (fun point => dot scales (cs.flatMap (·.wts point))) direct g ood

theorem verifyStackedOpeningS_eq (levels : List Level) (stackLog : Nat) (cs : List SClaim) (direct : Bool)
    (g : Nat) (ood : Bool) :
    verifyStackedOpeningS levels stackLog cs direct g ood =
      verifyStackedOpening levels stackLog (cs.flatMap SClaim.flat) direct g ood := by
  unfold verifyStackedOpeningS verifyStackedOpening
  simp only [SClaim.wts_eq, List.map_flatMap]

/-- The table claims on commitment `com`, one run per table (`tableClaimsR`'s order). -/
def tableRunsR (tabs : List Tab) (evs : List (List FE × List FE)) (com : Com) : List SClaim :=
  (tabs.zip evs).map fun x => .run x.1.τ x.2.1 (x.1.cols.zipIdx.filterMap fun ci => match ci.1 with
    | .com rec off => if (if rec then Com.crec else Com.main) == com then some (off, x.2.2.getD ci.2 0) else none
    | .fix _ _ => none)

theorem tableRunsR_flat (tabs : List Tab) (evs : List (List FE × List FE)) (com : Com) :
    (tableRunsR tabs evs com).flatMap SClaim.flat =
      ((tableClaimsR tabs evs).filter (·.1 == com)).map (·.2.onStack) := by
  unfold tableRunsR tableClaimsR
  rw [List.flatMap_map, List.filter_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro x _
  simp only [SClaim.flat, List.filter_filterMap, List.map_filterMap]
  apply List.filterMap_congr
  intro ci _
  rcases ci with ⟨c, i⟩
  cases c with
  | com rec off =>
    cases rec <;> by_cases hm : Com.main = com <;> by_cases hc : Com.crec = com <;>
      simp_all [Option.filter]
  | fix f e => rfl

theorem onS_flat (A B : List (Com × BlockClaim)) (tabs : List Tab) (evs : List (List FE × List FE)) (com : Com) :
    (((A.filter (·.1 == com)).map (·.2.onStack)).map SClaim.one ++ (tableRunsR tabs evs com ++
      ((B.filter (·.1 == com)).map (·.2.onStack)).map SClaim.one)).flatMap SClaim.flat =
    ((A ++ (tableClaimsR tabs evs ++ B)).filter (·.1 == com)).map (·.2.onStack) := by
  have h1 : ∀ (l : List StackClaim), (l.map SClaim.one).flatMap SClaim.flat = l := by
    intro l; induction l with
    | nil => rfl
    | cons c l ih => simp only [List.map_cons, List.flatMap_cons, ih]; rfl
  rw [List.flatMap_append, List.flatMap_append, h1, h1, tableRunsR_flat, List.filter_append, List.filter_append,
    List.map_append, List.map_append]

open DM in
/-- **`decideProgB` with the openings on runs** (`ts pub`: the tables of `m.tableClaims pub`). -/
def decideProgS (p : Params) (m : M3) (bb : BusIn → BusOutB) (ts : Pub → List Tab) (vk c : Vector UInt8 32) :
    DM Acc := do
  let sig ← read
  let pub := pubOf vk c sig
  -- 1] commit
  skip (nodeBytes * 2 ^ (p.level ⟨.main, 0⟩).cap)
  skip (nodeBytes * 2 ^ (p.level ⟨.crec, 0⟩).cap)
  -- 2] bus
  let alphas ← samples busBits
  let beta ← sampleE
  let (countRoot, point, values) ← verifyGkrGrandProducts p.busDepth
  require (countRoot != 0)
  let leafdec ← readEs p.leafdecReads
  let bus := bb ⟨alphas, beta, countRoot, point, values, leafdec, pub⟩
  require bus.ok
  -- 3] tables
  let xi ← sampleE
  let tables := m.tables pub
  let nC := (tables.map (·.nConstraints)).sum
  let xiPowers := powers xi (nC + 3)
  let formPowers := xiPowers.drop nC
  let evals ← tableSumcheckG p.tableRounds tables bus.fv (xiPowers.take nC) formPowers
    point (dot formPowers bus.totals)
  let accOut ← accFold p m pub evals
  -- 4] the tape (lvm2 S2, T1–T2)
  let tp ← dTape p.logN
  -- 5] the wire (T3–T4), after A1's range of `n`
  dRange p pub
  let wo ← dWire p pub tp.claim
  -- 6] KS
  let rk ← samples p.ksLog
  let vks ← readEs lanes
  let kko ← verifyKeccak p.ksLog rk vks
  let kring ← ringSwitch kko.slicePoint kko.slices
  let ksClaims := keccakClaims m.ksBlock kko kring
  -- 7] KS link
  let kchal ← samples (p.ksLog + laneBits)
  let kshift ← sumcheck (m.ksShiftTarget kchal) 3 (List.replicate p.ksLog none)
  let kvals ← readEs 4
  let (okK, kLinkClaims) := m.ksLink ⟨kchal, kshift, kvals, rk, pub⟩
  require okK
  -- 8] the openings
  let rest : List (Com × BlockClaim) :=
    (tapeClaims p tp wo pub ++ ksClaims).map (.main, ·) ++ m.ksOutputClaims rk vks ++ kLinkClaims
  let onS (com : Com) : List SClaim :=
    ((bus.claims.filter (·.1 == com)).map (·.2.onStack)).map .one ++ tableRunsR (ts pub) evals com ++
      ((rest.filter (·.1 == com)).map (·.2.onStack)).map .one
  verifyStackedOpeningS p.recLevels p.nuRec (onS .crec) false p.grind false
  verifyStackedOpeningS p.mainLevels p.nuMain (onS .main) false p.grind p.mainOod
  pure accOut

theorem decideProgS_eq (p : Params) (m : M3) (bb : BusIn → BusOutB) (ts : Pub → List Tab)
    (h : ∀ pub evs, m.tableClaims pub evs = tableClaimsR (ts pub) evs) (vk c : Vector UInt8 32) :
    decideProgS p m bb ts vk c = decideProgB p m bb vk c := by
  unfold decideProgS decideProgB
  simp only [verifyStackedOpeningS_eq, List.append_assoc, onS_flat, h]

/-- `decideFB` on `decideProgS`. -/
def decideFS (p : Params) (m : M3) (bb : BusIn → BusOutB) (ts : Pub → List Tab) (vk c : Vector UInt8 32)
    (sig : ByteArray) : Bool :=
  let (a, s) := (decideProgS p m bb ts vk c).runOn sig
  (s.ok && s.ent == sig.size && s.msg == 0) && AccOk p m (pubOf vk c sig) a

/-- `VSB` on `decideFS`. -/
def VSS (p : Params) (m : M3) (bb : BusIn → BusOutB) (ts : Pub → List Tab) (vk c : Digest) (π : Proof) :
    OProg Bool :=
  if parseOk p vk c π then drive p π (decideFS p m bb ts vk c) else .ret false

theorem VSS_eq (p : Params) (m : M3) (bb : BusIn → BusOutB) (ts : Pub → List Tab)
    (h : ∀ pub evs, m.tableClaims pub evs = tableClaimsR (ts pub) evs) : VSS p m bb ts = VSB p m bb := by
  funext vk c π
  unfold VSS VSB decideFS decideFB
  simp only [decideProgS_eq p m bb ts h]

/-! ## The parts and `V_S` at `P20` with the V-LEV2 twins -/

/-- **The parts** of `QAsm.tabs C G D`, the groups with `grpEvalGN`. -/
def pre2 (C : QCfg) (G : PG) (D : QData) : Pre :=
  let U := unifT G
  let LT := leafT G
  let NT := nuT G
  { unif := U
    leaves := LT
    grps := (List.range D.groups.length).map fun i =>
    shapeTab (D.groups.getD i default).σ (D.groups.getD i default).τ (grpFix G.C.Q (D.groups.getD i default))
      (grpEvalGN NT LT U G (D.groups.getD i default)) (plOf D i)
    head := (arrsHead C D).map InArr.tab
    tail := (arrsTail C D).map InArr.tab
    aux := auxF C D }

theorem tabsPre2_eq (C : QCfg) (G : PG) (D : QData) (P : Pub) :
    tabsPre (pre2 C G D) C D P = QAsm.tabs C G D P := by
  unfold tabsPre pre2 QAsm.tabs lvmTabsC
  rw [arrs_split, auxF_eq]
  simp only [List.map_append, List.map_cons, List.map_nil, grpEvalGN_eq]

/-- The parts at `P20` (a top-level constant: evaluated once per process). -/
def pre20G : Pre := pre2 cfg20 M3.G20 data20

/-- **The `P20` tables** with the V-LEV2 twins. -/
def tabs20G (P : Pub) : List Tab := tabsPre pre20G cfg20 data20 P

theorem tabs20G_eq : tabs20G = tabs20F := funext fun P => by
  unfold tabs20G pre20G
  rw [tabsPre2_eq, tabs20F_eq]
  rfl

/-- The `P20` M3 instance on `tabs20G` (`m20F`'s text). -/
def m20G : M3 :=
  { M3.ofParts P20 (fun i => busFinalRF (sumcheckTabs (tabs20G i.pub)) i)
      (fun pub => (sumcheckTabs (tabs20G pub)).map nativeTableF)
      (fun pub => tableClaimsR (sumcheckTabs (tabs20G pub)))
      (fun pub => fixValsR (sumcheckTabs (tabs20G pub)) P20.pubTab)
      (fun pub => fixSentR (sumcheckTabs (tabs20G pub)) P20.pubTab)
      (fun pub => pubCheckR P20.pubTab pub) with
    ksLink := ksLinkF P20 }

theorem m20G_eq : m20G = m20F := by
  unfold m20G m20F
  rw [tabs20G_eq]

/-- The `P20` bus step on `tabs20G`. -/
def busB20G (i : BusIn) : BusOutB := busFinalV (sumcheckTabs (tabs20G i.pub)) i

theorem busB20G_eq : busB20G = busB20 := by
  funext i
  unfold busB20G busB20
  rw [tabs20G_eq]

/-- **`V_S` at `P20`**, with the V-LEV2 twins. -/
def VS20G (vk c : Digest) (π : Proof) : OProg Bool :=
  VSS P20 m20G busB20G (fun pub => sumcheckTabs (tabs20G pub)) vk c π

/-- **It is `VS20F`** (hence `VS20`). -/
theorem VS20G_eq : VS20G = VS20F := by
  funext vk c π
  unfold VS20G VS20F
  rw [VSS_eq P20 m20G busB20G _ (fun _ _ => rfl), m20G_eq, busB20G_eq]

end Lvm.VF
