-- New for lvm (HAR-WH): the claim batching of a stacked opening, part 3: the claims as trie terms
-- and the batched basis `Σ_i s^i · onStack_i(x)` (`basisG`, `basisG_spec`); with `targetG`
-- (`LvmQAsmArith2WhirBasis0`) the two values `verifyStackedOpening` batches.
import LvmQAsmArith2WhirBasis1

/-!
# Claim batching, part 3: the basis

Every claim becomes trie terms (`TC`, `LvmQAsmArith2WhirBasis0`) of value
`scale · Π_{i ∈ [k, ν)} f(bit_i, x_i) · leaf`:

* a point claim `(blk, z)`: one term, scale `s^i`; the bits are `eqAbove`'s selector bits on
  `[vc, ν)` and, below `vc`, the maximal suffix of `z` made of the constant cells `z` (bit 0) and
  `o` (bit 1) (`ncPre`, `bitP`); the leaf is the memoised chain `Π_{i<k} (1 + z_i + x_i)`
  (`chainG`: table claims share their point, so their chains are memo hits);
* a ring claim `(blk, pt, cs)`: one term, the selector bits on `[vc, ν)`, the leaf
  `ringWeight pt (x.take vc) cs` (`ringLeaf`);
* a sum claim `(nu, parts)`: one term per part, scale `s^i · c_j` (one row), bits 0 on `[nu, ν)`
  then the part's as for a point claim.

`partW_eq` is the algebra (`eqAbove`, `eqEval` as products of the factors `f(bit, x_i)`); the
terms' sum is `F`'s `dot (powers s n) (claims.map (·.onStack.1 x))` (`claimTerms_spec`,
`basisG_spec`). **Rows** (`E·E` `mulAdd` unless noted): `targetG` 1 per claim; `basisG`: per term
1 (leaf) + 1 per sum part (scale); per new chain prefix 2 (`E lin` + `mulAdd`); per one-child trie
node 1, per two-child node 2 (`E lin` + `mulAdd`); per ring claim `vc` + 64 copies (`E lin`),
`130·vc + 1` loop rows + 65 (QA2's `fChunks`/`pChunks`, 64-sum).
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Loop.QRing

variable {c : Ctx} {M : Mem}

/-! ## Keys -/

/-- The length of `l` without its maximal suffix of constant cells (`z` or `o`). -/
def ncPre (z o : Cell) : List Cell → Nat
  | [] => 0
  | a :: l => if ncPre z o l = 0 ∧ (a = z ∨ a = o) then 0 else ncPre z o l + 1

theorem ncPre_le (z o : Cell) : ∀ l : List Cell, ncPre z o l ≤ l.length
  | [] => le_rfl
  | a :: l => by
    have := ncPre_le z o l
    simp only [ncPre, List.length_cons]
    split_ifs <;> omega

theorem ncPre_const (z o : Cell) : ∀ (l : List Cell) (i : Nat), ncPre z o l ≤ i → i < l.length →
    l.getD i default = z ∨ l.getD i default = o
  | [], _, _, hi => by simp at hi
  | a :: l, i, hk, hi => by
    simp only [ncPre] at hk
    split_ifs at hk with h
    · rcases i with _ | i
      · simpa using h.2
      · simpa using ncPre_const z o l i (by omega) (by simpa using hi)
    · rcases i with _ | i
      · omega
      · simpa using ncPre_const z o l i (by omega) (by simpa using hi)

/-- Bit `i` of the selector above a block (`eqAbove`'s `selectorPoint`). -/
def selbit (blk : Placement) (i : Nat) : Bool :=
  (blk.index >>> blk.variableCount >>> (i - blk.variableCount)) % 2 == 1

/-- The bit of coordinate `i` of a part of a claim on `nu` variables: 0 above `nu`, the selector
on `[vc, nu)`, the constant cell below. -/
def bitP (z o : Cell) (nu : Nat) (blk : Placement) (zl : List Cell) (i : Nat) : Bool :=
  if nu ≤ i then false else if blk.variableCount ≤ i then selbit blk i else zl.getD i default == o

/-- The key of the coordinates `[k, n)`, the top one first. -/
def keyOf (bit : Nat → Bool) : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, k => if n < k then [] else bit n :: keyOf bit n k

theorem kprod_keyOf (X : Nat → FE) (bit : Nat → Bool) (k : Nat) :
    ∀ n, kprod X n (keyOf bit n k) = ∏ i ∈ Finset.Ico k n, fb (bit i) (X i)
  | 0 => by simp [keyOf, kprod]
  | n + 1 => by
    simp only [keyOf]
    split_ifs with h
    · rw [Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty]; rfl
    · rw [kprod, kprod_keyOf X bit k n, Finset.prod_Ico_succ_top (by omega)]
      ring

/-! ## The algebra -/

theorem eOfNat_zero : eOfNat 0 = 0 := rfl
theorem eOfNat_one : eOfNat 1 = 1 := rfl

theorem eOfNat_bit (b : Nat) (y : FE) : 1 + eOfNat (b % 2) + y = fb (b % 2 == 1) y := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> rw [h]
  · simp [fb, eOfNat_zero]
  · simp only [eOfNat_one, fb, beq_self_eq_true, if_true]
    rw [CharTwo.add_self_eq_zero, zero_add]

theorem getD_take' {α : Type} (l : List α) (d : α) {i m : Nat} (hi : i < m) :
    (l.take m).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

/-- **`eqAbove` as a product** of the factors `f(bit_i, y_i)` over `[vc, |ys|)`. -/
theorem eqAbove_prod (blk : Placement) (ys : List FE) (Y : Nat → FE) (hv : blk.variableCount ≤ ys.length)
    (hy : ∀ i < ys.length, ys.getD i 0 = Y i) :
    blk.eqAbove ys = ∏ i ∈ Finset.Ico blk.variableCount ys.length, fb (selbit blk i) (Y i) := by
  rw [Placement.eqAbove, eqEval_prod _ _ (by simp [selectorPoint]), Finset.prod_Ico_eq_prod_range]
  simp only [selectorPoint, List.length_map, List.length_range]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj', Option.map_some,
    Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    hy _ (by omega), eOfNat_bit, selbit, Nat.add_sub_cancel_left]

/-- The point `x` as a list. -/
def xsOf (M : Mem) (ν xb : Nat) : List FE := (List.range ν).map fun i => M.e (xb + i)

theorem xs_length (ν xb : Nat) : (xsOf M ν xb).length = ν := by simp [xsOf]

theorem xs_getD {ν xb i : Nat} (hi : i < ν) : (xsOf M ν xb).getD i 0 = M.e (xb + i) := by
  simp [xsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

/-- The selector-and-point part of a part's weight on `nu` variables. -/
def partW (M : Mem) (ν xb nu : Nat) (blk : Placement) (zl : List Cell) : FE :=
  blk.eqAbove ((xsOf M ν xb).take nu) * eqEval (vs M zl) (((xsOf M ν xb).take nu).take blk.variableCount)

/-- The zero selector bits above `nu`. -/
def e0f (M : Mem) (ν xb nu : Nat) : FE := ∏ i ∈ Finset.Ico nu ν, (1 + M.e (xb + i))

theorem bitP_hi {z o : Cell} {nu : Nat} {blk : Placement} {zl : List Cell} {i : Nat} (h : nu ≤ i) :
    bitP z o nu blk zl i = false := by simp [bitP, h]

theorem bitP_mid {z o : Cell} {nu : Nat} {blk : Placement} {zl : List Cell} {i : Nat} (h : ¬ nu ≤ i)
    (h' : blk.variableCount ≤ i) : bitP z o nu blk zl i = selbit blk i := by simp [bitP, h, h']

theorem bitP_lo {z o : Cell} {nu : Nat} {blk : Placement} {zl : List Cell} {i : Nat} (h : ¬ nu ≤ i)
    (h' : ¬ blk.variableCount ≤ i) : bitP z o nu blk zl i = (zl.getD i default == o) := by
  simp [bitP, h, h']

/-- **A part's weight as a product**: the key's factors on `[k, ν)` times the chain below `k`. -/
theorem partW_eq {ν xb nu : Nat} {z o : Cell} {blk : Placement} {zl : List Cell}
    (hz : z.val M = 0) (ho : o.val M = 1)
    (hzl : zl.length = blk.variableCount) (hvc : blk.variableCount ≤ nu) (hnu : nu ≤ ν) :
    (∏ i ∈ Finset.Ico (ncPre z o zl) ν, fb (bitP z o nu blk zl i) (M.e (xb + i))) *
        cv M (fun i => M.e (xb + i)) zl (ncPre z o zl) = e0f M ν xb nu * partW M ν xb nu blk zl := by
  have hk : ncPre z o zl ≤ blk.variableCount := hzl ▸ ncPre_le z o zl
  have hys : ((xsOf M ν xb).take nu).length = nu := by rw [List.length_take, xs_length]; omega
  have e1 : ∏ i ∈ Finset.Ico nu ν, fb (bitP z o nu blk zl i) (M.e (xb + i)) = e0f M ν xb nu :=
    Finset.prod_congr rfl fun i hi => by
      rw [bitP_hi (Finset.mem_Ico.mp hi).1]; rfl
  have e2 : ∏ i ∈ Finset.Ico blk.variableCount nu, fb (bitP z o nu blk zl i) (M.e (xb + i)) =
      blk.eqAbove ((xsOf M ν xb).take nu) := by
    rw [eqAbove_prod blk _ (fun i => M.e (xb + i)) (by rw [hys]; exact hvc) (fun i hi => by
      rw [hys] at hi; rw [getD_take' _ _ hi, xs_getD (by omega)]), hys]
    refine Finset.prod_congr rfl fun i hi => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
    rw [bitP_mid (by omega) h1]
  have hZ : ∀ i < blk.variableCount, (vs M zl).getD i 0 = (zl.getD i default).val M := fun i hi =>
    getD_map_val zl (by omega)
  have e3 : eqEval (vs M zl) (((xsOf M ν xb).take nu).take blk.variableCount) =
      cv M (fun i => M.e (xb + i)) zl (ncPre z o zl) *
        ∏ i ∈ Finset.Ico (ncPre z o zl) blk.variableCount, fb (bitP z o nu blk zl i) (M.e (xb + i)) := by
    rw [eqEval_prod _ _ (by simp [vs, xs_length, hzl]; omega)]
    have hl : (vs M zl).length = blk.variableCount := by simp [vs, hzl]
    rw [hl, cv, ← Finset.prod_range_mul_prod_Ico _ hk]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [hZ i (by omega), getD_take' _ _ (by omega), getD_take' _ _ (by omega), xs_getD (by omega)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
      rw [hZ i h2, getD_take' _ _ h2, getD_take' _ _ (by omega), xs_getD (by omega),
        bitP_lo (by omega) (by omega)]
      rcases ncPre_const z o zl i h1 (by omega) with hc | hc
      · by_cases ho' : zl.getD i default = o
        · rw [ho', ho, beq_self_eq_true, fb, if_pos rfl, CharTwo.add_self_eq_zero, zero_add]
        · have hb : (zl.getD i default == o) = false := by simpa using ho'
          rw [hb, hc, hz, fb, if_neg (by simp), add_zero]
      · rw [hc, ho, beq_self_eq_true, fb, if_pos rfl, CharTwo.add_self_eq_zero, zero_add]
  rw [partW, e3, ← e2, ← e1, ← Finset.prod_Ico_consecutive _ hk (le_trans hvc hnu),
    ← Finset.prod_Ico_consecutive _ hvc hnu]
  ring

/-! ## Terms of the claims -/

/-- The term of a part (a point claim, or a part of a sum claim on `nu` variables). -/
def partTerm (ν xb : Nat) (z o sc : Cell) (nu : Nat) (blk : Placement) (zl : List Cell) (memo : Memo) :
    BM (Memo × TC) := do
  let r ← chainG xb z o zl (ncPre z o zl) memo
  pure (r.1, ⟨sc, keyOf (bitP z o nu blk zl) ν (ncPre z o zl), r.2⟩)

/-- The term of a ring claim. -/
def ringTerm (ν xb : Nat) (z sc : Cell) (blk : Placement) (pt cs : List Cell) : BM TC := do
  let lf ← ringLeaf blk.variableCount pt cs xb z.n
  pure ⟨sc, keyOf (selbit blk) ν blk.variableCount, lf⟩

/-- The terms of a sum claim's parts (scale `sc · c_j`). -/
def partsTerms (ν xb : Nat) (z o sc : Cell) (nu : Nat) :
    List (Cell × Placement × List Cell) → Memo → BM (Memo × List TC)
  | [], memo => pure (memo, [])
  | x :: ps, memo => do
    let sc' ← mulAdd .E sc x.1 z
    let r ← partTerm ν xb z o sc' nu x.2.1 x.2.2 memo
    let r' ← partsTerms ν xb z o sc nu ps r.1
    pure (r'.1, r.2 :: r'.2)

/-- The terms of a claim (scale cell `sc`). -/
def oneClaim (ν xb : Nat) (z o sc : Cell) (cc : CClaim) (memo : Memo) : BM (Memo × List TC) :=
  match cc.cw with
  | .point blk zl => do
    let r ← partTerm ν xb z o sc ν blk zl memo
    pure (r.1, [r.2])
  | .ring blk pt cs => do
    let t ← ringTerm ν xb z sc blk pt cs
    pure (memo, [t])
  | .sum nu parts => partsTerms ν xb z o sc nu parts memo

/-- The terms of the claims from index `i` (scale cells `sp + i`). -/
def claimTerms (ν xb : Nat) (z o : Cell) (sp : Nat) : Nat → List CClaim → Memo → BM (Memo × List TC)
  | _, [], memo => pure (memo, [])
  | i, cc :: cl, memo => do
    let r ← oneClaim ν xb z o (ec (sp + i)) cc memo
    let r' ← claimTerms ν xb z o sp (i + 1) cl r.1
    pure (r'.1, r.2 ++ r'.2)

/-- Static well-formedness of one claim. -/
def WF1 (ν : Nat) (cc : CClaim) : Bool :=
  match cc.cw with
  | .point blk zl => decide (blk.variableCount ≤ ν) && decide (zl.length = blk.variableCount)
  | .ring blk pt cs => decide (blk.variableCount ≤ ν) && decide (pt.length = blk.variableCount) &&
      decide (cs.length = 64) && decide (sz (binDec 64 blk.variableCount 0) = blk.variableCount)
  | .sum nu parts => decide (nu ≤ ν) &&
      parts.all fun x => decide (x.2.1.variableCount ≤ nu) && decide (x.2.2.length = x.2.1.variableCount)

/-- Static well-formedness of the claims for a stack of `ν` variables (cheap to decide on ≈ 3 k claims). -/
def ClaimsWF (ν : Nat) (cl : List CClaim) : Bool := cl.all (WF1 ν)

/-- The batched weight `Σ_i s^i · onStack_i(x)` at the point in the `E` cells `xb + i`, `i < ν`. -/
def basisG (ν : Nat) (cl : List CClaim) (sp xb : Nat) (z o _g : Cell) : BM Cell := do
  let r ← claimTerms ν xb z o sp 0 cl []
  trieG xb z ν r.2

/-! ## Specs -/

section
variable {ν xb : Nat} {z o : Cell}

theorem partTerm_spec (hz : z.val M = 0) (ho : o.val M = 1) {sc : Cell} {nu : Nat} {blk : Placement}
    {zl : List Cell} {memo : Memo} (hm : MemoOk M (fun i => M.e (xb + i)) memo)
    (hzl : zl.length = blk.variableCount) (hvc : blk.variableCount ≤ nu) (hnu : nu ≤ ν) :
    Hs c M (partTerm ν xb z o sc nu blk zl memo) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
      tval M (fun i => M.e (xb + i)) ν r.2 = sc.val M * (e0f M ν xb nu * partW M ν xb nu blk zl)) :=
  hs_bind (chainG_spec hz ho _ memo (ncPre_le z o zl) hm) fun r ⟨hm', hv⟩ => hs_pure ⟨hm', by
    rw [tval, kprod_keyOf, hv, ← partW_eq hz ho hzl hvc hnu]
    ring⟩

theorem zval_e (hz : z.val M = 0) (hzE : z.ty = .E) : M.e z.n = 0 := by
  rw [← hz]; rcases z with ⟨ty, n⟩; cases hzE; rfl

theorem ringTerm_spec (hz : z.val M = 0) (hzE : z.ty = .E) {sc : Cell} {blk : Placement} {pt cs : List Cell}
    (hvc : blk.variableCount ≤ ν) (hpt : pt.length = blk.variableCount) (hcs : cs.length = 64)
    (hbs : sz (binDec 64 blk.variableCount 0) = blk.variableCount) :
    Hs c M (ringTerm ν xb z sc blk pt cs) (fun t => tval M (fun i => M.e (xb + i)) ν t =
      sc.val M * (blk.eqAbove (xsOf M ν xb) *
        ringWeight (vs M pt) ((xsOf M ν xb).take blk.variableCount) (vs M cs))) :=
  hs_bind (ringLeaf_spec (zval_e hz hzE) hpt hcs hbs ((xsOf M ν xb).take blk.variableCount)
    (by rw [List.length_take, xs_length]; omega)
    (fun n hn => by rw [getD_take' _ _ hn, xs_getD (by omega)])) fun lf hlf => hs_pure (by
    rw [tval, kprod_keyOf, hlf, eqAbove_prod blk _ (fun i => M.e (xb + i)) (by rw [xs_length]; exact hvc)
      (fun i hi => xs_getD (by rwa [xs_length] at hi)), xs_length]
    ring)

theorem partsTerms_spec (hz : z.val M = 0) (ho : o.val M = 1) {sc : Cell} {nu : Nat} (hnu : nu ≤ ν) :
    ∀ (ps : List (Cell × Placement × List Cell)) (memo : Memo),
      (ps.all fun x => decide (x.2.1.variableCount ≤ nu) && decide (x.2.2.length = x.2.1.variableCount)) = true →
      MemoOk M (fun i => M.e (xb + i)) memo →
      Hs c M (partsTerms ν xb z o sc nu ps memo) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
        (r.2.map (tval M (fun i => M.e (xb + i)) ν)).sum =
          sc.val M * (e0f M ν xb nu * (ps.map fun x => x.1.val M * partW M ν xb nu x.2.1 x.2.2).sum))
  | [], memo, _, hm => hs_pure ⟨hm, by simp⟩
  | x :: ps, memo, hwf, hm => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨h1, h2⟩, hrest⟩ := hwf
    show Hs c M (mulAdd .E sc x.1 z >>= fun sc' => partTerm ν xb z o sc' nu x.2.1 x.2.2 memo >>= fun r =>
      partsTerms ν xb z o sc nu ps r.1 >>= fun r' => pure (r'.1, r.2 :: r'.2)) _
    refine hs_bind (hs_mulAdd _ _ _ _) fun sc' hsc => hs_bind (partTerm_spec hz ho hm h2 h1 hnu)
      fun r ⟨hm', hv⟩ => hs_bind (partsTerms_spec hz ho hnu ps r.1 hrest hm') fun r' ⟨hm'', hv'⟩ =>
        hs_pure ⟨hm'', ?_⟩
    rw [List.map_cons, List.sum_cons, hv, hv', hsc, hz, List.map_cons, List.sum_cons]
    ring

theorem sumE_eq (l : List FE) : sumE l = l.sum := by
  rw [sumE, foldl_add_id, zero_add]

/-- A sum claim's weight on the stack. -/
theorem sum_onStack (nu : Nat) (parts : List (Cell × Placement × List Cell)) (com : Com) (v : Cell)
    (xs : List FE) :
    ((⟨com, .sum nu parts, v⟩ : CClaim).val M).2.onStack.1 xs =
      (⟨nu, 0⟩ : Placement).eqAbove xs * (parts.map fun x => x.1.val M *
        (x.2.1.eqAbove (xs.take nu) * eqEval (vs M x.2.2) ((xs.take nu).take x.2.1.variableCount))).sum := by
  simp only [CClaim.val, sumClaim, BlockClaim.onStack, sumE_eq, List.map_map]
  refine congrArg (_ * ·) (congrArg List.sum (List.map_congr_left fun x _ => ?_))
  rcases x with ⟨k, blk, zl⟩
  simp only [Function.comp_apply]
  ring

theorem oneClaim_spec (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) {sc : Cell} {cc : CClaim}
    {memo : Memo} (hwf : WF1 ν cc = true) (hm : MemoOk M (fun i => M.e (xb + i)) memo) :
    Hs c M (oneClaim ν xb z o sc cc memo) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
      (r.2.map (tval M (fun i => M.e (xb + i)) ν)).sum = sc.val M * (cc.val M).2.onStack.1 (xsOf M ν xb)) := by
  rcases cc with ⟨com, cw, v⟩
  cases cw with
  | point blk zl =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    show Hs c M (partTerm ν xb z o sc ν blk zl memo >>= fun r => pure (r.1, [r.2])) _
    refine hs_bind (partTerm_spec hz ho hm hwf.2 hwf.1 le_rfl) fun r ⟨hm', hv⟩ => hs_pure ⟨hm', ?_⟩
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hv, e0f, partW, Finset.Ico_self,
      Finset.prod_empty, List.take_of_length_le (by rw [xs_length])]
    show _ = sc.val M * (blk.eqAbove (xsOf M ν xb) * eqEval (vs M zl) ((xsOf M ν xb).take blk.variableCount))
    ring
  | ring blk pt cs =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hwf
    show Hs c M (ringTerm ν xb z sc blk pt cs >>= fun t => pure (memo, [t])) _
    refine hs_bind (ringTerm_spec hz hzE h1 h2 h3 h4) fun t ht => hs_pure ⟨hm, ?_⟩
    rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ht]
    rfl
  | sum nu parts =>
    simp only [WF1, Bool.and_eq_true, decide_eq_true_eq] at hwf
    show Hs c M (partsTerms ν xb z o sc nu parts memo) _
    refine hs_mono (partsTerms_spec hz ho hwf.1 parts memo hwf.2 hm) fun r ⟨hm', hv⟩ => ⟨hm', ?_⟩
    rw [hv, sum_onStack, eqAbove_prod ⟨nu, 0⟩ _ (fun i => M.e (xb + i)) (by rw [xs_length]; exact hwf.1)
      (fun i hi => xs_getD (by rwa [xs_length] at hi)), xs_length]
    have e0 : ∏ i ∈ Finset.Ico nu ν, fb (selbit ⟨nu, 0⟩ i) (M.e (xb + i)) = e0f M ν xb nu :=
      Finset.prod_congr rfl fun i _ => by simp [selbit, fb]
    rw [e0]
    exact congrArg (_ * ·) (congrArg (_ * ·) (congrArg List.sum (List.map_congr_left fun x _ => rfl)))

theorem claimTerms_spec (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) {sp N : Nat} {s : FE}
    (hs : ∀ j < N, M.e (sp + j) = s ^ j) :
    ∀ (cl : List CClaim) (i : Nat) (memo : Memo), cl.all (WF1 ν) = true →
      MemoOk M (fun i => M.e (xb + i)) memo → i + cl.length ≤ N →
      Hs c M (claimTerms ν xb z o sp i cl memo) (fun r => MemoOk M (fun i => M.e (xb + i)) r.1 ∧
        (r.2.map (tval M (fun i => M.e (xb + i)) ν)).sum =
          bsum s i (cl.map fun cc => (cc.val M).2.onStack.1 (xsOf M ν xb)))
  | [], _, memo, _, hm, _ => hs_pure ⟨hm, by simp [bsum]⟩
  | cc :: cl, i, memo, hwf, hm, hN => by
    simp only [List.all_cons, Bool.and_eq_true] at hwf
    simp only [List.length_cons] at hN
    show Hs c M (oneClaim ν xb z o (ec (sp + i)) cc memo >>= fun r =>
      claimTerms ν xb z o sp (i + 1) cl r.1 >>= fun r' => pure (r'.1, r.2 ++ r'.2)) _
    refine hs_bind (oneClaim_spec hz ho hzE hwf.1 hm) fun r ⟨hm', hv⟩ =>
      hs_bind (claimTerms_spec hz ho hzE hs cl (i + 1) r.1 hwf.2 hm' (by omega)) fun r' ⟨hm'', hv'⟩ =>
        hs_pure ⟨hm'', ?_⟩
    rw [List.map_append, List.sum_append, hv, hv', List.map_cons, bsum, Cell.val_E, hs i (by omega)]

end

/-- **The batched basis**: the cell is `F`'s `dot (powers s n) (claims.map (·.onStack.1 x))`. -/
theorem basisG_spec {ν : Nat} {cl : List CClaim} {sp xb : Nat} {z o g : Cell} {p : Ptr}
    (h : SegsHold c M p (basisG ν cl sp xb z o g p).2) (hwf : ClaimsWF ν cl = true)
    (hz : z.val M = 0) (ho : o.val M = 1) (hzE : z.ty = .E) (_hoE : o.ty = .E) (_hg : g.ty = .K)
    (_hp : 1 ≤ p.e) (s : FE) (hs : ∀ i < cl.length, M.e (sp + i) = s ^ i) :
    (basisG ν cl sp xb z o g p).1.val M =
      Lvm.dot (powers s cl.length) (cl.map fun cc => (cc.val M).2.onStack.1 ((List.range ν).map fun i => M.e (xb + i))) := by
  have key := hs_bind (claimTerms_spec (c := c) (ν := ν) (xb := xb) hz ho hzE hs cl 0 [] hwf
    (fun _ he => by simp at he) (by omega)) fun r ⟨_, hv⟩ =>
      hs_mono (trieG_spec (c := c) (xb := xb) hz ν r.2) fun w hw => hw.trans hv
  have e := key p h
  rw [show (basisG ν cl sp xb z o g p).1 = ((claimTerms ν xb z o sp 0 cl [] >>= fun r => trieG xb z ν r.2) p).1
    from rfl, e]
  show _ = Lvm.dot (powers s cl.length) (cl.map fun cc => (cc.val M).2.onStack.1 (xsOf M ν xb))
  have hl : cl.length = (cl.map fun cc => (cc.val M).2.onStack.1 (xsOf M ν xb)).length := by simp
  rw [hl, dot_powers_bsum]

end Lvm.Har
