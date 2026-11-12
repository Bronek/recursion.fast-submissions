-- adapted from rf-k/submissions/flock-recursive/lean/FRXOut.lean@kk/base
-- (8bff272b; section `G6_FRNodeReadS`: `Seg`, `segOut`, `segLen`, `catL`; section `G6_FRXOut`: the
-- compiler `segIR` and its proofs), with FR's helpers `LoKSg`, `hframeKSg`, `entryK_countSg`,
-- `inv_entryKSg`, `inv_decSSg`, `shr_toWordSg`, `shl_toWordSg`, `and_one_toWordSg` from `FRXRead.lean@kk/base`
-- and `noW_lo` from `FRXNd4.lean@kk/base`. Changes for lvm (WP-13a): namespace `Lvm.X`; FR's
-- position-bit sibling `sib` (and `sibW`, `sibHit`, `sibH`, `sibP`, `sibIR`) is replaced by the
-- compare-based `sibc`; new: the contiguous address shape `apC`, the cost/size/output bounds.
import LvmXLookup

/-!
# Output segments and their compiled code: `Seg`, `segOut`, `segIR`

A small language of **segments** (`Seg`) says which words an output program emits, read from a
word source `W` at a base offset `b`:

* `wd x`: the constant word `x`; `cp o n`: the `n` words `W (b + o + j)`;
* `rep c s x`: `x` at the bases `b + s j`, `j < c`; `cat`, `nil`;
* `shw o`, `sh8 o`: shifted words (`(W o >>> 8) + (W (o + 1) <<< 56)`, `W o >>> 8`);
* `kite x y`: `x` under the kind flag `κ`, else `y`;
* `sibc o`: **one Merkle sibling chosen by comparison**: the node query entry whose length word is
  `W (b + o)` has the left half `W (b + o + 1 … b + o + 4)` and the right half
  `W (b + o + 5 … b + o + 8)`; the previous entry's answer is `W (b + o − 4 … b + o − 1)`. If the
  left half is that answer, the sibling is the right half, else the left half.

`segOut W κ b s` is the list a segment denotes. A segment is compiled to `XIR` (`segIR ap d`), with
no store: every word is read from the heap by one computed load (`ldw ap`) at

`addrW ap R n = R + (((n >>> 1) &&& m₁) <<< st) + ((n >>> s₃) <<< s₄) + (n &&& 1)`

(`ap = (m₁, s₃, s₄, st)`); `apC` is the contiguous shape (`addrW_apC`: `R + n`). The base offset of
a segment is register `oBd d` at nesting depth `d`; a `rep` at depth `d` counts in `oCd d` and
moves the base of depth `d + 1`.

* **`segIR_sem`**: from a state in context (`Ctx`: the heap is `M₀`'s, `oR = R`, the kind flag),
  the compiled segment appends `segOut (src M₀ ap R) κ b s` to the output;
* `wf_segIR`, `loK_segIR` (no store), `noLoopT_segIR`, `ctx_segIR` (the context is kept);
* `cost_segIR`, `outs_segIR` (syntactic bounds `segCost`, `segOuts`), `sizeIR_segIR` (exact,
  `segSize`).
-/

namespace Lvm.X

open RecursionFast

/-! ## Specification: segments -/

/-- An output segment over a word source. -/
inductive Seg where
  /-- Nothing. -/
  | nil
  /-- One segment, then the other. -/
  | cat (a b : Seg)
  /-- A constant word. -/
  | wd (x : Word)
  /-- `n` source words from `b + o`. -/
  | cp (o n : ℕ)
  /-- `c` copies of the body, the base advancing by `s`. -/
  | rep (c s : ℕ) (body : Seg)
  /-- The word of bytes `1 … 8` of source words `o, o + 1`. -/
  | shw (o : ℕ)
  /-- The word of bytes `1 … 7` of source word `o`. -/
  | sh8 (o : ℕ)
  /-- By the kind flag: the first if it is set, else the second. -/
  | kite (a b : Seg)
  /-- One Merkle sibling chosen by comparison, for the node query entry at `b + o` (`segOut`). -/
  | sibc (o : ℕ)

/-- **The words a segment denotes**, from base `b`, for the kind flag `κ`. -/
def segOut (W : ℕ → Word) (κ : Bool) : ℕ → Seg → List Word
  | _, .nil => []
  | b, .cat x y => segOut W κ b x ++ segOut W κ b y
  | _, .wd x => [x]
  | b, .cp o n => (List.range n).map fun j => W (b + o + j)
  | b, .rep c s x => (List.range c).flatMap fun j => segOut W κ (b + s * j) x
  | b, .shw o => [(W (b + o) >>> 8) + (W (b + o + 1) <<< 56)]
  | b, .sh8 o => [W (b + o) >>> 8]
  | b, .kite x y => if κ then segOut W κ b x else segOut W κ b y
  | b, .sibc o =>
    if (List.range 4).map (fun j => W (b + o + 1 + j)) = (List.range 4).map (fun j => W (b + o - 4 + j))
    then (List.range 4).map (fun j => W (b + o + 5 + j))
    else (List.range 4).map (fun j => W (b + o + 1 + j))

/-- The number of words a segment denotes. -/
def segLen (κ : Bool) : Seg → ℕ
  | .nil => 0
  | .cat x y => segLen κ x + segLen κ y
  | .wd _ | .shw _ | .sh8 _ => 1
  | .cp _ n => n
  | .rep c _ x => c * segLen κ x
  | .kite x y => if κ then segLen κ x else segLen κ y
  | .sibc _ => 4

/-- A list of segments in turn. -/
def catL : List Seg → Seg
  | [] => .nil
  | x :: xs => .cat x (catL xs)

theorem segOut_length (W : ℕ → Word) (κ : Bool) : ∀ (s : Seg) (b : ℕ),
    (segOut W κ b s).length = segLen κ s
  | .nil, _ => rfl
  | .cat x y, b => by simp [segOut, segLen, segOut_length W κ x, segOut_length W κ y]
  | .wd _, _ => rfl
  | .cp _ _, _ => by simp [segOut, segLen]
  | .rep c s x, b => by
    simp [segOut, segLen, List.length_flatMap, segOut_length W κ x]
  | .shw _, _ => rfl
  | .sh8 _, _ => rfl
  | .kite x y, b => by cases κ <;> simp [segOut, segLen, segOut_length W _ x, segOut_length W _ y]
  | .sibc o, b => by simp only [segOut, segLen]; split <;> simp

theorem segOut_catL (W : ℕ → Word) (κ : Bool) (b : ℕ) : ∀ l : List Seg,
    segOut W κ b (catL l) = l.flatMap (segOut W κ b)
  | [] => rfl
  | x :: xs => by rw [catL, segOut, segOut_catL W κ b xs, List.flatMap_cons]

theorem flatMap_single {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

attribute [local irreducible] entryK storeM runPrims

/-! ## Registers -/

/-- The source index. -/ def oU : ℕ := 200
/-- The source base `R`. -/ def oR : ℕ := 201
/-- The word read or emitted. -/ def oX : ℕ := 202
/-- The load address. -/ def oAd : ℕ := 203
/-- Address scratch. -/ def oT1 : ℕ := 204
/-- Address scratch. -/ def oT2 : ℕ := 205
/-- Address scratch. -/ def oT3 : ℕ := 206
/-- Constants. -/ def oK : ℕ := 207
/-- The seed's second word; the compared word. -/ def oY : ℕ := 208
/-- The kind flag (`kite`). -/ def oKF : ℕ := 209
/-- The copy counter. -/ def oCp : ℕ := 210
/-- The copy count. -/ def oNp : ℕ := 211
/-- One comparison. -/ def oB2 : ℕ := 223
/-- A flag (the comparisons' conjunction). -/ def oFl : ℕ := 224
/-- A `rep`'s counter at depth `d`. -/ def oCd (d : ℕ) : ℕ := 226 + 3 * d
/-- A `rep`'s count at depth `d`. -/ def oNd (d : ℕ) : ℕ := 227 + 3 * d
/-- The base at depth `d`. -/ def oBd (d : ℕ) : ℕ := 228 + 3 * d

/-! ## Specification: the address block and the compiled segments -/

/-- An address shape `(m₁, s₃, s₄)` at row shift `st`. -/
structure AP where
  m1 : ℕ
  s3 : ℕ
  s4 : ℕ
  st : ℕ

/-- **The address of source word `x`** from the base `R`, as the machine computes it. -/
def addrW (ap : AP) (R x : Word) : Word :=
  XOp.add.eval (XOp.add.eval (XOp.add.eval R
    (XOp.shl.eval (XOp.and.eval (XOp.shr.eval x (toWord 1)) (toWord ap.m1)) (toWord ap.st)))
    (XOp.shl.eval (XOp.shr.eval x (toWord ap.s3)) (toWord ap.s4))) (XOp.and.eval x 1)

/-- **The source**: word `n` is the heap word at `addrW ap R n`. -/
def src (M : Mem) (ap : AP) (R : ℕ) (n : ℕ) : Word := rd M (addrW ap (toWord R) (toWord n)).toNat

/-- **The contiguous shape**: `addrW apC R n = R + n` (`addrW_apC`, for `R + n < 2^40`). -/
def apC : AP := ⟨1099511627775, 63, 0, 1⟩

/-- The address block: `oAd := addrW ap oR oU`. -/
def ldPs (ap : AP) : List Prim :=
  [.const oK (toWord 1), .op .shr oT1 oU oK, .const oK (toWord ap.m1), .op .and oT1 oT1 oK,
   .const oK (toWord ap.st), .op .shl oT1 oT1 oK, .const oK (toWord ap.s3), .op .shr oT2 oU oK,
   .const oK (toWord ap.s4), .op .shl oT2 oT2 oK, .op .and oT3 oU cOne, .op .add oAd oR oT1,
   .op .add oAd oAd oT2, .op .add oAd oAd oT3]

/-- **One source word**: `oX := M[addrW ap oR oU]`. -/
def ldw (ap : AP) : XIR := .seq (.blk (ldPs ap)) (.load oX oAd)

/-- **A copy** of `n` source words from `rb + o`. -/
def cpIR (ap : AP) (rb o n : ℕ) : XIR :=
  .seq (.blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)])
    (.loopK oCp oNp (toWord n) (.seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne]))))

/-- **One comparison**: source words `rb + oa` and `rb + ob`, their equality and-ed into `oFl`. -/
def cmpW (ap : AP) (rb oa ob : ℕ) : XIR :=
  .seq (.blk [.const oK (toWord oa), .op .add oU rb oK])
    (.seq (ldw ap) (.seq (.blk [.op .or oY oX oX, .const oK (toWord ob), .op .add oU rb oK])
      (.seq (ldw ap) (.blk [.op .eq oB2 oX oY, .op .and oFl oFl oB2]))))

/-- **One sibling chosen by comparison** (`Seg.sibc`) from base register `rb`: the four words
`o + 1 + j` against `o − 4 + j`, then the right half (`o + 5`) if all are equal, else the left
half (`o + 1`). -/
def sibcIR (ap : AP) (rb o : ℕ) : XIR :=
  .seq (.blk [.const oFl 1])
    (.seq (cmpW ap rb (o - 4) (o + 1)) (.seq (cmpW ap rb (o - 3) (o + 2))
      (.seq (cmpW ap rb (o - 2) (o + 3)) (.seq (cmpW ap rb (o - 1) (o + 4))
        (.ite oFl (cpIR ap rb (o + 5) 4) (cpIR ap rb (o + 1) 4))))))

/-- **A compiled segment** at depth `d` (base register `oBd d`). -/
def segIR (ap : AP) : ℕ → Seg → XIR
  | _, .nil => .blk []
  | d, .cat x y => .seq (segIR ap d x) (segIR ap d y)
  | _, .wd x => .seq (.blk [.const oX x]) (.out oX)
  | d, .cp o n => cpIR ap (oBd d) o n
  | d, .rep c s x => .seq (.blk [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)])
      (.loopK (oCd d) (oNd d) (toWord c)
        (.seq (segIR ap (d + 1) x) (.blk [.const oK (toWord s), .op .add (oBd (d + 1)) (oBd (d + 1)) oK])))
  | d, .shw o => .seq (.blk [.const oK (toWord o), .op .add oU (oBd d) oK])
      (.seq (ldw ap) (.seq (.blk [.op .or oY oX oX, .op .add oU oU cOne]) (.seq (ldw ap)
        (.seq (.blk [.const oK (toWord 56), .op .shl oX oX oK, .const oK (toWord 8), .op .shr oY oY oK,
          .op .add oX oY oX])
          (.out oX)))))
  | d, .sh8 o => .seq (.blk [.const oK (toWord o), .op .add oU (oBd d) oK])
      (.seq (ldw ap) (.seq (.blk [.const oK (toWord 8), .op .shr oX oX oK]) (.out oX)))
  | d, .kite x y => .ite oKF (segIR ap d x) (segIR ap d y)
  | d, .sibc o => sibcIR ap (oBd d) o

/-- The `rep` nesting depth. -/
def depthSeg : Seg → ℕ
  | .cat x y | .kite x y => max (depthSeg x) (depthSeg y)
  | .rep _ _ x => depthSeg x + 1
  | _ => 0

/-- The counts fit a word with room (`< 2^32`), and a sibling's entry has a previous answer
(`4 ≤ o`). -/
def okSeg : Seg → Bool
  | .cat x y | .kite x y => okSeg x && okSeg y
  | .rep c _ x => decide (c < 2 ^ 32) && okSeg x
  | .cp _ n => decide (n < 2 ^ 32)
  | .sibc o => decide (4 ≤ o)
  | _ => true

/-- **The machine's context** for a segment: the heap is `M₀`'s, `oR = R`, the kind flag is `κ`. -/
structure Ctx (M₀ : Mem) (R : ℕ) (κ : Bool) (s : St) : Prop where
  inv : Inv s.M
  size : s.M.size = M₀.size
  heap : ∀ y, regs ≤ y → rd s.M y = rd M₀ y
  r : rd s.M oR = toWord R
  k : rd s.M oKF = 0 ↔ κ = false

/-- The registers a segment at depth `d` keeps: `oR`, `oKF`, the outer `rep`s' and its base. -/
def Prot (d r : ℕ) : Prop := r = oR ∨ r = oKF ∨ (226 ≤ r ∧ r < 226 + 3 * d) ∨ r = 228 + 3 * d

/-! ## Specification: cost, size and output bounds -/

/-- **The step bound** of a compiled segment (`cost_segIR`). -/
def segCost : Seg → ℕ
  | .nil => 1
  | .cat x y => segCost x + segCost y + 1
  | .wd _ => 3
  | .cp _ n => 14 + 36 * n
  | .rep c _ x => 12 + c * (segCost x + 7)
  | .shw _ => 79
  | .sh8 _ => 39
  | .kite x y => max (segCost x) (segCost y) + 1
  | .sibc _ => 457

/-- **The compiled size** of a segment (`sizeIR_segIR`). -/
def segSize : Seg → ℕ
  | .nil => 1
  | .cat x y | .kite x y => segSize x + segSize y + 1
  | .wd _ => 3
  | .cp _ _ => 50
  | .rep _ _ x => segSize x + 19
  | .shw _ => 79
  | .sh8 _ => 39
  | .sibc _ => 399

/-- **The output bound** of a compiled segment (`outs_segIR`). -/
def segOuts : Seg → ℕ
  | .nil => 0
  | .cat x y => segOuts x + segOuts y
  | .kite x y => max (segOuts x) (segOuts y)
  | .wd _ | .shw _ | .sh8 _ => 1
  | .cp _ n => n
  | .rep c _ x => c * segOuts x
  | .sibc _ => 4

/-! ## Proof helpers: words (FR's `FRXRead`) -/

theorem shr_toWordSg {a k : ℕ} (ha : a < 2 ^ 64) (hk : k < 64) :
    XOp.shr.eval (toWord a) (toWord k) = toWord (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_ushiftRight, toNat_toWord ha, toNat_toWord (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk, toNat_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) ha),
    Nat.shiftRight_eq_div_pow]

theorem shl_toWordSg {a k : ℕ} (hk : k < 64) (hb : a * 2 ^ k < 2 ^ 64) :
    XOp.shl.eval (toWord a) (toWord k) = toWord (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  have ha : a < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) hb
  rw [BitVec.toNat_shiftLeft, toNat_toWord ha, toNat_toWord (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk, toNat_toWord hb, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hb]

theorem and_one_toWordSg {a : ℕ} (ha : a < 2 ^ 64) :
    XOp.and.eval (toWord a) 1 = toWord (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_and, toNat_toWord ha, show (1 : Word).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, toNat_toWord (by omega)]

theorem and_mask_toWord {a m k : ℕ} (ha : a < 2 ^ 64) (hm : m + 1 = 2 ^ k) (hk : k ≤ 64) :
    XOp.and.eval (toWord a) (toWord m) = toWord (a % 2 ^ k) := by
  have hk' : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hk
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_and, toNat_toWord ha, toNat_toWord (by omega), show m = 2 ^ k - 1 by omega,
    Nat.and_two_pow_sub_one_eq_mod, toNat_toWord (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hk')]

theorem toNat_toWord_le (n : ℕ) : (toWord n).toNat ≤ n := by
  simp only [toWord, BitVec.toNat_ofNat]; exact Nat.mod_le _ _

/-! ## The contiguous shape -/

/-- **`apC` is contiguous**: source word `n` sits at `R + n`. -/
theorem addrW_apC {R n : ℕ} (h : R + n < 2 ^ 40) : addrW apC (toWord R) (toWord n) = toWord (R + n) := by
  have hn : n < 2 ^ 64 := by omega
  have h2 : n / 2 ^ 1 < 2 ^ 64 := by omega
  have h3 : n / 2 ^ 1 % 2 ^ 40 = n / 2 ^ 1 := Nat.mod_eq_of_lt (by omega)
  have h4 : n / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
  simp only [addrW, apC]
  rw [shr_toWordSg hn (by norm_num), and_mask_toWord (k := 40) h2 (by norm_num) (by norm_num), h3,
    shl_toWordSg (by norm_num) (by omega), shr_toWordSg hn (by norm_num), h4,
    shl_toWordSg (by norm_num) (by norm_num), and_one_toWordSg hn, add_toWord, add_toWord, add_toWord]
  congr 1
  omega

/-- **The contiguous source** is the heap from `R`. -/
theorem src_apC (M : Mem) {R n : ℕ} (h : R + n < 2 ^ 40) : src M apC R n = rd M (R + n) := by
  rw [src, addrW_apC h, toNat_toWord (by omega)]

/-- `apC`'s addresses from a heap base `R` stay in the heap. -/
theorem hA_apC {R : ℕ} (h1 : regs ≤ R) (h2 : R < 2 ^ 62) : ∀ x, regs ≤ (addrW apC (toWord R) x).toNat := by
  intro x
  have hR : (toWord R).toNat = R := toNat_toWord (by omega)
  have e1 : (XOp.shl.eval (XOp.and.eval (XOp.shr.eval x (toWord 1)) (toWord apC.m1)) (toWord apC.st)).toNat
      < 2 ^ 41 := by
    simp only [XOp.eval, apC, BitVec.toNat_shiftLeft, BitVec.toNat_and]
    have e : (toWord 1).toNat % 64 = 1 := rfl
    rw [e, Nat.shiftLeft_eq]
    have : ((x >>> 1).toNat &&& (toWord 1099511627775).toNat) ≤ 1099511627775 :=
      le_trans Nat.and_le_right (toNat_toWord_le _)
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  have e2 : (XOp.shl.eval (XOp.shr.eval x (toWord apC.s3)) (toWord apC.s4)).toNat ≤ 1 := by
    simp only [XOp.eval, apC, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
    have e : (toWord 63).toNat % 64 = 63 := rfl
    have e' : (toWord 0).toNat % 64 = 0 := rfl
    rw [e, e', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, pow_zero, Nat.mul_one]
    have := x.isLt
    exact le_trans (Nat.mod_le _ _) (by omega)
  have e3 : (XOp.and.eval x 1).toNat ≤ 1 := by
    simp only [XOp.eval, BitVec.toNat_and]
    exact Nat.and_le_right
  simp only [addrW]
  generalize XOp.shl.eval (XOp.and.eval (XOp.shr.eval x (toWord 1)) (toWord apC.m1)) (toWord apC.st) = A at e1
  generalize XOp.shl.eval (XOp.shr.eval x (toWord apC.s3)) (toWord apC.s4) = B at e2
  generalize XOp.and.eval x 1 = C at e3
  simp only [XOp.eval, BitVec.toNat_add, hR]
  simp only [regs] at h1 ⊢
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## Proof helpers: what the code writes -/

/-- The cells a program names as destinations, as a list. -/
def wrL : XIR → List ℕ
  | .blk ps => ps.map Prim.dst
  | .load d _ | .input d _ => [d]
  | .store .. => [cTmp]
  | .out _ => []
  | .seq p q | .ite _ p q => wrL p ++ wrL q
  | .loopK c _ _ b => c :: cTmp :: wrL b
  | .loopT c _ _ b => c :: wrL b

theorem writes_wrL : ∀ (P : XIR) (r : ℕ), Writes P r → r ∈ wrL P
  | .blk ps, r, ⟨p, hp, he⟩ => List.mem_map.2 ⟨p, hp, he⟩
  | .load _ _, _, h | .input _ _, _, h | .store _ _, _, h => List.mem_singleton.2 h
  | .out _, _, h => h.elim
  | .seq p q, r, h | .ite _ p q, r, h => List.mem_append.2 (h.imp (writes_wrL p r) (writes_wrL q r))
  | .loopK c _ _ b, r, h => by
    rcases h with rfl | rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (writes_wrL b r h))
  | .loopT c _ _ b, r, h => by
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (writes_wrL b r h)

/-- Leaf code writes only leaf registers (and the compiler's `cTmp`). -/
def LW (r : ℕ) : Prop := r = cTmp ∨ (200 ≤ r ∧ r ≤ 224 ∧ r ≠ 201 ∧ r ≠ 209)

/-- The registers a segment at depth `d` may write: the leaf registers, and the `rep` registers
from depth `d` on. -/
def OW (d r : ℕ) : Prop :=
  LW r ∨ ∃ e, d ≤ e ∧ (r = 226 + 3 * e ∨ r = 227 + 3 * e ∨ r = 231 + 3 * e)

theorem lw_cpIR (ap : AP) (rb o n r : ℕ) (h : Writes (cpIR ap rb o n) r) : LW r := by
  have := writes_wrL _ _ h
  simp only [cpIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
    List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at this
  simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oNp, oCp, cTmp] at this ⊢; omega

theorem lw_cmpW (ap : AP) (rb oa ob r : ℕ) (h : Writes (cmpW ap rb oa ob) r) : LW r := by
  have := writes_wrL _ _ h
  simp only [cmpW, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
    List.nil_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_append] at this
  simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oY, oB2, oFl, cTmp] at this ⊢; omega

theorem lw_sibcIR (ap : AP) (rb o r : ℕ) (h : Writes (sibcIR ap rb o) r) : LW r := by
  rcases h with ⟨p, hp, rfl⟩ | h | h | h | h | h | h
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    subst hp; simp [LW, Prim.dst, oFl]
  all_goals first | exact lw_cmpW _ _ _ _ _ h | exact lw_cpIR _ _ _ _ _ h

theorem ow_segIR (ap : AP) : ∀ (seg : Seg) (d r : ℕ), Writes (segIR ap d seg) r → OW d r
  | .nil, _, _, h => by simp [segIR, Writes] at h
  | .cat x y, d, r, h => h.elim (ow_segIR ap x d r) (ow_segIR ap y d r)
  | .kite x y, d, r, h => h.elim (ow_segIR ap x d r) (ow_segIR ap y d r)
  | .wd _, _, r, h => by
    simp [segIR, Writes, Prim.dst] at h; exact .inl (.inr (by simp only [oX] at *; omega))
  | .cp o n, d, r, h => .inl (lw_cpIR ap _ o n r h)
  | .sibc o, d, r, h => .inl (lw_sibcIR ap _ o r h)
  | .shw o, d, r, h => by
    have := writes_wrL _ _ h
    simp only [segIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, List.mem_append] at this
    left; simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, oY, cTmp] at *; omega
  | .sh8 o, d, r, h => by
    have := writes_wrL _ _ h
    simp only [segIR, ldw, ldPs, wrL, List.map_cons, List.map_nil, Prim.dst, List.cons_append,
      List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, List.mem_append] at this
    left; simp only [LW, oK, oT1, oT2, oT3, oAd, oX, oU, cTmp] at *; omega
  | .rep c s x, d, r, h => by
    simp only [segIR, Writes, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with ⟨p, hp, rfl⟩ | rfl | rfl | h | ⟨p, hp, rfl⟩
    · rcases hp with rfl | rfl
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oBd]; omega⟩
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oNd]⟩
    · exact .inr ⟨d, le_rfl, by simp [oCd]⟩
    · exact .inl (.inl rfl)
    · rcases ow_segIR ap x (d + 1) r h with h | ⟨e, he, h⟩
      · exact .inl h
      · exact .inr ⟨e, by omega, h⟩
    · rcases hp with rfl | rfl
      · exact .inl (.inr (by simp [Prim.dst, oK]))
      · exact .inr ⟨d, le_rfl, by simp [Prim.dst, oBd]; omega⟩

theorem not_ow_prot {d r : ℕ} (hp : Prot d r) (hw : OW d r) : False := by
  simp only [Prot, OW, LW, oR, oKF, cTmp] at hp hw
  rcases hw with h | ⟨e, he, h⟩ <;> omega

/-- **A segment keeps its protected registers.** -/
theorem noW_segIR (ap : AP) (seg : Seg) (d r : ℕ) (hp : Prot d r) : ¬ Writes (segIR ap d seg) r :=
  fun h => not_ow_prot hp (ow_segIR ap seg d r h)

/-- **A segment keeps every register below `200`** but `cTmp`. -/
theorem noW_lo (ap : AP) (sg : Seg) (d : ℕ) {r : ℕ} (hr : r < 200) (hc : r ≠ cTmp) : ¬ Writes (segIR ap d sg) r :=
  fun h => by
    rcases ow_segIR ap sg d r h with h1 | ⟨e, -, h2⟩
    · rcases h1 with h1 | h1
      · exact hc h1
      · omega
    · omega

/-! ## Proof helpers: heap frames of store-free code (FR's `FRXRead`) -/

/-- No store, no tape-length loop, register destinations; `loopK` counters registers. -/
def LoKSg : XIR → Prop
  | .blk ps => ∀ p ∈ ps, p.dst < regs
  | .load d _ => d < regs
  | .input d _ => d < regs
  | .out _ => True
  | .seq p q => LoKSg p ∧ LoKSg q
  | .ite _ p q => LoKSg p ∧ LoKSg q
  | .loopK c _ _ b => c < regs ∧ LoKSg b
  | _ => False

theorem iterL_hframeSg {f : St → St} {c : ℕ} (hc : c < regs)
    (hf : ∀ s, ∀ x, regs ≤ x → rd (f s).M x = rd s.M x) :
    ∀ k s, ∀ x, regs ≤ x → rd (iterL f c k s).M x = rd s.M x
  | 0, _, _, _ => rfl
  | k + 1, s, x, hx => (iterL_hframeSg hc hf k _ x hx).trans
      ((rd_decS (by omega) _).trans (hf s x hx))

/-- **Heap frame** for `LoKSg` code. -/
theorem hframeKSg (I : Array Word) : ∀ (P : XIR) (s : St), LoKSg P → ∀ x, regs ≤ x →
    rd (semXIR I P s).M x = rd s.M x
  | .blk _, _, h, _, hx => rd_runPrims_of_not_writes (fun p hp he => by have := h p hp; omega) _
  | .load _ _, _, h, _, hx => rd_set_ne (by simp only [LoKSg] at h; omega)
  | .input _ _, _, h, _, hx => rd_set_ne (by simp only [LoKSg] at h; omega)
  | .out _, _, _, _, _ => rfl
  | .seq p q, s, h, x, hx => (hframeKSg I q _ h.2 x hx).trans (hframeKSg I p s h.1 x hx)
  | .ite _ p q, s, h, x, hx => by
    simp only [semXIR]; split
    · exact hframeKSg I q s h.2 x hx
    · exact hframeKSg I p s h.1 x hx
  | .loopK c n K b, s, h, x, hx => by
    simp only [semXIR]
    rw [iterL_hframeSg h.1 (fun s' x' hx' => hframeKSg I b s' h.2 x' hx') _ _ x hx]
    exact entryK_frame _ (by have := h.1; omega) (by simp only [cTmp, regs] at *; omega)
  | .store .., _, h, _, _ => h.elim
  | .loopT .., _, h, _, _ => h.elim

/-- The count of a `loopK` whose count register holds `K`. -/
theorem entryK_countSg {c n : ℕ} {K : Word} {M : Mem} (hM : Inv M) (hc : 4 < c) (hcr : c < regs)
    (hn : n ≠ c) (hN : rd M n = K) : rd (entryK c n K M) c = K := by
  have hs := hM.1
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds c K) n = K := by rw [rd_set_ne (Ne.symm hn), hN]
  have h2 : rd (M.setIfInBounds c K) c = K := rd_set_self (by simp only [regs] at *; omega)
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp, regs] at *; omega)]
  have : XOp.ltu.eval K K = 0 := by simp [XOp.eval]
  rw [this, if_pos rfl, rd_set_ne (by simp only [cTmp]; omega), h2]

theorem inv_entryKSg {c n : ℕ} {K : Word} {M : Mem} (hM : Inv M) (hc : 4 < c) :
    Inv (entryK c n K M) :=
  inv_of_frame hM (size_entryK ..) fun i hi =>
    entryK_frame _ (by omega) (by simp only [cTmp]; omega)

theorem inv_decSSg {c : ℕ} {s : St} (hM : Inv s.M) (hc : 4 ≤ c) : Inv (decS c s).M :=
  inv_of_frame hM (size_decS ..) fun i hi => rd_decS (by omega) _

/-! ## Proof helpers: well formed, no store, the context -/

theorem wf_ldw (ap : AP) : WF (ldw ap) := by
  simp +decide only [ldw, ldPs, WF, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem wf_cpIR (ap : AP) (rb o n : ℕ) : WF (cpIR ap rb o n) := by
  refine ⟨by simp +decide only [WF, Prim.dst, oK, oU, oNp, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], ⟨by simp [oCp, oNp, cTmp], by simp [oCp, regs], fun h => ?_,
    wf_ldw ap, trivial, by simp +decide only [WF, Prim.dst, oU]⟩⟩
  have := writes_wrL _ _ h
  simp [wrL, ldw, ldPs, Prim.dst, oCp, oK, oT1, oT2, oT3, oAd, oX, oU] at this

theorem wf_cmpW (ap : AP) (rb oa ob : ℕ) : WF (cmpW ap rb oa ob) :=
  ⟨by simp +decide only [WF, Prim.dst, oK, oU, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false, and_true], wf_ldw ap,
   by simp +decide only [WF, Prim.dst, oY, oK, oU, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false, and_true], wf_ldw ap,
   by simp +decide only [WF, Prim.dst, oB2, oFl, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false, and_true]⟩

theorem wf_sibcIR (ap : AP) (rb o : ℕ) : WF (sibcIR ap rb o) :=
  ⟨by simp +decide only [WF, Prim.dst, oFl, List.mem_cons, List.mem_nil_iff, forall_eq_or_imp,
    forall_eq, or_false], wf_cmpW .., wf_cmpW .., wf_cmpW .., wf_cmpW .., wf_cpIR .., wf_cpIR ..⟩

theorem wf_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), depthSeg seg + d ≤ 9 → WF (segIR ap d seg)
  | .nil, _, _ => by simp +decide only [segIR, WF]
  | .cat x y, d, h => ⟨wf_segIR ap x d (by simp [depthSeg] at h; omega),
      wf_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .kite x y, d, h => ⟨wf_segIR ap x d (by simp [depthSeg] at h; omega),
      wf_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .wd _, _, _ => by simp +decide only [segIR, WF, Prim.dst, oX, List.mem_cons, List.mem_nil_iff,
    forall_eq, or_false, and_true]
  | .cp .., _, _ => wf_cpIR ..
  | .sibc .., _, _ => wf_sibcIR ..
  | .shw _, _, _ => ⟨by simp +decide only [WF, Prim.dst, oK, oU, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], wf_ldw ap, by simp +decide only [
    WF, Prim.dst, oY, oU], wf_ldw ap,
      by simp +decide only [WF, Prim.dst, oK, oX, oY], trivial⟩
  | .sh8 _, _, _ => ⟨by simp +decide only [WF, Prim.dst, oK, oU, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], wf_ldw ap, by simp +decide only [
    WF, Prim.dst, oK, oX], trivial⟩
  | .rep c s x, d, h => by
    simp only [depthSeg] at h
    refine ⟨by simp +decide only [WF, Prim.dst, oBd, oNd, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false]; omega, ⟨by simp [oCd, oNd, cTmp]; omega,
      by simp [oCd, regs]; omega, fun hw => ?_, wf_segIR ap x (d + 1) (by omega),
      by simp [WF, Prim.dst, oK, oBd]; omega⟩⟩
    rcases hw with hw | ⟨p, hp, he⟩
    · exact noW_segIR ap x (d + 1) _ (.inr (.inr (.inl ⟨by simp only [oCd]; omega, by simp only [oCd]; omega⟩))) hw
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> simp [Prim.dst, oK, oCd, oBd] at he
      all_goals omega

theorem loK_ldw (ap : AP) : LoKSg (ldw ap) := by
  simp +decide only [ldw, ldPs, LoKSg, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, regs, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true]

theorem loK_cpIR (ap : AP) (rb o n : ℕ) : LoKSg (cpIR ap rb o n) :=
  ⟨by simp +decide only [LoKSg, Prim.dst, oK, oU, oNp, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], by simp [oCp, regs], loK_ldw ap, trivial,
    by simp +decide only [LoKSg, Prim.dst, oU, regs]⟩

theorem loK_cmpW (ap : AP) (rb oa ob : ℕ) : LoKSg (cmpW ap rb oa ob) :=
  ⟨by simp +decide only [LoKSg, Prim.dst, oK, oU, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], loK_ldw ap,
   by simp +decide only [LoKSg, Prim.dst, oY, oK, oU, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true], loK_ldw ap,
   by simp +decide only [LoKSg, Prim.dst, oB2, oFl, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false, and_true]⟩

theorem loK_sibcIR (ap : AP) (rb o : ℕ) : LoKSg (sibcIR ap rb o) :=
  ⟨by simp +decide only [LoKSg, Prim.dst, oFl, regs, List.mem_cons, List.mem_nil_iff,
    forall_eq_or_imp, forall_eq, or_false], loK_cmpW .., loK_cmpW .., loK_cmpW .., loK_cmpW ..,
    loK_cpIR .., loK_cpIR ..⟩

theorem loK_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), depthSeg seg + d ≤ 9 → LoKSg (segIR ap d seg)
  | .nil, _, _ => by simp +decide only [segIR, LoKSg]
  | .cat x y, d, h => ⟨loK_segIR ap x d (by simp [depthSeg] at h; omega),
      loK_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .kite x y, d, h => ⟨loK_segIR ap x d (by simp [depthSeg] at h; omega),
      loK_segIR ap y d (by simp [depthSeg] at h; omega)⟩
  | .wd _, _, _ => by simp +decide only [segIR, LoKSg, Prim.dst, oX, regs, List.mem_cons,
    List.mem_nil_iff, forall_eq, or_false, and_true]
  | .cp .., _, _ => loK_cpIR ..
  | .sibc .., _, _ => loK_sibcIR ..
  | .shw _, _, _ => ⟨by simp +decide only [LoKSg, Prim.dst, oK, oU, regs, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true], loK_ldw ap, by simp +decide only [LoKSg, Prim.dst, oY, oU, regs],
      loK_ldw ap, by simp +decide only [LoKSg, Prim.dst, oK, oX, oY, regs], trivial⟩
  | .sh8 _, _, _ => ⟨by simp +decide only [LoKSg, Prim.dst, oK, oU, regs, List.mem_cons,
    List.mem_nil_iff, forall_eq_or_imp, forall_eq, or_false, and_true], loK_ldw ap, by simp +decide only [LoKSg, Prim.dst, oK, oX, regs],
      trivial⟩
  | .rep c s x, d, h => by
    simp only [depthSeg] at h
    exact ⟨by simp +decide only [LoKSg, Prim.dst, oBd, oNd, regs, List.mem_cons, List.mem_nil_iff,
      forall_eq_or_imp, forall_eq, or_false]; omega, by simp [oCd, regs]; omega,
      loK_segIR ap x (d + 1) (by omega), by simp [LoKSg, Prim.dst, oK, oBd, regs]; omega⟩

theorem noLoopT_cpIR (ap : AP) (rb o n : ℕ) : NoLoopT (cpIR ap rb o n) := by
  simp [cpIR, ldw, NoLoopT]

theorem noLoopT_sibcIR (ap : AP) (rb o : ℕ) : NoLoopT (sibcIR ap rb o) := by
  simp [sibcIR, cmpW, cpIR, ldw, NoLoopT]

theorem noLoopT_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), NoLoopT (segIR ap d seg)
  | .nil, _ | .wd _, _ | .shw _, _ | .sh8 _, _ => by simp [segIR, ldw, NoLoopT]
  | .cat x y, d | .kite x y, d => ⟨noLoopT_segIR ap x d, noLoopT_segIR ap y d⟩
  | .cp .., _ => noLoopT_cpIR ..
  | .sibc .., _ => noLoopT_sibcIR ..
  | .rep c s x, d => ⟨trivial, noLoopT_segIR ap x (d + 1), trivial⟩

theorem ctx_sem {M₀ : Mem} {R : ℕ} {κ : Bool} (I : Array Word) {P : XIR} (hL : LoKSg P) (hw : WF P)
    (h1 : ¬ Writes P oR) (h2 : ¬ Writes P oKF) {s : St} (hc : Ctx M₀ R κ s) : Ctx M₀ R κ (semXIR I P s) where
  inv := inv_sem I hw hc.inv
  size := (size_sem I P s).trans hc.size
  heap y hy := (hframeKSg I P s hL y hy).trans (hc.heap y hy)
  r := (frame I P s hw hc.inv oR (by simp [oR, regs]) h1).trans hc.r
  k := by rw [frame I P s hw hc.inv oKF (by simp [oKF, regs]) h2]; exact hc.k

/-- **A segment keeps the context.** -/
theorem ctx_segIR {M₀ : Mem} {R : ℕ} {κ : Bool} (I : Array Word) (ap : AP) (seg : Seg) (d : ℕ)
    (hd : depthSeg seg + d ≤ 9) {s : St} (hc : Ctx M₀ R κ s) : Ctx M₀ R κ (semXIR I (segIR ap d seg) s) :=
  ctx_sem I (loK_segIR ap seg d hd) (wf_segIR ap seg d hd) (noW_segIR ap seg d _ (.inl rfl))
    (noW_segIR ap seg d _ (.inr (.inl rfl))) hc

/-! ## Proof helpers: loops that emit -/

theorem iterL_emit (I : Array Word) {b : XIR} {c K : ℕ} (Q : ℕ → St → Prop) (out : ℕ → List Word)
    (hf : ∀ j s, j < K → Q j s → (semXIR I b s).o.toList = s.o.toList ++ out j ∧
      Q (j + 1) (decS c (semXIR I b s))) :
    ∀ m j s, j + m ≤ K → Q j s → (iterL (semXIR I b) c m s).o.toList =
      s.o.toList ++ (List.range m).flatMap (fun i => out (j + i)) ∧ Q (j + m) (iterL (semXIR I b) c m s)
  | 0, j, s, _, h => ⟨by simp only [iterL, List.range_zero, List.flatMap_nil, List.append_nil], h⟩
  | m + 1, j, s, hm, h => by
    obtain ⟨h1, h2⟩ := hf j s (by omega) h
    obtain ⟨g1, g2⟩ := iterL_emit I Q out hf m (j + 1) _ (by omega) h2
    refine ⟨?_, by rw [show j + (m + 1) = j + 1 + m by omega]; exact g2⟩
    rw [iterL, g1, show (decS c (semXIR I b s)).o = (semXIR I b s).o from rfl, h1, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map, List.append_assoc, Nat.add_zero]
    simp only [Nat.add_assoc, Nat.add_comm 1, Nat.succ_eq_add_one, Nat.add_zero]

/-- **A counted loop that emits** `out j` in iteration `j`, under an invariant `Q`. -/
theorem loopK_emit (I : Array Word) {c n K : ℕ} {b : XIR} (Q : ℕ → St → Prop) (out : ℕ → List Word)
    (s : St) (hM : Inv s.M) (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hK : K < 2 ^ 64)
    (hN : rd s.M n = toWord K) (h0 : Q 0 ⟨entryK c n (toWord K) s.M, s.o⟩)
    (hf : ∀ j s, j < K → Q j s → (semXIR I b s).o.toList = s.o.toList ++ out j ∧
      Q (j + 1) (decS c (semXIR I b s))) :
    (semXIR I (.loopK c n (toWord K) b) s).o.toList = s.o.toList ++ (List.range K).flatMap out ∧
      Q K (semXIR I (.loopK c n (toWord K) b) s) := by
  have e : (rd (entryK c n (toWord K) s.M) c).toNat = K := by
    rw [entryK_countSg hM hc hcr hn hN, toNat_toWord hK]
  have := iterL_emit I Q out hf K 0 _ (by omega) h0
  simp only [Nat.zero_add] at this
  have e2 : semXIR I (.loopK c n (toWord K) b) s =
      iterL (semXIR I b) c K ⟨entryK c n (toWord K) s.M, s.o⟩ := by
    simp only [semXIR]; rw [e]
  rw [e2]; exact this

theorem ctx_decS {M₀ : Mem} {R : ℕ} {κ : Bool} {c : ℕ} (hc4 : 4 ≤ c) (hc : c < regs) (h1 : c ≠ oR)
    (h2 : c ≠ oKF) {s : St} (h : Ctx M₀ R κ s) : Ctx M₀ R κ (decS c s) where
  inv := inv_decSSg h.inv hc4
  size := (size_decS c s).trans h.size
  heap y hy := (rd_decS (by omega) s).trans (h.heap y hy)
  r := (rd_decS h1 s).trans h.r
  k := by rw [rd_decS h2]; exact h.k

theorem ctx_entryK {M₀ : Mem} {R : ℕ} {κ : Bool} {c n : ℕ} {K : Word} (hc4 : 4 < c) (hc : c < regs)
    (h1 : c ≠ oR) (h2 : c ≠ oKF) {s : St} (h : Ctx M₀ R κ s) : Ctx M₀ R κ ⟨entryK c n K s.M, s.o⟩ where
  inv := inv_entryKSg h.inv hc4
  size := (size_entryK ..).trans h.size
  heap y hy := (entryK_frame _ (by omega) (by simp only [cTmp, regs] at *; omega)).trans (h.heap y hy)
  r := (entryK_frame _ h1 (by simp [cTmp, oR])).trans h.r
  k := by rw [show rd (entryK c n K s.M) oKF = rd s.M oKF from entryK_frame _ h2 (by simp [cTmp, oKF])]; exact h.k

/-! ## Proof helpers: one source word -/

theorem one_cOne {M : Mem} (h : Inv M) : rd M cOne = 1 := h.2 0 (by decide)

/-- **The address block reads the source word** at `addrW ap rR rU`. -/
theorem ldw_sem (I : Array Word) (ap : AP) (s : St) (hM : Inv s.M)
    (hA : regs ≤ (addrW ap (rd s.M oR) (rd s.M oU)).toNat) :
    rd (semXIR I (ldw ap) s).M oX = rd s.M (addrW ap (rd s.M oR) (rd s.M oU)).toNat ∧
      (semXIR I (ldw ap) s).o = s.o := by
  have hs := hM.1
  have h1 := one_cOne hM
  simp only [regs] at hs hA
  have hv : rd (runPrims (ldPs ap) s.M) oAd = addrW ap (rd s.M oR) (rd s.M oU) := by
    simp only [ldPs, runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oT1, oT2, oT3, oAd, oX, oU, oR, cOne]; omega))
      only [rd_set_self, rd_set_ne, h1]
    simp only [addrW]
  have hh : ∀ a, regs ≤ a → rd (runPrims (ldPs ap) s.M) a = rd s.M a := fun a ha =>
    rd_runPrims_of_not_writes (fun p hp he => by
      simp only [ldPs, List.mem_cons, List.mem_nil_iff, or_false] at hp
      simp only [regs] at ha
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Prim.dst, oK, oT1, oT2, oT3, oAd] at he <;> omega) _
  constructor
  · simp only [ldw, semXIR]
    rw [rd_set_self (by rw [size_runPrims]; simp only [oX]; omega), hv, hh _ (by simp only [regs]; omega)]
  · simp only [ldw, semXIR]

theorem nw_of {P : XIR} {i : ℕ} (h : i ∉ wrL P) : ¬ Writes P i := fun hw => h (writes_wrL P i hw)

theorem loK_blk {ps : List Prim} (h : ∀ p ∈ ps, p.dst < regs) : LoKSg (.blk ps) := h

theorem wf_blk' {ps : List Prim} (h : ∀ p ∈ ps, 4 ≤ p.dst) : WF (.blk ps) := h

/-- The source word at the address of a register value. -/
theorem ldw_src (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s) {u : ℕ}
    (hu : rd s.M oU = toWord u) :
    rd (semXIR I (ldw ap) s).M oX = src M₀ ap R u ∧ (semXIR I (ldw ap) s).o = s.o := by
  have hA' : regs ≤ (addrW ap (rd s.M oR) (rd s.M oU)).toNat := by rw [hc.r, hu]; exact hA _
  obtain ⟨h1, h2⟩ := ldw_sem I ap s hc.inv hA'
  refine ⟨?_, h2⟩
  rw [h1, hc.heap _ hA', hc.r, hu]; rfl

theorem ctx_ldw (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool} {s : St} (hc : Ctx M₀ R κ s) :
    Ctx M₀ R κ (semXIR I (ldw ap) s) :=
  ctx_sem I (loK_ldw ap) (wf_ldw ap) (nw_of (by simp [wrL, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oR]))
    (nw_of (by simp [wrL, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oKF])) hc

theorem ldw_keep (I : Array Word) (ap : AP) (s : St) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (h : r ∉ [oK, oT1, oT2, oT3, oAd, oX]) : rd (semXIR I (ldw ap) s).M r = rd s.M r :=
  frame I _ s (wf_ldw ap) hM r hr (nw_of (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
    simp [wrL, ldw, ldPs, Prim.dst, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, eq_comm]))

/-- **The copy loop** emits `n` source words from `b + o` (`b` in `rb`). -/
theorem cpIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) {rb o n b : ℕ} (hrb : rb ≠ oK) (hn : n < 2 ^ 64)
    (s : St) (hc : Ctx M₀ R κ s) (hb : rd s.M rb = toWord b) :
    (semXIR I (cpIR ap rb o n) s).o.toList =
      s.o.toList ++ (List.range n).map (fun j => src M₀ ap R (b + o + j)) := by
  have hs := hc.inv.1
  simp only [regs] at hs
  have hb1 : semXIR I (.blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)]) s =
      ⟨runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M, s.o⟩ := rfl
  have r1 : rd (runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M) oU =
      toWord (b + o) := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oNp] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [hb, add_toWord]
  have r2 : rd (runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M) oNp =
      toWord n := by
    simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oK, oU, oNp] at *; omega)) only [rd_set_self]
  have c1 := ctx_sem (M₀ := M₀) I (P := .blk [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)])
    (loK_blk (by simp [Prim.dst, oK, oU, oNp, regs])) (wf_blk' (by simp [Prim.dst, oK, oU, oNp]))
    (nw_of (by simp [wrL, Prim.dst, oK, oU, oNp, oR])) (nw_of (by simp [wrL, Prim.dst, oK, oU, oNp, oKF])) hc
  rw [hb1] at c1
  rw [show semXIR I (cpIR ap rb o n) s = semXIR I (.loopK oCp oNp (toWord n)
      (.seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne]))))
      ⟨runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M, s.o⟩ from rfl]
  generalize runPrims [.const oK (toWord o), .op .add oU rb oK, .const oNp (toWord n)] s.M = M1 at r1 r2 c1 ⊢
  have := loopK_emit I (c := oCp) (n := oNp) (K := n)
    (b := .seq (ldw ap) (.seq (.out oX) (.blk [.op .add oU oU cOne])))
    (fun j s' => Ctx M₀ R κ s' ∧ rd s'.M oU = toWord (b + o + j)) (fun j => [src M₀ ap R (b + o + j)])
    ⟨M1, s.o⟩ c1.inv (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oNp]) hn r2
    ⟨ctx_entryK (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oR]) (by simp [oCp, oKF]) c1,
      by rw [entryK_frame _ (by simp [oCp, oU]) (by simp [oU, cTmp])]; exact r1⟩
    (fun j s' _ ⟨q1, q2⟩ => by
      obtain ⟨l1, l2⟩ := ldw_src I ap hA s' q1 q2
      have k2 := ctx_ldw I ap (s := s') q1
      have u2 := ldw_keep I ap s' q1.inv (r := oU) (by simp [oU, regs]) (by simp [oU, oK, oT1, oT2, oT3, oAd, oX])
      simp only [semXIR_seq]
      generalize semXIR I (ldw ap) s' = s2 at l1 l2 k2 u2 ⊢
      have hs2 := k2.inv.1
      simp only [regs] at hs2
      refine ⟨by simp [semXIR, l2, l1], ⟨ctx_decS (by simp [oCp]) (by simp [oCp, regs]) (by simp [oCp, oR])
        (by simp [oCp, oKF]) ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
      · exact inv_runPrims (by simp [Prim.dst, oU]) k2.inv
      · simp [semXIR, k2.size]
      · intro y hy
        simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp only [regs, oU] at *; omega)]; exact k2.heap y hy
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp [oU, oR])]; exact k2.r
      · simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_ne (by simp [oU, oKF])]; exact k2.k
      · rw [rd_decS (by simp [oCp, oU])]
        simp only [semXIR, runPrims, List.foldl, Prim.run]
        rw [rd_set_self (by simp only [oU]; omega), u2, q2, one_cOne k2.inv, add_one_toWord, Nat.add_assoc])
  rw [this.1, flatMap_single]

theorem ctx_blk {M₀ : Mem} {R : ℕ} {κ : Bool} {ps : List Prim}
    (h : ∀ p ∈ ps, 4 ≤ p.dst ∧ p.dst < regs ∧ p.dst ≠ oR ∧ p.dst ≠ oKF) {s : St} (hc : Ctx M₀ R κ s) :
    Ctx M₀ R κ ⟨runPrims ps s.M, s.o⟩ :=
  ctx_sem (P := .blk ps) #[] (fun p hp => (h p hp).2.1) (fun p hp => (h p hp).1)
    (fun ⟨p, hp, he⟩ => (h p hp).2.2.1 he) (fun ⟨p, hp, he⟩ => (h p hp).2.2.2 he) hc

theorem semXIR_blk (I : Array Word) (ps : List Prim) (s : St) : semXIR I (.blk ps) s = ⟨runPrims ps s.M, s.o⟩ :=
  rfl

theorem shr_c (x : Word) (k : ℕ) (hk : k < 64) : XOp.shr.eval x (toWord k) = x >>> k := by
  simp only [XOp.eval]; congr 1; rw [toNat_toWord (by omega), Nat.mod_eq_of_lt hk]

theorem shl_c (x : Word) (k : ℕ) (hk : k < 64) : XOp.shl.eval x (toWord k) = x <<< k := by
  simp only [XOp.eval]; congr 1; rw [toNat_toWord (by omega), Nat.mod_eq_of_lt hk]

theorem keep_of (I : Array Word) {P : XIR} {s : St} (hw : WF P) (hM : Inv s.M) {r : ℕ} (hr : r < regs)
    (h : r ∉ wrL P) : rd (semXIR I P s).M r = rd s.M r :=
  frame I P s hw hM r hr (nw_of h)

/-! ## Proof helpers: the sibling by comparison -/

/-- **One comparison** and-s `src (b + ob) = src (b + oa)` into `oFl` and keeps the context, the
output and the base register. -/
theorem cmpW_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s) {rb b oa ob : ℕ}
    (hrb : 224 < rb) (hrr : rb < regs) (hb : rd s.M rb = toWord b) :
    Ctx M₀ R κ (semXIR I (cmpW ap rb oa ob) s) ∧ (semXIR I (cmpW ap rb oa ob) s).o = s.o ∧
      rd (semXIR I (cmpW ap rb oa ob) s).M rb = toWord b ∧
      rd (semXIR I (cmpW ap rb oa ob) s).M oFl =
        XOp.and.eval (rd s.M oFl) (XOp.eq.eval (src M₀ ap R (b + ob)) (src M₀ ap R (b + oa))) := by
  have hs := hc.inv.1
  simp only [regs] at hs hrr
  have cW := ctx_sem I (loK_cmpW ap rb oa ob) (wf_cmpW ap rb oa ob)
    (nw_of (by simp [wrL, cmpW, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oU, oY, oB2, oFl, oR]))
    (nw_of (by simp [wrL, cmpW, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oU, oY, oB2, oFl, oKF])) hc
  have bW : rd (semXIR I (cmpW ap rb oa ob) s).M rb = toWord b := by
    rw [keep_of I (wf_cmpW ap rb oa ob) hc.inv (by simp only [regs]; omega) (by
      simp only [wrL, cmpW, ldw, ldPs, Prim.dst, oK, oT1, oT2, oT3, oAd, oX, oU, oY, oB2, oFl, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff,
        or_false]; omega)]
    exact hb
  refine ⟨cW, ?_, bW, ?_⟩ <;> clear cW bW <;> simp only [cmpW, semXIR_seq, semXIR_blk]
  all_goals
    have c1 := ctx_blk (ps := [.const oK (toWord oa), .op .add oU rb oK]) (by simp [Prim.dst, oK, oU, oR, oKF, regs]) hc
    have u1 : rd (runPrims [.const oK (toWord oa), .op .add oU rb oK] s.M) oU = toWord (b + oa) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oK, oU] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [hb, add_toWord]
    have w1 : ∀ p ∈ [Prim.const oK (toWord oa), .op .add oU rb oK], p.dst ≠ rb := by
      simp [Prim.dst, oK, oU]; omega
    have b1 : rd (runPrims [.const oK (toWord oa), .op .add oU rb oK] s.M) rb = toWord b := by
      rw [rd_runPrims_of_not_writes w1]; exact hb
    have f1 : rd (runPrims [.const oK (toWord oa), .op .add oU rb oK] s.M) oFl = rd s.M oFl :=
      rd_runPrims_of_not_writes (by simp [Prim.dst, oK, oU, oFl]) _
    obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
    have c2 := ctx_ldw I ap c1
    have w2 : rb ∉ [oK, oT1, oT2, oT3, oAd, oX] := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, oK, oT1, oT2, oT3, oAd, oX]; omega
    have b2 := ldw_keep I ap _ c1.inv (r := rb) (by simp only [regs]; omega) w2
    have f2 := ldw_keep I ap _ c1.inv (r := oFl) (by simp [oFl, regs]) (by simp [oFl, oK, oT1, oT2, oT3, oAd, oX])
    generalize semXIR I (ldw ap) ⟨runPrims [.const oK (toWord oa), .op .add oU rb oK] s.M, s.o⟩ = s2 at l1 l2 c2 b2 f2
    rw [b1] at b2; rw [f1] at f2
    have hs2 := c2.inv.1
    simp only [regs] at hs2
    have c3 := ctx_blk (ps := [.op .or oY oX oX, .const oK (toWord ob), .op .add oU rb oK])
      (by simp [Prim.dst, oY, oK, oU, oR, oKF, regs]) c2
    have u3 : rd (runPrims [.op .or oY oX oX, .const oK (toWord ob), .op .add oU rb oK] s2.M) oU =
        toWord (b + ob) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, oU, oX, oK] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [b2, add_toWord]
    have y3 : rd (runPrims [.op .or oY oX oX, .const oK (toWord ob), .op .add oU rb oK] s2.M) oY =
        src M₀ ap R (b + oa) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, oU, oX, oK] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [l1, or_self_eval]
    have f3 : rd (runPrims [.op .or oY oX oX, .const oK (toWord ob), .op .add oU rb oK] s2.M) oFl =
        rd s.M oFl := by
      rw [rd_runPrims_of_not_writes (by simp [Prim.dst, oY, oK, oU, oFl])]; exact f2
    obtain ⟨l4, l5⟩ := ldw_src I ap hA _ c3 u3
    have y4 := ldw_keep I ap _ c3.inv (r := oY) (by simp [oY, regs]) (by simp [oY, oK, oT1, oT2, oT3, oAd, oX])
    have f4 := ldw_keep I ap _ c3.inv (r := oFl) (by simp [oFl, regs]) (by simp [oFl, oK, oT1, oT2, oT3, oAd, oX])
    generalize h4 : semXIR I (ldw ap) ⟨runPrims [.op .or oY oX oX, .const oK (toWord ob), .op .add oU rb oK] s2.M, s2.o⟩ = s4 at l4 l5 y4 f4
    have c4 : Ctx M₀ R κ s4 := by rw [← h4]; exact ctx_ldw I ap c3
    have hs4 := c4.inv.1
    simp only [regs] at hs4
  · rw [l5]; exact l2
  · simp only [runPrims, List.foldl, Prim.run]
    simp (disch := (simp only [size_set, oB2, oX, oY, oFl] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l4, y4, y3, f4, f3]

/-- The comparisons' conjunction is `0` exactly when the left half is not the previous answer. -/
theorem flag4 (W : ℕ → Word) (b o : ℕ) :
    XOp.and.eval (XOp.and.eval (XOp.and.eval (XOp.and.eval 1
      (XOp.eq.eval (W (b + o + 1 + 0)) (W (b + o - 4 + 0))))
      (XOp.eq.eval (W (b + o + 1 + 1)) (W (b + o - 4 + 1))))
      (XOp.eq.eval (W (b + o + 1 + 2)) (W (b + o - 4 + 2))))
      (XOp.eq.eval (W (b + o + 1 + 3)) (W (b + o - 4 + 3))) = 0 ↔
    ¬ ((List.range 4).map (fun j => W (b + o + 1 + j)) = (List.range 4).map (fun j => W (b + o - 4 + j))) := by
  have e : ∀ f : ℕ → Word, (List.range 4).map f = [f 0, f 1, f 2, f 3] := fun f => rfl
  rw [e, e]
  simp only [List.cons.injEq, and_true]
  generalize W (b + o + 1 + 0) = x0
  generalize W (b + o + 1 + 1) = x1
  generalize W (b + o + 1 + 2) = x2
  generalize W (b + o + 1 + 3) = x3
  generalize W (b + o - 4 + 0) = y0
  generalize W (b + o - 4 + 1) = y1
  generalize W (b + o - 4 + 2) = y2
  generalize W (b + o - 4 + 3) = y3
  simp only [XOp.eval]
  by_cases h0 : x0 = y0 <;> by_cases h1 : x1 = y1 <;> by_cases h2 : x2 = y2 <;> by_cases h3 : x3 = y3 <;>
    simp +decide [h0, h1, h2, h3]

/-- **The sibling by comparison** emits `segOut … (.sibc o)` (`b` in `rb`). -/
theorem sibcIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) (s : St) (hc : Ctx M₀ R κ s) {rb b o : ℕ}
    (hrb : 224 < rb) (hrr : rb < regs) (ho : 4 ≤ o) (hb : rd s.M rb = toWord b) :
    (semXIR I (sibcIR ap rb o) s).o.toList = s.o.toList ++ segOut (src M₀ ap R) κ b (.sibc o) := by
  have hs := hc.inv.1
  simp only [regs] at hs hrr
  simp only [sibcIR, semXIR_seq, semXIR_blk]
  have c0 := ctx_blk (ps := [.const oFl 1]) (by simp [Prim.dst, oFl, oR, oKF, regs]) hc
  have f0 : rd (runPrims [.const oFl 1] s.M) oFl = 1 := by
    simp only [runPrims, List.foldl, Prim.run]; exact rd_set_self (by simp only [oFl]; omega)
  have w0 : ∀ p ∈ [Prim.const oFl 1], p.dst ≠ rb := by simp [Prim.dst, oFl]; omega
  have b0 : rd (runPrims [.const oFl 1] s.M) rb = toWord b := by
    rw [rd_runPrims_of_not_writes w0]; exact hb
  have hrr' : rb < regs := by simp only [regs]; omega
  obtain ⟨c1, o1, b1, f1⟩ := cmpW_sem I ap hA _ c0 (oa := o - 4) (ob := o + 1) hrb hrr' b0
  generalize semXIR I (cmpW ap rb (o - 4) (o + 1)) ⟨runPrims [.const oFl 1] s.M, s.o⟩ = s1 at c1 o1 b1 f1
  obtain ⟨c2, o2, b2, f2⟩ := cmpW_sem I ap hA _ c1 (oa := o - 3) (ob := o + 2) hrb hrr' b1
  generalize semXIR I (cmpW ap rb (o - 3) (o + 2)) s1 = s2 at c2 o2 b2 f2
  obtain ⟨c3, o3, b3, f3⟩ := cmpW_sem I ap hA _ c2 (oa := o - 2) (ob := o + 3) hrb hrr' b2
  generalize semXIR I (cmpW ap rb (o - 2) (o + 3)) s2 = s3 at c3 o3 b3 f3
  obtain ⟨c4, o4, b4, f4⟩ := cmpW_sem I ap hA _ c3 (oa := o - 1) (ob := o + 4) hrb hrr' b3
  generalize semXIR I (cmpW ap rb (o - 1) (o + 4)) s3 = s4 at c4 o4 b4 f4
  rw [f3, f2, f1, f0] at f4
  rw [show b + (o + 1) = b + o + 1 + 0 by omega, show b + (o + 2) = b + o + 1 + 1 by omega,
    show b + (o + 3) = b + o + 1 + 2 by omega, show b + (o + 4) = b + o + 1 + 3 by omega,
    show b + (o - 4) = b + o - 4 + 0 by omega, show b + (o - 3) = b + o - 4 + 1 by omega,
    show b + (o - 2) = b + o - 4 + 2 by omega, show b + (o - 1) = b + o - 4 + 3 by omega] at f4
  have key := flag4 (src M₀ ap R) b o
  rw [← f4] at key
  have hO : s4.o = s.o := by rw [o4, o3, o2, o1]
  rw [semXIR_ite, segOut]
  by_cases hq : (List.range 4).map (fun j => src M₀ ap R (b + o + 1 + j)) =
      (List.range 4).map (fun j => src M₀ ap R (b + o - 4 + j))
  · rw [if_neg (fun h => (key.1 h) hq), if_pos hq,
      cpIR_sem I ap hA (by simp only [oK]; omega) (by norm_num) _ c4 b4, hO]
    simp only [Nat.add_assoc]
  · rw [if_pos (key.2 hq), if_neg hq,
      cpIR_sem I ap hA (by simp only [oK]; omega) (by norm_num) _ c4 b4, hO]
    simp only [Nat.add_assoc]

/-! ## The headline: a compiled segment emits its words -/

/-- **A compiled segment emits its words** (`segOut` over the source `src M₀ ap R`). -/
theorem segIR_sem (I : Array Word) (ap : AP) {M₀ : Mem} {R : ℕ} {κ : Bool}
    (hA : ∀ x, regs ≤ (addrW ap (toWord R) x).toNat) :
    ∀ (seg : Seg) (d b : ℕ) (s : St), okSeg seg = true → depthSeg seg + d ≤ 9 → Ctx M₀ R κ s →
      rd s.M (oBd d) = toWord b →
      (semXIR I (segIR ap d seg) s).o.toList = s.o.toList ++ segOut (src M₀ ap R) κ b seg
  | .nil, _, _, s, _, _, _, _ => by simp [segIR, segOut, semXIR_blk]
  | .cat x y, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true] at hok
    simp only [depthSeg] at hd
    have h1 := segIR_sem I ap hA x d b s hok.1 (by omega) hc hb
    have c1 := ctx_segIR I ap x d (by omega) hc
    have k1 : rd (semXIR I (segIR ap d x) s).M (oBd d) = toWord b :=
      (frame I _ s (wf_segIR ap x d (by omega)) hc.inv _ (by simp only [oBd, regs]; omega)
        (noW_segIR ap x d _ (.inr (.inr (.inr rfl))))).trans hb
    rw [segIR, semXIR_seq, segIR_sem I ap hA y d b _ hok.2 (by omega) c1 k1, h1, segOut, List.append_assoc]
  | .kite x y, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true] at hok
    simp only [depthSeg] at hd
    rw [segIR, semXIR_ite, segOut]
    cases κ
    · rw [if_pos (hc.k.2 rfl), if_neg (by decide)]
      exact segIR_sem I ap hA y d b s hok.2 (by omega) hc hb
    · rw [if_neg (fun h => absurd (hc.k.1 h) (by decide)), if_pos rfl]
      exact segIR_sem I ap hA x d b s hok.1 (by omega) hc hb
  | .wd x, _, _, s, _, _, hc, _ => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp [segIR, segOut, semXIR, runPrims, Prim.run, rd_set_self (show oX < s.M.size by simp only [oX]; omega)]
  | .cp o n, d, b, s, hok, _, hc, hb => by
    simp only [okSeg, decide_eq_true_eq] at hok
    have := cpIR_sem I ap hA (rb := oBd d) (o := o) (n := n) (b := b) (by simp [oBd, oK]; omega) (by omega) s hc hb
    rw [segIR, segOut]; exact this
  | .sibc o, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, decide_eq_true_eq] at hok
    simp only [depthSeg] at hd
    rw [segIR]
    exact sibcIR_sem I ap hA s hc (by simp only [oBd]; omega) (by simp only [oBd, regs]; omega) hok hb
  | .shw o, d, b, s, _, _, hc, hb => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp only [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.const oK (toWord o), .op .add oU (oBd d) oK]) (by simp [Prim.dst, oK, oU, oR, oKF, regs]) hc
    have u1 : rd (runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M) oU = toWord (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oK, oU, oBd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [hb, add_toWord]
    obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
    have c2 := ctx_ldw I ap c1
    have u2 := ldw_keep I ap _ c1.inv (r := oU) (by simp [oU, regs]) (by simp [oU, oK, oT1, oT2, oT3, oAd, oX])
    generalize semXIR I (ldw ap) ⟨runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M, s.o⟩ = s2 at l1 l2 c2 u2
    have hs2 := c2.inv.1
    simp only [regs] at hs2
    have c3 := ctx_blk (ps := [.op .or oY oX oX, .op .add oU oU cOne]) (by simp [Prim.dst, oY, oU, oR, oKF, regs]) c2
    have u3 : rd (runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M) oU = toWord (b + o + 1) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, oU, oX, cOne] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [u2, u1, one_cOne c2.inv, add_one_toWord]
    have y3 : rd (runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M) oY = src M₀ ap R (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oY, oU, oX] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [l1, or_self_eval]
    obtain ⟨l4, l5⟩ := ldw_src I ap hA _ c3 u3
    have y4 := ldw_keep I ap _ c3.inv (r := oY) (by simp [oY, regs]) (by simp [oY, oK, oT1, oT2, oT3, oAd, oX])
    generalize h4 : semXIR I (ldw ap) ⟨runPrims [.op .or oY oX oX, .op .add oU oU cOne] s2.M, s2.o⟩ = s4 at l4 l5 y4
    have c4 : Ctx M₀ R κ s4 := by rw [← h4]; exact ctx_ldw I ap c3
    have hs4 := c4.inv.1
    simp only [regs] at hs4
    simp only [semXIR, runPrims, List.foldl, Prim.run, Array.toList_push, l5, l2, segOut]
    simp (disch := (simp only [size_set, oY, oX, oK] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l4, y4, y3, shl_c _ _ (by norm_num), shr_c _ _ (by norm_num)]
    rfl
  | .sh8 o, d, b, s, _, _, hc, hb => by
    have hs := hc.inv.1
    simp only [regs] at hs
    simp only [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.const oK (toWord o), .op .add oU (oBd d) oK]) (by simp [Prim.dst, oK, oU, oR, oKF, regs]) hc
    have u1 : rd (runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M) oU = toWord (b + o) := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oK, oU, oBd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [hb, add_toWord]
    obtain ⟨l1, l2⟩ := ldw_src I ap hA _ c1 u1
    have c2 := ctx_ldw I ap c1
    generalize semXIR I (ldw ap) ⟨runPrims [.const oK (toWord o), .op .add oU (oBd d) oK] s.M, s.o⟩ = s2 at l1 l2 c2
    have hs2 := c2.inv.1
    simp only [regs] at hs2
    simp only [semXIR, runPrims, List.foldl, Prim.run, Array.toList_push, l2, segOut]
    simp (disch := (simp only [size_set, oX, oK] at *; omega)) only [rd_set_self, rd_set_ne]
    rw [l1, shr_c _ _ (by norm_num)]
  | .rep c s' x, d, b, s, hok, hd, hc, hb => by
    simp only [okSeg, Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [depthSeg] at hd
    have hs := hc.inv.1
    simp only [regs] at hs
    rw [segIR, semXIR_seq, semXIR_blk]
    have c1 := ctx_blk (ps := [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)])
      (by simp [Prim.dst, oBd, oNd, oR, oKF, regs]; omega) hc
    have b1 : rd (runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M)
        (oBd (d + 1)) = toWord b := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oBd, oNd] at *; omega)) only [rd_set_self, rd_set_ne]
      rw [or_self_eval, hb]
    have n1 : rd (runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M)
        (oNd d) = toWord c := by
      simp only [runPrims, List.foldl, Prim.run]
      simp (disch := (simp only [size_set, oBd, oNd] at *; omega)) only [rd_set_self, rd_set_ne]
    generalize runPrims [.op .or (oBd (d + 1)) (oBd d) (oBd d), .const (oNd d) (toWord c)] s.M = M1 at c1 b1 n1 ⊢
    have := loopK_emit I (c := oCd d) (n := oNd d) (K := c)
      (b := .seq (segIR ap (d + 1) x) (.blk [.const oK (toWord s'), .op .add (oBd (d + 1)) (oBd (d + 1)) oK]))
      (fun j s'' => Ctx M₀ R κ s'' ∧ rd s''.M (oBd (d + 1)) = toWord (b + s' * j))
      (fun j => segOut (src M₀ ap R) κ (b + s' * j) x) ⟨M1, s.o⟩ c1.inv
      (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega) (by simp only [oCd, oNd]; omega)
      (by omega) n1
      ⟨ctx_entryK (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega) (by simp only [oCd, oR]; omega)
        (by simp only [oCd, oKF]; omega) c1,
        by rw [entryK_frame _ (by simp only [oCd, oBd]; omega) (by simp only [oBd, cTmp]; omega)]; simpa using b1⟩
      (fun j s'' _ ⟨q1, q2⟩ => by
        have h1 := segIR_sem I ap hA x (d + 1) (b + s' * j) s'' hok.2 (by omega) q1 q2
        have c2 := ctx_segIR I ap x (d + 1) (by omega) q1
        have k2 : rd (semXIR I (segIR ap (d + 1) x) s'').M (oBd (d + 1)) = toWord (b + s' * j) :=
          (frame I _ s'' (wf_segIR ap x (d + 1) (by omega)) q1.inv _ (by simp only [oBd, regs]; omega)
            (noW_segIR ap x (d + 1) _ (.inr (.inr (.inr rfl))))).trans q2
        simp only [semXIR_seq, semXIR_blk]
        generalize semXIR I (segIR ap (d + 1) x) s'' = s3 at h1 c2 k2 ⊢
        have hs3 := c2.inv.1
        simp only [regs] at hs3
        refine ⟨h1, ctx_decS (by simp only [oCd]; omega) (by simp only [oCd, regs]; omega)
          (by simp only [oCd, oR]; omega) (by simp only [oCd, oKF]; omega)
          (ctx_blk (by simp [Prim.dst, oK, oBd, oR, oKF, regs]; omega) c2), ?_⟩
        rw [rd_decS (by simp only [oCd, oBd]; omega)]
        simp only [runPrims, List.foldl, Prim.run]
        simp (disch := (simp only [size_set, oBd, oK] at *; omega)) only [rd_set_self, rd_set_ne]
        rw [k2, add_toWord]; congr 1; ring)
    rw [this.1, segOut]

/-! ## Cost, size and output bounds -/

/-- **The step bound**: a compiled segment's `cost` is at most `segCost` (on every tape). -/
theorem cost_segIR (ap : AP) : ∀ (seg : Seg) (d t : ℕ), cost (segIR ap d seg) t ≤ segCost seg
  | .nil, _, _ => by simp [segIR, cost, segCost, blkSteps]
  | .cat x y, d, t => by
    have := cost_segIR ap x d t; have := cost_segIR ap y d t
    simp only [segIR, cost, segCost]; omega
  | .kite x y, d, t => by
    have := cost_segIR ap x d t; have := cost_segIR ap y d t
    simp only [segIR, cost, segCost]; omega
  | .wd _, _, _ => by simp [segIR, cost, segCost, blkSteps]
  | .cp _ n, _, _ => by
    have := toNat_toWord_le n
    simp [segIR, cpIR, ldw, ldPs, cost, segCost, blkSteps]; omega
  | .rep c _ x, d, t => by
    have h1 := cost_segIR ap x (d + 1) t
    have h2 := toNat_toWord_le c
    have h3 := Nat.mul_le_mul h2 (Nat.add_le_add_right h1 7)
    simp only [segIR, cost, segCost, blkSteps, List.length_cons, List.length_nil]
    rw [show (if 0 + 1 + 1 = 0 then 1 else 2 * (0 + 1 + 1) - 1) = 3 from rfl,
      show cost (segIR ap (d + 1) x) t + 3 + 1 + 3 = cost (segIR ap (d + 1) x) t + 7 by omega]
    omega
  | .shw _, _, _ => by simp [segIR, ldw, ldPs, cost, segCost, blkSteps]
  | .sh8 _, _, _ => by simp [segIR, ldw, ldPs, cost, segCost, blkSteps]
  | .sibc _, _, _ => by
    simp [segIR, sibcIR, cmpW, cpIR, ldw, ldPs, cost, segCost, blkSteps, toNat_toWord]

/-- **The compiled size** of a segment is `segSize`. -/
theorem sizeIR_segIR (ap : AP) : ∀ (seg : Seg) (d : ℕ), sizeIR (segIR ap d seg) = segSize seg
  | .nil, _ => by simp [segIR, sizeIR, segSize, blkSteps]
  | .cat x y, d | .kite x y, d => by
    simp only [segIR, sizeIR, segSize, sizeIR_segIR ap x d, sizeIR_segIR ap y d]
  | .wd _, _ => by simp [segIR, sizeIR, segSize, blkSteps]
  | .cp _ _, _ => by simp [segIR, cpIR, ldw, ldPs, sizeIR, segSize, blkSteps]
  | .rep _ _ x, d => by
    simp only [segIR, sizeIR, segSize, sizeIR_segIR ap x (d + 1), blkSteps, List.length_cons,
      List.length_nil]
    norm_num; omega
  | .shw _, _ => by simp [segIR, ldw, ldPs, sizeIR, segSize, blkSteps]
  | .sh8 _, _ => by simp [segIR, ldw, ldPs, sizeIR, segSize, blkSteps]
  | .sibc _, _ => by simp [segIR, sibcIR, cmpW, cpIR, ldw, ldPs, sizeIR, segSize, blkSteps]

/-- **The output bound**: a compiled segment's `outs` is at most `segOuts`. -/
theorem outs_segIR (ap : AP) : ∀ (seg : Seg) (d t : ℕ), outs (segIR ap d seg) t ≤ segOuts seg
  | .nil, _, _ => by simp [segIR, outs, segOuts]
  | .cat x y, d, t => by
    have := outs_segIR ap x d t; have := outs_segIR ap y d t
    simp only [segIR, outs, segOuts]; omega
  | .kite x y, d, t => by
    have := outs_segIR ap x d t; have := outs_segIR ap y d t
    simp only [segIR, outs, segOuts]; omega
  | .wd _, _, _ => by simp [segIR, outs, segOuts]
  | .cp _ n, _, _ => by
    have := toNat_toWord_le n
    simp [segIR, cpIR, ldw, outs, segOuts]; omega
  | .rep c _ x, d, t => by
    have h1 := outs_segIR ap x (d + 1) t
    have h2 := toNat_toWord_le c
    simp only [segIR, outs, segOuts, Nat.add_zero, Nat.zero_add]
    exact Nat.mul_le_mul h2 h1
  | .shw _, _, _ => by simp [segIR, ldw, outs, segOuts]
  | .sh8 _, _, _ => by simp [segIR, ldw, outs, segOuts]
  | .sibc _, _, _ => by simp [segIR, sibcIR, cmpW, cpIR, ldw, outs, segOuts, toNat_toWord]

/-! ## Non-vacuity of `sibc` -/

/-- `sibc` takes the right half when the left half is the previous answer, else the left half. -/
theorem segOut_sibc_ctl :
    segOut (fun u => toWord (u % 5)) false 0 (.sibc 4) = [toWord 4, 0, toWord 1, toWord 2] ∧
    segOut (fun u => toWord u) false 0 (.sibc 4) = [toWord 5, toWord 6, toWord 7, toWord 8] := by
  decide

end Lvm.X
