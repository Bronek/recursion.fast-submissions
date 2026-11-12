-- Split out of `LvmKeccakRmfe` (BS-1): the literals of the embedding and the kernel check of the
-- embedding lemma, which need only `LvmVCore`, so they build beside the Keccak bit/linear chain.
-- The check `rmfeOk_lit` (statement unchanged) is now proved by two small kernel checks on
-- natural numbers (`rowsOk_lit`, `colsOk_lit`) and a bridge, instead of one `decide +kernel` on
-- bit lists (61 s, 8.5 GB → about 5 s).
import LvmVCore

/-!
# The RMFE literals and the kernel check of the embedding lemma

See `LvmKeccakRmfe` for the lemma over `E`. Here: `RMFE_EMBED`, `RMFE_PROJECT` as literals
(`rmfeEmbed_eq`, `rmfeProject_eq`), and `rmfeOk_lit`, the embedding lemma on unit vectors as a
boolean: for `a, b, i < 16`, the parity of the coefficients of `emb_a · emb_b` selected by
`mask_i` is `[i = a = b]`.

The kernel does not check `rmfeOk` directly. Per pair `(a, b)` it computes the carry-less product
`P = emb_a · emb_b` as a number (`clmulN`) and the 16 parities at once, as the XOR of the columns
`col_c` (bit `i` of `col_c` is bit `c` of `mask_i`) over the set bits `c` of `P` (`rowOf`);
`rowsOk_lit` checks that this is `2^a` if `a = b` and `0` otherwise (the kernel runs `rowsOkH`,
one pass over the columns), `colsOk_lit` checks the columns against `RMFE_PROJECT`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier

section

/-! ## The literals -/

/-- `RMFE_EMBED` (`keccak.rs:25-28`), in decimal. -/
def embedLit : List ℕ := [4244747, 8354290, 4935178, 7500812, 5461978, 1907870, 310894, 7885382,
  621788, 1089150, 2036820, 2178300, 5045448, 7821168, 1602438, 8489494]

/-- `RMFE_PROJECT` (`keccak.rs:29-46`), in decimal. -/
def projectLit : List ℕ := [1, 140737488355327, 43218598786281, 32136906789799, 111925089164473,
  101951566367639, 112771593653537, 102871349771039, 126754541004432, 60819261648545,
  20682647020959, 30409630824272, 11891857888673, 6939470531743, 76314673122000, 70368744177664]

set_option maxRecDepth 100000 in
theorem rmfeEmbed_eq : rmfeEmbed = embedLit := by decide +kernel

set_option maxRecDepth 100000 in
theorem rmfeProject_eq : rmfeProject = projectLit := by decide +kernel

theorem rmfeEmbed_length : rmfeEmbed.length = 16 := by rw [rmfeEmbed_eq]; rfl

theorem rmfeProject_length : rmfeProject.length = 16 := by rw [rmfeProject_eq]; rfl

/-! ## The kernel check -/

/-- The low `k` bits of `n`, as a list. -/
def bitsFrom : ℕ → ℕ → List Bool
  | _, 0 => []
  | n, k + 1 => decide (n % 2 = 1) :: bitsFrom (n / 2) k

/-- The sum of two binary polynomials. -/
def xorL : List Bool → List Bool → List Bool
  | [], l => l
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x ^^ y) :: xorL xs ys

/-- The product of two binary polynomials. -/
def mulGF2 : List Bool → List Bool → List Bool
  | [], _ => []
  | a :: A, B => xorL (if a then B else []) (false :: mulGF2 A B)

/-- The parity of the coefficients of `M` that `mask` selects, among the first `47`. -/
def parityL (mask : ℕ) (M : List Bool) : Bool :=
  (List.range 47).foldl (fun acc c ↦ acc ^^ (mask.testBit c && M.getD c false)) false

/-- The embedding lemma on unit vectors, as a boolean. -/
def rmfeOk (emb proj : List ℕ) : Bool :=
  (List.range 16).all fun a ↦ (List.range 16).all fun b ↦ (List.range 16).all fun i ↦
    parityL (proj.getD i 0) (mulGF2 (bitsFrom (emb.getD a 0) 24) (bitsFrom (emb.getD b 0) 24)) ==
      (i == a && a == b)

theorem bitsFrom_getD : ∀ (n k c : ℕ), (bitsFrom n k).getD c false = (decide (c < k) && n.testBit c)
  | n, 0, c => by simp [bitsFrom]
  | n, k + 1, 0 => by simp [bitsFrom, Nat.testBit_zero]
  | n, k + 1, c + 1 => by
    rw [bitsFrom, List.getD_cons_succ, bitsFrom_getD (n / 2) k c, Nat.testBit_div_two]
    simp

/-! ## The check on numbers -/

/-- The carry-less product of the binary polynomial `A` (a bit list, lowest first) and `y`. -/
def clmulN : List Bool → ℕ → ℕ
  | [], _ => 0
  | a :: A, y => cond a y 0 ^^^ (clmulN A y <<< 1)

/-- The columns of `RMFE_PROJECT`: bit `i` of `colLit[c]` is bit `c` of `RMFE_PROJECT[i]`. -/
def colLit : List ℕ := [14079, 9386, 9386, 9366, 28082, 4702, 18438, 30526, 7402, 19370, 16214,
  25330, 6302, 3974, 894, 16874, 29034, 22998, 15986, 27166, 24070, 31550, 22506, 29802, 7446,
  3058, 18270, 15558, 9150, 24682, 22826, 14038, 9394, 9374, 9350, 28094, 4714, 18474, 30486,
  7410, 19358, 16198, 25342, 6314, 4010, 854, 49650]

/-- The sixteen parities of `P` at once: the XOR of the columns `cols[c]` over the set bits `c`
of `P`, `c < 47`. -/
def rowOf (P : ℕ) (cols : List ℕ) : ℕ :=
  (List.range 47).foldl (fun acc c ↦ bif P.testBit c then acc ^^^ cols.getD c 0 else acc) 0

/-- Per pair `(a, b)`, the parities of `emb_a · emb_b` are `2^a` if `a = b`, `0` otherwise. -/
def rowsOk (emb cols : List ℕ) : Bool :=
  (List.range 16).all fun a ↦ (List.range 16).all fun b ↦
    rowOf (clmulN (bitsFrom (emb.getD a 0) 24) (emb.getD b 0 % 2 ^ 24)) cols ==
      bif a == b then 1 <<< a else 0

/-- `cols` are the columns of `proj`. -/
def colsOk (proj cols : List ℕ) : Bool :=
  (List.range 16).all fun i ↦ (List.range 47).all fun c ↦
    (cols.getD c 0).testBit i == (proj.getD i 0).testBit c

/-- `rowOf` in one pass over the columns, halving `P` (`rowOf_eq_H`): no `getD`, no `testBit`. -/
def rowOfH : ℕ → List ℕ → ℕ → ℕ
  | _, [], acc => acc
  | P, col :: cs, acc => rowOfH (P / 2) cs (cond (Nat.beq (P % 2) 1) (acc ^^^ col) acc)

/-- `rowsOk` through `rowOfH` (`rowsOk_eq_H`), the form the kernel decides. -/
def rowsOkH (emb cols : List ℕ) : Bool :=
  (List.range 16).all fun a ↦ (List.range 16).all fun b ↦
    rowOfH (clmulN (bitsFrom (emb.getD a 0) 24) (emb.getD b 0 % 2 ^ 24)) cols 0 ==
      bif a == b then 1 <<< a else 0

private theorem foldl_rowOf (P : ℕ) (cols : List ℕ) : ∀ (n k acc : ℕ), k + n ≤ cols.length →
    (List.range' k n).foldl (fun acc c ↦ bif P.testBit c then acc ^^^ cols.getD c 0 else acc) acc =
      rowOfH (P / 2 ^ k) ((cols.drop k).take n) acc
  | 0, k, acc, _ => by simp [rowOfH]
  | n + 1, k, acc, h => by
    have hk : k < cols.length := by omega
    rw [List.range'_succ, List.foldl_cons, foldl_rowOf P cols n (k + 1) _ (by omega),
      List.drop_eq_getElem_cons hk, List.take_succ_cons, rowOfH, Nat.div_div_eq_div_mul, ← Nat.pow_succ,
      List.getD_eq_getElem _ _ hk, Nat.testBit_eq_decide_div_mod_eq]
    congr 1
    cases h2 : Nat.beq (P / 2 ^ k % 2) 1
    · have := Nat.ne_of_beq_eq_false h2; simp [this]
    · have := Nat.eq_of_beq_eq_true h2; simp [this]

theorem rowOf_eq_H (P : ℕ) {cols : List ℕ} (h : cols.length = 47) : rowOf P cols = rowOfH P cols 0 := by
  rw [rowOf, List.range_eq_range', foldl_rowOf P cols 47 0 0 (by omega)]
  simp [← h]

theorem rowsOk_eq_H {emb cols : List ℕ} (h : cols.length = 47) : rowsOk emb cols = rowsOkH emb cols := by
  simp only [rowsOk, rowsOkH, rowOf_eq_H _ h]

set_option maxRecDepth 100000 in
theorem rowsOk_lit : rowsOk embedLit colLit = true := by
  rw [rowsOk_eq_H rfl]; decide +kernel

set_option maxRecDepth 100000 in
theorem colsOk_lit : colsOk projectLit colLit = true := by decide +kernel

/-! ## The bridge to `rmfeOk` -/

private theorem getD_xorL : ∀ (A B : List Bool) (c : ℕ),
    (xorL A B).getD c false = (A.getD c false ^^ B.getD c false)
  | [], l, c => by simp [xorL]
  | x :: xs, [], c => by simp [xorL]
  | x :: xs, y :: ys, 0 => by simp [xorL]
  | x :: xs, y :: ys, c + 1 => by
    rw [xorL, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, getD_xorL xs ys c]

private theorem getD_mulGF2 {B : List Bool} {y : ℕ} (hB : ∀ c, B.getD c false = y.testBit c) :
    ∀ (A : List Bool) (c : ℕ), (mulGF2 A B).getD c false = (clmulN A y).testBit c
  | [], c => by simp [mulGF2, clmulN]
  | a :: A, c => by
    rw [mulGF2, clmulN, getD_xorL, Nat.testBit_xor, Nat.testBit_shiftLeft]
    have h1 : (if a then B else []).getD c false = (cond a y 0).testBit c := by
      cases a
      · simp
      · exact hB c
    have h2 : (false :: mulGF2 A B).getD c false =
        (decide (c ≥ 1) && (clmulN A y).testBit (c - 1)) := by
      rcases c with _ | c
      · simp
      · rw [List.getD_cons_succ, getD_mulGF2 hB A c]; simp
    rw [h1, h2]

private theorem getD_bitsFrom_mod (y k c : ℕ) :
    (bitsFrom y k).getD c false = (y % 2 ^ k).testBit c := by
  rw [bitsFrom_getD, Nat.testBit_mod_two_pow]

private theorem testBit_foldl_row (P : ℕ) (cols : List ℕ) (mask i : ℕ) : ∀ (l : List ℕ),
    (∀ c ∈ l, (cols.getD c 0).testBit i = mask.testBit c) → ∀ (acc : ℕ) (b : Bool),
    acc.testBit i = b →
    (l.foldl (fun acc c ↦ bif P.testBit c then acc ^^^ cols.getD c 0 else acc) acc).testBit i =
      l.foldl (fun b c ↦ b ^^ (mask.testBit c && P.testBit c)) b
  | [], _, acc, b, h => h
  | c :: l, hl, acc, b, h => by
    rw [List.foldl_cons, List.foldl_cons]
    apply testBit_foldl_row P cols mask i l (fun c' hc' ↦ hl c' (List.mem_cons_of_mem _ hc'))
    rw [← hl c (by simp), ← h]
    cases P.testBit c <;> simp [Nat.testBit_xor]

theorem rmfeOk_lit_at {a b i : ℕ} (ha : a < 16) (hb : b < 16) (hi : i < 16) :
    parityL (projectLit.getD i 0)
      (mulGF2 (bitsFrom (embedLit.getD a 0) 24) (bitsFrom (embedLit.getD b 0) 24)) =
        (i == a && a == b) := by
  have hr : rowOf (clmulN (bitsFrom (embedLit.getD a 0) 24) (embedLit.getD b 0 % 2 ^ 24)) colLit =
      bif a == b then 1 <<< a else 0 := by
    have h := rowsOk_lit
    simp only [rowsOk, List.all_eq_true, List.mem_range] at h
    exact eq_of_beq (h a ha b hb)
  have hc : ∀ c ∈ List.range 47, (colLit.getD c 0).testBit i = (projectLit.getD i 0).testBit c := by
    have h := colsOk_lit
    simp only [colsOk, List.all_eq_true, List.mem_range] at h
    exact fun c hc ↦ eq_of_beq (h i hi c (List.mem_range.1 hc))
  unfold parityL
  simp_rw [getD_mulGF2 (getD_bitsFrom_mod _ 24)]
  rw [← testBit_foldl_row _ colLit _ i _ hc 0 false (Nat.zero_testBit i)]
  change (rowOf _ colLit).testBit i = _
  rw [hr]
  by_cases hab : a = b
  · subst hab
    by_cases hia : i = a
    · subst hia; simp [Nat.one_shiftLeft]
    · simp [Nat.one_shiftLeft, hia, Ne.symm hia]
  · simp [hab]

/-- **The embedding lemma**, checked by the kernel on the literals (by `rowsOk_lit`,
`colsOk_lit`). -/
theorem rmfeOk_lit : rmfeOk embedLit projectLit = true := by
  simp only [rmfeOk, List.all_eq_true, List.mem_range]
  intro a ha b hb i hi
  rw [rmfeOk_lit_at ha hb hi, beq_self_eq_true]

end
end LeanVM.Protocol.KeccakGkr
