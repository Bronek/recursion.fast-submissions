-- New for lvm (WP-11b-QA2, helper H1). `ringWeight_sum` adapted from our
-- `LvmRingFidelity.ringWeight_fold`/`foldl_zip_eqEval` (restated on `Lvm.FE`, with the product
-- written out instead of `eqEval`).
import LvmQRing

/-!
# QA2 ring switching, part 3: the weight `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`

`F`'s weight (`LvmDecideKeccak.ringWeight point rPrime (ringCoefficients ch)`) at the sumcheck
point `r'`, the point `r` and the coefficients of `coeffs`. The point length `N` is cut into
chunks of `2^b` coordinates (`bs`, e.g. `26 = 16 + 8 + 2`, `21 = 16 + 4 + 1`). Gadget
`ringWeightG bs ch r0 rp0 z` (`r_n`, `r'_n` in the `E` cells `r0 + n`, `rp0 + n`):

* per chunk (`fChunk`), `f(n, k) = 1 + r_n^(2^k) + r'_n` for `k ≤ 64`: `D_n = r'_n² + r'_n`,
  `f(n, 0) = r_n + r'_n + 1`, then `f(n, k + 1) = f(n, k)² + D_n` (dims `[b, 6]`, `n` fastest; the
  `k = 0` row reads `f(n, 0)`, laid out just before): `66·2^b` rows;
* the coefficients (`coeffs`, 131 rows), which end just before the products;
* per chunk (`pChunk`), the running products `P(k, n) = P(k, n − 1)·f(n, k)` (dims `[6, b]`, `k`
  fastest; `n = −1` is the coefficient `c_k`, the chunk before ends with the products so far):
  `64·2^b` rows;
* `Σ_k P(k, N − 1)` by a running sum from a copy of the zero cell: 65 rows.

`ringWeight_eq`: **the weight cell is `F`'s `ringWeight r r' (ringCoefficients ch)`**.
-/

set_option autoImplicit false

namespace Lvm.Loop.QRing

open Lvm Lvm.Loop Lvm.Loop.Build

variable {c : Ctx} {M : Mem}

/-! ## `F`'s side -/

/-- The factor `1 + r^(2^k) + r'`. -/
def wf (r r' : FE) (k : Nat) : FE := 1 + r ^ 2 ^ k + r'

-- adapted from LvmRingFidelity.foldl_zip_eqEval, on Lvm.FE, product written out
theorem foldl_zip_prod : ∀ (l₁ l₂ : List FE) (a : FE), l₁.length = l₂.length →
    (List.zip l₁ l₂).foldl (fun (product : FE) (p : FE × FE) => product * (1 + p.1 + p.2)) a =
      a * ∏ n ∈ Finset.range l₁.length, (1 + l₁.getD n 0 + l₂.getD n 0)
  | [], [], a, _ => by simp
  | x :: l₁, y :: l₂, a, h => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_prod l₁ l₂ _ (by simpa using h),
      List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

-- adapted from LvmRingFidelity.ringWeight_fold, on Lvm.FE
theorem ringWeight_fold (r y : List FE) (hl : r.length = y.length) :
    ∀ (cs : List FE) (a : FE) (k : Nat),
      (cs.foldl (fun (acc : FE × List FE) cc =>
        ((acc.1 + (List.zip acc.2 y).foldl (fun (product : FE) (p : FE × FE) =>
          product * (1 + p.1 + p.2)) cc), acc.2.map FE.sq)) (a, r.map (· ^ 2 ^ k))).1 =
        a + ∑ i ∈ Finset.range cs.length,
          cs.getD i 0 * ∏ n ∈ Finset.range r.length, wf (r.getD n 0) (y.getD n 0) (k + i)
  | [], a, k => by simp
  | cc :: cs, a, k => by
    rw [List.foldl_cons]
    have hm : (r.map (· ^ 2 ^ k)).map FE.sq = r.map (· ^ 2 ^ (k + 1)) := by
      rw [List.map_map]
      refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp, FE.sq_eq_mul, pow_succ, pow_mul]
      ring
    simp only
    rw [hm, ringWeight_fold r y hl cs _ (k + 1), foldl_zip_prod _ _ _ (by simpa using hl),
      List.length_cons, Finset.sum_range_succ', List.length_map]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have e : ∀ n ∈ Finset.range r.length, 1 + (r.map (· ^ 2 ^ k)).getD n 0 + y.getD n 0 =
        wf (r.getD n 0) (y.getD n 0) k := by
      intro n hn
      have hn' := Finset.mem_range.1 hn
      rw [List.getD_eq_getElem _ _ (by simpa using hn'), List.getElem_map,
        List.getD_eq_getElem _ _ hn']
      rfl
    rw [Finset.prod_congr rfl e]
    have e2 : ∀ i ∈ Finset.range cs.length,
        cs.getD i 0 * ∏ n ∈ Finset.range r.length, wf (r.getD n 0) (y.getD n 0) (k + 1 + i) =
        cs.getD i 0 * ∏ n ∈ Finset.range r.length, wf (r.getD n 0) (y.getD n 0) (k + (i + 1)) :=
      fun i _ => by rw [show k + 1 + i = k + (i + 1) by omega]
    rw [Finset.sum_congr rfl e2]
    ring

/-- **`F`'s weight as a sum of products.** -/
theorem ringWeight_sum (r y cs : List FE) (hl : r.length = y.length) :
    ringWeight r y cs = ∑ i ∈ Finset.range cs.length,
      cs.getD i 0 * ∏ n ∈ Finset.range r.length, wf (r.getD n 0) (y.getD n 0) i := by
  have e1 : (fun (product : FE) (p : FE × FE) => match p with
      | (value, challenge) => product * (1 + value + challenge)) =
      fun (product : FE) (p : FE × FE) => product * (1 + p.1 + p.2) := by
    funext a p; rcases p with ⟨u, v⟩; rfl
  have := ringWeight_fold r y hl cs 0 0
  simp only [pow_zero, pow_one, List.map_id', zero_add] at this
  rw [ringWeight, e1, this]

/-! ## The factors `f(n, k)` of one chunk -/

/-- Chunk `n ∈ [n₀, n₀ + 2^b)`: `D_n`, `f(n, 0)`, then the chain `f(n, k)`, `k ≤ 64`, at the
returned base `F`: `f(n₀ + n', k)` is cell `F + n' + 2^b·k`. -/
def fChunk (b r0 rp0 n0 : Nat) : BM Nat := do
  let d ← madL [b] (eA (rp0 + n0) [1]) (eA (rp0 + n0) [1]) (eA (rp0 + n0) [1])
  let fi ← linL [b] 1 1 (eA (r0 + n0) [1]) (eA (rp0 + n0) [1])
  let _ ← madL [b, 6] (eA fi.p.e [1, 2 ^ b]) (eA fi.p.e [1, 2 ^ b]) (eA d.p.e [1, 0])
  pure fi.p.e

theorem fChunk_out (b r0 rp0 n0 : Nat) (p : Ptr) : (fChunk b r0 rp0 n0 p).1 = p.e + 2 ^ b := by
  simp only [fChunk]
  rw [bind_fst_eq rfl (madL_adv _ _ _ _ _), bind_fst_eq rfl (linL_adv _ _ _ _ _ _),
    bind_fst_eq rfl (madL_adv _ _ _ _ _)]
  simp [pure_apply]

theorem fChunk_adv (b r0 rp0 n0 : Nat) (p : Ptr) :
    p.adv (fChunk b r0 rp0 n0 p).2 = ⟨p.k, p.e + 66 * 2 ^ b⟩ := by
  simp only [fChunk]
  rw [bind_adv_eq rfl (madL_adv _ _ _ _ _), bind_adv_eq rfl (linL_adv _ _ _ _ _ _),
    bind_adv_eq rfl (madL_adv _ _ _ _ _), pure_apply, Ptr.adv_nil]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Ptr.mk.injEq, true_and, pow_add]
  ring

/-- The factors of a chunk. -/
theorem fChunk_spec {b r0 rp0 n0 : Nat} {R R' : Nat → FE} {p : Ptr}
    (hr : ∀ n < 2 ^ b, M.e (r0 + n0 + n) = R (n0 + n))
    (hr' : ∀ n < 2 ^ b, M.e (rp0 + n0 + n) = R' (n0 + n))
    (h : SegsHold c M p (fChunk b r0 rp0 n0 p).2) :
    ∀ n < 2 ^ b, ∀ k ≤ 64, M.e (p.e + 2 ^ b + n + 2 ^ b * k) = wf (R (n0 + n)) (R' (n0 + n)) k := by
  simp only [fChunk] at h
  rw [hold_bind_eq rfl (madL_adv _ _ _ _ _)] at h
  obtain ⟨hd, h⟩ := h
  rw [hold_bind_eq rfl (linL_adv _ _ _ _ _ _)] at h
  obtain ⟨hi, h⟩ := h
  rw [hold_bind_eq rfl (madL_adv _ _ _ _ _)] at h
  obtain ⟨hc, -⟩ := h
  simp only [madL_p, linL_p, List.sum_cons, List.sum_nil, Nat.add_zero] at hc hi
  have hD : ∀ n < 2 ^ b, M.e (p.e + n) = R' (n0 + n) * R' (n0 + n) + R' (n0 + n) := by
    intro n hn
    have e := madL_spec hd (jf := n) (by simpa using hn)
    simp only [Mem.rd, Addr.at, unflat_one hn, dot, Nat.one_mul, Nat.add_zero] at e
    rw [e, hr' n hn]
  have hI : ∀ n < 2 ^ b, M.e (p.e + 2 ^ b + n) = wf (R (n0 + n)) (R' (n0 + n)) 0 := by
    intro n hn
    have e := linL_spec hi (jf := n) (by simpa using hn)
    simp only [Mem.rd, Addr.at, unflat_one hn, dot, Nat.one_mul, Nat.add_zero, ofK_one,
      one_mul, List.sum_cons, List.sum_nil] at e
    rw [e, hr n hn, hr' n hn, wf, pow_zero, pow_one]
    ring
  intro n hn k hk
  induction k with
  | zero => simpa using hI n hn
  | succ k ih =>
    have hk6 : k < 2 ^ 6 := by norm_num; omega
    have e := madL_spec hc (jf := n + 2 ^ b * k) (by simpa [Nat.add_comm b 6] using lt_two_dims hn hk6)
    rw [unflat_two hn hk6] at e
    simp only [Mem.rd, Addr.at, dot, Nat.one_mul, Nat.add_zero, Nat.zero_mul] at e
    rw [show p.e + 2 ^ b + n + 2 ^ b * (k + 1) = p.e + 2 ^ b + 2 ^ b + (n + 2 ^ b * k) by ring, e,
      show p.e + 2 ^ b + (n + 2 ^ b * k) = p.e + 2 ^ b + n + 2 ^ b * k by ring, ih (by omega),
      hD n hn]
    simp only [wf, pow_succ, pow_mul]
    have h2 : ∀ x : FE, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
    linear_combination h2 (R (n0 + n) ^ 2 ^ k) + h2 (R' (n0 + n)) +
      h2 (R (n0 + n) ^ 2 ^ k * R' (n0 + n)) + h2 (R' (n0 + n) * R' (n0 + n))

/-! ## All chunks -/

/-- The number of coordinates of the chunks `2^b`, `b ∈ bs`. -/
def sz (bs : List Nat) : Nat := (bs.map (2 ^ ·)).sum

theorem sz_cons (b : Nat) (bs : List Nat) : sz (b :: bs) = 2 ^ b + sz bs := by simp [sz]

/-- The factor tables of the chunks, the first from coordinate `n₀`; returns their bases. -/
def fChunks (r0 rp0 : Nat) : Nat → List Nat → BM (List Nat)
  | _, [] => pure []
  | n0, b :: bs => do
    let F ← fChunk b r0 rp0 n0
    let Fs ← fChunks r0 rp0 (n0 + 2 ^ b) bs
    pure (F :: Fs)

theorem fChunks_adv (r0 rp0 : Nat) : ∀ (bs : List Nat) (n0 : Nat) (p : Ptr),
    p.adv (fChunks r0 rp0 n0 bs p).2 = ⟨p.k, p.e + 66 * sz bs⟩
  | [], n0, p => by simp [fChunks, pure_apply, sz]
  | b :: bs, n0, p => by
    simp only [fChunks]
    rw [bind_adv_eq rfl (fChunk_adv _ _ _ _ _), bind_adv_eq rfl (fChunks_adv r0 rp0 bs _ _),
      pure_apply, Ptr.adv_nil, sz_cons]
    simp only [Ptr.mk.injEq, true_and]
    ring

/-- The factor tables: chunk `b` (coordinates from `n₀`) has `fv (n₀ + n) k` at the cell
`F + n + 2^b·k`, `F` its base (the head of `Fs`). -/
def FOk (M : Mem) (fv : Nat → Nat → FE) : Nat → List Nat → List Nat → Prop
  | _, [], _ => True
  | n0, b :: bs, Fs => (∀ n < 2 ^ b, ∀ k < 64, M.e (Fs.headD 0 + n + 2 ^ b * k) = fv (n0 + n) k) ∧
      FOk M fv (n0 + 2 ^ b) bs Fs.tail

theorem fChunks_spec {r0 rp0 : Nat} {R R' : Nat → FE} : ∀ (bs : List Nat) (n0 : Nat) (p : Ptr),
    (∀ n < sz bs, M.e (r0 + n0 + n) = R (n0 + n)) →
    (∀ n < sz bs, M.e (rp0 + n0 + n) = R' (n0 + n)) →
    SegsHold c M p (fChunks r0 rp0 n0 bs p).2 →
    FOk M (fun n k => wf (R n) (R' n) k) n0 bs (fChunks r0 rp0 n0 bs p).1
  | [], _, _, _, _, _ => trivial
  | b :: bs, n0, p, hr, hr', h => by
    simp only [fChunks] at h ⊢
    rw [hold_bind_eq rfl (fChunk_adv _ _ _ _ _)] at h
    obtain ⟨h1, h⟩ := h
    rw [hold_bind_eq rfl (fChunks_adv _ _ _ _ _)] at h
    obtain ⟨h2, -⟩ := h
    rw [bind_fst_eq rfl (fChunk_adv _ _ _ _ _), bind_fst_eq rfl (fChunks_adv _ _ _ _ _), pure_apply]
    simp only [FOk, List.headD_cons, List.tail_cons]
    rw [sz_cons] at hr hr'
    refine ⟨?_, ?_⟩
    · intro n hn k hk
      rw [fChunk_out]
      exact fChunk_spec (fun n hn' => hr n (by omega)) (fun n hn' => hr' n (by omega)) h1 n hn k
        hk.le
    · refine fChunks_spec bs (n0 + 2 ^ b) _ (fun n hn => ?_) (fun n hn => ?_) h2
      · rw [show r0 + (n0 + 2 ^ b) + n = r0 + n0 + (2 ^ b + n) by ring, hr _ (by omega)]
        congr 1; ring
      · rw [show rp0 + (n0 + 2 ^ b) + n = rp0 + n0 + (2 ^ b + n) by ring, hr' _ (by omega)]
        congr 1; ring

/-! ## The products -/

/-- Chunk `b` of the running products: the 64 products so far are the 64 cells before the
pointer; `P(k, n) = P(k, n − 1)·f(n, k)` with `f(n, k)` at `F + n + 2^b·k` (dims `[6, b]`). -/
def pChunk (b F z : Nat) : BM Unit := do
  let p ← getPtr
  let _ ← madL [6, b] (eA (p.e - 64) [1, 64]) (eA F [2 ^ b, 1]) (eA z [])
  pure ()

theorem pChunk_adv (b F z : Nat) (p : Ptr) : p.adv (pChunk b F z p).2 = ⟨p.k, p.e + 64 * 2 ^ b⟩ := by
  simp only [pChunk]
  rw [bind_adv_eq (getPtr_out _) (getPtr_adv _), bind_adv_eq rfl (madL_adv _ _ _ _ _), pure_apply,
    Ptr.adv_nil]
  simp [pow_add]

theorem pChunk_spec {b F z : Nat} {p : Ptr} {A : Nat → FE} {g : Nat → Nat → FE} (hz : M.e z = 0)
    (h64 : 64 ≤ p.e) (hA : ∀ k < 64, M.e (p.e - 64 + k) = A k)
    (hg : ∀ n < 2 ^ b, ∀ k < 64, M.e (F + n + 2 ^ b * k) = g n k)
    (h : SegsHold c M p (pChunk b F z p).2) :
    ∀ k < 64, M.e (p.e + 64 * 2 ^ b - 64 + k) = A k * ∏ n ∈ Finset.range (2 ^ b), g n k := by
  simp only [pChunk] at h
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq rfl (madL_adv _ _ _ _ _)] at h
  obtain ⟨hs, -⟩ := h
  have hrun : ∀ k < 2 ^ 6, ∀ n < 2 ^ b,
      M.e (p.e + (k + 2 ^ 6 * n)) = A k * ∏ m ∈ Finset.range (n + 1), g m k := by
    intro k hk n
    induction n with
    | zero =>
      intro hn
      have e := madL_spec hs (jf := k + 2 ^ 6 * 0) (by simpa using lt_two_dims hk hn)
      rw [unflat_two hk hn] at e
      simp only [Mem.rd, Addr.at, dot, hz, add_zero, Nat.one_mul, Nat.mul_zero] at e
      rw [show p.e + (k + 2 ^ 6 * 0) = p.e + k by simp, e, hA k (by simpa using hk),
        show F + 2 ^ b * k = F + 0 + 2 ^ b * k by simp, hg 0 hn k (by simpa using hk)]
      simp
    | succ n ih =>
      intro hn
      have e := madL_spec hs (jf := k + 2 ^ 6 * (n + 1)) (by simpa using lt_two_dims hk hn)
      rw [unflat_two hk hn] at e
      simp only [Mem.rd, Addr.at, dot, hz, add_zero, Nat.one_mul] at e
      rw [e, show p.e - 64 + (k + 64 * (n + 1)) = p.e + (k + 2 ^ 6 * n) by omega, ih (by omega),
        show F + (2 ^ b * k + (n + 1)) = F + (n + 1) + 2 ^ b * k by ring,
        hg (n + 1) hn k (by simpa using hk), Finset.prod_range_succ _ (n + 1)]
      ring
  intro k hk
  have hb1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have e := hrun k (by simpa using hk) (2 ^ b - 1) (by omega)
  rw [Nat.sub_add_cancel hb1] at e
  rw [← e]
  congr 1
  have : 2 ^ 6 * (2 ^ b - 1) = 64 * 2 ^ b - 64 := by
    rw [Nat.mul_sub, Nat.mul_one]; rfl
  omega

/-- The product chunks, chunk `j` reading the `j`-th factor table. -/
def pChunks (z : Nat) : List Nat → List Nat → BM Unit
  | [], _ => pure ()
  | b :: bs, Fs => do
    pChunk b (Fs.headD 0) z
    pChunks z bs Fs.tail

theorem pChunks_adv (z : Nat) : ∀ (bs Fs : List Nat) (p : Ptr),
    p.adv (pChunks z bs Fs p).2 = ⟨p.k, p.e + 64 * sz bs⟩
  | [], Fs, p => by simp [pChunks, pure_apply, sz]
  | b :: bs, Fs, p => by
    simp only [pChunks]
    rw [bind_adv_eq rfl (pChunk_adv _ _ _ _), pChunks_adv z bs _ _, sz_cons]
    simp only [Ptr.mk.injEq, true_and]
    ring

theorem pChunks_spec {z : Nat} {fv : Nat → Nat → FE} (hz : M.e z = 0) :
    ∀ (bs Fs : List Nat) (n0 : Nat) (p : Ptr) (A : Nat → FE), 64 ≤ p.e →
    (∀ k < 64, M.e (p.e - 64 + k) = A k) → FOk M fv n0 bs Fs →
    SegsHold c M p (pChunks z bs Fs p).2 →
    ∀ k < 64, M.e (p.e + 64 * sz bs - 64 + k) = A k * ∏ n ∈ Finset.range (sz bs), fv (n0 + n) k
  | [], _, _, p, A, _, hA, _, _ => by simpa [sz] using hA
  | b :: bs, Fs, n0, p, A, h64, hA, hF, h => by
    simp only [pChunks] at h
    rw [hold_bind_eq rfl (pChunk_adv _ _ _ _)] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hF1, hF2⟩ := hF
    have hs := pChunk_spec (g := fun n k => fv (n0 + n) k) hz h64 hA hF1 h1
    have ih := pChunks_spec hz bs Fs.tail (n0 + 2 ^ b) _
      (fun k => A k * ∏ n ∈ Finset.range (2 ^ b), fv (n0 + n) k)
      (by show 64 ≤ p.e + 64 * 2 ^ b; have := Nat.one_le_two_pow (n := b); omega)
      (fun k hk => by rw [← hs k hk])
      hF2 h2
    intro k hk
    have e := ih k hk
    rw [show ({ k := p.k, e := p.e + 64 * 2 ^ b } : Ptr).e + 64 * sz bs - 64 + k =
      p.e + 64 * sz (b :: bs) - 64 + k by simp only [sz_cons]; ring_nf] at e
    rw [e, sz_cons, Finset.prod_range_add, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun n _ => ?_
    rw [Nat.add_assoc]

/-! ## The weight -/

/-- **The ring-switching weight** at the point `r` (cells `r0 + n`) and `r'` (cells `rp0 + n`),
`n < sz bs`, with the challenges in the `E` cells `ch + i` and a zero `E` cell `z`. -/
def ringWeightG (bs : List Nat) (ch r0 rp0 z : Nat) : BM Nat := do
  let Fs ← fChunks r0 rp0 0 bs
  let _ ← coeffs ch z
  pChunks z bs Fs
  let p ← getPtr
  let q ← copy (ec z)
  let _ ← linL [6] 1 0 (eA (p.e - 64) [1]) (eA q.n [1])
  pure (q.n + 64)

theorem ringWeightG_out (bs : List Nat) (ch r0 rp0 z : Nat) (p : Ptr) :
    (ringWeightG bs ch r0 rp0 z p).1 = p.e + 130 * sz bs + 195 := by
  simp only [ringWeightG]
  rw [bind_fst_eq rfl (fChunks_adv _ _ _ _ _), bind_fst_eq rfl (coeffs_adv _ _ _),
    bind_fst_eq rfl (pChunks_adv _ _ _ _), bind_fst_eq (getPtr_out _) (getPtr_adv _),
    bind_fst_eq (copy_out _ _) (copyE_adv _ _), bind_fst_eq rfl (linL_adv _ _ _ _ _ _), pure_apply]
  simp only [ec, Ptr.at]
  ring

theorem ringWeightG_adv (bs : List Nat) (ch r0 rp0 z : Nat) (p : Ptr) :
    p.adv (ringWeightG bs ch r0 rp0 z p).2 = ⟨p.k, p.e + 130 * sz bs + 196⟩ := by
  simp only [ringWeightG]
  rw [bind_adv_eq rfl (fChunks_adv _ _ _ _ _), bind_adv_eq rfl (coeffs_adv _ _ _),
    bind_adv_eq rfl (pChunks_adv _ _ _ _), bind_adv_eq (getPtr_out _) (getPtr_adv _),
    bind_adv_eq (copy_out _ _) (copyE_adv _ _), bind_adv_eq rfl (linL_adv _ _ _ _ _ _), pure_apply,
    Ptr.adv_nil]
  simp only [List.sum_cons, List.sum_nil, Ptr.mk.injEq, true_and]
  ring

/-- **Q_arith_eq, ring-switching weight.** If the `E` cells `r0 + n`, `rp0 + n` hold the point `r`
and the sumcheck point `r'` (`n < sz bs`, both of length `sz bs`), the cells `ch + i` the six
challenges and `z` zero, the gadget's cell (`p.e + 130·sz bs + 195`) is `F`'s
`ringWeight r r' (ringCoefficients ch)`. -/
theorem ringWeight_eq {bs : List Nat} {ch r0 rp0 z : Nat} {chs r rp : List FE}
    (hl : chs.length = 6) (hch : ∀ i < 6, M.e (ch + i) = chs.getD i 0) (hz : M.e z = 0)
    (hr : r.length = sz bs) (hrp : rp.length = sz bs)
    (hrv : ∀ n < sz bs, M.e (r0 + n) = r.getD n 0) (hrpv : ∀ n < sz bs, M.e (rp0 + n) = rp.getD n 0)
    {p : Ptr} (h : SegsHold c M p (ringWeightG bs ch r0 rp0 z p).2) :
    M.e (ringWeightG bs ch r0 rp0 z p).1 = ringWeight r rp (ringCoefficients chs) := by
  rw [ringWeightG_out]
  simp only [ringWeightG] at h
  rw [hold_bind_eq rfl (fChunks_adv _ _ _ _ _)] at h
  obtain ⟨hf, h⟩ := h
  rw [hold_bind_eq rfl (coeffs_adv _ _ _)] at h
  obtain ⟨hc, h⟩ := h
  rw [hold_bind_eq rfl (pChunks_adv _ _ _ _)] at h
  obtain ⟨hp, h⟩ := h
  rw [hold_bind_eq (getPtr_out _) (getPtr_adv _)] at h
  obtain ⟨-, h⟩ := h
  rw [hold_bind_eq (copy_out _ _) (copyE_adv _ _)] at h
  obtain ⟨hq, h⟩ := h
  rw [hold_bind_eq rfl (linL_adv' [6] 64 rfl _ _ _ _ _)] at h
  obtain ⟨hH, -⟩ := h
  have hF := fChunks_spec (R := fun n => r.getD n 0) (R' := fun n => rp.getD n 0) bs 0 p
    (by simpa using hrv) (by simpa using hrpv) hf
  have hC := coeffs_eq hl hch hz hc
  have hP := pChunks_spec hz bs _ 0 ⟨p.k, p.e + 66 * sz bs + 131⟩
    (fun k => (ringCoefficients chs).getD k 0) (by show 64 ≤ p.e + 66 * sz bs + 131; omega)
    (fun k hk => by
      rw [← hC k hk]
      show M.e (p.e + 66 * sz bs + 131 - 64 + k) = M.e (p.e + 66 * sz bs + 67 + k)
      rw [show p.e + 66 * sz bs + 131 - 64 + k = p.e + 66 * sz bs + 67 + k by omega]) hF hp
  simp only [Nat.zero_add] at hP
  have h0 := (copyE_spec hq).2
  simp only [ec, Ptr.at] at h0 hH
  -- the running sum of the 64 products
  have hacc : ∀ k < 64, M.e (p.e + 66 * sz bs + 131 + 64 * sz bs + 1 + k) =
      ∑ j ∈ Finset.range (k + 1), (ringCoefficients chs).getD j 0 *
        ∏ n ∈ Finset.range (sz bs), wf (r.getD n 0) (rp.getD n 0) j := by
    intro k hk
    induction k with
    | zero =>
      have e := linL_spec hH (jf := 0) (by simp)
      simp only [Mem.rd, Addr.at, unflat_one (show 0 < 2 ^ 6 by norm_num), dot, Nat.add_zero,
        Nat.mul_zero, h0, hz, mul_zero, ofK_zero, ofK_one, one_mul, add_zero] at e
      rw [e, zero_add, Finset.sum_range_one]
      exact hP 0 hk
    | succ k ih =>
      have e := linL_spec hH (jf := k + 1) (by simpa using hk)
      simp only [Mem.rd, Addr.at, unflat_one (show k + 1 < 2 ^ 6 by simpa using hk), dot,
        Nat.add_zero, ofK_zero, ofK_one, one_mul, Nat.one_mul, add_zero] at e
      rw [e, Finset.sum_range_succ, ← ih (by omega), ← hP (k + 1) hk, add_comm]
      congr 2
      omega
  rw [show p.e + 130 * sz bs + 195 = p.e + 66 * sz bs + 131 + 64 * sz bs + 1 + 63 by ring,
    hacc 63 (by norm_num), ringWeight_sum r rp _ (by rw [hr, hrp]), hr]
  have hlen : (ringCoefficients chs).length = 64 := by simp [ringCoefficients, kBits]
  rw [hlen]

end Lvm.Loop.QRing
