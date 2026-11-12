-- WP-13b: shared loop, frame and word lemmas of the decoder's `XIR` programs.
-- adapted from rf-k/submissions/flock-recursive/lean@8bff272b: FRXRead.lean (`shr_toWord` … `rd_decS_self`,
-- `LoK`, `hframeK`, `entryK_count`), FRXFwd.lean (`iterL_ind`, `loopK_eq`, word facts) and FRXBary.lean
-- (`loopK_run`), verbatim; namespace `FR.X` → `Lvm.X`. `load_sem`, `store_sem`, `rdK_toWord` are new.
import LvmXField
import LvmXLookup

/-!
# Loops by invariant, heap frames, word arithmetic

* `iterL_ind`, `loopK_eq`, **`loopK_run`**: a `loopK` whose count register holds `K` runs its
  body `K` times; an invariant preserved by the body holds after it.
* `LoK`, **`hframeK`**: store-free code with counted loops and register destinations keeps every
  heap cell.
* `entryK_count`, `inv_entryK`, `inv_decS`, `rd_decS_self`: the loop entry and decrement.
* Word facts: `divu_toWord`, `remu_toWord`, `mul_toWord`, `shr_toWord`, `shl_toWord`,
  `and_one_toWord`, `bit_eq`, `mask_bit`.
-/

namespace Lvm.X

open RecursionFast

attribute [local irreducible] entryK storeM


/-! ## Words -/

theorem shr_toWord {a k : ℕ} (ha : a < 2 ^ 64) (hk : k < 64) :
    XOp.shr.eval (toWord a) (toWord k) = toWord (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_ushiftRight, toNat_toWord ha, toNat_toWord (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk, toNat_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) ha),
    Nat.shiftRight_eq_div_pow]

theorem shl_toWord {a k : ℕ} (hk : k < 64) (hb : a * 2 ^ k < 2 ^ 64) :
    XOp.shl.eval (toWord a) (toWord k) = toWord (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  have ha : a < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by positivity)) hb
  rw [BitVec.toNat_shiftLeft, toNat_toWord ha, toNat_toWord (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt hk, toNat_toWord hb, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hb]

theorem and_one_toWord {a : ℕ} (ha : a < 2 ^ 64) :
    XOp.and.eval (toWord a) 1 = toWord (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_and, toNat_toWord ha, show (1 : Word).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, toNat_toWord (by omega)]

theorem bit_eq (p h : ℕ) : p / 2 ^ h % 2 = if p.testBit h then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases e : p / 2 ^ h % 2 = 1
  · simp [e]
  · simp [e]; omega


/-! ## Heap frames of store-free code with counted loops -/

/-- No store, no tape-length loop, register destinations; `loopK` counters registers. -/
def LoK : XIR → Prop
  | .blk ps => ∀ p ∈ ps, p.dst < regs
  | .load d _ => d < regs
  | .input d _ => d < regs
  | .out _ => True
  | .seq p q => LoK p ∧ LoK q
  | .ite _ p q => LoK p ∧ LoK q
  | .loopK c _ _ b => c < regs ∧ LoK b
  | _ => False

theorem iterL_hframe {f : St → St} {c : ℕ} (hc : c < regs)
    (hf : ∀ s, ∀ x, regs ≤ x → rd (f s).M x = rd s.M x) :
    ∀ k s, ∀ x, regs ≤ x → rd (iterL f c k s).M x = rd s.M x
  | 0, _, _, _ => rfl
  | k + 1, s, x, hx => (iterL_hframe hc hf k _ x hx).trans
      ((rd_decS (by omega) _).trans (hf s x hx))

/-- **Heap frame** for `LoK` code. -/
theorem hframeK (I : Array Word) : ∀ (P : XIR) (s : St), LoK P → ∀ x, regs ≤ x →
    rd (semXIR I P s).M x = rd s.M x
  | .blk _, _, h, _, hx => rd_runPrims_of_not_writes (fun p hp he => by have := h p hp; omega) _
  | .load _ _, _, h, _, hx => rd_set_ne (by simp only [LoK] at h; omega)
  | .input _ _, _, h, _, hx => rd_set_ne (by simp only [LoK] at h; omega)
  | .out _, _, _, _, _ => rfl
  | .seq p q, s, h, x, hx => (hframeK I q _ h.2 x hx).trans (hframeK I p s h.1 x hx)
  | .ite _ p q, s, h, x, hx => by
    simp only [semXIR]; split
    · exact hframeK I q s h.2 x hx
    · exact hframeK I p s h.1 x hx
  | .loopK c n K b, s, h, x, hx => by
    simp only [semXIR]
    rw [iterL_hframe h.1 (fun s' x' hx' => hframeK I b s' h.2 x' hx') _ _ x hx]
    exact entryK_frame _ (by have := h.1; omega) (by simp only [cTmp, regs] at *; omega)
  | .store .., _, h, _, _ => h.elim
  | .loopT .., _, h, _, _ => h.elim

/-- The count of a `loopK` whose count register holds `K`. -/
theorem entryK_count {c n : ℕ} {K : Word} {M : Mem} (hM : Inv M) (hc : 4 < c) (hcr : c < regs)
    (hn : n ≠ c) (hN : rd M n = K) : rd (entryK c n K M) c = K := by
  have hs := hM.1
  unfold entryK
  dsimp only
  have h1 : rd (M.setIfInBounds c K) n = K := by rw [rd_set_ne (Ne.symm hn), hN]
  have h2 : rd (M.setIfInBounds c K) c = K := rd_set_self (by simp only [regs] at *; omega)
  rw [h1, h2, rd_set_self (by simp only [size_set, cTmp, regs] at *; omega)]
  have : XOp.ltu.eval K K = 0 := by simp [XOp.eval]
  rw [this, if_pos rfl, rd_set_ne (by simp only [cTmp]; omega), h2]

theorem inv_entryK {c n : ℕ} {K : Word} {M : Mem} (hM : Inv M) (hc : 4 < c) :
    Inv (entryK c n K M) :=
  inv_of_frame hM (size_entryK ..) fun i hi =>
    entryK_frame _ (by omega) (by simp only [cTmp]; omega)

theorem inv_decS {c : ℕ} {s : St} (hM : Inv s.M) (hc : 4 ≤ c) : Inv (decS c s).M :=
  inv_of_frame hM (size_decS ..) fun i hi => rd_decS (by omega) _

theorem rd_decS_self {c : ℕ} {s : St} (hM : Inv s.M) (hcr : c < regs) {m : ℕ}
    (h : rd s.M c = toWord (m + 1)) (hm : m + 1 < 2 ^ 64) : rd (decS c s).M c = toWord m := by
  have hs := hM.1
  have h1 : rd s.M cOne = 1 := hM.2 0 (by decide)
  simp only [decS]
  rw [rd_set_self (by simp only [regs] at *; omega), h, h1, show (1 : Word) = toWord 1 from rfl,
    sub_toWord hm (by omega)]
  rfl

/-! ## The lookup on a sorted index -/

/-! ## Loops by invariant -/

theorem iterL_ind {f : St → St} {c m : ℕ} (P : ℕ → St → Prop)
    (h : ∀ j s, j < m → P j s → P (j + 1) (decS c (f s))) :
    ∀ k j s, j + k ≤ m → P j s → P (j + k) (iterL f c k s)
  | 0, _, _, _, hP => hP
  | k + 1, j, s, hk, hP => by
    rw [show j + (k + 1) = (j + 1) + k by omega]
    exact iterL_ind P h k (j + 1) _ (by omega) (h j s (by omega) hP)

theorem loopK_eq (I : Array Word) {c n : ℕ} {K : Word} (b : XIR) (s : St) (hM : Inv s.M)
    (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hN : rd s.M n = K) :
    semXIR I (.loopK c n K b) s = iterL (semXIR I b) c K.toNat ⟨entryK c n K s.M, s.o⟩ := by
  simp only [semXIR, entryK_count hM hc hcr hn hN]


/-! ## Word facts -/

theorem divu_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.divu.eval (toWord a) (toWord b) = toWord (a / b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_udiv, toNat_toWord ha, toNat_toWord hb,
    toNat_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem remu_toWord {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    XOp.remu.eval (toWord a) (toWord b) = toWord (a % b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [XOp.eval]
  rw [BitVec.toNat_umod, toNat_toWord ha, toNat_toWord hb,
    toNat_toWord (lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem mul_toWord (a b : ℕ) : XOp.mul.eval (toWord a) (toWord b) = toWord (a * b) :=
  (BitVec.ofNat_mul a b).symm

/-- The branch-free bit mask: `v` if bit `j` of `b` is set, else `0`. -/
theorem mask_bit (v : Word) {b j : ℕ} (hb : b < 2 ^ 64) (hj : j < 64) :
    XOp.and.eval v (XOp.sub.eval 0 (XOp.and.eval (XOp.shr.eval (toWord b) (toWord j)) 1)) =
      if b.testBit j then v else 0 := by
  rw [shr_toWord hb hj, and_one_toWord (lt_of_le_of_lt (Nat.div_le_self _ _) hb), bit_eq]
  by_cases h : b.testBit j
  · rw [if_pos h, if_pos h]
    show v &&& (0 - toWord 1) = v
    rw [show (0 : Word) - toWord 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
  · rw [if_neg h, if_neg h]
    show v &&& (0 - toWord 0) = 0
    rw [show (0 : Word) - toWord 0 = 0 by decide]
    exact BitVec.eq_of_toNat_eq (by simp)

theorem xor_zero' (a : Word) : a ^^^ 0 = a := BitVec.eq_of_toNat_eq (by simp)


/-! ## Helpers -/

/-- **A generic `loopK` run**: an invariant `P` preserved by the body for `j < K` holds after the
loop. -/
theorem loopK_run (I : Array Word) {c n K : ℕ} (b : XIR) (P : ℕ → St → Prop) (s : St)
    (hM : Inv s.M) (hc : 4 < c) (hcr : c < regs) (hn : n ≠ c) (hN : rd s.M n = toWord K)
    (hK : K < 2 ^ 64) (h0 : P 0 ⟨entryK c n (toWord K) s.M, s.o⟩)
    (hstep : ∀ j s, j < K → P j s → P (j + 1) (decS c (semXIR I b s))) :
    P K (semXIR I (.loopK c n (toWord K) b) s) := by
  rw [loopK_eq I b s hM hc hcr hn hN, toNat_toWord hK]
  simpa using iterL_ind P hstep K 0 _ (by omega) h0

theorem toWord_zero' : toWord 0 = (0 : Word) := rfl

theorem toWord_mul' (a b : ℕ) : toWord a * toWord b = toWord (a * b) := (BitVec.ofNat_mul a b).symm

/-! ## One-word heap loads and stores (a `K` element is one word) -/

/-- **A heap load** `d := M[M[p]]` (`M[p] = x`). -/
theorem load_sem (I : Array Word) (s : St) (hM : Inv s.M) {d p x : ℕ} (hd : 4 ≤ d)
    (hdr : d < regs) (hP : rd s.M p = toWord x) (hx2 : x < 2 ^ 64) :
    rd (semXIR I (.load d p) s).M d = rd s.M x ∧
    (∀ i, i ≠ d → rd (semXIR I (.load d p) s).M i = rd s.M i) ∧
    Inv (semXIR I (.load d p) s).M := by
  have hs := hM.1
  have e : semXIR I (.load d p) s = ⟨s.M.setIfInBounds d (rd s.M (rd s.M p).toNat), s.o⟩ := rfl
  refine ⟨?_, fun i hi => ?_, inv_sem I (P := .load d p) hd hM⟩ <;> rw [e]
  · rw [rd_set_self (by simp only [regs] at *; omega), hP, toNat_toWord hx2]
  · exact rd_set_ne (Ne.symm hi)

/-- **A heap store** `M[M[p]] := M[v]` (`M[p] = x ≥ regs`); the compiler's scratch `cTmp` and
the cell `x` change, nothing else. -/
theorem store_sem (I : Array Word) (s : St) (hM : Inv s.M) {p v x : ℕ} (hpT : p ≠ cTmp)
    (hvT : v ≠ cTmp) (hP : rd s.M p = toWord x) (hx : regs ≤ x) (hx2 : x < 2 ^ 64)
    (hxs : x < s.M.size) :
    rd (semXIR I (.store p v) s).M x = rd s.M v ∧
    (∀ i, i ≠ x → i ≠ cTmp → rd (semXIR I (.store p v) s).M i = rd s.M i) ∧
    Inv (semXIR I (.store p v) s).M := by
  have e : semXIR I (.store p v) s = ⟨storeM s.M p v, s.o⟩ := rfl
  have hxT : x ≠ cTmp := by simp only [regs, cTmp] at *; omega
  refine ⟨?_, fun i hi hiT => ?_, inv_sem I (P := .store p v) hpT hM⟩ <;> rw [e]
  · rw [rd_storeM hM hP hx hx2 hxs hpT hvT hxT, if_pos rfl]
  · rw [rd_storeM hM hP hx hx2 hxs hpT hvT hiT, if_neg hi]

/-- `ptK`'s words: the domain point of `j` is the word `j` read as a `K` element. -/
theorem rdK_toWord {M : Mem} {a j : ℕ} (h : rd M a = toWord j) :
    rdK M a = BF64.ofBitVec (BitVec.ofNat 64 j) := by
  rw [rdK, h]; rfl

end Lvm.X
