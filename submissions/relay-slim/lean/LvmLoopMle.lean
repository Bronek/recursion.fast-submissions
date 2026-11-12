import LvmLoopSound

/-!
# Multilinear extensions and the closed forms of the fixed columns

`mle r f` (`LvmLoopTable`) is the multilinear extension of the table `f` on `[0, 2^|r|)` at `r`, bit
`i` of the row index the variable `r_i`; (`eqW` is the `eq` kernel of the usual form `Σ_x eq(r, x)·f x`.)

* `mle_split`: the extension at `r₁ ++ r₂` is the extension over the high bits of the extensions over
  the low bits (the tensor rule that makes a piece's columns `tpl ⊗ power`).
* `mle_pow`: the power column `x ↦ c^x` has extension `powEval` (`Π_b (1 - r_b + r_b c^{2^b})`).
* `mle_box`: the column `j ↦ g^{dot s (unflat D j)}` has extension `boxEval D s`.
* **`pieceEval_eq`**: for every piece, every address column (result or operand) and every constant
  column, `pieceEval` is the extension of the fixed column (`fval`) at the piece's point.
* `mle_fixmul`: a `fixmul` piece's multiplier column has extension `Σ_c eq(r_c, c)·mle r_x F_c`,
  a combination of the glue columns' extensions (the self-evaluation identity, `LvmSelfEval`).
-/

namespace Lvm.Loop

open FE Program

/-! ## Basic rules -/

theorem mle_lin : ∀ (r : List FE) (a b : FE) (u w : Nat → FE),
    mle r (fun x => a * u x + b * w x) = a * mle r u + b * mle r w
  | [], _, _, _, _ => rfl
  | r :: rs, a, b, u, w => by
    simp only [mle, mle_lin rs]; ring

theorem mle_smul (r : List FE) (a : FE) (u : Nat → FE) : mle r (fun x => a * u x) = a * mle r u := by
  have := mle_lin r a 0 u u
  simp only [zero_mul, add_zero] at this
  exact this

theorem mle_add (r : List FE) (u w : Nat → FE) : mle r (fun x => u x + w x) = mle r u + mle r w := by
  have := mle_lin r 1 1 u w
  simp only [one_mul] at this
  exact this

theorem mle_const : ∀ (r : List FE) (c : FE), mle r (fun _ => c) = c
  | [], _ => rfl
  | r :: rs, c => by simp only [mle, mle_const rs]; ring

theorem mle_congr : ∀ (r : List FE) {u w : Nat → FE}, (∀ x < 2 ^ r.length, u x = w x) →
    mle r u = mle r w
  | [], _, _, h => h 0 (by simp)
  | r :: rs, u, w, h => by
    simp only [mle]
    rw [mle_congr rs (u := fun x => u (2 * x)) (w := fun x => w (2 * x))
        (fun x hx => h _ (by simp [pow_succ] at hx ⊢; omega)),
      mle_congr rs (u := fun x => u (2 * x + 1)) (w := fun x => w (2 * x + 1))
        (fun x hx => h _ (by simp [pow_succ] at hx ⊢; omega))]

/-- **The tensor rule.** -/
theorem mle_split : ∀ (r₁ r₂ : List FE) (f : Nat → FE),
    mle (r₁ ++ r₂) f = mle r₂ (fun y => mle r₁ (fun x => f (x + 2 ^ r₁.length * y)))
  | [], r₂, f => by simp [mle]
  | r :: r₁, r₂, f => by
    simp only [List.cons_append, mle, mle_split r₁ r₂, List.length_cons]
    rw [← mle_lin]
    congr 1; funext y
    congr 2 <;> (congr 1; funext x; congr 1; ring)

/-! ## Power and box columns -/

theorem ofK_mul' (a b : FK) : FE.ofK (a * b) = FE.ofK a * FE.ofK b := map_mul Lvm.FE.ofKRingHom a b

theorem ofK_one' : FE.ofK 1 = 1 := rfl

theorem mle_pow : ∀ (r : List FE) (c : FK), mle r (fun x => FE.ofK (c ^ x)) = powEval r c
  | [], _ => by simp [mle, powEval]; rfl
  | r :: rs, c => by
    simp only [mle, powEval]
    have h1 : (fun x => FE.ofK (c ^ (2 * x))) = fun x => FE.ofK ((c * c) ^ x) := by
      funext x; rw [pow_mul, sq]
    have h2 : (fun x => FE.ofK (c ^ (2 * x + 1))) = fun x => FE.ofK c * FE.ofK ((c * c) ^ x) := by
      funext x; rw [← ofK_mul', pow_succ, pow_mul, sq, mul_comm]
    rw [h1, h2, mle_smul, mle_pow rs]
    ring

/-- **The box rule**: the column `j ↦ g^{dot s (unflat D j)}` has extension `boxEval D s`. -/
theorem mle_box : ∀ (D s : List Nat) (r : List FE), r.length = D.sum →
    mle r (fun jf => FE.ofK (FK.x ^ dot s (unflat D jf))) = boxEval D s r
  | [], s, r, h => by
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    cases s <;> simp [mle, unflat, dot, boxEval] <;> rfl
  | d :: ds, [], r, _ => by
    simp only [dot, boxEval]
    rw [show (fun _ : Nat => FE.ofK (FK.x ^ 0)) = fun _ => (1 : FE) by funext; simp; rfl]
    exact mle_const r 1
  | d :: ds, s :: ss, r, h => by
    simp only [List.sum_cons] at h
    have ht : (r.take d).length = d := by simp; omega
    have hd : (r.drop d).length = ds.sum := by simp; omega
    conv_lhs => rw [← List.take_append_drop d r]
    rw [mle_split, ht]
    have inner : ∀ y, mle (r.take d) (fun x => FE.ofK (FK.x ^ dot (s :: ss) (unflat (d :: ds)
        (x + 2 ^ d * y)))) = FE.ofK (FK.x ^ dot ss (unflat ds y)) * powEval (r.take d) (FK.x ^ s) := by
      intro y
      rw [← mle_pow, ← mle_smul]
      apply mle_congr
      intro x hx
      rw [ht] at hx
      have h1 : (x + 2 ^ d * y) % 2 ^ d = x := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
      have h2 : (x + 2 ^ d * y) / 2 ^ d = y := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos d), Nat.div_eq_of_lt hx, Nat.zero_add]
      simp only [unflat, dot, h1, h2, pow_add, ofK_mul', pow_mul]
      ring
    simp only [inner]
    rw [show (fun y => FE.ofK (FK.x ^ dot ss (unflat ds y)) * powEval (r.take d) (FK.x ^ s)) =
      fun y => powEval (r.take d) (FK.x ^ s) * FE.ofK (FK.x ^ dot ss (unflat ds y)) by
        funext y; ring, mle_smul, mle_box ds ss _ hd, boxEval]

theorem dot_scaledStrides : ∀ (D j : List Nat) (w : Nat), j.length = D.length →
    dot (scaledStrides D w) j = w * flat D j
  | [], [], _, _ => by simp [scaledStrides, dot, flat]
  | d :: ds, j :: js, w, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [scaledStrides, dot, flat, dot_scaledStrides ds js _ h]; ring
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem length_unflat : ∀ (D : List Nat) (n : Nat), (unflat D n).length = D.length
  | [], _ => rfl
  | _ :: ds, n => by simp [unflat, length_unflat ds]

/-! ## The closed forms of a piece's fixed columns -/

namespace Program

variable (Q : Program)

/-- Row `jf + size·i` of a piece is loop index `jf`, template row `ts[i]`. -/
theorem pinst_split (p : Piece) {jf : Nat} (i : Nat) (hjf : jf < (Q.blk p.blk).size) :
    Q.pinst p (jf + 2 ^ (Q.blk p.blk).lsize * i) = Q.inst p.blk jf (p.ts.getD i 0) := by
  have hsz : 0 < (Q.blk p.blk).size := Nat.two_pow_pos _
  have h1 : (jf + (Q.blk p.blk).size * i) % (Q.blk p.blk).size = jf := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjf]
  have h2 : (jf + (Q.blk p.blk).size * i) / (Q.blk p.blk).size = i := by
    rw [Nat.add_mul_div_left _ _ hsz, Nat.div_eq_of_lt hjf, Nat.zero_add]
  simp only [pinst]
  rw [show 2 ^ (Q.blk p.blk).lsize = (Q.blk p.blk).size from rfl, h1, h2]

/-- **The closed forms are the extensions of the fixed columns.** For an address column (the result
or an operand) or a constant column of a piece, at a point of the piece's height. -/
theorem pieceEval_eq (p : Piece) (c : FCol) (hc : c ≠ .F) (r : List FE)
    (hr : r.length = Q.height p) :
    Q.pieceEval p c r = mle r (fun x => FE.ofK (Q.fval p c x)) := by
  set B := Q.blk p.blk
  have hr' : r.length = p.a + B.lsize := hr
  have hJ : (r.take B.lsize).length = B.lsize := by simp; omega
  have hsplit : mle r (fun x => FE.ofK (Q.fval p c x)) = mle (r.drop B.lsize) (fun i =>
      mle (r.take B.lsize) (fun jf => FE.ofK (Q.fval p c (jf + 2 ^ B.lsize * i)))) := by
    conv_lhs => rw [← List.take_append_drop B.lsize r]
    rw [mle_split, hJ]
  rw [hsplit]
  have hfv : ∀ x, Q.fval p c x = Q.fvalBasic p c x := by
    intro x; cases c <;> first | rfl | exact absurd rfl hc
  rcases c with _ | o | _ | _ | _
  · simp only [pieceEval]
    apply congrArg (tplSum _)
    funext i
    have hcol : ∀ jf < 2 ^ (r.take B.lsize).length, FE.ofK (Q.fval p .res (jf + 2 ^ B.lsize * i)) =
        FE.ofK (FK.x ^ (Q.colAffine p .res (p.ts.getD i 0)).1) *
          FE.ofK (FK.x ^ dot (Q.colAffine p .res (p.ts.getD i 0)).2 (unflat B.dims jf)) := by
      intro jf hjf
      rw [hJ] at hjf
      rw [hfv, fvalBasic, Q.pinst_split p i hjf, ← ofK_mul', ← pow_add]
      simp only [colAffine, inst, B]
      rw [dot_scaledStrides _ _ _ (length_unflat _ _), flat_unflat_of_lt _ hjf, Inst.clock_eq_pick]
      cases ((Q.blk p.blk).tpl.getD (p.ts.getD i 0) default).ty <;> simp only [Ty.pick] <;>
        congr 1 <;> ring
    rw [mle_congr _ hcol, mle_smul, mle_box _ _ _ hJ]
  · simp only [pieceEval]
    apply congrArg (tplSum _)
    funext i
    have hcol : ∀ jf < 2 ^ (r.take B.lsize).length, FE.ofK (Q.fval p (.arg o) (jf + 2 ^ B.lsize * i)) =
        FE.ofK (FK.x ^ (Q.colAffine p (.arg o) (p.ts.getD i 0)).1) *
          FE.ofK (FK.x ^ dot (Q.colAffine p (.arg o) (p.ts.getD i 0)).2 (unflat B.dims jf)) := by
      intro jf hjf
      rw [hJ] at hjf
      rw [hfv, fvalBasic, Q.pinst_split p i hjf, ← ofK_mul', ← pow_add]
      rfl
    rw [mle_congr _ hcol, mle_smul, mle_box _ _ _ hJ]
  · simp only [pieceEval]
    apply congrArg (tplSum _)
    funext i
    rw [show Q.fvalBasic p .k (B.size * i) = Q.fvalBasic p .k (0 + 2 ^ B.lsize * i) by
      rw [Nat.zero_add]; rfl]
    have hcol : ∀ jf < 2 ^ (r.take B.lsize).length, FE.ofK (Q.fval p .k (jf + 2 ^ B.lsize * i)) =
        FE.ofK (Q.fvalBasic p .k (0 + 2 ^ B.lsize * i)) := by
      intro jf hjf
      rw [hJ] at hjf
      rw [hfv, fvalBasic, fvalBasic, Q.pinst_split p i hjf, Q.pinst_split p i (Nat.two_pow_pos _)]
      rfl
    rw [mle_congr _ hcol, mle_const]
  · simp only [pieceEval]
    apply congrArg (tplSum _)
    funext i
    rw [show Q.fvalBasic p .k' (B.size * i) = Q.fvalBasic p .k' (0 + 2 ^ B.lsize * i) by
      rw [Nat.zero_add]; rfl]
    have hcol : ∀ jf < 2 ^ (r.take B.lsize).length, FE.ofK (Q.fval p .k' (jf + 2 ^ B.lsize * i)) =
        FE.ofK (Q.fvalBasic p .k' (0 + 2 ^ B.lsize * i)) := by
      intro jf hjf
      rw [hJ] at hjf
      rw [hfv, fvalBasic, fvalBasic, Q.pinst_split p i hjf, Q.pinst_split p i (Nat.two_pow_pos _)]
      rfl
    rw [mle_congr _ hcol, mle_const]
  · exact absurd rfl hc

end Program

end Lvm.Loop
