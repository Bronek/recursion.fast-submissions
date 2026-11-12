-- Vendored for lvm2 (WP JB-L) from Flock `submissions/flock-recursive/lean/JBHeight.lean` @ 1b74a2a2 (archive/pcs/S1P), Flock's port (PJB) of
-- longfellow-zk `formal/ligero` @ 1c06629 (Copyright Google LLC; Apache License 2.0, see
-- `LICENSE-longfellow`). Changed: imports `JB*` renamed `LvmJB*`; nothing else.
import LvmJBResultant

/-!
# Heights and the concrete branch bound `B`

The §3 incidence count needs a *column bound*: a number `B` such that a nonzero
`g_x` can vanish under at most `B` branch specialisations.  §2 supplies the shape of
`B` — it is the `Z`-degree of a resultant — and this file supplies the estimate.

## The `Z`-height

For `p : F[Z][T]`, `IsHeightLE p a` says every coefficient of `p`, as a polynomial in
`Z`, has degree at most `a`.  This is the "height" of §2: *a bound on the `Z`-degree of
the reduced numerator*.

A useful simplification: we never need to reduce modulo `H̃`.  The resultant bound of §2
applies to arbitrary representatives in `F[Z][T]`, so it is enough to track the pair
(`T`-degree, `Z`-height) of an unreduced representative.  This removes the quotient ring
`A = 𝔽_q[Z,T,1/(Wξ)]/(H̃)` from the argument entirely, leaving only polynomials.

## Main results

* the height calculus `IsHeightLE.add`, `.mul`, `.pow`, `.sum` — heights add under
  multiplication and are stable under addition;
* `card_badSpecializations_le_of_height` — the concrete branch bound

    `B ≤ deg_T(g) * ht(H) + deg_T(H) * ht(g)`,

  which has shape `(2r+1) * d_H * d * D` once the height of an order-`r` jet numerator
  is known to be linear in `r`.
-/

namespace JBAgreement

open Polynomial

variable {F : Type*}

/-! ### The height predicate -/

/-- `IsHeightLE p a` : every coefficient of `p : F[Z][T]`, as a polynomial in `Z`, has
degree at most `a`. -/
def IsHeightLE [Semiring F] (p : F[X][X]) (a : ℕ) : Prop :=
  ∀ i, (p.coeff i).natDegree ≤ a

namespace IsHeightLE

variable [CommSemiring F] {p q : F[X][X]} {a b : ℕ}

theorem mono (h : IsHeightLE p a) (hab : a ≤ b) : IsHeightLE p b := fun i => (h i).trans hab

@[simp] theorem zero : IsHeightLE (0 : F[X][X]) a := by intro i; simp

theorem add (hp : IsHeightLE p a) (hq : IsHeightLE q a) : IsHeightLE (p + q) a := by
  intro i
  rw [coeff_add]
  exact natDegree_add_le_of_degree_le (hp i) (hq i)

/-- **Heights add under multiplication.**  Each coefficient of `p * q` is a sum of
products `p.coeff i * q.coeff j`, of `Z`-degree at most `a + b`. -/
theorem mul (hp : IsHeightLE p a) (hq : IsHeightLE q b) : IsHeightLE (p * q) (a + b) := by
  intro n
  rw [coeff_mul]
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact natDegree_mul_le_of_le (hp x.1) (hq x.2)

theorem pow (hp : IsHeightLE p a) : ∀ n : ℕ, IsHeightLE (p ^ n) (n * a)
  | 0 => by
      intro i
      rw [pow_zero, coeff_one]
      split_ifs <;> simp
  | (n + 1) => by
      have := (pow hp n).mul hp
      refine this.mono ?_
      ring_nf
      omega

theorem sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → F[X][X])
    (hf : ∀ i ∈ s, IsHeightLE (f i) a) : IsHeightLE (∑ i ∈ s, f i) a := by
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx]
      exact (hf x (Finset.mem_insert_self x s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end IsHeightLE

/-! ### The concrete branch bound -/

variable [Field F] [Fintype F] [DecidableEq F]

/-- **The column bound `B` of §3, made concrete.**

If `H` has `T`-degree at most `dH` and `Z`-height at most `hH`, and `g` has `T`-degree at
most `dg` and `Z`-height at most `hg`, then the number of specialisations `z` at which
`H(·, z)` and `g(·, z)` acquire a common root is at most

  `dg * hH + dH * hg`.

Instantiated at `g = g_x` this is the bound `B` fed to `card_exceptional_ge`.  The `§3`
shape `(2r+1) * d_H * d * D` is the case where an order-`r` jet numerator has height
linear in `r`, the remaining estimate. -/
theorem card_badSpecializations_le_of_height (H g : F[X][X]) {dH dg hH hg : ℕ}
    (hHdeg : H.natDegree ≤ dH) (hgdeg : g.natDegree ≤ dg)
    (hHht : IsHeightLE H hH) (hght : IsHeightLE g hg)
    (hmn : dH ≠ 0 ∨ dg ≠ 0)
    (hres : resultant H g dH dg ≠ 0) :
    (badSpecializations H g).card ≤ dg * hH + dH * hg :=
  le_trans (card_badSpecializations_le H g hHdeg hgdeg hmn hres)
    (natDegree_resultant_le H g dH dg hHht hght)

end JBAgreement
