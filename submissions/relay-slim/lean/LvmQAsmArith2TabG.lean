-- New for lvm (HAR-BT): `CPoly` evaluation gadgets over a table's evaluation cells (QL's builder):
-- monomials scaled or not, geometric (`BITS` output) suffixes by suffix sums, a fresh evaluation
-- with a one-row `a·b + c` start (the `BITS` bit constraints), Horner over a table's constraints.
-- Searched QA2's `LvmQBusGkr` (`hornerG`, `prodG`: lists of cells, reused in spirit), QA1's `LvmQKeccakTB`
-- (template builder): no `CPoly` evaluator to adapt.
import LvmQAsmArith2TabF

/-!
# Evaluating `CPoly`s on cells

`ev i` is the cell of column `i` (value `col i`), `sc k` the suffix-sum cell `S k` (`Sv col k`, `k ≤ 64`).

* `prodAccG t vs acc`: `acc + t·Π_{v∈vs} col v`; `monAccS A acc m`: `acc + A·m(col)`;
  `monAccU acc m`: `acc + m(col)` (one row for `c·x_i`, `x_i x_j`, a constant).
* `geoMatch P`: `P = pre ++ geoPoly a e d` (checked); `geoAccU`/`geoAccS`: the suffix by `S`
  (`x^d (S a + x^{e−a} S e)`: two rows, three when scaled).
* `polyAccU`, `polyAccS`: `acc + P(col)`, `acc + A·P(col)`; `polyFresh`: `P(col)` (a first
  `x_i x_j` and `x_k` in one row: `β_z² + β_z`); `hornerC`: `Σ_c ξ^c C_c(col)`.
-/

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.M3 Lvm.Loop Lvm.Loop.Build

/-! ## Monomials -/

/-- `acc + t·Π_{v∈vs} ev v`. -/
def prodAccG (z : Cell) (ev : Nat → Cell) : Cell → List Nat → Cell → BM Cell
  | t, [], acc => lin .E 1 0 acc t
  | t, [v], acc => mulAdd .E t (ev v) acc
  | t, v :: w :: vs, acc => do
    let t' ← mulAdd .E t (ev v) z
    prodAccG z ev t' (w :: vs) acc

/-- `k·A` (no row for `k = 1`). -/
def scaleC (z : Cell) (k : FK) (A : Cell) : BM Cell := if k = 1 then pure A else lin .E k 0 z A

/-- `acc + A·m(ev)`. -/
def monAccS (z : Cell) (ev : Nat → Cell) (A acc : Cell) (m : FK × List Nat) : BM Cell :=
  scaleC z m.1 A >>= fun t => prodAccG z ev t m.2 acc

/-- `acc + m(ev)`. -/
def monAccU (z : Cell) (ev : Nat → Cell) (acc : Cell) : FK × List Nat → BM Cell
  | (c, []) => lin .E 0 c acc acc
  | (c, [i]) => lin .E c 0 acc (ev i)
  | (c, [i, j]) => if c = 1 then mulAdd .E (ev i) (ev j) acc else do
      let t ← lin .E c 0 z (ev i)
      mulAdd .E t (ev j) acc
  | (c, i :: vs) => do
      let t ← lin .E c 0 z (ev i)
      prodAccG z ev t vs acc

/-- The monomials one by one, unscaled. -/
def monsAccU (z : Cell) (ev : Nat → Cell) : Cell → CPoly → BM Cell
  | acc, [] => pure acc
  | acc, m :: ms => do
    let acc' ← monAccU z ev acc m
    monsAccU z ev acc' ms

/-- The monomials one by one, scaled by `A`. -/
def monsAccS (z : Cell) (ev : Nat → Cell) (A : Cell) : Cell → CPoly → BM Cell
  | acc, [] => pure acc
  | acc, m :: ms => do
    let acc' ← monAccS z ev A acc m
    monsAccS z ev A acc' ms

section
variable {c : Ctx} {M : Mem} {z : Cell} {ev : Nat → Cell} {col : Nat → FE}

theorem prodAccG_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) :
    ∀ (vs : List Nat) (t acc : Cell),
      SoundG c M (prodAccG z ev t vs acc) fun r =>
        r.val M = acc.val M + t.val M * (vs.map col).foldl (· * ·) 1
  | [], t, acc => fun p hH _ => by
    simp only [prodAccG] at hH ⊢
    rw [lin_spec hH, ofK_one, ofK_zero]; simp
  | [v], t, acc => fun p hH _ => by
    simp only [prodAccG] at hH ⊢
    rw [mulAdd_spec hH, hev]; simp; ring
  | v :: w :: vs, t, acc => by
    show SoundG c M (mulAdd .E t (ev v) z >>= fun t' => prodAccG z ev t' (w :: vs) acc) _
    refine soundG_bind (soundG_mono (soundG_aspec (QB.aspec_mulAdd .E t (ev v) z)) fun _ h => h.1)
      fun t' ht' => soundG_mono (prodAccG_sound hz hev (w :: vs) t' acc) fun r hr => ?_
    rw [hr, ht', hev, hz, add_zero]
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_mul_one _ (1 * col w), foldl_mul_one _ (1 * col v * col w)]
    ring

theorem monAccS_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (A acc : Cell)
    (m : FK × List Nat) :
    SoundG c M (monAccS z ev A acc m) fun r => r.val M = acc.val M + A.val M * monV col m := by
  unfold monAccS
  have h1 : SoundG c M (scaleC z m.1 A) (fun t => t.val M = FE.ofK m.1 * A.val M) := by
    unfold scaleC
    split
    · rename_i h
      exact soundG_pure (by rw [h, ofK_one, one_mul])
    · exact soundG_mono (soundG_aspec (QB.aspec_lin .E m.1 0 z A)) fun x h => by
        rw [h.1, hz, ofK_zero]; ring
  refine soundG_bind h1 fun t ht => soundG_mono (prodAccG_sound hz hev m.2 t acc) fun r hr => ?_
  rw [hr, ht, monV]; ring

theorem monAccU_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (acc : Cell) :
    ∀ m : FK × List Nat, SoundG c M (monAccU z ev acc m) fun r => r.val M = acc.val M + monV col m
  | (k, []) => fun p hH _ => by
    simp only [monAccU] at hH ⊢; rw [lin_spec hH, monV]; simp [ofK_zero]
  | (k, [i]) => fun p hH _ => by
    simp only [monAccU] at hH ⊢; rw [lin_spec hH, monV, hev]; simp [ofK_zero]
  | (k, [i, j]) => by
    rw [show monAccU z ev acc (k, [i, j]) = (if k = 1 then mulAdd .E (ev i) (ev j) acc else
      (lin .E k 0 z (ev i) >>= fun t => mulAdd .E t (ev j) acc)) from rfl]
    split
    · rename_i h; subst h
      exact fun p hH _ => by
        simp only at hH ⊢; rw [mulAdd_spec hH, hev, hev, monV]; simp [ofK_one]; ring
    · refine soundG_bind (soundG_mono (soundG_aspec (QB.aspec_lin .E k 0 z (ev i))) fun _ h => h.1)
        fun t ht => soundG_mono (soundG_aspec (QB.aspec_mulAdd .E t (ev j) acc)) fun r hr => ?_
      rw [hr.1, ht, hz, hev, hev, monV, ofK_zero]; simp; ring
  | (k, i :: w :: x :: vs) => by
    show SoundG c M (lin .E k 0 z (ev i) >>= fun t => prodAccG z ev t (w :: x :: vs) acc) _
    refine soundG_bind (soundG_mono (soundG_aspec (QB.aspec_lin .E k 0 z (ev i))) fun _ h => h.1)
      fun t ht => soundG_mono (prodAccG_sound hz hev _ t acc) fun r hr => ?_
    rw [hr, ht, hz, hev, monV, ofK_zero]
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_mul_one _ (1 * col w * col x), foldl_mul_one _ (1 * col i * col w * col x)]
    ring

theorem monsAccU_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) :
    ∀ (P : CPoly) (acc : Cell),
      SoundG c M (monsAccU z ev acc P) fun r => r.val M = acc.val M + CPoly.evalE col P
  | [], acc => soundG_pure (by rw [evalE_nil, add_zero])
  | m :: ms, acc => soundG_bind (monAccU_sound hz hev acc m) fun a ha =>
      soundG_mono (monsAccU_sound hz hev ms a) fun r hr => by rw [hr, ha, evalE_cons]; ring

theorem monsAccS_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (A : Cell) :
    ∀ (P : CPoly) (acc : Cell),
      SoundG c M (monsAccS z ev A acc P) fun r => r.val M = acc.val M + A.val M * CPoly.evalE col P
  | [], acc => soundG_pure (by rw [evalE_nil, mul_zero, add_zero])
  | m :: ms, acc => soundG_bind (monAccS_sound hz hev A acc m) fun a ha =>
      soundG_mono (monsAccS_sound hz hev A ms a) fun r hr => by rw [hr, ha, evalE_cons]; ring

end

/-! ## Geometric suffixes -/

/-- **Recognise a geometric suffix** (checked: the result is `P = pre ++ geoPoly a e d`). -/
def geoMatch (P : CPoly) : Option (CPoly × Nat × Nat × Nat) :=
  let g := P.drop (P.length - 64)
  let a := g.findIdx (·.1 != 0)
  let e := 64 - g.reverse.findIdx (·.1 != 0)
  let d := (g.getD a (0, [])).1.val.toNat.log2
  if 64 ≤ P.length ∧ a ≤ e ∧ e ≤ 64 ∧ e - a + d ≤ 64 ∧ g = geoPoly a e d then
    some (P.take (P.length - 64), a, e, d) else none

theorem geoMatch_spec {P pre : CPoly} {a e d : Nat} (h : geoMatch P = some (pre, a, e, d)) :
    P = pre ++ geoPoly a e d ∧ a ≤ e ∧ e ≤ 64 ∧ e - a + d ≤ 64 := by
  unfold geoMatch at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨(List.take_append_drop _ P).symm.trans (congrArg _ hc.2.2.2.2), hc.2.1, hc.2.2.1,
      hc.2.2.2.1⟩
  · simp at h

/-- `S a + x^{e−a} S e`. -/
def geoT (sc : Nat → Cell) (a e : Nat) : BM Cell :=
  if e < 64 then lin .E (Bits.wt (e - a)) 0 (sc a) (sc e) else pure (sc a)

/-- `acc + x^d (S a + x^{e−a} S e)`. -/
def geoAccU (sc : Nat → Cell) (acc : Cell) (a e d : Nat) : BM Cell :=
  geoT sc a e >>= fun t => lin .E (Bits.wt d) 0 acc t

/-- `acc + A · x^d (S a + x^{e−a} S e)`. -/
def geoAccS (z : Cell) (sc : Nat → Cell) (A acc : Cell) (a e d : Nat) : BM Cell := do
  let t ← geoT sc a e
  let u ← scaleC z (Bits.wt d) A
  mulAdd .E u t acc

section
variable {c : Ctx} {M : Mem} {z : Cell} {sc : Nat → Cell} {col : Nat → FE}

theorem geoT_sound (hsc : ∀ k ≤ 64, (sc k).val M = Sv col k) {a e : Nat} (hae : a ≤ e) (he : e ≤ 64) :
    SoundG c M (geoT sc a e) fun t => t.val M = Sv col a + gen ^ (e - a) * Sv col e := by
  unfold geoT
  split
  · rename_i h
    exact soundG_mono (soundG_aspec (QB.aspec_lin .E _ 0 _ _)) fun t ht => by
      rw [ht.1, hsc a (by omega), hsc e (by omega), ofK_wt (by omega), ofK_zero, add_zero]
  · rename_i h
    exact soundG_pure (by rw [show e = 64 by omega, Sv_64, mul_zero, add_zero, hsc a (by omega)])

theorem geo_zero {a : Nat} (k : FE) : k * (Sv col a + gen ^ (a - a) * Sv col a) = 0 := by
  rw [Nat.sub_self, pow_zero, one_mul, CharTwo.add_self_eq_zero, mul_zero]

theorem geoAccU_sound (hsc : ∀ k ≤ 64, (sc k).val M = Sv col k) (acc : Cell) {a e d : Nat}
    (hae : a ≤ e) (he : e ≤ 64) (hd : e - a + d ≤ 64) :
    SoundG c M (geoAccU sc acc a e d) fun r =>
      r.val M = acc.val M + gen ^ d * (Sv col a + gen ^ (e - a) * Sv col e) :=
  soundG_bind (geoT_sound hsc hae he) fun t ht =>
    soundG_mono (soundG_aspec (QB.aspec_lin .E _ 0 acc t)) fun r hr => by
      rw [hr.1, ht, ofK_zero, add_zero]
      rcases Nat.lt_or_ge a e with h | h
      · rw [ofK_wt (by omega)]
      · obtain rfl : a = e := by omega
        rw [geo_zero, geo_zero]

theorem scaleC_sound (hz : z.val M = 0) (k : FK) (A : Cell) :
    SoundG c M (scaleC z k A) fun t => t.val M = FE.ofK k * A.val M := by
  unfold scaleC
  split
  · rename_i h
    exact soundG_pure (by rw [h, ofK_one, one_mul])
  · exact soundG_mono (soundG_aspec (QB.aspec_lin .E k 0 z A)) fun x h => by
      rw [h.1, hz, ofK_zero]; ring

theorem geoAccS_sound (hz : z.val M = 0) (hsc : ∀ k ≤ 64, (sc k).val M = Sv col k) (A acc : Cell)
    {a e d : Nat} (hae : a ≤ e) (he : e ≤ 64) (hd : e - a + d ≤ 64) :
    SoundG c M (geoAccS z sc A acc a e d) fun r =>
      r.val M = acc.val M + A.val M * (gen ^ d * (Sv col a + gen ^ (e - a) * Sv col e)) :=
  soundG_bind (geoT_sound hsc hae he) fun t ht =>
    soundG_bind (scaleC_sound hz _ A) fun u hu =>
      soundG_mono (soundG_aspec (QB.aspec_mulAdd .E u t acc)) fun r hr => by
        rw [hr.1, hu, ht]
        rcases Nat.lt_or_ge a e with h | h
        · rw [ofK_wt (by omega)]; ring
        · obtain rfl : a = e := by omega
          rw [Nat.sub_self, pow_zero, one_mul, CharTwo.add_self_eq_zero]; ring

end

/-! ## Polynomials -/

/-- `acc + P(ev)`. -/
def polyAccU (z : Cell) (ev sc : Nat → Cell) (acc : Cell) (P : CPoly) : BM Cell :=
  match geoMatch P with
  | some (pre, a, e, d) => monsAccU z ev acc pre >>= fun r => geoAccU sc r a e d
  | none => monsAccU z ev acc P

/-- `acc + A·P(ev)`. -/
def polyAccS (z : Cell) (ev sc : Nat → Cell) (A acc : Cell) (P : CPoly) : BM Cell :=
  match geoMatch P with
  | some (pre, a, e, d) => monsAccS z ev A acc pre >>= fun r => geoAccS z sc A r a e d
  | none => monsAccS z ev A acc P

/-- `P(ev)`, a first `c x_i` or `x_i x_j + x_k` at no or one row. -/
def monsFresh (z : Cell) (ev : Nat → Cell) : CPoly → BM Cell
  | [] => pure z
  | (k, [i]) :: ms => if k = 1 then monsAccU z ev (ev i) ms else monsAccU z ev z ((k, [i]) :: ms)
  | (k, [i, j]) :: (k', [l]) :: ms =>
    if k = 1 ∧ k' = 1 then mulAdd .E (ev i) (ev j) (ev l) >>= fun r => monsAccU z ev r ms
    else monsAccU z ev z ((k, [i, j]) :: (k', [l]) :: ms)
  | ms => monsAccU z ev z ms

/-- `P(ev)`. -/
def polyFresh (z : Cell) (ev sc : Nat → Cell) (P : CPoly) : BM Cell :=
  match geoMatch P with
  | some (pre, a, e, d) => monsFresh z ev pre >>= fun r => geoAccU sc r a e d
  | none => monsFresh z ev P

/-- **Horner over constraints**: `Σ_c ξ^c C_c(ev)`. -/
def hornerC (z : Cell) (ev sc : Nat → Cell) (xi : Cell) : List CPoly → BM Cell
  | [] => pure z
  | [C] => polyFresh z ev sc C
  | C :: D :: Cs => do
    let h ← hornerC z ev sc xi (D :: Cs)
    let c ← polyFresh z ev sc C
    mulAdd .E xi h c

/-- The suffix sums `S (64 − n) … S 63` (`S 64` is the zero cell). -/
def sufG (z : Cell) (ev : Nat → Cell) : Nat → BM (List Cell)
  | 0 => pure []
  | n + 1 => do
    let l ← sufG z ev n
    let s ← lin .E FK.x 0 (ev (1 + (63 - n))) (l.headD z)
    pure (s :: l)

section
variable {c : Ctx} {M : Mem} {z : Cell} {ev sc : Nat → Cell} {col : Nat → FE}

theorem polyAccU_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (acc : Cell) (P : CPoly)
    (hsc : (geoMatch P).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k) :
    SoundG c M (polyAccU z ev sc acc P) fun r => r.val M = acc.val M + CPoly.evalE col P := by
  unfold polyAccU
  split
  · rename_i pre a e d hm
    obtain ⟨hP, hae, he, hd⟩ := geoMatch_spec hm
    exact soundG_bind (monsAccU_sound hz hev pre acc) fun r hr =>
      soundG_mono (geoAccU_sound (hsc (by rw [hm]; rfl)) r hae he hd) fun x hx => by
        rw [hx, hr, hP, evalE_append, evalE_geo col hae he hd]; ring
  · exact monsAccU_sound hz hev P acc

theorem polyAccS_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (A acc : Cell) (P : CPoly)
    (hsc : (geoMatch P).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k) :
    SoundG c M (polyAccS z ev sc A acc P) fun r =>
      r.val M = acc.val M + A.val M * CPoly.evalE col P := by
  unfold polyAccS
  split
  · rename_i pre a e d hm
    obtain ⟨hP, hae, he, hd⟩ := geoMatch_spec hm
    exact soundG_bind (monsAccS_sound hz hev A pre acc) fun r hr =>
      soundG_mono (geoAccS_sound hz (hsc (by rw [hm]; rfl)) A r hae he hd) fun x hx => by
        rw [hx, hr, hP, evalE_append, evalE_geo col hae he hd]; ring
  · exact monsAccS_sound hz hev A P acc

theorem monsFresh_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (P : CPoly) :
    SoundG c M (monsFresh z ev P) fun r => r.val M = CPoly.evalE col P := by
  have hz0 : ∀ Q : CPoly, SoundG c M (monsAccU z ev z Q) fun r => r.val M = CPoly.evalE col Q :=
    fun Q => soundG_mono (monsAccU_sound hz hev Q z) fun r hr => by rw [hr, hz, zero_add]
  unfold monsFresh
  split
  · exact soundG_pure (by rw [hz, evalE_nil])
  · rename_i k i ms
    split
    · rename_i hk
      exact soundG_mono (monsAccU_sound hz hev ms (ev i)) fun r hr => by
        rw [hr, hev, evalE_cons, monV, hk]; simp [ofK_one]
    · exact hz0 _
  · rename_i k i j k' l ms
    split
    · rename_i hk
      exact soundG_bind (soundG_aspec (QB.aspec_mulAdd .E (ev i) (ev j) (ev l))) fun r hr =>
        soundG_mono (monsAccU_sound hz hev ms r) fun x hx => by
          rw [hx, hr.1, hev, hev, hev, evalE_cons, evalE_cons, monV, monV, hk.1, hk.2]
          simp [ofK_one]; ring
    · exact hz0 _
  · exact hz0 _

theorem polyFresh_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (P : CPoly)
    (hsc : (geoMatch P).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k) :
    SoundG c M (polyFresh z ev sc P) fun r => r.val M = CPoly.evalE col P := by
  unfold polyFresh
  split
  · rename_i pre a e d hm
    obtain ⟨hP, hae, he, hd⟩ := geoMatch_spec hm
    exact soundG_bind (monsFresh_sound hz hev pre) fun r hr =>
      soundG_mono (geoAccU_sound (hsc (by rw [hm]; rfl)) r hae he hd) fun x hx => by
        rw [hx, hr, hP, evalE_append, evalE_geo col hae he hd]
  · exact monsFresh_sound hz hev P

theorem hornerC_sound (hz : z.val M = 0) (hev : ∀ i, (ev i).val M = col i) (xi : Cell) :
    ∀ Cs : List CPoly, (∀ C ∈ Cs, (geoMatch C).isSome = true → ∀ k ≤ 64, (sc k).val M = Sv col k) →
      SoundG c M (hornerC z ev sc xi Cs) fun r =>
        r.val M = polyEval (Cs.map (CPoly.evalE col)) (xi.val M)
  | [], _ => soundG_pure (by rw [hz]; rfl)
  | [C], hsc => soundG_mono (polyFresh_sound hz hev C (hsc C List.mem_cons_self)) fun r hr => by
      rw [hr]; simp [polyEval]
  | C :: D :: Cs, hsc => soundG_bind (hornerC_sound hz hev xi (D :: Cs)
      fun C' h => hsc C' (List.mem_cons_of_mem _ h)) fun h hh =>
      soundG_bind (polyFresh_sound hz hev C (hsc C List.mem_cons_self)) fun c' hc =>
        soundG_mono (soundG_aspec (QB.aspec_mulAdd .E xi h c')) fun r hr => by
          rw [hr.1, hh, hc]
          simp only [List.map_cons, polyEval, List.foldr_cons]
          ring

theorem sufG_sound (hev : ∀ i, (ev i).val M = col i) (hz : z.val M = 0) :
    ∀ n ≤ 64, SoundG c M (sufG z ev n) fun l =>
      l.length = n ∧ ∀ i < n, (l.getD i z).val M = Sv col (64 - n + i)
  | 0, _ => soundG_pure ⟨rfl, fun i hi => absurd hi (by omega)⟩
  | n + 1, hn => soundG_bind (sufG_sound hev hz n (by omega)) fun l hl =>
      soundG_bind (soundG_aspec (QB.aspec_lin .E FK.x 0 (ev (1 + (63 - n))) (l.headD z)))
        fun s hs => soundG_pure ⟨by simp [hl.1], fun i hi => by
          rcases i with _ | i
          · simp only [List.getD_cons_zero]
            have hh : (l.headD z).val M = Sv col (64 - n) := by
              rcases l with _ | ⟨x, l'⟩
              · have : n = 0 := by simpa using hl.1.symm
                subst this; simp [hz, Sv_64]
              · have := hl.2 0 (by simp at hl; omega)
                simpa using this
            rw [show 64 - (n + 1) + 0 = 63 - n by omega, Sv_succ col (by omega : 63 - n < 64),
              show 63 - n + 1 = 64 - n by omega, hs.1, hev, ofK_zero, add_zero, hh]
            rfl
          · simp only [List.getD_cons_succ]
            rw [hl.2 i (by omega), show 64 - (n + 1) + (i + 1) = 64 - n + i by omega]⟩

end

end Lvm.Har
