import LvmLoopInterp

/-!
# LoopIR tables: the constraint polynomials state the row relations

`Shape.Rel σ v` is a shape's operation as a relation between the values a table row holds: the
result and operand values assembled from their limb columns (`valOf`), and the fixed constants.
`constraints_sound`: on a well-typed shape, if every constraint polynomial vanishes at a row, the
relation holds (`constraints_complete`: and conversely, for the honest prover). The algebra is the
limb formula of the product in `FE = FK[y]/(y^3 + y + 1)` (`mul_c₀`, `mul_c₁`, `mul_c₂`, from
`LvmFieldE`'s Karatsuba product in characteristic 2).
-/

namespace Lvm.Loop

open FE Program

/-! ## Limbs -/

/-- Limb `l` of an `E` value (`c₂` from `l = 2` on). -/
def limb (x : FE) : Nat → FK
  | 0 => x.c₀
  | 1 => x.c₁
  | _ => x.c₂

theorem two_eq_zero_FK : (2 : FK) = 0 := CharTwo.two_eq_zero

theorem mul_c₀ (x y : FE) : (x * y).c₀ = x.c₀ * y.c₀ + x.c₁ * y.c₂ + x.c₂ * y.c₁ := by
  show (FE.mul x y).c₀ = _
  simp only [FE.mul]
  linear_combination (x.c₁ * y.c₁ + x.c₂ * y.c₂) * two_eq_zero_FK

theorem mul_c₁ (x y : FE) :
    (x * y).c₁ = x.c₀ * y.c₁ + x.c₁ * y.c₀ + x.c₁ * y.c₂ + x.c₂ * y.c₁ + x.c₂ * y.c₂ := by
  show (FE.mul x y).c₁ = _
  simp only [FE.mul]
  linear_combination (x.c₀ * y.c₀ + x.c₁ * y.c₁) * two_eq_zero_FK

theorem mul_c₂ (x y : FE) :
    (x * y).c₂ = x.c₀ * y.c₂ + x.c₁ * y.c₁ + x.c₂ * y.c₀ + x.c₂ * y.c₂ := by
  show (FE.mul x y).c₂ = _
  simp only [FE.mul]
  linear_combination (x.c₀ * y.c₀) * two_eq_zero_FK

@[simp] theorem add_c₀ (x y : FE) : (x + y).c₀ = x.c₀ + y.c₀ := rfl
@[simp] theorem add_c₁ (x y : FE) : (x + y).c₁ = x.c₁ + y.c₁ := rfl
@[simp] theorem add_c₂ (x y : FE) : (x + y).c₂ = x.c₂ + y.c₂ := rfl

theorem FE.ext_limb {x y : FE} (h : ∀ l < 3, limb x l = limb y l) : x = y := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  cases x; cases y; simp only [limb] at h0 h1 h2; subst h0 h1 h2; rfl

theorem FK.eq_of_add_eq_zero {a b : FK} (h : a + b = 0) : a = b := by
  linear_combination h - b * two_eq_zero_FK

/-! ## Polynomial evaluation -/

theorem Poly2.ev_append (P R : Poly2) (v : Var → FK) : (P ++ R).ev v = P.ev v + R.ev v := by
  induction P with
  | nil => simp [Poly2.ev]
  | cons m P ih =>
    simp only [List.cons_append, Poly2.ev, List.foldr_cons] at ih ⊢
    rw [ih]; ring

@[simp] theorem Poly2.ev_nil (v : Var → FK) : Poly2.ev [] v = 0 := rfl

@[simp] theorem Poly2.ev_var (u : Var) (v : Var → FK) : (Poly2.var u).ev v = v u := by
  simp [Poly2.var, Poly2.ev, prodK]

@[simp] theorem Poly2.ev_const (c : FK) (v : Var → FK) : (Poly2.const c).ev v = c := by
  simp [Poly2.const, Poly2.ev, prodK]

theorem valOf_limb_E (u : Nat → FK) {l : Nat} (hl : l < 3) : limb (valOf .E u) l = u l := by
  interval_cases l <;> rfl

theorem valOf_limb_K (u : Nat → FK) (l : Nat) : limb (valOf .K u) l = if l = 0 then u 0 else 0 := by
  rcases l with _ | _ | l <;> rfl

/-- Limb `l` of an operand column group is the value's limb. -/
theorem limbPoly_ev (τ : Ty) (u : Nat → Var) (v : Var → FK) {l : Nat} (hl : l < 3) :
    (limbPoly u τ.limbs l).ev v = limb (valOf τ (fun i => v (u i))) l := by
  cases τ
  · rw [valOf_limb_K]; simp only [limbPoly, Ty.limbs]
    by_cases h : l = 0
    · subst h; simp
    · simp [h, show ¬ l < 1 by omega]
  · simp [limbPoly, Ty.limbs, hl, valOf_limb_E _ hl]

theorem limbFix_ev (c : FCol) (τ : Ty) (u : Nat → Var) (v : Var → FK) {l : Nat} (hl : l < 3) :
    (limbFix c u τ.limbs l).ev v = v (.fix c) * limb (valOf τ (fun i => v (u i))) l := by
  cases τ
  · rw [valOf_limb_K]; simp only [limbFix, Ty.limbs]
    by_cases h : l = 0
    · subst h; simp [Poly2.ev, prodK]
    · simp [h, show ¬ l < 1 by omega]
  · simp [limbFix, Ty.limbs, hl, valOf_limb_E _ hl, Poly2.ev, prodK]

theorem prodTerms_110 : prodTerms 1 1 0 = ([(0, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_111 : prodTerms 1 1 1 = ([] : List (Nat × Nat)) := rfl
theorem prodTerms_112 : prodTerms 1 1 2 = ([] : List (Nat × Nat)) := rfl
theorem prodTerms_310 : prodTerms 3 1 0 = ([(0, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_311 : prodTerms 3 1 1 = ([(1, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_312 : prodTerms 3 1 2 = ([(2, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_130 : prodTerms 1 3 0 = ([(0, 0)] : List (Nat × Nat)) := rfl
theorem prodTerms_131 : prodTerms 1 3 1 = ([(0, 1)] : List (Nat × Nat)) := rfl
theorem prodTerms_132 : prodTerms 1 3 2 = ([(0, 2)] : List (Nat × Nat)) := rfl
theorem prodTerms_330 : prodTerms 3 3 0 = ([(0, 0), (1, 2), (2, 1)] : List (Nat × Nat)) := rfl
theorem prodTerms_331 : prodTerms 3 3 1 = ([(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)] : List (Nat × Nat)) := rfl
theorem prodTerms_332 : prodTerms 3 3 2 = ([(0, 2), (1, 1), (2, 0), (2, 2)] : List (Nat × Nat)) := rfl

/-- **The product limb formula**: limb `l` of `a·b` from the limb columns of `a` and `b`. -/
theorem prodPoly_ev (τa τb : Ty) (u w : Nat → Var) (v : Var → FK) {l : Nat} (hl : l < 3) :
    (prodPoly u w τa.limbs τb.limbs l).ev v =
      limb (valOf τa (fun i => v (u i)) * valOf τb (fun i => v (w i))) l := by
  cases τa <;> cases τb <;> interval_cases l <;>
    simp [Ty.limbs, prodPoly, prodTerms_110, prodTerms_111, prodTerms_112, prodTerms_310, prodTerms_311, prodTerms_312, prodTerms_130, prodTerms_131, prodTerms_132, prodTerms_330, prodTerms_331, prodTerms_332, Poly2.ev, prodK, valOf, limb, mul_c₀, mul_c₁,
      mul_c₂, FE.ofK] <;> ring

/-! ## The relation of a shape -/

namespace Shape

variable (σ : Shape)

/-- Operand `o`'s value at a row. -/
def argV (v : Var → FK) (o : Nat) : FE := valOf (σ.args.getD o .K) fun l => v (.arg o l)

/-- The result's value at a row. -/
def resV (v : Var → FK) : FE := valOf σ.ty fun l => v (.res l)

/-- **The relation a row of the shape states.** -/
def Rel (v : Var → FK) : Prop :=
  match σ.kind with
  | .muladd => σ.resV v = σ.argV v 0 * σ.argV v 1 + σ.argV v 2
  | .lin => σ.resV v = σ.argV v 0 + FE.ofK (v (.fix .k)) * σ.argV v 1 + FE.ofK (v (.fix .k'))
  | .assert0 => σ.argV v 1 * σ.argV v 0 = 0
  | .loadE => σ.resV v = σ.argV v 0 + FE.y * σ.argV v 1 + FE.y * FE.y * σ.argV v 2
  | .fixmul => σ.resV v = FE.ofK (v (.fix .F)) * σ.argV v 0 + σ.argV v 1
  | .readd => True

/-- A well-typed shape: arities, and a `K` result only from `K` operands. -/
def TypeOk : Prop :=
  match σ.kind with
  | .muladd => σ.args.length = 3 ∧ (σ.ty = .E ∨ ∀ t ∈ σ.args, t = .K)
  | .lin => σ.args.length = 2 ∧ (σ.ty = .E ∨ ∀ t ∈ σ.args, t = .K)
  | .assert0 => σ.args.length = 2
  | .loadE => σ.args = [.K, .K, .K] ∧ σ.ty = .E
  | .fixmul => σ.args.length = 2 ∧ (σ.ty = .E ∨ ∀ t ∈ σ.args, t = .K)
  | .readd => σ.args = [.K]

end Shape

theorem argLimbs_eq (σ : Shape) (o : Nat) : σ.argLimbs o = (σ.args.getD o .K).limbs := rfl

theorem isK_valOf_K (u : Nat → FK) : IsK (valOf .K u) := rfl

theorem argV_isK {σ : Shape} (h : ∀ t ∈ σ.args, t = .K) (v : Var → FK) (o : Nat) :
    IsK (σ.argV v o) := by
  unfold Shape.argV
  by_cases ho : o < σ.args.length
  · rw [show σ.args.getD o .K = .K by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho, Option.getD_some]
      exact h _ (List.getElem_mem ho)]
    exact isK_valOf_K _
  · rw [List.getD_eq_default _ _ (by omega)]; exact isK_valOf_K _

theorem isK_limb_pos {x : FE} (h : IsK x) {l : Nat} (hl : 0 < l) : limb x l = 0 := by
  rw [← h]; rcases l with _ | _ | l
  · omega
  · rfl
  · rfl

/-- The result value is `rhs` when its limb columns are `rhs`'s (and `rhs` is a `K` value when the
result is a `K` cell). -/
theorem resV_eq (σ : Shape) (v : Var → FK) (rhs : FE)
    (h : ∀ l < σ.ty.limbs, v (.res l) = limb rhs l) (hK : σ.ty = .K → IsK rhs) :
    σ.resV v = rhs := by
  apply FE.ext_limb
  intro l hl
  unfold Shape.resV
  cases hσ : σ.ty
  · rw [valOf_limb_K]
    rw [hσ] at h
    by_cases h0 : l = 0
    · subst h0; simp only [if_true]; exact h 0 (by simp [Ty.limbs])
    · rw [if_neg h0, isK_limb_pos (hK hσ) (by omega)]
  · rw [valOf_limb_E _ hl]; rw [hσ] at h; exact h l (by simpa [Ty.limbs] using hl)

theorem mem_constraints_map {f : Nat → Poly2} {n : Nat} {v : Var → FK}
    (h : ∀ C ∈ (List.range n).map f, C.ev v = 0) : ∀ l < n, (f l).ev v = 0 :=
  fun l hl => h _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)

theorem limbs_le (τ : Ty) : τ.limbs ≤ 3 := by cases τ <;> simp [Ty.limbs]

theorem limb_add (x y : FE) (l : Nat) : limb (x + y) l = limb x l + limb y l := by
  rcases l with _ | _ | l <;> rfl

theorem limb_ofK_mul (c : FK) (x : FE) (l : Nat) : limb (FE.ofK c * x) l = c * limb x l := by
  rcases l with _ | _ | l <;> simp [limb, mul_c₀, mul_c₁, mul_c₂, FE.ofK]

theorem limb_ofK (c : FK) (l : Nat) : limb (FE.ofK c) l = if l = 0 then c else 0 := by
  rcases l with _ | _ | l <;> rfl

theorem Shape.ev_limbArg (σ : Shape) (v : Var → FK) (o : Nat) {l : Nat} (hl : l < 3) :
    (limbPoly (Var.arg o) (σ.argLimbs o) l).ev v = limb (σ.argV v o) l := limbPoly_ev _ _ _ hl

theorem Shape.ev_fixArg (σ : Shape) (c : FCol) (v : Var → FK) (o : Nat) {l : Nat} (hl : l < 3) :
    (limbFix c (Var.arg o) (σ.argLimbs o) l).ev v = v (.fix c) * limb (σ.argV v o) l :=
  limbFix_ev _ _ _ _ hl

theorem Shape.ev_prodArg (σ : Shape) (v : Var → FK) {l : Nat} (hl : l < 3) :
    (prodPoly (Var.arg 0) (Var.arg 1) (σ.argLimbs 0) (σ.argLimbs 1) l).ev v =
      limb (σ.argV v 0 * σ.argV v 1) l := prodPoly_ev _ _ _ _ _ hl

theorem argV_K {σ : Shape} {o : Nat} (h : σ.args.getD o .K = .K) (v : Var → FK) :
    σ.argV v o = FE.ofK (v (.arg o 0)) := by
  unfold Shape.argV; rw [h]; rfl

/-- **The constraints state the relation.** -/
theorem constraints_sound (σ : Shape) (hσ : σ.TypeOk) (v : Var → FK)
    (h : ∀ C ∈ σ.constraints, C.ev v = 0) : σ.Rel v := by
  have h3 := limbs_le σ.ty
  rcases hk : σ.kind with _ | _ | _ | _ | _ | _
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    have hl := mem_constraints_map h
    simp only [Shape.Rel, hk]
    refine resV_eq σ v _ (fun l hlt => ?_) (fun hK => isK_add (isK_mul (argV_isK
      (hσ.2.resolve_left (by simp [hK])) _ _) (argV_isK (hσ.2.resolve_left (by simp [hK])) _ _))
      (argV_isK (hσ.2.resolve_left (by simp [hK])) _ _))
    have hl3 : l < 3 := by omega
    have e := hl l hlt
    rw [Poly2.ev_append, Poly2.ev_append, Poly2.ev_var, σ.ev_prodArg v hl3, σ.ev_limbArg v 2 hl3] at e
    rw [limb_add]
    apply FK.eq_of_add_eq_zero; linear_combination e
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    have hl := mem_constraints_map h
    simp only [Shape.Rel, hk]
    refine resV_eq σ v _ (fun l hlt => ?_) (fun hK => isK_add (isK_add (argV_isK
      (hσ.2.resolve_left (by simp [hK])) _ _) (isK_mul (isK_ofK _)
      (argV_isK (hσ.2.resolve_left (by simp [hK])) _ _))) (isK_ofK _))
    have hl3 : l < 3 := by omega
    have e := hl l hlt
    rw [Poly2.ev_append, Poly2.ev_append, Poly2.ev_append, Poly2.ev_var, σ.ev_limbArg v 0 hl3,
      σ.ev_fixArg .k v 1 hl3] at e
    rw [limb_add, limb_add, limb_ofK_mul, limb_ofK]
    apply FK.eq_of_add_eq_zero
    by_cases h0 : l = 0
    · simp only [h0, if_true, Poly2.ev_var] at e ⊢; linear_combination e
    · simp only [h0, if_false, Poly2.ev_nil] at e ⊢; linear_combination e
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    simp only [Shape.Rel, hk]
    rw [mul_comm]
    apply FE.ext_limb
    intro l hl3
    have hl := mem_constraints_map h
    by_cases hb : σ.argLimbs 0 = 1 ∧ σ.argLimbs 1 = 1
    · have hK0 : (σ.args.getD 0 .K) = .K := by
        rcases h0 : σ.args.getD 0 .K <;> simp_all [argLimbs_eq, Ty.limbs]
      have hK1 : (σ.args.getD 1 .K) = .K := by
        rcases h1 : σ.args.getD 1 .K <;> simp_all [argLimbs_eq, Ty.limbs]
      have hisK : IsK (σ.argV v 0 * σ.argV v 1) := isK_mul (by rw [argV_K hK0]; rfl)
        (by rw [argV_K hK1]; rfl)
      rcases l with _ | l
      · have e := hl 0 (by simp [hb])
        rw [σ.ev_prodArg v (by omega)] at e
        exact e
      · rw [isK_limb_pos hisK (by omega)]; rcases l with _ | _ <;> rfl
    · have e := hl l (by simp [hb, hl3])
      rw [σ.ev_prodArg v hl3] at e
      exact e.trans (by interval_cases l <;> rfl)
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    have hl := mem_constraints_map h
    simp only [Shape.Rel, hk]
    refine resV_eq σ v _ (fun l hlt => ?_) (fun hK => by simp [hσ.2] at hK)
    rw [hσ.2] at hlt
    have hl3 : l < 3 := by simpa [Ty.limbs] using hlt
    have e := hl l hl3
    rw [Poly2.ev_append, Poly2.ev_var, Poly2.ev_var] at e
    rw [FK.eq_of_add_eq_zero e]
    have hg : ∀ o < 3, σ.args.getD o .K = .K := fun o ho => by
      rw [hσ.1]; interval_cases o <;> rfl
    rw [argV_K (hg 0 (by omega)), argV_K (hg 1 (by omega)), argV_K (hg 2 (by omega))]
    interval_cases l <;> simp [limb, mul_c₀, mul_c₁, mul_c₂, FE.y, FE.ofK]
  · simp only [Shape.constraints, hk] at h
    simp only [Shape.TypeOk, hk] at hσ
    have hl := mem_constraints_map h
    simp only [Shape.Rel, hk]
    refine resV_eq σ v _ (fun l hlt => ?_) (fun hK => isK_add (isK_mul (isK_ofK _)
      (argV_isK (hσ.2.resolve_left (by simp [hK])) _ _))
      (argV_isK (hσ.2.resolve_left (by simp [hK])) _ _))
    have hl3 : l < 3 := by omega
    have e := hl l hlt
    rw [Poly2.ev_append, Poly2.ev_append, Poly2.ev_var, σ.ev_fixArg .F v 0 hl3,
      σ.ev_limbArg v 1 hl3] at e
    rw [limb_add, limb_ofK_mul]
    apply FK.eq_of_add_eq_zero; linear_combination e
  · simp [Shape.Rel, hk]

/-- A row's shape is well typed when the row is. -/
theorem Row.shape_typeOk {r : Row} (h : r.typeOk = true) : r.shape.TypeOk := by
  rcases hop : r.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ <;>
    simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
      List.mem_map] at h <;>
    simp only [Shape.TypeOk, Row.shape, Op.kind, hop, List.length_map, List.mem_map] <;>
    first
    | exact ⟨h.1, h.2.imp id fun h' t ⟨a, ha, he⟩ => he ▸ (by simpa using h' t ⟨a, ha, he⟩)⟩
    | exact h
    | exact ⟨h.1, h.2⟩
    | simp_all

end Lvm.Loop
