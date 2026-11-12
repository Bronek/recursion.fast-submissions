-- New for lvm (WP-14a, H1): V_S's phases 2–3 (bus, table sumcheck, fixed-column check; LvmVEqPhases
-- `dBus`, `dTab` on `M3.real`) refine WP-9b's program `M3.lbusTableCheckProg` on the stream, with the
-- tables' committed column claims related (`CRel`). Uses WP-9b's bridges (LvmM3FidNative:
-- `busFinalR_forms/totals`, `nativeTable_shape/cons`, `claimsOfEvs`, `tableCheckVB_of_R`, `colLoc_raw`).
import LvmVEqSum
import LvmVEqRel
import LvmVEqFit

/-!
# Phases 2–3: V_S refines `lvmBusTableProg`

* `ref_dBus`: `dBus p (M3.real p tabs) pub` refines `lvmBusProg p.busDepth` (`p.leafdecReads = 1`):
  the GKR point mapped, the native bus result `busResV`'s forms and totals mapped (`BusRel`);
* `ref_tableTerms`, `ref_tableSumcheck`: the native table sumcheck refines `tableSumcheckClaims`
  with the claims `claimsOfEvs T evs` and every table's evaluations as many as its columns (`EvLen`);
* `ref_dTab`: `dTab` refines `tablePhaseClaims` (A23: no fixed-column check; the claims are
  `claimsOfEvs` of the native evaluations, for phase 3b);
* `tableClaims_rel`: the native committed-column claims `tableClaimsR T evs` are `tableClaimsE T` of
  the program's claims, claim for claim (`CRel`);
* **`ref_busTab`** (P20, from `Fit`): phases 2–3 refine `M3.lvmBusTableProg` on the sumcheck tables
  (`TabRel`); `monoD_busTab`.
-/

set_option autoImplicit false

namespace Lvm.VEq

open Lvm DM LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
open Lvm.M3 (Tab nativeTable vTable vTables vLayout busResV busFinalR tableCheckR tableClaimsR
  sumcheckTabs claimsOfEvs tableCheckVB formE LBus lvmBusProg lvmBusTableProg FE_eq_of_beq tE_add tE_mul
  nativeTable_shape nativeTable_cons)

/-! ## List helpers -/

theorem forall₂_flatMap {α β γ δ : Type} {R : γ → δ → Prop} {f : α → List γ} {g : β → List δ} :
    ∀ {A : List α} {B : List β}, List.Forall₂ (fun a b ↦ List.Forall₂ R (f a) (g b)) A B →
      List.Forall₂ R (A.flatMap f) (B.flatMap g)
  | _, _, .nil => .nil
  | _, _, .cons h t => by
    simp only [List.flatMap_cons]
    exact List.rel_append h (forall₂_flatMap t)

theorem forall₂_filterMap {α β γ δ : Type} {R : γ → δ → Prop} {f : α → Option γ} {g : β → Option δ} :
    ∀ {A : List α} {B : List β}, List.Forall₂ (fun a b ↦ Option.Rel R (f a) (g b)) A B →
      List.Forall₂ R (A.filterMap f) (B.filterMap g)
  | _, _, .nil => .nil
  | a :: _, b :: _, .cons h t => by
    have ih := forall₂_filterMap t
    simp only [List.filterMap_cons]
    generalize f a = x at h ⊢
    generalize g b = y at h ⊢
    cases h with
    | none => exact ih
    | some hr => exact .cons hr ih

theorem forall₂_of_getElem {α β : Type} {S : α → β → Prop} {A : List α} {B : List β}
    (hl : A.length = B.length) (h : ∀ i (h1 : i < A.length) (h2 : i < B.length), S A[i] B[i]) :
    List.Forall₂ S A B :=
  List.forall₂_iff_get.mpr ⟨hl, fun i h1 h2 ↦ by simpa using h i h1 h2⟩

theorem map_replicate_none (n : ℕ) :
    (List.replicate n (none : Option FE)).map (Option.map FE.toExt3) = List.replicate n none := by
  simp

/-- `zipWith` against a list left alone. -/
theorem map_zipWith_left {α β γ : Type} {f : α → γ} {g : α → β → α} {g' : γ → β → γ}
    (h : ∀ x y, f (g x y) = g' (f x) y) (a : List α) (b : List β) :
    (List.zipWith g a b).map f = List.zipWith g' (a.map f) b := by
  induction a generalizing b with
  | nil => rfl
  | cons x a ih => cases b with
    | nil => rfl
    | cons y b => simp only [List.zipWith_cons_cons, List.map_cons, h, ih]

theorem map_tableWeights (hs : List ℕ) (eqp point : List FE) :
    (Lvm.tableWeights hs eqp point).map FE.toExt3 =
      Verifier.tableWeights hs (eqp.map FE.toExt3) (point.map FE.toExt3) := by
  unfold Lvm.tableWeights Verifier.tableWeights
  rw [zipIdx_map_toExt3]
  generalize point.zipIdx = l
  suffices h : ∀ acc : List FE, (l.foldl (fun weights (x : FE × ℕ) ↦
      List.zipWith (fun weight height ↦ weight *
        if x.2 < height then 1 + eqp.getD x.2 0 + x.1 else x.1) weights hs) acc).map FE.toExt3 =
      (l.map (Prod.map FE.toExt3 id)).foldl (fun weights (x : E × ℕ) ↦
      List.zipWith (fun weight height ↦ weight *
        if x.2 < height then 1 + (eqp.map FE.toExt3).getD x.2 0 + x.1 else x.1) weights hs)
        (acc.map FE.toExt3) by
    rw [h]; simp
  induction l with
  | nil => intro acc; rfl
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    congr 1
    refine map_zipWith_left (fun w h ↦ ?_) acc hs
    simp only [Prod.map_fst, Prod.map_snd, id_eq]
    split_ifs <;> simp only [tE_mul, tE_add, Lvm.M3.tE_one, getD_map_toExt3]

/-! ## The table sumcheck's per-table loop -/

/-- The verifier tables of `T` numbered from `k`. -/
def vTablesK : ℕ → List Tab → List Verifier.Table
  | _, [] => []
  | k, t :: T => vTable k t :: vTablesK (k + 1) T

theorem vTables_eq (T : List Tab) : vTables T = vTablesK 0 T := by
  suffices h : ∀ k, (T.zipIdx k).map (fun x ↦ vTable x.2 x.1) = vTablesK k T from h 0
  induction T with
  | nil => intro k; rfl
  | cons t T ih => intro k; simp only [List.zipIdx_cons, List.map_cons, ih, vTablesK]

/-- The table phase's claims of the tables' points and evaluations from table `k` on
(`claimsOfEvs` at an offset). -/
def cOE (bases : List ℕ) (k : ℕ) (l : List (Tab × (List FE × List FE))) : List Verifier.ColumnClaim :=
  (l.zipIdx k).flatMap fun x ↦ x.1.2.2.zipIdx.map fun vi ↦
    ⟨bases.getD x.2 0 + vi.2, x.1.2.1.map FE.toExt3, FE.toExt3 vi.1⟩

theorem claimsOfEvs_eq (T : List Tab) (evs : List (List FE × List FE)) :
    claimsOfEvs T evs = cOE (Verifier.globalColumnBases (vTables T)) 0 (T.zip evs) := rfl

/-- Every table's evaluations are as many as its columns. -/
def EvLen (T : List Tab) (evs : List (List FE × List FE)) : Prop :=
  ∀ j (h1 : j < T.length) (h2 : j < evs.length), evs[j].2.length = T[j].w

/-- **Scalars**, with their count. -/
theorem ref_readEsL {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} :
    ∀ n, RefAt cap shp sig (DM.readEs n) (VerifierProgram.readScalars n)
      fun xs ys ↦ ys = xs.map FE.toExt3 ∧ xs.length = n
  | 0 => RefAt.pure ⟨rfl, rfl⟩
  | n + 1 => by
    refine RefAt.bind (fun _ ↦ (monoD_readEs n).bind fun _ ↦ MonoD.pure _) ref_readE ?_
    intro x y hxy
    refine RefAt.bind (fun _ ↦ MonoD.pure _) (ref_readEsL n) ?_
    rintro xs ys ⟨hs, hl⟩
    exact RefAt.pure (by simp [hxy, hs, hl])

/-- A native step whose value is mapped afterwards. -/
theorem RefAt.map_left {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray} {α β β' : Type}
    {d : DM β} {k : β → DM β'} {g : β → β'} {P : VerifierProgram α} {R : β → α → Prop}
    {R' : β' → α → Prop} (hk : ∀ b, k b = Pure.pure (g b)) (h : RefAt cap shp sig d P R)
    (hR : ∀ b a, R b a → R' (g b) a) : RefAt cap shp sig (d >>= k) P R' := by
  intro s hok
  have e : runD (d >>= k) sig s = runD (k (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [e, hk] at hok ⊢
  obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
  exact ⟨a, h1, h2, h3, hR _ _ h4⟩

theorem monoD_tableTerms (cp fp point : List FE) :
    ∀ rows cursor final, MonoD (Lvm.tableTerms cp fp point rows cursor final)
  | [], _, _ => MonoD.pure _
  | _ :: rest, _, _ => (monoD_readEs _).bind fun _ ↦
      (monoD_tableTerms cp fp point rest _ _).bind fun ⟨_, _⟩ ↦ MonoD.pure _

theorem monoD_tableSumcheck (rounds : ℕ) (tables : List TableSpec) (busForms : List (List Lvm.Form))
    (cp fp eqp : List FE) (target : FE) :
    MonoD (Lvm.tableSumcheck rounds tables busForms cp fp eqp target) :=
  (monoD_sumcheck _ _ _).bind fun ⟨_, _⟩ ↦ (monoD_tableTerms _ _ _ _ _ _).bind fun ⟨_, _⟩ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem map_value (f : List Lvm.Form) (ev : List FE) :
    (f.map (·.value (ev.getD · 0))).map FE.toExt3 =
      (f.map formE).map (·.evaluate ((ev.map FE.toExt3).getD · 0)) := by
  simp only [List.map_map]
  refine List.map_congr_left fun x _ ↦ ?_
  simp only [Function.comp_apply, toExt3_value, getD_map_toExt3]

section Ref

variable {cap : ℕ → ℕ → ℕ} {shp : ℕ → ℕ × ℕ} {sig : ByteArray}

/-- **The per-table loop** (`tableTerms` against `tableTermsClaims`, tables numbered from `k`). -/
theorem ref_tableTerms (tables : List Verifier.Table) (cp fp point : List FE) :
    ∀ (T : List Tab) (fs : List (List Lvm.Form)) (ws : List FE) (k cursor : ℕ) (final : FE)
      (final' : E) (acc : List Verifier.ColumnClaim), final' = FE.toExt3 final →
    RefAt cap shp sig (Lvm.tableTerms cp fp point (List.zip (T.map nativeTable) (List.zip fs ws)) cursor final)
      (Verifier.tableTermsClaims tables (cp.map FE.toExt3) (fp.map FE.toExt3) (point.map FE.toExt3)
        (List.zip (vTablesK k T) (List.zip (T.map (·.τ)) (List.zip (fs.map (·.map formE))
          (ws.map FE.toExt3)))) cursor final' acc)
      (fun r r' ↦ r'.1 = FE.toExt3 r.1 ∧
        r'.2 = acc ++ cOE (Verifier.globalColumnBases tables) k (T.zip r.2) ∧ EvLen T r.2)
  | [], _, _, _, _, _, _, _, hf => RefAt.pure ⟨hf, by simp [cOE], fun _ h ↦ absurd h (by simp)⟩
  | _ :: _, [], _, _, _, _, _, _, hf => RefAt.pure ⟨hf, by simp [cOE], fun _ _ h ↦ absurd h (by simp)⟩
  | _ :: _, _ :: _, [], _, _, _, _, _, hf => RefAt.pure ⟨hf, by simp [cOE], fun _ _ h ↦ absurd h (by simp)⟩
  | t :: T, f :: fs, w :: ws, k, cursor, final, final', acc, hf => by
    simp only [List.map_cons, List.zip_cons_cons, vTablesK, Lvm.tableTerms, Verifier.tableTermsClaims]
    rw [← (nativeTable_shape k t).2.1, ← (nativeTable_shape k t).2.2]
    refine RefAt.bind (fun _ ↦ (monoD_tableTerms _ _ _ _ _ _).bind fun ⟨_, _⟩ ↦ MonoD.pure _)
      (ref_readEsL _) ?_
    rintro ev _ ⟨rfl, hl⟩
    refine RefAt.map_left (g := fun x ↦ (x.1, (point.take (nativeTable t).logHeight, ev) :: x.2))
      (fun ⟨_, _⟩ ↦ rfl) (ref_tableTerms tables cp fp point T fs ws (k + 1) _ _ _ _ ?_) ?_
    · subst hf
      simp only [tE_add, tE_mul, toExt3_dot, map_toExt3_take, map_toExt3_drop, nativeTable_cons k t,
        map_value]
    · rintro ⟨fin, evs⟩ ⟨fin', cl⟩ ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · rw [h2]
        simp [cOE, List.zipIdx_map, vTable, List.map_take, List.append_assoc]
        intros; rfl
      · intro j h1 h2
        cases j with
        | zero => simpa [nativeTable] using hl
        | succ j => simpa using h3 j (by simpa using h1) (by simpa using h2)

/-- **The table sumcheck** (`tableSumcheck` against `tableSumcheckClaims`; the program's arguments
given by equations). -/
theorem ref_tableSumcheck (T : List Tab) (rounds : ℕ) (hr : rounds = (T.map (·.τ)).foldl max 0)
    (fs : List (List Lvm.Form)) (cp fp eqp : List FE) (target : FE) {hs : List ℕ}
    {fs' : List (List Verifier.Form)} {cp' fp' eqp' : List E} {target' : E}
    (hhs : hs = T.map (·.τ)) (hfs : fs' = fs.map (·.map formE)) (hcp : cp' = cp.map FE.toExt3)
    (hfp : fp' = fp.map FE.toExt3) (heqp : eqp' = eqp.map FE.toExt3)
    (ht : target' = FE.toExt3 target) :
    RefAt cap shp sig (Lvm.tableSumcheck rounds (T.map nativeTable) fs cp fp eqp target)
      (Verifier.tableSumcheckClaims (vTables T) hs fs' cp' fp' eqp' target')
      (fun evs cl ↦ cl = claimsOfEvs T evs ∧ EvLen T evs) := by
  subst hr hhs hfs hcp hfp heqp ht
  have hsc := ref_sumcheck (cap := cap) (shp := shp) (sig := sig) 4
    (List.replicate ((T.map (·.τ)).foldl max 0) none) target
  rw [map_replicate_none] at hsc
  refine RefAt.bind (fun ⟨_, _⟩ ↦ (monoD_tableTerms _ _ _ _ _ _).bind fun ⟨_, _⟩ ↦
    (MonoD.require _).bind fun _ ↦ MonoD.pure _) hsc ?_
  rintro ⟨ch, cl⟩ _ rfl
  have hlh : (T.map nativeTable).map (·.logHeight) = T.map (·.τ) := by
    simp only [List.map_map]; rfl
  have htt := ref_tableTerms (cap := cap) (shp := shp) (sig := sig) (vTables T) cp fp ch.reverse T fs
    (Lvm.tableWeights (T.map (·.τ)) eqp ch.reverse) 0 0 0 0 [] Lvm.M3.tE_zero.symm
  rw [map_tableWeights, ← vTables_eq, List.map_reverse] at htt
  simp only [hlh]
  refine RefAt.bind (fun ⟨_, _⟩ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) htt ?_
  rintro ⟨fin, evs⟩ ⟨fin', cls⟩ ⟨h1, h2, h3⟩
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · simp only at h1 ⊢
    rw [h1]
    exact congrArg FE.toExt3 (FE_eq_of_beq hc)
  · intro _ _ _
    exact RefAt.pure ⟨by simpa [claimsOfEvs_eq] using h2, h3⟩

/-! ## The bus phase -/

/-- The native bus phase's result (the GKR point, the bus result) against the lvm bus phase's read:
no claim, the point mapped, `busResV`'s forms and totals the native ones mapped. -/
def BusRel (T : List Tab) (pb : List FE × BusOut) (b : LBus) : Prop :=
  pb.2.claims = [] ∧ b.point = pb.1.map FE.toExt3 ∧
    (busResV T b).forms = pb.2.forms.map (·.map formE) ∧
      (busResV T b).totals = pb.2.totals.map FE.toExt3

theorem FE_beq_self (x : FE) : (x == x) = true := by
  change (x.c₀ == x.c₀ && x.c₁ == x.c₁ && x.c₂ == x.c₂) = true
  simp

/-- One scalar read as a list of `n = 1`. -/
theorem ref_readEs_one {n : ℕ} (hn : n = 1) :
    RefAt cap shp sig (DM.readEs n) VerifierProgram.readScalar fun xs z ↦ xs.map FE.toExt3 = [z] := by
  subst hn
  intro s hok
  obtain ⟨a, h1, h2, h3, h4⟩ := ref_readE (cap := cap) (shp := shp) (sig := sig) s hok
  exact ⟨a, h1, h2, h3, by rw [h4]; rfl⟩

theorem monoD_dBus (p : Params) (m : M3) (pub : Pub) : MonoD (dBus p m pub) :=
  (monoD_samples _).bind fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_verifyGkrGrandProducts _).bind fun ⟨_, _, _⟩ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _

theorem monoD_dTab (p : Params) (m : M3) (pub : Pub) (point : List FE) (bus : BusOut) :
    MonoD (dTab p m pub point bus) :=
  monoD_sampleE.bind fun _ ↦ monoD_tableSumcheck _ _ _ _ _ _ _

/-- **Phase 2**: the native bus phase refines the lvm bus phase. -/
theorem ref_dBus (p : Params) (tabs : Pub → List Tab) (pub : Pub) (hl : p.leafdecReads = 1) :
    RefAt cap shp sig (dBus p (M3.real p tabs) pub) (lvmBusProg p.busDepth)
      (BusRel (sumcheckTabs (tabs pub))) := by
  simp only [lvmBusProg, LeanVM.Protocol.EndToEnd.Front.abProg, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]
  refine RefAt.bind (fun _ ↦ monoD_sampleE.bind fun _ ↦
    (monoD_verifyGkrGrandProducts _).bind fun ⟨_, _, _⟩ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_samples _) ?_
  rintro as _ rfl
  refine RefAt.bind (fun _ ↦
    (monoD_verifyGkrGrandProducts _).bind fun ⟨_, _, _⟩ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) ref_sampleE ?_
  rintro be _ rfl
  refine RefAt.bind (fun ⟨_, _, _⟩ ↦ (MonoD.require _).bind fun _ ↦
      (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _)
    (ref_verifyGkrGrandProducts _) ?_
  rintro ⟨cr, pt, vs⟩ _ rfl
  refine RefAt.bind (fun _ ↦ (monoD_readEs _).bind fun _ ↦ (MonoD.require _).bind fun _ ↦
    MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · intro h0
    have h0' : cr = 0 := FE.toExt3_inj.mp (h0.trans Lvm.M3.tE_zero.symm)
    subst h0'
    rw [bne, FE_beq_self] at hc
    exact absurd hc (by decide)
  intro _ _ _
  refine RefAt.bind (fun _ ↦ (MonoD.require _).bind fun _ ↦ MonoD.pure _) (ref_readEs_one hl) ?_
  intro ld z hz
  refine RefAt.bind (fun _ ↦ MonoD.pure _) (RefAt.require fun hc ↦ ?_) ?_
  · have hc' : (vs.length == 3 && ld == [0]) = true := hc
    rw [Bool.and_eq_true] at hc'
    rcases ld with _ | ⟨x, _ | ⟨y, l⟩⟩
    · simp at hz
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hz
      have hx : (x == 0) = true := by simpa [List.cons_beq_cons] using hc'.2
      rw [← hz, FE_eq_of_beq hx, Lvm.M3.tE_zero]
    · simp at hz
  intro _ _ _
  have e : (M3.real p tabs).busFinal ⟨as, be, cr, pt, vs, ld, pub⟩ =
      busFinalR (sumcheckTabs (tabs pub)) ⟨as, be, cr, pt, vs, ld, pub⟩ := rfl
  rw [e]
  exact RefAt.pure ⟨rfl, rfl,
    (Lvm.M3.busFinalR_forms (sumcheckTabs (tabs pub)) ⟨as, be, cr, pt, vs, ld, pub⟩).symm,
    (Lvm.M3.busFinalR_totals (sumcheckTabs (tabs pub)) ⟨as, be, cr, pt, vs, ld, pub⟩).symm⟩

/-! ## The table phase -/

theorem real_tables (p : Params) (tabs : Pub → List Tab) (pub : Pub) :
    (M3.real p tabs).tables pub = (sumcheckTabs (tabs pub)).map nativeTable := rfl

theorem map_nC_vTablesK : ∀ (k : ℕ) (T : List Tab),
    (vTablesK k T).map Verifier.Table.nConstraints = (T.map nativeTable).map (·.nConstraints)
  | _, [] => rfl
  | k, t :: T => by
    simp only [vTablesK, List.map_cons, map_nC_vTablesK (k + 1) T, (nativeTable_shape k t).2.2]

theorem nC_eq (T : List Tab) :
    ((vTables T).map Verifier.Table.nConstraints).sum = ((T.map nativeTable).map (·.nConstraints)).sum := by
  rw [vTables_eq, map_nC_vTablesK]

/-- **The tables' committed-column claims**: the native ones are the program's, claim for claim. -/
theorem tableClaims_rel (T : List Tab) (evs : List (List FE × List FE)) (hl : EvLen T evs) :
    List.Forall₂ CRel (tableClaimsR T evs) (tableClaimsE T (claimsOfEvs T evs)) := by
  unfold tableClaimsR tableClaimsE claimsOfEvs
  rw [List.filterMap_flatMap]
  refine forall₂_flatMap (forall₂_of_getElem (by simp) fun j h1 h2 ↦ ?_)
  have hj1 : j < T.length := by simp at h1; omega
  have hj2 : j < evs.length := by simp at h1; omega
  have hlj := hl j hj1 hj2
  simp only [List.getElem_zipIdx, List.getElem_zip, Nat.zero_add]
  generalize evs[j] = pe at hlj ⊢
  obtain ⟨pt, ev⟩ := pe
  simp only [List.filterMap_map]
  refine forall₂_filterMap (forall₂_of_getElem (by simp [hlj]) fun i i1 i2 ↦ ?_)
  have hi : i < T[j].w := by simpa using i1
  have hie : i < ev.length := by simpa using i2
  simp only [List.getElem_zipIdx, Function.comp_apply, Nat.zero_add, Lvm.M3.colLoc_raw T hj1 hi,
    Option.bind_some, List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hi, Option.map_some,
    Option.getD_some]
  cases hc : T[j].cols[i] with
  | com rec off =>
    refine Option.Rel.some ⟨rfl, rfl, ?_, fun xs ↦ (toExt3_eqEval pt xs).symm⟩
    simp [BClaim.point, BlockClaim.point, List.getD_eq_getElem?_getD, hie]
  | fix f e => exact Option.Rel.none

/-- **Phase 3**: the native table phase refines the table phase's program (A23: no fixed-column
check; the claims are those of the native evaluations, for phase 3b). -/
theorem ref_dTab (p : Params) (tabs : Pub → List Tab) (pub : Pub)
    (hr : p.tableRounds = ((sumcheckTabs (tabs pub)).map (·.τ)).foldl max 0)
    (pb : List FE × BusOut) (b : LBus) (hb : BusRel (sumcheckTabs (tabs pub)) pb b) :
    RefAt cap shp sig (dTab p (M3.real p tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev))
      (Verifier.tablePhaseClaims (vTables (sumcheckTabs (tabs pub))) (vLayout (sumcheckTabs (tabs pub)))
          (busResV (sumcheckTabs (tabs pub)) b))
      (fun r cl ↦ r.1.2.claims = [] ∧
        List.Forall₂ CRel (tableClaimsR (sumcheckTabs (tabs pub)) r.2)
          (tableClaimsE (sumcheckTabs (tabs pub)) cl) ∧
        cl = claimsOfEvs (sumcheckTabs (tabs pub)) r.2 ∧ EvLen (sumcheckTabs (tabs pub)) r.2) := by
  obtain ⟨hcl, hpt, hfs, htt⟩ := hb
  simp only [dTab, real_tables, bind_assoc, pure_bind]
  simp only [Verifier.tablePhaseClaims, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
  refine RefAt.bind (fun _ ↦ (monoD_tableSumcheck _ _ _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    ref_sampleE ?_
  rintro xi _ rfl
  refine RefAt.bind (fun _ ↦ MonoD.pure _)
    (ref_tableSumcheck _ _ hr _ _ _ _ _ rfl hfs ?_ ?_ hpt ?_) ?_
  · rw [nC_eq, map_toExt3_take, map_powers]
  · rw [nC_eq, map_toExt3_drop, map_powers]
  · rw [htt, nC_eq, toExt3_dot, map_toExt3_drop, map_powers]
  rintro evs cl ⟨rfl, hlen⟩
  exact RefAt.pure ⟨hcl, tableClaims_rel _ _ hlen, rfl, hlen⟩

/-! ## Phases 2–3 -/

theorem monoD_busTab (p : Params) (m : M3) (pub : Pub) :
    MonoD (dBus p m pub >>= fun pb ↦ dTab p m pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev)) :=
  (monoD_dBus p m pub).bind fun _ ↦ (monoD_dTab _ _ _ _ _).bind fun _ ↦ MonoD.pure _

/-- What phases 2–3 give: no bus claim, the committed-column claims related, and the table phase's
claims those of the native evaluations (for phase 3b). -/
def TabRel (T : List Tab) (r : (List FE × BusOut) × List (List FE × List FE))
    (cl : List Verifier.ColumnClaim) : Prop :=
  r.1.2.claims = [] ∧ List.Forall₂ CRel (tableClaimsR T r.2) (tableClaimsE T cl) ∧
    cl = claimsOfEvs T r.2 ∧ EvLen T r.2

/-- Phases 2–3 at a record with one leaf-decomposition scalar and the tallest table's rounds. -/
theorem ref_busTabP (p : Params) (tabs : Pub → List Tab) (pub : Pub) (hl : p.leafdecReads = 1)
    (hr : p.tableRounds = ((sumcheckTabs (tabs pub)).map (·.τ)).foldl max 0) :
    RefAt cap shp sig (dBus p (M3.real p tabs) pub >>= fun pb ↦
        dTab p (M3.real p tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev))
      (M3.lvmBusTableProg (vTables (sumcheckTabs (tabs pub))) (vLayout (sumcheckTabs (tabs pub)))
        p.busDepth (busResV (sumcheckTabs (tabs pub))))
      (TabRel (sumcheckTabs (tabs pub))) := by
  unfold lvmBusTableProg
  refine RefAt.bind (fun _ ↦ (monoD_dTab _ _ _ _ _).bind fun _ ↦ MonoD.pure _)
    (ref_dBus p tabs pub hl) ?_
  intro pb b hb
  exact ref_dTab p tabs pub hr pb b hb

end Ref

/-- **V_S's phases 2–3 refine WP-9b's `lvmBusTableProg`** at P20: wherever V_S's checks hold, the
program returns the table phase's claims at the same cursor (`TabRel`). -/
theorem ref_busTab (sig : ByteArray) (tabs : Pub → List M3.Tab) (pub : Pub) (F : Fit P20 (tabs pub)) :
    Ref20 sig (dBus P20 (M3.real P20 tabs) pub >>= fun pb ↦
        dTab P20 (M3.real P20 tabs) pub pb.1 pb.2 >>= fun ev ↦ pure (pb, ev))
      (M3.lvmBusTableProg (vTables (M3.sumcheckTabs (tabs pub))) (vLayout (M3.sumcheckTabs (tabs pub)))
        P20.busDepth (busResV (M3.sumcheckTabs (tabs pub))))
      (TabRel (M3.sumcheckTabs (tabs pub))) :=
  ref_busTabP P20 tabs pub F.leafdec F.rounds

end Lvm.VEq
