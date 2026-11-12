import LvmQKeccakRounds

/-!
# QA1: the Keccak layer's arithmetic as template gadgets

Each gadget computes one piece of `F`'s `verifyKeccakLayer` (or of the structured forms of
`LvmQKeccakSpec`), and its spec states the value in `F`'s own form:

* `gProj`: the RMFE projection `Σ_c (Σ_{i: mask_i ∋ c} μ_i)·product_c` (masks a parameter; `F` uses
  `rmfeProject`);
* `gPowers`, `gInst`: `powers s 24` and the instance weights `Σ_{b ∈ e} s^b` per embedding `e`
  (`keccakInstanceWeights` with `rmfeEmbed`);
* `gSumMap`: `Σ_{c<k} f(c)` for per-index gadgets (the pattern of every sum below).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-- `Σ_{c<k}` of per-index gadgets. -/
def gSumMap (z : Src) (k : Nat) (f : Nat → TB Src) : TB Src :=
  mapTB f (List.range k) >>= fun ts => gSum z ts

theorem gSumMap_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {k : Nat}
    {f : Nat → TB Src} {F : Nat → FE} (hf : ∀ c n, THold xv V n (f c n).2 → (f c n).1.valF xv V = F c)
    (n : Nat) (h : THold xv V n (gSumMap z k f n).2) :
    (gSumMap z k f n).1.valF xv V = ((List.range k).map F).sum := by
  obtain ⟨h1, h2⟩ := (thold_bind _ _).mp h
  have k1 := mapTB_spec (P := fun c v => v = F c) (fun c m hm => hf c m hm) _ _ h1
  rw [gSumMap, tb_bind, gSum_spec _ _ _ h2, hz, zero_add, forall₂_map_eq k1]

/-- `mapTB_spec` with the elements' membership. -/
theorem mapTB_spec_mem {α : Type} {xv : Src → FE} {V : Nat → FE} {f : α → TB Src} {P : α → FE → Prop} :
    ∀ (as : List α), (∀ a ∈ as, ∀ n, THold xv V n (f a n).2 → P a ((f a n).1.valF xv V)) →
      ∀ (n : Nat), THold xv V n (mapTB f as n).2 → List.Forall₂ (fun a s => P a (s.valF xv V)) as (mapTB f as n).1
  | [], _, _, _ => List.Forall₂.nil
  | a :: as, hf, n, h => by
    simp only [mapTB, tb_bind, tb_pure, List.append_nil] at h ⊢
    rw [thold_append] at h
    exact List.Forall₂.cons (hf a (by simp) n h.1)
      (mapTB_spec_mem as (fun b hb => hf b (by simp [hb])) _ h.2)

theorem gSumMap_spec' {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) {k : Nat}
    {f : Nat → TB Src} {F : Nat → FE} (hf : ∀ c < k, ∀ n, THold xv V n (f c n).2 → (f c n).1.valF xv V = F c)
    (n : Nat) (h : THold xv V n (gSumMap z k f n).2) :
    (gSumMap z k f n).1.valF xv V = ((List.range k).map F).sum := by
  obtain ⟨h1, h2⟩ := (thold_bind _ _).mp h
  have k1 := mapTB_spec_mem (P := fun c v => v = F c) _ (fun c hc m hm => hf c (List.mem_range.mp hc) m hm) _ h1
  rw [gSumMap, tb_bind, gSum_spec _ _ _ h2, hz, zero_add, forall₂_map_eq k1]

theorem getD_valF {xv : Src → FE} {V : Nat → FE} (l : List Src) {i : Nat} (hi : i < l.length) :
    (l.getD i default).valF xv V = (l.map (Src.valF xv V)).getD i 0 := by
  simp [List.getD_eq_getElem _ _ hi, hi]

/-! ## The RMFE projection -/

/-- The weights summed for product coefficient `c`: `μ_i` with bit `c` of mask `i`. -/
def projSrcs (masks : List Nat) (mu : List Src) (c : Nat) : List Src :=
  (mu.zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none

theorem projSrcs_map {xv : Src → FE} {V : Nat → FE} (masks : List Nat) (c : Nat) (mu : List Src) :
    (projSrcs masks mu c).map (Src.valF xv V) =
      ((mu.map (Src.valF xv V)).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none := by
  rw [projSrcs, List.map_filterMap, List.zip_map_left, List.filterMap_map]
  apply List.filterMap_congr
  intro p _
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  split <;> rfl

/-- **The projection**: `Σ_{c<k} (Σ projSrcs c)·product_c`. -/
def gProj (z : Src) (masks : List Nat) (mu prod : List Src) : TB Src :=
  gSumMap z prod.length fun c => gSum z (projSrcs masks mu c) >>= fun P => gMul P (prod.getD c default) z

theorem gProj_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) (masks : List Nat)
    (mu prod : List Src) (n : Nat) (h : THold xv V n (gProj z masks mu prod n).2) :
    (gProj z masks mu prod n).1.valF xv V = sumE ((List.range prod.length).map fun c =>
      sumE (((mu.map (Src.valF xv V)).zip masks).filterMap fun p => if p.2.testBit c then some p.1 else none) *
        (prod.getD c default).valF xv V) := by
  rw [sumE_eq_sum]
  refine gSumMap_spec hz (fun c m hm => ?_) n h
  obtain ⟨h1, h2⟩ := (thold_bind _ _).mp hm
  rw [tb_bind, gMul_spec h2, gSum_spec _ _ _ h1, hz, zero_add, add_zero, projSrcs_map, sumE_eq_sum]

/-! ## Instance weights -/

/-- `acc, acc·s, acc·s², …` (`k` terms; `powersFrom`). -/
def gPowers (z s : Src) : Src → Nat → TB (List Src)
  | _, 0 => pure []
  | acc, k + 1 => gMul acc s z >>= fun nx => gPowers z s nx k >>= fun rest => pure (acc :: rest)

theorem gPowers_spec {xv : Src → FE} {V : Nat → FE} {z s : Src} (hz : z.valF xv V = 0) :
    ∀ (k : Nat) (acc : Src) (n : Nat), THold xv V n (gPowers z s acc k n).2 →
      (gPowers z s acc k n).1.map (Src.valF xv V) = powersFrom (acc.valF xv V) (s.valF xv V) k
  | 0, _, _, _ => rfl
  | k + 1, acc, n, h => by
    simp only [gPowers] at h ⊢
    obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
    obtain ⟨h2, -⟩ := (thold_bind _ _).mp h
    simp only [tb_bind, tb_pure, List.map_cons, powersFrom]
    rw [gPowers_spec hz k _ _ h2, gMul_spec h1, hz, add_zero]

theorem powersFrom_length (acc base : FE) : ∀ k : Nat, (powersFrom acc base k).length = k
  | 0 => rfl
  | k + 1 => by simp [powersFrom, powersFrom_length _ _ k]

theorem gPowers_length (z s : Src) : ∀ (k : Nat) (acc : Src) (n : Nat), (gPowers z s acc k n).1.length = k
  | 0, _, _ => rfl
  | k + 1, acc, n => by simp [gPowers, tb_bind, tb_pure, gPowers_length z s k]

/-- The powers an embedding `e` sums. -/
def embSrcs (pw : List Src) (e : Nat) : List Src :=
  (List.range embedBits).filterMap fun b => if e.testBit b then some (pw.getD b default) else none

/-- **The instance weights** `μ_e = Σ_{b ∈ e} s^b` and their sum `κ` (`one` a cell holding `1`). -/
def gInst (z one s : Src) (embs : List Nat) : TB (List Src × Src) :=
  gPowers z s one embedBits >>= fun pw => mapTB (fun e => gSum z (embSrcs pw e)) embs >>= fun mu =>
    gSum z mu >>= fun kappa => pure (mu, kappa)

theorem gInst_spec {xv : Src → FE} {V : Nat → FE} {z one s : Src} (hz : z.valF xv V = 0)
    (hone : one.valF xv V = 1) (embs : List Nat) (n : Nat) (h : THold xv V n (gInst z one s embs n).2) :
    (gInst z one s embs n).1.1.map (Src.valF xv V) =
        embs.map (fun e => sumE ((List.range embedBits).filterMap fun b =>
          if e.testBit b then some ((powers (s.valF xv V) embedBits).getD b 0) else none)) ∧
    (gInst z one s embs n).1.2.valF xv V = ((gInst z one s embs n).1.1.map (Src.valF xv V)).sum := by
  obtain ⟨h1, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h2, h⟩ := (thold_bind _ _).mp h
  obtain ⟨h3, -⟩ := (thold_bind _ _).mp h
  have epw := gPowers_spec hz embedBits one n h1
  rw [hone] at epw
  have hlen := gPowers_length z s embedBits one n
  have k2 := mapTB_spec (P := fun e v => v = sumE ((List.range embedBits).filterMap fun b =>
      if e.testBit b then some ((powers (s.valF xv V) embedBits).getD b 0) else none))
    (fun e m hm => by
      rw [gSum_spec _ _ _ hm, hz, zero_add, sumE_eq_sum]
      congr 1
      simp only [embSrcs, List.map_filterMap]
      apply List.filterMap_congr
      intro b hb
      split
      · simp only [Option.map_some, Option.some.injEq]
        rw [getD_valF _ (by rw [hlen]; simpa using hb), epw]; rfl
      · rfl) embs _ h2
  refine ⟨?_, ?_⟩
  · simp only [gInst, tb_bind, tb_pure]
    exact forall₂_map_eq k2
  · simp only [gInst, tb_bind, tb_pure]
    rw [gSum_spec _ _ _ h3, hz, zero_add]

end Lvm.Q1
