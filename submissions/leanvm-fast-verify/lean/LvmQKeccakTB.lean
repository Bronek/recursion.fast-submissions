import LvmQSumcheck

/-!
# QA1: a builder for loop templates (`TB`) and its program logic (`THold`)

Large loop templates (the Keccak layer) are written as programs `TB α = Nat → α × List Ins`: given
the position of the next instruction, they return their result (operands `Src`) and the
instructions they emit; `emit i` returns `loc n`. The program logic mirrors QL's `SegsHold`: on a
fixed point `V` of the whole template (`Fix`, what `fix_of_loop` gives for a loop's iteration),
`THold xv V n δ` says the instructions `δ` placed at `n` hold. **`thold_of_fix`** gives it for the
whole template; `thold_bind` splits it along `>>=`; each gadget's spec is stated as
`THold xv V n (g n).2 → P (g n).1`.
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop Lvm.Loop.Build

/-- A template program: from the next position, its result and its instructions. -/
def TB (α : Type) : Type := Nat → α × List Ins

instance : Monad TB where
  pure a := fun _ => (a, [])
  bind m f := fun n =>
    let r := m n
    let r' := f r.1 (n + r.2.length)
    (r'.1, r.2 ++ r'.2)

/-- Emit one instruction; its result is `loc n`. -/
def emit (i : Ins) : TB Src := fun n => (.loc n, [i])

/-- Emit an assertion (no result). -/
def emitA (i : Ins) : TB Unit := fun _ => ((), [i])

theorem tb_bind {α β : Type} (m : TB α) (f : α → TB β) (n : Nat) :
    (m >>= f) n = ((f (m n).1 (n + (m n).2.length)).1, (m n).2 ++ (f (m n).1 (n + (m n).2.length)).2) := rfl

theorem tb_pure {α : Type} (a : α) (n : Nat) : (pure a : TB α) n = (a, []) := rfl

/-- An operand's value: `V k` for `loc k`, `xv` for the others (values as a function). -/
def Src.valF (xv : Src → FE) (V : Nat → FE) : Src → FE
  | .loc k => V k
  | s => xv s

/-- An instruction's value on `V`. -/
def Ins.evalF (xv : Src → FE) (V : Nat → FE) (i : Ins) : FE :=
  let a (o : Nat) : FE := Src.valF xv V (i.args.getD o default)
  match i.op with
  | .muladd => a 0 * a 1 + a 2
  | .lin k k' => a 0 + FE.ofK k * a 1 + FE.ofK k'
  | .loadE => a 0 + FE.y * a 1 + FE.y * FE.y * a 2
  | _ => 0

/-- The ops whose relation `evalF` states. -/
def Ins.arith (i : Ins) : Prop := i.op = .muladd ∨ (∃ k k', i.op = .lin k k') ∨ i.op = .loadE

/-- **The instructions `δ` placed at `n` hold in `V`**: every arithmetic one's value is its
evaluation. -/
def THold (xv : Src → FE) (V : Nat → FE) (n : Nat) (δ : List Ins) : Prop :=
  ∀ k < δ.length, (δ.getD k default).arith → V (n + k) = (δ.getD k default).evalF xv V

/-- Iteration `jf`'s cells as a function. -/
def iterF (M : Mem) (o : LoopOut) (jf : Nat) (t : Nat) : FE := (o.cell t jf).val M

/-- **A loop of a template holds the template** at each iteration (no well-formedness needed:
`cur k` reads row `k`'s cell whatever `k`). -/
theorem thold_of_loop {c : Ctx} {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr}
    (h : SegsHold c M p (loop dims (tplOf ins) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    THold (iterXv M (loop dims (tplOf ins) p).1 jf) (iterF M (loop dims (tplOf ins) p).1 jf) 0 ins := by
  intro t ht hw
  rw [Nat.zero_add]
  have hrel := loop_rel h hjf (t := t) (by simpa [tplOf] using ht)
  have harg : ∀ k, LoopOut.arg M (loop dims (tplOf ins) p).1 jf t k =
      ((ins.getD t default).args.getD k default).valF (iterXv M (loop dims (tplOf ins) p).1 jf)
        (iterF M (loop dims (tplOf ins) p).1 jf) := by
    intro k
    simp only [LoopOut.arg]
    show (((tplOf ins).getD t default).args.getD k default).val M _ jf = _
    rw [tplOf_getD ins ht, Ins.toLRow, getD_map_default Src.toOpd rfl]
    cases ((ins.getD t default).args.getD k default) with
    | loc k' => rw [Src.toOpd, Opd.val_cur M _ hjf]; rfl
    | prev k' => rfl
    | ext a => rfl
  unfold LRel at hrel
  simp only [harg] at hrel
  have hop : ((loop dims (tplOf ins) p).1.tpl.getD t default).op = (ins.getD t default).op := by
    show ((tplOf ins).getD t default).op = _
    rw [tplOf_getD ins ht]; rfl
  rw [hop] at hrel
  unfold Ins.evalF
  rcases hw with h1 | ⟨a, b, h1⟩ | h1 <;> simp only [h1] at hrel ⊢ <;> exact hrel

theorem thold_of_loopP {c : Ctx} {M : Mem} {dims : List Nat} {ins : List Ins} {init : Nat → Cell} {p : Ptr}
    (h : SegsHold c M p (loopP dims (tplOf ins) init p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    THold (iterXv M (loopP dims (tplOf ins) init p).1 jf) (iterF M (loopP dims (tplOf ins) init p).1 jf) 0 ins := by
  rw [loopP_fst]
  exact thold_of_loop (hold_loop_of_loopP h) hjf

theorem thold_append {xv : Src → FE} {V : Nat → FE} {n : Nat} {δ₁ δ₂ : List Ins} :
    THold xv V n (δ₁ ++ δ₂) ↔ THold xv V n δ₁ ∧ THold xv V (n + δ₁.length) δ₂ := by
  constructor
  · intro h
    refine ⟨fun k hk hw => ?_, fun k hk hw => ?_⟩
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
      rw [← e] at hw ⊢
      exact h k (by simp; omega) hw
    · have e : (δ₁ ++ δ₂).getD (δ₁.length + k) default = δ₂.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [← e] at hw ⊢
      rw [Nat.add_assoc]
      exact h _ (by simp; omega) hw
  · rintro ⟨h₁, h₂⟩ k hk hw
    by_cases hk1 : k < δ₁.length
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk1]
      rw [e] at hw ⊢
      exact h₁ k hk1 hw
    · obtain ⟨k', rfl⟩ : ∃ k', k = δ₁.length + k' := ⟨k - δ₁.length, by omega⟩
      have e : (δ₁ ++ δ₂).getD (δ₁.length + k') default = δ₂.getD k' default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [e] at hw ⊢
      rw [← Nat.add_assoc]
      exact h₂ k' (by simp at hk; omega) hw

/-- **Composition**: a bind holds iff both parts hold at their positions. -/
theorem thold_bind {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β) :
    THold xv V n ((m >>= f) n).2 ↔
      THold xv V n (m n).2 ∧ THold xv V (n + (m n).2.length) (f (m n).1 (n + (m n).2.length)).2 := by
  rw [tb_bind]; exact thold_append

/-- **One instruction**: its result's value is its evaluation. -/
theorem emit_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {i : Ins} (hw : i.arith)
    (h : THold xv V n (emit i n).2) : (emit i n).1.valF xv V = i.evalF xv V := by
  have := h 0 (by simp [emit]) (by simpa [emit] using hw)
  simpa [emit, Src.valF] using this

/-! ## Primitive gadgets (all results in `E`) -/

/-- `a·b + d`. -/
def gMul (a b d : Src) : TB Src := emit (mulI a b d)
/-- `a + b`. -/
def gAdd (a b : Src) : TB Src := emit (addI a b)
/-- `a + k·b + k'`. -/
def gLin (k k' : FK) (a b : Src) : TB Src := emit (linI k k' a b)
/-- `1 + a`. -/
def gOne (a : Src) : TB Src := gLin 0 1 a a
/-- `0` (`a + a`). -/
def gZero (a : Src) : TB Src := gLin 1 0 a a
/-- `k·a` for a constant `k ∈ K` (`a + (k + 1)·a`). -/
def gScale (k : FK) (a : Src) : TB Src := gLin (k + 1) 0 a a
/-- A stream scalar: `loadE` of lanes `q, q+1, q+2`, moving by `str` per loop step. -/
def gLoad (q : Nat) (str : List Nat) : TB Src := emit (loadI q str)

theorem gMul_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a b d : Src} (h : THold xv V n (gMul a b d n).2) :
    (gMul a b d n).1.valF xv V = a.valF xv V * b.valF xv V + d.valF xv V := by
  rw [gMul, emit_spec (Or.inl rfl) h]; rfl

theorem gAdd_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a b : Src} (h : THold xv V n (gAdd a b n).2) :
    (gAdd a b n).1.valF xv V = a.valF xv V + b.valF xv V := by
  rw [gAdd, emit_spec (Or.inr (Or.inl ⟨1, 0, rfl⟩)) h]
  show _ + FE.ofK 1 * _ + FE.ofK 0 = _
  rw [show FE.ofK 1 = 1 from rfl, show FE.ofK 0 = 0 from rfl, one_mul, add_zero]; rfl

theorem gLin_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {k k' : FK} {a b : Src}
    (h : THold xv V n (gLin k k' a b n).2) :
    (gLin k k' a b n).1.valF xv V = a.valF xv V + FE.ofK k * b.valF xv V + FE.ofK k' := by
  rw [gLin, emit_spec (Or.inr (Or.inl ⟨k, k', rfl⟩)) h]; rfl

theorem FE_add_self (x : FE) : x + x = 0 := CharTwo.add_self_eq_zero x

theorem gOne_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : Src} (h : THold xv V n (gOne a n).2) :
    (gOne a n).1.valF xv V = 1 + a.valF xv V := by
  rw [gOne, gLin_spec h, show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl]; ring

theorem gZero_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a : Src} (h : THold xv V n (gZero a n).2) :
    (gZero a n).1.valF xv V = 0 := by
  rw [gZero, gLin_spec h, show FE.ofK 0 = 0 from rfl, show FE.ofK 1 = 1 from rfl, one_mul, add_zero,
    FE_add_self]

theorem gScale_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {k : FK} {a : Src}
    (h : THold xv V n (gScale k a n).2) : (gScale k a n).1.valF xv V = FE.ofK k * a.valF xv V := by
  rw [gScale, gLin_spec h, show FE.ofK 0 = 0 from rfl, add_zero,
    show FE.ofK (k + 1) = FE.ofK k + 1 from map_add FE.ofKRingHom k 1]
  have := FE_add_self (a.valF xv V)
  calc a.valF xv V + (FE.ofK k + 1) * a.valF xv V = FE.ofK k * a.valF xv V + (a.valF xv V + a.valF xv V) := by ring
    _ = _ := by rw [this, add_zero]

theorem gLoad_spec {xv : Src → FE} {V : Nat → FE} {n q : Nat} {str : List Nat} (h : THold xv V n (gLoad q str n).2) :
    (gLoad q str n).1.valF xv V = xv (.ext ⟨.K, q, str⟩) + FE.y * xv (.ext ⟨.K, q + 1, str⟩) +
      FE.y * FE.y * xv (.ext ⟨.K, q + 2, str⟩) := by
  rw [gLoad, emit_spec (Or.inr (Or.inr rfl)) h]; rfl

/-! ## Lists -/

/-- Run a gadget per element. -/
def mapTB {α : Type} (f : α → TB Src) : List α → TB (List Src)
  | [] => pure []
  | a :: as => f a >>= fun x => mapTB f as >>= fun xs => pure (x :: xs)

theorem mapTB_length {α : Type} (f : α → TB Src) : ∀ (as : List α) (n : Nat), (mapTB f as n).1.length = as.length
  | [], _ => rfl
  | a :: as, n => by
    simp only [mapTB, tb_bind, tb_pure, List.length_cons]
    rw [mapTB_length f as]

/-- **Per-element specs** of `mapTB`. -/
theorem mapTB_spec {α : Type} {xv : Src → FE} {V : Nat → FE} {f : α → TB Src} {P : α → FE → Prop}
    (hf : ∀ a n, THold xv V n (f a n).2 → P a ((f a n).1.valF xv V)) :
    ∀ (as : List α) (n : Nat), THold xv V n (mapTB f as n).2 →
      List.Forall₂ (fun a s => P a (s.valF xv V)) as (mapTB f as n).1
  | [], _, _ => List.Forall₂.nil
  | a :: as, n, h => by
    simp only [mapTB, tb_bind, tb_pure, List.append_nil] at h ⊢
    rw [thold_append] at h
    exact List.Forall₂.cons (hf a n h.1) (mapTB_spec hf as _ h.2)

theorem forall₂_map_eq {α : Type} {g : α → FE} {h : Src → FE} :
    ∀ {as : List α} {bs : List Src}, List.Forall₂ (fun a s => h s = g a) as bs → bs.map h = as.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h1 h2 => by simp [h1, forall₂_map_eq h2]

/-! ## Sums, dot products, Horner, `eq` tables -/

/-- `s + c₀ + c₁ + …`. -/
def gSum : Src → List Src → TB Src
  | s, [] => pure s
  | s, c :: cs => gAdd s c >>= fun s' => gSum s' cs

theorem gSum_spec {xv : Src → FE} {V : Nat → FE} : ∀ (s : Src) (cs : List Src) (n : Nat),
    THold xv V n (gSum s cs n).2 → (gSum s cs n).1.valF xv V = s.valF xv V + (cs.map (Src.valF xv V)).sum
  | s, [], n, _ => by simp [gSum, tb_pure]
  | s, c :: cs, n, h => by
    simp only [gSum] at h ⊢
    rw [thold_bind] at h
    rw [tb_bind, gSum_spec _ cs _ h.2, gAdd_spec h.1]
    simp [add_assoc]

/-- `acc + Σ cᵢ·dᵢ`. -/
def gDot : Src → List (Src × Src) → TB Src
  | acc, [] => pure acc
  | acc, cd :: rest => gMul cd.1 cd.2 acc >>= fun a => gDot a rest

theorem gDot_spec {xv : Src → FE} {V : Nat → FE} : ∀ (acc : Src) (cds : List (Src × Src)) (n : Nat),
    THold xv V n (gDot acc cds n).2 →
      (gDot acc cds n).1.valF xv V = acc.valF xv V + (cds.map fun cd => cd.1.valF xv V * cd.2.valF xv V).sum
  | acc, [], n, _ => by simp [gDot, tb_pure]
  | acc, cd :: rest, n, h => by
    simp only [gDot] at h ⊢
    rw [thold_bind] at h
    rw [tb_bind, gDot_spec _ rest _ h.2, gMul_spec h.1]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- Horner from the top coefficient `h`, then `cs` downwards. -/
def gHorner (x : Src) : Src → List Src → TB Src
  | h, [] => pure h
  | h, c :: cs => gMul h x c >>= fun h' => gHorner x h' cs

theorem gHorner_spec {xv : Src → FE} {V : Nat → FE} (x : Src) : ∀ (h : Src) (cs : List Src) (n : Nat),
    THold xv V n (gHorner x h cs n).2 →
      (gHorner x h cs n).1.valF xv V = hornerVal (x.valF xv V) (h.valF xv V) (cs.map (Src.valF xv V))
  | h, [], n, _ => by simp [gHorner, tb_pure, hornerVal]
  | h, c :: cs, n, hh => by
    simp only [gHorner] at hh ⊢
    rw [thold_bind] at hh
    rw [tb_bind, gHorner_spec x _ cs _ hh.2, gMul_spec hh.1]
    rfl

/-- One level of an `eq` table (`eqKernel`'s step): `e·(1 + r)` for every `e`, then `e·r`. -/
def gEqStep (z : Src) (tab : List Src) (r : Src) : TB (List Src) :=
  gOne r >>= fun r1 => mapTB (fun e => gMul e r1 z) tab >>= fun lo =>
    mapTB (fun e => gMul e r z) tab >>= fun hi => pure (lo ++ hi)

/-- The `eq` table of a point from `tab` (`z` a zero cell). -/
def gEqTab (z : Src) : List Src → List Src → TB (List Src)
  | tab, [] => pure tab
  | tab, r :: rs => gEqStep z tab r >>= fun t => gEqTab z t rs

theorem gOne_fst (r : Src) (n : Nat) : (gOne r n).1 = .loc n := rfl

theorem gEqStep_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) (tab : List Src) (r : Src)
    (n : Nat) (h : THold xv V n (gEqStep z tab r n).2) :
    (gEqStep z tab r n).1.map (Src.valF xv V) =
      (tab.map (Src.valF xv V)).map (· * (1 + r.valF xv V)) ++ (tab.map (Src.valF xv V)).map (· * r.valF xv V) := by
  obtain ⟨h1, h'⟩ := (thold_bind _ _).mp h
  obtain ⟨h2, h''⟩ := (thold_bind _ _).mp h'
  obtain ⟨h3, -⟩ := (thold_bind _ _).mp h''
  have e1 : V n = 1 + r.valF xv V := gOne_spec h1
  rw [gOne_fst] at h2 h3
  have k2 := mapTB_spec (P := fun e v => v = e.valF xv V * (1 + r.valF xv V))
    (fun a m hm => by rw [gMul_spec hm, show (Src.loc n).valF xv V = V n from rfl, e1, hz, add_zero]) tab _ h2
  have k3 := mapTB_spec (P := fun e v => v = e.valF xv V * r.valF xv V)
    (fun a m hm => by rw [gMul_spec hm, hz, add_zero]) tab _ h3
  simp only [gEqStep, tb_bind, tb_pure, gOne_fst] at k2 k3 ⊢
  rw [List.map_append, forall₂_map_eq k2, forall₂_map_eq k3, List.map_map, List.map_map]
  rfl

theorem gEqTab_spec {xv : Src → FE} {V : Nat → FE} {z : Src} (hz : z.valF xv V = 0) :
    ∀ (pt tab : List Src) (n : Nat), THold xv V n (gEqTab z tab pt n).2 →
      (gEqTab z tab pt n).1.map (Src.valF xv V) =
        (pt.map (Src.valF xv V)).foldl (fun out r => out.map (· * (1 + r)) ++ out.map (· * r)) (tab.map (Src.valF xv V))
  | [], tab, n, _ => by simp [gEqTab, tb_pure]
  | r :: rs, tab, n, h => by
    simp only [gEqTab] at h ⊢
    rw [thold_bind] at h
    rw [tb_bind, gEqTab_spec hz rs _ _ h.2, gEqStep_spec hz tab r n h.1]
    rfl

/-! ## Assertions -/

/-- The assertions of `δ` placed at `n` hold: `gate · a = 0`. -/
def TAssert (xv : Src → FE) (V : Nat → FE) (δ : List Ins) : Prop :=
  ∀ k < δ.length, (δ.getD k default).op = .assert0 →
    ((δ.getD k default).args.getD 1 default).valF xv V * ((δ.getD k default).args.getD 0 default).valF xv V = 0

theorem tassert_append {xv : Src → FE} {V : Nat → FE} {δ₁ δ₂ : List Ins} :
    TAssert xv V (δ₁ ++ δ₂) ↔ TAssert xv V δ₁ ∧ TAssert xv V δ₂ := by
  constructor
  · intro h
    refine ⟨fun k hk ha => ?_, fun k hk ha => ?_⟩
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
      rw [← e] at ha ⊢; exact h k (by simp; omega) ha
    · have e : (δ₁ ++ δ₂).getD (δ₁.length + k) default = δ₂.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [← e] at ha ⊢; exact h _ (by simp; omega) ha
  · rintro ⟨h₁, h₂⟩ k hk ha
    by_cases hk1 : k < δ₁.length
    · have e : (δ₁ ++ δ₂).getD k default = δ₁.getD k default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk1]
      rw [e] at ha ⊢; exact h₁ k hk1 ha
    · obtain ⟨k', rfl⟩ : ∃ k', k = δ₁.length + k' := ⟨k - δ₁.length, by omega⟩
      have e : (δ₁ ++ δ₂).getD (δ₁.length + k') default = δ₂.getD k' default := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
      rw [e] at ha ⊢; exact h₂ k' (by simp at hk; omega) ha

theorem tassert_bind {α β : Type} {xv : Src → FE} {V : Nat → FE} {n : Nat} (m : TB α) (f : α → TB β) :
    TAssert xv V ((m >>= f) n).2 ↔
      TAssert xv V (m n).2 ∧ TAssert xv V (f (m n).1 (n + (m n).2.length)).2 := by
  rw [tb_bind]; exact tassert_append

theorem tassert_of_loop {M : Mem} {dims : List Nat} {ins : List Ins} {p : Ptr}
    (h : SegsAssert M p (loop dims (tplOf ins) p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum) :
    TAssert (iterXv M (loop dims (tplOf ins) p).1 jf) (iterF M (loop dims (tplOf ins) p).1 jf) ins := by
  intro t ht ha
  have hA := loop_assert h hjf (t := t) (by simpa [tplOf] using ht)
  unfold LAssert at hA
  have hop : ((loop dims (tplOf ins) p).1.tpl.getD t default).op = .assert0 := by
    show ((tplOf ins).getD t default).op = _
    rw [tplOf_getD ins ht]; exact ha
  rw [hop] at hA
  have harg : ∀ k, LoopOut.arg M (loop dims (tplOf ins) p).1 jf t k =
      ((ins.getD t default).args.getD k default).valF (iterXv M (loop dims (tplOf ins) p).1 jf)
        (iterF M (loop dims (tplOf ins) p).1 jf) := by
    intro k
    simp only [LoopOut.arg]
    show (((tplOf ins).getD t default).args.getD k default).val M _ jf = _
    rw [tplOf_getD ins ht, Ins.toLRow, getD_map_default Src.toOpd rfl]
    cases ((ins.getD t default).args.getD k default) with
    | loc k' => rw [Src.toOpd, Opd.val_cur M _ hjf]; rfl
    | prev k' => rfl
    | ext a => rfl
  simp only [harg] at hA
  exact hA

/-- A gated assertion `gate · a = 0`. -/
def gAssert (a gate : Src) : TB Unit := emitA ⟨.assert0, .K, [a, gate]⟩

theorem gAssert_spec {xv : Src → FE} {V : Nat → FE} {n : Nat} {a gate : Src}
    (h : TAssert xv V (gAssert a gate n).2) : gate.valF xv V * a.valF xv V = 0 :=
  h 0 (by simp [gAssert, emitA]) rfl

end Lvm.Q1
