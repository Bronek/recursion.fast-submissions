-- New for lvm (HAR): the shapes of the node program's tables do not depend on the closed forms of their
-- fixed columns (the cache `G`) nor on the public values (`PUB`'s contents): the circuit is built from
-- the shapes of one instance and `F` runs on another.
import LvmQAsmProg
import LvmQAsmHarBase

set_option autoImplicit false

namespace Lvm.Har

open Lvm Lvm.Loop Lvm.M3 Lvm.QAsm

/-- The sumcheck filter on shapes. -/
def TShape.sc (s : TShape) : Bool := !s.cons.isEmpty || !s.reads.isEmpty || !s.seeds.isEmpty

theorem sumcheckTabs_shape : ∀ (l : List Tab),
    (sumcheckTabs l).map Tab.shape = (l.map Tab.shape).filter TShape.sc
  | [] => rfl
  | t :: l => by
    have ih := sumcheckTabs_shape l
    unfold sumcheckTabs at ih ⊢
    rw [List.filter_cons, List.map_cons, List.filter_cons]
    have e : TShape.sc t.shape = (!t.cons.isEmpty || !t.reads.isEmpty || !t.seeds.isEmpty) := rfl
    rw [e]
    split <;> simp [ih]

theorem shapeTab_shape (σ : Shape) (τ : Nat) (fx fx' : FCol → Nat → FK) (fe fe' : FCol → List FE → FE)
    (pl : Var → Bool × Nat) : (shapeTab σ τ fx fe pl).shape = (shapeTab σ τ fx' fe' pl).shape := by
  simp only [Tab.shape, shapeTab, List.map_map]
  congr 1
  refine List.map_congr_left fun u _ => ?_
  cases u <;> rfl

theorem inArr_shape (a a' : InArr) (hτ : a.τ = a'.τ) (hb : a.base = a'.base) (hs : a.stride = a'.stride)
    (hv : a.val = a'.val) (hf : a.fin = a'.fin) (hp : a.pub.isSome = a'.pub.isSome) (hty : a.ty = a'.ty) :
    a.tab.shape = a'.tab.shape := by
  rcases a with ⟨ty, τ, base, stride, val, fin, pub⟩
  rcases a' with ⟨ty', τ', base', stride', val', fin', pub'⟩
  simp only at hτ hb hs hv hf hp hty
  subst hτ hb hs hv hf hty
  simp only [Tab.shape, InArr.tab, InArr.vcols, List.map_append, List.map_cons, List.map_nil]
  congr 2
  cases pub <;> cases pub' <;> simp_all [List.map_map, colKind]

theorem lvmTabsC_shape (G G' : PG) (pl : Nat → Var → Bool × Nat) (gs : List Grp) (as as' : List InArr)
    (aux : List Tab) (ha : as.map (·.tab.shape) = as'.map (·.tab.shape)) :
    (lvmTabsC G pl gs as aux).map Tab.shape = (lvmTabsC G' pl gs as' aux).map Tab.shape := by
  unfold lvmTabsC
  rw [List.map_append, List.map_append, List.map_append, List.map_append, List.map_map, List.map_map,
    List.map_map, List.map_map]
  have hg : (List.range gs.length).map (Tab.shape ∘ fun i => shapeTab (gs.getD i default).σ (gs.getD i default).τ
      (grpFix G.C.Q (gs.getD i default)) (grpEvalG G (gs.getD i default)) (pl i)) =
      (List.range gs.length).map (Tab.shape ∘ fun i => shapeTab (gs.getD i default).σ (gs.getD i default).τ
      (grpFix G'.C.Q (gs.getD i default)) (grpEvalG G' (gs.getD i default)) (pl i)) :=
    List.map_congr_left fun i _ => shapeTab_shape _ _ _ _ _ _ _
  have ha' : as.map (Tab.shape ∘ InArr.tab) = as'.map (Tab.shape ∘ InArr.tab) := ha
  rw [hg, ha']

/-- **The node program's table shapes depend only on the configuration and the placement record.** -/
theorem tabs_shape (C : QCfg) (G G' : PG) (D : QData) (P P' : Pub) :
    (tabs C G D P).map Tab.shape = (tabs C G' D P').map Tab.shape := by
  unfold tabs
  apply lvmTabsC_shape
  unfold arrs
  simp only [List.map_append]
  congr 1

end Lvm.Har
