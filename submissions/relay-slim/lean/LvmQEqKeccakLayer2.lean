import LvmQKeccakLayer

/-!
# QA1: tools for reading one Keccak layer template (`LvmQEqKeccakLayer`)

* `NoA`: a gadget emits no assertion (every gadget of `layerTB` but `gAssert`);
* `TInv`, `peelN`, `peelA`, `peelL`, `inv_end`: walk a template along its `>>=` chain, keeping the
  rows that hold, the whole's length and what its assertions amount to;
* `cp_append`, `cp_get`, `cp_range`: the copy rows;
* small facts on `F`'s side (`packSpec_pos`, `scSpec_length`, `fe_beq_iff`, `laneForm_congr`).
-/

set_option autoImplicit false

namespace Lvm.Q1

open Lvm Lvm.Loop

/-! ## Gadgets without assertions -/

/-- `m` emits no assertion: its assertions hold on every memory. -/
def NoA {α : Type} (m : TB α) : Prop := ∀ (xv : Src → FE) (V : Nat → FE) (n : Nat), TAssert xv V (m n).2

theorem noA_pure {α : Type} (a : α) : NoA (pure a : TB α) := by
  intro xv V n k hk
  simp [tb_pure] at hk

theorem noA_bind {α β : Type} {m : TB α} {f : α → TB β} (hm : NoA m) (hf : ∀ a, NoA (f a)) : NoA (m >>= f) :=
  fun xv V n => (tassert_bind m f).mpr ⟨hm xv V n, hf _ xv V _⟩

theorem noA_emit {i : Ins} (hi : i.op ≠ .assert0) : NoA (emit i) := by
  intro xv V n k hk ha
  simp only [emit, List.length_singleton, Nat.lt_one_iff] at hk
  subst hk
  exact absurd ha hi

theorem noA_gMul (a b d : Src) : NoA (gMul a b d) := noA_emit nofun
theorem noA_gLin (k k' : FK) (a b : Src) : NoA (gLin k k' a b) := noA_emit nofun
theorem noA_gAdd (a b : Src) : NoA (gAdd a b) := noA_emit nofun
theorem noA_gOne (a : Src) : NoA (gOne a) := noA_gLin _ _ _ _
theorem noA_gZero (a : Src) : NoA (gZero a) := noA_gLin _ _ _ _
theorem noA_gScale (k : FK) (a : Src) : NoA (gScale k a) := noA_gLin _ _ _ _
theorem noA_gLoad (q : Nat) (str : List Nat) : NoA (gLoad q str) := noA_emit nofun
theorem noA_gCopy (a : Src) : NoA (gCopy a) := noA_gLin _ _ _ _

theorem noA_mapTB {α : Type} {f : α → TB Src} (hf : ∀ a, NoA (f a)) : ∀ l : List α, NoA (mapTB f l)
  | [] => noA_pure _
  | a :: as => noA_bind (hf a) fun _ => noA_bind (noA_mapTB hf as) fun _ => noA_pure _

theorem noA_gSum : ∀ (s : Src) (cs : List Src), NoA (gSum s cs)
  | _, [] => noA_pure _
  | s, c :: cs => noA_bind (noA_gAdd s c) fun s' => noA_gSum s' cs

theorem noA_gDot : ∀ (acc : Src) (cds : List (Src × Src)), NoA (gDot acc cds)
  | _, [] => noA_pure _
  | acc, _ :: rest => noA_bind (noA_gMul _ _ acc) fun a => noA_gDot a rest

theorem noA_gHorner (x : Src) : ∀ (h : Src) (cs : List Src), NoA (gHorner x h cs)
  | _, [] => noA_pure _
  | h, c :: cs => noA_bind (noA_gMul h x c) fun h' => noA_gHorner x h' cs

theorem noA_gEqStep (z : Src) (tab : List Src) (r : Src) : NoA (gEqStep z tab r) :=
  noA_bind (noA_gOne r) fun _ => noA_bind (noA_mapTB (fun _ => noA_gMul _ _ _) _) fun _ =>
    noA_bind (noA_mapTB (fun _ => noA_gMul _ _ _) _) fun _ => noA_pure _

theorem noA_gEqTab (z : Src) : ∀ (tab pt : List Src), NoA (gEqTab z tab pt)
  | _, [] => noA_pure _
  | tab, r :: rs => noA_bind (noA_gEqStep z tab r) fun t => noA_gEqTab z t rs

theorem noA_gPackRound (z : Src) (q : Nat) (str : List Nat) (r value scale : Src) :
    NoA (gPackRound z q str r value scale) :=
  noA_bind (noA_gLoad _ _) fun _ => noA_bind (noA_gLoad _ _) fun _ => noA_bind (noA_gLoad _ _) fun _ =>
  noA_bind (noA_gAdd _ _) fun _ => noA_bind (noA_gMul _ _ _) fun _ => noA_bind (noA_gMul _ _ _) fun _ =>
  noA_bind (noA_gMul _ _ _) fun _ => noA_bind (noA_gLin _ _ _ _) fun _ => noA_bind (noA_gMul _ _ _) fun _ =>
  noA_bind (noA_gMul _ _ _) fun _ => noA_pure _

theorem noA_gPackRounds (z : Src) (str : List Nat) :
    ∀ (q : Nat) (rs : List Src) (value scale : Src), NoA (gPackRounds z str q rs value scale)
  | _, [], _, _ => noA_pure _
  | q, r :: rs, value, scale => noA_bind (noA_gPackRound z q str r value scale) fun a =>
    noA_bind (noA_gPackRounds z str (q + 15) rs a.1 a.2.1) fun _ => noA_pure _

theorem noA_gLocalRound (q : Nat) (str : List Nat) (value : Src) : NoA (gLocalRound q str value) :=
  noA_bind (noA_gLoad _ _) fun _ => noA_bind (noA_gLoad _ _) fun _ => noA_bind (noA_gLoad _ _) fun _ =>
  noA_bind (noA_gLoad _ _) fun _ => noA_bind (noA_gAdd _ _) fun _ => noA_bind (noA_gAdd _ _) fun _ =>
  noA_bind (noA_gMul _ _ _) fun _ => noA_bind (noA_gMul _ _ _) fun _ => noA_bind (noA_gMul _ _ _) fun _ =>
  noA_pure _

theorem noA_gLocalRounds (str : List Nat) : ∀ (k q : Nat) (value : Src), NoA (gLocalRounds str k q value)
  | 0, _, _ => noA_pure _
  | k + 1, q, value => noA_bind (noA_gLocalRound q str value) fun a =>
    noA_bind (noA_gLocalRounds str k (q + 18) a.1) fun _ => noA_pure _

theorem noA_gSumMap (z : Src) (k : Nat) {f : Nat → TB Src} (hf : ∀ c, NoA (f c)) : NoA (gSumMap z k f) :=
  noA_bind (noA_mapTB hf _) fun ts => noA_gSum z ts

theorem noA_gProj (z : Src) (masks : List Nat) (mu prod : List Src) : NoA (gProj z masks mu prod) :=
  noA_gSumMap _ _ fun _ => noA_bind (noA_gSum _ _) fun _ => noA_gMul _ _ _

theorem noA_gPowers (z s : Src) : ∀ (acc : Src) (k : Nat), NoA (gPowers z s acc k)
  | _, 0 => noA_pure _
  | acc, k + 1 => noA_bind (noA_gMul acc s z) fun nx => noA_bind (noA_gPowers z s nx k) fun _ => noA_pure _

theorem noA_gInst (z one s : Src) (embs : List Nat) : NoA (gInst z one s embs) :=
  noA_bind (noA_gPowers _ _ _ _) fun _ => noA_bind (noA_mapTB (fun _ => noA_gSum _ _) _) fun _ =>
    noA_bind (noA_gSum _ _) fun _ => noA_pure _

theorem noA_gLowTab (z : Src) (ta tb : List Src) (c rl : Nat) : NoA (gLowTab z ta tb c rl) :=
  noA_gSumMap _ _ fun zz => by
    by_cases h : (zz + rl) / 8 = c
    · simp only [h, ite_true]; exact noA_gMul _ _ _
    · simp only [h, ite_false]; exact noA_pure _

theorem noA_gHighTab (z : Src) (ta tb : List Src) (k : Nat) : NoA (gHighTab z ta tb k) :=
  noA_gSumMap _ _ fun _ => noA_gMul _ _ _

theorem noA_gShift (z : Src) (L0 L1 H : List Src) (r : Nat) : NoA (gShift z L0 L1 H r) :=
  noA_bind (noA_gMul _ _ _) fun _ => noA_gMul _ _ _

theorem noA_gLaneForm (z : Src) (B : List Src) (R : Nat → Src) (l : Nat) : NoA (gLaneForm z B R l) :=
  noA_bind (noA_gMul _ _ _) fun _ => noA_bind (noA_gDot _ _) fun _ => noA_gDot _ _

theorem noA_gFlip (z : Src) (B A : List Src) (i : Nat) : NoA (gFlip z B A i) := noA_gLaneForm _ _ _ _

theorem noA_gLaneW (eL : List Src) (beta : Src) : NoA (gLaneW eL beta) :=
  noA_mapTB (fun _ => noA_bind (noA_gMul _ _ _) fun _ => noA_gMul _ _ _) _

theorem noA_gIndexStep (z : Src) (k : Nat) (acc r : Src) : NoA (gIndexStep z k acc r) :=
  noA_bind (noA_gScale _ _) fun _ => noA_bind (noA_gOne _) fun _ => noA_gMul _ _ _

theorem noA_gIndex (z : Src) : ∀ (k : Nat) (acc : Src) (rs : List Src), NoA (gIndex z k acc rs)
  | _, _, [] => noA_pure _
  | k, acc, r :: rs => noA_bind (noA_gIndexStep z k acc r) fun acc' => noA_gIndex z (k + 1) acc' rs

/-! ## Walking a template -/

/-- While reading a template from position `n`: the rows of the rest `R` hold, the whole has length
`L`, and the whole's assertions `TA` hold iff the rest's do and `Q` (the assertions read so far). -/
def TInv (xv : Src → FE) (V : Nat → FE) (TA : Prop) (L : Nat) (Q : Prop) {α : Type} (R : TB α) (n : Nat) :
    Prop :=
  THold xv V n (R n).2 ∧ L = n + (R n).2.length ∧ (TA ↔ TAssert xv V (R n).2 ∧ Q)

theorem inv_start {xv : Src → FE} {V : Nat → FE} {α : Type} {R : TB α} (h : THold xv V 0 (R 0).2) :
    TInv xv V (TAssert xv V (R 0).2) (R 0).2.length True R 0 :=
  ⟨h, (Nat.zero_add _).symm, ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩⟩

/-- Read a gadget without assertions. -/
theorem peelN {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {α β : Type} {m : TB α}
    {f : α → TB β} {n : Nat} (h : TInv xv V TA L Q (m >>= f) n) (hm : NoA m) :
    ∃ a n', (m n).1 = a ∧ THold xv V n (m n).2 ∧ TInv xv V TA L Q (f a) n' := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [thold_bind] at h1
  refine ⟨(m n).1, n + (m n).2.length, rfl, h1.1, h1.2, ?_, ?_⟩
  · rw [h2, tb_bind, List.length_append]; omega
  · rw [h3, tassert_bind]
    exact ⟨fun ⟨⟨_, h⟩, hq⟩ => ⟨h, hq⟩, fun ⟨h, hq⟩ => ⟨⟨hm _ _ _, h⟩, hq⟩⟩

/-- Read the last gadget (its position kept). -/
theorem peelL {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {α β : Type} {m : TB α}
    {f : α → TB β} {n : Nat} (h : TInv xv V TA L Q (m >>= f) n) (hm : NoA m) :
    THold xv V n (m n).2 ∧ TInv xv V TA L Q (f (m n).1) (n + (m n).2.length) := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [thold_bind] at h1
  refine ⟨h1.1, h1.2, ?_, ?_⟩
  · rw [h2, tb_bind, List.length_append]; omega
  · rw [h3, tassert_bind]
    exact ⟨fun ⟨⟨_, h⟩, hq⟩ => ⟨h, hq⟩, fun ⟨h, hq⟩ => ⟨⟨hm _ _ _, h⟩, hq⟩⟩

theorem tassert_gAssert {xv : Src → FE} {V : Nat → FE} {n : Nat} {a g : Src} :
    TAssert xv V (gAssert a g n).2 ↔ g.valF xv V * a.valF xv V = 0 := by
  refine ⟨gAssert_spec, fun h k hk _ => ?_⟩
  simp only [gAssert, emitA, List.length_singleton, Nat.lt_one_iff] at hk
  subst hk
  exact h

/-- Read an assertion. -/
theorem peelA {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {β : Type} {a g : Src}
    {f : Unit → TB β} {n : Nat} (h : TInv xv V TA L Q (gAssert a g >>= f) n) :
    ∃ n', TInv xv V TA L (Q ∧ g.valF xv V * a.valF xv V = 0) (f ()) n' := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : (gAssert a g n).1 = () := rfl
  rw [thold_bind, e] at h1
  rw [tb_bind, e] at h2
  rw [tassert_bind, e] at h3
  refine ⟨n + (gAssert a g n).2.length, h1.2, ?_, ?_⟩
  · rw [h2, List.length_append]; omega
  · rw [h3, tassert_gAssert]
    exact ⟨fun ⟨⟨h, h'⟩, hq⟩ => ⟨h', hq, h⟩, fun ⟨h', hq, h⟩ => ⟨⟨h, h'⟩, hq⟩⟩

theorem inv_end {xv : Src → FE} {V : Nat → FE} {TA : Prop} {L : Nat} {Q : Prop} {n : Nat}
    (h : TInv xv V TA L Q (pure () : TB Unit) n) : L = n ∧ (TA ↔ Q) := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨by simpa [tb_pure] using h2, ?_⟩
  rw [h3]
  exact ⟨fun h => h.2, fun h => ⟨noA_pure () xv V n, h⟩⟩

/-! ## Copy rows -/

theorem mapTB_gCopy_snd : ∀ (l : List Src) (n : Nat), (mapTB gCopy l n).2 = l.map fun x => linI 0 0 x x
  | [], _ => rfl
  | a :: as, n => by
    simp only [mapTB, tb_bind, tb_pure, List.append_nil, List.map_cons]
    rw [mapTB_gCopy_snd as]
    rfl

theorem mapTB_gCopy_length (l : List Src) (n : Nat) : (mapTB gCopy l n).2.length = l.length := by
  rw [mapTB_gCopy_snd, List.length_map]

/-- The copy rows of `l` placed at `n` hold. -/
def CopyHold (xv : Src → FE) (V : Nat → FE) (n : Nat) (l : List Src) : Prop :=
  THold xv V n (l.map fun x => linI 0 0 x x)

theorem cp_of {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List Src} (h : THold xv V n (mapTB gCopy l n).2) :
    CopyHold xv V n l := by
  rw [mapTB_gCopy_snd] at h; exact h

theorem cp_append {xv : Src → FE} {V : Nat → FE} {n : Nat} {l₁ l₂ : List Src} (h : CopyHold xv V n (l₁ ++ l₂)) :
    CopyHold xv V n l₁ ∧ CopyHold xv V (n + l₁.length) l₂ := by
  unfold CopyHold at h ⊢
  rw [List.map_append, thold_append, List.length_map] at h
  exact h

theorem cp_get {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List Src} (h : CopyHold xv V n l) :
    ∀ j < l.length, V (n + j) = (l.map (Src.valF xv V)).getD j 0 := by
  intro j hj
  have e : (l.map fun x => linI 0 0 x x).getD j default = linI 0 0 (l.getD j default) (l.getD j default) := by
    simp [hj]
  have := h j (by simpa using hj) (by rw [e]; exact Or.inr (Or.inl ⟨0, 0, rfl⟩))
  rw [this, e, ← getD_valF _ hj]
  show _ + FE.ofK 0 * _ + FE.ofK 0 = _
  rw [show FE.ofK 0 = 0 from rfl, zero_mul, add_zero, add_zero]
  rfl

theorem range_map_getD (l : List FE) : (List.range l.length).map (fun j => l.getD j 0) = l := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h2]

theorem cp_range {xv : Src → FE} {V : Nat → FE} {n : Nat} {l : List Src} (h : CopyHold xv V n l) {k : Nat}
    (hk : l.length = k) : (List.range k).map (fun j => V (n + j)) = l.map (Src.valF xv V) := by
  subst hk
  rw [List.map_congr_left (fun j hj => cp_get h j (List.mem_range.mp hj))]
  have := range_map_getD (vals xv V l)
  simp only [vals, List.length_map] at this ⊢
  exact this

/-! ## Small facts -/

theorem fe_beq_iff (x y : FE) : (x == y) = true ↔ x = y := by
  obtain ⟨a0, a1, a2⟩ := x
  obtain ⟨b0, b1, b2⟩ := y
  show ((a0 == b0 && a1 == b1) && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, FE.mk.injEq, and_assoc]

theorem fe_add_eq_zero (x y : FE) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x + (y + y) := by rw [FE_add_self, add_zero]
      _ = (x + y) + y := by ring
      _ = y := by rw [h, zero_add]
  · intro h; rw [h, FE_add_self]

theorem packSpec_pos (v : Nat → FE) : ∀ (pt : List FE) (value scale : FE) (p : Nat),
    (packSpec v pt value scale p).2.2.2 = p + 120 * pt.length
  | [], _, _, p => by simp [packSpec]
  | r :: rs, value, scale, p => by
    simp only [packSpec, List.length_cons]
    rw [packSpec_pos v rs]
    ring

theorem scSpec_length (v : Nat → FE) (count : Nat) : ∀ (p : Nat) (claim : FE) (es : List (Option FE)),
    (scSpec v count p claim es).1.length = es.length
  | _, _, [] => rfl
  | p, claim, e :: es => by
    simp only [scSpec, List.length_cons]
    rw [scSpec_length v count]

theorem rho_lt (i : Nat) : rho i < 64 := by
  unfold rho
  have hall : ∀ x ∈ keccakRho, x < 64 := by decide
  rw [List.getD_eq_getElem?_getD]
  cases h : keccakRho[i]? with
  | none => simp
  | some x => exact hall x (List.mem_of_getElem? h)

theorem laneForm_congr (B : List FE) {R R' : Nat → FE} (hR : ∀ s < 64, R s = R' s) (l : Nat) :
    laneForm B R l = laneForm B R' l := by
  have h1 : ∀ i, R (rho i) = R' (rho i) := fun i => hR _ (rho_lt i)
  have h2 : ∀ i, R ((rho i + 1) % 64) = R' ((rho i + 1) % 64) := fun i => hR _ (Nat.mod_lt _ (by norm_num))
  simp only [laneForm, h1, h2]

theorem eqTab_one {xv : Src → FE} {V : Nat → FE} {z one : Src} (hz : z.valF xv V = 0) (hone : one.valF xv V = 1)
    (pt : List Src) (n : Nat) (h : THold xv V n (gEqTab z [one] pt n).2) :
    (gEqTab z [one] pt n).1.map (Src.valF xv V) = eqKernel (pt.map (Src.valF xv V)) := by
  rw [gEqTab_spec hz pt [one] n h, eqKernel, List.map_singleton, hone]

theorem rc_mem {i : Nat} (hi : i < 24) : keccakRC.getD i 0 ∈ keccakRC := by
  rw [List.getD_eq_getElem _ _ (by simpa [keccakRC] using hi)]
  exact List.getElem_mem _

end Lvm.Q1
