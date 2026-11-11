-- New for lvm (WP-16b, kernel time): the static facts of the plan at `P20` from one kernel
-- evaluation of the plan (it was evaluated once per fact: `streamOk_P20`, `planCap_P20`,
-- `plan_static_P20`).
import LvmQLinkBridge

/-!
# The plan at `P20`, checked in one pass

`passR` walks the plan once (a `List.rec`: one iota step per entry) and checks at every entry `i`
`elemF`: `entryOk` (QL's stream facts; the cap entry's length from a table `lk`), the length
`≡ 0 mod 8` after `q₀`, the length `≤ queryCap`. A cursor over the table checks its entries'
lengths on the way, and at the end the count and two sums: `Σ clenC` (the reassembled body) and
`Σ (40 + len)` (`slenS`). **`passR_P20`** is the one decision; **`streamOkL_P20`**, `slen_P20`,
`cap_P20`, `node_P20`, `clen_P20` are read off it (`passR_sound`, `entF_sound`).
-/

set_option autoImplicit false

namespace Lvm.PlanChk

open RecursionFast Lvm Lvm.Replay Lvm.QLink

/-- The length of an entry's contribution to the reassembled proof (node queries 64 bytes; as
`NS.clen`). -/
def clenC (e : PE) : ℕ :=
  match e.k with
  | .q0 => 0
  | .leaf => e.len
  | _ => e.len - 32

/-- A table lookup: the length of entry `c`, `0` if `c` is not in the table. -/
def capLk : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (k, l) :: r, c => bif Nat.beq k c then l else capLk r c

/-- `entryOk` with the cap entry's length from `lk` (and the comparisons as `Nat.ble`/`Nat.beq`). -/
def entF (lk : ℕ → ℕ) (e : PE) (i : ℕ) : Bool :=
  match e.k with
  | .q0 => Nat.beq i 0 && Nat.beq e.len 7
  | .fs st => Nat.ble 32 e.len && Nat.blt st i && Nat.ble 1 i
  | .leaf => Nat.ble 1 i
  | .node pe h j lvl cap =>
    Nat.beq e.len 64 && Nat.ble 2 i && Nat.blt lvl h && Nat.ble (j % 8 * h + h) 192 &&
      Nat.blt (pe + j / 8) i && Nat.ble 1 (pe + j / 8) &&
      (match cap with
       | none => true
       | some (ce, co, path) => Nat.beq (co % 8) 0 && Nat.ble path h && Nat.ble 32 co &&
           Nat.ble (co + 32 * 2 ^ (h - path)) (lk ce) && Nat.ble 1 ce && Nat.blt ce i)

/-- The checks at entry `i`. -/
def elemF (lk : ℕ → ℕ) (e : PE) (i : ℕ) : Bool :=
  (Nat.beq i 0 || Nat.beq (e.len % 8) 0) && entF lk e i && Nat.ble e.len queryCap

/-- **The one pass** from entry `i` (sums `s1`, `s2` so far, cursor `cur` into the table). -/
noncomputable def passR (lk : ℕ → ℕ) (n t1 t2 : ℕ) (P : List PE) : List (ℕ × ℕ) → ℕ → ℕ → ℕ → Bool :=
  P.rec (fun cur i s1 s2 => cur.isEmpty && Nat.beq i n && Nat.beq s1 t1 && Nat.beq s2 t2)
    (fun e _ ih cur i s1 s2 => elemF lk e i &&
      cur.casesOn (ih [] (i + 1) (s1 + clenC e) (s2 + (40 + e.len)))
        (fun c rest => bif Nat.beq c.1 i then Nat.beq e.len c.2 && ih rest (i + 1) (s1 + clenC e) (s2 + (40 + e.len))
          else ih (c :: rest) (i + 1) (s1 + clenC e) (s2 + (40 + e.len))))

/-! ## Soundness -/

section
variable (lk : ℕ → ℕ) (n t1 t2 : ℕ)

theorem passR_sound : ∀ (P : List PE) (cur : List (ℕ × ℕ)) (i s1 s2 : ℕ),
    passR lk n t1 t2 P cur i s1 s2 = true →
    (∀ k (hk : k < P.length), elemF lk P[k] (i + k) = true) ∧
    (∀ x ∈ cur, i ≤ x.1 ∧ (P.getD (x.1 - i) default).len = x.2) ∧
    i + P.length = n ∧ s1 + (P.map clenC).sum = t1 ∧ s2 + (P.map fun e => 40 + e.len).sum = t2
  | [], cur, i, s1, s2, h => by
    change (cur.isEmpty && Nat.beq i n && Nat.beq s1 t1 && Nat.beq s2 t2) = true at h
    simp only [Bool.and_eq_true, List.isEmpty_iff, Nat.beq_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
    simp
  | e :: es, cur, i, s1, s2, h => by
    change (elemF lk e i && cur.casesOn (passR lk n t1 t2 es [] (i + 1) (s1 + clenC e) (s2 + (40 + e.len)))
        (fun c rest => bif Nat.beq c.1 i then Nat.beq e.len c.2 &&
            passR lk n t1 t2 es rest (i + 1) (s1 + clenC e) (s2 + (40 + e.len))
          else passR lk n t1 t2 es (c :: rest) (i + 1) (s1 + clenC e) (s2 + (40 + e.len)))) = true at h
    rw [Bool.and_eq_true] at h
    obtain ⟨he, h⟩ := h
    -- the rest of the pass, from `i + 1`, with the cursor it continues with
    have key : ∃ cur', passR lk n t1 t2 es cur' (i + 1) (s1 + clenC e) (s2 + (40 + e.len)) = true ∧
        ∀ x ∈ cur, (x.1 = i ∧ e.len = x.2) ∨ x ∈ cur' := by
      rcases cur with _ | ⟨c, rest⟩
      · exact ⟨[], h, fun x hx => absurd hx List.not_mem_nil⟩
      · by_cases hc : c.1 = i
        · have h' : (Nat.beq e.len c.2 && passR lk n t1 t2 es rest (i + 1) (s1 + clenC e)
              (s2 + (40 + e.len))) = true := by
            simpa [hc, Nat.beq_refl] using h
          rw [Bool.and_eq_true, Nat.beq_eq] at h'
          refine ⟨rest, h'.2, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl ⟨hc, h'.1⟩
          · exact Or.inr hx
        · have hb : Nat.beq c.1 i = false := by
            cases hq : Nat.beq c.1 i
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true hq) hc
          have h' : passR lk n t1 t2 es (c :: rest) (i + 1) (s1 + clenC e) (s2 + (40 + e.len)) = true := by
            simpa [hb] using h
          exact ⟨c :: rest, h', fun x hx => Or.inr hx⟩
    obtain ⟨cur', hr, hcur⟩ := key
    obtain ⟨h1, h2, h3, h4, h5⟩ := passR_sound es cur' (i + 1) _ _ hr
    refine ⟨fun k hk => ?_, fun x hx => ?_, by simp only [List.length_cons]; omega,
      by simp only [List.map_cons, List.sum_cons]; omega, by simp only [List.map_cons, List.sum_cons]; omega⟩
    · cases k with
      | zero => simpa using he
      | succ k =>
        have := h1 k (by simpa using hk)
        rwa [show i + 1 + k = i + (k + 1) by omega] at this
    · rcases hcur x hx with ⟨hxi, hxl⟩ | hx'
      · refine ⟨hxi.ge, ?_⟩
        rw [hxi, Nat.sub_self, List.getD_cons_zero, hxl]
      · obtain ⟨hle, hl⟩ := h2 x hx'
        refine ⟨by omega, ?_⟩
        rw [show x.1 - i = (x.1 - (i + 1)) + 1 by omega, List.getD_cons_succ, hl]

end

theorem capLk_spec (P : List PE) : ∀ (tbl : List (ℕ × ℕ)), (∀ x ∈ tbl, (P.getD x.1 default).len = x.2) →
    ∀ c, capLk tbl c = (P.getD c default).len ∨ capLk tbl c = 0
  | [], _, _ => Or.inr rfl
  | (k, l) :: r, h, c => by
    by_cases hk : k = c
    · subst hk
      left
      simp only [capLk, Nat.beq_refl, Bool.cond_true]
      exact (h (k, l) (List.mem_cons_self ..)).symm
    · have hb : Nat.beq k c = false := by
        cases hq : Nat.beq k c
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hq) hk
      simp only [capLk, hb, Bool.cond_false]
      exact capLk_spec P r (fun x hx => h x (List.mem_cons_of_mem _ hx)) c

/-- `entF` with a lookup that is the plan's (where it is not `0`) is `entryOk`. -/
theorem entF_sound (P : List PE) (lk : ℕ → ℕ) (hlk : ∀ c, lk c = (P.getD c default).len ∨ lk c = 0)
    (e : PE) (i : ℕ) (h : entF lk e i = true) : entryOk P e i = true := by
  rcases e with ⟨k, len⟩
  cases k with
  | q0 =>
    simp only [entF, entryOk, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at h ⊢
    exact h
  | fs st =>
    simp only [entF, entryOk, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, decide_eq_true_eq] at h ⊢
    exact h
  | leaf =>
    simp only [entF, entryOk, Nat.ble_eq, decide_eq_true_eq] at h ⊢
    exact h
  | node pe hh j lvl cap =>
    rcases cap with _ | ⟨ce, co, path⟩
    · simp only [entF, entryOk, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq,
        decide_eq_true_eq, beq_iff_eq] at h ⊢
      exact h
    · simp only [entF, entryOk, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq,
        decide_eq_true_eq, beq_iff_eq] at h ⊢
      obtain ⟨hA, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩⟩ := h
      refine ⟨hA, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩, h6⟩⟩
      rcases hlk ce with hl | hl
      · rwa [← hl]
      · rw [hl] at h4
        exfalso
        omega

/-! ## The decision at `P20` -/

/-- The cap entries at `P20` and their lengths (the FS queries that absorb the caps). -/
def tbl20 : List (ℕ × ℕ) := [(2, 12320), (3078, 4176), (6854, 4176)]

set_option maxRecDepth 200000 in
/-- **The one decision**: the plan at `P20` passes, with 9,916 entries, `Σ clenC = 1094240`,
`Σ (40 + len) = 1780999`. -/
theorem passR_P20 : passR (capLk tbl20) 9916 1094240 1780999 (plan P20) tbl20 0 0 0 = true := by
  rw [P20_eq]; decide +kernel

theorem sound_P20 :
    (∀ k (hk : k < (plan P20).length), elemF (capLk tbl20) (plan P20)[k] k = true) ∧
    (∀ x ∈ tbl20, ((plan P20).getD x.1 default).len = x.2) ∧
    (plan P20).length = 9916 ∧ ((plan P20).map clenC).sum = 1094240 ∧
    ((plan P20).map fun e => 40 + e.len).sum = 1780999 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := passR_sound _ _ _ _ _ _ _ _ _ passR_P20
  refine ⟨fun k hk => ?_, fun x hx => ?_, by rw [Nat.zero_add] at h3; exact h3,
    by rw [Nat.zero_add] at h4; exact h4, by rw [Nat.zero_add] at h5; exact h5⟩
  · have := h1 k hk
    rwa [Nat.zero_add] at this
  · have := (h2 x hx).2
    rwa [Nat.sub_zero] at this

theorem elem_P20 {k : ℕ} (hk : k < (plan P20).length) : elemF (capLk tbl20) (plan P20)[k] k = true :=
  sound_P20.1 k hk

/-- **QL's stream facts** at `P20` (the first half of `StreamOk P20`). -/
theorem streamOkL_P20 : streamOkL (plan P20) = true := by
  have hlk := capLk_spec (plan P20) tbl20 sound_P20.2.1
  simp only [streamOkL, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun e he => ?_, fun x hx => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have hk' : k + 1 < (plan P20).length := by rw [List.length_tail] at hk; omega
    have h := elem_P20 hk'
    simp only [elemF, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
    simp only [List.getElem_tail, beq_iff_eq]
    omega
  · obtain ⟨hk, he⟩ : ∃ hk : x.2 < (plan P20).length, (plan P20)[x.2] = x.1 := by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      rw [List.getElem?_eq_some_iff] at this
      exact this
    have h := elem_P20 hk
    simp only [elemF, Bool.and_eq_true] at h
    rw [← he]
    exact entF_sound _ _ hlk _ _ h.1.2

/-- `Σ (40 + len)` over the plan's lengths at `P20` (the second half of `StreamOk P20`). -/
theorem slen_P20 : slenS (lens P20) = 1780999 := by
  rw [slenS, lens, List.map_map]
  exact sound_P20.2.2.2.2

theorem length_P20 : (plan P20).length = 9916 := sound_P20.2.2.1

theorem clen_P20 : ((plan P20).map clenC).sum = 1094240 := sound_P20.2.2.2.1

/-- Every planned query is within `queryCap`. -/
theorem cap_P20 : ∀ e ∈ plan P20, e.len ≤ queryCap := by
  intro e he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  have h := elem_P20 hk
  simp only [elemF, Bool.and_eq_true, Nat.ble_eq] at h
  exact h.2

/-- Node queries are 64 bytes. -/
theorem node_P20 : ∀ e ∈ plan P20, ∀ pe h j lvl cap, e.k = .node pe h j lvl cap → e.len = 64 := by
  intro e he pe h j lvl cap hk
  obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem he
  have h := elem_P20 hk'
  simp only [elemF, entF, Bool.and_eq_true] at h
  have h2 := h.1.2
  rw [hk] at h2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h2
  exact h2.1.1.1.1.1.1

end Lvm.PlanChk
