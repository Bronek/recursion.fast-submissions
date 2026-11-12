-- New for lvm (INB): Q_link's `readd`s are in region. The address computations are WP-11b-QL's
-- (`LvmQLinkGadgets.qltLoop_spec`, `capLoop_spec`: the parts that do not use the gate or the
-- assertions, adapted) and the opening walk is `LvmQLinkSound.open_facts`'s.
import LvmQAsmInbCore
import LvmQLinkSound

/-!
# Q_link's `readd` addresses

Q_link reads by address in two places, both into the stream region `[sb, sb + 2^m)`:

* the **QLT loop**: the table cells `g^e₁`, `g^e₂` and `g^l` times them (`qltLoop_in`);
* the **cap loops**: `g^(lo + 4·Σ_z β_z 2^z + i)`, `i < 4`, from the cap bits of each (padded)
  position (`capLoop_in`, `capAddr`). With every bit cell `0` or `1` the exponent is below
  `lo + 4·2^c` (`bitSum_lt`).

Neither uses the gate or any assertion: the address is a function of the rows alone.
**`qlink_in`**: with `QOk`, the QLT cells holding `qltData` and the cap bits of every position
`j < padT t` of every opening being bits, every `readd` of `qlink p lay` is in region (`InOk`).
-/

set_option autoImplicit false

namespace Lvm.Loop.Build

open Lvm.Loop

/-- The region condition from an address `g^e`, `lo ≤ e < lo + 2^m`. -/
theorem rd_of_gpow {v : FE} {e lo m : Nat} (hv : v = FE.ofK (gpow e)) (h1 : lo ≤ e) (h2 : e < lo + 2 ^ m) :
    ∃ k < 2 ^ m, FK.x ^ (lo + k) = v.c₀ :=
  ⟨e - lo, by omega, by rw [hv, show lo + (e - lo) = e by omega]; rfl⟩

/-! ## The QLT loop -/

theorem qltLoop_in {c : Ctx} {M : Mem} {p : Ptr} {a qt lo m g : Nat}
    (h : SegsHold c M p (qltLoop a qt lo m (kc g) p).2)
    (hE : ∀ jf < 2 ^ a, ∃ e₁ e₂, M.k (qt + 3 * jf) = gpow e₁ ∧ M.k (qt + 1 + 3 * jf) = gpow e₂ ∧
      lo ≤ e₁ ∧ e₁ + 5 ≤ lo + 2 ^ m ∧ lo ≤ e₂ ∧ e₂ + 4 ≤ lo + 2 ^ m) :
    SegsIn M p (qltLoop a qt lo m (kc g) p).2 := by
  simp only [qltLoop, hold_bind] at h
  simp only [qltLoop, in_bind, SegsIn, and_true]
  refine ⟨loop_in (fun jf hjf t ht lo' m' args hr => ?_) (fun t ht lo' m' hop => ?_), trivial⟩
  · have hj : jf < 2 ^ [a].sum := by simpa using hjf
    have hjf' : jf < 2 ^ a := by simpa using hjf
    obtain ⟨e₁, e₂, hα, hβ, h1, h2, h3, h4⟩ := hE jf hjf'
    set o : LoopOut := ⟨p, [a], qltTpl qt lo m (kc g)⟩ with ho
    have hR : ∀ t < 26, LRel c M o jf t := fun t ht => loop_rel h.1 hj (t := t) (by simp [qltTpl]; omega)
    have hu : unflat o.dims jf = [jf] := unflat_one' hj
    have vα : (Opd.abs ⟨.K, qt, [3]⟩).val M o jf = FE.ofK (gpow e₁) := by
      rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]; rw [hα]
    have vβ : (Opd.abs ⟨.K, qt + 1, [3]⟩).val M o jf = FE.ofK (gpow e₂) := by
      rw [Opd.val_absK, hu]; simp only [dot, Nat.add_zero]; rw [hβ]
    have hadr : ∀ (t l e : Nat) (x : Opd), o.tpl.getD t default = ⟨.lin (gpow l + 1) 0, .K, [x, x]⟩ →
        x.val M o jf = FE.ofK (gpow e) → t < 26 → (Opd.cur t).val M o jf = FE.ofK (gpow (e + l)) := by
      intro t l e x hr hx ht
      rw [Opd.val_cur _ _ hj, lrel_lin hr (hR t ht)]
      simp only [List.getD_cons_zero, List.getD_cons_succ, hx, ofK_zero, add_zero]
      rw [← ofK_mul, ← ofK_add, ← gpow_scale l e, add_zero]
    have a1 := hadr 0 1 e₁ _ rfl vα (by omega)
    have a2 := hadr 1 2 e₁ _ rfl vα (by omega)
    have a3 := hadr 2 3 e₁ _ rfl vα (by omega)
    have a4 := hadr 3 4 e₁ _ rfl vα (by omega)
    have b1 := hadr 4 1 e₂ _ rfl vβ (by omega)
    have b2 := hadr 5 2 e₂ _ rfl vβ (by omega)
    have b3 := hadr 6 3 e₂ _ rfl vβ (by omega)
    have ht26 : t < 26 := by simpa [qltTpl] using ht
    interval_cases t <;>
      simp only [qltTpl, List.getD_cons_succ, List.getD_cons_zero, LRow.mk.injEq, Op.readd.injEq,
        reduceCtorEq, false_and] at hr <;> obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := hr <;>
      simp only [List.getD_cons_zero] <;>
      first
      | (rw [vα]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [vβ]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [a1]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [a2]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [a3]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [a4]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [b1]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [b2]; exact rd_of_gpow rfl (by omega) (by omega))
      | (rw [b3]; exact rd_of_gpow rfl (by omega) (by omega))
  · have ht26 : t < 26 := by simpa [qltTpl] using ht
    interval_cases t <;> simp only [qltTpl, List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq] at hop ⊢

/-! ## The cap loops -/

/-- The rows of the cap template past the address chain (`capLoop_spec`'s `hpost`). -/
theorem capTpl_post (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) (hc : 1 ≤ c) (i : Nat) :
    (capTpl lenL row A lo rlo m s bt sb c z sz).getD (2 * c + 1 + i) default =
      ([⟨.lin (gpow 1 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩, ⟨.lin (gpow 2 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
       ⟨.lin (gpow 3 + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩,
       ⟨.readd rlo m, .K, [.cur (2 * c)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 1)]⟩, ⟨.readd rlo m, .K, [.cur (2 * c + 2)]⟩,
       ⟨.readd rlo m, .K, [.cur (2 * c + 3)]⟩,
       ⟨.lin 1 0, .K, [.cur (2 * c + 4), .abs ⟨.K, A, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 8), .abs ⟨.K, z, sz⟩]⟩,
       ⟨.lin 1 0, .K, [.cur (2 * c + 5), .abs ⟨.K, A + 1, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 10), .abs ⟨.K, z, sz⟩]⟩,
       ⟨.lin 1 0, .K, [.cur (2 * c + 6), .abs ⟨.K, A + 2, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 12), .abs ⟨.K, z, sz⟩]⟩,
       ⟨.lin 1 0, .K, [.cur (2 * c + 7), .abs ⟨.K, A + 3, s⟩]⟩, ⟨.assert0, .K, [.cur (2 * c + 14), .abs ⟨.K, z, sz⟩]⟩] :
        List LRow).getD i default := by
  have e : 2 * c + 1 + i = [(default : LRow), default, default].length + (capChain bt sb c).length + i := by
    simp [capChain_length]; omega
  rw [e]; exact getD_app3

theorem capTpl_length (lenL row A lo rlo m : Nat) (s : List Nat) (bt : Nat) (sb : List Nat) (c z : Nat)
    (sz : List Nat) (hc : 1 ≤ c) : (capTpl lenL row A lo rlo m s bt sb c z sz).length = 2 * c + 16 := by
  simp [capTpl, capChain_length]; omega

/-- **The cap address chain** (`capLoop_spec`'s chain, without the gate): with Boolean cap bits, the
addresses at rows `2c + i` are `g^(lo + 4·idx + i)`, `i < 4`. -/
theorem capAddr {cx : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {lenL row A lo rlo m bt c z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold cx M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2) {jf : Nat} (hjf : jf < 2 ^ dims.sum)
    (hc : 1 ≤ c)
    (hb : ∀ y < c, M.k (bt + y + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + y + dot sb (unflat dims jf)) = 1) :
    ∀ i < 4, (Opd.cur (2 * c + i)).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
      FE.ofK (gpow (lo + 4 * bitSum M bt sb (unflat dims jf) c + i)) := by
  simp only [capLoop, hold_bind] at h
  have hlen := capTpl_length lenL row A lo rlo m s bt sb c z sz hc
  have hR := fun t (ht : t < 2 * c + 16) => loop_rel h.1 hjf (t := t) (by rw [hlen]; exact ht)
  generalize hJ : unflat dims jf = J at *
  have vK : ∀ (b : Nat) (st : List Nat),
      (Opd.abs ⟨.K, b, st⟩).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
        FE.ofK (M.k (b + dot st J)) := fun b st => by
    rw [Opd.val_absK]; show _ = FE.ofK (M.k (b + dot st J)); rw [← hJ]; rfl
  have vc : ∀ t, (Opd.cur t).val M (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1 jf =
      ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell t jf).val M := fun t => Opd.val_cur _ _ hjf t
  have hpost := capTpl_post lenL row A lo rlo m s bt sb c z sz hc
  have chain : ∀ y < c, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * y + 2) jf).val M =
      FE.ofK (gpow (lo + 4 * bitSum M bt sb J (y + 1))) := by
    intro y
    induction y with
    | zero =>
      intro _
      have h2 := lrel_lin (t := 2) rfl (hR 2 (by omega))
      simp only [List.getD_cons_zero, List.getD_cons_succ, vK] at h2
      rw [h2, ← ofK_mul, ← ofK_add, ← ofK_add]
      congr 1
      rw [bitSum_succ, show bitSum M bt sb J 0 = 0 from rfl, Nat.zero_add, Nat.add_zero]
      rcases hb 0 hc with h0 | h1
      · simp only [Nat.add_zero] at h0; rw [h0]; simp [show (0 : FK) ≠ 1 from by decide, gpow]
      · simp only [Nat.add_zero] at h1
        rw [h1, if_pos rfl, mul_one]
        have e : (1 : FK) + (gpow lo * (gpow 4 + 1) + 1) + gpow lo =
            gpow lo * gpow 4 + ((1 + 1) + (gpow lo + gpow lo)) := by ring
        rw [e, FK.add_self, FK.add_self, add_zero, add_zero, ← gpow_add]
        simp
    | succ y ih =>
      intro hy
      have ihv := ih (by omega)
      obtain ⟨k1, k2⟩ := capChain_getD bt sb c y hy
      have r1 := capTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y) (by omega)
      have r2 := capTpl_chain lenL row A lo rlo m s bt sb c z sz (i := 2 * y + 1) (by omega)
      rw [k1] at r1; rw [k2] at r2
      rw [show 3 + 2 * y = 2 * y + 3 by omega] at r1
      rw [show 3 + (2 * y + 1) = 2 * (y + 1) + 2 by omega] at r2
      have e1 := lrel_lin r1 (hR _ (by omega))
      have e2 := lrel_muladd r2 (hR _ (by omega))
      simp only [List.getD_cons_zero, List.getD_cons_succ, vK, vc, ofK_zero, add_zero] at e1 e2
      rw [show 2 * (y + 1) = 2 * y + 2 by ring] at e1 e2
      rw [show 2 * y + 2 + 1 = 2 * y + 3 by ring] at e2
      rw [show 2 * (y + 1) + 2 = 2 * y + 2 + 2 by ring, e2, e1, ihv]
      simp only [← ofK_mul, ← ofK_add]
      congr 1
      have hsel := bit_select (gpow (lo + 4 * bitSum M bt sb J (y + 1))) (gpow (4 * 2 ^ (y + 1)))
        (M.k (bt + (y + 1) + dot sb J)) (hb (y + 1) hy)
      rw [add_zero] at hsel
      rw [hsel, bitSum_succ (n := y + 1)]
      split_ifs with hβ
      · rw [← gpow_add]; congr 1; ring
      · simp
  have hα0 := chain (c - 1) (by omega)
  rw [show 2 * (c - 1) + 2 = 2 * c by omega, show c - 1 + 1 = c by omega] at hα0
  generalize bitSum M bt sb J c = idx at hα0 ⊢
  have sc : ∀ i < 3, ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M =
      FE.ofK (gpow (lo + 4 * idx + (i + 1))) := by
    intro i hi
    have key : ∀ l, (loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.tpl.getD (2 * c + 1 + i) default =
        ⟨.lin (gpow l + 1) 0, .K, [.cur (2 * c), .cur (2 * c)]⟩ → l = i + 1 →
        ((loop dims (capTpl lenL row A lo rlo m s bt sb c z sz) p).1.cell (2 * c + 1 + i) jf).val M =
          FE.ofK (gpow (lo + 4 * idx + (i + 1))) := by
      intro l hr hl
      have e := lrel_lin hr (hR _ (by omega))
      simp only [List.getD_cons_zero, List.getD_cons_succ, vc, hα0, ofK_zero, add_zero] at e
      rw [e, ← ofK_mul, ← ofK_add, ← hl, ← gpow_scale l, add_zero]
    interval_cases i
    · exact key 1 (hpost 0) rfl
    · exact key 2 (hpost 1) rfl
    · exact key 3 (hpost 2) rfl
  intro i hi
  rw [vc]
  rcases i with _ | i
  · simpa using hα0
  · have := sc i (by omega); rw [show 2 * c + (i + 1) = 2 * c + 1 + i by omega, this]

/-- **A cap loop's `readd`s are in region**: Boolean cap bits at every iteration, and the cap
region `[lo, lo + 4·2^c)` inside the `readd` region `[rlo, rlo + 2^m)`. -/
theorem capLoop_in {cx : Ctx} {M : Mem} {p : Ptr} {dims : List Nat} {lenL row A lo rlo m bt c z : Nat}
    {s sb sz : List Nat}
    (h : SegsHold cx M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2) (hc : 1 ≤ c)
    (hb : ∀ jf < 2 ^ dims.sum, ∀ y < c,
      M.k (bt + y + dot sb (unflat dims jf)) = 0 ∨ M.k (bt + y + dot sb (unflat dims jf)) = 1)
    (h1 : rlo ≤ lo) (h2 : lo + 4 * 2 ^ c ≤ rlo + 2 ^ m) :
    SegsIn M p (capLoop dims lenL row A lo rlo m s bt sb c z sz p).2 := by
  have hlen := capTpl_length lenL row A lo rlo m s bt sb c z sz hc
  have hpost := capTpl_post lenL row A lo rlo m s bt sb c z sz hc
  -- the rows before the post rows are not `readd`s
  have hpre : ∀ t < 2 * c + 1, ¬ ∃ lo' m', ((capTpl lenL row A lo rlo m s bt sb c z sz).getD t default).op =
      .readd lo' m' := by
    rintro t ht ⟨lo', m', hop⟩
    by_cases h3 : t < 3
    · interval_cases t <;> simp [capTpl] at hop
    · obtain ⟨i, rfl⟩ : ∃ i, t = 3 + i := ⟨t - 3, by omega⟩
      rw [capTpl_chain _ _ _ _ _ _ _ _ _ _ _ _ (by omega)] at hop
      rcases Nat.even_or_odd' i with ⟨y, rfl | rfl⟩
      · have hy : y + 1 < c := by omega
        rw [(capChain_getD bt sb c y hy).1] at hop; simp at hop
      · have hy : y + 1 < c := by omega
        rw [(capChain_getD bt sb c y hy).2] at hop; simp at hop
  simp only [capLoop, hold_bind] at h
  simp only [capLoop, in_bind, SegsIn, and_true]
  refine ⟨loop_in (fun jf hjf t ht lo' m' args hr => ?_) (fun t ht lo' m' hop => ?_), trivial⟩
  · have hA := capAddr (p := p) (h := by simp only [capLoop, hold_bind]; exact ⟨h.1, trivial⟩) hjf hc (hb jf hjf)
    have hidx := bitSum_lt M bt sb (unflat dims jf) c
    rw [hlen] at ht
    by_cases ht1 : t < 2 * c + 1
    · exact absurd ⟨lo', m', by rw [hr]⟩ (hpre t ht1)
    · obtain ⟨i, rfl⟩ : ∃ i, t = 2 * c + 1 + i := ⟨t - (2 * c + 1), by omega⟩
      rw [hpost i] at hr
      have hi : i < 15 := by omega
      have hf : 4 * bitSum M bt sb (unflat dims jf) c + 4 ≤ 4 * 2 ^ c := by omega
      interval_cases i <;> simp at hr <;> obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hr <;>
        simp only [List.getD_cons_zero]
      · exact rd_of_gpow (hA 0 (by omega)) (by omega) (by omega)
      · exact rd_of_gpow (hA 1 (by omega)) (by omega) (by omega)
      · exact rd_of_gpow (hA 2 (by omega)) (by omega) (by omega)
      · exact rd_of_gpow (hA 3 (by omega)) (by omega) (by omega)
  · rw [hlen] at ht
    by_cases ht1 : t < 2 * c + 1
    · exact absurd ⟨lo', m', hop⟩ (hpre t ht1)
    · obtain ⟨i, rfl⟩ : ∃ i, t = 2 * c + 1 + i := ⟨t - (2 * c + 1), by omega⟩
      rw [hpost i] at hop ⊢
      have hi : i < 15 := by omega
      interval_cases i <;> simp at hop ⊢

end Lvm.Loop.Build

namespace Lvm.QLink

open RecursionFast Lvm Lvm.Replay Lvm.Loop Lvm.Loop.Build

/-! ## Q_link -/

theorem pchunks_end {t : Nat} : ∀ c ∈ pchunks t, c.1 + 2 ^ c.2 ≤ padT t := by
  intro c hc
  unfold padT
  by_cases h : t = 2 ^ t.log2
  · rw [pchunks, if_pos h] at hc ⊢
    rw [List.mem_singleton] at hc
    subst hc; simp
  · rw [pchunks, if_neg h] at hc ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp

theorem qltPadded_mem (p : Params) (lay : Layout) {jf : Nat} (hjf : jf < (qltPadded p lay).length) :
    (qltPadded p lay).getD jf (0, 0, 0) ∈ qltEntries p lay := by
  have h0 : (lay.sb, lay.sb + 1, lane0C) ∈ qltEntries p lay := by simp [qltEntries]
  unfold qltPadded at hjf ⊢
  rw [List.getD_eq_getElem _ _ hjf]
  rcases List.mem_append.mp (List.getElem_mem hjf) with h | h
  · exact h
  · rw [List.eq_of_mem_replicate h]; exact h0

variable {p : Params} {lay : Layout} {c : Ctx} {M : Mem}

/-- **Every `readd` of Q_link is in region** (its rows holding in `M`): the QLT cells hold
`qltData`, and every cap bit of every padded position is a bit. -/
theorem qlink_in (hQ : QOk p lay)
    (htab : ∀ x < (qltData p lay).length, M.k (lay.qt + x) = (qltData p lay).getD x 0)
    (hbits : ∀ k < (opens p).length, ∀ j < padT ((opens p).getD k default).L.t,
      ∀ z < ((opens p).getD k default).L.height,
      M.k (bitBase p lay k + ((opens p).getD k default).L.height * j + z) = 0 ∨
        M.k (bitBase p lay k + ((opens p).getD k default).L.height * j + z) = 1) :
    InOk c M (qlink p lay) := by
  have ho : ∀ k < (opens p).length, (opens p).getD k default ∈ opens p := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  -- the QLT loop
  have hqlt : ∀ zo : Nat, InOk c M (qltLoop lay.aQ lay.qt lay.sb lay.m (kc lay.fg)) := by
    intro _ q h
    refine qltLoop_in h fun jf hjf => ?_
    have hl := qltPadded_length p lay hQ.qlen
    have hlen : (qltData p lay).length = 3 * 2 ^ lay.aQ := by rw [qltData, tblOf_length, hl]
    obtain ⟨g1, g2, -⟩ := tblOf_getD (qltPadded p lay) (k := jf) (by omega)
    obtain ⟨b1, b2, b3, b4, -⟩ := hQ.qbound _ (qltPadded_mem p lay (jf := jf) (by omega))
    refine ⟨_, _, ?_, ?_, b1, b3, b2, b4⟩
    · rw [htab _ (by omega)]; exact g1
    · rw [show lay.qt + 1 + 3 * jf = lay.qt + (3 * jf + 1) by omega, htab _ (by omega)]; exact g2
  -- one opening
  have hopen : ∀ zo k, k < (opens p).length →
      InOk c M (openLoops p lay zo (bitBase p lay k) ((opens p).getD k default)) := by
    intro zo k hk
    obtain ⟨hp1, hph, -, hcap, -⟩ := hQ.opens _ (ho k hk)
    generalize hog : (opens p).getD k default = o at hbits hp1 hph hcap
    have hb := hbits k hk
    rw [hog] at hb
    unfold openLoops
    refine inOk_bind (inOk_seqAll _ fun m hm => ?_) fun _ => inOk_pure _
    obtain ⟨cc, hcc, rfl⟩ := List.mem_map.mp hm
    have hend := pchunks_end cc hcc
    refine inOk_bind (fun q h => capLoop_in h (by omega) (fun jf hjf y hy => ?_) (by omega) (by omega))
      fun _ => inOk_bind (inOk_seqAll _ fun m' hm' => ?_) fun _ => inOk_pure _
    · have hj : jf < 2 ^ cc.2 := by simpa using hjf
      simp only [unflat_one' hjf, Loop.dot, Nat.add_zero]
      rw [show bitBase p lay k + o.L.height * cc.1 + o.L.path + y + o.L.height * jf =
        bitBase p lay k + o.L.height * (cc.1 + jf) + (o.L.path + y) by rw [Nat.mul_add]; omega]
      exact hb _ (by omega) _ (by omega)
    · obtain ⟨dd, -, rfl⟩ := List.mem_map.mp hm'
      exact inOk_noReadd fun _ => rfl
  unfold qlink qlinkCore
  refine inOk_bind (inOk_noReadd fun _ => rfl) fun _ =>
    inOk_bind (inOk_noReadd fun _ => rfl) fun q => inOk_bind (hqlt 0) fun _ =>
      inOk_bind (inOk_seqAll _ fun m hm => ?_) fun _ => inOk_pure _
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
  exact hopen _ k (List.mem_range.mp hk)

end Lvm.QLink
