-- New for lvm (WP-14a): the query correspondence for an opening: V_S's driver (`openLoop`,
-- `climb`) and the compiled verifier (`openAll`, `openOne`, `climb`) ask the same leaf and node
-- queries on the same trace, and the rows the compiled verifier returns are the ones the program on
-- the stream reads (`opRows`).
import LvmVEqStream
import LvmReplayBase

/-!
# Openings: the driver and the compiled verifier in lockstep

`climb_sim`: a Merkle climb of `j` levels: the same node queries (`cur ‖ sib` iff the position's bit
is `0`), the body cursor `32·j` further, the stream cursor `104·j` further. `openAll_sim`: the
openings of a list of positions of one commitment (leaf query = the row, the climb, the cap
compare), with the compiled verifier's rows = the rows on the stream at the leaf entries.
-/

set_option autoImplicit false

namespace Lvm.VEq

open RecursionFast Lvm Lvm.FS LeanVM.Parameters LeanVM.Protocol.Compile

/-! ## Bytes -/

theorem toQ_eq {l : List UInt8} {b : ByteArray} (h : blb b = l) : toQ l = b := by
  rw [← h]; exact toQ_qb b

theorem blb_extract (b : ByteArray) (i j : ℕ) : blb (b.extract i j) = ((blb b).drop i).take (j - i) :=
  Lvm.Replay.bl_extract b i j

theorem blb_digestBytes (d : Digest) : blb (digestBytes d) = d.toList := Lvm.Replay.bl_digestBytes d

theorem blb_append (a b : ByteArray) : blb (a ++ b) = blb a ++ blb b := Lvm.Replay.bl_append a b

theorem length_blb (b : ByteArray) : (blb b).length = b.size := by
  simp only [blb, Array.length_toList]; rfl

theorem size_extract_of {b : ByteArray} {i n : ℕ} (h : i + n ≤ b.size) : (b.extract i (i + n)).size = n := by
  rw [← length_blb, blb_extract]; simp [length_blb]; omega

theorem size_digestBytes (d : Digest) : (digestBytes d).size = 32 := by
  rw [← length_blb, blb_digestBytes]; simp

theorem take_drop_blb {b : ByteArray} {o n : ℕ} (h : o + n ≤ b.size) :
    (((blb b).drop o).take n).length = n := by simp [length_blb]; omega

theorem opRows_succ (sig : ByteArray) (wd path n e : ℕ) :
    opRows sig wd path (n + 1) e =
      (rowAt sig (e + 8) wd :: (opRows sig wd path n (e + 40 + 8 * wd + 104 * path)).1,
        (opRows sig wd path n (e + 40 + 8 * wd + 104 * path)).2) := rfl

/-! ## Climbing -/

section Climb

variable (π : ByteArray) (tr : Trace) (q : ℕ)

/-- **A Merkle climb in lockstep.** -/
theorem climb_sim : ∀ (j lvl : ℕ) (cur : Digest) (s : DSt) (i : ℕ) (kc : DSt → Digest → OProg Bool),
    (∀ s' d n, (kc s' d).runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
    (climb π q j lvl cur s kc).runSeq (tr.drop i) = some true →
    ∃ s' top n, (kc s' top).runSeq (tr.drop (i + n)) = some true ∧ s'.off = s.off + nodeBytes * j ∧
      s'.st = s.st ∧ s'.pend = s.pend ∧ s'.caps = s.caps ∧ s'.pos = s.pos ∧
      entOff tr (i + n) = entOff tr i + 104 * j ∧
      ∀ K : Option (Digest × List UInt8) → OProg Bool,
      ((Scheme.climb j cur (q >>> lvl) ((blb π).drop s.off)).bind K).runSeq (tr.drop i) =
        (K (some (top, (blb π).drop s'.off))).runSeq (tr.drop (i + n))
  | 0, lvl, cur, s, i, kc, _, h => ⟨s, cur, 0, h, by simp, rfl, rfl, rfl, rfl, by simp, fun K ↦ by
      simp [Scheme.climb, OProg.bind]⟩
  | j + 1, lvl, cur, s, i, kc, hb, h => by
    rw [climb] at h
    obtain ⟨a, rest, hdrop, h'⟩ := ask_run h
    -- the bound: the climb goes on to the end
    obtain ⟨s₂, d₂, n₂, h₂, -, ho₂, -⟩ := climb_run π q j (lvl + 1) a _ kc rest h'
    have hle : s.off + nodeBytes * (j + 1) ≤ π.size := by
      have := hb s₂ d₂ (i + 1 + n₂) (by rw [← List.drop_drop, ← List.drop_drop, hdrop]; exact h₂)
      rw [ho₂] at this; simp only [nodeBytes] at this ⊢; ring_nf at this ⊢; omega
    have h32 : s.off + 32 ≤ π.size := by simp only [nodeBytes] at hle; omega
    have hrest : tr.drop (i + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
    obtain ⟨s', top, n, h1, h2, h3, h4, h5, h6, h7, h8⟩ := climb_sim j (lvl + 1) a _ (i + 1) kc
      hb
      (by rw [hrest]; exact h')
    refine ⟨s', top, n + 1, by rw [show i + (n + 1) = i + 1 + n by omega]; exact h1, ?_, h3, h4, h5, h6, ?_, ?_⟩
    · rw [h2]; simp only [nodeBytes]; ring
    · -- the node entry is 104 bytes
      have hsz : (if (q >>> lvl) % 2 = 0 then digestBytes cur ++ π.extract s.off (s.off + 32)
          else π.extract s.off (s.off + 32) ++ digestBytes cur).size = 64 := by
        split <;> rw [ByteArray.size_append, size_extract_of h32, size_digestBytes]
      have he := (stream_entry hdrop).2.2
      rw [show i + (n + 1) = i + 1 + n by omega, h7, he, hsz]; ring
    · -- the compiled climb asks the same node query
      intro K
      have hlen : ¬ ((blb π).drop s.off).length < 32 := by simp [length_blb]; omega
      have hq : toQ (if (q >>> lvl) % 2 = 0 then cur.toList ++ ((blb π).drop s.off).take 32
          else ((blb π).drop s.off).take 32 ++ cur.toList) =
          (if (q >>> lvl) % 2 = 0 then digestBytes cur ++ π.extract s.off (s.off + 32)
            else π.extract s.off (s.off + 32) ++ digestBytes cur) := by
        apply toQ_eq
        split <;> simp [blb_append, blb_extract, blb_digestBytes]
      simp only [Scheme.climb, hlen, ↓reduceIte, OProg.bind, hq, hdrop, OProg.runSeq, ↓reduceIte]
      rw [show (q >>> lvl) / 2 = q >>> (lvl + 1) by rw [Nat.shiftRight_succ],
        show ((blb π).drop s.off).drop 32 = (blb π).drop (s.off + 32) by rw [List.drop_drop]]
      rw [← hrest, show i + (n + 1) = i + 1 + n by omega]
      exact h8 K

end Climb

/-! ## Opening -/

theorem oprog_bind_assoc {α β γ : Type} (p : OProg α) (f : α → OProg β) (g : β → OProg γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | query q k ih => simp only [OProg.bind, ih]

theorem bind_query' {α β : Type} (q : ByteArray) (f : Digest → OProg α) (g : α → OProg β) :
    (OProg.query q f).bind g = .query q fun d ↦ (f d).bind g := rfl

theorem bind_ret' {α β : Type} (a : α) (g : α → OProg β) : (OProg.ret a).bind g = g a := rfl

theorem runSeq_query_eq {α : Type} (q : ByteArray) (f : Digest → OProg α) (a : Digest) (rest : Trace) :
    (OProg.query q f).runSeq ((q, a) :: rest) = (f a).runSeq rest := by simp [OProg.runSeq]

@[simp] theorem capI_wd (S : Scheme) (ht wd : ℕ) (b : List UInt8) : (S.capI ht wd b).wd = wd := rfl
@[simp] theorem capI_ht (S : Scheme) (ht wd : ℕ) (b : List UInt8) : (S.capI ht wd b).ht = ht := rfl
@[simp] theorem capI_lv (S : Scheme) (ht wd : ℕ) (b : List UInt8) : (S.capI ht wd b).lv = S.capOf ht wd := rfl

theorem get!_blb (b : ByteArray) (i : ℕ) : b.get! i = (blb b).getD i 0 := Lvm.Replay.get!_bl b i

/-- A cap node of a commitment record. -/
theorem cap_get (S : Scheme) (π : ByteArray) (ht wd capOff k : ℕ) (hk : k < 2 ^ S.capOf ht wd) :
    (S.capI ht wd ((blb π).drop capOff)).cap[k]? = some (digestAt π (capOff + nodeBytes * k)) := by
  simp only [Scheme.capI, digestsOf, Scheme.capBytes]
  rw [List.getElem?_map, List.getElem?_range hk, Option.map_some]
  refine congrArg some ?_
  apply Vector.ext
  intro t ht'
  simp only [dg, digestAt, Vector.getElem_ofFn, get!_blb, nodeBytes]
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_take_of_lt (by
    have : k + 1 ≤ 2 ^ S.capOf ht wd := hk
    nlinarith), List.getElem?_drop, ← List.getD_eq_getElem?_getD]
  rw [show capOff + 32 * k + t = capOff + (32 * k + t) by ring]

section Open

variable (S : Scheme) (π : ByteArray) (tr : Trace)

/-- **An opening in lockstep**: the driver's `openLoop` and the compiled `openAll` ask the same
queries, and the compiled rows are the stream's (`opRows`). -/
theorem openAll_sim (hdecK : S.decK = kOfBytes) (L : Level) (capOff ht wd : ℕ)
    (hht : L.height = ht) (hrow : L.row = 8 * wd) (hpath : L.path = ht - S.capOf ht wd)
    (hlv : S.capOf ht wd ≤ ht) :
    ∀ (ps : List ℕ) (s : DSt) (i : ℕ) (k'' : DSt → OProg Bool),
      (∀ q ∈ ps, q < 2 ^ ht) →
      (∀ s' n, (k'' s').runSeq (tr.drop n) = some true → s'.off ≤ π.size) →
      (openLoop π L capOff ps s k'').runSeq (tr.drop i) = some true →
      ∃ s' n, (k'' s').runSeq (tr.drop (i + n)) = some true ∧ s'.st = s.st ∧ s'.pend = s.pend ∧
        s'.caps = s.caps ∧ s'.pos = s.pos ∧ s.off ≤ s'.off ∧
        (opRows (traceBytesB tr) wd L.path ps.length (entOff tr i)).2 = entOff tr (i + n) ∧
        ∀ Kc : Option (List (List K) × List UInt8) → OProg Bool,
        ((S.openAll (S.capI ht wd ((blb π).drop capOff)) ps ((blb π).drop s.off)).bind Kc).runSeq
            (tr.drop i) =
          (Kc (some ((opRows (traceBytesB tr) wd L.path ps.length (entOff tr i)).1,
            (blb π).drop s'.off))).runSeq (tr.drop (i + n))
  | [], s, i, k'', _, _, h => ⟨s, 0, h, rfl, rfl, rfl, rfl, le_rfl, rfl, fun Kc ↦ by simp [Scheme.openAll, OProg.bind, opRows]⟩
  | q :: qs, s, i, k'', hps, hk, h => by
    obtain ⟨d₀, rest, hdrop, h'⟩ := ask_run h
    have hrest : tr.drop (i + 1) = rest := by rw [← List.drop_drop, hdrop]; rfl
    -- the climb's continuation reaches the next positions, whose run bounds the body
    have hkc : ∀ s' d n, ((fun s top ↦ if top == digestAt π (capOff + nodeBytes * (q >>> L.path)) then
        openLoop π L capOff qs s k'' else OProg.ret false) s' d).runSeq (tr.drop n) = some true →
        s'.off ≤ π.size := by
      intro s' d n hh
      simp only at hh
      split at hh
      · obtain ⟨s'', n', h1, -, h3, -⟩ := openLoop_run π L capOff qs s' k'' _ hh
        have := hk s'' (n + n') (by rw [← List.drop_drop]; exact h1)
        omega
      · exact absurd (runSeq_ret_true hh).2 (by simp)
    obtain ⟨s₁, top, n₁, h1, ho1, hst1, hpe1, hca1, hpo1, he1, hc1⟩ :=
      climb_sim π tr q L.path 0 d₀ _ (i + 1) _
        hkc (by rw [hrest]; exact h')
    have hb1 := hkc _ _ _ h1
    simp only at ho1
    have hoff : s.off + L.row ≤ π.size := by rw [ho1] at hb1; omega
    -- the cap check held
    split at h1
    · rename_i hcap
      have htop : top = digestAt π (capOff + nodeBytes * (q >>> L.path)) := by simpa using hcap
      obtain ⟨s', n, h2, hst, hpe, hca, hpo, hle, he2, hc2⟩ := openAll_sim hdecK L capOff ht wd hht hrow hpath hlv
        qs s₁ (i + 1 + n₁) k'' (fun q' hq' ↦ hps q' (List.mem_cons_of_mem _ hq')) hk h1
      refine ⟨s', n₁ + 1 + n, by rw [show i + (n₁ + 1 + n) = i + 1 + n₁ + n by omega]; exact h2,
        by rw [hst, hst1], by rw [hpe, hpe1], by rw [hca, hca1], by rw [hpo, hpo1], ?_, ?_, ?_⟩
      · have : s₁.off ≤ s'.off := hle
        omega
      · have hsz : (π.extract s.off (s.off + L.row)).size = 8 * wd := by rw [size_extract_of hoff, hrow]
        have he0 := (stream_entry hdrop).2.2
        rw [List.length_cons, opRows_succ]
        dsimp only
        rw [show i + (n₁ + 1 + n) = i + 1 + n₁ + n by omega, ← he2, he1, he0, hsz]
        exact congrArg (fun e ↦ (opRows (traceBytesB tr) wd L.path qs.length e).2) (by ring)
      · intro Kc
        have hlen : ¬ ((blb π).drop s.off).length < 8 * wd := by
          rw [List.length_drop, length_blb]; rw [hrow] at hoff; omega
        have hq : toQ (((blb π).drop s.off).take (8 * wd)) = π.extract s.off (s.off + L.row) := by
          apply toQ_eq; rw [blb_extract, hrow, show s.off + 8 * wd - s.off = 8 * wd by omega]
        have hq0 : q < 2 ^ ht := hps q List.mem_cons_self
        have hqmod : q % 2 ^ ht = q >>> 0 := by rw [Nat.mod_eq_of_lt hq0]; rfl
        have hcapk : (S.capI ht wd ((blb π).drop capOff)).cap[q % 2 ^ ht / 2 ^ (ht - S.capOf ht wd)]? =
            some top := by
          rw [Nat.mod_eq_of_lt hq0, cap_get, htop, Nat.shiftRight_eq_div_pow, hpath]
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm,
            Nat.sub_add_cancel hlv]
          exact hq0
        have hrow0 : rowOf S.decK wd (((blb π).drop s.off).take (8 * wd)) =
            rowAt (traceBytesB tr) (entOff tr i + 8) wd := by
          have hsz : (π.extract s.off (s.off + L.row)).size = 8 * wd := by
            rw [size_extract_of hoff, hrow]
          have := (stream_entry hdrop).1 0 (8 * wd) (by rw [hsz]; omega)
          simp only [Nat.add_zero, List.drop_zero] at this
          rw [rowAt, hdecK, this, blb_extract, hrow, show s.off + 8 * wd - s.off = 8 * wd by omega,
            List.take_take, min_self]
        rw [hqmod, ← hpath] at hcapk
        have hdd : ((blb π).drop s.off).drop (8 * wd) = (blb π).drop (s.off + L.row) := by
          rw [List.drop_drop, hrow]
        rw [Scheme.openAll, oprog_bind_assoc, Scheme.openOne,
          if_neg (show ¬ ((blb π).drop s.off).length < 8 * (S.capI ht wd ((blb π).drop capOff)).wd from hlen)]
        simp only [capI_wd, capI_ht, capI_lv, bind_query', hq, hdrop, runSeq_query_eq,
          oprog_bind_assoc, hqmod, ← hpath, hdd]
        simp only at hc1
        rw [← hrest, hc1]
        simp only [bind_ret', hcapk, ↓reduceIte, hrow0]
        rw [oprog_bind_assoc, hc2, bind_ret', List.length_cons, opRows_succ,
          show i + (n₁ + 1 + n) = i + 1 + n₁ + n by omega]
        have hent : entOff tr (i + 1 + n₁) = entOff tr i + 40 + 8 * wd + 104 * L.path := by
          rw [he1, (stream_entry hdrop).2.2, size_extract_of hoff, hrow]; ring
        rw [hent]
    · exact absurd (runSeq_ret_true h1).2 (by simp)

end Open

end Lvm.VEq
