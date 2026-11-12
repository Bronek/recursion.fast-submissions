import LvmLoopRows

/-!
# Pieces partition the instances

A block's template rows are cut by shape (`Block.shapes`, `Block.rowsOf`) and each shape's rows by
the binary decomposition of their count (`binParts`, `chunks`): every template row lies in exactly
one piece, at one position, and a piece has `2^a` rows. So the piece rows `(n, p, x)` of the program
(`Program.prows`) and its instances are in bijection by `Program.pinst`:

* `prow_inst`: a piece row is an instance of the program, of the piece's shape;
* `inst_prow`: every instance is a piece row (`pinst p x`);
* `prow_inj`: two piece rows with one instance are one piece row.

Proof-help for `LvmLoopSound` (one seed per cell, and every row relation from a table row).
-/

namespace Lvm.Loop

/-! ## Binary decomposition and chunks -/

theorem bitsUp_sum : ∀ (f k n : Nat), n < 2 ^ f → ((bitsUp f k n).map (2 ^ ·)).sum = 2 ^ k * n
  | 0, k, n, h => by simp at h; subst h; simp [bitsUp]
  | f + 1, k, n, h => by
    have ih := bitsUp_sum f (k + 1) (n / 2) (by rw [Nat.pow_succ] at h; omega)
    simp only [bitsUp, List.map_append, List.sum_append, ih]
    split
    · have hn : n = 2 * (n / 2) + 1 := by omega
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      conv_rhs => rw [hn]
      ring
    · have hn : n = 2 * (n / 2) := by omega
      simp only [List.map_nil, List.sum_nil, Nat.zero_add]
      conv_rhs => rw [hn]
      ring

theorem binParts_sum (n : Nat) : ((binParts n).map (2 ^ ·)).sum = n := by
  have h : n < 2 ^ (n + 1) := Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by omega) (by omega))
  rw [binParts, List.map_reverse, List.sum_reverse, bitsUp_sum _ _ _ h]; simp

theorem chunks_spec : ∀ (as l : List Nat), (as.map (2 ^ ·)).sum = l.length →
    (chunks as l).flatMap (·.2) = l ∧ ∀ c ∈ chunks as l, c.2.length = 2 ^ c.1
  | [], l, h => by simp at h; simp [chunks, List.eq_nil_of_length_eq_zero h.symm]
  | a :: as, l, h => by
    simp only [List.map_cons, List.sum_cons] at h
    obtain ⟨ih1, ih2⟩ := chunks_spec as (l.drop (2 ^ a)) (by simp; omega)
    refine ⟨by simp [chunks, ih1], fun c hc => ?_⟩
    simp only [chunks, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp; omega
    · exact ih2 c hc

/-! ## Distinct shapes -/

theorem mem_nub {α : Type} [DecidableEq α] : ∀ (l : List α) (y : α), y ∈ nub l ↔ y ∈ l
  | [], _ => by simp [nub]
  | x :: xs, y => by
    simp only [nub, List.mem_cons, List.mem_filter, mem_nub xs, decide_eq_true_eq]
    by_cases h : y = x <;> simp [h]

theorem nodup_nub {α : Type} [DecidableEq α] : ∀ (l : List α), (nub l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    rw [nub, List.nodup_cons]
    exact ⟨fun h => by simp [List.mem_filter] at h, (nodup_nub xs).filter _⟩

/-- Filters of a nodup list by the values of a function, over a nodup list of values covering it,
are a permutation of the list. -/
theorem flatMap_filter_perm {α β : Type} [DecidableEq β] (l : List α) (hl : l.Nodup) (f : α → β)
    (S : List β) (hS : S.Nodup) (hcov : ∀ x ∈ l, f x ∈ S) :
    (S.flatMap fun s => l.filter fun x => decide (f x = s)).Perm l := by
  rw [List.perm_ext_iff_of_nodup _ hl]
  · intro x
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun ⟨_, _, h, _⟩ => h, fun h => ⟨f x, hcov x h, h, rfl⟩⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun s _ => hl.filter _, ?_⟩
    refine hS.imp fun {s s'} hne => ?_
    intro x hx hx'
    simp only [List.mem_filter, decide_eq_true_eq] at hx hx'
    exact hne (hx.2.symm.trans hx'.2)

/-! ## The pieces of a block -/

namespace Block

variable (B : Block)

theorem shapes_rowsOf_perm : (B.shapes.flatMap B.rowsOf).Perm (List.range B.tpl.length) := by
  apply flatMap_filter_perm _ List.nodup_range _ _ (nodup_nub _)
  intro t ht
  rw [List.mem_range] at ht
  rw [mem_nub, List.mem_map]
  exact ⟨_, by simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    Option.getD_some]; exact List.getElem_mem ht, rfl⟩

theorem pieces_ts (b : Nat) : ((B.pieces b).flatMap (·.ts)).Perm (List.range B.tpl.length) := by
  have : (B.pieces b).flatMap (·.ts) = B.shapes.flatMap B.rowsOf := by
    simp only [pieces, List.flatMap_assoc, List.flatMap_map]
    congr 1; funext σ
    exact (chunks_spec _ _ (binParts_sum _)).1
  rw [this]; exact B.shapes_rowsOf_perm

theorem mem_pieces {b : Nat} {p : Piece} (hp : p ∈ B.pieces b) :
    p.blk = b ∧ p.ts.length = 2 ^ p.a ∧
      ∀ t ∈ p.ts, t < B.tpl.length ∧ (B.tpl.getD t default).shape = p.shape := by
  simp only [pieces, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨σ, -, ⟨a, ts⟩, hc, rfl⟩ := hp
  refine ⟨rfl, (chunks_spec _ _ (binParts_sum _)).2 _ hc, fun t ht => ?_⟩
  have : t ∈ B.rowsOf σ := by
    rw [← (chunks_spec (binParts (B.rowsOf σ).length) (B.rowsOf σ) (binParts_sum _)).1,
      List.mem_flatMap]
    exact ⟨_, hc, ht⟩
  simp only [rowsOf, List.mem_filter, List.mem_range, decide_eq_true_eq] at this
  exact this

end Block

/-! ## The pieces of a program -/

namespace Program

variable (Q : Program)

theorem mem_pieces {p : Piece} (hp : p ∈ Q.pieces) :
    p.blk < Q.blocks.length ∧ p.ts.length = 2 ^ p.a ∧
      ∀ t ∈ p.ts, t < (Q.blk p.blk).tpl.length ∧ ((Q.blk p.blk).tpl.getD t default).shape = p.shape := by
  simp only [pieces, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨b, hb, hp⟩ := hp
  obtain ⟨h1, h2, h3⟩ := (Q.blk b).mem_pieces hp
  subst h1
  exact ⟨hb, h2, h3⟩

/-- Every (block, template row) pair, through the pieces: each once. -/
theorem pieces_bt_nodup : (Q.pieces.flatMap fun p => p.ts.map (p.blk, ·)).Nodup := by
  have : (Q.pieces.flatMap fun p => p.ts.map (p.blk, ·)) =
      (List.range Q.blocks.length).flatMap fun b =>
        (((Q.blk b).pieces b).flatMap (·.ts)).map (b, ·) := by
    simp only [pieces, List.flatMap_assoc]
    congr 1; funext b
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro p hp
    rw [((Q.blk b).mem_pieces hp).1]
  rw [this, List.nodup_flatMap]
  refine ⟨fun b _ => ((Q.blk b).pieces_ts b).nodup_iff.mpr List.nodup_range |>.map
    (fun _ _ h => (Prod.mk.inj h).2), ?_⟩
  refine List.nodup_range.imp fun {b b'} hne => ?_
  intro x hx hx'
  simp only [List.mem_map] at hx hx'
  obtain ⟨_, _, rfl⟩ := hx
  obtain ⟨_, _, h⟩ := hx'
  exact hne (Prod.mk.inj h).1.symm

theorem mem_ipieces {n : Nat} {p : Piece} : (n, p) ∈ Q.ipieces ↔ Q.pieces[n]? = some p := by
  simp only [ipieces, List.mem_map, List.mem_zipIdx_iff_getElem?, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨p', n'⟩, h, rfl, rfl⟩; exact h
  · intro h; exact ⟨(p, n), h, rfl, rfl⟩

theorem mem_prows {n x : Nat} {p : Piece} :
    (n, p, x) ∈ Q.prows ↔ Q.pieces[n]? = some p ∧ x < 2 ^ Q.height p := by
  simp only [prows, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨n', p'⟩, hm, x', hx, rfl, rfl, rfl⟩
    exact ⟨(Q.mem_ipieces).mp hm, hx⟩
  · rintro ⟨h, hx⟩
    exact ⟨(n, p), (Q.mem_ipieces).mpr h, x, hx, rfl, rfl, rfl⟩

theorem height_eq (p : Piece) : 2 ^ Q.height p = 2 ^ p.a * (Q.blk p.blk).size := by
  simp [height, Block.size, pow_add]

/-- **A piece row is an instance of the program, of the piece's shape.** -/
theorem prow_inst {n x : Nat} {p : Piece} (h : (n, p, x) ∈ Q.prows) :
    Q.pinst p x ∈ Q.insts ∧ (Q.pinst p x).row.shape = p.shape := by
  obtain ⟨hn, hx⟩ := (Q.mem_prows).mp h
  have hp : p ∈ Q.pieces := List.mem_of_getElem? hn
  obtain ⟨hb, hlen, hts⟩ := Q.mem_pieces hp
  have hsz : 0 < (Q.blk p.blk).size := Nat.two_pow_pos _
  rw [Q.height_eq] at hx
  have hi : x / (Q.blk p.blk).size < p.ts.length := by
    rw [hlen, Nat.div_lt_iff_lt_mul hsz]; exact hx
  have hmem : p.ts.getD (x / (Q.blk p.blk).size) 0 ∈ p.ts := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi
  obtain ⟨ht, hsh⟩ := hts _ hmem
  refine ⟨(Q.mem_insts _).mpr ⟨p.blk, hb, _, Nat.mod_lt _ hsz, _, ht, rfl⟩, ?_⟩
  simpa [pinst, inst] using hsh

/-- **Every instance is a piece row.** -/
theorem inst_prow {b jf t : Nat} (hb : b < Q.blocks.length) (hjf : jf < (Q.blk b).size)
    (ht : t < (Q.blk b).tpl.length) :
    ∃ n p x, (n, p, x) ∈ Q.prows ∧ Q.pinst p x = Q.inst b jf t := by
  have htm : t ∈ ((Q.blk b).pieces b).flatMap (·.ts) :=
    ((Q.blk b).pieces_ts b).mem_iff.mpr (List.mem_range.mpr ht)
  obtain ⟨p, hp, htp⟩ := List.mem_flatMap.mp htm
  obtain ⟨hpb, hlen, -⟩ := (Q.blk b).mem_pieces hp
  have hpQ : p ∈ Q.pieces := List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb, hp⟩
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hpQ
  obtain ⟨i, hi, hti⟩ := List.getElem_of_mem htp
  subst hpb
  have hsz : 0 < (Q.blk p.blk).size := Nat.two_pow_pos _
  refine ⟨n, p, jf + (Q.blk p.blk).size * i, (Q.mem_prows).mpr ⟨hn, ?_⟩, ?_⟩
  · rw [Q.height_eq]
    rw [hlen] at hi
    calc jf + (Q.blk p.blk).size * i < (Q.blk p.blk).size * (i + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ (Q.blk p.blk).size * 2 ^ p.a := Nat.mul_le_mul_left _ hi
      _ = 2 ^ p.a * (Q.blk p.blk).size := Nat.mul_comm _ _
  · have h1 : (jf + (Q.blk p.blk).size * i) % (Q.blk p.blk).size = jf := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjf]
    have h2 : (jf + (Q.blk p.blk).size * i) / (Q.blk p.blk).size = i := by
      rw [Nat.add_mul_div_left _ _ hsz, Nat.div_eq_of_lt hjf, Nat.zero_add]
    simp only [pinst, h1, h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some, hti]

theorem inst_inj {b jf t b' jf' t' : Nat} (h : Q.inst b jf t = Q.inst b' jf' t') :
    b = b' ∧ jf = jf' ∧ t = t' := by
  simp only [inst, Inst.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- **Two piece rows with one instance are one piece row.** -/
theorem prow_inj {n x n' x' : Nat} {p p' : Piece} (h : (n, p, x) ∈ Q.prows)
    (h' : (n', p', x') ∈ Q.prows) (he : Q.pinst p x = Q.pinst p' x') : n = n' ∧ p = p' ∧ x = x' := by
  obtain ⟨hn, hx⟩ := (Q.mem_prows).mp h
  obtain ⟨hn', hx'⟩ := (Q.mem_prows).mp h'
  obtain ⟨hb, hjf, ht⟩ := Q.inst_inj he
  have hp : p ∈ Q.pieces := List.mem_of_getElem? hn
  have hp' : p' ∈ Q.pieces := List.mem_of_getElem? hn'
  obtain ⟨-, hlen, -⟩ := Q.mem_pieces hp
  obtain ⟨-, hlen', -⟩ := Q.mem_pieces hp'
  have hsz : 0 < (Q.blk p.blk).size := Nat.two_pow_pos _
  rw [Q.height_eq] at hx hx'
  have hi : x / (Q.blk p.blk).size < p.ts.length := by
    rw [hlen, Nat.div_lt_iff_lt_mul hsz]; exact hx
  have hi' : x' / (Q.blk p'.blk).size < p'.ts.length := by
    rw [hlen', Nat.div_lt_iff_lt_mul (show 0 < (Q.blk p'.blk).size from Nat.two_pow_pos _)]
    exact hx'
  set i := x / (Q.blk p.blk).size
  set i' := x' / (Q.blk p'.blk).size
  have hti : p.ts.getD i 0 = p.ts[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hti' : p'.ts.getD i' 0 = p'.ts[i'] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  rw [hti, hti'] at ht
  -- the pair (block, template row) is in piece `n` and in piece `n'`
  have hnn : n = n' := by
    by_contra hne
    have hnd := Q.pieces_bt_nodup
    rw [List.nodup_flatMap] at hnd
    have hlt : n < Q.pieces.length := (List.getElem?_eq_some_iff.mp hn).1
    have hlt' : n' < Q.pieces.length := (List.getElem?_eq_some_iff.mp hn').1
    have hpn : Q.pieces[n] = p := (List.getElem?_eq_some_iff.mp hn).2
    have hpn' : Q.pieces[n'] = p' := (List.getElem?_eq_some_iff.mp hn').2
    have hy : (p.blk, p.ts[i]) ∈ p.ts.map (p.blk, ·) := List.mem_map_of_mem (List.getElem_mem hi)
    have hy' : (p.blk, p.ts[i]) ∈ p'.ts.map (p'.blk, ·) := by
      rw [hb, ht]; exact List.mem_map_of_mem (List.getElem_mem hi')
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have := List.pairwise_iff_getElem.mp hnd.2 n n' hlt hlt' hl
      rw [hpn, hpn'] at this
      exact this hy hy'
    · have := List.pairwise_iff_getElem.mp hnd.2 n' n hlt' hlt hl
      rw [hpn, hpn'] at this
      exact this hy' hy
  subst hnn
  have hpp : p = p' := Option.some.inj (hn.symm.trans hn')
  subst hpp
  have hnd : p.ts.Nodup := by
    have := (List.nodup_flatMap.mp Q.pieces_bt_nodup).1 p hp
    exact List.Nodup.of_map _ this
  have hii : i = i' := (hnd.getElem_inj_iff).mp ht
  refine ⟨rfl, rfl, ?_⟩
  have := Nat.div_add_mod x (Q.blk p.blk).size
  have := Nat.div_add_mod x' (Q.blk p.blk).size
  have hjf' : x % (Q.blk p.blk).size = x' % (Q.blk p.blk).size := hjf
  simp only [i, i'] at hii
  rw [← Nat.div_add_mod x (Q.blk p.blk).size, ← Nat.div_add_mod x' (Q.blk p.blk).size, hii, hjf']

end Program

end Lvm.Loop
