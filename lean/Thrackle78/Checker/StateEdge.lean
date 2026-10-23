import Thrackle78.Checker.MinorE
import Thrackle78.Checker.Bridge3

/-!
# The edge test of a state decides edges of the partial augmented graph

`stateEdge_mem`: every pair accepted by `stateEdge` is an edge of `edgeIds` (in one of the two orientations), so
`not_planar_aug_of_stateE`: a certificate accepted against `stateEdge` proves that `aug E P` is not planar for every
`P` extending the state.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

/-! ## Paths of the partial graph, by position -/

theorem mem_pairs_of_getElem? : ∀ {l : List ℕ} {i a b : ℕ}, l[i]? = some a → l[i + 1]? = some b →
    (a, b) ∈ pairs l
  | [], _, _, _, h, _ => by simp at h
  | [_], i, _, _, h1, h2 => by
    cases i with
    | zero => simp at h2
    | succ i => simp at h1
  | x :: y :: rest, i, a, b, h1, h2 => by
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h2
      subst h1; subst h2
      simp [pairs]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h1 h2
      simp only [pairs, List.mem_cons]
      exact Or.inr (mem_pairs_of_getElem? h1 h2)

theorem pathIds_getElem?_cross (n m : ℕ) (es : Array (ℕ × ℕ)) (e : ℕ) {r : List ℕ} (hnd : r.Nodup) {f : ℕ}
    (hf : f ∈ r) (cl : Bool) :
    (pathIds n m es e r cl)[2 * r.idxOf f + 1]? = some (xId n m e f) ∧
    (pathIds n m es e r cl)[2 * r.idxOf f]? = some (nbrB n m es e r f) ∧
    (∀ y, nbrA n m es e r cl f = some y → (pathIds n m es e r cl)[2 * r.idxOf f + 2]? = some y) := by
  have hr : r ≠ [] := List.ne_nil_of_mem hf
  have hj : r.idxOf f < r.length := List.idxOf_lt_length_iff.2 hf
  have hrf : r[r.idxOf f] = f := List.getElem_idxOf hj
  have hlen := midIds_length n m e r 0 hr
  have hpath : pathIds n m es e r cl =
      (es.getD e (0, 0)).1 :: (midIds n m e r 0 ++ if cl then [(es.getD e (0, 0)).2] else []) := by
    unfold pathIds
    cases cl <;> simp [hr]
  rw [hpath]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.getElem?_cons_succ, List.getElem?_append_left (by omega),
      midIds_getElem?_even n m e r 0 _ hj, hrf]
  · by_cases h0 : r.idxOf f = 0
    · rw [nbrB, ite_eq_left h0, h0]; rfl
    · obtain ⟨j', hj'⟩ : ∃ j', r.idxOf f = j' + 1 := ⟨r.idxOf f - 1, by omega⟩
      rw [nbrB, ite_eq_right h0, hj', show 2 * (j' + 1) = 2 * j' + 1 + 1 by ring, List.getElem?_cons_succ,
        List.getElem?_append_left (by omega), midIds_getElem?_odd n m e r 0 j' (by omega)]
      simp
  · intro y hy
    by_cases h1 : r.idxOf f + 1 = r.length
    · rw [nbrA, ite_eq_left h1] at hy
      by_cases hcl : cl = true
      · rw [ite_eq_left hcl] at hy
        have hyv : y = (es.getD e (0, 0)).2 := (Option.some.inj hy).symm
        rw [hyv, show 2 * r.idxOf f + 2 = (2 * r.idxOf f + 1) + 1 by ring, List.getElem?_cons_succ,
          List.getElem?_append_right (by omega), ite_eq_left hcl,
          show 2 * r.idxOf f + 1 - (midIds n m e r 0).length = 0 by omega]
        rfl
      · rw [ite_eq_right hcl] at hy; simp at hy
    · rw [nbrA, ite_eq_right h1] at hy
      rw [show 2 * r.idxOf f + 2 = (2 * r.idxOf f + 1) + 1 by ring, List.getElem?_cons_succ,
        List.getElem?_append_left (by omega), midIds_getElem?_odd n m e r 0 _ (by omega), ← Option.some.inj hy]
      simp

theorem pairs_nbrB (n m : ℕ) (es : Array (ℕ × ℕ)) (e : ℕ) {r : List ℕ} (hnd : r.Nodup) {f : ℕ} (hf : f ∈ r)
    (cl : Bool) : (nbrB n m es e r f, xId n m e f) ∈ pairs (pathIds n m es e r cl) := by
  obtain ⟨h1, h2, -⟩ := pathIds_getElem?_cross n m es e hnd hf cl
  exact mem_pairs_of_getElem? h2 h1

theorem pairs_nbrA (n m : ℕ) (es : Array (ℕ × ℕ)) (e : ℕ) {r : List ℕ} (hnd : r.Nodup) {f : ℕ} (hf : f ∈ r)
    (cl : Bool) {y : ℕ} (hy : nbrA n m es e r cl f = some y) : (xId n m e f, y) ∈ pairs (pathIds n m es e r cl) := by
  obtain ⟨h1, -, h3⟩ := pathIds_getElem?_cross n m es e hnd hf cl
  exact mem_pairs_of_getElem? h1 (h3 y hy)

/-! ## Membership in `edgeIds` -/

variable {n : ℕ} {es : Array (ℕ × ℕ)} {k : ℕ} {rows : Array (List ℕ)}

theorem drawnE_lt {e : ℕ} (h : drawnE es k rows e = true) : e < Nat.min (k + 1) es.size := by
  unfold drawnE at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
  have : e ≤ k := by rcases h.2 with h' | ⟨h', -⟩ <;> omega
  show e < min (k + 1) es.size
  omega

theorem mem_edgeIds_path {e a b : ℕ} (he : drawnE es k rows e = true)
    (h : (a, b) ∈ pairs (pathIds n es.size es e (rows.getD e []) (decide (e < k)))) :
    (a, b) ∈ edgeIds n es k rows := by
  unfold edgeIds
  rw [List.mem_flatMap]
  exact ⟨e, List.mem_range.2 (drawnE_lt he), List.mem_append_left _ h⟩

theorem mem_edgeIds_diamond {e f a b : ℕ} (he : drawnE es k rows e = true) (hf : f ∈ rows.getD e [])
    (hef : e < f)
    (h : (a, b) ∈ diamondIds (nbrB n es.size es e (rows.getD e []) f)
      (nbrA n es.size es e (rows.getD e []) (decide (e < k)) f)
      (nbrB n es.size es f (rows.getD f []) e) (nbrA n es.size es f (rows.getD f []) (decide (f < k)) e)) :
    (a, b) ∈ edgeIds n es k rows := by
  unfold edgeIds
  rw [List.mem_flatMap]
  refine ⟨e, List.mem_range.2 (drawnE_lt he), List.mem_append_right _ ?_⟩
  rw [List.mem_flatMap]
  exact ⟨f, hf, by rw [ite_eq_left hef]; exact h⟩

theorem mem_diamondIds_of {a1 b1 x y : ℕ} {a2 b2 : Option ℕ} (hx : x = a1 ∨ a2 = some x)
    (hy : y = b1 ∨ b2 = some y) : (x, y) ∈ diamondIds a1 a2 b1 b2 ∨ (y, x) ∈ diamondIds a1 a2 b1 b2 := by
  unfold diamondIds
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · left; simp
  · right; subst hy; cases a2 <;> simp
  · right; subst hx; cases b2 <;> simp
  · left; subst hx; subst hy; simp

/-- A diamond pair of a drawn crossing (either listing order) is an edge. -/
theorem mem_edgeIds_diamond' (hirr : ∀ e, e ∉ rows.getD e []) {e f x y : ℕ}
    (hp : presentE es k rows e f = true)
    (hx : x = nbrB n es.size es e (rows.getD e []) f ∨ nbrA n es.size es e (rows.getD e []) (decide (e < k)) f = some x)
    (hy : y = nbrB n es.size es f (rows.getD f []) e ∨
      nbrA n es.size es f (rows.getD f []) (decide (f < k)) e = some y) :
    (x, y) ∈ edgeIds n es k rows ∨ (y, x) ∈ edgeIds n es k rows := by
  unfold presentE at hp
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hp
  obtain ⟨⟨⟨hde, hdf⟩, hfe⟩, hef⟩ := hp
  have hne : e ≠ f := by
    rintro rfl
    exact hirr e hfe
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rcases mem_diamondIds_of hx hy with h | h
    · exact Or.inl (mem_edgeIds_diamond hde hfe hlt h)
    · exact Or.inr (mem_edgeIds_diamond hde hfe hlt h)
  · rcases mem_diamondIds_of hy hx with h | h
    · exact Or.inr (mem_edgeIds_diamond hdf hef hlt h)
    · exact Or.inl (mem_edgeIds_diamond hdf hef hlt h)

/-! ## The edge test -/

/-- Rows without duplicates and without self-crossings. -/
def RowsOK (rows : Array (List ℕ)) : Prop := ∀ e, (rows.getD e []).Nodup ∧ e ∉ rows.getD e []

theorem rowsOK_of_restr {m : ℕ} {E : Fin m → Fin n × Fin n} (P : CrossingSystem E) {k t : ℕ}
    {rows : Array (List ℕ)} (hr : Restr P k t rows) : RowsOK rows := by
  intro e
  by_cases he : e < m
  · rw [hr.2.2.2 ⟨e, he⟩]
    refine ⟨(rowAt_nodup P k t _).map Fin.val_injective, fun hm => ?_⟩
    obtain ⟨g, hg, hge⟩ := List.mem_map.1 hm
    have hgπ := (rowAt_sublist P k t _).subset hg
    exact ne_of_mem_π P hgπ (Fin.ext hge)
  · have : rows.getD e [] = [] := by
      simp [Array.getD, show ¬ e < rows.size by rw [hr.1]; exact he]
    rw [this]
    exact ⟨List.nodup_nil, by simp⟩

theorem idxOf_getD_of_nodup {r : List ℕ} (hnd : r.Nodup) {i : ℕ} (hi : i < r.length) :
    r.idxOf (r.getD i 0) = i := by
  rw [List.getD_eq_getElem _ _ hi]; exact hnd.idxOf_getElem i hi

theorem idxOf_getLast_of_nodup {r : List ℕ} (hnd : r.Nodup) {f : ℕ} (hf : r.getLast? = some f) :
    r.idxOf f + 1 = r.length := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hf
  have hfy : f ∉ ys := fun h' => (List.nodup_append.1 hnd).2.2 f h' f (by simp) rfl
  have : (ys ++ [f]).idxOf f = ys.length := by
    clear hf hnd
    induction ys with
    | nil => simp
    | cons a l ih =>
      have haf : a ≠ f := fun e => hfy (e ▸ List.mem_cons_self)
      rw [List.cons_append, List.idxOf_cons_ne _ haf, ih (fun h' => hfy (List.mem_cons_of_mem _ h'))]
      simp
  rw [this]; simp

theorem decode_xId {n m x : ℕ} (hx : n ≤ x) (hlt : (x - n) / m < (x - n) % m) :
    x = xId n m ((x - n) / m) ((x - n) % m) := by
  rw [xId_eq hlt]
  have := Nat.div_add_mod (x - n) m
  rw [Nat.mul_comm] at this
  omega

theorem decode_sId {n m x : ℕ} (hx : n + m * m ≤ x) :
    x = sId n m ((x - n - m * m) / m) ((x - n - m * m) % m) := by
  unfold sId
  have := Nat.div_add_mod (x - n - m * m) m
  rw [Nat.mul_comm] at this
  omega

theorem crossAdj_mem (hok : RowsOK rows) {e f y : ℕ} (hef : e < f) (h : crossAdj n es k rows e f y = true) :
    (xId n es.size e f, y) ∈ edgeIds n es k rows ∨ (y, xId n es.size e f) ∈ edgeIds n es k rows := by
  unfold crossAdj at h
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hp, hn⟩ := h
  have hp' := hp
  unfold presentE at hp'
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hp'
  obtain ⟨⟨⟨hde, hdf⟩, hfe⟩, hef'⟩ := hp'
  rcases hn with hn | hn <;> unfold pathNbr at hn <;> rw [Bool.or_eq_true, beq_iff_eq] at hn
  · rcases hn with rfl | hn
    · exact Or.inr (mem_edgeIds_path hde (pairs_nbrB n es.size es e (hok e).1 hfe _))
    · exact Or.inl (mem_edgeIds_path hde (pairs_nbrA n es.size es e (hok e).1 hfe _ (by simpa using hn)))
  · rw [xId_comm]
    rcases hn with rfl | hn
    · exact Or.inr (mem_edgeIds_path hdf (pairs_nbrB n es.size es f (hok f).1 hef' _))
    · exact Or.inl (mem_edgeIds_path hdf (pairs_nbrA n es.size es f (hok f).1 hef' _ (by simpa using hn)))

theorem pathNbr_cases {f e y : ℕ} (h : pathNbr n es k rows f e y = true) :
    y = nbrB n es.size es f (rows.getD f []) e ∨
      nbrA n es.size es f (rows.getD f []) (decide (f < k)) e = some y := by
  unfold pathNbr at h
  rw [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

theorem subAdj_mem (hok : RowsOK rows) {e i y : ℕ} (h : subAdj n es k rows e i y = true) :
    (sId n es.size e i, y) ∈ edgeIds n es k rows ∨ (y, sId n es.size e i) ∈ edgeIds n es k rows := by
  unfold subAdj at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hi⟩, h | h⟩ := h
  · obtain ⟨hp, hn⟩ := h
    refine mem_edgeIds_diamond' (fun e => (hok e).2) hp (Or.inr ?_) (pathNbr_cases hn)
    unfold nbrA
    rw [idxOf_getD_of_nodup (hok e).1 (by omega), ite_eq_right (by omega)]
  · obtain ⟨hp, hn⟩ := h
    refine mem_edgeIds_diamond' (fun e => (hok e).2) hp (Or.inl ?_) (pathNbr_cases hn)
    unfold nbrB
    rw [idxOf_getD_of_nodup (hok e).1 hi, ite_eq_right (by omega)]
    rfl

theorem origAdj_mem (hok : RowsOK rows) {v w : ℕ} (h : origAdj n es k rows v w = true) :
    (v, w) ∈ edgeIds n es k rows ∨ (w, v) ∈ edgeIds n es k rows := by
  unfold origAdj at h
  rw [List.any_eq_true] at h
  obtain ⟨e, -, h⟩ := h
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨hde, h | h⟩ := h
  · rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨htail, h⟩ := h
    cases hre : rows.getD e [] with
    | nil =>
      rw [hre] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨hek, hhead⟩ := h
      left
      apply mem_edgeIds_path hde
      rw [hre, decide_eq_true hek, ← htail, ← hhead]
      simp [pathIds, midIds, pairs]
    | cons f rest =>
      rw [hre] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hp, hn⟩ := h
      refine mem_edgeIds_diamond' (fun e => (hok e).2) hp (Or.inl ?_) (pathNbr_cases hn)
      unfold nbrB
      rw [hre, List.idxOf_cons_self, ite_eq_left rfl, htail]
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hhead, hek⟩, h⟩ := h
    cases hl : (rows.getD e []).getLast? with
    | none =>
      rw [hl] at h
      simp only [beq_iff_eq] at h
      have hre : rows.getD e [] = [] := List.getLast?_eq_none_iff.1 hl
      right
      apply mem_edgeIds_path hde
      rw [hre, decide_eq_true hek, ← hhead, ← h]
      simp [pathIds, midIds, pairs]
    | some f =>
      rw [hl] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hp, hn⟩ := h
      refine mem_edgeIds_diamond' (fun e => (hok e).2) hp (Or.inr ?_) (pathNbr_cases hn)
      unfold nbrA
      rw [idxOf_getLast_of_nodup (hok e).1 hl, ite_eq_left rfl, decide_eq_true hek, ite_eq_left rfl, hhead]

/-- **Every pair accepted by the edge test is an edge of the partial augmented graph.** -/
theorem stateEdge_mem (hok : RowsOK rows) {x y : ℕ} (h : stateEdge n es k rows x y = true) :
    (x, y) ∈ edgeIds n es k rows ∨ (y, x) ∈ edgeIds n es k rows := by
  unfold stateEdge at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    rw [decode_xId h1.1.1 h1.2]
    exact crossAdj_mem hok h1.2 h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    rw [decode_xId h2.1.1 h2.2]
    exact (crossAdj_mem hok h2.2 h).symm
  · simp only [decide_eq_true_eq] at h3
    rw [decode_sId h3]
    exact subAdj_mem hok h
  · simp only [decide_eq_true_eq] at h4
    rw [decode_sId h4]
    exact (subAdj_mem hok h).symm
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact origAdj_mem hok h.2

/-! ## The bridge with the edge test -/

variable {m : ℕ} {E : Fin m → Fin n × Fin n}

/-- **Bridge (edge test)**: if the rows are the restriction of `P` to a stage and the graph of the edge test of the
state is not planar, then `aug E P` is not planar. -/
theorem not_planar_aug_of_stateE (P : CrossingSystem E) (t : ℕ) (hes : Matches es E) (hr : Restr P k t rows)
    (hnp : ¬ Planar (eSG (stateEdge n es k rows))) : ¬ Planar (aug E P) := by
  have hok := rowsOK_of_restr P hr
  have hadj : ∀ x y, (eSG (stateEdge n es k rows)).Adj x y → Realized P k t x y ∧ x ≠ y := by
    intro x y hxy
    rw [eSG_adj] at hxy
    unfold hasE at hxy
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at hxy
    obtain ⟨hne, hxy | hxy⟩ := hxy
    · rcases stateEdge_mem hok hxy with h1 | h1
      · exact ⟨realized_edgeIds P k t hes hr h1, hne⟩
      · exact ⟨realized_symm P k t (realized_edgeIds P k t hes hr h1), hne⟩
    · rcases stateEdge_mem hok hxy with h1 | h1
      · exact ⟨realized_symm P k t (realized_edgeIds P k t hes hr h1), hne⟩
      · exact ⟨realized_edgeIds P k t hes hr h1, hne⟩
  refine not_planar_of_map hnp (fiber P k t) ?_ ?_ ?_ ?_
  · rintro x ⟨y, hxy⟩
    obtain ⟨⟨a, -, ha, -⟩, -⟩ := hadj x y hxy
    exact (good_of_asg P k t hes ha).1
  · rintro x ⟨y, hxy⟩
    obtain ⟨⟨a, -, ha, -⟩, -⟩ := hadj x y hxy
    exact (good_of_asg P k t hes ha).2
  · intro x x' _ _ hxx'
    rw [Set.disjoint_left]
    intro a ha ha'
    exact hxx' (Option.some.inj ((show asg P k t a = some x from ha).symm.trans ha'))
  · intro x y hxy
    obtain ⟨hreal, hne⟩ := hadj x y hxy
    exact realized_adj P k t hreal hne

end Thrackle78.Checker
