import Thrackle78.Checker.Bridge2

/-!
# The partial augmented graph of a stage is a minor of `aug E P`: edges and the transfer

* `realized_pairs`, `realized_diamond`: the path edges and the diamond edges of the partial augmented graph are
  realized by aug vertices (equal or adjacent) in the two branch sets;
* `good_of_asg`: every assigned value has a nonempty connected branch set;
* `not_planar_aug_of_state`: if the core rows are the restriction of `P` to a stage and the partial augmented graph
  (core `stateGraph`) is not planar, then `aug E P` is not planar.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n} (P : CrossingSystem E) (k t : ℕ) {es : Array (ℕ × ℕ)}

/-- `x` and `y` are realized by aug vertices of their branch sets that are equal or adjacent. -/
def Realized (x y : ℕ) : Prop :=
  ∃ a b : AV n m, asg P k t a = some x ∧ asg P k t b = some y ∧ (a = b ∨ (aug E P).Adj a b)

theorem realized_symm {x y : ℕ} (h : Realized P k t x y) : Realized P k t y x := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  exact ⟨b, a, hb, ha, hab.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩

theorem realized_adj {x y : ℕ} (h : Realized P k t x y) (hxy : x ≠ y) :
    ∃ a ∈ fiber P k t x, ∃ b ∈ fiber P k t y, (aug E P).Adj a b := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  rcases hab with rfl | hab
  · rw [ha] at hb; exact absurd (Option.some.inj hb) hxy
  · exact ⟨a, ha, b, hb, hab⟩

/-- Path edges are realized. -/
theorem realized_pairs (hes : Matches es E) {e : Fin m} (hd : Drawn P k t e) {x y : ℕ}
    (h : (x, y) ∈ pairs (Q P k t es e)) : Realized P k t x y := by
  obtain ⟨i, hi, hx, hy⟩ := mem_pairs h
  obtain ⟨D, hD, hmuD⟩ := exists_cover_end P k t hes e hd
  have hDlt := covered_lt P k t hD
  obtain ⟨p, -, hpD, hp1, hp2⟩ := exists_step (mu P k t e) i 0 D (Nat.zero_le _) (by rw [mu_zero]; omega)
    (by omega) (fun p _ hpD => (mu_step P k t e p (by omega)).1)
  have hcov1 : Covered P k t e (p + 1) := covered_mono P k t hD (by omega)
  have hcov0 : Covered P k t e p := covered_mono P k t hD (by omega)
  refine ⟨node P e p, node P e (p + 1), ?_, ?_, node_adj P e p (by omega)⟩
  · rw [asg_node P k t hes e p hcov0, hp1]; exact congrArg some hx
  · rw [asg_node P k t hes e (p + 1) hcov1, hp2]; exact congrArg some hy

theorem drawn_of_mem {e g : Fin m} (hg : g ∈ rowAt P k t e) : Drawn P k t e := by
  rcases Nat.lt_or_eq_of_le (le_of_mem_rowAt P hg).1 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, List.ne_nil_of_mem hg⟩

/-- The node before a drawn crossing. -/
theorem asg_nbrs_fst (hes : Matches es E) {e g : Fin m} (hg : g ∈ rowAt P k t e) :
    asg P k t (nbrs E P e g).1 = some (nbrB n m es e.val ((rowAt P k t e).map Fin.val) g.val) := by
  have hgπ : g ∈ P.π e := (rowAt_sublist P k t e).subset hg
  obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ hj : j < (P.π e).length, (P.π e)[j] = g :=
    ⟨_, List.idxOf_lt_length_iff.2 hgπ, List.getElem_idxOf _⟩
  have hi : (rowAt P k t e).idxOf (P.π e)[j] = cnt P k t e j := by
    rw [idxOf_rowAt P k t e hg, (P.nodup e).idxOf_getElem j hj]
  have hiL : cnt P k t e j < (rowAt P k t e).length := by
    rw [← hi]; exact List.idxOf_lt_length_iff.2 hg
  have hd := drawn_of_mem P k t hg
  have hlen := pathNodes_length P e
  rw [ite_eq_right (List.ne_nil_of_length_pos (by omega))] at hlen
  have hcov : Covered P k t e (2 * j) := by
    unfold Covered
    split_ifs with he
    · omega
    · exact ⟨by have := (le_of_mem_rowAt P hg).1; omega, by rw [show 2 * j / 2 = j by omega]; exact hiL⟩
  rw [nbrs_fst_node P e j hj, asg_node P k t hes e _ hcov]
  congr 1
  have hmu : mu P k t e (2 * j) = 2 * cnt P k t e j := by
    unfold mu
    rw [ite_eq_right (fun h => by simp [h.2.1] at hg), show 2 * j / 2 = j by omega,
      show (2 * j + 1) / 2 = j by omega]
    ring
  rw [hmu]
  unfold nbrB
  rw [idxOf_map_val, hi, hes.get e]
  split_ifs with h0
  · rw [h0, Nat.mul_zero, qnode_zero P k t hes hd]
  · obtain ⟨c', hc'⟩ : ∃ c', cnt P k t e j = c' + 1 := ⟨_, (Nat.succ_pred_eq_of_ne_zero h0).symm⟩
    rw [hc', show 2 * (c' + 1) = 2 * c' + 2 by ring, qnode_even P k t hes hd c' (by omega)]
    simp

/-- The node after a drawn crossing, when drawn. -/
theorem asg_nbrs_snd (hes : Matches es E) {e g : Fin m} (hg : g ∈ rowAt P k t e) {y : ℕ}
    (hy : nbrA n m es e.val ((rowAt P k t e).map Fin.val) (decide (e.val < k)) g.val = some y) :
    asg P k t (nbrs E P e g).2 = some y := by
  have hgπ : g ∈ P.π e := (rowAt_sublist P k t e).subset hg
  obtain ⟨j, hj, rfl⟩ : ∃ j, ∃ hj : j < (P.π e).length, (P.π e)[j] = g :=
    ⟨_, List.idxOf_lt_length_iff.2 hgπ, List.getElem_idxOf _⟩
  have hi : (rowAt P k t e).idxOf (P.π e)[j] = cnt P k t e j := by
    rw [idxOf_rowAt P k t e hg, (P.nodup e).idxOf_getElem j hj]
  have hiL : cnt P k t e j < (rowAt P k t e).length := by
    rw [← hi]; exact List.idxOf_lt_length_iff.2 hg
  have hd := drawn_of_mem P k t hg
  have hR : rowAt P k t e ≠ [] := List.ne_nil_of_mem hg
  have hlen := pathNodes_length P e
  rw [ite_eq_right (List.ne_nil_of_length_pos (by omega))] at hlen
  have hcj1 : cnt P k t e (j + 1) = cnt P k t e j + 1 := by rw [cnt_succ P k t e j hj, ite_eq_left hg]
  have hmu : mu P k t e (2 * j + 2) = 2 * (cnt P k t e j + 1) := by
    unfold mu
    rw [ite_eq_right (fun h => hR h.2.1), show (2 * j + 2) / 2 = j + 1 by omega,
      show (2 * j + 2 + 1) / 2 = j + 1 by omega, hcj1]
    ring
  rw [nbrs_snd_node P e j hj]
  unfold nbrA at hy
  rw [idxOf_map_val, hi, List.length_map, hes.get e] at hy
  by_cases h1 : cnt P k t e j + 1 = (rowAt P k t e).length
  · rw [ite_eq_left h1] at hy
    by_cases he : e.val < k
    · rw [ite_eq_left (show decide (e.val < k) = true by simpa using he)] at hy
      have hcov : Covered P k t e (2 * j + 2) := by unfold Covered; rw [ite_eq_left he]; omega
      rw [asg_node P k t hes e _ hcov, hmu, ← Option.some.inj hy, h1]
      congr 1
      apply qnode_last P k t hes he
      rw [Q_length_closed P k t hes he, ite_eq_right hR]
    · rw [ite_eq_right (show ¬ decide (e.val < k) = true by simpa using he)] at hy
      simp at hy
  · rw [ite_eq_right h1] at hy
    have hcov : Covered P k t e (2 * j + 2) := by
      unfold Covered
      split_ifs with he
      · omega
      · exact ⟨by have := (le_of_mem_rowAt P hg).1; omega,
          by rw [show (2 * j + 2) / 2 = j + 1 by omega, hcj1]; omega⟩
    rw [asg_node P k t hes e _ hcov, hmu, ← Option.some.inj hy,
      show 2 * (cnt P k t e j + 1) = 2 * cnt P k t e j + 2 by ring, qnode_even P k t hes hd _ (by omega)]

/-- Diamond edges are realized. -/
theorem realized_diamond (hes : Matches es E) {e g : Fin m} (hg : g ∈ rowAt P k t e) (heg : e < g) {x y : ℕ}
    (h : (x, y) ∈ diamondIds (nbrB n m es e.val ((rowAt P k t e).map Fin.val) g.val)
      (nbrA n m es e.val ((rowAt P k t e).map Fin.val) (decide (e.val < k)) g.val)
      (nbrB n m es g.val ((rowAt P k t g).map Fin.val) e.val)
      (nbrA n m es g.val ((rowAt P k t g).map Fin.val) (decide (g.val < k)) e.val)) :
    Realized P k t x y := by
  have he : e ∈ rowAt P k t g := (mem_rowAt_symm P).1 hg
  have hni : NonInc E e g := (P.mem e g).1 ((rowAt_sublist P k t e).subset hg)
  have hreal : ∀ a b : AV n m, s(a, b) ∈ diamondEdges E P e g → a = b ∨ (aug E P).Adj a b := by
    intro a b hab
    by_cases h : a = b
    · exact Or.inl h
    · exact Or.inr (aug_adj_of_mem P (diamond_mem P heg hni hab) h)
  rcases mem_diamondIds h with ⟨rfl, rfl⟩ | ⟨rfl, hA2⟩ | ⟨hA2, hB2⟩ | ⟨hB2, rfl⟩
  · exact ⟨_, _, asg_nbrs_fst P k t hes hg, asg_nbrs_fst P k t hes he, hreal _ _ (by simp [diamondEdges])⟩
  · exact ⟨_, _, asg_nbrs_fst P k t hes he, asg_nbrs_snd P k t hes hg hA2, hreal _ _ (by simp [diamondEdges])⟩
  · exact ⟨_, _, asg_nbrs_snd P k t hes hg hA2, asg_nbrs_snd P k t hes he hB2,
      hreal _ _ (by simp [diamondEdges])⟩
  · exact ⟨_, _, asg_nbrs_snd P k t hes he hB2, asg_nbrs_fst P k t hes hg, hreal _ _ (by simp [diamondEdges])⟩

/-- Every assigned value has a nonempty connected branch set. -/
theorem good_of_asg (hes : Matches es E) {a : AV n m} {x : ℕ} (h : asg P k t a = some x) :
    (fiber P k t x).Nonempty ∧ ((aug E P).induce (fiber P k t x)).Connected := by
  refine ⟨⟨a, h⟩, ?_⟩
  rcases asg_cases P k t hes h with ⟨w, -, rfl⟩ | ⟨e, g, hg, -, -, rfl⟩ | ⟨e, p, c, hcov, -, hmu, hs⟩
  · exact fiber_connected_orig P k t hes w
  · exact fiber_connected_cross P k t hes hg
  · rcases (segAsg_some P k t hs).2 with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨hc0, rfl⟩
    · exact fiber_connected_orig P k t hes (E e).1
    · exact fiber_connected_orig P k t hes (E e).2
    · have hcL : c < (rowAt P k t e).length := by
        rcases (segAsg_some P k t hs).1 with he | ⟨-, h'⟩
        · have h1 := mu_le_length P k t e p
          have hcle : c ≤ (rowAt P k t e).length := by omega
          rcases Nat.lt_or_eq_of_le hcle with h' | h'
          · exact h'
          · exfalso
            have hv : segAsg P k t e c = some (E e).2.val := by
              unfold segAsg
              rw [ite_eq_left he, ite_eq_right hc0, ite_eq_left h']
            rw [hs] at hv
            have := Option.some.inj hv
            have := le_sId n m e.val (c - 1)
            have := (E e).2.isLt
            omega
        · exact h'
      exact fiber_connected_sub P k t hes (covered_drawn P k t hcov) (c - 1) (by omega)

/-- Every edge of the partial augmented graph of a stage is realized. -/
theorem realized_edgeIds (hes : Matches es E) {rows : Array (List ℕ)} (hr : Restr P k t rows) {x y : ℕ}
    (h : (x, y) ∈ edgeIds n es k rows) : Realized P k t x y := by
  obtain ⟨-, -, -, hrows⟩ := hr
  unfold edgeIds at h
  rw [List.mem_flatMap] at h
  obtain ⟨e, he, h⟩ := h
  rw [List.mem_range, hes.size] at he
  have he' : e < k + 1 ∧ e < m := by
    unfold Nat.min at he
    exact ⟨lt_of_lt_of_le he (min_le_left _ _), lt_of_lt_of_le he (min_le_right _ _)⟩
  have hem : e < m := he'.2
  have hrow : rows.getD e [] = (rowAt P k t ⟨e, hem⟩).map Fin.val := hrows ⟨e, hem⟩
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [hrow, hes.size] at h
    have hQ : (x, y) ∈ pairs (Q P k t es ⟨e, hem⟩) := h
    have hd : Drawn P k t ⟨e, hem⟩ := by
      rcases Nat.lt_or_eq_of_le (show e ≤ k by omega) with h' | h'
      · exact Or.inl h'
      · refine Or.inr ⟨h', fun hnil => ?_⟩
        have hnil' : Q P k t es ⟨e, hem⟩ = [] := by
          simp [Q, pathIds, hnil, show ¬ e < k by omega]
        rw [hnil'] at hQ
        simp [pairs] at hQ
    exact realized_pairs P k t hes hd hQ
  · rw [List.mem_flatMap] at h
    obtain ⟨f, hf, h⟩ := h
    rw [hrow] at hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    split_ifs at h with hlt
    · have hgrow : rows.getD g.val [] = (rowAt P k t g).map Fin.val := hrows g
      rw [hrow, hgrow, hes.size] at h
      exact realized_diamond P k t hes hg (show (⟨e, hem⟩ : Fin m) < g from hlt) h
    · simp at h

/-- **Bridge**: if the core rows are the restriction of `P` to a stage and the partial augmented graph is not planar,
then `aug E P` is not planar. -/
theorem not_planar_aug_of_state (hes : Matches es E) {rows : Array (List ℕ)} (hr : Restr P k t rows)
    (hnp : ¬ Planar (stateGraph n es k rows).toSG) : ¬ Planar (aug E P) := by
  have hadj : ∀ x y, (stateGraph n es k rows).toSG.Adj x y → Realized P k t x y ∧ x ≠ y := by
    intro x y hxy
    obtain ⟨hne, hmem⟩ := fromEdges_hasEdge hxy
    rcases hmem with h1 | h1
    · exact ⟨realized_edgeIds P k t hes hr h1, hne⟩
    · exact ⟨realized_symm P k t (realized_edgeIds P k t hes hr h1), hne⟩
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
