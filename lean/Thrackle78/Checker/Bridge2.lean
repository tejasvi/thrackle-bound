import Thrackle78.Checker.Bridge1

/-!
# The partial augmented graph of a stage is a minor of `aug E P`

With the branch sets `φ x = {a | asg a = some x}`:
* every edge of the partial augmented graph is realized by an edge of `aug E P` between the two branch sets (path edges
  by `real_pairs`, diamond edges by `real_diamond`);
* the branch sets of the vertices of the partial graph are nonempty and connected (`fiber_nonempty`,
  `fiber_connected`): an original vertex with the end segments of its edges, a drawn crossing alone, a subdivision
  vertex with an interval of its path.
Hence a non-planar partial graph gives a non-planar `aug E P` (`not_planar_aug_of_state`).
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

/-! ## The graph of an edge list -/

theorem getD_modify {α : Type} (a : Array α) (i j : ℕ) (f : α → α) (d : α) :
    (a.modify i f).getD j d = if i = j ∧ j < a.size then f (a.getD j d) else a.getD j d := by
  by_cases hj : j < a.size
  · by_cases hij : i = j
    · subst hij; simp [Array.getD, hj, Array.getElem_modify]
    · simp [Array.getD, hj, hij, Array.getElem_modify]
  · simp [Array.getD, hj]

theorem foldl_modify_contains (l : List (ℕ × ℕ)) : ∀ (acc : Array (Array ℕ)) (x y : ℕ),
    ((l.foldl (fun adj p => adj.modify p.1 (·.push p.2)) acc).getD x #[]).contains y = true →
      (acc.getD x #[]).contains y = true ∨ (x, y) ∈ l := by
  induction l with
  | nil => intro acc x y h; exact Or.inl h
  | cons p l ih =>
    intro acc x y h
    rw [List.foldl_cons] at h
    rcases ih _ x y h with h1 | h1
    · rw [getD_modify] at h1
      split_ifs at h1 with hc
      · rw [Array.contains_push, Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · refine Or.inr ?_
          have : y = p.2 := by simpa using h1
          rw [← hc.1, this]
          exact List.mem_cons_self
      · exact Or.inl h1
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem fromEdges_hasEdge {nv : ℕ} {l : List (ℕ × ℕ)} {x y : ℕ} (h : (fromEdges nv l).hasEdge x y = true) :
    x ≠ y ∧ ((x, y) ∈ l ∨ (y, x) ∈ l) := by
  unfold AGraph.hasEdge fromEdges at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  have hrep : ∀ z, ((Array.replicate nv (#[] : Array ℕ)).getD z #[]).contains y = false ∧
      ((Array.replicate nv (#[] : Array ℕ)).getD z #[]).contains x = false := by
    intro z; simp [Array.getD]
  refine ⟨h.1, ?_⟩
  rcases h.2 with h2 | h2
  · rcases foldl_modify_contains l _ x y h2 with h3 | h3
    · rw [(hrep x).1] at h3; exact absurd h3 (by simp)
    · exact Or.inl h3
  · rcases foldl_modify_contains l _ y x h2 with h3 | h3
    · rw [(hrep y).2] at h3; exact absurd h3 (by simp)
    · exact Or.inr h3

theorem mem_pairs {x y : ℕ} : ∀ {l : List ℕ}, (x, y) ∈ pairs l →
    ∃ i, i + 1 < l.length ∧ l.getD i 0 = x ∧ l.getD (i + 1) 0 = y
  | [], h => by simp [pairs] at h
  | [_], h => by simp [pairs] at h
  | a :: b :: rest, h => by
    simp only [pairs, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨0, by simp, rfl, rfl⟩
    · obtain ⟨i, hi, h1, h2⟩ := mem_pairs h
      exact ⟨i + 1, by simp at hi ⊢; omega, by simpa using h1, by simpa using h2⟩

theorem mem_diamondIds {x y a1 b1 : ℕ} {a2 b2 : Option ℕ} (h : (x, y) ∈ diamondIds a1 a2 b1 b2) :
    (x = a1 ∧ y = b1) ∨ (x = b1 ∧ a2 = some y) ∨ (a2 = some x ∧ b2 = some y) ∨ (b2 = some x ∧ y = a1) := by
  unfold diamondIds at h
  cases a2 <;> cases b2 <;> simp at h <;> aesop

theorem idxOf_map_val {m : ℕ} (l : List (Fin m)) (g : Fin m) : (l.map Fin.val).idxOf g.val = l.idxOf g := by
  induction l with
  | nil => rfl
  | cons h l ih =>
    by_cases hhg : h = g
    · subst hhg; simp [List.idxOf_cons]
    · have : h.val ≠ g.val := fun e => hhg (Fin.ext e)
      simp [List.idxOf_cons, hhg, this, ih]

variable {n m : ℕ} {E : Fin m → Fin n × Fin n} (P : CrossingSystem E) (k t : ℕ) {es : Array (ℕ × ℕ)}

/-! ## Monotone positions and walks along a path -/

theorem mu_mono (e : Fin m) {p p' : ℕ} (h : p ≤ p') (hp' : p' < (pathNodes E P e).length) :
    mu P k t e p ≤ mu P k t e p' := by
  induction p' with
  | zero => obtain rfl : p = 0 := by omega
            exact le_refl _
  | succ q ih =>
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · exact le_trans (ih (by omega) (by omega)) (mu_step P k t e q hp').2

theorem mu_le_length (e : Fin m) (p : ℕ) : mu P k t e p ≤ 2 * (rowAt P k t e).length + 1 := by
  have h1 := cnt_le_length P k t e (p / 2)
  have h2 := cnt_le_length P k t e ((p + 1) / 2)
  unfold mu
  split_ifs <;> omega

/-- The branch set of `x`. -/
def fiber (x : ℕ) : Set (AV n m) := {a | asg P k t a = some x}

theorem reach_of_adj_or_eq {V : Type} {G : SimpleGraph V} {s : Set V} {a b : V} (ha : a ∈ s) (hb : b ∈ s)
    (h : a = b ∨ G.Adj a b) : (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  rcases h with rfl | h
  · rfl
  · exact SimpleGraph.Adj.reachable (by simpa using h)

/-- **Walk along a path**: positions with the same `mu` are joined inside their branch set. -/
theorem fiber_walk (hes : Matches es E) (e : Fin m) (x : ℕ) :
    ∀ d p (hp : Covered P k t e (p + d)), mu P k t e p = mu P k t e (p + d) →
      qnode P k t es e (mu P k t e (p + d)) = x →
      ∃ (h1 : node P e p ∈ fiber P k t x) (h2 : node P e (p + d) ∈ fiber P k t x),
        ((aug E P).induce (fiber P k t x)).Reachable ⟨_, h1⟩ ⟨_, h2⟩ := by
  intro d
  induction d with
  | zero =>
    intro p hp _ hx
    have h2 : node P e (p + 0) ∈ fiber P k t x := by
      show asg P k t _ = some x; rw [asg_node P k t hes e _ hp, hx]
    exact ⟨h2, h2, by rfl⟩
  | succ d ih =>
    intro p hp hmu hx
    have hlt := covered_lt P k t hp
    have hm1 : mu P k t e (p + 1) = mu P k t e (p + 1 + d) := by
      have a1 := mu_mono P k t e (show p ≤ p + 1 by omega) (by omega)
      have a2 := mu_mono P k t e (show p + 1 ≤ p + 1 + d by omega) (by rw [show p + 1 + d = p + (d + 1) by omega]; exact hlt)
      rw [show p + 1 + d = p + (d + 1) by omega] at a2 ⊢
      omega
    obtain ⟨h1, h2, hr⟩ := ih (p + 1) (by rw [show p + 1 + d = p + (d + 1) by omega]; exact hp) hm1
      (by rw [show p + 1 + d = p + (d + 1) by omega]; exact hx)
    have h0 : node P e p ∈ fiber P k t x := by
      show asg P k t _ = some x
      rw [asg_node P k t hes e p (covered_mono P k t hp (by omega)), hmu, hx]
    refine ⟨h0, by rw [show p + (d + 1) = p + 1 + d by omega]; exact h2, ?_⟩
    have hstep := reach_of_adj_or_eq h0 h1 (node_adj P e p (by omega))
    have hr' := hstep.trans hr
    convert hr' using 2 <;> rw [show p + (d + 1) = p + 1 + d by omega]

/-! ## The cases of the assignment -/

theorem segAsg_some {e : Fin m} {c x : ℕ} (h : segAsg P k t e c = some x) :
    (e.val < k ∨ (e.val = k ∧ c < (rowAt P k t e).length)) ∧
      ((c = 0 ∧ x = (E e).1.val) ∨ (e.val < k ∧ c = (rowAt P k t e).length ∧ c ≠ 0 ∧ x = (E e).2.val) ∨
        (c ≠ 0 ∧ x = sId n m e.val (c - 1))) := by
  unfold segAsg at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> simp only [Option.some.injEq] at h
  · exact ⟨Or.inl h1, Or.inl ⟨h2, h.symm⟩⟩
  · exact ⟨Or.inl h1, Or.inr (Or.inl ⟨h1, h3, h2, h.symm⟩)⟩
  · exact ⟨Or.inl h1, Or.inr (Or.inr ⟨h2, h.symm⟩)⟩
  · exact ⟨Or.inr h4, Or.inl ⟨h5, h.symm⟩⟩
  · exact ⟨Or.inr h4, Or.inr (Or.inr ⟨h5, h.symm⟩)⟩

/-- Every aug vertex with an assignment is an original vertex, a drawn crossing, or a covered node of a path at an
even `mu` (a segment). -/
theorem asg_cases (hes : Matches es E) {a : AV n m} {x : ℕ} (h : asg P k t a = some x) :
    (∃ w : Fin n, a = ov w ∧ x = w.val) ∨
    (∃ e g : Fin m, g ∈ rowAt P k t e ∧ e < g ∧ a = xv e g ∧ x = xId n m e.val g.val) ∨
    (∃ e : Fin m, ∃ p c, Covered P k t e p ∧ a = node P e p ∧ mu P k t e p = 2 * c ∧ segAsg P k t e c = some x) := by
  rcases a with w | ⟨p', q'⟩ | ⟨e', j'⟩
  · exact Or.inl ⟨w, rfl, (Option.some.inj h).symm⟩
  · simp only [asg] at h
    split_ifs at h with hc hq
    · refine Or.inr (Or.inl ⟨p', q', hq, hc.1, ?_, (Option.some.inj h).symm⟩)
      unfold xv; rw [min_eq_left hc.1.le, max_eq_right hc.1.le]
    · refine Or.inr (Or.inr ?_)
      have hqπ : q' ∈ P.π p' := (P.mem p' q').2 hc.2
      set j := (P.π p').idxOf q' with hj_def
      have hj : j < (P.π p').length := List.idxOf_lt_length_iff.2 hqπ
      have hqj : (P.π p')[j] = q' := List.getElem_idxOf hj
      have hcov : Covered P k t p' (2 * j + 1) := by
        have := (segAsg_some P k t h).1
        unfold Covered
        split_ifs with hpk
        · rw [pathNodes_length, ite_eq_right (List.ne_nil_of_length_pos (by omega))]; omega
        · rcases this with h' | h'
          · exact absurd h' hpk
          · rw [show (2 * j + 1) / 2 = j by omega]; exact h'
      refine ⟨p', 2 * j + 1, cnt P k t p' j, hcov, ?_, ?_, h⟩
      · rw [node_odd P p' j hj, hqj]
        unfold xv; rw [min_eq_left hc.1.le, max_eq_right hc.1.le]
      · have hlen := covered_lt P k t hcov
        unfold mu
        rw [ite_eq_right (fun h' => absurd h'.2.2 (by
          rw [pathNodes_length, ite_eq_right (List.ne_nil_of_length_pos (by omega))]; omega)),
          show (2 * j + 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega,
          cnt_succ P k t p' j hj, hqj, ite_eq_right hq]
        ring
  · simp only [asg] at h
    split_ifs at h with hj
    refine Or.inr (Or.inr ?_)
    have hjm : j'.val < m := j'.isLt
    have hcov : Covered P k t e' (2 * j'.val + 2) := by
      have := (segAsg_some P k t h).1
      unfold Covered
      split_ifs with hpk
      · rw [pathNodes_length, ite_eq_right (List.ne_nil_of_length_pos (by omega))]; omega
      · rcases this with h' | h'
        · exact absurd h' hpk
        · rw [show (2 * j'.val + 2) / 2 = j'.val + 1 by omega]; exact h'
    refine ⟨e', 2 * j'.val + 2, cnt P k t e' (j'.val + 1), hcov, ?_, ?_, h⟩
    · rw [node_even P e' j'.val hj]
      unfold sv
      simp [Nat.mod_eq_of_lt hjm]
    · have hlen := covered_lt P k t hcov
      unfold mu
      rw [ite_eq_right (fun h' => absurd h'.2.2 (by
        rw [pathNodes_length, ite_eq_right (List.ne_nil_of_length_pos (by omega))]; omega)),
        show (2 * j'.val + 2) / 2 = j'.val + 1 by omega, show (2 * j'.val + 2 + 1) / 2 = j'.val + 1 by omega]
      ring

/-! ## Branch sets: nonempty and connected -/

theorem segAsg_lt_or_ge {e : Fin m} {c x : ℕ} (h : segAsg P k t e c = some x) :
    x < n ∨ (n + m * m ≤ x ∧ ∃ c', c = c' + 1 ∧ x = sId n m e.val c') := by
  rcases (segAsg_some P k t h).2 with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨hc, rfl⟩
  · exact Or.inl (E e).1.isLt
  · exact Or.inl (E e).2.isLt
  · exact Or.inr ⟨le_sId _ _ _ _, c - 1, by omega, rfl⟩

/-- An original vertex: its branch set is the vertex with the end segments of its edges. -/
theorem fiber_connected_orig (hes : Matches es E) (v : Fin n) :
    ((aug E P).induce (fiber P k t v.val)).Connected := by
  have hv : (ov v : AV n m) ∈ fiber P k t v.val := asg_ov P k t v
  have key : ∀ a (ha : a ∈ fiber P k t v.val), ((aug E P).induce (fiber P k t v.val)).Reachable ⟨_, hv⟩ ⟨a, ha⟩ := by
    intro a ha
    rcases asg_cases P k t hes ha with ⟨w, rfl, hw⟩ | ⟨e, g, hg, heg, rfl, hx⟩ | ⟨e, p, c, hcov, rfl, hmu, hs⟩
    · have : w = v := Fin.ext hw.symm
      subst this; rfl
    · exfalso
      have := le_xId n m e.val g.val
      have := v.isLt
      omega
    · rcases (segAsg_some P k t hs).2 with ⟨hc0, hx⟩ | ⟨he, hcL, hc0, hx⟩ | ⟨-, hx⟩
      · -- a tail segment: walk to position 0
        have hm0 : mu P k t e 0 = mu P k t e (0 + p) := by rw [mu_zero, Nat.zero_add, hmu, hc0]
        have hq : qnode P k t es e (mu P k t e (0 + p)) = v.val := by
          rw [Nat.zero_add, hmu, hc0, Nat.mul_zero, qnode_zero P k t hes (covered_drawn P k t hcov), hx]
        obtain ⟨h1, h2, hr⟩ := fiber_walk P k t hes e v.val p 0 (by rwa [Nat.zero_add]) hm0 hq
        have hov : node P e 0 = ov v := by
          rw [node_zero]; congr 1; exact Fin.ext hx.symm
        convert hr using 2
        · exact hov.symm
        · simp
      · -- a head segment: walk to the last position
        have hlen := covered_lt P k t hcov
        set D := (pathNodes E P e).length - 1 with hD
        have hpD : p ≤ D := by omega
        have hcovD : Covered P k t e (p + (D - p)) := by
          unfold Covered; rw [ite_eq_left he]; omega
        have hr0 : rowAt P k t e ≠ [] := List.ne_nil_of_length_pos (by omega)
        have hmuD : mu P k t e (p + (D - p)) = 2 * (rowAt P k t e).length := by
          rw [show p + (D - p) = D by omega]
          have hl := pathNodes_length P e
          have hπ : P.π e ≠ [] := fun h => hr0 (by
            have := (rowAt_sublist P k t e).length_le; rw [h] at this; simpa using this)
          rw [ite_eq_right hπ] at hl
          unfold mu
          rw [ite_eq_right (fun h => hr0 h.2.1), show D / 2 = (P.π e).length by omega,
            show (D + 1) / 2 = (P.π e).length by omega, cnt_of_le P k t e (le_refl _)]
          ring
        have hm : mu P k t e p = mu P k t e (p + (D - p)) := by rw [hmuD, hmu, hcL]
        have hq : qnode P k t es e (mu P k t e (p + (D - p))) = v.val := by
          rw [hmuD]
          rw [qnode_last P k t hes he]
          · exact hx.symm
          · rw [Q_length_closed P k t hes he, ite_eq_right hr0]
        obtain ⟨h1, h2, hr⟩ := fiber_walk P k t hes e v.val (D - p) p hcovD hm hq
        have hov : node P e (p + (D - p)) = ov v := by
          rw [node_last P e _ (by omega)]; congr 1; exact Fin.ext hx.symm
        have := hr.symm
        convert this using 2
        exact hov.symm
      · exfalso
        have := le_sId n m e.val (c - 1)
        have := v.isLt
        omega
  have : Nonempty (fiber P k t v.val) := ⟨⟨_, hv⟩⟩
  refine Connected.mk fun a b => ?_
  exact (key a.1 a.2).symm.trans (key b.1 b.2)

/-- A drawn crossing: its branch set is the crossing vertex alone. -/
theorem fiber_connected_cross (hes : Matches es E) {e g : Fin m} (hg : g ∈ rowAt P k t e) :
    ((aug E P).induce (fiber P k t (xId n m e.val g.val))).Connected := by
  have hv : (xv e g : AV n m) ∈ fiber P k t (xId n m e.val g.val) := asg_xv_drawn P k t hg
  have hgπ : g ∈ P.π e := (rowAt_sublist P k t e).subset hg
  have hne : g ≠ e := ne_of_mem_π P hgπ
  have key : ∀ a (ha : a ∈ fiber P k t (xId n m e.val g.val)), a = xv e g := by
    intro a ha
    rcases asg_cases P k t hes ha with ⟨w, rfl, hw⟩ | ⟨e', g', hg', heg', rfl, hx⟩ | ⟨e', p, c, hcov, rfl, hmu, hs⟩
    · exfalso
      have := le_xId n m e.val g.val
      have := w.isLt
      omega
    · rcases lt_or_gt_of_ne hne with h | h
      · -- g < e
        rw [xId_comm] at hx
        obtain ⟨h1, h2⟩ := xId_inj (show g.val < e.val from h) heg' e.isLt g'.isLt hx
        have : g = e' := Fin.ext h1
        have : e = g' := Fin.ext h2
        subst_vars
        unfold xv; rw [min_comm, max_comm]
      · obtain ⟨h1, h2⟩ := xId_inj (show e.val < g.val from h) heg' g.isLt g'.isLt hx
        have : e = e' := Fin.ext h1
        have : g = g' := Fin.ext h2
        subst_vars; rfl
    · exfalso
      rcases segAsg_lt_or_ge P k t hs with h | ⟨h, -⟩
      · have := le_xId n m e.val g.val; omega
      · have := xId_lt (n := n) e.isLt g.isLt; omega
  have : Nonempty (fiber P k t (xId n m e.val g.val)) := ⟨⟨_, hv⟩⟩
  refine Connected.mk fun a b => ?_
  have ha := key a.1 a.2
  have hb := key b.1 b.2
  have : a = b := Subtype.ext (ha.trans hb.symm)
  rw [this]

/-- A subdivision vertex: its branch set is an interval of its path. -/
theorem fiber_connected_sub (hes : Matches es E) {e : Fin m} (hd : Drawn P k t e) (c : ℕ)
    (hc : c + 1 < (rowAt P k t e).length) : ((aug E P).induce (fiber P k t (sId n m e.val c))).Connected := by
  obtain ⟨j, hj, hy, hcj⟩ := exists_pos_of_lt P k t e c (by omega)
  have hyR : (P.π e)[j] ∈ rowAt P k t e := hy ▸ List.getElem_mem (by omega)
  have hcj1 : cnt P k t e (j + 1) = c + 1 := by rw [cnt_succ P k t e j hj, ite_eq_left hyR, hcj]
  have hlenπ := pathNodes_length P e
  have hπ : P.π e ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [ite_eq_right hπ] at hlenπ
  -- the hub: the subdivision vertex after the `c`-th drawn crossing
  have hcovH : Covered P k t e (2 * j + 2) := by
    unfold Covered
    split_ifs with he
    · omega
    · rcases hd with hd | ⟨hd, -⟩
      · exact absurd hd he
      · rw [show (2 * j + 2) / 2 = j + 1 by omega, hcj1]; exact ⟨hd, hc⟩
  have hmuH : mu P k t e (2 * j + 2) = 2 * (c + 1) := by
    unfold mu
    rw [ite_eq_right (fun h => absurd h.2.1 (List.ne_nil_of_length_pos (by omega))),
      show (2 * j + 2) / 2 = j + 1 by omega, show (2 * j + 2 + 1) / 2 = j + 1 by omega, hcj1]
    ring
  have hqH : qnode P k t es e (2 * (c + 1)) = sId n m e.val c := by
    rw [show 2 * (c + 1) = 2 * c + 2 by ring, qnode_even P k t hes hd c hc]
  have hH : node P e (2 * j + 2) ∈ fiber P k t (sId n m e.val c) := by
    show asg P k t _ = some _
    rw [asg_node P k t hes e _ hcovH, hmuH, hqH]
  have key : ∀ a (ha : a ∈ fiber P k t (sId n m e.val c)),
      ((aug E P).induce (fiber P k t (sId n m e.val c))).Reachable ⟨_, hH⟩ ⟨a, ha⟩ := by
    intro a ha
    rcases asg_cases P k t hes ha with ⟨w, rfl, hw⟩ | ⟨e', g', hg', heg', rfl, hx⟩ | ⟨e', p, c', hcov, rfl, hmu, hs⟩
    · exfalso
      have := le_sId n m e.val c
      have := w.isLt
      omega
    · exfalso
      have := le_sId n m e.val c
      have := xId_lt (n := n) e'.isLt g'.isLt
      omega
    · rcases segAsg_lt_or_ge P k t hs with h | ⟨-, c'', hc'', hx⟩
      · have := le_sId n m e.val c; omega
      · have hcm : c < m := by
          have := (rowAt_sublist P k t e).length_le
          have := length_π_le P e
          omega
        have hc''m : c'' < m := by
          have h1 := mu_le_length P k t e' p
          have h2 := (rowAt_sublist P k t e').length_le
          have h3 := length_π_le P e'
          omega
        obtain ⟨h1, h2⟩ := sId_inj hcm hc''m hx
        have he' : e' = e := Fin.ext h1.symm
        subst he'
        have hmu' : mu P k t e' p = 2 * (c + 1) := by rw [hmu, hc'', ← h2]
        rcases le_total p (2 * j + 2) with hpH | hpH
        · obtain ⟨h1', h2', hr⟩ := fiber_walk P k t hes e' (sId n m e'.val c) (2 * j + 2 - p) p
            (by rw [show p + (2 * j + 2 - p) = 2 * j + 2 by omega]; exact hcovH)
            (by rw [show p + (2 * j + 2 - p) = 2 * j + 2 by omega, hmu', hmuH])
            (by rw [show p + (2 * j + 2 - p) = 2 * j + 2 by omega, hmuH, hqH])
          have := hr.symm
          convert this using 2
          rw [show p + (2 * j + 2 - p) = 2 * j + 2 by omega]
        · obtain ⟨h1', h2', hr⟩ := fiber_walk P k t hes e' (sId n m e'.val c) (p - (2 * j + 2)) (2 * j + 2)
            (by rw [show 2 * j + 2 + (p - (2 * j + 2)) = p by omega]; exact hcov)
            (by rw [show 2 * j + 2 + (p - (2 * j + 2)) = p by omega, hmu', hmuH])
            (by rw [show 2 * j + 2 + (p - (2 * j + 2)) = p by omega, hmu', hqH])
          convert hr using 2
          rw [show 2 * j + 2 + (p - (2 * j + 2)) = p by omega]
  have : Nonempty (fiber P k t (sId n m e.val c)) := ⟨⟨_, hH⟩⟩
  refine Connected.mk fun a b => ?_
  exact (key a.1 a.2).symm.trans (key b.1 b.2)

end Thrackle78.Checker
