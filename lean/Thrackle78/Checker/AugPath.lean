import Thrackle78.Defs
import Thrackle78.Checker.Lists

/-!
# The paths of the augmented graph, by position

The path of edge `e` in `aug E P` has the nodes `ov tail`, then `xv e π₀, sv e 0, xv e π₁, sv e 1, …, xv e π_last`,
then `ov head` (`pathNodes_eq`): position `2j + 1` is the crossing with `πⱼ`, position `2j + 2` the subdivision vertex
after it (`node`). Consecutive nodes are joined (`node_adj`), and `nbrs` gives the nodes at positions `2j` and `2j + 2`
(`nbrs_fst_node`, `nbrs_snd_node`).
-/

namespace Thrackle78.Checker

open SimpleGraph

variable {n m : ℕ} {E : Fin m → Fin n × Fin n} (P : CrossingSystem E)

/-- The inner nodes `xv e f₀, sv e j, xv e f₁, sv e (j + 1), …` of a path with crossing list `f₀, f₁, …`. -/
def innerNodes (e : Fin m) : List (Fin m) → ℕ → List (AV n m)
  | [], _ => []
  | [f], _ => [xv e f]
  | f :: g :: rest, j => xv e f :: sv e j :: innerNodes e (g :: rest) (j + 1)

theorem flatten_mapIdx_eq (e : Fin m) : ∀ (l : List (Fin m)) (j0 K : ℕ), j0 + l.length = K →
    (l.mapIdx (fun i f => if j0 + i + 1 < K then [(xv e f : AV n m), sv e (j0 + i)] else [xv e f])).flatten =
      innerNodes e l j0
  | [], _, _, _ => rfl
  | [f], j0, K, h => by
    simp only [List.length_singleton] at h
    simp [innerNodes, show ¬ j0 + 0 + 1 < K by omega]
  | f :: g :: rest, j0, K, h => by
    simp only [List.length_cons] at h
    rw [List.mapIdx_cons, List.flatten_cons, ite_eq_left (by omega)]
    have ih := flatten_mapIdx_eq e (g :: rest) (j0 + 1) K (by simp; omega)
    have hfun : (fun i f => if j0 + (i + 1) + 1 < K then [(xv e f : AV n m), sv e (j0 + (i + 1))] else [xv e f]) =
        (fun i f => if j0 + 1 + i + 1 < K then [(xv e f : AV n m), sv e (j0 + 1 + i)] else [xv e f]) := by
      funext i f
      rw [show j0 + (i + 1) = j0 + 1 + i by omega]
    simp only [Nat.add_zero] at *
    rw [hfun, ih]
    rfl

theorem pathNodes_eq (e : Fin m) :
    pathNodes E P e = ov (E e).1 :: (innerNodes e (P.π e) 0 ++ [ov (E e).2]) := by
  unfold pathNodes
  rw [← flatten_mapIdx_eq e (P.π e) 0 (P.π e).length (by simp)]
  simp

theorem innerNodes_length (e : Fin m) : ∀ (l : List (Fin m)) (j : ℕ), l ≠ [] →
    (innerNodes (n := n) e l j).length = 2 * l.length - 1
  | [], _, h => absurd rfl h
  | [f], _, _ => rfl
  | f :: g :: rest, j, _ => by
    simp only [innerNodes, List.length_cons]
    rw [innerNodes_length e (g :: rest) (j + 1) (by simp)]
    simp only [List.length_cons]
    omega

theorem innerNodes_length_nil (e : Fin m) (j : ℕ) : (innerNodes (n := n) e [] j).length = 0 := rfl

/-- The node at position `p` of the path of `e` (the tail beyond the end). -/
def node (e : Fin m) (p : ℕ) : AV n m := (pathNodes E P e).getD p (ov (E e).1)

theorem node_of_getElem? {e : Fin m} {p : ℕ} {a : AV n m} (h : (pathNodes E P e)[p]? = some a) :
    node P e p = a := by
  simp [node, List.getD_eq_getElem?_getD, h]

theorem node_eq_getElem (e : Fin m) (p : ℕ) (hp : p < (pathNodes E P e).length) :
    node P e p = (pathNodes E P e)[p] := by
  simp [node, List.getElem?_eq_getElem hp]

theorem innerNodes_getElem?_even (e : Fin m) : ∀ (l : List (Fin m)) (j i : ℕ) (hi : i < l.length),
    (innerNodes (n := n) e l j)[2 * i]? = some (xv e l[i])
  | [], _, _, hi => absurd hi (by simp)
  | [f], j, i, hi => by
    simp only [List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    rfl
  | f :: g :: rest, j, i, hi => by
    cases i with
    | zero => rfl
    | succ i =>
      have := innerNodes_getElem?_even e (g :: rest) (j + 1) i (by simp at hi ⊢; omega)
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]
      simp only [innerNodes, List.getElem?_cons_succ]
      rw [this]
      simp

theorem innerNodes_getElem?_odd (e : Fin m) : ∀ (l : List (Fin m)) (j i : ℕ), i + 1 < l.length →
    (innerNodes (n := n) e l j)[2 * i + 1]? = some (sv e (j + i))
  | [], _, _, hi => absurd hi (by simp)
  | [f], _, _, hi => absurd hi (by simp)
  | f :: g :: rest, j, i, hi => by
    cases i with
    | zero => rfl
    | succ i =>
      have := innerNodes_getElem?_odd e (g :: rest) (j + 1) i (by simp at hi ⊢; omega)
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring]
      simp only [innerNodes, List.getElem?_cons_succ]
      rw [this, show j + 1 + i = j + (i + 1) by omega]

/-- The number of nodes of the path of `e`. -/
theorem pathNodes_length (e : Fin m) :
    (pathNodes E P e).length = if P.π e = [] then 2 else 2 * (P.π e).length + 1 := by
  rw [pathNodes_eq]
  split_ifs with h
  · rw [h]; rfl
  · have h1 := innerNodes_length (n := n) e (P.π e) 0 h
    have h2 : 0 < (P.π e).length := List.length_pos_iff.2 h
    simp only [List.length_cons, List.length_append, List.length_nil, h1]
    omega

theorem pathNodes_getElem?_zero (e : Fin m) : (pathNodes E P e)[0]? = some (ov (E e).1) := by
  simp [pathNodes_eq]

theorem pathNodes_getElem?_odd (e : Fin m) (j : ℕ) (hj : j < (P.π e).length) :
    (pathNodes E P e)[2 * j + 1]? = some (xv e (P.π e)[j]) := by
  have hne : P.π e ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlen := innerNodes_length (n := n) e (P.π e) 0 hne
  rw [pathNodes_eq, List.getElem?_cons_succ, List.getElem?_append_left (by omega)]
  exact innerNodes_getElem?_even e _ 0 j hj

theorem pathNodes_getElem?_even (e : Fin m) (j : ℕ) (hj : j + 1 < (P.π e).length) :
    (pathNodes E P e)[2 * j + 2]? = some (sv e j) := by
  have hne : P.π e ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlen := innerNodes_length (n := n) e (P.π e) 0 hne
  rw [pathNodes_eq, show 2 * j + 2 = (2 * j + 1) + 1 by ring, List.getElem?_cons_succ,
    List.getElem?_append_left (by omega), innerNodes_getElem?_odd e _ 0 j hj]
  simp

theorem pathNodes_getElem?_last (e : Fin m) (p : ℕ) (hp : p + 1 = (pathNodes E P e).length) :
    (pathNodes E P e)[p]? = some (ov (E e).2) := by
  rw [pathNodes_eq] at hp ⊢
  simp only [List.length_cons, List.length_append, List.length_nil] at hp
  rw [show p = (innerNodes (n := n) e (P.π e) 0).length + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (le_refl _)]
  simp

theorem node_zero (e : Fin m) : node P e 0 = ov (E e).1 := node_of_getElem? P (pathNodes_getElem?_zero P e)

theorem node_odd (e : Fin m) (j : ℕ) (hj : j < (P.π e).length) : node P e (2 * j + 1) = xv e (P.π e)[j] :=
  node_of_getElem? P (pathNodes_getElem?_odd P e j hj)

theorem node_even (e : Fin m) (j : ℕ) (hj : j + 1 < (P.π e).length) : node P e (2 * j + 2) = sv e j :=
  node_of_getElem? P (pathNodes_getElem?_even P e j hj)

theorem node_last (e : Fin m) (p : ℕ) (hp : p + 1 = (pathNodes E P e).length) : node P e p = ov (E e).2 :=
  node_of_getElem? P (pathNodes_getElem?_last P e p hp)

/-- Consecutive nodes of a path are joined in the augmented graph (or equal). -/
theorem node_adj (e : Fin m) (p : ℕ) (hp : p + 1 < (pathNodes E P e).length) :
    node P e p = node P e (p + 1) ∨ (aug E P).Adj (node P e p) (node P e (p + 1)) := by
  rw [node_eq_getElem P e p (by omega), node_eq_getElem P e (p + 1) hp]
  by_cases heq : (pathNodes E P e)[p] = (pathNodes E P e)[p + 1]
  · exact Or.inl heq
  · refine Or.inr ?_
    unfold aug
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨Or.inl ⟨e, ?_⟩, heq⟩
    unfold pathEdges
    rw [List.mem_map]
    refine ⟨((pathNodes E P e)[p], (pathNodes E P e)[p + 1]), ?_, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨p, by simp; omega, ?_⟩
    simp [List.getElem_zip, List.getElem_tail]

/-- An edge of `augEdges` between distinct vertices is an edge of `aug`. -/
theorem aug_adj_of_mem {a b : AV n m} (h : s(a, b) ∈ augEdges E P) (hab : a ≠ b) : (aug E P).Adj a b := by
  unfold aug
  rw [SimpleGraph.fromEdgeSet_adj]
  exact ⟨h, hab⟩

/-- The neighbours of a crossing on the path of `e`, by position. -/
theorem nbrs_eq (e : Fin m) (j : ℕ) (hj : j < (P.π e).length) :
    nbrs E P e (P.π e)[j] = (if j = 0 then ov (E e).1 else sv e (j - 1),
      if j + 1 = (P.π e).length then ov (E e).2 else sv e j) := by
  unfold nbrs
  rw [(P.nodup e).idxOf_getElem j hj]

theorem nbrs_fst_node (e : Fin m) (j : ℕ) (hj : j < (P.π e).length) :
    (nbrs E P e (P.π e)[j]).1 = node P e (2 * j) := by
  rw [nbrs_eq P e j hj]
  simp only
  split_ifs with h0
  · subst h0; exact (node_zero P e).symm
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [show 2 * (j' + 1) = 2 * j' + 2 by ring, node_even P e j' hj]
    simp

theorem nbrs_snd_node (e : Fin m) (j : ℕ) (hj : j < (P.π e).length) :
    (nbrs E P e (P.π e)[j]).2 = node P e (2 * j + 2) := by
  rw [nbrs_eq P e j hj]
  simp only
  split_ifs with h1
  · refine (node_last P e _ ?_).symm
    rw [pathNodes_length]
    have : P.π e ≠ [] := List.ne_nil_of_length_pos (by omega)
    simp [this]; omega
  · exact (node_even P e j (by omega)).symm

/-- The diamond edges of a crossing are edges of `augEdges`. -/
theorem diamond_mem {e f : Fin m} (hef : e < f) (hn : NonInc E e f) {x : Sym2 (AV n m)}
    (hx : x ∈ diamondEdges E P e f) : x ∈ augEdges E P :=
  Or.inr ⟨e, f, hef, hn, hx⟩

end Thrackle78.Checker
