import Thrackle78.Checker.Minor
import Thrackle78.Checker.AugPath
import Thrackle78.Checker.Restrict

/-!
# Relabeling the edges of a listing

For a permutation `σ` of the edges, a crossing system `P` of `E` gives the crossing system `relabel σ P` of `E ∘ σ`
(the same drawing with the edges renamed). The vertex map `psi σ` is an injective homomorphism from its augmented
graph to `aug E P` (`psi_adj`), so non-planarity transfers (`not_planar_of_relabel`).
-/

namespace Thrackle78.Checker

open SimpleGraph

variable {n m : ℕ} {E : Fin m → Fin n × Fin n} (σ : Equiv.Perm (Fin m))

theorem nonInc_comp {e f : Fin m} : NonInc (E ∘ σ) e f ↔ NonInc E (σ e) (σ f) := by
  unfold NonInc
  simp only [Function.comp, ne_eq, σ.injective.eq_iff]

/-- The crossing system of the relabeled listing `E ∘ σ`. -/
def relabel (P : CrossingSystem E) : CrossingSystem (E ∘ σ) where
  π e := (P.π (σ e)).map σ.symm
  nodup e := (P.nodup (σ e)).map σ.symm.injective
  mem e f := by
    rw [List.mem_map, nonInc_comp]
    constructor
    · rintro ⟨f', hf', rfl⟩
      simpa using (P.mem (σ e) f').1 hf'
    · intro h
      exact ⟨σ f, (P.mem (σ e) (σ f)).2 h, by simp⟩

/-- The vertex map of the relabeling (injective on all labels). -/
def psi : AV n m → AV n m
  | Sum.inl v => Sum.inl v
  | Sum.inr (Sum.inl (p, q)) =>
    if p < q then Sum.inr (Sum.inl (min (σ p) (σ q), max (σ p) (σ q)))
    else if q < p then Sum.inr (Sum.inl (max (σ p) (σ q), min (σ p) (σ q)))
    else Sum.inr (Sum.inl (σ p, σ q))
  | Sum.inr (Sum.inr (e, t)) => Sum.inr (Sum.inr (σ e, t))

theorem psi_left_inv (x : AV n m) : psi σ.symm (psi σ x) = x := by
  rcases x with v | ⟨p, q⟩ | ⟨e, t⟩
  · rfl
  · rcases lt_trichotomy p q with h | rfl | h
    · have hne : σ p ≠ σ q := fun e => (ne_of_lt h) (σ.injective e)
      simp only [psi, ite_eq_left h]
      rcases lt_or_gt_of_ne hne with h' | h'
      · rw [min_eq_left h'.le, max_eq_right h'.le, ite_eq_left h']
        simp [min_eq_left h.le, max_eq_right h.le]
      · rw [min_eq_right h'.le, max_eq_left h'.le, ite_eq_left h']
        simp only [Equiv.symm_apply_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
        rcases le_total p q with hpq | hpq <;> simp [min_def, max_def, hpq, h.le, not_le.2 h] <;> omega
    · simp [psi]
    · have hne : σ p ≠ σ q := fun e => (ne_of_gt h) (σ.injective e)
      simp only [psi, ite_eq_right (not_lt.2 h.le), ite_eq_left h]
      rcases lt_or_gt_of_ne hne with h' | h'
      · rw [max_eq_right h'.le, min_eq_left h'.le, ite_eq_right (not_lt.2 h'.le), ite_eq_left h']
        simp only [Equiv.symm_apply_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
        rcases le_total p q with hpq | hpq <;> simp [min_def, max_def, hpq, h.le, not_le.2 h] <;> omega
      · rw [max_eq_left h'.le, min_eq_right h'.le, ite_eq_right (not_lt.2 h'.le), ite_eq_left h']
        simp [max_eq_left h.le, min_eq_right h.le]
  · simp [psi]

theorem psi_injective : Function.Injective (psi (n := n) σ) :=
  Function.LeftInverse.injective (psi_left_inv σ)

theorem psi_xv {e f : Fin m} (hef : e ≠ f) : psi σ (xv e f : AV n m) = xv (σ e) (σ f) := by
  unfold xv
  rcases lt_or_gt_of_ne hef with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    simp [psi, h]
  · rw [min_eq_right h.le, max_eq_left h.le]
    simp only [psi, ite_eq_left h]
    rw [min_comm, max_comm]

theorem psi_sv (e : Fin m) (t : ℕ) : psi σ (sv e t : AV n m) = sv (σ e) t := rfl

theorem psi_ov (v : Fin n) : psi σ (ov v : AV n m) = ov v := rfl

theorem innerNodes_map (e : Fin m) : ∀ (l : List (Fin m)) (j : ℕ), (∀ f ∈ l, f ≠ e) →
    (innerNodes (n := n) e l j).map (psi σ) = innerNodes (σ e) (l.map σ) j
  | [], _, _ => rfl
  | [f], j, h => by
    simp [innerNodes, psi_xv σ (h f (by simp)).symm]
  | f :: g :: rest, j, h => by
    simp only [innerNodes, List.map_cons]
    rw [psi_xv σ (h f (by simp)).symm, psi_sv]
    have := innerNodes_map e (g :: rest) (j + 1) (fun f' hf' => h f' (List.mem_cons_of_mem _ hf'))
    simp only [List.map_cons] at this
    rw [this]

theorem relabel_π_map (P : CrossingSystem E) (e : Fin m) : ((relabel σ P).π e).map σ = P.π (σ e) := by
  simp [relabel, List.map_map]

theorem pathNodes_relabel (P : CrossingSystem E) (e : Fin m) :
    (pathNodes (E ∘ σ) (relabel σ P) e).map (psi σ) = pathNodes E P (σ e) := by
  rw [pathNodes_eq, pathNodes_eq, List.map_cons, List.map_append, innerNodes_map σ e _ 0
    (fun f hf => ne_of_mem_π (relabel σ P) hf), relabel_π_map]
  rfl

theorem idxOf_map_equiv {α β : Type} [DecidableEq α] [DecidableEq β] (g : α ≃ β) (l : List α) (x : α) :
    (l.map g).idxOf (g x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hax : a = x
    · subst hax; simp [List.idxOf_cons]
    · have : g a ≠ g x := fun h => hax (g.injective h)
      simp [List.idxOf_cons, hax, this, ih]

theorem nbrs_relabel (P : CrossingSystem E) (e f : Fin m) :
    (psi σ (nbrs (E ∘ σ) (relabel σ P) e f).1, psi σ (nbrs (E ∘ σ) (relabel σ P) e f).2) =
      nbrs E P (σ e) (σ f) := by
  have hidx : ((relabel σ P).π e).idxOf f = (P.π (σ e)).idxOf (σ f) := by
    rw [← relabel_π_map σ P e, idxOf_map_equiv]
  have hlen : ((relabel σ P).π e).length = (P.π (σ e)).length := by
    rw [← relabel_π_map σ P e, List.length_map]
  unfold nbrs
  simp only [hidx, hlen]
  congr 1 <;> split_ifs <;> rfl

theorem diamondEdges_comm (P : CrossingSystem E) (a b : Fin m) (x : Sym2 (AV n m)) :
    x ∈ diamondEdges E P a b ↔ x ∈ diamondEdges E P b a := by
  simp only [diamondEdges, List.mem_cons, List.mem_nil_iff, or_false]
  constructor <;> rintro (h | h | h | h) <;> simp only [h, Sym2.eq_swap] <;> tauto

/-- The relabeling vertex map is a homomorphism of augmented graphs. -/
theorem psi_mem_augEdges (P : CrossingSystem E) {a b : AV n m}
    (h : s(a, b) ∈ augEdges (E ∘ σ) (relabel σ P)) : s(psi σ a, psi σ b) ∈ augEdges E P := by
  rcases h with ⟨e, he⟩ | ⟨e, f, hef, hni, hx⟩
  · refine Or.inl ⟨σ e, ?_⟩
    unfold pathEdges at he ⊢
    rw [← pathNodes_relabel σ P e]
    obtain ⟨⟨x, y⟩, hxy, hs⟩ := List.mem_map.1 he
    rw [List.mem_map]
    refine ⟨(psi σ x, psi σ y), ?_, ?_⟩
    · rw [← List.map_tail, List.zip_map]
      exact List.mem_map.2 ⟨(x, y), hxy, rfl⟩
    · simp only at hs ⊢
      rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  · have hni' : NonInc E (σ e) (σ f) := (nonInc_comp σ).1 hni
    have hx' : s(psi σ a, psi σ b) ∈ diamondEdges E P (σ e) (σ f) := by
      have h1 := nbrs_relabel σ P e f
      have h2 := nbrs_relabel σ P f e
      unfold diamondEdges at hx ⊢
      rw [← h1, ← h2]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
      rcases hx with hx | hx | hx | hx <;> rcases Sym2.eq_iff.1 hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [Sym2.eq_swap]
    rcases lt_or_gt_of_ne (fun h => hni'.1 h) with h | h
    · exact Or.inr ⟨σ e, σ f, h, hni', hx'⟩
    · exact Or.inr ⟨σ f, σ e, h, NonInc.symm' hni', (diamondEdges_comm P _ _ _).1 hx'⟩

theorem psi_adj (P : CrossingSystem E) {a b : AV n m} (h : (aug (E ∘ σ) (relabel σ P)).Adj a b) :
    (aug E P).Adj (psi σ a) (psi σ b) := by
  unfold aug at h ⊢
  rw [SimpleGraph.fromEdgeSet_adj] at h ⊢
  exact ⟨psi_mem_augEdges σ P h.1, fun e => h.2 (psi_injective σ e)⟩

/-- **Non-planarity transfers along a relabeling.** -/
theorem not_planar_of_relabel (P : CrossingSystem E) (h : ¬ Planar (aug (E ∘ σ) (relabel σ P))) :
    ¬ Planar (aug E P) := by
  refine not_planar_of_map h (fun x => {psi σ x}) (fun x _ => Set.singleton_nonempty _) ?_ ?_ ?_
  · intro x _
    have : Nonempty ({psi σ x} : Set (AV n m)) := ⟨⟨_, rfl⟩⟩
    refine Connected.mk fun p q => ?_
    have : p = q := Subtype.ext (p.2.trans q.2.symm)
    rw [this]
  · intro x x' _ _ hxx'
    rw [Set.disjoint_singleton]
    exact fun e => hxx' (psi_injective σ e)
  · intro x x' hxx'
    exact ⟨_, rfl, _, rfl, psi_adj σ P hxx'⟩

end Thrackle78.Checker
