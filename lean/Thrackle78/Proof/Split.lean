import Thrackle78.Hyp

/-!
# Splitting a graph along a component or a cut vertex

A disconnected graph splits into a nonempty set of vertices closed under adjacency and its nonempty complement; a
connected graph with at least three vertices that is not 2-connected splits at a cut vertex `v` into `C ∪ {v}` and
`Cᶜ`, where `C` is a nonempty proper set closed under adjacency away from `v`. In both cases every edge lies on
exactly one side, so the edge numbers add up.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The number of edges of `G` inside `S`. -/
lemma card_induce (S : Finset V) :
    #(G.induce (S : Set V)).edgeFinset = #(G.edgeFinset.filter fun e => e.toFinset ⊆ S) := by
  rw [card_filter_edgeFinset_toFinset_subset]

/-- **Edges split.** If every edge lies inside exactly one of `S`, `T`, the edge numbers add up. -/
lemma edge_split (S T : Finset V) (hcov : ∀ e ∈ G.edgeFinset, e.toFinset ⊆ S ∨ e.toFinset ⊆ T)
    (hdis : ∀ e ∈ G.edgeFinset, ¬ (e.toFinset ⊆ S ∧ e.toFinset ⊆ T)) :
    #G.edgeFinset = #(G.induce (S : Set V)).edgeFinset + #(G.induce (T : Set V)).edgeFinset := by
  rw [card_induce, card_induce, ← Finset.card_union_of_disjoint]
  · congr 1
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro he
      rcases hcov e he with h | h
      · exact Or.inl ⟨he, h⟩
      · exact Or.inr ⟨he, h⟩
    · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact hdis e h1.1 ⟨h1.2, h2.2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The reachability class of `a` inside `W` is closed under adjacency within `W`. -/
lemma closed_class (W : Set V) (a : V) (ha : a ∈ W) :
    let C := {x | ∃ hx : x ∈ W, (G.induce W).Reachable ⟨a, ha⟩ ⟨x, hx⟩}
    a ∈ C ∧ C ⊆ W ∧ ∀ x ∈ C, ∀ y ∈ W, G.Adj x y → y ∈ C := by
  refine ⟨⟨ha, Reachable.refl _⟩, fun x hx => hx.1, ?_⟩
  rintro x ⟨hx, hr⟩ y hy hxy
  exact ⟨hy, hr.trans (Adj.reachable (by simpa using hxy))⟩

omit [DecidableRel G.Adj] in
/-- **Disconnected split.** -/
lemma disconnected_split [Nonempty V] (hG : ¬ G.Connected) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧ ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S := by
  classical
  have hpre : ¬ G.Preconnected := fun h => hG ⟨h⟩
  simp only [Preconnected, not_forall] at hpre
  obtain ⟨a, b, hab⟩ := hpre
  obtain ⟨haC, -, hcl⟩ := closed_class (G := G) Set.univ a (Set.mem_univ a)
  set C := {x | ∃ hx : x ∈ (Set.univ : Set V), (G.induce Set.univ).Reachable ⟨a, Set.mem_univ a⟩ ⟨x, hx⟩}
  refine ⟨C.toFinset, ⟨a, by simpa using haC⟩, ⟨b, ?_⟩, fun x hx y hxy => ?_⟩
  · rw [Finset.mem_compl, Set.mem_toFinset]
    intro hbC
    obtain ⟨_, hr⟩ := hbC
    exact hab (by simpa using SimpleGraph.Reachable.map (Embedding.induce (Set.univ : Set V)).toHom hr)
  · rw [Set.mem_toFinset] at hx ⊢
    exact hcl x hx y (Set.mem_univ y) hxy

omit [DecidableRel G.Adj] in
/-- **Cut-vertex split.** -/
lemma cut_split (hG : G.Connected) (h3 : 3 ≤ Fintype.card V) (h2 : ¬ TwoConn G) :
    ∃ (v : V) (C : Finset V), v ∉ C ∧ C.Nonempty ∧ (insert v C)ᶜ.Nonempty ∧
      ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = v := by
  classical
  simp only [TwoConn, not_and, not_forall] at h2
  obtain ⟨v, hv⟩ := h2 h3 hG
  set W : Set V := {w | w ≠ v}
  have hne : Nonempty W := by
    obtain ⟨w, hw⟩ : ∃ w : V, w ≠ v := by
      by_contra h
      push Not at h
      have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
      omega
    exact ⟨⟨w, hw⟩⟩
  have hpre : ¬ (G.induce W).Preconnected := fun h => hv ⟨h⟩
  simp only [Preconnected, not_forall] at hpre
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hpre
  obtain ⟨haC, hCW, hcl⟩ := closed_class (G := G) W a ha
  set C := {x | ∃ hx : x ∈ W, (G.induce W).Reachable ⟨a, ha⟩ ⟨x, hx⟩}
  refine ⟨v, C.toFinset, ?_, ⟨a, by simpa using haC⟩, ⟨b, ?_⟩, fun x hx y hxy => ?_⟩
  · rw [Set.mem_toFinset]
    exact fun h => (hCW h) rfl
  · simp only [Finset.mem_compl, Finset.mem_insert, Set.mem_toFinset, not_or]
    exact ⟨hb, fun ⟨_, hr⟩ => hab hr⟩
  · rw [Set.mem_toFinset] at hx ⊢
    by_cases hy : y = v
    · exact Or.inr hy
    · exact Or.inl (hcl x hx y hy hxy)

end Thrackle78.Proof
