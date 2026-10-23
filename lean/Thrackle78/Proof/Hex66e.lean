import Thrackle78.Proof.Hex66eCheck

/-!
# Two 6-cycles sharing an edge of a triangle-free thrackle have the same edges

Rotate (and reflect) the cycles so that the shared edge is `c₀c₁ = d₀d₁`; the assignment of the remaining vertices has
a certificate (`certOf66e_ok`): the second cycle uses only edges of the first, or the union contains a triangle, `C4`,
`DB(6,6,-1)`, `DB(6,6,-2)`, `DB(6,6,-3)`, `u66v_4` or `u66v_5`, each excluded by triangle-freeness, `c4`, or `link`
with the computational facts of `CompFacts15`.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

/-- Soundness of a certificate: equal edges, or some class embeds, which is impossible. -/
lemma cert66e_sound (ax : ThrackleAxioms Thr) (comp : CompFacts15) (hT : Thr G) (htri : G.CliqueFree 3)
    {c d : Fin 6 → V} (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1)
    (cert : ℕ × List ℕ) (h : checkCert66e (asgL66e c d) cert = true) : cycleEdges c = cycleEdges d := by
  have sound := fun {n m : ℕ} (E : Fin m → Fin n × Fin n) (h : checkE66e (asgL66e c d) n E cert.2 = true) =>
    copy_of_checkE66e hc hd h0 h1 E cert.2 h
  unfold checkCert66e at h
  split at h
  · exact (not_K3 htri (sound _ h)).elim
  · exact (not_C4 Thr ax hT (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db661 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db662 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db663 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.v4 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.v5 (sound _ h)).elim
  · exact eq_of_eqB66e hc hd h0 h1 h
  · exact absurd h (by decide)

/-- The core case: the cycles start with the same edge. -/
lemma hex_e_core (ax : ThrackleAxioms Thr) (comp : CompFacts15) (hT : Thr G) (htri : G.CliqueFree 3)
    {c d : Fin 6 → V} (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1) :
    cycleEdges c = cycleEdges d := by
  have hv := asgL66e_valid (c := c) hd.2.1
  have hok := certOf66e_ok (asg66e c d 0) (asg66e c d 1) (asg66e c d 2) (asg66e c d 3) hv
  exact cert66e_sound Thr ax comp hT htri hc hd h0 h1 _ hok

/-- **The 6-6 edge lemma.** In a triangle-free thrackle, two 6-cycles with a common edge have the same edges. -/
theorem hex_edge (ax : ThrackleAxioms Thr) (comp : CompFacts15) (hT : Thr G) (htri : G.CliqueFree 3)
    (c d : Fin 6 → V) (hc : IsCycleMap G c) (hd : IsCycleMap G d) (x : Sym2 V) (hxc : x ∈ cycleEdges c)
    (hxd : x ∈ cycleEdges d) : cycleEdges c = cycleEdges d := by
  simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and] at hxc hxd
  obtain ⟨i, rfl⟩ := hxc
  obtain ⟨j, hj⟩ := hxd
  rw [finRotate_apply, finRotate_apply] at hj
  rcases Sym2.eq_iff.1 hj with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · rw [← cycleEdges_rot c i, ← cycleEdges_rot d j]
    refine hex_e_core Thr ax comp hT htri (cycle_rot hc i) (cycle_rot hd j) ?_ ?_
    · simp only [zero_add]; exact e0.symm
    · simp only [add_comm (1 : Fin 6)]; exact e1.symm
  · rw [← cycleEdges_rot c i, ← cycleEdges_refl d j]
    refine hex_e_core Thr ax comp hT htri (cycle_rot hc i) (cycle_refl hd j) ?_ ?_
    · simp only [zero_add, sub_zero]; exact e1.symm
    · simp only [add_sub_cancel_right, add_comm (1 : Fin 6)]; exact e0.symm

end Thrackle78.Proof
