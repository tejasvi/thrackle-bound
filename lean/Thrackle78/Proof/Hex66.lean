import Thrackle78.Proof.Hex66Check

/-!
# Two 6-cycles through a common vertex of a triangle-free thrackle have the same edges (L3v)

Rotate the cycles so that `c₀ = d₀`; the assignment of the remaining vertices has a certificate (`certOf66_ok`): the
second cycle uses only edges of the first, or the union contains a triangle, `C4`, `DB(6,6,0)`, …, `DB(6,6,-3)` or one
of `u66v_4`, `u66v_5`, `u66v_7`, each excluded by triangle-freeness, `c4`, or `link` with the computational facts.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

/-- Soundness of a certificate: equal edges, or some class embeds, which is impossible. -/
lemma cert66_sound (ax : ThrackleAxioms Thr) (comp : CompFacts) (hT : Thr G) (htri : G.CliqueFree 3)
    {c d : Fin 6 → V} (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0)
    (cert : ℕ × List ℕ) (h : checkCert66 (asgL66 c d) cert = true) : cycleEdges c = cycleEdges d := by
  have sound := fun {n m : ℕ} (E : Fin m → Fin n × Fin n) (h : checkE66 (asgL66 c d) n E cert.2 = true) =>
    copy_of_checkE66 hc hd h0 E cert.2 h
  unfold checkCert66 at h
  split at h
  · exact (not_K3 htri (sound _ h)).elim
  · exact (not_C4 Thr ax hT (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db660 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db661 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db662 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db663 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.v4 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.v5 (sound _ h)).elim
  · exact (not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.v7 (sound _ h)).elim
  · exact eq_of_eqB66 hc hd h0 h
  · exact absurd h (by decide)

/-- The core case: the cycles start at the same vertex. -/
lemma hex_core (ax : ThrackleAxioms Thr) (comp : CompFacts) (hT : Thr G) (htri : G.CliqueFree 3)
    {c d : Fin 6 → V} (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) :
    cycleEdges c = cycleEdges d := by
  have hv := asgL66_valid (c := c) hd.2.1
  have hok := certOf66_ok (asg66 c d 0) (asg66 c d 1) (asg66 c d 2) (asg66 c d 3) (asg66 c d 4) hv
  exact cert66_sound Thr ax comp hT htri hc hd h0 _ hok

/-- **L3v.** In a triangle-free thrackle, two 6-cycles with a common vertex have the same edges. -/
theorem hex_tf (ax : ThrackleAxioms Thr) (comp : CompFacts) (hT : Thr G) (htri : G.CliqueFree 3)
    (c d : Fin 6 → V) (hc : IsCycleMap G c) (hd : IsCycleMap G d) (hcom : ∃ i j, c i = d j) :
    cycleEdges c = cycleEdges d := by
  obtain ⟨i, j, hij⟩ := hcom
  rw [← cycleEdges_rot c i, ← cycleEdges_rot d j]
  refine hex_core Thr ax comp hT htri (cycle_rot hc i) (cycle_rot hd j) ?_
  simp only [zero_add]
  exact hij

end Thrackle78.Proof
