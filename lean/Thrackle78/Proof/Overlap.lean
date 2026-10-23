import Thrackle78.Proof.OverlapCheck
import Thrackle78.Proof.Hex66e

/-!
# The overlap lemma: in a triangle-free thrackle, no 6-cycle shares an edge with an 8-cycle

Rotate (and reflect) the two cycles so that the shared edge is `w₀w₁ = d₀d₁`; the assignment of the remaining vertices
has a certificate (`certOf_ok`), which embeds a triangle, `C4`, one of the 13 computed graphs, or a union with two
6-cycles through a common vertex into the graph: each contradicts triangle-freeness, `c4`, `link` with the
computational facts, or the 6-6 edge lemma `hex_edge`.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

/-! ## The classes are excluded -/

lemma not_two_six (ax : ThrackleAxioms Thr) (comp : CompFacts15) (hT : Thr G) (htri : G.CliqueFree 3) {n m : ℕ}
    (E : Fin m → Fin n × Fin n) (c₁ c₂ : Fin 6 → Fin n) (hc₁ : IsCycleMap (ofListing E) c₁)
    (hc₂ : IsCycleMap (ofListing E) c₂) (x : Sym2 (Fin n)) (hx₁ : x ∈ cycleEdges c₁) (hx₂ : x ∈ cycleEdges c₂)
    (hne : cycleEdges c₁ ≠ cycleEdges c₂) (h : ofListing E ⊑ G) : False :=
  hne (hex_edge Thr ax comp (ax.sub _ _ h hT) (CliqueFree.comap h htri) c₁ c₂ hc₁ hc₂ x hx₁ hx₂)

/-! The two 6-cycles of each union `u2c6_k` (with a common edge and different edge sets). -/
def u0a : Fin 6 → Fin 11 := ![0, 1, 8, 9, 4, 10]
def u0b : Fin 6 → Fin 11 := ![0, 1, 2, 3, 4, 10]
def u1a : Fin 6 → Fin 10 := ![0, 1, 8, 5, 4, 9]
def u1b : Fin 6 → Fin 10 := ![0, 1, 8, 5, 6, 7]
def u2a : Fin 6 → Fin 9 := ![0, 1, 8, 5, 6, 7]
def u2b : Fin 6 → Fin 9 := ![1, 8, 5, 4, 3, 2]
def u3a : Fin 6 → Fin 8 := ![0, 1, 2, 6, 5, 4]
def u3b : Fin 6 → Fin 8 := ![0, 4, 3, 2, 6, 7]

/-- Soundness of a certificate: some class embeds, which is impossible. -/
lemma cert_false (ax : ThrackleAxioms Thr) (comp : CompFacts15) (hT : Thr G) (htri : G.CliqueFree 3)
    {c : Fin 6 → V} {d : Fin 8 → V} (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1)
    (cert : ℕ × List ℕ) (h : checkCert (asgL c d) cert = true) : False := by
  have sound := fun {n m : ℕ} (E : Fin m → Fin n × Fin n) (h : checkE (asgL c d) n E cert.2 = true) =>
    copy_of_checkE hc hd h0 h1 E cert.2 h
  unfold checkCert at h
  split at h
  · exact not_K3 htri (sound _ h)
  · exact not_C4 Thr ax hT (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db681 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db682 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.db683 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u7 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u8 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u9 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u10 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u11 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u12 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u13 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u14 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u15 (sound _ h)
  · exact not_listed Thr ax hT _ (by decide) (by decide) (by decide) comp.u16 (sound _ h)
  · exact not_two_six Thr ax comp hT htri _ u0a u0b (by unfold IsCycleMap; decide) (by unfold IsCycleMap; decide)
      s(0, 1) (by decide) (by decide) (by decide) (sound _ h)
  · exact not_two_six Thr ax comp hT htri _ u1a u1b (by unfold IsCycleMap; decide) (by unfold IsCycleMap; decide)
      s(0, 1) (by decide) (by decide) (by decide) (sound _ h)
  · exact not_two_six Thr ax comp hT htri _ u2a u2b (by unfold IsCycleMap; decide) (by unfold IsCycleMap; decide)
      s(1, 8) (by decide) (by decide) (by decide) (sound _ h)
  · exact not_two_six Thr ax comp hT htri _ u3a u3b (by unfold IsCycleMap; decide) (by unfold IsCycleMap; decide)
      s(0, 4) (by decide) (by decide) (by decide) (sound _ h)
  · exact absurd h (by decide)

/-- The core case: the cycles share the edge `c₀c₁ = d₀d₁`. -/
lemma overlap_core (ax : ThrackleAxioms Thr) (comp : CompFacts15) (hT : Thr G) (htri : G.CliqueFree 3)
    {c : Fin 6 → V} {d : Fin 8 → V} (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0)
    (h1 : c 1 = d 1) : False := by
  have hv := asgL_valid (d := d) hc.2.1
  have hok := certOf_ok (asg c d 0) (asg c d 1) (asg c d 2) (asg c d 3) hv
  exact cert_false Thr ax comp hT htri hc hd h0 h1 _ hok

/-- **The overlap lemma.** In a triangle-free thrackle no 6-cycle shares an edge with an 8-cycle. -/
theorem no_six_eight (ax : ThrackleAxioms Thr) (comp : CompFacts15) (hT : Thr G) (htri : G.CliqueFree 3)
    (c : Fin 6 → V) (d : Fin 8 → V) (hc : IsCycleMap G c) (hd : IsCycleMap G d) :
    Disjoint (cycleEdges c) (cycleEdges d) := by
  rw [Finset.disjoint_left]
  intro x hxc hxd
  simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and] at hxc hxd
  obtain ⟨i, rfl⟩ := hxc
  obtain ⟨j, hj⟩ := hxd
  rw [finRotate_apply, finRotate_apply] at hj
  rcases Sym2.eq_iff.1 hj with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · refine overlap_core Thr ax comp hT htri (cycle_rot hc i) (cycle_rot hd j) ?_ ?_
    · simp only [zero_add]; exact e0.symm
    · simp only [add_comm (1 : Fin 6), add_comm (1 : Fin 8)]; exact e1.symm
  · refine overlap_core Thr ax comp hT htri (cycle_rot hc i) (cycle_refl hd j) ?_ ?_
    · simp only [zero_add, sub_zero]; exact e1.symm
    · simp only [add_sub_cancel_right, add_comm (1 : Fin 6)]; exact e0.symm

end Thrackle78.Proof
