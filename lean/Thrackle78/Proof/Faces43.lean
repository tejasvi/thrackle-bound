import Thrackle78.Proof.Run3Face
import Thrackle78.Proof.Discharge43

/-!
# The `4/3` bound for 2-connected triangle-free thrackles

With face data without spikes and no copy of the three theta graphs, the run lemma for `4/3` gives at most six
6-edges on a 10-face (`ten_face_six`), and the discharging (`discharge43`) gives `4 f ≤ m`; with Euler:
`3 m ≤ 4 (n - 1)`, and `3 m ≤ 4 (n - 2)` if bipartite, except for `G = C6` in the bipartite bound.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

/-- **2-connected bound for `4/3`.** For a 2-connected triangle-free thrackle (face data without spikes) in which
two 6-cycles with a common vertex have the same edges and no 6-cycle shares an edge with an 8-cycle, with the theta
facts: `3 m + 4 ≤ 4 n`; if bipartite, `3 m + 8 ≤ 4 n` unless `m = n = 6`. -/
theorem twoConn_bound43 (ax : ThrackleAxioms Thr) (ns : NoSpikeFaces Thr) (th : ThetaFacts) (hT : Thr G)
    (h2 : TwoConn G) (htri : G.CliqueFree 3)
    (h66 : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → (∃ i j, c i = d j) → cycleEdges c = cycleEdges d)
    (h68 : ∀ (c : Fin 6 → V) (d : Fin 8 → V), IsCycleMap G c → IsCycleMap G d →
      Disjoint (cycleEdges c) (cycleEdges d)) :
    3 * G.edgeFinset.card + 4 ≤ 4 * Fintype.card V ∧
      (G.Colorable 2 → 3 * G.edgeFinset.card + 8 ≤ 4 * Fintype.card V ∨
        (G.edgeFinset.card = 6 ∧ Fintype.card V = 6)) := by
  have h66e : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → ∀ x, x ∈ cycleEdges c → x ∈ cycleEdges d →
      cycleEdges c = cycleEdges d :=
    fun c d hc hd x hxc hxd => h66 c d hc hd (common_vertex_cyc c d x hxc hxd)
  obtain ⟨D, hD⟩ := ns.faces_ns G hT h2 htri
  have hc4 : ∀ c : Fin 4 → V, IsCycleMap G c → False := fun c hc => no_C4 Thr ax hT c hc
  have h233 : ¬ ofListing (mkE 7 lTH233) ⊑ G := fun h =>
    not_listed Thr ax hT (mkE 7 lTH233) (by decide) (by decide) (by decide) th.th233 h
  have h234 : ¬ ofListing (mkE 8 lTH234) ⊑ G := fun h =>
    not_listed Thr ax hT (mkE 8 lTH234) (by decide) (by decide) (by decide) th.th234 h
  have h337 : ¬ ofListing (mkE 12 lTH337) ⊑ G := fun h =>
    not_listed Thr ax hT (mkE 12 lTH337) (by decide) (by decide) (by decide) th.th337 h
  have hlen := face_len_ge_six Thr ax hT D
  by_cases hcase : ∃ i j : Fin D.faces.length, i ≠ j ∧ Function.Injective (D.faces.get i).v ∧
      Function.Injective (D.faces.get j).v ∧ (D.faces.get i).edges = (D.faces.get j).edges
  · -- `G` is a single cycle: `m = len ≤ n`
    obtain ⟨i, j, hij, hi, hj, he⟩ := hcase
    have hE := D.distinct i j hij hi hj he
    have hm : G.edgeFinset.card = (D.faces.get i).len := by
      rw [hE, card_edges_of_injective _ hi (by have := hlen i; omega)]
    have hn : (D.faces.get i).len ≤ Fintype.card V := by
      simpa using Fintype.card_le_of_injective _ hi
    have h6 := hlen i
    obtain ⟨k, hk⟩ := D.even _ (List.get_mem _ i)
    refine ⟨by omega, fun _ => ?_⟩
    by_cases h8 : 8 ≤ (D.faces.get i).len
    · left; omega
    · by_cases h7 : 7 ≤ Fintype.card V
      · left; omega
      · right; omega
  · push Not at hcase
    have hAC := rule_applies Thr ax hT D h66e h68 fun i j hij hi hj => hcase i j hij hi hj
    have hd := discharge43 D hlen hAC fun a ha => ten_face_six D hD h66 h68 htri hc4 h233 h234 h337 a ha
    have e1 := D.euler
    refine ⟨by omega, fun hbip => Or.inl ?_⟩
    have e2 := D.euler_bip hbip
    omega

end Thrackle78.Proof
