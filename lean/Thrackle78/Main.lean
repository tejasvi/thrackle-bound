/-
Thrackle78.Main: the main statements.
-/
import Thrackle78.Proof.Cases5138
import Thrackle78.Proof.Cases43

namespace Thrackle78

open SimpleGraph

/-- **Main theorem.** Let `Thr` satisfy the published facts `ThrackleAxioms`, and suppose the twenty computed graphs
are not combinatorially thrackleable (`CompFacts`, oriented edge listings exactly as run). Then every thrackleable
graph on `n ≥ 4` vertices has at most `27/20 (n - 1)` edges. -/
theorem thrackle_bound (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)
    (ax : ThrackleAxioms Thr) (comp : CompFacts)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Thr G) (hn : 4 ≤ Fintype.card V) :
    20 * Nat.card G.edgeSet ≤ 27 * (Fintype.card V - 1) := by
  classical
  have h := (Proof.case3_2720 Thr ax comp (Fintype.card V) G rfl (by omega) hG).2 hn
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  omega

/-- **The bound `15/11 (n - 1)`**, from the published facts and the eighteen computed graphs of `CompFacts15` (proved
without the 10-face lemma and without `DB(6,6,0)`, `u66v_7`). -/
theorem thrackle_bound_15_11 (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)
    (ax : ThrackleAxioms Thr) (comp : CompFacts15)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Thr G) (hn : 4 ≤ Fintype.card V) :
    11 * Nat.card G.edgeSet ≤ 15 * (Fintype.card V - 1) := by
  classical
  have h := (Proof.case3 Thr ax comp (Fintype.card V) G rfl (by omega) hG).2 hn
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  omega

/-- **The bound `51/38 (n - 1)`** (the run lemma on 10-faces), from the published facts, facial walks without
spikes (`NoSpikeFaces`), and the twenty computed graphs of `CompFacts`. -/
theorem thrackle_bound_51_38 (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)
    (ax : ThrackleAxioms Thr) (ns : NoSpikeFaces Thr) (comp : CompFacts)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Thr G) (hn : 4 ≤ Fintype.card V) :
    38 * Nat.card G.edgeSet ≤ 51 * (Fintype.card V - 1) := by
  classical
  have h := (Proof.case3_5138 Thr ax ns comp (Fintype.card V) G rfl (by omega) hG).2 hn
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  omega

/-- **The bound `4/3 (n - 1)`** (maximal runs of 6-edges on a 10-face have length at most 2), from the published
facts, facial walks without spikes (`NoSpikeFaces`), the twenty computed graphs of `CompFacts` and the three theta
graphs of `ThetaFacts`. -/
theorem thrackle_bound_4_3 (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)
    (ax : ThrackleAxioms Thr) (ns : NoSpikeFaces Thr) (comp : CompFacts) (th : ThetaFacts)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Thr G) (hn : 4 ≤ Fintype.card V) :
    3 * Nat.card G.edgeSet ≤ 4 * (Fintype.card V - 1) := by
  classical
  have h := (Proof.case3_43 Thr ax ns comp th (Fintype.card V) G rfl (by omega) hG).2 hn
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  omega

end Thrackle78
