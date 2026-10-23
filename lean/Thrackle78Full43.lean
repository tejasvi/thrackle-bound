/-
Thrackle78Full43: the three theta facts (`TH233`, `TH234`, `TH337`; each by its native
search) and the `4/3` bound of `Thrackle78.Main` with `CompFacts` and `ThetaFacts` discharged.
-/
import Thrackle78Full
import Thrackle78Facts.TH233
import Thrackle78Facts.TH234
import Thrackle78Facts.TH337

namespace Thrackle78

open SimpleGraph

/-- The three theta graphs are not combinatorially thrackleable. -/
theorem thetaFacts : ThetaFacts :=
  { th233 := Facts.th233, th234 := Facts.th234, th337 := Facts.th337 }

/-- **The bound `4/3 (n - 1)`**, from the published facts `ThrackleAxioms` and facial walks without spikes
(`NoSpikeFaces`). -/
theorem thrackle_bound_4_3_full (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)
    (ax : ThrackleAxioms Thr) (ns : NoSpikeFaces Thr)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Thr G) (hn : 4 ≤ Fintype.card V) :
    3 * Nat.card G.edgeSet ≤ 4 * (Fintype.card V - 1) :=
  thrackle_bound_4_3 Thr ax ns compFacts thetaFacts G hG hn

end Thrackle78
