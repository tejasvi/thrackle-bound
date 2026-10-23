/-
Thrackle78Full: the twenty computational facts of `CompFacts` (each proved by its native run in `Thrackle78Facts`),
and the three bounds of `Thrackle78.Main` with `CompFacts` / `CompFacts15` discharged.
-/
import Thrackle78.Main
import Thrackle78Facts.DB660
import Thrackle78Facts.DB661
import Thrackle78Facts.DB662
import Thrackle78Facts.DB663
import Thrackle78Facts.DB681
import Thrackle78Facts.DB682
import Thrackle78Facts.DB683
import Thrackle78Facts.U7
import Thrackle78Facts.U8
import Thrackle78Facts.U9
import Thrackle78Facts.U10
import Thrackle78Facts.U11
import Thrackle78Facts.U12
import Thrackle78Facts.U13
import Thrackle78Facts.U14
import Thrackle78Facts.U15
import Thrackle78Facts.U16
import Thrackle78Facts.V4
import Thrackle78Facts.V5
import Thrackle78Facts.V7

namespace Thrackle78

open SimpleGraph

/-- The twenty computed graphs are not combinatorially thrackleable. -/
theorem compFacts : CompFacts :=
  { db681 := Facts.db681, db682 := Facts.db682, db683 := Facts.db683,
    u7 := Facts.u7, u8 := Facts.u8, u9 := Facts.u9, u10 := Facts.u10, u11 := Facts.u11, u12 := Facts.u12,
    u13 := Facts.u13, u14 := Facts.u14, u15 := Facts.u15, u16 := Facts.u16,
    db661 := Facts.db661, db662 := Facts.db662, db663 := Facts.db663,
    v4 := Facts.v4, v5 := Facts.v5, db660 := Facts.db660, v7 := Facts.v7 }

/-- The eighteen computed graphs of the `15/11` bound are not combinatorially thrackleable. -/
theorem compFacts15 : CompFacts15 :=
  { db681 := Facts.db681, db682 := Facts.db682, db683 := Facts.db683,
    u7 := Facts.u7, u8 := Facts.u8, u9 := Facts.u9, u10 := Facts.u10, u11 := Facts.u11, u12 := Facts.u12,
    u13 := Facts.u13, u14 := Facts.u14, u15 := Facts.u15, u16 := Facts.u16,
    db661 := Facts.db661, db662 := Facts.db662, db663 := Facts.db663,
    v4 := Facts.v4, v5 := Facts.v5 }

/-- **Main theorem.** Every thrackleable graph on `n ≥ 4` vertices has at most `27/20 (n - 1)` edges, from the
published facts `ThrackleAxioms`. -/
theorem thrackle_bound_full (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)
    (ax : ThrackleAxioms Thr)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Thr G) (hn : 4 ≤ Fintype.card V) :
    20 * Nat.card G.edgeSet ≤ 27 * (Fintype.card V - 1) :=
  thrackle_bound Thr ax compFacts G hG hn

/-- **The bound `15/11 (n - 1)`**, from the published facts `ThrackleAxioms`. -/
theorem thrackle_bound_15_11_full (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)
    (ax : ThrackleAxioms Thr)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Thr G) (hn : 4 ≤ Fintype.card V) :
    11 * Nat.card G.edgeSet ≤ 15 * (Fintype.card V - 1) :=
  thrackle_bound_15_11 Thr ax compFacts15 G hG hn

/-- **The bound `51/38 (n - 1)`**, from the published facts `ThrackleAxioms` and facial walks without spikes
(`NoSpikeFaces`). -/
theorem thrackle_bound_51_38_full (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)
    (ax : ThrackleAxioms Thr) (ns : NoSpikeFaces Thr)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Thr G) (hn : 4 ≤ Fintype.card V) :
    38 * Nat.card G.edgeSet ≤ 51 * (Fintype.card V - 1) :=
  thrackle_bound_51_38 Thr ax ns compFacts G hG hn

end Thrackle78
