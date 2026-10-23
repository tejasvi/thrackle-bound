/-
Thrackle78.NoSpike: the named hypothesis `NoSpikeFaces Thr` (facial walks do not backtrack), a hypothesis of the `51/38`
bound only.
-/
import Thrackle78.Hyp

namespace Thrackle78

open SimpleGraph

/-! ## Facial walks without spikes (used only for `51/38`) -/

/-- No facial walk reverses along an edge at once (`w_i ≠ w_{i+2}`). Face tracing in a cellular embedding leaves a
vertex along the rotation successor (or predecessor) of the arriving edge, which is the arriving edge itself only at a
vertex of degree 1; 2-connected graphs have minimum degree at least 2. -/
def FaceData.NoSpike {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : FaceData G) : Prop :=
  ∀ F ∈ D.faces, ∀ i : Fin F.len, F.v i ≠ F.v (finRotate F.len (finRotate F.len i))

/-- The facial structure of `faces`, with facial walks that do not backtrack. -/
structure NoSpikeFaces (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop) : Prop where
  faces_ns : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Thr G → TwoConn G →
    G.CliqueFree 3 → ∃ D : FaceData G, D.NoSpike

end Thrackle78
