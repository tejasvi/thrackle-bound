/-
Thrackle78.Defs: definitions for the statement "every thrackle on n >= 4 vertices has at most 15/11 (n - 1) edges".

* `Planar H`: combinatorial planarity by Wagner's characterization (no `K₅` and no `K₃,₃` minor).
* `aug E P`: the Fulek-Pach augmented graph of an oriented edge listing `E` and a crossing system `P`.
* `CombThr E`: some crossing system has a planar augmented graph (combinatorial thrackleability).
* `FaceData G`: the combinatorial shadow of a cellular embedding in the sphere or the projective plane used by the
  discharging argument.
-/
import Mathlib

namespace Thrackle78

open SimpleGraph

/-! ## Planarity (Wagner) -/

section Planarity

/-- `H` is a minor of `G`: nonempty, connected, pairwise disjoint branch sets, adjacent along every edge of `H`. -/
def IsMinor {U W : Type} (H : SimpleGraph U) (G : SimpleGraph W) : Prop :=
  ∃ B : U → Set W, (∀ u, (B u).Nonempty) ∧ (∀ u, (G.induce (B u)).Connected) ∧
    (Pairwise fun u u' => Disjoint (B u) (B u')) ∧ ∀ u u', H.Adj u u' → ∃ x ∈ B u, ∃ y ∈ B u', G.Adj x y

/-- Planarity by Wagner's characterization: no `K₅` minor and no `K₃,₃` minor. Non-planarity has finite certificates
(minor models, e.g. Kuratowski subdivisions); a graph drawn in the plane without crossings satisfies `Planar` (the easy
direction of Wagner's theorem). -/
def Planar {W : Type} (G : SimpleGraph W) : Prop :=
  ¬ IsMinor (completeGraph (Fin 5)) G ∧ ¬ IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G

end Planarity

/-! ## Oriented edge listings, crossing systems, augmented graph -/

section Augmented

variable {n m : ℕ}

/-- Edges `e` and `f` of the listing `E` are distinct and have no common endpoint. -/
def NonInc (E : Fin m → Fin n × Fin n) (e f : Fin m) : Prop :=
  e ≠ f ∧ (E e).1 ≠ (E f).1 ∧ (E e).1 ≠ (E f).2 ∧ (E e).2 ≠ (E f).1 ∧ (E e).2 ≠ (E f).2

instance (E : Fin m → Fin n × Fin n) (e f : Fin m) : Decidable (NonInc E e f) := by
  unfold NonInc; infer_instance

/-- A crossing system: for each edge, the order (from tail to head) of its crossings with the edges not incident to
it; every such edge appears exactly once. -/
structure CrossingSystem (E : Fin m → Fin n × Fin n) where
  π : Fin m → List (Fin m)
  nodup : ∀ e, (π e).Nodup
  mem : ∀ e f, f ∈ π e ↔ NonInc E e f

/-- Vertices of the augmented graph: original vertices, crossing vertices `(e, f)` (used with `e < f`), and
subdivision vertices `(e, t)` (between the t-th and (t+1)-th crossing of `e`, 0-based). Unused labels are isolated. -/
abbrev AV (n m : ℕ) := Fin n ⊕ (Fin m × Fin m) ⊕ (Fin m × Fin m)

/-- Original vertex. -/
def ov (v : Fin n) : AV n m := Sum.inl v

/-- The crossing vertex of edges `e` and `f`. -/
def xv (e f : Fin m) : AV n m := Sum.inr (Sum.inl (min e f, max e f))

/-- Subdivision vertex of edge `e` after its crossing number `t`; only used with `t + 1 < (P.π e).length < m`. -/
def sv (e : Fin m) (t : ℕ) : AV n m := Sum.inr (Sum.inr (e, ⟨t % m, Nat.mod_lt _ e.pos⟩))

variable {E : Fin m → Fin n × Fin n}

/-- Neighbours (before, after) of the crossing vertex of `e` and `f` on the path of edge `e`. -/
def nbrs (E : Fin m → Fin n × Fin n) (P : CrossingSystem E) (e f : Fin m) : AV n m × AV n m :=
  let j := (P.π e).idxOf f
  let k := (P.π e).length
  (if j = 0 then ov (E e).1 else sv e (j - 1), if j + 1 = k then ov (E e).2 else sv e j)

/-- The path of edge `e` in the augmented graph, as its list of nodes from tail to head. -/
def pathNodes (E : Fin m → Fin n × Fin n) (P : CrossingSystem E) (e : Fin m) : List (AV n m) :=
  [ov (E e).1] ++
    ((P.π e).mapIdx (fun j f => if j + 1 < (P.π e).length then [xv e f, sv e j] else [xv e f])).flatten ++
    [ov (E e).2]

/-- Unordered pairs of consecutive nodes on the path of `e`. -/
def pathEdges (E : Fin m → Fin n × Fin n) (P : CrossingSystem E) (e : Fin m) : List (Sym2 (AV n m)) :=
  ((pathNodes E P e).zip (pathNodes E P e).tail).map (fun p => s(p.1, p.2))

/-- The four diamond edges at the crossing of `e` and `f`: an alternating 4-cycle through the neighbours. -/
def diamondEdges (E : Fin m → Fin n × Fin n) (P : CrossingSystem E) (e f : Fin m) : List (Sym2 (AV n m)) :=
  let a := nbrs E P e f
  let b := nbrs E P f e
  [s(a.1, b.1), s(b.1, a.2), s(a.2, b.2), s(b.2, a.1)]

/-- Edge set of the augmented graph. -/
def augEdges (E : Fin m → Fin n × Fin n) (P : CrossingSystem E) : Set (Sym2 (AV n m)) :=
  {x | (∃ e, x ∈ pathEdges E P e) ∨ (∃ e f, e < f ∧ NonInc E e f ∧ x ∈ diamondEdges E P e f)}

/-- The Fulek-Pach augmented graph (loops are removed by `fromEdgeSet`; there are none anyway). -/
def aug (E : Fin m → Fin n × Fin n) (P : CrossingSystem E) : SimpleGraph (AV n m) :=
  SimpleGraph.fromEdgeSet (augEdges E P)

/-- Combinatorial thrackleability of an oriented edge listing. -/
def CombThr (E : Fin m → Fin n × Fin n) : Prop :=
  ∃ P : CrossingSystem E, Planar (aug E P)

/-- `E` lists every edge of `G` exactly once, each with some orientation. -/
def IsEdgeListing {V : Type} (G : SimpleGraph V) (E : Fin m → V × V) : Prop :=
  (∀ e, G.Adj (E e).1 (E e).2) ∧ (∀ e f, s((E e).1, (E e).2) = s((E f).1, (E f).2) → e = f) ∧
    (∀ u v, G.Adj u v → ∃ e, s((E e).1, (E e).2) = s(u, v))

/-- The graph spanned by an edge listing. -/
def ofListing (E : Fin m → Fin n × Fin n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {x | ∃ e, x = s((E e).1, (E e).2)}

end Augmented

/-! ## Cycles, 2-connectivity, face data -/

section Faces

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `c : Fin k → V` traverses a cycle of length `k >= 3` of `G` (injective, consecutive vertices adjacent). -/
def IsCycleMap (G : SimpleGraph V) {k : ℕ} (c : Fin k → V) : Prop :=
  3 ≤ k ∧ Function.Injective c ∧ ∀ i : Fin k, G.Adj (c i) (c (finRotate k i))

/-- The edge set of a cycle map. -/
def cycleEdges {k : ℕ} (c : Fin k → V) : Finset (Sym2 V) :=
  Finset.univ.image (fun i : Fin k => s(c i, c (finRotate k i)))

/-- 2-connected: at least 3 vertices, connected, and connected after deleting any one vertex. -/
def TwoConn (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧ ∀ v : V, (G.induce {w | w ≠ v}).Connected

/-- A closed walk of positive length. -/
structure CWalk (G : SimpleGraph V) where
  len : ℕ
  pos : 0 < len
  v : Fin len → V
  adj : ∀ i : Fin len, G.Adj (v i) (v (finRotate len i))

/-- Number of times the closed walk traverses the edge `x`. -/
def CWalk.count {G : SimpleGraph V} (W : CWalk G) (x : Sym2 V) : ℕ :=
  (Finset.univ.filter (fun i : Fin W.len => s(W.v i, W.v (finRotate W.len i)) = x)).card

/-- The edge set traversed by a closed walk. -/
def CWalk.edges {G : SimpleGraph V} (W : CWalk G) : Finset (Sym2 V) :=
  Finset.univ.image (fun i : Fin W.len => s(W.v i, W.v (finRotate W.len i)))

/-- The facial structure of an embedding of a 2-connected graph `G` (at least 3 vertices) in the sphere or the
projective plane, as used by the discharging argument (one entry per facial boundary walk):
* `cover`: every edge is traversed twice in total (its two sides);
* `euler`: `e + 1 <= n + f` (Euler for the projective plane; the sphere gives `e + 2 = n + f`);
* `even`: facial walks have even length (parity embedding, FP19);
* `three_le`: facial walks have length at least 3 (a facial walk of length 2 needs a vertex of degree 1);
* `short_simple`: facial walks of length at most 8 are cycles (FP19, Prop. 1);
* `euler_bip`: if `G` is bipartite the embedding is planar, `e + 2 <= n + f` (FP19, Cor. 1);
* `distinct`: two different facial walks that are both cycles with the same edge set exhaust `G` (a cycle bounding
  faces on both sides is the whole connected graph). -/
structure FaceData (G : SimpleGraph V) [DecidableRel G.Adj] where
  faces : List (CWalk G)
  cover : ∀ x ∈ G.edgeFinset, (faces.map (fun F => F.count x)).sum = 2
  euler : G.edgeFinset.card + 1 ≤ Fintype.card V + faces.length
  even : ∀ F ∈ faces, Even F.len
  three_le : ∀ F ∈ faces, 3 ≤ F.len
  short_simple : ∀ F ∈ faces, F.len ≤ 8 → Function.Injective F.v
  euler_bip : G.Colorable 2 → G.edgeFinset.card + 2 ≤ Fintype.card V + faces.length
  distinct : ∀ i j : Fin faces.length, i ≠ j → Function.Injective (faces.get i).v →
    Function.Injective (faces.get j).v → (faces.get i).edges = (faces.get j).edges →
    G.edgeFinset = (faces.get i).edges

end Faces

end Thrackle78
