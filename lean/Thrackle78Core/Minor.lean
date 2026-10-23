/-!
# K5 / K3,3 minor-model certificates (core Lean only, precompilable)

A graph `G : AGraph` has the vertices `0, …, nv - 1` and adjacency lists, read symmetrically. A certificate
`c : MinorCert` gives the branch sets of a `K5` (`c.k5 = true`, branch sets `0, …, 4`) or a `K3,3` (`c.k5 = false`,
sides `{0, 1, 2}` and `{3, 4, 5}`) minor model:

* `branch u` lists the vertices of branch set `u` in a connection order: the entry `(v, j)` at position `i ≥ 1` says
  that `v` is adjacent to the vertex at position `j < i` (the `j` of position `0` is ignored);
* `wit e = (i, j)` gives, for the `e`-th edge `(u, u')` of `hEdges c.k5`, a graph edge between position `i` of branch
  `u` and position `j` of branch `u'`.

`checkMinor` accepts iff the branch sets are nonempty, in range and pairwise disjoint (each vertex labelled once), every
connection step and every witness is a graph edge. Its soundness (`Thrackle78.Checker.checkMinor_sound`) gives a minor
model in the sense of `Thrackle78.IsMinor`, so the graph is not `Thrackle78.Planar`.
-/

namespace Thrackle78Core

/-- A graph on the vertices `0, …, nv - 1` by adjacency lists, read symmetrically. -/
structure AGraph where
  nv : Nat
  adj : Array (Array Nat)

/-- `x ≠ y` and one of them lists the other. -/
def AGraph.hasEdge (G : AGraph) (x y : Nat) : Bool :=
  x != y && ((G.adj.getD x #[]).contains y || (G.adj.getD y #[]).contains x)

/-- A `K5` (`k5 = true`) or `K3,3` (`k5 = false`) minor-model certificate. -/
structure MinorCert where
  k5 : Bool
  branch : Array (Array (Nat × Nat))
  wit : Array (Nat × Nat)

/-- The edges of `K5` on `0, …, 4`, and of `K3,3` with sides `{0, 1, 2}` and `{3, 4, 5}`. -/
def hEdges (k5 : Bool) : Array (Nat × Nat) :=
  if k5 then #[(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
  else #[(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]

/-- The number of branch sets. -/
def numBranch (k5 : Bool) : Nat := if k5 then 5 else 6

/-- Label the vertices of one branch list with `u + 1`; `none` if a vertex is out of range or already labelled. -/
def labelList (u : Nat) : List (Nat × Nat) → Array Nat → Option (Array Nat)
  | [], lab => some lab
  | p :: rest, lab => if p.1 < lab.size ∧ lab.getD p.1 0 = 0 then labelList u rest (lab.set! p.1 (u + 1)) else none

/-- Label all branch lists (the branch with index `u` gets `u + 1`). -/
def labelBranches : List (Array (Nat × Nat)) → Nat → Array Nat → Option (Array Nat)
  | [], _, lab => some lab
  | B :: Bs, u, lab =>
    match labelList u B.toList lab with
    | none => none
    | some lab' => labelBranches Bs (u + 1) lab'

/-- The connection order of one branch list. -/
def connOK (G : AGraph) (B : Array (Nat × Nat)) : Bool :=
  (List.range B.size).all fun i => i == 0 || ((B.getD i (0, 0)).2 < i &&
    G.hasEdge (B.getD i (0, 0)).1 (B.getD (B.getD i (0, 0)).2 (0, 0)).1)

/-- The witness of the `e`-th edge. -/
def witOK (G : AGraph) (c : MinorCert) (e : Nat) : Bool :=
  let uu := (hEdges c.k5).getD e (0, 0)
  let ij := c.wit.getD e (0, 0)
  let Bu := c.branch.getD uu.1 #[]
  let Bv := c.branch.getD uu.2 #[]
  ij.1 < Bu.size && ij.2 < Bv.size && G.hasEdge (Bu.getD ij.1 (0, 0)).1 (Bv.getD ij.2 (0, 0)).1

/-- **The checker.** -/
def checkMinor (G : AGraph) (c : MinorCert) : Bool :=
  c.branch.size == numBranch c.k5 &&
  c.wit.size == (hEdges c.k5).size &&
  c.branch.all (fun B => 0 < B.size) &&
  c.branch.all (connOK G) &&
  (labelBranches c.branch.toList 0 (Array.replicate G.nv 0)).isSome &&
  (List.range (hEdges c.k5).size).all (witOK G c)

end Thrackle78Core
