import Thrackle78Core.Search

/-!
# Minor-model checks against an edge test, and the edge test of a state (core Lean only)

`checkMinorE nv adj c` is `checkMinor` with the adjacency given by a function (read symmetrically, no loops) instead of
adjacency lists. `stateEdge n es k rows` decides the edges of the partial augmented graph of the state `(k, rows)`
directly from the rows (path neighbours of a crossing; diamond partners of a subdivision vertex or an original
vertex), so no graph is built.
-/

namespace Thrackle78Core

/-- The edge test read symmetrically, without loops. -/
def hasE (adj : Nat → Nat → Bool) (x y : Nat) : Bool := x != y && (adj x y || adj y x)

/-- The connection order of one branch list (edge test version). -/
def connOKE (adj : Nat → Nat → Bool) (B : Array (Nat × Nat)) : Bool :=
  (List.range B.size).all fun i => i == 0 || ((B.getD i (0, 0)).2 < i &&
    hasE adj (B.getD i (0, 0)).1 (B.getD (B.getD i (0, 0)).2 (0, 0)).1)

/-- The witness of the `e`-th edge (edge test version). -/
def witOKE (adj : Nat → Nat → Bool) (c : MinorCert) (e : Nat) : Bool :=
  let uu := (hEdges c.k5).getD e (0, 0)
  let ij := c.wit.getD e (0, 0)
  let Bu := c.branch.getD uu.1 #[]
  let Bv := c.branch.getD uu.2 #[]
  ij.1 < Bu.size && ij.2 < Bv.size && hasE adj (Bu.getD ij.1 (0, 0)).1 (Bv.getD ij.2 (0, 0)).1

/-- **The checker** with an edge test on the vertices `0, …, nv - 1`. -/
def checkMinorE (nv : Nat) (adj : Nat → Nat → Bool) (c : MinorCert) : Bool :=
  c.branch.size == numBranch c.k5 &&
  c.wit.size == (hEdges c.k5).size &&
  c.branch.all (fun B => 0 < B.size) &&
  c.branch.all (connOKE adj) &&
  (labelBranches c.branch.toList 0 (Array.replicate nv 0)).isSome &&
  (List.range (hEdges c.k5).size).all (witOKE adj c)

/-- Edge `e` of the state is drawn (closed, or open with a crossing). -/
def drawnE (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) (e : Nat) : Bool :=
  decide (e < es.size) && (decide (e < k) || (e == k && !(rows.getD e []).isEmpty))

/-- The crossing of `e` and `f` is drawn. -/
def presentE (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) (e f : Nat) : Bool :=
  drawnE es k rows e && drawnE es k rows f && (rows.getD e []).contains f && (rows.getD f []).contains e

/-- `y` is a path neighbour of the crossing with `f` on the path of `e`. -/
def pathNbr (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) (e f y : Nat) : Bool :=
  y == nbrB n es.size es e (rows.getD e []) f ||
    nbrA n es.size es e (rows.getD e []) (decide (e < k)) f == some y

/-- `y` is adjacent to the crossing vertex of `e` and `f`. -/
def crossAdj (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) (e f y : Nat) : Bool :=
  presentE es k rows e f && (pathNbr n es k rows e f y || pathNbr n es k rows f e y)

/-- `y` is a diamond partner of the subdivision vertex `i` of edge `e`. -/
def subAdj (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) (e i y : Nat) : Bool :=
  drawnE es k rows e && decide (i + 1 < (rows.getD e []).length) &&
    ((presentE es k rows e ((rows.getD e []).getD i 0) && pathNbr n es k rows ((rows.getD e []).getD i 0) e y) ||
     (presentE es k rows e ((rows.getD e []).getD (i + 1) 0) &&
       pathNbr n es k rows ((rows.getD e []).getD (i + 1) 0) e y))

/-- `w` is adjacent to the original vertex `v` (diamond partner at a first or last crossing, or the other end of an
edge without crossings). -/
def origAdj (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) (v w : Nat) : Bool :=
  (List.range es.size).any fun e => drawnE es k rows e &&
    (((es.getD e (0, 0)).1 == v &&
      (match rows.getD e [] with
        | [] => decide (e < k) && (es.getD e (0, 0)).2 == w
        | f :: _ => presentE es k rows e f && pathNbr n es k rows f e w)) ||
     ((es.getD e (0, 0)).2 == v && decide (e < k) &&
      (match (rows.getD e []).getLast? with
        | none => (es.getD e (0, 0)).1 == w
        | some f => presentE es k rows e f && pathNbr n es k rows f e w)))

/-- **The edge test of the partial augmented graph of the state `(k, rows)`.** -/
def stateEdge (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) (x y : Nat) : Bool :=
  let m := es.size
  let isX := fun z => decide (n ≤ z) && decide (z < n + m * m) && decide ((z - n) / m < (z - n) % m)
  let isS := fun z => decide (n + m * m ≤ z)
  if isX x then crossAdj n es k rows ((x - n) / m) ((x - n) % m) y
  else if isX y then crossAdj n es k rows ((y - n) / m) ((y - n) % m) x
  else if isS x then subAdj n es k rows ((x - n - m * m) / m) ((x - n - m * m) % m) y
  else if isS y then subAdj n es k rows ((y - n - m * m) / m) ((y - n - m * m) % m) x
  else decide (x < n) && decide (y < n) && origAdj n es k rows x y

end Thrackle78Core
