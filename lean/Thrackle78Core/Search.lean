import Thrackle78Core.Minor

/-!
# The crossing-system search with minor-model certificates (core Lean only, precompilable)

A listing `es` gives the edges `0, …, m - 1` (`m = es.size`) as oriented pairs `(tail, head)` of vertices `< n`. The
search adds the edges in this order and traces each edge from its tail, one crossing at a time (SPEC §3, §9):

* a state is `(k, rows)`: the edges `e < k` are drawn completely, edge `k` up to its last crossing; `rows[e]` lists the
  crossing partners of `e` from tail to head;
* if edge `k` has crossed all its earlier partners (edges `f < k` without a common endpoint), the only child closes it:
  `(k + 1, rows)`; otherwise the children cross an earlier partner `f` not crossed yet, inserted at any position of
  `rows[f]` (`children`).

`stateGraph` is the partial augmented graph of a state, on the vertex ids
`v` (original vertex), `xId n m e f` (crossing of `e` and `f`), `sId n m e i` (subdivision vertex of `e` after its
`i`-th crossing): the path of every drawn edge, and at every crossing the drawn edges of its diamond.

`walk` checks a pre-order certificate of the search tree: at every node either a `K₅`/`K₃,₃` minor model of the partial
augmented graph (tag `1`), or the expansion into the children (tag `0`); leaves (`k = m`) must be pruned. The data are
read through a `Reader`; the soundness (`Thrackle78.Checker.not_combThr_of_check`) does not depend on it.
-/

namespace Thrackle78Core

/-- The edges `e` and `f` of the listing are distinct and share no endpoint. -/
def nonInc (es : Array (Nat × Nat)) (e f : Nat) : Bool :=
  e != f && (es.getD e (0, 0)).1 != (es.getD f (0, 0)).1 && (es.getD e (0, 0)).1 != (es.getD f (0, 0)).2 &&
    (es.getD e (0, 0)).2 != (es.getD f (0, 0)).1 && (es.getD e (0, 0)).2 != (es.getD f (0, 0)).2

/-- The number of earlier partners of edge `k`. -/
def numEarlier (es : Array (Nat × Nat)) (k : Nat) : Nat := ((List.range k).filter (nonInc es k)).length

/-! ## The partial augmented graph -/

/-- The id of the crossing vertex of the edges `e` and `f` (`m` edges, `n` vertices). -/
def xId (n m e f : Nat) : Nat := if e < f then n + (e * m + f) else n + (f * m + e)

/-- The id of the subdivision vertex of edge `e` after its `i`-th crossing (0-based). -/
def sId (n m e i : Nat) : Nat := n + m * m + (e * m + i)

/-- The inner nodes `X(e, r₀), S(e, i), X(e, r₁), S(e, i + 1), …, X(e, r_last)` of a path with crossing row `r`. -/
def midIds (n m e : Nat) : List Nat → Nat → List Nat
  | [], _ => []
  | [f], _ => [xId n m e f]
  | f :: g :: rest, i => xId n m e f :: sId n m e i :: midIds n m e (g :: rest) (i + 1)

/-- The nodes of the path of edge `e` with row `r`: closed (`cl`): tail, inner nodes, head; open: tail and inner
nodes, or nothing if `r = []`. -/
def pathIds (n m : Nat) (es : Array (Nat × Nat)) (e : Nat) (r : List Nat) (cl : Bool) : List Nat :=
  if cl then (es.getD e (0, 0)).1 :: (midIds n m e r 0 ++ [(es.getD e (0, 0)).2])
  else if r = [] then [] else (es.getD e (0, 0)).1 :: midIds n m e r 0

/-- Consecutive pairs of a list. -/
def pairs : List Nat → List (Nat × Nat)
  | x :: y :: rest => (x, y) :: pairs (y :: rest)
  | _ => []

/-- The node before the crossing with `f` on the path of edge `e` with row `r`. -/
def nbrB (n m : Nat) (es : Array (Nat × Nat)) (e : Nat) (r : List Nat) (f : Nat) : Nat :=
  if r.idxOf f = 0 then (es.getD e (0, 0)).1 else sId n m e (r.idxOf f - 1)

/-- The node after the crossing with `f` on the path of edge `e` with row `r`, if drawn. -/
def nbrA (n m : Nat) (es : Array (Nat × Nat)) (e : Nat) (r : List Nat) (cl : Bool) (f : Nat) : Option Nat :=
  if r.idxOf f + 1 = r.length then (if cl then some (es.getD e (0, 0)).2 else none)
  else some (sId n m e (r.idxOf f))

/-- The drawn edges of the diamond `a₁ - b₁ - a₂ - b₂ - a₁` (an edge with a missing end is not drawn). -/
def diamondIds (a1 : Nat) (a2 : Option Nat) (b1 : Nat) (b2 : Option Nat) : List (Nat × Nat) :=
  (a1, b1) :: ((match a2 with | some x => [(b1, x)] | none => []) ++
    (match a2, b2 with | some x, some y => [(x, y)] | _, _ => []) ++
    (match b2 with | some y => [(y, a1)] | none => []))

/-- The edges of the partial augmented graph of the state `(k, rows)`: the paths of the edges `e ≤ k` (closed iff
`e < k`) and the diamonds of their crossings. -/
def edgeIds (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) : List (Nat × Nat) :=
  (List.range (Nat.min (k + 1) es.size)).flatMap fun e =>
    pairs (pathIds n es.size es e (rows.getD e []) (decide (e < k))) ++
    (rows.getD e []).flatMap fun f =>
      if e < f then
        diamondIds (nbrB n es.size es e (rows.getD e []) f)
          (nbrA n es.size es e (rows.getD e []) (decide (e < k)) f)
          (nbrB n es.size es f (rows.getD f []) e) (nbrA n es.size es f (rows.getD f []) (decide (f < k)) e)
      else []

/-- The graph with the vertices `0, …, nv - 1` and the edges of the list `l` (others are dropped). -/
def fromEdges (nv : Nat) (l : List (Nat × Nat)) : AGraph :=
  { nv := nv, adj := l.foldl (fun adj p => adj.modify p.1 (·.push p.2)) (Array.replicate nv #[]) }

/-- The partial augmented graph of the state `(k, rows)`. -/
def stateGraph (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) : AGraph :=
  fromEdges (n + 2 * es.size * es.size) (edgeIds n es k rows)

/-! ## The search tree and its certificate -/

/-- The children of a state `(k, rows)` whose edge `k` has an earlier partner not crossed yet: cross such a partner `f`,
inserting `k` at any position `p` of the row of `f`. -/
def children (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) : List (Array (List Nat)) :=
  (List.range k).flatMap fun f =>
    if nonInc es k f && !(rows.getD k []).contains f then
      (List.range ((rows.getD f []).length + 1)).map fun p =>
        (rows.set! k (rows.getD k [] ++ [f])).set! f ((rows.getD f []).take p ++ k :: (rows.getD f []).drop p)
    else []

/-- Access to the certificate data: the tag at a position (`1`: minor model, `0`: expansion) and the minor model at a
position, each with the next position. -/
structure Reader where
  tag : Nat → Nat × Nat
  cert : Nat → MinorCert × Nat

/-- Check the subtree of the state `(k, rows)`, reading its pre-order certificate from position `pos`; returns the
position after it. -/
def walk (n : Nat) (es : Array (Nat × Nat)) (rd : Reader) : Nat → Nat → Array (List Nat) → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, k, rows, pos =>
    let t := rd.tag pos
    if t.1 = 1 then
      let c := rd.cert t.2
      if checkMinor (stateGraph n es k rows) c.1 then some c.2 else none
    else if t.1 = 0 ∧ k < es.size then
      if (rows.getD k []).length = numEarlier es k then walk n es rd fuel (k + 1) rows t.2
      else (children es k rows).foldl (fun acc r => acc.bind fun p => walk n es rd fuel k r p) (some t.2)
    else none

/-- **The check** of the listing `es` on `n` vertices: the whole search tree from the empty state. -/
def check (n : Nat) (es : Array (Nat × Nat)) (rd : Reader) : Bool :=
  (walk n es rd ((es.size + 1) * (es.size + 1)) 0 (Array.replicate es.size []) 0).isSome

end Thrackle78Core
