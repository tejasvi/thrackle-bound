import Thrackle78Core.Search

/-!
# The search with a certificate finder, and sharding (core Lean only)

`walkN` runs the search tree itself: a node is pruned when the minor model proposed by `find` (any function, e.g. an
untrusted Kuratowski extractor) is accepted by `checkMinor`; otherwise it is expanded, and leaves must be pruned.
`walkS` expands the top of the tree down to a list `L` of shard roots (each shard is checked separately).
-/

namespace Thrackle78Core

/-- The search from the state `(k, rows)` with the certificate finder `find`. -/
def walkN (n : Nat) (es : Array (Nat × Nat)) (find : Nat → Array (List Nat) → Option MinorCert) :
    Nat → Nat → Array (List Nat) → Bool
  | 0, _, _ => false
  | fuel + 1, k, rows =>
    (match find k rows with
      | some c => checkMinor (stateGraph n es k rows) c
      | none => false) ||
    (decide (k < es.size) &&
      (if (rows.getD k []).length = numEarlier es k then walkN n es find fuel (k + 1) rows
       else (children es k rows).all fun r => walkN n es find fuel k r))

/-- The full search with the certificate finder. -/
def checkN (n : Nat) (es : Array (Nat × Nat)) (find : Nat → Array (List Nat) → Option MinorCert) : Bool :=
  walkN n es find ((es.size + 1) * (es.size + 1)) 0 (Array.replicate es.size [])

/-- The top of the tree, expanded down to the shard roots `L` (depth at most `d`). -/
def walkS (es : Array (Nat × Nat)) (L : List (Nat × Array (List Nat))) : Nat → Nat → Array (List Nat) → Bool
  | 0, k, rows => L.contains (k, rows)
  | d + 1, k, rows =>
    L.contains (k, rows) ||
    (decide (k < es.size) &&
      (if (rows.getD k []).length = numEarlier es k then walkS es L d (k + 1) rows
       else (children es k rows).all fun r => walkS es L d k r))

end Thrackle78Core

namespace Thrackle78Core

/-- The states at depth `d` of the search tree from `(k, rows)` (no pruning), in pre-order; leaves (`k = m`) above
depth `d` are included. Untrusted helper for choosing shard roots. -/
def cutStates (es : Array (Nat × Nat)) : Nat → Nat → Array (List Nat) → List (Nat × Array (List Nat))
  | 0, k, rows => [(k, rows)]
  | d + 1, k, rows =>
    if k < es.size then
      if (rows.getD k []).length = numEarlier es k then cutStates es d (k + 1) rows
      else (children es k rows).flatMap fun r => cutStates es d k r
    else [(k, rows)]

end Thrackle78Core
