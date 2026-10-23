import Thrackle78Core.FilterI
import Thrackle78Core.StateEdge

/-!
# The search with a certificate oracle and incremental filters (core Lean only)

`Oracle`: any function proposing a minor model for the partial augmented graph of the state `(k, rows)` (e.g. an
untrusted Kuratowski extractor); every proposal is verified by `checkMinorE` against the edge test `stateEdge` of the
state (no graph is built).

* `walkIO`: the main search; a node is pruned if some filter has no compatible system left, or if the oracle's model is
  accepted; otherwise it is expanded (leaves must be pruned).
* `walkHO`: the search tree of a filter (on the reordered listing), stopped at level `h`, where the rows must be the
  listed system at the index proposed by `look` (also untrusted: the equality is checked).
* `checkIO`, `checkIOFrom` (from a shard root, with fresh compatible sets).
-/

namespace Thrackle78Core

/-- A certificate oracle: a proposed minor model for the partial augmented graph of the state `(k, rows)`. -/
abbrev Oracle := Nat → Array (List Nat) → Option MinorCert

/-- The oracle proposes a model of the partial augmented graph that is accepted. -/
def oracleOK (n : Nat) (es : Array (Nat × Nat)) (orc : Oracle) (k : Nat) (rows : Array (List Nat)) : Bool :=
  match orc k rows with
  | some c => checkMinorE (n + 2 * es.size * es.size) (stateEdge n es k rows) c
  | none => false

/-- The main search with oracle and incremental filters. -/
def walkIO (n : Nat) (es : Array (Nat × Nat)) (fs : List Filt) (orc : Oracle) :
    Nat → Nat → Array (List Nat) → List (List (List (List Nat))) → Bool
  | 0, _, _, _ => false
  | fuel + 1, k, rows, alive =>
    (List.range fs.length).any (fun i => ((aliveAt fs alive k rows).getD i []).isEmpty) ||
    oracleOK n es orc k rows ||
    (decide (k < es.size) &&
      (if (rows.getD k []).length = numEarlier es k then
        walkIO n es fs orc fuel (k + 1) rows (aliveAt fs alive k rows)
       else (children es k rows).all fun r => walkIO n es fs orc fuel k r (aliveAt fs alive k rows)))

/-- The search tree of a filter with oracle, listed systems at level `h` (index proposed by `look`). -/
def walkHO (n : Nat) (es : Array (Nat × Nat)) (h : Nat) (S : Array (List (List Nat)))
    (look : List (List Nat) → Nat) (orc : Oracle) : Nat → Nat → Array (List Nat) → Bool
  | 0, _, _ => false
  | fuel + 1, k, rows =>
    oracleOK n es orc k rows ||
    (decide (k = h) && decide (rows.getD h [] = []) &&
      decide (look ((List.range h).map (fun e => rows.getD e [])) < S.size) &&
      decide (S.getD (look ((List.range h).map (fun e => rows.getD e []))) [] =
        (List.range h).map (fun e => rows.getD e []))) ||
    (decide (k < h) &&
      (if (rows.getD k []).length = numEarlier es k then walkHO n es h S look orc fuel (k + 1) rows
       else (children es k rows).all fun r => walkHO n es h S look orc fuel k r))

/-- The tree of filter `φ` with an oracle for the reordered listing (`orcF` gives the oracle of a listing). -/
def checkFilterO (n : Nat) (es : Array (Nat × Nat)) (φ : Filt) (look : List (List Nat) → Nat)
    (orcF : Array (Nat × Nat) → Oracle) : Bool :=
  φ.valid es.size &&
    walkHO n (reorder es φ.g) φ.g.length φ.sys.toArray look (orcF (reorder es φ.g))
      ((es.size + 1) * (es.size + 1)) 0
      (Array.replicate es.size [])

/-- The search from the state `(k, rows)` with fresh compatible sets. -/
def checkIOFrom (n : Nat) (es : Array (Nat × Nat)) (fs : List Filt) (orc : Oracle) (k : Nat)
    (rows : Array (List Nat)) : Bool :=
  walkIO n es fs orc ((es.size + 1) * (es.size + 1)) k rows (fs.map (·.sys))

/-- **The search with oracle and filters**: every filter tree, and the main search from the root. -/
def checkIO (n : Nat) (es : Array (Nat × Nat)) (fs : List (Filt × (List (List Nat) → Nat)))
    (orcF : Array (Nat × Nat) → Oracle) : Bool :=
  fs.all (fun φl => checkFilterO n es φl.1 φl.2 orcF) &&
    checkIOFrom n es (fs.map Prod.fst) (orcF es) 0 (Array.replicate es.size [])

end Thrackle78Core
