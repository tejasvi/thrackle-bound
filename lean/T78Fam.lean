import Thrackle78Core
import T78Sym

/-!
# The bitset walk with family hints (core Lean only)

`walkBF` is `walkB` with one more certificate tried at every node before the oracle: a hint passed down from the parent.
At an expanded node, the children that cross the same earlier edge `f` (at the different insertion positions) form a
family; `famOrc k rows f` is evaluated once per family with at least two live children (e.g. a minor model of the
graph with `f`'s path contracted) and `adapt` turns it into each child's hint. Both are untrusted, like the oracle:
every hint is checked by `checkMinorE` against the child's own edge test. `checkBFromListRF`: the batch check with
root-restricted filters and family hints.
-/

namespace Thrackle78Core

/-- The bitsets of a child (as in `walkB`). -/
def childAlive (es : Array (Nat × Nat)) (fs : List FiltB) (alive : List Nat) (k : Nat) (rows : Array (List Nat))
    (c : Nat × Nat × Array (List Nat)) : List Nat :=
  (List.range fs.length).map fun i =>
    alive.getD i 0 &&& stepMask es (fs.getD i ⟨[], [], #[], 0⟩).g (fs.getD i ⟨[], [], #[], 0⟩).ms
      (fs.getD i ⟨[], [], #[], 0⟩).all k c.1 c.2.1 rows

/-- The oracle search with bitset filters and family hints. -/
def walkBF {α : Type} (n : Nat) (es : Array (Nat × Nat)) (fs : List FiltB) (orc : Oracle)
    (famOrc : Nat → Array (List Nat) → Nat → α) (adapt : α → Nat → Array (List Nat) → Option MinorCert) :
    Nat → Nat → Array (List Nat) → List Nat → Option MinorCert → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, k, rows, alive, hint =>
    (List.range fs.length).any (fun i => alive.getD i 0 == 0) ||
    oracleOK n es (fun _ _ => hint) k rows ||
    oracleOK n es orc k rows ||
    (decide (k < es.size) &&
      (if (rows.getD k []).length = numEarlier es k then
         walkBF n es fs orc famOrc adapt fuel (k + 1) rows alive none
       else
         let cs := (childrenFP es k rows).map fun c => (c, childAlive es fs alive k rows c)
         let nlive := fun (f : Nat) =>
           (cs.filter fun ca => ca.1.1 == f && !(List.range fs.length).any (fun i => ca.2.getD i 0 == 0)).length
         let fams := (List.range k).map fun f => if 2 ≤ nlive f then some (famOrc k rows f) else none
         cs.all fun ca =>
           walkBF n es fs orc famOrc adapt fuel k ca.1.2.2 ca.2
             ((fams.getD ca.1.1 none).bind fun fm => adapt fm ca.1.2.1 ca.1.2.2)))

/-- `checkBFromListR` with family hints. -/
def checkBFromListRF {α : Type} (n : Nat) (es : Array (Nat × Nat)) (fs : List Filt) (orc : Oracle)
    (famOrc : Nat → Array (List Nat) → Nat → α) (adapt : α → Nat → Array (List Nat) → Option MinorCert)
    (L : List (Nat × Array (List Nat))) : Bool :=
  L.all fun s =>
    let fs' := fs.map fun φ => restrictFilt φ s.1 s.2
    walkBF n es (fs'.map prepB) orc famOrc adapt ((es.size + 1) * (es.size + 1)) s.1 s.2
      (fs'.map fun φ => allOf φ.sys) none

end Thrackle78Core
