import Thrackle78Core
import T78Sym
import T78FX

/-!
# The filter tree of an indexed filter with family hints (core Lean only)

`walkHOXF` is `walkHOX` with the family hints of `walkBF`: at an expanded node the children crossing the same earlier
edge `f` form a family, `famOrc k rows f` is evaluated once per family with at least two children and `adapt` turns it
into each child's hint. Hints are untrusted, like the oracle: each is checked by `checkMinorE` against the child's own
edge test. `checkFilterXShardsF`: the shard check of `checkFilterXShards` with family hints.

`symSkipL K R syms`: `symSkip` for several edge maps (with their flips): a node is skipped if its restriction to `R` is
larger than its image under one of them. `FiltX.topFilt`: the bucket keys of an indexed filter as a filter on its first
H-edges (for the top tree of a search whose batches use the indexed filter).
-/

namespace Thrackle78Core

/-- The search tree of a filter stopped at level `h`, leaves checked by `inS`, with family hints. -/
def walkHOXF {α : Type} (n : Nat) (es : Array (Nat × Nat)) (h : Nat) (inS : List (List Nat) → Bool) (orc : Oracle)
    (famOrc : Nat → Array (List Nat) → Nat → α) (adapt : α → Nat → Array (List Nat) → Option MinorCert) :
    Nat → Nat → Array (List Nat) → Option MinorCert → Bool
  | 0, _, _, _ => false
  | fuel + 1, k, rows, hint =>
    oracleOK n es (fun _ _ => hint) k rows ||
    oracleOK n es orc k rows ||
    (decide (k = h) && decide (rows.getD h [] = []) && inS ((List.range h).map fun e => rows.getD e [])) ||
    (decide (k < h) &&
      (if (rows.getD k []).length = numEarlier es k then
         walkHOXF n es h inS orc famOrc adapt fuel (k + 1) rows none
       else
         let cs := childrenFP es k rows
         let fams := (List.range k).map fun f =>
           if 2 ≤ (cs.filter fun c => c.1 == f).length then some (famOrc k rows f) else none
         cs.all fun c =>
           walkHOXF n es h inS orc famOrc adapt fuel k c.2.2 ((fams.getD c.1 none).bind fun fm => adapt fm c.2.1 c.2.2)))

/-- A batch of shard states of the filter tree of an indexed filter, with family hints. -/
def checkFilterXShardsF {α : Type} (n : Nat) (es : Array (Nat × Nat)) (φ : FiltX) (look : List (List Nat) → Nat)
    (orcF : Array (Nat × Nat) → Oracle) (famOrcF : Array (Nat × Nat) → Nat → Array (List Nat) → Nat → α)
    (adaptF : Array (Nat × Nat) → α → Nat → Array (List Nat) → Option MinorCert)
    (L : List (Nat × Array (List Nat))) : Bool :=
  L.all fun s =>
    walkHOXF n (reorder es φ.g) φ.g.length (φ.inS look) (orcF (reorder es φ.g)) (famOrcF (reorder es φ.g))
      (adaptF (reorder es φ.g)) ((es.size + 1) * (es.size + 1)) s.1 s.2 none

/-- Skip the nodes at stage `K` or later whose restriction to `R` is not canonical for one of the edge maps `syms`. -/
def symSkipL (K : Nat) (R : List Nat) (syms : List ((Nat → Nat) × (Nat → Bool))) (k : Nat) (rows : Array (List Nat)) :
    Bool :=
  syms.any fun s => symSkip K R s.1 s.2 k rows

/-- The top filter of an indexed filter: its bucket keys, as a filter on its first `j` H-edges. -/
def FiltX.topFilt (φ : FiltX) (j : Nat) : Filt := ⟨φ.g.take j, (List.range φ.nb).map fun b => φ.bkeys.getD b []⟩

end Thrackle78Core
