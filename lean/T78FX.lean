import Thrackle78Core
import T78Fam

/-!
# Indexed filters (core Lean only)

A large filter is given by an accessor `sysAt : Nat → List (List Nat)` for its `nsys` systems (the logical filter is
`(List.range nsys).map sysAt`, see `FiltX.toFilt`), sorted into buckets `[bl[b], bl[b+1])` of systems with the same
prefix key `keyOf g K s` (the rows of the H-edges `< K`, restricted to the H-edges `< K`). At a shard root of stage `K`
the systems compatible with the root are among the buckets whose key is the root's key (`keyRoot`), so a batch reads
only those (`FiltX.restrict`), never the whole list. `idxOK` is the one-off check of the buckets (every system lies in
the bucket found for it, with the bucket's key).

The filter tree of an indexed filter: `walkHOX` (the search tree of the reordered listing stopped at level `h`, leaves
checked by a membership test `inS`) and `walkHOXT` (its top, delegating the states of a shard array).
-/

namespace Thrackle78Core

/-- The prefix key of a system: the rows of the H-edges `< K`, restricted to the H-edges `< K`. -/
def keyOf (g : List Nat) (K : Nat) (s : List (List Nat)) : List (List Nat) :=
  (List.range g.length).filterMap fun i =>
    if g.getD i 0 < K then some ((s.getD i []).filter fun j => decide (g.getD j 0 < K)) else none

/-- The prefix key of a state of stage `K`: the H-rows of its H-edges `< K`. -/
def keyRoot (g : List Nat) (K : Nat) (rows : Array (List Nat)) : List (List Nat) :=
  (List.range g.length).filterMap fun i =>
    if g.getD i 0 < K then some (((rows.getD (g.getD i 0) []).filter fun f => g.contains f).map (labOf g)) else none

/-- An indexed filter. -/
structure FiltX where
  g : List Nat
  K : Nat
  nsys : Nat
  sysAt : Nat → List (List Nat)
  bl : Array Nat
  bkeys : Array (List (List Nat))

/-- The logical filter. -/
def FiltX.toFilt (φ : FiltX) : Filt := ⟨φ.g, (List.range φ.nsys).map φ.sysAt⟩

/-- The number of buckets. -/
def FiltX.nb (φ : FiltX) : Nat := φ.bl.size - 1

/-- The systems of bucket `b`. -/
def FiltX.bucket (φ : FiltX) (b : Nat) : List (List (List Nat)) :=
  (List.range (φ.bl.getD (b + 1) 0 - φ.bl.getD b 0)).map fun d => φ.sysAt (φ.bl.getD b 0 + d)

/-- The bucket containing the index `j` (binary search on `bl`; untrusted, checked by `idxOK`). -/
def bsearch (bl : Array Nat) (j : Nat) : Nat :=
  let rec go (lo hi : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => lo
    | fuel + 1 =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if bl.getD mid 0 ≤ j then go mid hi fuel else go lo mid fuel
  go 0 (bl.size - 1) 64

/-- **The one-off check of the buckets**: every system `j` lies in the bucket `b` found for it, and has its key. -/
def FiltX.idxOK (φ : FiltX) : Bool :=
  (List.range φ.nsys).all fun j =>
    let b := bsearch φ.bl j
    decide (b < φ.nb) && decide (φ.bl.getD b 0 ≤ j) && decide (j < φ.bl.getD (b + 1) 0) &&
      keyOf φ.g φ.K (φ.sysAt j) == φ.bkeys.getD b []

/-- The filter restricted to the buckets with the key of the state (stage `K`, open row empty), else to its systems
compatible with the state. -/
def FiltX.restrict (φ : FiltX) (k : Nat) (rows : Array (List Nat)) : Filt :=
  if k == φ.K && (rows.getD k []).isEmpty then
    let κ := keyRoot φ.g k rows
    ⟨φ.g, (List.range φ.nb).flatMap fun b => if φ.bkeys.getD b [] == κ then φ.bucket b else []⟩
  else restrictFilt φ.toFilt k rows

/-- The batch check with indexed filters restricted at each shard root, and family hints. -/
def checkBFromListRX {α : Type} (n : Nat) (es : Array (Nat × Nat)) (fs : List FiltX) (orc : Oracle)
    (famOrc : Nat → Array (List Nat) → Nat → α) (adapt : α → Nat → Array (List Nat) → Option MinorCert)
    (L : List (Nat × Array (List Nat))) : Bool :=
  L.all fun s =>
    let fs' := fs.map fun φ => φ.restrict s.1 s.2
    walkBF n es (fs'.map prepB) orc famOrc adapt ((es.size + 1) * (es.size + 1)) s.1 s.2
      (fs'.map fun φ => allOf φ.sys) none

/-- The search tree of a filter stopped at level `h`, leaves checked by `inS`. -/
def walkHOX (n : Nat) (es : Array (Nat × Nat)) (h : Nat) (inS : List (List Nat) → Bool) (orc : Oracle) :
    Nat → Nat → Array (List Nat) → Bool
  | 0, _, _ => false
  | fuel + 1, k, rows =>
    oracleOK n es orc k rows ||
    (decide (k = h) && decide (rows.getD h [] = []) && inS ((List.range h).map fun e => rows.getD e [])) ||
    (decide (k < h) &&
      (if (rows.getD k []).length = numEarlier es k then walkHOX n es h inS orc fuel (k + 1) rows
       else (children es k rows).all fun r => walkHOX n es h inS orc fuel k r))

/-- The top of the search tree of a filter: the states of the shard array `LA` (at the index proposed by `look`) are
delegated. -/
def walkHOXT (n : Nat) (es : Array (Nat × Nat)) (h : Nat) (inS : List (List Nat) → Bool) (orc : Oracle)
    (LA : Array (Nat × Array (List Nat))) (look : Nat × Array (List Nat) → Nat) :
    Nat → Nat → Array (List Nat) → Bool
  | 0, _, _ => false
  | fuel + 1, k, rows =>
    (decide (look (k, rows) < LA.size) && LA.getD (look (k, rows)) (0, #[]) == (k, rows)) ||
    oracleOK n es orc k rows ||
    (decide (k = h) && decide (rows.getD h [] = []) && inS ((List.range h).map fun e => rows.getD e [])) ||
    (decide (k < h) &&
      (if (rows.getD k []).length = numEarlier es k then walkHOXT n es h inS orc LA look fuel (k + 1) rows
       else (children es k rows).all fun r => walkHOXT n es h inS orc LA look fuel k r))

/-- The membership test of an indexed filter (index proposed by `look`, checked). -/
def FiltX.inS (φ : FiltX) (look : List (List Nat) → Nat) (x : List (List Nat)) : Bool :=
  decide (look x < φ.nsys) && φ.sysAt (look x) == x

/-- The top of the filter tree of an indexed filter (on the reordered listing, with the oracle of that listing). -/
def checkFilterXTop (n : Nat) (es : Array (Nat × Nat)) (φ : FiltX) (look : List (List Nat) → Nat)
    (orcF : Array (Nat × Nat) → Oracle) (LA : Array (Nat × Array (List Nat))) (lookS : Nat × Array (List Nat) → Nat) :
    Bool :=
  φ.toFilt.valid es.size &&
    walkHOXT n (reorder es φ.g) φ.g.length (φ.inS look) (orcF (reorder es φ.g)) LA lookS
      ((es.size + 1) * (es.size + 1)) 0 (Array.replicate es.size [])

/-- A batch of shard states of the filter tree of an indexed filter. -/
def checkFilterXShards (n : Nat) (es : Array (Nat × Nat)) (φ : FiltX) (look : List (List Nat) → Nat)
    (orcF : Array (Nat × Nat) → Oracle) (L : List (Nat × Array (List Nat))) : Bool :=
  L.all fun s =>
    walkHOX n (reorder es φ.g) φ.g.length (φ.inS look) (orcF (reorder es φ.g)) ((es.size + 1) * (es.size + 1)) s.1 s.2

/-- A system in the compact line format (rows separated by `|`, one digit per entry). -/
def parseCompact (ln : String) : List (List Nat) :=
  (ln.splitOn "|").map fun r => r.toList.map fun c => c.toNat - '0'.toNat

/-- The keys of the buckets (from their first systems). -/
def mkBkeys (g : List Nat) (K : Nat) (sysAt : Nat → List (List Nat)) (bl : Array Nat) : Array (List (List Nat)) :=
  ((List.range (bl.size - 1)).map fun b => keyOf g K (sysAt (bl.getD b 0))).toArray

end Thrackle78Core
