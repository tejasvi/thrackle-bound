import Thrackle78Core.OracleWalk

/-!
# Filters with bitsets (core Lean only)

For large filter lists the compatible systems are carried as a bitset (`Nat`, bit `s` for system `s`), updated at every
crossing step by the precedences it creates (as in the C search): when edge `k` crosses `f` at position `p` of the row
of `f` and both are H-edges, `k` comes after the last H-partner before position `p` and before the first one after it
on `f`; on `k`, `f` comes after the last H-partner crossed so far and before every earlier H-partner not crossed yet.
`maskOf S i x y` is the bitset of the systems of `S` in which `x` comes before `y` in row `i`.
-/

namespace Thrackle78Core

/-- `x` comes before `y` in the list. -/
def precB (l : List Nat) (x y : Nat) : Bool :=
  l.contains x && l.contains y && decide (l.idxOf x < l.idxOf y)

/-- The bitset of the indices `lo, …, lo + len - 1` satisfying `p` (bit `j` for index `lo + j`), built by halves. -/
def bitsDC (p : Nat → Bool) (lo : Nat) : Nat → Nat
  | 0 => 0
  | 1 => if p lo then 1 else 0
  | len + 2 =>
    bitsDC p lo ((len + 2) / 2) ||| (bitsDC p (lo + (len + 2) / 2) (len + 2 - (len + 2) / 2) <<< ((len + 2) / 2))
termination_by len => len

/-- The bitset of the systems of `SA` in which `x` comes before `y` in row `i`. -/
def maskOfA (SA : Array (List (List Nat))) (i x y : Nat) : Nat :=
  bitsDC (fun s => precB ((SA.getD s []).getD i []) x y) 0 SA.size

/-- The bitset of the systems of `S` in which `x` comes before `y` in row `i`. -/
def maskOf (S : List (List (List Nat))) (i x y : Nat) : Nat := maskOfA S.toArray i x y

/-- The masks of a filter with `h` H-edges, indexed by `(i * h + x) * h + y`. -/
def masksOf (S : List (List (List Nat))) (h : Nat) : Array Nat :=
  let SA := S.toArray
  ((List.range (h * h * h)).map fun c => maskOfA SA (c / (h * h)) (c / h % h) (c % h)).toArray

/-- The bitset of all systems of `S`. -/
def allOf (S : List (List (List Nat))) : Nat := (1 <<< S.length) - 1

/-- The children of a state with the crossed edge `f` and the insertion position `p` (same order as `children`). -/
def childrenFP (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) :
    List (Nat × Nat × Array (List Nat)) :=
  (List.range k).flatMap fun f =>
    if nonInc es k f && !(rows.getD k []).contains f then
      (List.range ((rows.getD f []).length + 1)).map fun p =>
        (f, p, (rows.set! k (rows.getD k [] ++ [f])).set! f
          ((rows.getD f []).take p ++ k :: (rows.getD f []).drop p))
    else []

/-- The bitset of the precedences created when `k` crosses `f` at position `p` (filter `g` with masks `ms`). -/
def stepMask (es : Array (Nat × Nat)) (g : List Nat) (ms : Array Nat) (all : Nat) (k f p : Nat)
    (rows : Array (List Nat)) : Nat :=
  if g.contains k && g.contains f then
    let h := g.length
    let mk := fun (i x y : Nat) => ms.getD ((i * h + x) * h + y) 0
    let ik := labOf g k
    let iF := labOf g f
    let rf := rows.getD f []
    let rk := rows.getD k []
    let m1 := match ((rf.take p).filter g.contains).getLast? with
      | some a => mk iF (labOf g a) ik
      | none => all
    let m2 := match ((rf.drop p).filter g.contains).head? with
      | some b => mk iF ik (labOf g b)
      | none => all
    let m3 := match (rk.filter g.contains).getLast? with
      | some y => mk ik (labOf g y) iF
      | none => all
    let qs := (List.range k).filter fun q => nonInc es k q && !rk.contains q && q != f && g.contains q
    m1 &&& m2 &&& m3 &&& qs.foldl (fun acc q => acc &&& mk ik iF (labOf g q)) all
  else all

/-- A filter prepared for the bitset walk: H-edges, systems, masks, the full bitset. -/
structure FiltB where
  g : List Nat
  sys : List (List (List Nat))
  ms : Array Nat
  all : Nat

/-- Prepare a filter (the masks are computed here, not read from data). -/
def prepB (φ : Filt) : FiltB := ⟨φ.g, φ.sys, masksOf φ.sys φ.g.length, allOf φ.sys⟩

/-- The oracle search with bitset filters: a node is pruned if a bitset is empty or the oracle's model is accepted. -/
def walkB (n : Nat) (es : Array (Nat × Nat)) (fs : List FiltB) (orc : Oracle) :
    Nat → Nat → Array (List Nat) → List Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, k, rows, alive =>
    (List.range fs.length).any (fun i => alive.getD i 0 == 0) ||
    oracleOK n es orc k rows ||
    (decide (k < es.size) &&
      (if (rows.getD k []).length = numEarlier es k then walkB n es fs orc fuel (k + 1) rows alive
       else (childrenFP es k rows).all fun c =>
         walkB n es fs orc fuel k c.2.2
           ((List.range fs.length).map fun i =>
             alive.getD i 0 &&& stepMask es (fs.getD i ⟨[], [], #[], 0⟩).g (fs.getD i ⟨[], [], #[], 0⟩).ms
               (fs.getD i ⟨[], [], #[], 0⟩).all k c.1 c.2.1 rows)))

/-- The bitset of the indices `s < N` with `p s`. -/
def bitsOf (p : Nat → Bool) (N : Nat) : Nat := bitsDC p 0 N

/-- The bitset of the systems of a filter compatible with the state `(k, rows)`. -/
def compatMask (φ : Filt) (k : Nat) (rows : Array (List Nat)) : Nat :=
  let SA := φ.sys.toArray
  bitsOf (fun s => compat φ.g (SA.getD s []) k rows) SA.size

/-- The oracle search with bitset filters from the state `(k, rows)`, starting from the compatible systems. -/
def checkBFrom (n : Nat) (es : Array (Nat × Nat)) (fs : List Filt) (orc : Oracle) (k : Nat)
    (rows : Array (List Nat)) : Bool :=
  walkB n es (fs.map prepB) orc ((es.size + 1) * (es.size + 1)) k rows (fs.map fun φ => compatMask φ k rows)

/-- **The oracle search with bitset filters**: every filter tree (with the oracle), and the main search. -/
def checkB (n : Nat) (es : Array (Nat × Nat)) (fs : List (Filt × (List (List Nat) → Nat)))
    (orcF : Array (Nat × Nat) → Oracle) : Bool :=
  fs.all (fun φl => checkFilterO n es φl.1 φl.2 orcF) &&
    checkBFrom n es (fs.map Prod.fst) (orcF es) 0 (Array.replicate es.size [])

end Thrackle78Core

namespace Thrackle78Core

/-- The oracle search with bitset filters from every state of the list `L` (the masks are computed once). -/
def checkBFromList (n : Nat) (es : Array (Nat × Nat)) (fs : List Filt) (orc : Oracle)
    (L : List (Nat × Array (List Nat))) : Bool :=
  let fbs := fs.map prepB
  L.all fun s => walkB n es fbs orc ((es.size + 1) * (es.size + 1)) s.1 s.2 (fs.map fun φ => compatMask φ s.1 s.2)

/-- **The oracle search with bitset filters whose trees are certified by data** (as in `checkF`). -/
def checkBD (n : Nat) (es : Array (Nat × Nat)) (fs : List (Filt × ReaderX)) (orc : Oracle) : Bool :=
  fs.all (fun φr => checkFilter n es φr.1 φr.2) &&
    checkBFrom n es (fs.map Prod.fst) orc 0 (Array.replicate es.size [])

end Thrackle78Core

namespace Thrackle78Core

/-- The bitset oracle search where a state of the shard array `LA` (found at the index proposed by `look`) is
delegated: the top of a sharded search, pruning by filters and the oracle as the shards do. -/
def walkBS (n : Nat) (es : Array (Nat × Nat)) (fs : List FiltB) (orc : Oracle) (LA : Array (Nat × Array (List Nat)))
    (look : Nat × Array (List Nat) → Nat) : Nat → Nat → Array (List Nat) → List Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, k, rows, alive =>
    (decide (look (k, rows) < LA.size) && LA.getD (look (k, rows)) (0, #[]) == (k, rows)) ||
    (List.range fs.length).any (fun i => alive.getD i 0 == 0) ||
    oracleOK n es orc k rows ||
    (decide (k < es.size) &&
      (if (rows.getD k []).length = numEarlier es k then walkBS n es fs orc LA look fuel (k + 1) rows alive
       else (childrenFP es k rows).all fun c =>
         walkBS n es fs orc LA look fuel k c.2.2
           ((List.range fs.length).map fun i =>
             alive.getD i 0 &&& stepMask es (fs.getD i ⟨[], [], #[], 0⟩).g (fs.getD i ⟨[], [], #[], 0⟩).ms
               (fs.getD i ⟨[], [], #[], 0⟩).all k c.1 c.2.1 rows)))

/-- The top of the sharded search from the root (full bitsets at the root). -/
def checkTop (n : Nat) (es : Array (Nat × Nat)) (fs : List Filt) (orc : Oracle) (LA : Array (Nat × Array (List Nat)))
    (look : Nat × Array (List Nat) → Nat) : Bool :=
  walkBS n es (fs.map prepB) orc LA look ((es.size + 1) * (es.size + 1)) 0 (Array.replicate es.size [])
    (fs.map fun φ => compatMask φ 0 (Array.replicate es.size []))

end Thrackle78Core
