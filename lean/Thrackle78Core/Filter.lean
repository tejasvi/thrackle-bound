import Thrackle78Core.Search

/-!
# Filters (core Lean only)

A filter is a sub-listing `H` of the listing `es`, given by the G-edge ids `g` of its edges (in H-order), with the list
`sys` of its complete planar crossing systems (rows of H-edges, entries are H-indices). Its list is certified by the
search tree of the reordered listing `reorder es g` (H-edges first), stopped when the H-edges are complete: there every
leaf is a minor model or a listed system (`L i`). In the main tree, a node may be pruned by a filter (`F φ`): no listed
system of the filter is compatible with the node (`compat`).
-/

namespace Thrackle78Core

/-- A filter: H-edges as G-edge ids (in H-order) and the complete planar systems of `H`. -/
structure Filt where
  g : List Nat
  sys : List (List (List Nat))

/-- The H-index of a G-edge. -/
def labOf (g : List Nat) (f : Nat) : Nat := g.idxOf f

/-- The system `s` of `H` is compatible with the state `(k, rows)`: on every drawn H-edge the drawn H-crossings are in
the order of `s`; on the open edge `k` (if an H-edge) its drawn H-crossings come first among its earlier H-partners. -/
def compat (g : List Nat) (s : List (List Nat)) (k : Nat) (rows : Array (List Nat)) : Bool :=
  (List.range g.length).all fun i =>
    if g.getD i 0 < k then
      ((rows.getD (g.getD i 0) []).filter (fun f => g.contains f)).map (labOf g) ==
        (s.getD i []).filter (fun j => (rows.getD (g.getD i 0) []).contains (g.getD j 0))
    else if g.getD i 0 = k then
      (((rows.getD k []).filter (fun f => g.contains f)).map (labOf g)).isPrefixOf
        ((s.getD i []).filter (fun j => g.getD j 0 < k))
    else true

/-- No duplicates. -/
def nodupB : List Nat → Bool
  | [] => true
  | x :: l => !l.contains x && nodupB l

/-- A filter is valid for a listing with `m` edges: distinct H-edges, all `< m`. -/
def Filt.valid (m : Nat) (φ : Filt) : Bool := nodupB φ.g && φ.g.all (· < m)

/-- The edge order with the H-edges first (in H-order), then the other edges in increasing order. -/
def reorderIdx (m : Nat) (g : List Nat) : List Nat := g ++ (List.range m).filter (fun i => !g.contains i)

/-- The listing reordered with the H-edges first. -/
def reorder (es : Array (Nat × Nat)) (g : List Nat) : Array (Nat × Nat) :=
  ((reorderIdx es.size g).map (fun i => es.getD i (0, 0))).toArray

/-- Certificate access with numbers (the index of a listed system or of a filter). -/
structure ReaderX extends Reader where
  num : Nat → Nat × Nat

/-- The tree walk with listed leaves at level `h` (systems `S`) and filter prunes (filters `fs`). Tags: `1` minor
model, `3` listed system, `4` filter, `0` expansion. -/
def walkG (n : Nat) (es : Array (Nat × Nat)) (h : Nat) (S : List (List (List Nat))) (fs : List Filt)
    (rd : ReaderX) : Nat → Nat → Array (List Nat) → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, k, rows, pos =>
    let t := rd.tag pos
    if t.1 = 1 then
      let c := rd.cert t.2
      if checkMinor (stateGraph n es k rows) c.1 then some c.2 else none
    else if t.1 = 3 then
      let i := rd.num t.2
      if k = h ∧ rows.getD h [] = [] ∧ i.1 < S.length ∧ (List.range h).map (fun e => rows.getD e []) = S.getD i.1 []
      then some i.2 else none
    else if t.1 = 4 then
      let i := rd.num t.2
      if i.1 < fs.length ∧ ((fs.getD i.1 ⟨[], []⟩).sys.all fun s => !compat (fs.getD i.1 ⟨[], []⟩).g s k rows)
      then some i.2 else none
    else if t.1 = 0 ∧ k < h then
      if (rows.getD k []).length = numEarlier es k then walkG n es h S fs rd fuel (k + 1) rows t.2
      else (children es k rows).foldl (fun acc r => acc.bind fun p => walkG n es h S fs rd fuel k r p) (some t.2)
    else none

/-- The tree of filter `φ` (with its data `rd`) certifies its list of systems. -/
def checkFilter (n : Nat) (es : Array (Nat × Nat)) (φ : Filt) (rd : ReaderX) : Bool :=
  φ.valid es.size &&
    (walkG n (reorder es φ.g) φ.g.length φ.sys [] rd ((es.size + 1) * (es.size + 1)) 0
      (Array.replicate es.size []) 0).isSome

/-- **The check with filters**: every filter tree and the main tree. -/
def checkF (n : Nat) (es : Array (Nat × Nat)) (fs : List (Filt × ReaderX)) (rd : ReaderX) : Bool :=
  fs.all (fun φr => checkFilter n es φr.1 φr.2) &&
    (walkG n es es.size [] (fs.map Prod.fst) rd ((es.size + 1) * (es.size + 1)) 0 (Array.replicate es.size []) 0).isSome

end Thrackle78Core
