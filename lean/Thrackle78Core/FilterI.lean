import Thrackle78Core.Filter

/-!
# Filters with incremental compatible sets (core Lean only)

`walkI` carries, for every filter, the list of its systems not yet found incompatible; at each node the lists are
filtered by `compat`, and a filter prune (`F φ`) needs the filtered list of `φ` to be empty. Same certificates as
`walkG`.
-/

namespace Thrackle78Core

/-- The compatible sets at the node `(k, rows)`, from the parent's. -/
def aliveAt (fs : List Filt) (alive : List (List (List (List Nat)))) (k : Nat) (rows : Array (List Nat)) :
    List (List (List (List Nat))) :=
  (List.range fs.length).map fun i =>
    (alive.getD i []).filter fun s => compat (fs.getD i ⟨[], []⟩).g s k rows

/-- The tree walk with listed leaves and filter prunes, carrying the compatible sets. -/
def walkI (n : Nat) (es : Array (Nat × Nat)) (h : Nat) (S : List (List (List Nat))) (fs : List Filt)
    (rd : ReaderX) : Nat → Nat → Array (List Nat) → List (List (List (List Nat))) → Nat → Option Nat
  | 0, _, _, _, _ => none
  | fuel + 1, k, rows, alive, pos =>
    let al := aliveAt fs alive k rows
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
      if i.1 < fs.length ∧ al.getD i.1 [] = [] then some i.2 else none
    else if t.1 = 0 ∧ k < h then
      if (rows.getD k []).length = numEarlier es k then walkI n es h S fs rd fuel (k + 1) rows al t.2
      else (children es k rows).foldl (fun acc r => acc.bind fun p => walkI n es h S fs rd fuel k r al p)
        (some t.2)
    else none

/-- **The check with filters**, main tree with incremental compatible sets. -/
def checkI (n : Nat) (es : Array (Nat × Nat)) (fs : List (Filt × ReaderX)) (rd : ReaderX) : Bool :=
  fs.all (fun φr => checkFilter n es φr.1 φr.2) &&
    (walkI n es es.size [] (fs.map Prod.fst) rd ((es.size + 1) * (es.size + 1)) 0 (Array.replicate es.size [])
      (fs.map (fun φr => φr.1.sys)) 0).isSome

end Thrackle78Core
