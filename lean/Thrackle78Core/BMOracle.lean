import Thrackle78Core.BM
import Thrackle78Core.OracleWalk

/-!
# The BM oracle (core Lean)

`bmOracleKR n es k rows`: the partial augmented graph of the state `(k, rows)` on compact vertex ids (`buildKR`), the
Boyer–Myrvold test, and on a nonplanar graph the isolated `K₅` / `K₃,₃` minor model with the `stateGraph` vertex ids
(`O v = v`, `X(e, f) = n + e * m + f` for `e < f`, `S(e, i) = n + m * m + e * m + i`); `none` on a planar graph or if
the isolation fails. `bmOrcKR n es` is the same as an `Oracle` (`Thrackle78Core.OracleWalk`). Nothing here is trusted:
the walk checks every model with `checkMinorE`.
-/

namespace Thrackle78Core.BM

/-! ## The partial augmented graph on compact ids, straight from the state -/

/-- Add the edge `(a, b)`: edges are pairs from position `nv` of `buf`; `buf[x]` (`x < nv`) has bit `u` set when the
edge `(u, x)` with an original vertex `u` is present (canonical: `u < x` if both are original). Only edges at an original
vertex can be parallel (crossings appear once per pair), so these are the only ones checked. -/
@[inline] def addE (n : Nat) (buf : Array Nat) (a b : Nat) : Array Nat :=
  if a < n || b < n then
    let u := if a < n && (b ≥ n || a < b) then a else b
    let x := if a < n && (b ≥ n || a < b) then b else a
    let mk := buf[x]!
    if (mk >>> u) &&& 1 == 1 then buf
    else ((buf.set! x (mk ||| (1 <<< u))).push a).push b
  else (buf.push a).push b

/-- The path edges of edge `e` from the node `prev`, for the remaining row `row` (crossing ids from `xc`, next
subdivision id `s`), closed at `hd` if `cl`. -/
partial def pathLoop (n m e : Nat) (xc : Array Nat) (buf : Array Nat) (row : List Nat) (prev s : Nat) (cl : Bool)
    (hd : Nat) : Array Nat :=
  match row with
  | [] => buf
  | f :: rest =>
    let x := xc[(if e < f then e * m + f else f * m + e)]!
    let buf := addE n buf prev x
    match rest with
    | [] => if cl then addE n buf x hd else buf
    | _ => pathLoop n m e xc (addE n buf x s) rest s (s + 1) cl hd

/-- The diamonds of the crossings of `e` with later edges (`i`: position in the row of `e`). -/
partial def diaLoop (n k e : Nat) (es : Array (Nat × Nat)) (rows : Array (List Nat)) (sBase : Array Nat)
    (buf : Array Nat) (row : List Nat) (i le : Nat) : Array Nat :=
  match row with
  | [] => buf
  | f :: rest =>
    if e < f then
      let te := (es.getD e (0, 0)).1
      let he := (es.getD e (0, 0)).2
      let tf := (es.getD f (0, 0)).1
      let hf := (es.getD f (0, 0)).2
      let rf := rows.getD f []
      let j := rf.idxOf e
      let lf := rf.length
      let a1 := if i == 0 then te else sBase[e]! + i - 1
      let a2 := if i + 1 == le then (if e < k then he else NILN) else sBase[e]! + i
      let b1 := if j == 0 then tf else sBase[f]! + j - 1
      let b2 := if j + 1 == lf then (if f < k then hf else NILN) else sBase[f]! + j
      let buf := addE n buf a1 b1
      let buf := if a2 != NILN then addE n buf b1 a2 else buf
      let buf := if a2 != NILN && b2 != NILN then addE n buf a2 b2 else buf
      let buf := if b2 != NILN then addE n buf b2 a1 else buf
      diaLoop n k e es rows sBase buf rest (i + 1) le
    else diaLoop n k e es rows sBase buf rest (i + 1) le

/-- Crossing ids: `X(e, f)` (`e < f`) in order of `e`, then of the row of `e`. -/
partial def xLoop (n m : Nat) (rows : Array (List Nat)) (xc gid : Array Nat) (e ke : Nat) (row : List Nat) :
    Array Nat × Array Nat :=
  match row with
  | f :: rest =>
    if e < f then xLoop n m rows (xc.set! (e * m + f) gid.size) (gid.push (n + (e * m + f))) e ke rest
    else xLoop n m rows xc gid e ke rest
  | [] => if e + 1 < ke then xLoop n m rows xc gid (e + 1) ke (rows.getD (e + 1) []) else (xc, gid)

/-- Subdivision ids: `S(e, i)` at `sBase[e] + i`. -/
partial def sLoop (n m : Nat) (rows : Array (List Nat)) (sBase gid : Array Nat) (e ke : Nat) : Array Nat × Array Nat :=
  if e ≥ ke then (sBase, gid)
  else
    let le := (rows.getD e []).length
    let sBase := sBase.set! e gid.size
    let gid := (List.range (le - 1)).foldl (fun g i => g.push (n + m * m + (e * m + i))) gid
    sLoop n m rows sBase gid (e + 1) ke

/-- Edges of all drawn paths and diamonds. -/
partial def edgeLoop (n k m : Nat) (es : Array (Nat × Nat)) (rows : Array (List Nat)) (xc sBase : Array Nat)
    (buf : Array Nat) (e ke : Nat) : Array Nat :=
  if e ≥ ke then buf
  else
    let row := rows.getD e []
    let cl := e < k
    let te := (es.getD e (0, 0)).1
    let he := (es.getD e (0, 0)).2
    let buf := if row.isEmpty then (if cl then addE n buf te he else buf)
      else pathLoop n m e xc buf row te sBase[e]! cl he
    let buf := diaLoop n k e es rows sBase buf row 0 row.length
    edgeLoop n k m es rows xc sBase buf (e + 1) ke

/-- The partial augmented graph of `(k, rows)` on compact ids: originals `0 … n-1`, then the crossings, then the
subdivision vertices. Returns the vertex count `nv`, the buffer with the edges as pairs from position `nv` (parallel
edges merged) and the `stateGraph` id of every compact vertex. -/
def buildKR (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) :
    Nat × Array Nat × Array Nat :=
  let m := es.size
  let ke := Nat.min (k + 1) m
  let xg := if ke == 0 then (Array.replicate (m * m) NILN, Array.range n)
    else xLoop n m rows (Array.replicate (m * m) NILN) (Array.range n) 0 ke (rows.getD 0 [])
  let sg := sLoop n m rows (Array.replicate m 0) xg.2 0 ke
  let gid := sg.2
  let nv := gid.size
  let buf := edgeLoop n k m es rows xg.1 sg.1 (Array.replicate nv 0) 0 ke
  (nv, buf, gid)

/-- The minor model of a failed run, with the ids mapped by `gid`. -/
def isoMap (r : Lay × Array UInt32 × Bool) (gid : Array Nat) : Option MinorCert :=
  (bmIsolate r.1 r.2.1).map fun c => { c with branch := c.branch.map fun B => B.map fun p => (gid[p.1]!, p.2) }

/-- The oracle straight from the state: compact graph, planarity test, isolation, ids mapped to `stateGraph` ids. -/
def bmOracleKR (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) : Option MinorCert :=
  let g := buildKR n es k rows
  let nv := g.1
  let ne := (g.2.1.size - nv) / 2
  if ne < 9 then none
  else
    let r := bmPlanarE #[] nv g.2.1 nv ne
    if r.2.2 then none else isoMap r g.2.2

/-- The planarity test of `buildKR`'s graph. -/
def planarKR (g : Nat × Array Nat × Array Nat) : Lay × Array UInt32 × Bool :=
  bmPlanarE #[] g.1 g.2.1 g.1 ((g.2.1.size - g.1) / 2)

/-- The compact-graph oracle as an `Oracle`. -/
def bmOrcKR (n : Nat) (es : Array (Nat × Nat)) : Oracle := fun k rows => bmOracleKR n es k rows

end Thrackle78Core.BM
