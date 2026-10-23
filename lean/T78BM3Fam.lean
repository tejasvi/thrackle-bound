import T78BM3

/-!
# Family models for the BM3 oracle (core Lean, no proof needed)

The children of a state `(k, rows)` that cross the same earlier edge `f` (at the positions `p = 0, …, |row f|`) differ
only along the path of `f`. Contracting the internal vertices of that path (all `X(f, ·)` and `S(f, ·)`, the new
crossing included) to one vertex `C` gives the same graph for every middle position; the end positions differ from it
only at `tail f` / `head f`. `famOrc` takes a `K₅` / `K₃,₃` model of the part common to all children (the middle
contraction without the end-specific edges at `tail f` / `head f`), or else of the whole middle contraction (then the
end children may not fit); ids as in `stateGraph`, `C` written `CID`. `adapt` lifts it to a child: `C` becomes the
path (a chain in its branch set), and the elements and witnesses that used `C` are re-attached to a path vertex
adjacent in that child.
Nothing here is trusted: the walk checks every lifted model, and `none` sends the child to the ordinary oracle.
-/

namespace Thrackle78Core.BM3

/-- The id standing for the contracted path vertex in a family model. -/
def CID : Nat := NILN

/-- The child of `(k, rows)` crossing `f` at position `p` (as in `childrenFP`). -/
def childRows (k f p : Nat) (rows : Array (List Nat)) : Array (List Nat) :=
  let rk := rows.getD k []
  let rf := rows.getD f []
  (rows.set! k (rk ++ [f])).set! f (rf.take p ++ k :: rf.drop p)

/-- Compact ids of the internal vertices of the path of `f` (row `rowF`) from position `i`: crossings from `xc`,
subdivision vertices at `sb + i`. -/
partial def pathCompact (m f sb : Nat) (xc : Array Nat) (rowF : List Nat) (i : Nat) (acc : Array Nat) : Array Nat :=
  match rowF with
  | [] => acc
  | g :: rest =>
    let acc := acc.push xc[(if f < g then f * m + g else g * m + f)]!
    match rest with
    | [] => acc
    | _ => pathCompact m f sb xc rest (i + 1) (acc.push (sb + i))

/-- Mark the path vertices. -/
partial def markP (P : Array Nat) (i : Nat) (inP : Array Bool) : Array Bool :=
  if i ≥ P.size then inP else markP P (i + 1) (inP.set! P[i]! true)

/-- Contracted ids: non-path vertices numbered in order, the path vertices all `c0`; the `stateGraph` ids of the
contracted vertices in `hg` (`CID` for `c0`). -/
partial def phiLoop (inP : Array Bool) (gid : Array Nat) (v nv c0 : Nat) (phi hg : Array Nat) : Array Nat × Array Nat :=
  if v ≥ nv then (phi, hg.push CID)
  else if inP[v]! then phiLoop inP gid (v + 1) nv c0 (phi.set! v c0) hg
  else phiLoop inP gid (v + 1) nv c0 (phi.set! v hg.size) (hg.push gid[v]!)

/-- The contracted edges (loops dropped, parallel edges at `c0` merged, `mk` marks the neighbours of `c0`). -/
partial def contrEdges (buf phi : Array Nat) (c0 i iEnd : Nat) (mk : Array Bool) (E : Array Nat) : Array Nat :=
  if i ≥ iEnd then E
  else
    let a := phi[buf[i]!]!
    let b := phi[buf[i + 1]!]!
    if a == b then contrEdges buf phi c0 (i + 2) iEnd mk E
    else if a == c0 || b == c0 then
      let w := if a == c0 then b else a
      if mk[w]! then contrEdges buf phi c0 (i + 2) iEnd mk E
      else contrEdges buf phi c0 (i + 2) iEnd (mk.set! w true) ((E.push a).push b)
    else contrEdges buf phi c0 (i + 2) iEnd mk ((E.push a).push b)

/-- The edge pairs of `E` from `i` on that are not in `bad` (either orientation). -/
partial def dropEdges (E : Array Nat) (bad : List (Nat × Nat)) (i : Nat) (acc : Array Nat) : Array Nat :=
  if i + 1 ≥ E.size then acc
  else
    let a := E[i]!
    let b := E[i + 1]!
    if bad.any (fun xy => (xy.1 == a && xy.2 == b) || (xy.1 == b && xy.2 == a)) then dropEdges E bad (i + 2) acc
    else dropEdges E bad (i + 2) ((acc.push a).push b)

/-- The family hint: `(k, f, model of the contracted middle child)`. -/
abbrev FamHint := Nat × Nat × Option MinorCert

/-- **The family oracle**: a model of the middle child of `(k, rows)` crossing `f` with the path of `f` contracted
(`none` if that graph is planar or the isolation fails). -/
def famOrc (n : Nat) (es : Array (Nat × Nat)) (k : Nat) (rows : Array (List Nat)) (f : Nat) : FamHint :=
  let m := es.size
  let lf := (rows.getD f []).length
  let rows' := childRows k f (if lf ≥ 2 then 1 else 0) rows
  let ke := Nat.min (k + 1) m
  let t : RowTabs := scanRows n m rows' (Array.replicate (m * m) NILN) (Array.range n) (Array.replicate (m * m) 0)
    (Array.replicate m 0) 0 ke 0 (rows'.getD 0 [])
  let sg := sLoop n m t.lens (Array.replicate m 0) t.gid 0 ke
  let gid := sg.2
  let nv := gid.size
  let L := t.lens.foldl (· + ·) 0
  let buf0 := pushZeros (Array.mkEmpty (nv + 2 * ke + 6 * L + 8)) nv
  let buf := edgeLoop n k m es rows' t.xc t.pos t.lens sg.1 buf0 0 ke
  let P := pathCompact m f sg.1[f]! t.xc (rows'.getD f []) 0 #[]
  let inP := markP P 0 (Array.replicate nv false)
  let c0 := nv - P.size
  let ph := phiLoop inP gid 0 nv c0 (Array.replicate nv 0) #[]
  let E0 := contrEdges buf ph.1 c0 nv buf.size (Array.replicate (c0 + 1) false) (Array.mkEmpty (buf.size - nv))
  -- drop the edges that some end child lacks (the diamond edges of tail f / head f at the old first / last crossing,
  -- and their edges to k's node at the new crossing), so that the model fits every child of the family
  let rf := rows.getD f []
  let tf := (es.getD f (0, 0)).1
  let hf := (es.getD f (0, 0)).2
  let hid := fun (sgId : Nat) => match gid.findIdx? (· == sgId) with
    | some c => if inP[c]! then NILN else ph.1[c]!
    | none => NILN
  let nb := fun (g : Nat) => [nbrB n m es g (rows'.getD g []) f] ++
    (match nbrA n m es g (rows'.getD g []) (decide (g < k)) f with | some y => [y] | none => [])
  let rk := rows'.getD k []
  let a1k := if rk.length ≥ 2 then sId n m k (rk.length - 2) else (es.getD k (0, 0)).1
  let bad : List (Nat × Nat) :=
    (match rf.head? with | some g => (nb g).map fun y => (tf, y) | none => []) ++
    (match rf.getLast? with | some g => (nb g).map fun y => (hf, y) | none => []) ++
    (if lf ≥ 2 then [] else [(tf, a1k), (hf, a1k)])
  let badH := bad.map fun xy => (hid xy.1, hid xy.2)
  let E := dropEdges E0 badH 0 (Array.mkEmpty E0.size)
  let ne := E.size / 2
  let r := bmPlanarE #[] (c0 + 1) E 0 ne
  if ne ≥ 9 && !r.2.2 then (k, f, isoMap r ph.2)
  else
    -- the common part is planar: a model of the whole middle contraction still fits the middle children
    let ne0 := E0.size / 2
    let r0 := bmPlanarE r.2.1 (c0 + 1) E0 0 ne0
    if ne0 < 9 || r0.2.2 then (k, f, none) else (k, f, isoMap r0 ph.2)

/-- The first path vertex (index into `P`) adjacent to `v` (`P.size` if none). -/
partial def firstAdj (adj : Nat → Nat → Bool) (P : Array Nat) (v t : Nat) : Nat :=
  if t ≥ P.size then P.size else if hasE adj P[t]! v then t else firstAdj adj P v (t + 1)

/-- The path vertex (index into `P`, the path of `f` in the child `rows'`) that a neighbour `w` of the path is expected
to be adjacent to: for a subdivision vertex of an edge `g`, the crossing `X(f, g)` (at index `2 · pos g`); for the ends
of `f`, the first / last path vertex; for an end of another edge `g`, `X(f, g)` if it is the first / last crossing of
`g`. Then the adjacency is confirmed, and the full scan `firstAdj` is the fallback. -/
def anchorAdj (n : Nat) (es : Array (Nat × Nat)) (k f : Nat) (rows' : Array (List Nat)) (adj : Nat → Nat → Bool)
    (P : Array Nat) (w : Nat) : Nat :=
  let m := es.size
  let rf := rows'.getD f []
  let guess : Nat :=
    if w ≥ n + m * m then
      let g := (w - n - m * m) / m
      if g == f || !rf.contains g then P.size else 2 * rf.idxOf g
    else if w < n then
      if w == (es.getD f (0, 0)).1 then 0
      else if w == (es.getD f (0, 0)).2 then P.size - 1
      else
        match rf.find? (fun g => ((es.getD g (0, 0)).1 == w && (rows'.getD g []).head? == some f) ||
            ((es.getD g (0, 0)).2 == w && g < k && (rows'.getD g []).getLast? == some f)) with
        | some g => 2 * rf.idxOf g
        | none => P.size
    else P.size
  if guess < P.size && hasE adj P[guess]! w then guess else firstAdj adj P w 0

/-- **Lift a family model to a child** (`rows'`, the child's rows; `p` is not needed). -/
def adapt (n : Nat) (es : Array (Nat × Nat)) (h : FamHint) (_p : Nat) (rows' : Array (List Nat)) :
    Option MinorCert := Id.run do
  let (k, f, mc) := h
  let some c := mc | return none
  let m := es.size
  let adj := stateEdge n es k rows'
  let P : Array Nat := (midIds n m f (rows'.getD f []) 0).toArray
  let np := P.size
  -- the branch set holding C, and its position
  let mut u := c.branch.size
  let mut q := 0
  for b in [0:c.branch.size] do
    let B := c.branch[b]!
    for j in [0:B.size] do
      if B[j]!.1 == CID then
        u := b
        q := j
  if u == c.branch.size then return some c
  let B := c.branch[u]!
  let remap := fun (j : Nat) => if j < q then j else j + np - 1
  -- chain order of the path, starting at the vertex adjacent to C's parent
  let t0 := if q == 0 then 0 else anchorAdj n es k f rows' adj P (B[B[q]!.2]!).1
  if t0 ≥ np then return none
  let mut order : Array Nat := #[t0]
  for d in [1:t0 + 1] do order := order.push (t0 - d)
  for t in [t0 + 1:np] do order := order.push t
  let mut posOf : Array Nat := Array.replicate np 0
  for i in [0:np] do posOf := posOf.set! order[i]! (q + i)
  let mut nb : Array (Nat × Nat) := #[]
  for j in [0:q] do
    let e := B[j]!
    nb := nb.push (e.1, if j == 0 then 0 else remap e.2)
  -- the chain: order[0] attached like C, then each step to an adjacent earlier path vertex
  for i in [0:np] do
    let t := order[i]!
    let par := if i == 0 then (if q == 0 then 0 else remap B[q]!.2)
      else if t < t0 then posOf[t + 1]! else posOf[t - 1]!
    nb := nb.push (P[t]!, par)
  for j in [q + 1:B.size] do
    let e := B[j]!
    if e.2 == q then
      let t := anchorAdj n es k f rows' adj P e.1
      if t ≥ np then return none
      nb := nb.push (e.1, posOf[t]!)
    else nb := nb.push (e.1, remap e.2)
  -- witnesses
  let hE := hEdges c.k5
  let mut wit : Array (Nat × Nat) := #[]
  for e2 in [0:c.wit.size] do
    let uu := hE[e2]!
    let ij := c.wit[e2]!
    let mut i1 := ij.1
    let mut j1 := ij.2
    if uu.1 == u then
      if i1 == q then
        let w := (c.branch[uu.2]!)[j1]!.1
        let t := anchorAdj n es k f rows' adj P w
        if t ≥ np then return none
        i1 := posOf[t]!
      else i1 := remap i1
    if uu.2 == u then
      if j1 == q then
        let w := (c.branch[uu.1]!)[ij.1]!.1
        let t := anchorAdj n es k f rows' adj P w
        if t ≥ np then return none
        j1 := posOf[t]!
      else j1 := remap j1
    wit := wit.push (i1, j1)
  return some { c with branch := c.branch.set! u nb, wit := wit }

end Thrackle78Core.BM3
