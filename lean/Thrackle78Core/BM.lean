import Thrackle78Core.Search

/-!
# Boyer–Myrvold planarity and Kuratowski isolation (core Lean, no proof needed)

A transliteration of the C program `bm.c` of the search program (edge-addition planarity, Boyer–Myrvold, JGAA 8(3) 2004,
and its key-point isolator producing a `K₅` / `K₃,₃` minor model), with a faster minimization step. It is used only as
an oracle: every minor model it returns is verified by the checker, so nothing here is trusted.

All integer state of the planarity test lives in one flat `Array UInt32` (`mem`, C-style offsets from `Lay`, unboxed
arithmetic), so that every update is in place; `NIL` plays the role of the C value `-1`. Real vertices `0, …, n - 1` of the embedding are DFS indices; the virtual
root vertex `n + c` is the copy of `parent(c)` in the biconnected component whose root edge goes to the child `c`.
Arc signs are stored as `1` (`+1`) and `0` (`-1`).
-/

namespace Thrackle78Core.BM

/-- The C value `-1`. -/
def NIL : UInt32 := 1073741824

/-- `NIL` as a natural number (isolation code). -/
def NILN : Nat := 1073741824

/-- Offsets of the arrays in `mem`. Scalar slots: `0` arc count, `1` current vertex, `2` stack pointer,
`3` failing vertex. -/
structure Lay where
  n : UInt32
  m : UInt32
  iadjStart : UInt32
  iadj : UInt32
  dfi : UInt32
  vert : UInt32
  par : UInt32
  leastAnc : UInt32
  lowpt : UInt32
  szt : UInt32
  first : UInt32
  last : UInt32
  anb : UInt32
  atwin : UInt32
  aprev : UInt32
  anext : UInt32
  asign : UInt32
  visited : UInt32
  bflag : UInt32
  prHead : UInt32
  prTail : UInt32
  prNext : UInt32
  prPrev : UInt32
  scHead : UInt32
  scTail : UInt32
  scNext : UInt32
  scPrev : UInt32
  stk : UInt32
  kStart : UInt32
  kList : UInt32
  bStart : UInt32
  bList : UInt32
  size : UInt32

def mkLay (n m : Nat) : Lay :=
  let narc := 2 * m + 2
  let iadjStart := 8
  let iadj := iadjStart + n + 1
  let dfi := iadj + 2 * m
  let vert := dfi + n
  let par := vert + n
  let leastAnc := par + n
  let lowpt := leastAnc + n
  let szt := lowpt + n
  let first := szt + n
  let last := first + 2 * n
  let anb := last + 2 * n
  let atwin := anb + narc
  let aprev := atwin + narc
  let anext := aprev + narc
  let asign := anext + narc
  let visited := asign + narc
  let bflag := visited + 2 * n
  let prHead := bflag + n
  let prTail := prHead + n
  let prNext := prTail + n
  let prPrev := prNext + 2 * n
  let scHead := prPrev + 2 * n
  let scTail := scHead + n
  let scNext := scTail + n
  let scPrev := scNext + n
  let stk := scPrev + n
  let kStart := stk + 4 * n + 8
  let kList := kStart + n + 1
  let bStart := kList + n
  let bList := bStart + n + 1
  { n := n.toUInt32, m := m.toUInt32, iadjStart := iadjStart.toUInt32, iadj := iadj.toUInt32, dfi := dfi.toUInt32,
    vert := vert.toUInt32, par := par.toUInt32, leastAnc := leastAnc.toUInt32, lowpt := lowpt.toUInt32,
    szt := szt.toUInt32, first := first.toUInt32, last := last.toUInt32, anb := anb.toUInt32, atwin := atwin.toUInt32,
    aprev := aprev.toUInt32, anext := anext.toUInt32, asign := asign.toUInt32, visited := visited.toUInt32,
    bflag := bflag.toUInt32, prHead := prHead.toUInt32, prTail := prTail.toUInt32, prNext := prNext.toUInt32,
    prPrev := prPrev.toUInt32, scHead := scHead.toUInt32, scTail := scTail.toUInt32, scNext := scNext.toUInt32,
    scPrev := scPrev.toUInt32, stk := stk.toUInt32, kStart := kStart.toUInt32, kList := kList.toUInt32,
    bStart := bStart.toUInt32, bList := bList.toUInt32, size := (bList + m + 2).toUInt32 }

@[inline] def rd (mem : Array UInt32) (i : UInt32) : UInt32 := mem[i.toNat]!
@[inline] def wr (mem : Array UInt32) (i v : UInt32) : Array UInt32 := mem.set! i.toNat v

/-! ## The embedding structure -/

@[inline] def getLink (L : Lay) (mem : Array UInt32) (x i : UInt32) : UInt32 :=
  if i == 1 then rd mem (L.last + x) else rd mem (L.first + x)

def insertArc (L : Lay) (mem : Array UInt32) (x a e : UInt32) : Array UInt32 :=
  if e == 0 then
    let f := rd mem (L.first + x)
    let mem := wr mem (L.aprev + a) NIL
    let mem := wr mem (L.anext + a) f
    let mem := if f != NIL then wr mem (L.aprev + f) a else wr mem (L.last + x) a
    wr mem (L.first + x) a
  else
    let l := rd mem (L.last + x)
    let mem := wr mem (L.anext + a) NIL
    let mem := wr mem (L.aprev + a) l
    let mem := if l != NIL then wr mem (L.anext + l) a else wr mem (L.first + x) a
    wr mem (L.last + x) a

def newEdge (L : Lay) (mem : Array UInt32) (x xe y ye : UInt32) : Array UInt32 :=
  let a := rd mem 0
  let b := a + 1
  let mem := wr mem 0 (a + 2)
  let mem := wr mem (L.anb + a) y
  let mem := wr mem (L.anb + b) x
  let mem := wr mem (L.atwin + a) b
  let mem := wr mem (L.atwin + b) a
  let mem := wr mem (L.asign + a) 1
  let mem := wr mem (L.asign + b) 1
  let mem := insertArc L mem x a xe
  insertArc L mem y b ye

partial def invLoop (L : Lay) (mem : Array UInt32) (a : UInt32) : Array UInt32 :=
  if a == NIL then mem
  else
    let p := rd mem (L.aprev + a)
    let nx := rd mem (L.anext + a)
    invLoop L (wr (wr mem (L.aprev + a) nx) (L.anext + a) p) p

def invertVertex (L : Lay) (mem : Array UInt32) (x : UInt32) : Array UInt32 :=
  let f := rd mem (L.first + x)
  let l := rd mem (L.last + x)
  invLoop L (wr (wr mem (L.first + x) l) (L.last + x) f) l

/-- The next vertex on the external face, exiting `cur` through the link not used to enter it; encoded as
`next * 2 + link` (no allocation). -/
@[inline] def nof (L : Lay) (mem : Array UInt32) (cur pl : UInt32) : UInt32 :=
  let arc := getLink L mem cur (1 ^^^ pl)
  let nx := rd mem (L.anb + arc)
  let f := rd mem (L.first + nx)
  if f != rd mem (L.last + nx) then nx * 2 + (if rd mem (L.atwin + arc) == f then 0 else 1) else nx * 2 + pl

@[inline] def pertinent (L : Lay) (mem : Array UInt32) (w : UInt32) : Bool :=
  rd mem (L.bflag + w) == rd mem 1 || rd mem (L.prHead + w) != NIL

@[inline] def extActive (L : Lay) (mem : Array UInt32) (w : UInt32) : Bool :=
  let cv := rd mem 1
  rd mem (L.leastAnc + w) < cv ||
    (let s := rd mem (L.scHead + w); s != NIL && rd mem (L.lowpt + s) < cv)

@[inline] def intActive (L : Lay) (mem : Array UInt32) (w : UInt32) : Bool := pertinent L mem w && !extActive L mem w
@[inline] def inactive (L : Lay) (mem : Array UInt32) (w : UInt32) : Bool := !pertinent L mem w && !extActive L mem w

def prAppend (L : Lay) (mem : Array UInt32) (z r : UInt32) : Array UInt32 :=
  let t := rd mem (L.prTail + z)
  let mem := wr mem (L.prNext + r) NIL
  let mem := wr mem (L.prPrev + r) t
  let mem := if t != NIL then wr mem (L.prNext + t) r else wr mem (L.prHead + z) r
  wr mem (L.prTail + z) r

def prPrepend (L : Lay) (mem : Array UInt32) (z r : UInt32) : Array UInt32 :=
  let h := rd mem (L.prHead + z)
  let mem := wr mem (L.prPrev + r) NIL
  let mem := wr mem (L.prNext + r) h
  let mem := if h != NIL then wr mem (L.prPrev + h) r else wr mem (L.prTail + z) r
  wr mem (L.prHead + z) r

def prRemove (L : Lay) (mem : Array UInt32) (z r : UInt32) : Array UInt32 :=
  let p := rd mem (L.prPrev + r)
  let nx := rd mem (L.prNext + r)
  let mem := if p != NIL then wr mem (L.prNext + p) nx else wr mem (L.prHead + z) nx
  if nx != NIL then wr mem (L.prPrev + nx) p else wr mem (L.prTail + z) p

def scRemove (L : Lay) (mem : Array UInt32) (z c : UInt32) : Array UInt32 :=
  let p := rd mem (L.scPrev + c)
  let nx := rd mem (L.scNext + c)
  let mem := if p != NIL then wr mem (L.scNext + p) nx else wr mem (L.scHead + z) nx
  if nx != NIL then wr mem (L.scPrev + nx) p else wr mem (L.scTail + z) p

/-! ## Walkup and Walkdown (tail-recursive loops) -/

partial def walkupLoop (L : Lay) (mem : Array UInt32) (v x xin y yin : UInt32) : Array UInt32 :=
  if x == v then mem
  else if rd mem (L.visited + x) == v || rd mem (L.visited + y) == v then mem
  else
    let n := L.n
    let mem := wr (wr mem (L.visited + x) v) (L.visited + y) v
    let zr := if x >= n then x else if y >= n then y else NIL
    if zr != NIL then
      let c := zr - n
      let z := rd mem (L.par + c)
      let mem := if z != v then (if rd mem (L.lowpt + c) < v then prAppend L mem z zr else prPrepend L mem z zr) else mem
      walkupLoop L mem v z 1 z 0
    else
      let px := nof L mem x xin
      let py := nof L mem y yin
      walkupLoop L mem v (px >>> 1) (px &&& 1) (py >>> 1) (py &&& 1)

def walkup (L : Lay) (mem : Array UInt32) (v w : UInt32) : Array UInt32 :=
  walkupLoop L (wr mem (L.bflag + w) v) v w 1 w 0

@[inline] def push (L : Lay) (mem : Array UInt32) (x : UInt32) : Array UInt32 :=
  let sp := rd mem 2
  wr (wr mem (L.stk + sp) x) 2 (sp + 1)

partial def signLoop (L : Lay) (mem : Array UInt32) (a c : UInt32) : Array UInt32 :=
  if a == NIL then mem
  else
    let tw := rd mem (L.atwin + a)
    let nx := rd mem (L.anext + a)
    let mem := if rd mem (L.anb + a) == c then wr (wr mem (L.asign + a) 0) (L.asign + tw) 0 else mem
    signLoop L mem nx c

partial def relinkLoop (L : Lay) (mem : Array UInt32) (a r : UInt32) : Array UInt32 :=
  if a == NIL then mem
  else
    let tw := rd mem (L.atwin + a)
    let nx := rd mem (L.anext + a)
    relinkLoop L (wr mem (L.anb + tw) r) nx r

def mergeTop (L : Lay) (mem : Array UInt32) : Array UInt32 :=
  let n := L.n
  let sp := rd mem 2
  let rcout := rd mem (L.stk + sp - 1)
  let rc := rd mem (L.stk + sp - 2)
  let rin := rd mem (L.stk + sp - 3)
  let r := rd mem (L.stk + sp - 4)
  let mem := wr mem 2 (sp - 4)
  let c := rc - n
  let mem := if rin == rcout then (let mem := invertVertex L mem rc; signLoop L mem (rd mem (L.first + rc)) c)
    else mem
  let mem := relinkLoop L mem (rd mem (L.first + rc)) r
  let mem := prRemove L mem r rc
  let mem := scRemove L mem r c
  let frc := rd mem (L.first + rc)
  let mem :=
    if frc != NIL then
      let lrc := rd mem (L.last + rc)
      if rin == 1 then
        let lr := rd mem (L.last + r)
        wr (wr (wr mem (L.anext + lr) frc) (L.aprev + frc) lr) (L.last + r) lrc
      else
        let fr := rd mem (L.first + r)
        wr (wr (wr mem (L.aprev + fr) lrc) (L.anext + lrc) fr) (L.first + r) frc
    else mem
  wr (wr mem (L.first + rc) NIL) (L.last + rc) NIL

partial def mergeAll (L : Lay) (mem : Array UInt32) : Array UInt32 :=
  if rd mem 2 > 0 then mergeAll L (mergeTop L mem) else mem

/-- The next active vertex on the external face from `r` (encoded `w * 2 + link`). -/
partial def activeNext (L : Lay) (mem : Array UInt32) (r pl : UInt32) : UInt32 :=
  let q := nof L mem r pl
  let w := q >>> 1
  if w < L.n && inactive L mem w then activeNext L mem w (q &&& 1) else q

partial def wdLoop (L : Lay) (mem : Array UInt32) (v R vout w win : UInt32) : Array UInt32 :=
  if w == R then mem
  else
    let n := L.n
    let mem :=
      if w < n && rd mem (L.bflag + w) == v then
        wr (newEdge L (mergeAll L mem) R vout w win) (L.bflag + w) n
      else mem
    if w < n && rd mem (L.prHead + w) != NIL then
      let mem := push L (push L mem w) win
      let wr' := rd mem (L.prHead + w)
      let px := activeNext L mem wr' 1
      let py := activeNext L mem wr' 0
      let x := px >>> 1
      let y := py >>> 1
      let sel := if x < n && intActive L mem x then 0 else if y < n && intActive L mem y then 1
        else if x < n && pertinent L mem x then 0 else 1
      let mem := push L (push L mem wr') sel
      if sel == 0 then wdLoop L mem v R vout x (px &&& 1) else wdLoop L mem v R vout y (py &&& 1)
    else if w < n && inactive L mem w then
      let q := nof L mem w win
      wdLoop L mem v R vout (q >>> 1) (q &&& 1)
    else mem

def walkdown (L : Lay) (mem : Array UInt32) (v R : UInt32) : Array UInt32 :=
  let mem := wr mem 2 0
  let q := nof L mem R 1
  let mem := wdLoop L mem v R 0 (q >>> 1) (q &&& 1)
  if rd mem 2 > 0 then mem
  else
    let q := nof L mem R 0
    wdLoop L mem v R 1 (q >>> 1) (q &&& 1)

/-! ## The planarity test -/

/-- Iterative DFS (stack of vertices at `stk`, adjacency cursors at `stk + n + 1`); stores the next DFI in slot `4`. -/
partial def dfsLoop (L : Lay) (mem : Array UInt32) (top t : UInt32) : Array UInt32 :=
  let co := L.stk + L.n + 1
  let x := rd mem (L.stk + top)
  let k := rd mem (co + top)
  if k < rd mem (L.iadjStart + x + 1) then
    let y := rd mem (L.iadj + k)
    let mem := wr mem (co + top) (k + 1)
    if rd mem (L.dfi + y) == NIL then
      let px := rd mem (L.dfi + x)
      let iy := rd mem (L.iadjStart + y)
      let mem := wr (wr (wr mem (L.dfi + y) t) (L.vert + t) y) (L.par + t) px
      dfsLoop L (wr (wr mem (L.stk + top + 1) y) (co + top + 1) iy) (top + 1) (t + 1)
    else dfsLoop L mem top t
  else if top == 0 then wr mem 4 t
  else dfsLoop L mem (top - 1) t

/-- DFS from every unvisited vertex `s ≥ s0` in increasing order. -/
partial def rootsLoop (L : Lay) (mem : Array UInt32) (s : UInt32) : Array UInt32 :=
  if s ≥ L.n then mem
  else if rd mem (L.dfi + s) != NIL then rootsLoop L mem (s + 1)
  else
    let t := rd mem 4
    let is := rd mem (L.iadjStart + s)
    let mem := wr (wr (wr mem (L.dfi + s) t) (L.vert + t) s) (L.par + t) NIL
    let mem := wr (wr mem L.stk s) (L.stk + L.n + 1) is
    rootsLoop L (dfsLoop L mem 0 (t + 1)) (s + 1)

/-- `mem[off + i] := v` for `lo ≤ i < hi`. -/
partial def fillLoop (mem : Array UInt32) (off i hi v : UInt32) : Array UInt32 :=
  if i ≥ hi then mem else fillLoop (wr mem (off + i) v) off (i + 1) hi v

partial def degLoop (L : Lay) (mem : Array UInt32) (E : Array Nat) (i iEnd : Nat) : Array UInt32 :=
  if i ≥ iEnd then mem
  else
    let u := (E[i]!).toUInt32
    let v := (E[i + 1]!).toUInt32
    let du := rd mem (L.dfi + u)
    let mem := wr mem (L.dfi + u) (du + 1)
    let dv := rd mem (L.dfi + v)
    degLoop L (wr mem (L.dfi + v) (dv + 1)) E (i + 2) iEnd

partial def prefLoop (L : Lay) (mem : Array UInt32) (i : UInt32) : Array UInt32 :=
  if i ≥ L.n then mem
  else
    let st := rd mem (L.iadjStart + i)
    let d := rd mem (L.dfi + i)
    prefLoop L (wr (wr mem (L.iadjStart + i + 1) (st + d)) (L.vert + i) st) (i + 1)

partial def adjLoop (L : Lay) (mem : Array UInt32) (E : Array Nat) (i iEnd : Nat) : Array UInt32 :=
  if i ≥ iEnd then mem
  else
    let u := (E[i]!).toUInt32
    let v := (E[i + 1]!).toUInt32
    let cu := rd mem (L.vert + u)
    let mem := wr (wr mem (L.iadj + cu) v) (L.vert + u) (cu + 1)
    let cv := rd mem (L.vert + v)
    adjLoop L (wr (wr mem (L.iadj + cv) u) (L.vert + v) (cv + 1)) E (i + 2) iEnd

/-- One adjacency pass of the DFI vertex `v` (parent `pv`) from entry `k`: the least ancestor (slot `7`), the children
appended at `kList` (cursor in slot `5`) and the back-edge descendants at `bList` (cursor in slot `6`), in adjacency
order. -/
partial def clsInner (L : Lay) (mem : Array UInt32) (v pv k kEnd : UInt32) : Array UInt32 :=
  if k ≥ kEnd then mem
  else
    let u := rd mem (L.dfi + rd mem (L.iadj + k))
    let la := rd mem 7
    let mem := if u < la && u != pv then wr mem 7 u else mem
    let mem :=
      if u > v then
        if rd mem (L.par + u) == v then
          let kc := rd mem 5
          wr (wr mem (L.kList + kc) u) 5 (kc + 1)
        else
          let bc := rd mem 6
          wr (wr mem (L.bList + bc) u) 6 (bc + 1)
      else mem
    clsInner L mem v pv (k + 1) kEnd

/-- Least ancestors, lowpoint and subtree-size initialization, and the child / back-edge lists of every vertex. -/
partial def clsLoop (L : Lay) (mem : Array UInt32) (v : UInt32) : Array UInt32 :=
  let kc := rd mem 5
  let bc := rd mem 6
  if v ≥ L.n then wr (wr mem (L.kStart + v) kc) (L.bStart + v) bc
  else
    let x := rd mem (L.vert + v)
    let pv := rd mem (L.par + v)
    let k0 := rd mem (L.iadjStart + x)
    let k1 := rd mem (L.iadjStart + x + 1)
    let mem := clsInner L (wr (wr (wr mem 7 v) (L.kStart + v) kc) (L.bStart + v) bc) v pv k0 k1
    let la := rd mem 7
    clsLoop L (wr (wr (wr mem (L.leastAnc + v) la) (L.lowpt + v) la) (L.szt + v) 1) (v + 1)

partial def lowLoop (L : Lay) (mem : Array UInt32) (i : UInt32) : Array UInt32 :=
  if i ≥ L.n then mem
  else
    let v := L.n - 1 - i
    let p := rd mem (L.par + v)
    if p != NIL then
      let lv := rd mem (L.lowpt + v)
      let lp := rd mem (L.lowpt + p)
      let sp := rd mem (L.szt + p)
      let sv := rd mem (L.szt + v)
      let mem := if lv < lp then wr mem (L.lowpt + p) lv else mem
      lowLoop L (wr mem (L.szt + p) (sp + sv)) (i + 1)
    else lowLoop L mem (i + 1)

/-- Bucket the vertices by lowpoint (heads at `visited + l`, links at `visited + n + v`), larger DFI first. -/
partial def bucketLoop (L : Lay) (mem : Array UInt32) (i : UInt32) : Array UInt32 :=
  if i ≥ L.n then mem
  else
    let v := L.n - 1 - i
    let l := rd mem (L.lowpt + v)
    let h := rd mem (L.visited + l)
    bucketLoop L (wr (wr mem (L.visited + L.n + v) h) (L.visited + l) v) (i + 1)

partial def chainLoop (L : Lay) (mem : Array UInt32) (c : UInt32) : Array UInt32 :=
  if c == NIL then mem
  else
    let p := rd mem (L.par + c)
    let nx := rd mem (L.visited + L.n + c)
    if p != NIL then
      let tl := rd mem (L.scTail + p)
      let mem := wr (wr mem (L.scNext + c) NIL) (L.scPrev + c) tl
      let mem := if tl != NIL then wr mem (L.scNext + tl) c else wr mem (L.scHead + p) c
      chainLoop L (wr mem (L.scTail + p) c) nx
    else chainLoop L mem nx

/-- Separated child lists in increasing lowpoint order. -/
partial def scLoop (L : Lay) (mem : Array UInt32) (l : UInt32) : Array UInt32 :=
  if l ≥ L.n then mem
  else
    let h := rd mem (L.visited + l)
    scLoop L (chainLoop L mem h) (l + 1)

/-- Per vertex `v` (DFI): root edges to the children, walkups for the back edges, walkdowns for the children, and
the failure check (a back edge left unembedded). -/
partial def kidsLoop (L : Lay) (mem : Array UInt32) (j jEnd : UInt32) : Array UInt32 :=
  if j ≥ jEnd then mem
  else
    let u := rd mem (L.kList + j)
    kidsLoop L (newEdge L mem (L.n + u) 0 u 0) (j + 1) jEnd

partial def backsLoop (L : Lay) (mem : Array UInt32) (v j jEnd : UInt32) : Array UInt32 :=
  if j ≥ jEnd then mem
  else
    let u := rd mem (L.bList + j)
    backsLoop L (walkup L mem v u) v (j + 1) jEnd

partial def downLoop (L : Lay) (mem : Array UInt32) (v j jEnd : UInt32) : Array UInt32 :=
  if j ≥ jEnd then mem
  else
    let u := rd mem (L.kList + j)
    downLoop L (walkdown L mem v (L.n + u)) v (j + 1) jEnd

partial def failLoop (L : Lay) (mem : Array UInt32) (v j jEnd : UInt32) : Bool :=
  if j ≥ jEnd then false
  else if rd mem (L.bflag + rd mem (L.bList + j)) == v then true
  else failLoop L mem v (j + 1) jEnd

partial def mainLoop (L : Lay) (mem : Array UInt32) (i : UInt32) : Array UInt32 × Bool :=
  if i ≥ L.n then (mem, true)
  else
    let v := L.n - 1 - i
    let mem := wr mem 1 v
    let k0 := rd mem (L.kStart + v)
    let k1 := rd mem (L.kStart + v + 1)
    let b0 := rd mem (L.bStart + v)
    let b1 := rd mem (L.bStart + v + 1)
    let mem := kidsLoop L mem k0 k1
    let mem := backsLoop L mem v b0 b1
    let mem := downLoop L mem v k0 k1
    if failLoop L mem v b0 b1 then (wr mem 3 v, false) else mainLoop L mem (i + 1)

/-- Run the planarity test on the graph with `n` vertices and the `ne` edges `(E[e0 + 2i], E[e0 + 2i + 1])` (simple,
no loops), in the memory `buf` if it is large enough (else a new one). Returns the layout, the final memory (for the
isolator, or for reuse) and `true` iff planar. -/
def bmPlanarE (buf : Array UInt32) (n : Nat) (E : Array Nat) (e0 ne : Nat) : Lay × Array UInt32 × Bool :=
  let L := mkLay n ne
  let mem : Array UInt32 :=
    if buf.size ≥ L.size.toNat then fillLoop buf 0 0 L.size NIL else Array.replicate L.size.toNat NIL
  -- adjacency (CSR): degrees in the dfi slots, cursors in the vert slots
  let mem := fillLoop mem L.dfi 0 L.n 0
  let mem := degLoop L mem E e0 (e0 + 2 * ne)
  let mem := prefLoop L (wr mem L.iadjStart 0) 0
  let mem := adjLoop L mem E e0 (e0 + 2 * ne)
  let mem := fillLoop mem L.dfi 0 L.n NIL
  -- DFS, least ancestors, lowpoints, subtree sizes
  let mem := rootsLoop L (wr mem 4 0) 0
  let mem := clsLoop L (wr (wr mem 5 0) 6 0) 0
  let mem := lowLoop L mem 0
  -- separated child lists (bucket sort by lowpoint in the visited slots, reset after)
  let mem := fillLoop mem L.bflag 0 L.n L.n
  let mem := scLoop L (bucketLoop L mem 0) 0
  let mem := fillLoop mem L.visited 0 (2 * L.n) L.n
  let r := mainLoop L (wr (wr mem 0 0) 3 NIL) 0
  (L, r.1, r.2)

/-- `bmPlanarE` on the edges `(U[i], V[i])`. -/
def bmPlanar (n : Nat) (U V : Array Nat) : Lay × Array UInt32 × Bool :=
  let E := (Array.range (2 * U.size)).map fun i => if i % 2 == 0 then U[i / 2]! else V[i / 2]!
  bmPlanarE #[] n E 0 U.size

/-! ## Isolation helpers (natural numbers; memory read through `rn`) -/

@[inline] def rn (mem : Array UInt32) (i : Nat) : Nat := (mem[i]!).toNat

/-- `nextOnFace` on natural numbers. -/
@[inline] def nextOnFaceN (L : Lay) (mem : Array UInt32) (cur pl : Nat) : Nat × Nat :=
  let q := nof L mem cur.toUInt32 pl.toUInt32
  ((q >>> 1).toNat, (q &&& 1).toNat)

/-- The tree path from the ancestor `a` down to its descendant `d` (both included), top-down. -/
def treePathDown (L : Lay) (mem : Array UInt32) (a d : Nat) : Option (Array Nat) := Id.run do
  let mut tmp : Array Nat := #[]
  let mut t := d
  while t != a && t != NILN do
    tmp := tmp.push t
    t := rn mem (L.par.toNat + t)
  if t != a then return none
  let mut out : Array Nat := #[a]
  for i in [0:tmp.size] do
    out := out.push tmp[tmp.size - 1 - i]!
  return some out

/-- The smallest neighbour of the ancestor `u` inside the subtree of `chi` (`NILN` if none). -/
def nbrInSubtree (L : Lay) (mem : Array UInt32) (u chi : Nat) : Nat := Id.run do
  let x := rn mem (L.vert.toNat + u)
  let hi := chi + rn mem (L.szt.toNat + chi)
  let mut best := NILN
  for k in [rn mem (L.iadjStart.toNat + x):rn mem (L.iadjStart.toNat + x + 1)] do
    let q := rn mem (L.dfi.toNat + rn mem (L.iadj.toNat + k))
    if q ≥ chi && q < hi && (best == NILN || q < best) then best := q
  return best

@[inline] def isExtActive (L : Lay) (mem : Array UInt32) (a : Nat) : Bool := a < L.n.toNat && extActive L mem a.toUInt32

/-- The external-activity connection of `a` at step `v`: a path from `a` down to a vertex adjacent to the landing
ancestor, and the landing. -/
def extConn (L : Lay) (mem : Array UInt32) (a v : Nat) : Option (Array Nat × Nat) :=
  let la := rn mem (L.leastAnc.toNat + a)
  if la < v then some (#[a], la)
  else
    let chi := rn mem (L.scHead.toNat + a)
    if chi == NILN || rn mem (L.lowpt.toNat + chi) ≥ v then none
    else
      let u := rn mem (L.lowpt.toNat + chi)
      let d := nbrInSubtree L mem u chi
      if d == NILN then none
      else (treePathDown L mem a d).map fun p => (p, u)

/-- Adjacency in the input graph (DFI vertices). -/
def inputAdj (L : Lay) (mem : Array UInt32) (a b : Nat) : Bool := Id.run do
  let x := rn mem (L.vert.toNat + a)
  let y := rn mem (L.vert.toNat + b)
  for k in [rn mem (L.iadjStart.toNat + x):rn mem (L.iadjStart.toNat + x + 1)] do
    if rn mem (L.iadj.toNat + k) == y then return true
  return false

/-- `K₅` and `K₃,₃` edge lists as in `hEdges`. -/
def k5E : Array (Nat × Nat) := #[(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
def k33E : Array (Nat × Nat) := #[(0, 3), (0, 4), (0, 5), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5)]

/-! ## The isolator -/

/-- The obstruction `H` of a failed run: key points (DFI vertices; `kU` stands for the tree path above `v`) and the
segments between them (vertex sequences, with the landing ancestors of the ends at `U`). -/
structure HInfo where
  mem : Array UInt32
  keyV : Array Nat
  kU : Nat
  segA : Array Nat
  segB : Array Nat
  segV : Array (Array Nat)
  segL0 : Array Nat
  segL1 : Array Nat

/-! ### Loops of the obstruction builder (tail-recursive) -/

/-- The external face from `w` (link `pl`) up to `Bt` (excluded), appended to `acc`; `none` after `fuel` steps. -/
partial def faceWalk (L : Lay) (mem : Array UInt32) (Bt w pl : UInt32) (acc : Array Nat) (fuel : Nat) :
    Option (Array Nat) :=
  if fuel == 0 then none
  else
    let q := nof L mem w pl
    let w' := q >>> 1
    if w' == Bt then some acc else faceWalk L mem Bt w' (q &&& 1) (acc.push w'.toNat) (fuel - 1)

/-- Orientation recovery: DFS over the tree arcs of the component from `p` (arc cursor `a`, pending vertices `stack`);
`mark[q]` becomes `1` (oriented as the root) or `2` (to be inverted); `0` outside the component. -/
partial def orientLoop (L : Lay) (mem : Array UInt32) (n p a : Nat) (stack mark : Array Nat) : Array Nat :=
  if a != NILN then
    let q := rn mem (L.anb.toNat + a)
    let nx := rn mem (L.anext.toNat + a)
    if q < n && mark[q]! == 0 then
      let tree := if p ≥ n then q == p - n else rn mem (L.par.toNat + q) == p
      if tree then
        let neg := (mark[p]! == 2) != (rn mem (L.asign.toNat + a) == 0)
        orientLoop L mem n p nx (stack.push q) (mark.set! q (if neg then 2 else 1))
      else orientLoop L mem n p nx stack mark
    else orientLoop L mem n p nx stack mark
  else if stack.size > 0 then
    let p2 := stack.back!
    orientLoop L mem n p2 (rn mem (L.first.toNat + p2)) stack.pop mark
  else mark

/-- Invert the real vertices marked `2`, from `q` on. -/
partial def invNeg (L : Lay) (mem : Array UInt32) (mark : Array Nat) (q n : Nat) : Array UInt32 :=
  if q ≥ n then mem
  else invNeg L (if mark[q]! == 2 then invertVertex L mem q.toUInt32 else mem) mark (q + 1) n

/-- Mark the arcs of `Bt` from `a` on (and their twins) as internal unless they are the external arcs `a0`, `a1`. -/
partial def intArcLoop (L : Lay) (mem : Array UInt32) (a a0 a1 : Nat) (ia : Array Bool) : Array Bool :=
  if a == NILN then ia
  else
    let internal := a != a0 && a != a1
    let tw := rn mem (L.atwin.toNat + a)
    let nx := rn mem (L.anext.toNat + a)
    intArcLoop L mem nx a0 a1 ((ia.set! a internal).set! tw internal)

/-- Skip the internal arcs of `Bt` in the rotation of `q` from `s2` (at most `g` steps). -/
partial def skipInt (L : Lay) (mem : Array UInt32) (ia : Array Bool) (Bt q s2 g : Nat) : Nat :=
  if rn mem (L.anb.toNat + s2) == Bt && ia[s2]! && g > 0 then
    let ns := rn mem (L.anext.toNat + s2)
    skipInt L mem ia Bt q (if ns != NILN then ns else rn mem (L.first.toNat + q)) (g - 1)
  else s2

/-- The face walk from `arc` up to `Bt` (included), appended to `fw`; `none` after `fuel` steps. -/
partial def fwWalk (L : Lay) (mem : Array UInt32) (ia : Array Bool) (n Bt arc : Nat) (fw : Array Nat) (fuel : Nat) :
    Option (Array Nat) :=
  let q := rn mem (L.anb.toNat + arc)
  let fw := fw.push q
  if q == Bt then some fw
  else if fuel == 0 then none
  else
    let tw := rn mem (L.atwin.toNat + arc)
    let nt := rn mem (L.anext.toNat + tw)
    let s2 := skipInt L mem ia Bt q (if nt != NILN then nt else rn mem (L.first.toNat + q)) (4 * n)
    fwWalk L mem ia n Bt s2 fw (fuel - 1)

/-- BFS (queue `q2` from position `qh`, current vertex `p` at arc `aa`) from `Bt` through vertices of the component off
the boundary, stopping at the first vertex of the x-y path; returns the parents and the vertex found (`NILN` if none). -/
partial def bfsLoop (L : Lay) (mem : Array UInt32) (n Bt a0 a1 : Nat) (onP : Array Bool) (cpos mark q2 : Array Nat)
    (qh p aa : Nat) (bpar : Array Nat) : Array Nat × Nat :=
  if aa == NILN then
    if qh < q2.size then
      let p2 := q2[qh]!
      bfsLoop L mem n Bt a0 a1 onP cpos mark q2 (qh + 1) p2 (rn mem (L.first.toNat + p2)) bpar
    else (bpar, NILN)
  else
    let q := rn mem (L.anb.toNat + aa)
    let nx := rn mem (L.anext.toNat + aa)
    if (p == Bt && (aa == a0 || aa == a1)) || q ≥ n || bpar[q]! != NILN + 1 then
      bfsLoop L mem n Bt a0 a1 onP cpos mark q2 qh p nx bpar
    else if onP[q]! then (bpar.set! q p, q)
    else if cpos[q]! == NILN && mark[q]! != 0 then
      bfsLoop L mem n Bt a0 a1 onP cpos mark (q2.push q) qh p nx (bpar.set! q p)
    else bfsLoop L mem n Bt a0 a1 onP cpos mark q2 qh p nx bpar

/-- After `bmPlanar` returned `false`: the obstruction `H` (`none` if the construction fails). -/
def bmIsoH (L : Lay) (mem0 : Array UInt32) : Option HInfo := Id.run do
  let n := L.n.toNat
  let mut mem := mem0
  let v := rn mem 3
  if v == NILN then return none
  mem := wr mem 1 v.toUInt32
  -- the unembedded back edge (v, d) and the child c of v above d
  let xv0 := rn mem (L.vert.toNat + v)
  let mut d := NILN
  for k in [rn mem (L.iadjStart.toNat + xv0):rn mem (L.iadjStart.toNat + xv0 + 1)] do
    let u := rn mem (L.dfi.toNat + rn mem (L.iadj.toNat + k))
    if d == NILN && u > v && rn mem (L.par.toNat + u) != v && rn mem (L.bflag.toNat + u) == v then d := u
  if d == NILN then return none
  let mut c := NILN
  for k in [rn mem (L.iadjStart.toNat + xv0):rn mem (L.iadjStart.toNat + xv0 + 1)] do
    let u := rn mem (L.dfi.toNat + rn mem (L.iadj.toNat + k))
    if rn mem (L.par.toNat + u) == v && u ≤ d && d < u + rn mem (L.szt.toNat + u) then c := u
  if c == NILN then return none
  let R := n + c
  mem := walkdown L mem v.toUInt32 R.toUInt32
  let sp := rn mem 2
  let minorA := sp > 0
  let Bt := if minorA then rn mem (L.stk.toNat + sp - 2) else R
  let rreal := rn mem (L.par.toNat + (Bt - n))
  -- the external face cycle of the blocked component, from Bt in direction 0 back to Bt (Bt excluded)
  let some cyc := faceWalk L mem Bt.toUInt32 Bt.toUInt32 1 #[] (2 * n + 4) | return none
  let ncyc := cyc.size
  let mut ix := NILN
  for i in [0:ncyc] do
    if ix == NILN && isExtActive L mem cyc[i]! then ix := i
  let mut iy := NILN
  for j in [0:ncyc] do
    let i := ncyc - 1 - j
    if iy == NILN && isExtActive L mem cyc[i]! then iy := i
  if ix == NILN || iy == NILN || ix ≥ iy then return none
  let x := cyc[ix]!
  let y := cyc[iy]!
  let mut iw := NILN
  for i in [ix + 1:iy] do
    if iw == NILN && cyc[i]! < n && pertinent L mem (cyc[i]!).toUInt32 then iw := i
  if iw == NILN then return none
  let w := cyc[iw]!
  -- key points
  let mut keyOf : Array Nat := Array.replicate n NILN
  let mut keyV : Array Nat := #[]
  let addKey := fun (keyOf keyV : Array Nat) (dv : Nat) =>
    if keyOf[dv]! != NILN then (keyOf, keyV, keyOf[dv]!)
    else (keyOf.set! dv keyV.size, keyV.push dv, keyV.size)
  let r1 := addKey keyOf keyV v
  keyOf := r1.1; keyV := r1.2.1
  let kV := r1.2.2
  let kU := keyV.size
  keyV := keyV.push NILN
  let mut kR := kV
  if minorA then
    let r := addKey keyOf keyV rreal
    keyOf := r.1; keyV := r.2.1; kR := r.2.2
  let rx := addKey keyOf keyV x
  keyOf := rx.1; keyV := rx.2.1
  let ry := addKey keyOf keyV y
  keyOf := ry.1; keyV := ry.2.1
  let rw := addKey keyOf keyV w
  keyOf := rw.1; keyV := rw.2.1
  let kw := rw.2.2
  let mut segA : Array Nat := #[]
  let mut segB : Array Nat := #[]
  let mut segV : Array (Array Nat) := #[]
  let mut segL0 : Array Nat := #[]
  let mut segL1 : Array Nat := #[]
  let mut xyP : Array Nat := #[]
  let mut kz := NILN
  let mut dpath : Array Nat := #[]
  let mut cpos : Array Nat := Array.replicate n NILN
  for i in [0:ncyc] do
    if cyc[i]! < n then cpos := cpos.set! cyc[i]! i
  if !minorA then
    -- orientation recovery of the component (sign products along tree edges from Bt)
    let mark := orientLoop L mem n Bt (rn mem (L.first.toNat + Bt)) #[] ((Array.replicate (2 * n) 0).set! Bt 1)
    mem := invNeg L mem mark 0 n
    -- the face bordered by Bt's two external arcs after deleting Bt's internal arcs
    let a0 := rn mem (L.first.toNat + Bt)
    let a1 := rn mem (L.last.toNat + Bt)
    let intArc := intArcLoop L mem a0 a0 a1 (Array.replicate (2 * L.m.toNat + 2) false)
    let fw? := fwWalk L mem intArc n Bt a1 #[] (4 * n + 8)
    let ok := fw?.isSome
    let fw := fw?.getD #[]
    if ok then
      -- remove loops (revisited cut vertices)
      let mut simp : Array Nat := #[]
      let mut spos : Array Nat := Array.replicate n NILN
      for i in [0:fw.size - 1] do
        let q := fw[i]!
        if q < n && spos[q]! != NILN then
          let j := spos[q]!
          for k2 in [j + 1:simp.size] do
            if simp[k2]! < n then spos := spos.set! simp[k2]! NILN
          simp := simp.extract 0 (j + 1)
        else
          if q < n then spos := spos.set! q simp.size
          simp := simp.push q
      let mut j := NILN
      for k2 in [0:simp.size] do
        let q := simp[k2]!
        if j == NILN && q < n && cpos[q]! != NILN && cpos[q]! < iw then j := k2
      if j != NILN && j > 0 then
        let mut i := NILN
        for t in [0:j] do
          let k2 := j - 1 - t
          let q := simp[k2]!
          if i == NILN && q < n && cpos[q]! != NILN && cpos[q]! > iw then i := k2
        if i != NILN then
          let mut okp := true
          for k2 in [i + 1:j] do
            let q := simp[k2]!
            if q ≥ n || cpos[q]! != NILN then okp := false
          if okp then xyP := simp.extract i (j + 1)
    if xyP.size ≥ 2 then
      let r := addKey keyOf keyV xyP[0]!
      keyOf := r.1; keyV := r.2.1
      let r' := addKey keyOf keyV xyP[xyP.size - 1]!
      keyOf := r'.1; keyV := r'.2.1
      -- the v-z path: BFS from Bt through vertices of B not on the boundary or the x-y path
      let mut onP : Array Bool := Array.replicate n false
      for t2 in [1:xyP.size - 1] do onP := onP.set! xyP[t2]! true
      let bz := bfsLoop L mem n Bt a0 a1 onP cpos mark #[Bt] 1 Bt (rn mem (L.first.toNat + Bt))
        ((Array.replicate (2 * n) (NILN + 1)).set! Bt NILN)
      let bpar := bz.1
      let zfound := bz.2
      if zfound != NILN then
        let rz := addKey keyOf keyV zfound
        keyOf := rz.1; keyV := rz.2.1; kz := rz.2.2
        let mut tmp : Array Nat := #[]
        let mut t2 := zfound
        while t2 != Bt && t2 != NILN do
          tmp := tmp.push t2
          t2 := bpar[t2]!
        dpath := #[v]
        for i in [0:tmp.size] do dpath := dpath.push tmp[tmp.size - 1 - i]!
  -- one extra externally active vertex on the lower path strictly between px and py (minor E1), other than w
  if xyP.size ≥ 2 then
    let lo := cpos[xyP[xyP.size - 1]!]!
    let hi := cpos[xyP[0]!]!
    if lo != NILN && hi != NILN then
      let mut found := false
      for i in [lo + 1:hi] do
        if !found && cyc[i]! != w && isExtActive L mem cyc[i]! then
          let r := addKey keyOf keyV cyc[i]!
          keyOf := r.1; keyV := r.2.1
          found := true
  -- boundary cycle segments: walk cyc as a closed cycle starting at the root key
  let kpy := if xyP.size ≥ 2 then keyOf[xyP[0]!]! else NILN
  do
    let start := if minorA then rreal else v
    let mut seq : Array Nat := #[start]
    let mut prevKey := kR
    for i in [0:ncyc + 1] do
      let q := if i < ncyc then cyc[i]! else start
      seq := seq.push q
      let kq := if i == ncyc then kR else (if q < n then keyOf[q]! else NILN)
      if kq != NILN && kq != kU then
        segA := segA.push prevKey; segB := segB.push kq; segV := segV.push seq
        segL0 := segL0.push NILN; segL1 := segL1.push NILN
        prevKey := kq
        seq := #[q]
  -- x-y path segments, split at z
  if xyP.size ≥ 2 then
    let mut seq2 : Array Nat := #[]
    let mut prevKey2 := kpy
    for t2 in [0:xyP.size] do
      seq2 := seq2.push xyP[t2]!
      if t2 > 0 then
        let kq := keyOf[xyP[t2]!]!
        if kq != NILN && (kq == kz || t2 == xyP.size - 1) then
          segA := segA.push prevKey2; segB := segB.push kq; segV := segV.push seq2
          segL0 := segL0.push NILN; segL1 := segL1.push NILN
          prevKey2 := kq
          seq2 := #[xyP[t2]!]
    if kz != NILN && dpath.size ≥ 2 then
      segA := segA.push kV; segB := segB.push kz; segV := segV.push dpath
      segL0 := segL0.push NILN; segL1 := segL1.push NILN
  -- external-activity connections of the externally active key points (except v, U)
  for k2 in [0:keyV.size] do
    if k2 == kU || k2 == kV then continue
    let a := keyV[k2]!
    if a == NILN || !isExtActive L mem a then continue
    match extConn L mem a v with
    | none => pure ()
    | some (path, land) =>
      let skip := a == w && path.size > 1 && rn mem (L.prHead.toNat + w) != NILN &&
        path[1]! + n == rn mem (L.prTail.toNat + w)
      if !skip then
        segA := segA.push k2; segB := segB.push kU; segV := segV.push path
        segL0 := segL0.push NILN; segL1 := segL1.push land
  -- the pertinence connection of w (and the minor A root path)
  let mut done := false
  let lastRoot := rn mem (L.prTail.toNat + w)
  if lastRoot != NILN && rn mem (L.lowpt.toNat + (lastRoot - n)) < v then
    let chi := lastRoot - n
    let dw := nbrInSubtree L mem v chi
    let du := rn mem (L.lowpt.toNat + chi)
    let dz := nbrInSubtree L mem du chi
    if dw != NILN && dz != NILN then
      -- t = LCA(dw, dz) within the subtree of chi (or w)
      let mut mark : Array Bool := Array.replicate n false
      let mut t2 := dw
      while t2 != NILN do
        mark := mark.set! t2 true
        if t2 == w then break
        t2 := rn mem (L.par.toNat + t2)
      let hi := chi + rn mem (L.szt.toNat + chi)
      let mut t := dz
      while t != NILN && !(t == w || (t ≥ chi && t < hi && mark[t]!)) do
        t := rn mem (L.par.toNat + t)
      if t != NILN && t ≥ chi && t < hi then
        let rt := addKey keyOf keyV t
        keyOf := rt.1; keyV := rt.2.1
        let kt := rt.2.2
        match treePathDown L mem w t with
        | some p =>
          segA := segA.push kw; segB := segB.push kt; segV := segV.push p
          segL0 := segL0.push NILN; segL1 := segL1.push NILN
        | none => pure ()
        match treePathDown L mem t dw with
        | some p =>
          segA := segA.push kt; segB := segB.push kV; segV := segV.push (p.push v)
          segL0 := segL0.push NILN; segL1 := segL1.push NILN
        | none => pure ()
        match treePathDown L mem t dz with
        | some p =>
          segA := segA.push kt; segB := segB.push kU; segV := segV.push p
          segL0 := segL0.push NILN; segL1 := segL1.push du
        | none => pure ()
        done := true
  if rn mem (L.bflag.toNat + w) == v then
    segA := segA.push kw; segB := segB.push kV; segV := segV.push #[w, v]
    segL0 := segL0.push NILN; segL1 := segL1.push NILN
    done := true
  if !done && rn mem (L.prHead.toNat + w) != NILN then
    let chi := rn mem (L.prHead.toNat + w) - n
    let dw := nbrInSubtree L mem v chi
    if dw != NILN then
      match treePathDown L mem w dw with
      | some p =>
        segA := segA.push kw; segB := segB.push kV; segV := segV.push (p.push v)
        segL0 := segL0.push NILN; segL1 := segL1.push NILN
        done := true
      | none => pure ()
  if !done then return none
  if minorA then
    match treePathDown L mem v rreal with
    | some p =>
      if p.size > 1 then
        segA := segA.push kV; segB := segB.push kR; segV := segV.push p
        segL0 := segL0.push NILN; segL1 := segL1.push NILN
    | none => pure ()
  -- v - U: the tree edge to the parent of v
  let pv := rn mem (L.par.toNat + v)
  if pv != NILN then
    segA := segA.push kV; segB := segB.push kU; segV := segV.push #[v]
    segL0 := segL0.push NILN; segL1 := segL1.push pv
  return some { mem, keyV, kU, segA, segB, segV, segL0, segL1 }

/-! ### Planarity of tiny graphs (the minimization tests) -/

/-- The first vertex `≥ v` of degree 1 or 2 (`nk` if none). -/
partial def findLow (deg : Array Nat) (v nk : Nat) : Nat :=
  if v ≥ nk then nk else if deg[v]! == 1 || deg[v]! == 2 then v else findLow deg (v + 1) nk

/-- The first neighbour `≥ j` of `v` (`nk` if none). -/
partial def nextNbr (adj : Array Nat) (nk v j : Nat) : Nat :=
  if j ≥ nk then nk else if adj[v * nk + j]! != 0 then j else nextNbr adj nk v (j + 1)

/-- Delete the vertices of degree 1 and suppress those of degree 2 (merging parallel edges), until none is left.
Planarity is unchanged. -/
partial def reduceLoop (nk : Nat) (adj deg : Array Nat) : Array Nat × Array Nat :=
  let v := findLow deg 0 nk
  if v ≥ nk then (adj, deg)
  else
    let a := nextNbr adj nk v 0
    let da := deg[a]!
    if deg[v]! == 1 then
      reduceLoop nk ((adj.set! (v * nk + a) 0).set! (a * nk + v) 0) ((deg.set! v 0).set! a (da - 1))
    else
      let b := nextNbr adj nk v (a + 1)
      let db := deg[b]!
      let ab := adj[a * nk + b]!
      let adj := (((adj.set! (v * nk + a) 0).set! (a * nk + v) 0).set! (v * nk + b) 0).set! (b * nk + v) 0
      if ab == 0 then
        reduceLoop nk ((adj.set! (a * nk + b) 1).set! (b * nk + a) 1) (deg.set! v 0)
      else reduceLoop nk adj (((deg.set! v 0).set! a (da - 1)).set! b (db - 1))

partial def nzCount (deg : Array Nat) (v nk acc : Nat) : Nat :=
  if v ≥ nk then acc else nzCount deg (v + 1) nk (if deg[v]! > 0 then acc + 1 else acc)

partial def sumArr (deg : Array Nat) (v nk acc : Nat) : Nat :=
  if v ≥ nk then acc else sumArr deg (v + 1) nk (acc + deg[v]!)

/-- A triangle `i < j < k` with `i ≥ i0` (lexicographic scan from `(i, j, k)`). -/
partial def hasTri (adj : Array Nat) (nk i j k : Nat) : Bool :=
  if i ≥ nk then false
  else if j ≥ nk then hasTri adj nk (i + 1) (i + 2) (i + 3)
  else if k ≥ nk || adj[i * nk + j]! == 0 then hasTri adj nk i (j + 1) (j + 2)
  else if adj[i * nk + k]! != 0 && adj[j * nk + k]! != 0 then true
  else hasTri adj nk i j (k + 1)

/-- The vertices of positive degree, in increasing order. -/
def liveVerts (deg : Array Nat) (nk : Nat) : Array Nat :=
  (Array.range nk).filter fun v => deg[v]! > 0

/-- Six live vertices `w` contain a `K₃,₃` (all 9 edges between `{w₀, wᵢ, wⱼ}` and the other three). On 6 vertices of
minimum degree 3 with at most 11 edges, a `K₅` subdivision would need a vertex of degree 2 plus an edge more, so such a
graph is nonplanar iff it contains `K₃,₃`. -/
def hasK33 (adj : Array Nat) (nk : Nat) (deg : Array Nat) : Bool :=
  let w := liveVerts deg nk
  let e := fun (x y : Nat) => adj[w[x]! * nk + w[y]!]! != 0
  [(1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)].any fun ij =>
    let o := ((List.range 6).filter fun t => t != 0 && t != ij.1 && t != ij.2)
    [0, ij.1, ij.2].all fun x => o.all fun y => e x y

/-- The edges `i < j` of `adj` from `(i, j)` on, appended to `U`, `V` (as one array of pairs). -/
partial def edgesOf (adj : Array Nat) (nk i j : Nat) (E : Array Nat) : Array Nat :=
  if i ≥ nk then E
  else if j ≥ nk then edgesOf adj nk (i + 1) (i + 2) E
  else edgesOf adj nk i (j + 1) (if adj[i * nk + j]! != 0 then (E.push i).push j else E)

/-- Planarity of the simple graph with the adjacency matrix `adj` (`nk × nk`, entries `0`/`1`) and degrees `deg`:
reduction, then `E < 9` is planar, `E > 3V - 6` is not, `V ≤ 5` is planar, a 3-regular graph on 6 vertices is `K₃,₃`
(nonplanar) iff it has no triangle (else the prism), on 6 vertices with at most 11 edges nonplanar iff it contains
`K₃,₃`, and the rest goes to `bmPlanar`. -/
def tinyPlanar (buf : Array UInt32) (nk : Nat) (adj0 deg0 : Array Nat) : Bool × Array UInt32 :=
  let r := reduceLoop nk adj0 deg0
  let adj := r.1
  let deg := r.2
  let nv := nzCount deg 0 nk 0
  let ne := sumArr deg 0 nk 0 / 2
  if ne < 9 then (true, buf)
  else if ne + 6 > 3 * nv then (false, buf)
  else if nv ≤ 5 then (true, buf)
  else if nv == 6 && ne == 9 then (hasTri adj nk 0 1 2, buf)
  else if nv == 6 && ne ≤ 11 then (!hasK33 adj nk deg, buf)
  else
    let E := edgesOf adj nk 0 1 (Array.mkEmpty (2 * ne))
    let p := bmPlanarE buf nk E 0 ne
    (p.2.2, p.2.1)

/-- Greedy deletion over the segments from `s` on (multiplicities `cnt`, simple key graph `adj`, `deg`). -/
partial def minLoop (nkey : Nat) (segA segB : Array Nat) (s : Nat) (cnt adj deg : Array Nat) (act : Array Bool)
    (buf : Array UInt32) : Array Bool :=
  if s ≥ segA.size then act
  else
    let a := segA[s]!
    let b := segB[s]!
    if a == b then minLoop nkey segA segB (s + 1) cnt adj deg (act.set! s false) buf
    else
      let i := a * nkey + b
      let j := b * nkey + a
      let c := cnt[i]!
      if c ≥ 2 then
        minLoop nkey segA segB (s + 1) ((cnt.set! i (c - 1)).set! j (c - 1)) adj deg (act.set! s false) buf
      else
        let da := deg[a]!
        let db := deg[b]!
        let adj := (adj.set! i 0).set! j 0
        let deg := (deg.set! a (da - 1)).set! b (db - 1)
        let t := tinyPlanar buf nkey adj deg
        if t.1 then
          minLoop nkey segA segB (s + 1) cnt ((adj.set! i 1).set! j 1) ((deg.set! a da).set! b db) act t.2
        else minLoop nkey segA segB (s + 1) ((cnt.set! i 0).set! j 0) adj deg (act.set! s false) t.2

/-- Segment multiplicities of the key pairs, from segment `s` on. -/
partial def cntLoop (nkey : Nat) (segA segB : Array Nat) (s : Nat) (cnt : Array Nat) : Array Nat :=
  if s ≥ segA.size then cnt
  else
    let a := segA[s]!
    let b := segB[s]!
    if a == b then cntLoop nkey segA segB (s + 1) cnt
    else
      let c := cnt[a * nkey + b]!
      cntLoop nkey segA segB (s + 1) ((cnt.set! (a * nkey + b) (c + 1)).set! (b * nkey + a) (c + 1))

/-- The simple graph (`0`/`1`) of the multiplicities, from entry `i` on. -/
partial def adjLoop2 (cnt adj : Array Nat) (i : Nat) : Array Nat :=
  if i ≥ cnt.size then adj else adjLoop2 cnt (if cnt[i]! != 0 then adj.set! i 1 else adj) (i + 1)

/-- Degrees of the rows of `adj` (`nk × nk`), from row `v` on. -/
partial def degLoop2 (adj : Array Nat) (nk v : Nat) (deg : Array Nat) : Array Nat :=
  if v ≥ nk then deg else degLoop2 adj nk (v + 1) (deg.set! v (sumArr adj (v * nk) (v * nk + nk) 0))

/-- Greedy segment deletion with the tiny-graph test: the active segments of a minimal nonplanar sub-obstruction
(`none` if `H` is planar). A loop or one of several parallel segments can always go (the simple key graph does not
change). -/
def bmIsoMin2 (nkey : Nat) (segA segB : Array Nat) : Option (Array Bool) :=
  let cnt := cntLoop nkey segA segB 0 (Array.replicate (nkey * nkey) 0)
  let adj := adjLoop2 cnt (Array.replicate (nkey * nkey) 0) 0
  let deg := degLoop2 adj nkey 0 (Array.replicate nkey 0)
  let t := tinyPlanar #[] nkey adj deg
  if t.1 then none
  else some (minLoop nkey segA segB 0 cnt adj deg (Array.replicate segA.size true) t.2)

/-- The minor model realizing the minimal sub-obstruction `act` of `H` (input vertex ids), `none` on failure. -/
def bmIsoReal (L : Lay) (h : HInfo) (act : Array Bool) : Option MinorCert := Id.run do
  let n := L.n.toNat
  let mem := h.mem
  let keyV := h.keyV
  let kU := h.kU
  let segA := h.segA
  let segB := h.segB
  let segV := h.segV
  let segL0 := h.segL0
  let segL1 := h.segL1
  let nkey := keyV.size
  let nseg := segA.size
  -- branch keys of the minimal H
  let mut kdeg : Array Nat := Array.replicate nkey 0
  for s2 in [0:nseg] do
    if act[s2]! then
      kdeg := kdeg.modify segA[s2]! (· + 1)
      kdeg := kdeg.modify segB[s2]! (· + 1)
  let mut br : Array Nat := #[]
  let mut d3 := 0
  let mut d4 := 0
  for k2 in [0:nkey] do
    let dg := kdeg[k2]!
    if dg == 3 then d3 := d3 + 1
    else if dg == 4 then d4 := d4 + 1
    else if dg != 0 && dg != 2 then return none
    if dg ≥ 3 && br.size < 6 then br := br.push k2
  let isK5 := d4 == 5 && d3 == 0
  let isK33 := d3 == 6 && d4 == 0
  if !isK5 && !isK33 then return none
  let nbr := if isK5 then 5 else 6
  let mut bidx : Array Nat := Array.replicate nkey NILN
  for q in [0:nbr] do bidx := bidx.set! br[q]! q
  -- trace the H-paths between branch keys (sequences of (segment, direction))
  let mut usedSeg : Array Bool := Array.replicate nseg false
  let mut hps : Array (Array (Array (Nat × Nat))) := Array.replicate nbr #[]
  let mut hend : Array (Array Nat) := Array.replicate nbr #[]
  for q in [0:nbr] do
    let kq := br[q]!
    for s2 in [0:nseg] do
      if !act[s2]! || usedSeg[s2]! || (segA[s2]! != kq && segB[s2]! != kq) then continue
      let mut path : Array (Nat × Nat) := #[]
      let mut cur := kq
      let mut sg := s2
      let mut fin := false
      let mut endB := NILN
      while !fin do
        usedSeg := usedSeg.set! sg true
        let dir := if segA[sg]! == cur then 0 else 1
        path := path.push (sg, dir)
        let nxt := if dir == 0 then segB[sg]! else segA[sg]!
        if bidx[nxt]! != NILN then
          endB := bidx[nxt]!
          fin := true
        else
          let mut ns2 := NILN
          for s3 in [0:nseg] do
            if ns2 == NILN && act[s3]! && !usedSeg[s3]! && (segA[s3]! == nxt || segB[s3]! == nxt) then ns2 := s3
          if ns2 == NILN then return none
          cur := nxt
          sg := ns2
      hps := hps.modify q (·.push path)
      hend := hend.modify q (·.push endB)
  -- labels: K5 identity, K3,3 by 2-colouring the branch graph
  let mut lab : Array Nat := Array.range nbr
  if !isK5 then
    let mut badj : Array Bool := Array.replicate 36 false
    for q in [0:6] do
      for e in hend[q]! do
        badj := badj.set! (q * 6 + e) true
        badj := badj.set! (e * 6 + q) true
    let mut col : Array Nat := Array.replicate 6 NILN
    col := col.set! 0 0
    let mut changed := true
    while changed do
      changed := false
      for q in [0:6] do
        if col[q]! != NILN then
          for r2 in [0:6] do
            if badj[q * 6 + r2]! then
              if col[r2]! == NILN then
                col := col.set! r2 (1 - col[q]!)
                changed := true
              else if col[r2]! == col[q]! then return none
    let mut na := 0
    let mut nb2 := 3
    for q in [0:6] do
      if col[q]! == 0 then
        lab := lab.set! q na; na := na + 1
      else
        lab := lab.set! q nb2; nb2 := nb2 + 1
    if na != 3 || nb2 != 6 then return none
  let mut inv : Array Nat := Array.replicate nbr 0
  for q in [0:nbr] do inv := inv.set! lab[q]! q
  -- branch sets (DFI vertices with parent positions): roots
  let mut bv : Array (Array Nat) := Array.replicate nbr #[]
  let mut bp : Array (Array Nat) := Array.replicate nbr #[]
  let mut owner : Array Nat := Array.replicate n NILN
  for u2 in [0:nbr] do
    let q := inv[u2]!
    let kq := br[q]!
    if kq == kU then
      let mut lo := n
      let mut hi := NILN
      for pi in [0:(hps[q]!).size] do
        let pth := hps[q]![pi]!
        let sg := pth[0]!.1
        let dir := pth[0]!.2
        let mut land := if dir == 0 then segL0[sg]! else segL1[sg]!
        if land == NILN then land := if dir == 0 then segL1[sg]! else segL0[sg]!
        if land != NILN then
          if land < lo then lo := land
          if hi == NILN || land > hi then hi := land
      for pi in [0:nbr] do
        for pj in [0:(hps[pi]!).size] do
          if hend[pi]![pj]! == q then
            let pth := hps[pi]![pj]!
            let sg := pth[pth.size - 1]!.1
            let dir := pth[pth.size - 1]!.2
            let land := if dir == 0 then segL1[sg]! else segL0[sg]!
            if land != NILN then
              if land < lo then lo := land
              if hi == NILN || land > hi then hi := land
      if hi == NILN then return none
      let mut vs : Array Nat := #[]
      let mut ps : Array Nat := #[]
      let mut t2 := hi
      let mut fin := false
      while !fin do
        ps := ps.push (if vs.size == 0 then 0 else vs.size - 1)
        vs := vs.push t2
        owner := owner.set! t2 u2
        if t2 == lo || rn mem (L.par.toNat + t2) == NILN then fin := true
        else t2 := rn mem (L.par.toNat + t2)
      bv := bv.set! u2 vs
      bp := bp.set! u2 ps
    else
      let g := keyV[kq]!
      bv := bv.set! u2 #[g]
      bp := bp.set! u2 #[0]
      owner := owner.set! g u2
  -- realize each H-path: internal vertices go to the first branch; record the realizing edge
  let hE := if isK5 then k5E else k33E
  let mut hp : Array (Nat × Nat) := Array.replicate hE.size (NILN, NILN)
  for q in [0:nbr] do
    for pi in [0:(hps[q]!).size] do
      let pth := hps[q]![pi]!
      let qb := hend[q]![pi]!
      let mut ua := lab[q]!
      let mut ub := lab[qb]!
      let rev := ua > ub
      if rev then
        let t9 := ua; ua := ub; ub := t9
      -- the full G vertex sequence of the H-path
      let mut gs : Array Nat := #[]
      let mut ancestorLast := NILN
      let pushNew := fun (gs : Array Nat) (x : Nat) => if gs.size == 0 || gs.back! != x then gs.push x else gs
      for t3 in [0:pth.size] do
        let sg := pth[t3]!.1
        let dir := pth[t3]!.2
        let fromU := (if dir == 0 then segA[sg]! else segB[sg]!) == kU
        let landFrom := if dir == 0 then segL0[sg]! else segL1[sg]!
        let landTo := if dir == 0 then segL1[sg]! else segL0[sg]!
        let sv := segV[sg]!
        if fromU then
          let land := if landFrom != NILN then landFrom else landTo
          if t3 > 0 && ancestorLast != NILN then
            let a1x := ancestorLast
            let b1x := land
            if a1x > b1x then
              let mut t2 := a1x
              while t2 != b1x do
                gs := pushNew gs t2
                t2 := rn mem (L.par.toNat + t2)
              gs := gs.push b1x
            else
              let mut tmp2 : Array Nat := #[]
              let mut t2 := b1x
              while t2 != a1x do
                tmp2 := tmp2.push t2
                t2 := rn mem (L.par.toNat + t2)
              tmp2 := tmp2.push a1x
              for i in [0:tmp2.size] do gs := pushNew gs tmp2[tmp2.size - 1 - i]!
          else if t3 == 0 then
            gs := gs.push land
          for i in [0:sv.size] do gs := pushNew gs sv[sv.size - 1 - i]!
          ancestorLast := NILN
        else
          if dir == 0 then
            for i in [0:sv.size] do gs := pushNew gs sv[i]!
          else
            for i in [0:sv.size] do gs := pushNew gs sv[sv.size - 1 - i]!
          let toU := (if dir == 0 then segB[sg]! else segA[sg]!) == kU
          if toU then
            let land := if landTo != NILN then landTo else landFrom
            gs := gs.push land
            ancestorLast := land
      if rev then gs := gs.reverse
      -- gs[0] in branch ua, gs.back in branch ub; internal vertices -> branch ua (a chain)
      let mut pa := NILN
      let bua := bv[ua]!
      for t2 in [0:bua.size] do
        if bua[t2]! == gs[0]! then pa := t2
      if pa == NILN then return none
      let mut last := pa
      let mut endPos := NILN
      let bub := bv[ub]!
      for t2 in [0:bub.size] do
        if bub[t2]! == gs.back! then endPos := t2
      if endPos == NILN then
        let mut j := NILN
        for t2 in [1:gs.size] do
          if j == NILN && gs[t2]! < n && owner[gs[t2]!]! == ub then j := t2
        if j == NILN then return none
        gs := gs.extract 0 (j + 1)
        for t2 in [0:bub.size] do
          if bub[t2]! == gs.back! then endPos := t2
      for t2 in [1:gs.size - 1] do
        let g := gs[t2]!
        if owner[g]! != NILN then return none
        let pos := (bv[ua]!).size
        bv := bv.modify ua (·.push g)
        bp := bp.modify ua (·.push last)
        owner := owner.set! g ua
        last := pos
      let mut ei := NILN
      for e2 in [0:hE.size] do
        if hE[e2]! == (ua, ub) then ei := e2
      if ei == NILN then return none
      hp := hp.set! ei (last, endPos)
  for e2 in [0:hE.size] do
    if hp[e2]!.1 == NILN then return none
  -- verify against the input graph (DFI vertices)
  for u2 in [0:nbr] do
    for t2 in [1:(bv[u2]!).size] do
      if !inputAdj L mem (bv[u2]![t2]!) (bv[u2]![bp[u2]![t2]!]!) then return none
  for e2 in [0:hE.size] do
    let ab := hE[e2]!
    if !inputAdj L mem (bv[ab.1]![hp[e2]!.1]!) (bv[ab.2]![hp[e2]!.2]!) then return none
  -- convert to input vertex ids
  let branch : Array (Array (Nat × Nat)) := (Array.range nbr).map fun u2 =>
    (Array.range (bv[u2]!).size).map fun t2 => (rn mem (L.vert.toNat + bv[u2]![t2]!), bp[u2]![t2]!)
  return some { k5 := isK5, branch := branch, wit := hp }

/-- After `bmPlanar` returned `false`: a `K₅` / `K₃,₃` minor model of the input graph (input vertex ids), or `none`
when the construction fails (nothing is trusted). -/
def bmIsolate (L : Lay) (mem0 : Array UInt32) : Option MinorCert :=
  match bmIsoH L mem0 with
  | none => none
  | some h =>
    match bmIsoMin2 h.keyV.size h.segA h.segB with
    | none => none
    | some act => bmIsoReal L h act

end Thrackle78Core.BM
