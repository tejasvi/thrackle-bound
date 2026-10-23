import Thrackle78Core

/-!
# A top tree with skipped nodes, and the canonical-restriction test (core Lean only)

`walkBQ` is `walkBS` with one more way to accept a node: `skip k rows = true`. If no crossing system with property `Q`
extends a skipped node, the walk shows that no crossing system with `Q` has a planar augmented graph; a symmetry
argument (every planar system has a planar image with `Q`) then gives `¬ CombThr`.

`symSkip K R σ flip`: the test of the C search with a symmetry. Once the edges of `R` (all `< K`) are closed, the rows of
`R` restricted to `R` are compared (lexicographically) with their image under the edge map `σ` (an involution of `R`,
rows of the edges with `flip` reversed); a node is skipped if the restriction is larger than its image.

`checkBFromListR`: the batch check with the filters restricted at each shard root to the systems compatible with it.

A separate library, so that the core library (and the facts built on it) stay unchanged.
-/

namespace Thrackle78Core

/-- The top of a sharded search where nodes with `skip` are accepted. -/
def walkBQ (n : Nat) (es : Array (Nat × Nat)) (fs : List FiltB) (orc : Oracle) (LA : Array (Nat × Array (List Nat)))
    (look : Nat × Array (List Nat) → Nat) (skip : Nat → Array (List Nat) → Bool) :
    Nat → Nat → Array (List Nat) → List Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, k, rows, alive =>
    skip k rows ||
    (decide (look (k, rows) < LA.size) && LA.getD (look (k, rows)) (0, #[]) == (k, rows)) ||
    (List.range fs.length).any (fun i => alive.getD i 0 == 0) ||
    oracleOK n es orc k rows ||
    (decide (k < es.size) &&
      (if (rows.getD k []).length = numEarlier es k then walkBQ n es fs orc LA look skip fuel (k + 1) rows alive
       else (childrenFP es k rows).all fun c =>
         walkBQ n es fs orc LA look skip fuel k c.2.2
           ((List.range fs.length).map fun i =>
             alive.getD i 0 &&& stepMask es (fs.getD i ⟨[], [], #[], 0⟩).g (fs.getD i ⟨[], [], #[], 0⟩).ms
               (fs.getD i ⟨[], [], #[], 0⟩).all k c.1 c.2.1 rows)))

/-- The top of the sharded search from the root, with skipped nodes. -/
def checkTopQ (n : Nat) (es : Array (Nat × Nat)) (fs : List Filt) (orc : Oracle) (LA : Array (Nat × Array (List Nat)))
    (look : Nat × Array (List Nat) → Nat) (skip : Nat → Array (List Nat) → Bool) : Bool :=
  walkBQ n es (fs.map prepB) orc LA look skip ((es.size + 1) * (es.size + 1)) 0 (Array.replicate es.size [])
    (fs.map fun φ => compatMask φ 0 (Array.replicate es.size []))

/-- The rows of the edges of `R` (in the order of `R`), restricted to `R`. -/
def restrR (R : List Nat) (row : Nat → List Nat) : List (List Nat) :=
  R.map fun e => (row e).filter (fun f => R.contains f)

/-- The image of `restrR` under the edge map `σ` (an involution of `R`): the row of `e` is the restricted row of `σ e`
mapped by `σ`, reversed if `σ e` is flipped. -/
def imageR (R : List Nat) (σ : Nat → Nat) (flip : Nat → Bool) (row : Nat → List Nat) : List (List Nat) :=
  R.map fun e =>
    let r := ((row (σ e)).filter (fun f => R.contains f)).map σ
    if flip (σ e) then r.reverse else r

/-- The restriction is canonical (lexicographically at most its image). -/
def canonR (R : List Nat) (σ : Nat → Nat) (flip : Nat → Bool) (row : Nat → List Nat) : Bool :=
  decide (restrR R row ≤ imageR R σ flip row)

/-- Skip the nodes at stage `K` or later whose restriction to `R` is not canonical. -/
def symSkip (K : Nat) (R : List Nat) (σ : Nat → Nat) (flip : Nat → Bool) (k : Nat) (rows : Array (List Nat)) : Bool :=
  decide (K ≤ k) && !canonR R σ flip (fun e => rows.getD e [])

/-- A filter restricted to its systems compatible with the state `(k, rows)`. -/
def restrictFilt (φ : Filt) (k : Nat) (rows : Array (List Nat)) : Filt :=
  ⟨φ.g, φ.sys.filter fun sy => compat φ.g sy k rows⟩

/-- `checkBFromList` with every filter restricted, at each shard root, to its systems compatible with the root (the
masks are computed per root on the short lists; the root bitsets are full). -/
def checkBFromListR (n : Nat) (es : Array (Nat × Nat)) (fs : List Filt) (orc : Oracle)
    (L : List (Nat × Array (List Nat))) : Bool :=
  L.all fun s =>
    let fs' := fs.map fun φ => restrictFilt φ s.1 s.2
    walkB n es (fs'.map prepB) orc ((es.size + 1) * (es.size + 1)) s.1 s.2 (fs'.map fun φ => allOf φ.sys)

end Thrackle78Core
