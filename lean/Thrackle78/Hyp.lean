/-
Thrackle78.Hyp: the named hypotheses.

`ThrackleAxioms Thr` collects the published facts about (geometric) thrackleability `Thr` that the proof uses; none of
them is proved here:
* `sub`    : a subgraph of a thrackle is a thrackle (restrict the drawing);
* `c4`     : C4 is not thrackleable (classical);
* `faces`  : a 2-connected triangle-free thrackle has the facial structure `FaceData` (Fulek-Pach 2019, Cor. 1 and
             Prop. 1: parity embedding in the projective plane, planar embedding when bipartite);
* `double` : Conway doubling of a triangle gives a connected bipartite thrackle with 3 more vertices and 3 more edges
             (Fulek-Pach 2011, Lemma 5; doubling preserves connectivity);
* `link`   : a thrackle drawing with at least one edge gives, for every oriented edge listing, a crossing system with
             a planar augmented graph (Fulek-Pach 2011, Sec. 4: the crossing orders of the drawing, and the augmented
             graph drawn without crossings, hence with no `K₅` or `K₃,₃` minor).
The computational facts are `¬ CombThr E` for the exact oriented edge listings used in the computations: the 13 graphs
of the 6-8 overlap lemma and the 7 graphs of the 6-6 overlap lemma (two 6-cycles through a common vertex, in
triangle-free graphs). `CompFacts15` (18 graphs, for `15/11`) omits the two graphs
needed only when the 6-cycles share no edge; `CompFacts` (all 20) is used for `27/20`. The overlap lemmas themselves
are proved from these by enumeration.
-/
import Thrackle78.Defs

namespace Thrackle78

open SimpleGraph

/-- Published facts about a thrackleability predicate `Thr` (on graphs over finite types). -/
structure ThrackleAxioms (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop) : Prop where
  sub : ∀ {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (H : SimpleGraph V)
    (G : SimpleGraph W), H ⊑ G → Thr G → Thr H
  c4 : ¬ Thr (cycleGraph 4)
  faces : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], Thr G → TwoConn G →
    G.CliqueFree 3 → Nonempty (FaceData G)
  double : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), Thr G → G.Connected →
    4 ≤ Fintype.card V → ¬ G.CliqueFree 3 →
    ∃ (N : ℕ) (H : SimpleGraph (Fin N)), Thr H ∧ H.Connected ∧ H.Colorable 2 ∧ N = Fintype.card V + 3 ∧
      Nat.card H.edgeSet = Nat.card G.edgeSet + 3
  link : ∀ {n m : ℕ} (G : SimpleGraph (Fin n)) (E : Fin m → Fin n × Fin n), 0 < m → IsEdgeListing G E →
    Thr G → CombThr E

/-! ## The oriented edge listings of the computations (vertex count, edge list) -/

/-- Edge listing from a list of pairs of naturals (entries reduced mod n; all entries below are < n). -/
def mkE (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) : Fin l.length → Fin n × Fin n :=
  fun i => (Fin.ofNat n (l.get i).1, Fin.ofNat n (l.get i).2)

/-- DB(6,8,-1) as run: graphs/DB_6_8_-1r.txt. -/
def lDB681 : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(0,5),(1,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,0)]
/-- DB(6,8,-2) as run: graphs/DB_6_8_-2.txt. -/
def lDB682 : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(2,6),(6,7),(7,8),(8,9),(9,10),(10,0)]
/-- DB(6,8,-3) as run: prep/r_udb_6.txt. -/
def lDB683 : List (ℕ × ℕ) :=
  [(0,7),(7,6),(6,9),(9,8),(8,1),(0,1),(1,2),(2,3),(3,4),(4,5),(5,6)]
/-- The ten further overlap classes as run: prep/r_union_7.txt ... prep/r_union_16.txt (vertex counts 11, 11, 10,
10, 11, 10, 10, 10, 9, 10). -/
def lU7 : List (ℕ × ℕ) :=
  [(0,7),(7,6),(6,5),(5,4),(0,4),(0,1),(1,2),(1,8),(2,3),(3,4),(4,10),(8,9),(9,10)]
def lU8 : List (ℕ × ℕ) :=
  [(0,10),(10,3),(3,2),(2,1),(0,1),(0,7),(1,8),(3,4),(3,9),(8,9),(4,5),(5,6),(6,7)]
def lU9 : List (ℕ × ℕ) :=
  [(0,7),(7,6),(6,5),(5,4),(0,4),(0,1),(1,2),(1,8),(2,3),(3,4),(3,9),(8,9)]
def lU10 : List (ℕ × ℕ) :=
  [(0,7),(7,3),(3,2),(2,1),(0,1),(1,8),(3,4),(3,9),(8,9),(4,5),(5,6),(6,7)]
def lU11 : List (ℕ × ℕ) :=
  [(0,10),(10,5),(5,6),(6,7),(0,7),(0,1),(1,2),(1,8),(2,3),(3,4),(4,5),(5,9),(8,9)]
def lU12 : List (ℕ × ℕ) :=
  [(0,7),(7,6),(6,5),(5,4),(0,4),(0,1),(1,2),(1,8),(2,3),(3,4),(5,9),(8,9)]
def lU13 : List (ℕ × ℕ) :=
  [(1,2),(2,3),(3,4),(4,8),(1,8),(1,0),(0,7),(4,5),(4,9),(7,9),(5,6),(6,7)]
def lU14 : List (ℕ × ℕ) :=
  [(0,9),(9,3),(3,2),(2,1),(0,1),(0,7),(1,8),(3,4),(4,8),(4,5),(5,6),(6,7)]
def lU15 : List (ℕ × ℕ) :=
  [(0,7),(7,3),(3,2),(2,1),(0,1),(1,8),(3,4),(4,8),(4,5),(5,6),(6,7)]
def lU16 : List (ℕ × ℕ) :=
  [(0,9),(9,5),(5,6),(6,7),(0,7),(0,1),(1,2),(1,8),(2,3),(3,4),(4,8),(4,5)]

/-! ## The 6-6 overlap classes (two 6-cycles through a common vertex; the computations of the 6-6 lemma) -/

/-- DB(6,6,0) as run: graphs/DB_6_6_0r.txt. -/
def lDB660 : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(0,5),(0,6),(6,7),(7,8),(8,9),(9,10),(10,0)]
/-- DB(6,6,-1) as run: graphs/DB_6_6_-1r.txt. -/
def lDB661 : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(0,5),(1,6),(6,7),(7,8),(8,9),(9,0)]
/-- DB(6,6,-2) as run: graphs/DB_6_6_-2.txt. -/
def lDB662 : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(2,6),(6,7),(7,8),(8,0)]
/-- DB(6,6,-3) as run: graphs/DB_6_6_-3.txt. -/
def lDB663 : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(3,6),(6,7),(7,0)]
/-- The triangle-free 6-6 classes not covered by `C4` or a dumbbell (u66v_4, u66v_5, u66v_7), as run: the listings
prep/r66_u66v_k.txt written by src/prep.py from graphs/u66v_k.txt (same vertex labels; edges reordered and
reoriented). -/
def lV4 : List (ℕ × ℕ) := [(0,5),(5,7),(7,2),(2,1),(0,1),(0,6),(2,3),(3,6),(3,4),(4,5)]
def lV5 : List (ℕ × ℕ) := [(0,5),(5,8),(8,2),(2,1),(0,1),(0,6),(2,3),(2,7),(6,7),(3,4),(4,5)]
def lV7 : List (ℕ × ℕ) := [(0,9),(9,3),(3,2),(2,1),(0,1),(0,5),(0,6),(3,4),(4,5),(3,8),(6,7),(7,8)]

/-- **The computational facts of the `15/11` bound**: the listed graphs (oriented edge listings) are not
combinatorially thrackleable. The 13 graphs of the 6-8 overlap lemma, and the five graphs of the 6-6 overlap lemma for
two 6-cycles sharing an edge (`DB(6,6,-1)`, `DB(6,6,-2)`, `DB(6,6,-3)`, `u66v_4`, `u66v_5`). -/
structure CompFacts15 : Prop where
  db681 : ¬ CombThr (mkE 12 lDB681)
  db682 : ¬ CombThr (mkE 11 lDB682)
  db683 : ¬ CombThr (mkE 10 lDB683)
  u7 : ¬ CombThr (mkE 11 lU7)
  u8 : ¬ CombThr (mkE 11 lU8)
  u9 : ¬ CombThr (mkE 10 lU9)
  u10 : ¬ CombThr (mkE 10 lU10)
  u11 : ¬ CombThr (mkE 11 lU11)
  u12 : ¬ CombThr (mkE 10 lU12)
  u13 : ¬ CombThr (mkE 10 lU13)
  u14 : ¬ CombThr (mkE 10 lU14)
  u15 : ¬ CombThr (mkE 9 lU15)
  u16 : ¬ CombThr (mkE 10 lU16)
  db661 : ¬ CombThr (mkE 10 lDB661)
  db662 : ¬ CombThr (mkE 9 lDB662)
  db663 : ¬ CombThr (mkE 8 lDB663)
  v4 : ¬ CombThr (mkE 8 lV4)
  v5 : ¬ CombThr (mkE 9 lV5)

/-- **The computational facts of the `27/20` bound**: the eighteen of `CompFacts15`, and the two further graphs of the
6-6 overlap lemma for two 6-cycles sharing only a vertex (`DB(6,6,0)`, `u66v_7`). -/
structure CompFacts : Prop where
  db681 : ¬ CombThr (mkE 12 lDB681)
  db682 : ¬ CombThr (mkE 11 lDB682)
  db683 : ¬ CombThr (mkE 10 lDB683)
  u7 : ¬ CombThr (mkE 11 lU7)
  u8 : ¬ CombThr (mkE 11 lU8)
  u9 : ¬ CombThr (mkE 10 lU9)
  u10 : ¬ CombThr (mkE 10 lU10)
  u11 : ¬ CombThr (mkE 11 lU11)
  u12 : ¬ CombThr (mkE 10 lU12)
  u13 : ¬ CombThr (mkE 10 lU13)
  u14 : ¬ CombThr (mkE 10 lU14)
  u15 : ¬ CombThr (mkE 9 lU15)
  u16 : ¬ CombThr (mkE 10 lU16)
  db661 : ¬ CombThr (mkE 10 lDB661)
  db662 : ¬ CombThr (mkE 9 lDB662)
  db663 : ¬ CombThr (mkE 8 lDB663)
  v4 : ¬ CombThr (mkE 8 lV4)
  v5 : ¬ CombThr (mkE 9 lV5)
  db660 : ¬ CombThr (mkE 11 lDB660)
  v7 : ¬ CombThr (mkE 10 lV7)

end Thrackle78
