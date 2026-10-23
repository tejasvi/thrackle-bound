/-
Thrackle78.Theta: the three theta graphs of the `4/3` bound (the computations of the run lemma), with their oriented edge
listings exactly as run, and the named hypothesis `ThetaFacts`: none of them is combinatorially thrackleable.
-/
import Thrackle78.Hyp

namespace Thrackle78

/-- theta(2,3,3) as run: graphs/u610_3_0.txt of the computations of the run lemma.
Poles 0 and 3; paths 0-6-3, 0-1-2-3 and 0-5-4-3. -/
def lTH233 : List (ℕ × ℕ) := [(0,1),(0,5),(0,6),(1,2),(2,3),(3,4),(3,6),(4,5)]

/-- theta(2,3,4) = DB(5,6,-2) as run: graphs/DB_5_6_-2.txt of the computations of the run lemma.
Poles 0 and 2; paths 0-1-2, 0-4-3-2 and 0-7-6-5-2. -/
def lTH234 : List (ℕ × ℕ) := [(0,1),(1,2),(2,3),(3,4),(4,0),(2,5),(5,6),(6,7),(7,0)]

/-- theta(3,3,7) = DB(6,10,-3) as run: graphs/T337s.txt of the theta(3,3,7) search. Poles 0 and 3; e0..e5 are the
paths A = 0-1-2-3 and B = 0-4-5-3, e6..e12 the path 0-6-7-8-9-10-11-3; every edge is oriented from 0 towards 3. -/
def lTH337 : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(0,4),(4,5),(5,3),(0,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,3)]

/-- **The computational facts of the `4/3` bound**: the three theta graphs (oriented edge listings exactly as run) are
not combinatorially thrackleable. -/
structure ThetaFacts : Prop where
  th233 : ¬ CombThr (mkE 7 lTH233)
  th234 : ¬ CombThr (mkE 8 lTH234)
  th337 : ¬ CombThr (mkE 12 lTH337)

end Thrackle78
