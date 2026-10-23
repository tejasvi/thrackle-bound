import Thrackle78.Proof.Run610Defs
import Thrackle78.Theta

/-!
# The run lemma for `4/3`: three consecutive 6-edges on a 10-face (the enumeration and its checks)

A 10-face walk `w₀ … w₉` whose first three traversals run along a 6-face `C = c₀ … c₅` (`w_t = c_t`, `t ≤ 3`). Labels:
`0 … 5` for `C`, and `t + 2` for a vertex not on `C` first seen at position `t` (`4 ≤ t ≤ 9`). A pattern `xs` lists
the labels of `w₄ … w₉`. `violB3` detects walks that a facial walk cannot be (as `violB`); every other valid pattern
has a certificate (`checkCert3`): those of the run lemma for `51/38` (a triangle, a 4-cycle, two 6-cycles with a
common vertex and different edges, a 6-cycle and an 8-cycle with a common edge), or a copy of one of the three theta
graphs of `ThetaFacts` in the union (a list of labels, one for each vertex of the listing).
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

/-! ## Labels and the union -/

/-- The labels of the whole walk. -/
def wl3 (xs : List ℕ) : List ℕ := [0, 1, 2, 3] ++ xs

/-- The label at position `t`. -/
def wlAt3 (xs : List ℕ) (t : ℕ) : ℕ := (wl3 xs).getD (t % 10) 0

/-- The step `t` and the step `u` use the same edge. -/
def sameStep3 (xs : List ℕ) (t u : ℕ) : Bool :=
  decide ((wlAt3 xs t = wlAt3 xs u ∧ wlAt3 xs (t + 1) = wlAt3 xs (u + 1)) ∨
    (wlAt3 xs t = wlAt3 xs (u + 1) ∧ wlAt3 xs (t + 1) = wlAt3 xs u))

/-- `ab` is an edge of the union of `C` and the walk. -/
def uEdgeB3 (xs : List ℕ) (a b : ℕ) : Bool :=
  cEdgeB a b || (List.range 10).any fun t =>
    decide ((a = wlAt3 xs t ∧ b = wlAt3 xs (t + 1)) ∨ (b = wlAt3 xs t ∧ a = wlAt3 xs (t + 1)))

/-- The label `l` occurs. -/
def usedB3 (xs : List ℕ) (l : ℕ) : Bool := decide (l < 6) || xs.contains l

/-- The pattern is consistent: each new label first occurs at its own position. -/
def validB3 (xs : List ℕ) : Bool :=
  decide (xs.length = 6) && (List.range 6).all fun k =>
    decide (xs.getD k 0 < 6 ∨ xs.getD k 0 = k + 6 ∨ ∃ k' < k, xs.getD k 0 = k' + 6 ∧ xs.getD k' 0 = k' + 6)

/-- The number of steps that use the same edge as step `t` (step `t` included). -/
def stepMult3 (xs : List ℕ) (t : ℕ) : ℕ := ((List.range 10).filter fun u => sameStep3 xs t u).length

/-- The walk cannot be a facial walk along `C`: a step joins equal labels, a step is reversed at once, an edge of `C`
is traversed twice, or an edge is traversed three times. -/
def violB3 (xs : List ℕ) : Bool :=
  (List.range 10).any (fun t => decide (wlAt3 xs t = wlAt3 xs (t + 1))) ||
  (List.range 10).any (fun t => decide (wlAt3 xs t = wlAt3 xs (t + 2))) ||
  (List.range 10).any (fun t => cEdgeB (wlAt3 xs t) (wlAt3 xs (t + 1)) && decide (2 ≤ stepMult3 xs t)) ||
  (List.range 10).any (fun t => decide (3 ≤ stepMult3 xs t))

/-- `c` is a cycle of length `k` in the union, on occurring labels. -/
def cycOK3 (xs : List ℕ) (k : ℕ) (c : List ℕ) : Bool :=
  decide (c.length = k) && decide c.Nodup && c.all (usedB3 xs) &&
    (List.range k).all fun i => uEdgeB3 xs (c.getD i 0) (c.getD ((i + 1) % k) 0)

/-- The labels `l` (one for each vertex `0 … n-1` of the listing `lst`) are a copy of the listed graph in the union. -/
def thetaOK3 (xs : List ℕ) (n : ℕ) (lst : List (ℕ × ℕ)) (l : List ℕ) : Bool :=
  decide (l.length = n) && decide l.Nodup && l.all (usedB3 xs) &&
    lst.all fun p => uEdgeB3 xs (l.getD p.1 0) (l.getD p.2 0)

/-- The check of a certificate `(kind, c, d)`. -/
def checkCert3 (xs : List ℕ) (cert : ℕ × List ℕ × List ℕ) : Bool :=
  match cert.1 with
  | 4 => cycOK3 xs 3 cert.2.1
  | 5 => cycOK3 xs 4 cert.2.1
  | 6 => cycOK3 xs 6 cert.2.1 && cycOK3 xs 6 cert.2.2 && cert.2.1.any (fun l => cert.2.2.contains l) &&
      (List.range 6).any fun i => !((List.range 6).any fun j => sameCEdge 6 6 cert.2.1 cert.2.2 i j)
  | 7 => cycOK3 xs 6 cert.2.1 && cycOK3 xs 8 cert.2.2 &&
      (List.range 6).any fun i => (List.range 8).any fun j => sameCEdge 6 8 cert.2.1 cert.2.2 i j
  | 8 => thetaOK3 xs 7 lTH233 cert.2.1
  | 9 => thetaOK3 xs 8 lTH234 cert.2.1
  | 10 => thetaOK3 xs 12 lTH337 cert.2.1
  | _ => false

end Thrackle78.Proof
