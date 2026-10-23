import Thrackle78.Proof.Hex66Defs

/-!
# The run lemma on 10-faces: the enumeration and its checks

A 10-face walk `w₀ … w₉` whose first four traversals run along a 6-face `C = c₀ … c₅` (`w_t = c_t`, `t ≤ 4`). Labels:
`0 … 5` for `C`, and `t + 1` for a vertex not on `C` first seen at position `t` (`5 ≤ t ≤ 9`). A pattern `xs` lists
the labels of `w₅ … w₉`. `violB` detects walks that a facial walk cannot be (a repeated or spiked step, an edge of `C`
traversed twice, an edge traversed three times); every other valid pattern has a certificate (`checkCert610`): a
triangle or a 4-cycle in the union `U` of `C` and the walk, two 6-cycles of `U` with a common vertex and different
edges, or a 6-cycle and an 8-cycle of `U` with a common edge.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

/-! ## Labels and the union -/

/-- The labels of the whole walk. -/
def wl (xs : List ℕ) : List ℕ := [0, 1, 2, 3, 4] ++ xs

/-- The label at position `t`. -/
def wlAt (xs : List ℕ) (t : ℕ) : ℕ := (wl xs).getD (t % 10) 0

/-- The step `t` and the step `u` use the same edge. -/
def sameStep (xs : List ℕ) (t u : ℕ) : Bool :=
  decide ((wlAt xs t = wlAt xs u ∧ wlAt xs (t + 1) = wlAt xs (u + 1)) ∨
    (wlAt xs t = wlAt xs (u + 1) ∧ wlAt xs (t + 1) = wlAt xs u))

/-- `ab` is an edge of the union of `C` and the walk. -/
def uEdgeB610 (xs : List ℕ) (a b : ℕ) : Bool :=
  cEdgeB a b || (List.range 10).any fun t =>
    decide ((a = wlAt xs t ∧ b = wlAt xs (t + 1)) ∨ (b = wlAt xs t ∧ a = wlAt xs (t + 1)))

/-- The label `l` occurs. -/
def usedB610 (xs : List ℕ) (l : ℕ) : Bool := decide (l < 6) || xs.contains l

/-- The pattern is consistent: each new label first occurs at its own position. -/
def validB610 (xs : List ℕ) : Bool :=
  decide (xs.length = 5) && (List.range 5).all fun k =>
    decide (xs.getD k 0 < 6 ∨ xs.getD k 0 = k + 6 ∨ ∃ k' < k, xs.getD k 0 = k' + 6 ∧ xs.getD k' 0 = k' + 6)

/-- The number of steps that use the same edge as step `t` (step `t` included). -/
def stepMult (xs : List ℕ) (t : ℕ) : ℕ := ((List.range 10).filter fun u => sameStep xs t u).length

/-- The walk cannot be a facial walk along `C`: a step joins equal labels, a step is reversed at once, an edge of `C`
is traversed twice, or an edge is traversed three times. -/
def violB (xs : List ℕ) : Bool :=
  (List.range 10).any (fun t => decide (wlAt xs t = wlAt xs (t + 1))) ||
  (List.range 10).any (fun t => decide (wlAt xs t = wlAt xs (t + 2))) ||
  (List.range 10).any (fun t => cEdgeB (wlAt xs t) (wlAt xs (t + 1)) && decide (2 ≤ stepMult xs t)) ||
  (List.range 10).any (fun t => decide (3 ≤ stepMult xs t))

/-- `c` is a cycle of length `k` in the union, on occurring labels. -/
def cycOK (xs : List ℕ) (k : ℕ) (c : List ℕ) : Bool :=
  decide (c.length = k) && decide c.Nodup && c.all (usedB610 xs) &&
    (List.range k).all fun i => uEdgeB610 xs (c.getD i 0) (c.getD ((i + 1) % k) 0)

/-- Edge `i` of the cycle `c` (length `k`) is edge `j` of the cycle `d` (length `l`). -/
def sameCEdge (k l : ℕ) (c d : List ℕ) (i j : ℕ) : Bool :=
  decide ((c.getD i 0 = d.getD j 0 ∧ c.getD ((i + 1) % k) 0 = d.getD ((j + 1) % l) 0) ∨
    (c.getD i 0 = d.getD ((j + 1) % l) 0 ∧ c.getD ((i + 1) % k) 0 = d.getD j 0))

/-- The check of a certificate `(kind, c, d)`. -/
def checkCert610 (xs : List ℕ) (cert : ℕ × List ℕ × List ℕ) : Bool :=
  match cert.1 with
  | 4 => cycOK xs 3 cert.2.1
  | 5 => cycOK xs 4 cert.2.1
  | 6 => cycOK xs 6 cert.2.1 && cycOK xs 6 cert.2.2 && cert.2.1.any (fun l => cert.2.2.contains l) &&
      (List.range 6).any fun i => !((List.range 6).any fun j => sameCEdge 6 6 cert.2.1 cert.2.2 i j)
  | 7 => cycOK xs 6 cert.2.1 && cycOK xs 8 cert.2.2 &&
      (List.range 6).any fun i => (List.range 8).any fun j => sameCEdge 6 8 cert.2.1 cert.2.2 i j
  | _ => false

end Thrackle78.Proof
