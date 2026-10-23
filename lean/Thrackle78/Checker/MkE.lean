import Thrackle78.Hyp
import Thrackle78.Checker.Tree

/-!
# The checker for the listings `mkE n l` of `Thrackle78.Hyp`

`not_combThr_mkE_of_check`: if the check of the listing `l` (pairs of vertices `< n`, as run) accepts a certificate,
then `¬ CombThr (mkE n l)`, which is the form of the computational hypotheses of `Thrackle78.thrackle_bound`.
-/

namespace Thrackle78.Checker

open Thrackle78Core

/-- A listing of pairs below `n` matches `mkE n l`. -/
theorem matches_mkE (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n) :
    Matches l.toArray (mkE n l) where
  size := by simp
  get i := by
    have hi : i.val < l.length := i.isLt
    have hp : l[i.val].1 < n ∧ l[i.val].2 < n := hl _ (List.getElem_mem hi)
    simp only [mkE, Array.getD, List.size_toArray, hi, dite_true, Fin.val_ofNat, List.get_eq_getElem]
    rw [Nat.mod_eq_of_lt hp.1, Nat.mod_eq_of_lt hp.2]
    rfl

/-- **Soundness for the computed listings.** -/
theorem not_combThr_mkE_of_check (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (rd : Reader) (h : check n l.toArray rd = true) : ¬ CombThr (mkE n l) :=
  not_combThr_of_check (matches_mkE n l hl) rd h

end Thrackle78.Checker
