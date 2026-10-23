import Thrackle78.Checker.Sym681
import Thrackle78.Checker.FilterBQ

/-!
# The symmetry hypothesis for `lDB681` in the form of `not_combThr_mkE_of_topBSym`
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78

/-- **`hsym` for `lDB681`**, with `R681`, `σ681`, `flip681`. -/
theorem hsym681 : ∀ P : CrossingSystem (mkE 12 lDB681), Planar (aug (mkE 12 lDB681) P) →
    ∃ P', QSym R681 σ681 flip681 P' ∧ Planar (aug (mkE 12 lDB681) P') := fun P hP =>
  let ⟨P', h1, h2⟩ := hsym681_core P hP
  ⟨P', decide_eq_true h1, h2⟩

/-- The side conditions of `not_combThr_mkE_of_topBSym` for `K = 10`. -/
theorem hR681 : ∀ e ∈ R681, e < 10 := by decide

theorem hσR681 : ∀ e ∈ R681, σ681 e ∈ R681 := by decide

end Thrackle78.Checker
