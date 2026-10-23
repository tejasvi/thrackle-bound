import Thrackle78.Checker.Filter
import Thrackle78.Checker.Sym681

/-!
# Filters transfer along the symmetry of `DB(6,8,-1)`

If a filter `φ` (H-edges `g`, listed systems `sys`) is sound for `lDB681`, so is its image `autFilt σ681 flip681 φ`:
H-edges `σ g_i`, row `i` of every listed system reversed when `σ g_i` is flipped. For a planar `P`, the image
`Q = P.aut …` is planar, so `rowsH Q g` is listed, and `rowsH P (map σ g)` is `rowsH Q g` with those rows reversed.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78 Thrackle78Core

/-- The image of a filter under an edge map `σ` with flips `fl`: H-edges `σ g_i`, row `i` reversed when `fl (σ g_i)`. -/
def autFilt (σ : ℕ → ℕ) (fl : ℕ → Bool) (φ : Thrackle78Core.Filt) : Thrackle78Core.Filt :=
  ⟨φ.g.map σ, φ.sys.map fun s => (List.range φ.g.length).map fun i =>
    if fl (σ (φ.g.getD i 0)) then (s.getD i []).reverse else s.getD i []⟩

lemma mem_map_σ681 (g : List ℕ) (f : ℕ) : f ∈ g.map σ681 ↔ σ681 f ∈ g := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [σ681_invol]
  · intro h
    exact ⟨σ681 f, h, σ681_invol f⟩

lemma σ681_injective : Function.Injective σ681 := fun a b h => by
  rw [← σ681_invol a, h, σ681_invol]

lemma idxOf_map_σ681 (g : List ℕ) (f : ℕ) : (g.map σ681).idxOf f = g.idxOf (σ681 f) := by
  induction g with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih]
    congr 1
    have : (σ681 a == f) = (a == σ681 f) := by
      by_cases h : a = σ681 f
      · subst h; rw [σ681_invol]; simp
      · have h' : σ681 a ≠ f := fun e => h (by rw [← e, σ681_invol])
        simp [h, h']
    rw [this]

lemma getD_map_σ681 (g : List ℕ) (i : ℕ) (hi : i < g.length) : (g.map σ681).getD i 0 = σ681 (g.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

lemma getD_range_map {α : Type} (n i : ℕ) (hi : i < n) (F : ℕ → List α) :
    ((List.range n).map F).getD i [] = F i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

/-- **Filters transfer along the symmetry of `lDB681`.** -/
theorem filtSound_aut681 (φ : Thrackle78Core.Filt) (hg : ∀ x ∈ φ.g, x < 13) (h : FiltSound (mkE 12 lDB681) φ) :
    FiltSound (mkE 12 lDB681) (autFilt σ681 flip681 φ) := by
  intro P
  by_cases hP : Planar (aug (mkE 12 lDB681) P)
  · right
    have hQ := planar_aut isAut681 P hP
    rcases h (P.aut σE681 τE681 flE681 isAut681) with hn | hmem
    · exact absurd hQ hn
    · show rowsH P (φ.g.map σ681) ∈ φ.sys.map _
      have key : rowsH P (φ.g.map σ681) = (List.range φ.g.length).map fun i =>
          if flip681 (σ681 (φ.g.getD i 0)) then
            ((rowsH (P.aut σE681 τE681 flE681 isAut681) φ.g).getD i []).reverse
          else (rowsH (P.aut σE681 τE681 flE681 isAut681) φ.g).getD i [] := by
        unfold rowsH
        rw [List.length_map]
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        have hgi : φ.g.getD i 0 ∈ φ.g := by
          rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
        have h13 := hg _ hgi
        rw [getD_map_σ681 φ.g i hi, getD_range_map _ i hi, πN_aut681 P _ h13]
        have hfilt : ∀ l : List ℕ, (l.map σ681).filter (fun f => φ.g.contains f) =
            (l.filter fun f => (φ.g.map σ681).contains f).map σ681 := by
          intro l
          rw [List.filter_map]
          congr 1
          apply List.filter_congr
          intro f _
          simp only [Function.comp]
          by_cases hm : σ681 f ∈ φ.g
          · have h2 : f ∈ φ.g.map σ681 := (mem_map_σ681 _ _).2 hm
            simp [hm, h2]
          · have h2 : f ∉ φ.g.map σ681 := fun h => hm ((mem_map_σ681 _ _).1 h)
            simp [hm, h2]
        have hlab : ∀ l : List ℕ, (l.map σ681).map (labOf φ.g) = l.map (labOf (φ.g.map σ681)) := by
          intro l
          rw [List.map_map]
          apply List.map_congr_left
          intro f _
          simp only [Function.comp, labOf, idxOf_map_σ681]
        split_ifs with hf
        · rw [List.filter_reverse, hfilt, List.map_reverse, hlab, List.reverse_reverse]
        · rw [hfilt, hlab]
      rw [key]
      exact List.mem_map_of_mem hmem
  · exact Or.inl hP

end Thrackle78.Checker
