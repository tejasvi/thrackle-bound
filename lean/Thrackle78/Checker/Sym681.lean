import Thrackle78.Checker.Aut
import Thrackle78.Checker.Filter
import Thrackle78.Hyp

/-!
# The symmetry of `DB(6,8,-1)` (listing `lDB681` as run)

The vertex automorphism `(0 1)(2 5)(3 4)(6 11)(7 10)(8 9)` of `DB(6,8,-1)` maps edge `e` to edge `σ681 e` (an
involution), reversed unless `e ∈ {1, 5}`. Every planar crossing system has a planar image under it (`planar_aut`), and
the restriction to `R681 = [0, 1, 2, 3, 4, 5, 9]` of one of the two is lexicographically at most its image
(`hsym681_core`): the symmetry hypothesis of the symmetry-reduced search.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78

/-- The edge map of the symmetry (an involution of `0 … 12`, the identity beyond). -/
def σ681 : ℕ → ℕ
  | 1 => 5 | 2 => 4 | 4 => 2 | 5 => 1 | 6 => 12 | 7 => 11 | 8 => 10 | 10 => 8 | 11 => 7 | 12 => 6 | e => e

/-- The edges reversed by the symmetry. -/
def flip681 : ℕ → Bool
  | 1 => false | 5 => false | _ => true

/-- The edges whose rows are compared. -/
def R681 : List ℕ := [0, 1, 2, 3, 4, 5, 9]

/-- The vertex map of the symmetry. -/
def τ681 : ℕ → ℕ
  | 0 => 1 | 1 => 0 | 2 => 5 | 3 => 4 | 4 => 3 | 5 => 2 | 6 => 11 | 7 => 10 | 8 => 9 | 9 => 8 | 10 => 7 | 11 => 6
  | v => v

lemma σ681_big {e : ℕ} (h : 13 ≤ e) : σ681 e = e := by
  unfold σ681; split <;> omega

lemma σ681_invol (e : ℕ) : σ681 (σ681 e) = e := by
  rcases Nat.lt_or_ge e 13 with h | h
  · interval_cases e <;> rfl
  · rw [σ681_big h, σ681_big h]

lemma σ681_lt {e : ℕ} (h : e < 13) : σ681 e < 13 := by
  interval_cases e <;> decide

lemma τ681_invol {v : ℕ} (h : v < 12) : τ681 (τ681 v) = v := by
  interval_cases v <;> rfl

lemma τ681_lt {v : ℕ} (h : v < 12) : τ681 v < 12 := by
  interval_cases v <;> decide

lemma flip681_σ (e : ℕ) : flip681 (σ681 e) = flip681 e := by
  rcases Nat.lt_or_ge e 13 with h | h
  · interval_cases e <;> rfl
  · rw [σ681_big h]

lemma R681_σ (f : ℕ) : R681.contains (σ681 f) = R681.contains f := by
  rcases Nat.lt_or_ge f 13 with h | h
  · interval_cases f <;> rfl
  · rw [σ681_big h]

lemma lDB681_length : lDB681.length = 13 := rfl

/-- The edge map as a permutation of the edges. -/
def σE681 : Fin lDB681.length ≃ Fin lDB681.length where
  toFun e := ⟨σ681 e.val, (σ681_lt (lt_of_lt_of_eq e.isLt lDB681_length) : σ681 e.val < 13)⟩
  invFun e := ⟨σ681 e.val, (σ681_lt (lt_of_lt_of_eq e.isLt lDB681_length) : σ681 e.val < 13)⟩
  left_inv e := Fin.ext (σ681_invol e.val)
  right_inv e := Fin.ext (σ681_invol e.val)

/-- The vertex map as a permutation of the vertices. -/
def τE681 : Fin 12 ≃ Fin 12 where
  toFun v := ⟨τ681 v.val, τ681_lt v.isLt⟩
  invFun v := ⟨τ681 v.val, τ681_lt v.isLt⟩
  left_inv v := Fin.ext (τ681_invol v.isLt)
  right_inv v := Fin.ext (τ681_invol v.isLt)

/-- The reversed edges. -/
def flE681 (e : Fin lDB681.length) : Bool := flip681 e.val

/-- The symmetry is an automorphism of the listing. -/
theorem isAut681 : IsAut (mkE 12 lDB681) σE681 τE681 flE681 := by
  unfold IsAut
  decide

/-- The rows of the image system. -/
lemma πN_aut681 (P : CrossingSystem (mkE 12 lDB681)) (e : ℕ) (he : e < 13) :
    πN (P.aut σE681 τE681 flE681 isAut681) e =
      if flip681 (σ681 e) then ((πN P (σ681 e)).map σ681).reverse else (πN P (σ681 e)).map σ681 := by
  have he' : e < lDB681.length := he
  have hσ : σ681 e < lDB681.length := σ681_lt he
  unfold πN
  rw [dite_eq_left he', dite_eq_left hσ, aut_π]
  have hs : σE681.symm ⟨e, he'⟩ = ⟨σ681 e, hσ⟩ := rfl
  rw [hs]
  have hmap : ∀ l : List (Fin lDB681.length), (l.map σE681).map Fin.val = (l.map Fin.val).map σ681 := by
    intro l
    simp only [List.map_map]
    rfl
  unfold flE681
  split_ifs <;> simp only [List.map_reverse, hmap]

/-- The restriction of the rows of `R681` to `R681`. -/
def restr681 (row : ℕ → List ℕ) : List (List ℕ) := R681.map fun e => (row e).filter fun f => R681.contains f

/-- Its image under the symmetry. -/
def image681 (row : ℕ → List ℕ) : List (List ℕ) :=
  R681.map fun e =>
    let r := ((row (σ681 e)).filter fun f => R681.contains f).map σ681
    if flip681 (σ681 e) then r.reverse else r

lemma filter_map_σ (l : List ℕ) :
    (l.map σ681).filter (fun f => R681.contains f) = (l.filter fun f => R681.contains f).map σ681 := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro f _
  simp only [Function.comp, R681_σ]

lemma restr_aut681 (P : CrossingSystem (mkE 12 lDB681)) :
    restr681 (πN (P.aut σE681 τE681 flE681 isAut681)) = image681 (πN P) := by
  unfold restr681 image681
  apply List.map_congr_left
  intro e he
  have he13 : e < 13 := by simp [R681] at he; omega
  rw [πN_aut681 P e he13]
  split_ifs
  · rw [List.filter_reverse, filter_map_σ]
  · rw [filter_map_σ]

lemma image_aut681 (P : CrossingSystem (mkE 12 lDB681)) :
    image681 (πN (P.aut σE681 τE681 flE681 isAut681)) = restr681 (πN P) := by
  unfold restr681 image681
  apply List.map_congr_left
  intro e he
  have he13 : e < 13 := by simp [R681] at he; omega
  simp only
  rw [πN_aut681 P (σ681 e) (σ681_lt he13), σ681_invol, flip681_σ]
  have hid : ∀ l : List ℕ, (l.map σ681).map σ681 = l := fun l => by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id l]
    congr 1
    funext f
    exact σ681_invol f
  split_ifs
  · rw [List.filter_reverse, filter_map_σ, List.map_reverse, hid, List.reverse_reverse]
  · rw [filter_map_σ, hid]

/-- **The symmetry hypothesis for `lDB681`.** Every planar crossing system has a planar image whose restriction to
`R681` is lexicographically at most its image under the symmetry (the order of core `List`, as in `canonR`). -/
theorem hsym681_core : ∀ P : CrossingSystem (mkE 12 lDB681), Planar (aug (mkE 12 lDB681) P) →
    ∃ P', @LE.le (List (List ℕ)) List.instLE (restr681 (πN P')) (image681 (πN P')) ∧
      Planar (aug (mkE 12 lDB681) P') := by
  intro P hP
  rcases List.le_total (restr681 (πN P)) (image681 (πN P)) with hle | hle
  · exact ⟨P, hle, hP⟩
  · refine ⟨P.aut σE681 τE681 flE681 isAut681, ?_, planar_aut isAut681 P hP⟩
    rw [restr_aut681, image_aut681]
    exact hle

end Thrackle78.Checker
