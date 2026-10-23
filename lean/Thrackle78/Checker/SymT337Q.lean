import Thrackle78.Checker.SymT337

/-!
# The symmetry hypothesis for `lTH337` in the form of `not_combThr_mkE_of_topBSymLFX`

The edge maps, flips and compared edges under the names of the symmetry-reduced search (a list of symmetries), with
`hsym337`, its side conditions, and the filter transfer along `a`, from `SymT337`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78

def σa337 : ℕ → ℕ
  | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 0 | 4 => 1 | 5 => 2 | e => e
def σb337 : ℕ → ℕ
  | 0 => 2 | 2 => 0 | 3 => 5 | 5 => 3 | 6 => 12 | 7 => 11 | 8 => 10 | 10 => 8 | 11 => 7 | 12 => 6 | e => e
def σab337 : ℕ → ℕ
  | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0 | 6 => 12 | 7 => 11 | 8 => 10 | 10 => 8 | 11 => 7 | 12 => 6 | e => e
def flipa337 : ℕ → Bool := fun _ => false
def flipb337 : ℕ → Bool := fun _ => true
def flipab337 : ℕ → Bool := fun _ => true
def R337 : List ℕ := [0, 1, 2, 3, 4, 5, 9]
def syms337 : List ((ℕ → ℕ) × (ℕ → Bool)) := [(σa337, flipa337), (σb337, flipb337), (σab337, flipab337)]

lemma σa337_eq : σa337 = σaT := by
  funext e
  rcases Nat.lt_or_ge e 13 with h | h
  · interval_cases e <;> rfl
  · rw [σaT_big h]; unfold σa337; split <;> omega

lemma σb337_eq : σb337 = σbT := by
  funext e
  rcases Nat.lt_or_ge e 13 with h | h
  · interval_cases e <;> rfl
  · rw [σbT_big h]; unfold σb337; split <;> omega

lemma σab337_eq : σab337 = σabT := by
  funext e
  rcases Nat.lt_or_ge e 13 with h | h
  · interval_cases e <;> rfl
  · rw [σabT_big h]; unfold σab337; split <;> omega

/-- **`hsym` for `lTH337`** with the list of symmetries `syms337`. -/
theorem hsym337 : ∀ P : CrossingSystem (mkE 12 lTH337), Planar (aug (mkE 12 lTH337) P) →
    ∃ P', (∀ s ∈ syms337, QSym R337 s.1 s.2 P') ∧ Planar (aug (mkE 12 lTH337) P') := by
  intro P hP
  obtain ⟨P', ⟨ha, hb, hab⟩, hP'⟩ := hsymT337 P hP
  refine ⟨P', fun s hs => ?_, hP'⟩
  simp only [syms337, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · rw [σa337_eq]; exact ha
  · rw [σb337_eq]; exact hb
  · rw [σab337_eq]; exact hab

/-- The side conditions for `K = 10`. -/
theorem hR337 : ∀ e ∈ R337, e < 10 := by decide

theorem hσR337 : ∀ s ∈ syms337, ∀ e ∈ R337, s.1 e ∈ R337 := by decide

/-- **Filters transfer along `a`**: if `φ` is sound for `lTH337`, so is `autFilt σa337 flipa337 φ`. -/
theorem filtSound_aut337a (φ : Thrackle78Core.Filt) (hg : ∀ x ∈ φ.g, x < 13) (h : FiltSound (mkE 12 lTH337) φ) :
    FiltSound (mkE 12 lTH337) (autFilt σa337 flipa337 φ) := by
  rw [σa337_eq]
  exact filtSound_autT337a φ hg h

end Thrackle78.Checker
