import Mathlib

/-!
# List and array lemmas used by the soundness proof of the checker
-/

namespace Thrackle78.Checker

/-- `Array.getD` after `set!`. -/
theorem getD_set!_eq {α : Type} (a : Array α) (i j : ℕ) (v d : α) :
    (a.set! i v).getD j d = if i = j ∧ j < a.size then v else a.getD j d := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by simpa using hj
    rw [Array.getD, Array.getD, dite_eq_left_of_eq_true (eq_true hj'), dite_eq_left_of_eq_true (eq_true hj)]
    simp only [Array.set!]
    by_cases hij : i = j <;> simp [hij, hj]
  · simp [Array.getD, hj]

/-- A sublist of a duplicate-free list is the filter of its members. -/
theorem filter_mem_eq_of_sublist {α : Type} [DecidableEq α] {s l : List α} (h : s.Sublist l) (hl : l.Nodup) :
    l.filter (fun y => decide (y ∈ s)) = s := by
  induction h with
  | slnil => rfl
  | @cons l₁ l₂ a h ih =>
    rw [List.nodup_cons] at hl
    have ha : a ∉ l₁ := fun h' => hl.1 (h.subset h')
    simp [ha, ih hl.2]
  | @cons_cons l₁ l₂ a h ih =>
    rw [List.nodup_cons] at hl
    rw [List.filter_cons, ite_eq_left (by simp)]
    congr 1
    rw [← ih hl.2]
    apply List.filter_congr
    intro y hy
    have hya : y ≠ a := fun e => hl.1 (e ▸ hy)
    simp [hya, hy]

/-- The position of an element in a filter of a duplicate-free list. -/
theorem idxOf_filter {α : Type} [DecidableEq α] (p : α → Bool) {x : α} :
    ∀ {l : List α}, l.Nodup → x ∈ l → p x = true → (l.filter p).idxOf x = (l.take (l.idxOf x)).countP p
  | [], _, hx, _ => absurd hx (by simp)
  | y :: l, hl, hx, hp => by
    rw [List.nodup_cons] at hl
    by_cases hyx : y = x
    · subst hyx
      simp [hp, List.idxOf_cons_self]
    · have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hyx
        · exact h
      rw [List.idxOf_cons_ne l hyx, List.take_succ_cons, List.countP_cons, List.filter_cons]
      by_cases hpy : p y = true
      · rw [ite_eq_left hpy, List.idxOf_cons_ne _ hyx, idxOf_filter p hl.2 hx' hp]
        simp [hpy]
      · rw [ite_eq_right hpy, idxOf_filter p hl.2 hx' hp]
        simp [hpy]

/-- Inserting `x` into a filter of a duplicate-free list: the filter by `q ∨ (· = x)`. -/
theorem filter_or_eq_insert {α : Type} [DecidableEq α] (q : α → Bool) {x : α} :
    ∀ {l : List α}, l.Nodup → x ∈ l → q x = false →
      l.filter (fun y => q y || decide (y = x)) =
        (l.filter q).take ((l.take (l.idxOf x)).countP q) ++ x :: (l.filter q).drop ((l.take (l.idxOf x)).countP q)
  | [], _, hx, _ => absurd hx (by simp)
  | y :: l, hl, hx, hq => by
    rw [List.nodup_cons] at hl
    by_cases hyx : y = x
    · subst hyx
      have hrest : l.filter (fun y' => q y' || decide (y' = y)) = l.filter q := by
        apply List.filter_congr
        intro z hz
        have : z ≠ y := fun e => hl.1 (e ▸ hz)
        simp [this]
      simp [hq, List.idxOf_cons_self, hrest]
    · have hx' : x ∈ l := by
        rcases List.mem_cons.1 hx with h | h
        · exact absurd h.symm hyx
        · exact h
      have ih := filter_or_eq_insert q hl.2 hx' hq
      rw [List.idxOf_cons_ne l hyx, List.take_succ_cons, List.countP_cons]
      by_cases hqy : q y = true
      · simp only [List.filter_cons, hqy, Bool.true_or, ite_true, ih]
        simp
      · have hqy' : q y = false := by simpa using hqy
        simp only [List.filter_cons, hqy', Bool.false_or, decide_eq_true_eq, hyx, ite_false, ih]
        simp

/-- A discrete intermediate value step: a function with increments at most one crosses every level. -/
theorem exists_step (f : ℕ → ℕ) (i a : ℕ) :
    ∀ b, a ≤ b → f a ≤ i → i < f b → (∀ p, a ≤ p → p < b → f (p + 1) ≤ f p + 1) →
      ∃ p, a ≤ p ∧ p < b ∧ f p = i ∧ f (p + 1) = i + 1
  | 0, hab, ha, hb, _ => by
    have : a = 0 := by omega
    subst this; omega
  | b + 1, hab, ha, hb, hstep => by
    by_cases hfb : f b ≤ i
    · have hb' : a ≤ b := by
        rcases Nat.eq_or_lt_of_le hab with h | h
        · rw [← h] at hb; omega
        · omega
      have := hstep b hb' (by omega)
      exact ⟨b, hb', by omega, by omega, by omega⟩
    · have hb' : a ≤ b := by
        rcases Nat.eq_or_lt_of_le hab with h | h
        · subst h; omega
        · omega
      obtain ⟨p, h1, h2, h3, h4⟩ := exists_step f i a b hb' ha (by omega)
        (fun p hp hpb => hstep p hp (by omega))
      exact ⟨p, h1, by omega, h3, h4⟩

end Thrackle78.Checker
