import Thrackle78.Checker.Bridge3

/-!
# Soundness of the search-tree check

`walk_sound`: if `walk` accepts the subtree of a state, then every crossing system whose restriction to some stage is
that state has a non-planar augmented graph (pruned nodes by `not_planar_aug_of_state`, closing by `restr_close`,
the children by `restr_child`). `not_combThr_of_check`: an accepted check of a listing `es` matching `E` proves
`¬ CombThr E`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

theorem foldl_bind_none {α β : Type} (g : α → β → Option β) :
    ∀ l : List α, l.foldl (fun acc x => acc.bind (g x)) none = none
  | [] => rfl
  | _ :: l => foldl_bind_none g l

theorem foldl_bind_some {α β : Type} (g : α → β → Option β) :
    ∀ (l : List α) (b r : β), l.foldl (fun acc x => acc.bind (g x)) (some b) = some r →
      ∀ x ∈ l, ∃ p q, g x p = some q
  | [], _, _, _, x, hx => absurd hx (by simp)
  | y :: l, b, r, h, x, hx => by
    rw [List.foldl_cons, Option.bind_some] at h
    cases hy : g y b with
    | none => rw [hy, foldl_bind_none] at h; exact absurd h (by simp)
    | some b' =>
      rw [hy] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, b', hy⟩
      · exact foldl_bind_some g l b' r h x hx

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- **Soundness of the tree walk.** -/
theorem walk_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (rd : Reader) :
    ∀ fuel k rows pos r, walk n es rd fuel k rows pos = some r →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → ¬ Planar (aug E P)
  | 0, _, _, _, _, h => by simp [walk] at h
  | fuel + 1, k, rows, pos, r, h => by
    intro P t hr
    simp only [walk] at h
    by_cases h1 : (rd.tag pos).1 = 1
    · rw [ite_eq_left h1] at h
      by_cases h2 : checkMinor (stateGraph n es k rows) (rd.cert (rd.tag pos).2).1 = true
      · exact not_planar_aug_of_state P k t hes hr (not_planar_of_checkMinor h2)
      · rw [ite_eq_right h2] at h; exact absurd h (by simp)
    · rw [ite_eq_right h1] at h
      by_cases h3 : (rd.tag pos).1 = 0 ∧ k < es.size
      · rw [ite_eq_left h3] at h
        have hk : k < m := hes.size ▸ h3.2
        by_cases h4 : (rows.getD k []).length = numEarlier es k
        · rw [ite_eq_left h4] at h
          exact walk_sound hes rd fuel (k + 1) rows _ r h P 0 (restr_close P hes hr hk h4)
        · rw [ite_eq_right h4] at h
          obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk h4
          obtain ⟨p, q, hpq⟩ := foldl_bind_some (fun r p => walk n es rd fuel k r p) _ _ _ h r' hr'
          exact walk_sound hes rd fuel k r' p q hpq P (t + 1) hres
      · rw [ite_eq_right h3] at h; exact absurd h (by simp)

/-- **Soundness of the check**: an accepted certificate proves that the listing is not combinatorially
thrackleable. -/
theorem not_combThr_of_check {es : Array (ℕ × ℕ)} (hes : Matches es E) (rd : Reader) (h : check n es rd = true) :
    ¬ CombThr E := by
  rintro ⟨P, hP⟩
  unfold check at h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h
  rw [hes.size] at hr
  exact walk_sound hes rd _ 0 _ 0 r hr P 0 (restr_root P) hP

end Thrackle78.Checker
