import Thrackle78Core.Native
import Thrackle78.Checker.MkE

/-!
# Soundness of the search with a certificate finder, and of sharding

`walkN_sound`: whatever the finder, an accepted search from a state proves non-planarity for every crossing system
extending it. `walkS_sound`: if the top of the tree reaches only shard roots `L` and every shard root is sound, so is
the root. `not_combThr_mkE_of_checkN`, `not_combThr_mkE_of_shards`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- Every crossing system extending the state `(k, rows)` has a non-planar augmented graph. -/
def StateSound (E : Fin m → Fin n × Fin n) (k : ℕ) (rows : Array (List ℕ)) : Prop :=
  ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → ¬ Planar (aug E P)

/-- **Soundness of the search with a certificate finder.** -/
theorem walkN_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (find : ℕ → Array (List ℕ) → Option MinorCert) :
    ∀ fuel k rows, walkN n es find fuel k rows = true → StateSound E k rows
  | 0, _, _, h => by simp [walkN] at h
  | fuel + 1, k, rows, h => by
    intro P t hr
    simp only [walkN, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hk, h⟩
    · cases hf : find k rows with
      | none => rw [hf] at h; exact absurd h (by simp)
      | some c =>
        rw [hf] at h
        exact not_planar_aug_of_state P k t hes hr (not_planar_of_checkMinor h)
    · have hk' : k < m := hes.size ▸ hk
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at h
        exact walkN_sound hes find fuel (k + 1) rows h P 0 (restr_close P hes hr hk' h8)
      · rw [ite_eq_right h8, List.all_eq_true] at h
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        exact walkN_sound hes find fuel k r' (h r' hr') P (t + 1) hres

/-- **Soundness of sharding.** -/
theorem walkS_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (L : List (ℕ × Array (List ℕ)))
    (hL : ∀ s ∈ L, StateSound E s.1 s.2) :
    ∀ d k rows, walkS es L d k rows = true → StateSound E k rows
  | 0, k, rows, h => by
    simp only [walkS, List.contains_iff_mem] at h
    exact hL _ h
  | d + 1, k, rows, h => by
    intro P t hr
    simp only [walkS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
    rcases h with h | ⟨hk, h⟩
    · exact hL _ h P t hr
    · have hk' : k < m := hes.size ▸ hk
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at h
        exact walkS_sound hes L hL d (k + 1) rows h P 0 (restr_close P hes hr hk' h8)
      · rw [ite_eq_right h8, List.all_eq_true] at h
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        exact walkS_sound hes L hL d k r' (h r' hr') P (t + 1) hres

theorem not_combThr_of_rootSound {es : Array (ℕ × ℕ)} (hes : Matches es E)
    (h : StateSound E 0 (Array.replicate es.size [])) : ¬ CombThr E := by
  rintro ⟨P, hP⟩
  rw [hes.size] at h
  exact h P 0 (restr_root P) hP

/-- **The search with a certificate finder proves `¬ CombThr (mkE n l)`.** -/
theorem not_combThr_mkE_of_checkN (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (find : ℕ → Array (List ℕ) → Option MinorCert) (h : checkN n l.toArray find = true) : ¬ CombThr (mkE n l) :=
  not_combThr_of_rootSound (matches_mkE n l hl) (walkN_sound (matches_mkE n l hl) find _ _ _ h)

/-- **Sharded search**: the top of the tree reaches only the shard roots `L`, and the search from every shard root
is accepted. -/
theorem not_combThr_mkE_of_shards (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (L : List (ℕ × Array (List ℕ))) (d : ℕ)
    (htop : walkS l.toArray L d 0 (Array.replicate l.length []) = true)
    (find : ℕ → Array (List ℕ) → Option MinorCert) (fuel : ℕ)
    (hsh : ∀ s ∈ L, walkN n l.toArray find fuel s.1 s.2 = true) : ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  apply not_combThr_of_rootSound hes
  have := walkS_sound hes L (fun s hs => walkN_sound hes find fuel s.1 s.2 (hsh s hs)) d 0 _
    (by simpa using htop)
  simpa using this

end Thrackle78.Checker

namespace Thrackle78.Checker

/-- Shard batches: if every batch passes `List.all`, every shard root of the concatenation passes. -/
theorem forall_mem_flatten_of_all {α : Type} (p : α → Bool) (Ls : List (List α))
    (h : ∀ L ∈ Ls, L.all p = true) : ∀ s ∈ Ls.flatten, p s = true := by
  intro s hs
  obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
  exact List.all_eq_true.1 (h L hL) s hsL

end Thrackle78.Checker
