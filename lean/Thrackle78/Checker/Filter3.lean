import Thrackle78Core.FilterI
import Thrackle78.Checker.Filter2

/-!
# Filters with incremental compatible sets

`walkI_sound`: as `walkG_sound`, for the walk that carries the compatible sets; the invariant `AliveOK` (the carried
set of every filter contains the restriction of the crossing system, if listed) is kept because the restriction is
compatible with every state it extends (`compat_rowsH`). `not_combThr_mkE_of_checkI`: the check with incremental
filters proves `¬ CombThr (mkE n l)`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- The carried sets contain the restriction of `P` to each filter, when it is listed. -/
def AliveOK (P : CrossingSystem E) (fs : List Filt) (alive : List (List (List (List ℕ)))) : Prop :=
  ∀ i < fs.length, rowsH P (fs.getD i ⟨[], []⟩).g ∈ (fs.getD i ⟨[], []⟩).sys →
    rowsH P (fs.getD i ⟨[], []⟩).g ∈ alive.getD i []

theorem getD_mem_of_lt {α : Type} {l : List α} {i : ℕ} (d : α) (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem aliveOK_aliveAt (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows)
    (fs : List Filt) (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) {alive : List (List (List (List ℕ)))}
    (ha : AliveOK P fs alive) : AliveOK P fs (aliveAt fs alive k rows) := by
  intro i hi hmem
  unfold aliveAt
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range, List.mem_filter]
  refine ⟨ha i hi hmem, ?_⟩
  obtain ⟨hval, -⟩ := hfs _ (getD_mem_of_lt ⟨[], []⟩ hi)
  unfold Filt.valid at hval
  rw [Bool.and_eq_true, nodupB_iff, List.all_eq_true] at hval
  exact compat_rowsH P hr hval.1 (fun x hx => by simpa using hval.2 x hx)

/-- **Soundness of the tree walk with incremental filters.** -/
theorem walkI_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (h : ℕ) (hh : h ≤ m) (S : List (List (List ℕ)))
    (fs : List Filt) (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (rd : ReaderX) :
    ∀ fuel k rows alive pos r, walkI n es h S fs rd fuel k rows alive pos = some r →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → AliveOK P fs alive →
        ¬ Planar (aug E P) ∨ listedRows P h ∈ S
  | 0, _, _, _, _, _, hw => by simp [walkI] at hw
  | fuel + 1, k, rows, alive, pos, r, hw => by
    intro P t hr ha
    have hal := aliveOK_aliveAt P hr fs hfs ha
    simp only [walkI] at hw
    by_cases h1 : (rd.tag pos).1 = 1
    · rw [ite_eq_left h1] at hw
      by_cases h2 : checkMinor (stateGraph n es k rows) (rd.cert (rd.tag pos).2).1 = true
      · exact Or.inl (not_planar_aug_of_state P k t hes hr (not_planar_of_checkMinor h2))
      · rw [ite_eq_right h2] at hw; exact absurd hw (by simp)
    · rw [ite_eq_right h1] at hw
      by_cases h3 : (rd.tag pos).1 = 3
      · rw [ite_eq_left h3] at hw
        by_cases h4 : k = h ∧ rows.getD h [] = [] ∧ (rd.num (rd.tag pos).2).1 < S.length ∧
            (List.range h).map (fun e => rows.getD e []) = S.getD (rd.num (rd.tag pos).2).1 []
        · -- the same argument as for `walkG`: run `walkG` on a one-node certificate
          have hw' : walkG n es h S fs rd (0 + 1) k rows pos = some (rd.num (rd.tag pos).2).2 := by
            simp only [walkG]
            rw [ite_eq_right h1, ite_eq_left h3, ite_eq_left h4]
          exact walkG_sound hes h hh S fs hfs rd 1 k rows pos _ hw' P t hr
        · rw [ite_eq_right h4] at hw; exact absurd hw (by simp)
      · rw [ite_eq_right h3] at hw
        by_cases h5 : (rd.tag pos).1 = 4
        · rw [ite_eq_left h5] at hw
          by_cases h6 : (rd.num (rd.tag pos).2).1 < fs.length ∧
              (aliveAt fs alive k rows).getD (rd.num (rd.tag pos).2).1 [] = []
          · refine Or.inl ?_
            obtain ⟨hi, hempty⟩ := h6
            set φ := fs.getD (rd.num (rd.tag pos).2).1 ⟨[], []⟩ with hφ
            obtain ⟨-, hsound⟩ := hfs φ (getD_mem_of_lt _ hi)
            rcases hsound P with hnp | hmem
            · exact hnp
            · exfalso
              have := hal _ hi hmem
              rw [hempty] at this
              simp at this
          · rw [ite_eq_right h6] at hw; exact absurd hw (by simp)
        · rw [ite_eq_right h5] at hw
          by_cases h7 : (rd.tag pos).1 = 0 ∧ k < h
          · rw [ite_eq_left h7] at hw
            have hk : k < m := by omega
            by_cases h8 : (rows.getD k []).length = numEarlier es k
            · rw [ite_eq_left h8] at hw
              exact walkI_sound hes h hh S fs hfs rd fuel (k + 1) rows _ _ r hw P 0
                (restr_close P hes hr hk h8) hal
            · rw [ite_eq_right h8] at hw
              obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk h8
              obtain ⟨p, q, hpq⟩ := foldl_bind_some
                (fun r p => walkI n es h S fs rd fuel k r (aliveAt fs alive k rows) p) _ _ _ hw r' hr'
              exact walkI_sound hes h hh S fs hfs rd fuel k r' _ p q hpq P (t + 1) hres hal
          · rw [ite_eq_right h7] at hw; exact absurd hw (by simp)

/-- **Soundness of the check with incremental filters.** -/
theorem not_combThr_of_checkI {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List (Filt × ReaderX))
    (rd : ReaderX) (h : checkI n es fs rd = true) : ¬ CombThr E := by
  rintro ⟨P, hP⟩
  unfold checkI at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hfs, hw⟩ := h
  have hfs' : ∀ φ ∈ fs.map Prod.fst, φ.valid m = true ∧ FiltSound E φ := by
    intro φ hφ
    obtain ⟨⟨φ', rdφ⟩, hmem, rfl⟩ := List.mem_map.1 hφ
    exact filtSound_of_checkFilter hes φ' rdφ (hfs _ hmem)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
  rw [hes.size] at hr
  have ha0 : AliveOK P (fs.map Prod.fst) (fs.map fun φr => φr.1.sys) := by
    intro i hi hmem
    have hi' : i < fs.length := by simpa using hi
    rw [List.getD_eq_getElem _ _ hi] at hmem ⊢
    rw [List.getD_eq_getElem _ _ (by simpa using hi')]
    simpa using hmem
  rcases walkI_sound hes m le_rfl [] _ hfs' rd _ 0 _ _ 0 r hr P 0 (restr_root P) ha0 with hnp | hl
  · exact hnp hP
  · simp at hl

/-- **Soundness of the check with incremental filters for the computed listings.** -/
theorem not_combThr_mkE_of_checkI (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × ReaderX)) (rd : ReaderX) (h : checkI n l.toArray fs rd = true) : ¬ CombThr (mkE n l) :=
  not_combThr_of_checkI (matches_mkE n l hl) fs rd h

end Thrackle78.Checker
