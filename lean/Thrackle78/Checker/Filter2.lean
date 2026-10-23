import Thrackle78.Checker.Filter
import Thrackle78.Checker.MkE

/-!
# Filters: the reordered listing, sound filter trees, and the check with filters

* `sigmaOf`: the permutation of the edges putting the H-edges first (core `reorderIdx`), with
  `matches_reorder : Matches (reorder es g) (E ∘ sigmaOf g)`;
* `listedRows_relabel`: the rows of the relabeled system at level `|g|` are the restriction to `H`;
* `filtSound_of_checkFilter`, `not_combThr_of_checkF`, `not_combThr_mkE_of_checkF`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

/-! ## The reordered listing -/

section Reorder

variable {m : ℕ} {g : List ℕ} (hg : g.Nodup) (hgm : ∀ x ∈ g, x < m)
include hg hgm

theorem reorderIdx_nodup : (reorderIdx m g).Nodup := by
  unfold reorderIdx
  rw [List.nodup_append]
  refine ⟨hg, List.nodup_range.filter _, fun a ha b hb hab => ?_⟩
  rw [List.mem_filter] at hb
  subst hab
  simp [List.contains_iff_mem, ha] at hb

theorem mem_reorderIdx {x : ℕ} : x ∈ reorderIdx m g ↔ x < m := by
  unfold reorderIdx
  rw [List.mem_append, List.mem_filter, List.mem_range]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact hgm x h
    · exact h
  · intro h
    by_cases hx : x ∈ g
    · exact Or.inl hx
    · exact Or.inr ⟨h, by simp [List.contains_iff_mem, hx]⟩

theorem reorderIdx_length : (reorderIdx m g).length = m := by
  have hp : (reorderIdx m g).Perm (List.range m) := by
    rw [List.perm_ext_iff_of_nodup (reorderIdx_nodup hg hgm) List.nodup_range]
    intro x
    rw [mem_reorderIdx hg hgm, List.mem_range]
  rw [hp.length_eq, List.length_range]

theorem length_le_of_reorder : g.length ≤ m := by
  have := reorderIdx_length hg hgm
  unfold reorderIdx at this
  rw [List.length_append] at this
  omega

theorem reorderIdx_getD_lt (i : ℕ) (hi : i < m) : (reorderIdx m g).getD i 0 < m := by
  have hl := reorderIdx_length hg hgm
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact (mem_reorderIdx hg hgm).1 (List.getElem_mem _)

omit hg hgm in
theorem reorderIdx_getD_of_lt (i : ℕ) (hi : i < g.length) : (reorderIdx m g).getD i 0 = g.getD i 0 := by
  unfold reorderIdx
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]

/-- The permutation of the edges with the H-edges first. -/
noncomputable def sigmaOf : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (fun i : Fin m => ⟨(reorderIdx m g).getD i 0, reorderIdx_getD_lt hg hgm i i.isLt⟩)
    (Finite.injective_iff_bijective.1 (by
      intro i j hij
      have hl := reorderIdx_length hg hgm
      simp only [Fin.mk.injEq] at hij
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hij
      exact Fin.ext ((reorderIdx_nodup hg hgm).getElem_inj_iff.1 hij)))

theorem sigmaOf_val (i : Fin m) : (sigmaOf hg hgm i).val = (reorderIdx m g).getD i 0 := rfl

theorem sigmaOf_symm (f : Fin m) :
    ((sigmaOf hg hgm).symm f).val < g.length ↔ f.val ∈ g := by
  have hf := congrArg Fin.val ((sigmaOf hg hgm).apply_symm_apply f)
  rw [sigmaOf_val] at hf
  set i := ((sigmaOf hg hgm).symm f).val with hi
  have hil : i < m := ((sigmaOf hg hgm).symm f).isLt
  have hl := reorderIdx_length hg hgm
  constructor
  · intro h
    rw [reorderIdx_getD_of_lt (m := m) i h, List.getD_eq_getElem _ _ h] at hf
    rw [← hf]; exact List.getElem_mem h
  · intro hfg
    by_contra hc
    have hlen2 : g.length + ((List.range m).filter (fun i => !g.contains i)).length = m := by
      have := reorderIdx_length hg hgm; unfold reorderIdx at this; rw [List.length_append] at this; exact this
    have hidx : i - g.length < ((List.range m).filter (fun i => !g.contains i)).length := by omega
    have hgetD : (reorderIdx m g).getD i 0 = ((List.range m).filter (fun i => !g.contains i))[i - g.length] := by
      unfold reorderIdx
      rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega), List.getElem_append_right (by omega)]
    rw [hgetD] at hf
    have hmem := List.getElem_mem hidx
    rw [hf, List.mem_filter] at hmem
    simp [hfg] at hmem

theorem sigmaOf_symm_eq (f : Fin m) (hf : f.val ∈ g) : ((sigmaOf hg hgm).symm f).val = labOf g f.val := by
  have hlt := (sigmaOf_symm hg hgm f).2 hf
  have h := congrArg Fin.val ((sigmaOf hg hgm).apply_symm_apply f)
  rw [sigmaOf_val, reorderIdx_getD_of_lt (m := m) _ hlt] at h
  rw [← h, labOf_getD hg hlt]

theorem sigmaOf_lt (i : Fin m) (hi : i.val < g.length) : (sigmaOf hg hgm i).val = g.getD i.val 0 := by
  rw [sigmaOf_val, reorderIdx_getD_of_lt (m := m) _ hi]

end Reorder

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

theorem matches_reorder {es : Array (ℕ × ℕ)} (hes : Matches es E) {g : List ℕ} (hg : g.Nodup)
    (hgm : ∀ x ∈ g, x < m) : Matches (reorder es g) (E ∘ sigmaOf hg hgm) where
  size := by
    unfold reorder
    rw [List.size_toArray, List.length_map, hes.size, reorderIdx_length hg hgm]
  get i := by
    have hl := reorderIdx_length hg hgm (m := m)
    have hi : i.val < (reorderIdx m g).length := by rw [hl]; exact i.isLt
    have hget := hes.get (sigmaOf hg hgm i)
    rw [sigmaOf_val, List.getD_eq_getElem _ _ hi] at hget
    show _ = ((E (sigmaOf hg hgm i)).1.val, (E (sigmaOf hg hgm i)).2.val)
    rw [← hget]
    unfold reorder
    rw [hes.size, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem hi]
    rfl

/-- The rows of the relabeled system at level `|g|` are the restriction to `H`. -/
theorem listedRows_relabel (P : CrossingSystem E) {g : List ℕ} (hg : g.Nodup) (hgm : ∀ x ∈ g, x < m) :
    listedRows (relabel (sigmaOf hg hgm) P) g.length = rowsH P g := by
  unfold listedRows rowsH
  apply List.map_congr_left
  intro e he
  rw [List.mem_range] at he
  have hem : e < m := lt_of_lt_of_le he (length_le_of_reorder hg hgm)
  simp only [hem, ↓reduceDIte]
  set σ := sigmaOf hg hgm with hσ
  have hσe : (σ ⟨e, hem⟩).val = g.getD e 0 := sigmaOf_lt hg hgm ⟨e, hem⟩ he
  rw [← hσe, πN_of_lt P (σ ⟨e, hem⟩).isLt]
  rw [rowAt, ite_eq_left (show (⟨e, hem⟩ : Fin m).val < g.length from he)]
  have hπ : (relabel σ P).π ⟨e, hem⟩ = (P.π (σ ⟨e, hem⟩)).map σ.symm := rfl
  have hfl : ((relabel σ P).π ⟨e, hem⟩).filter (fun f => decide (f.val < g.length ∨ (f.val = g.length ∧
      (⟨e, hem⟩ : Fin m) ∈ (earlier (relabel σ P) f).take 0))) =
      ((P.π (σ ⟨e, hem⟩)).filter (fun f => g.contains f.val)).map σ.symm := by
    rw [hπ, List.filter_map]
    congr 1
    apply List.filter_congr
    intro f _
    simp only [Function.comp, List.take_zero, List.not_mem_nil, and_false, or_false]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.contains_iff_mem]
    exact sigmaOf_symm hg hgm f
  rw [hfl, List.map_map, List.filter_map, List.map_map]
  apply List.map_congr_left
  intro f hf
  rw [List.mem_filter] at hf
  simp only [Function.comp]
  exact sigmaOf_symm_eq hg hgm f (List.contains_iff_mem.1 hf.2)

/-! ## Sound filters and the check with filters -/

/-- An accepted filter tree proves that the filter is sound. -/
theorem filtSound_of_checkFilter {es : Array (ℕ × ℕ)} (hes : Matches es E) (φ : Filt) (rd : ReaderX)
    (h : checkFilter n es φ rd = true) : φ.valid m = true ∧ FiltSound E φ := by
  unfold checkFilter at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hval, hw⟩ := h
  rw [hes.size] at hval hw
  refine ⟨hval, fun P => ?_⟩
  have hval' := hval
  unfold Filt.valid at hval'
  rw [Bool.and_eq_true, nodupB_iff, List.all_eq_true] at hval'
  have hg := hval'.1
  have hgm : ∀ x ∈ φ.g, x < m := fun x hx => by simpa using hval'.2 x hx
  have hes' := matches_reorder hes hg hgm
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
  have hh : φ.g.length ≤ m := length_le_of_reorder hg hgm
  rcases walkG_sound hes' φ.g.length hh φ.sys [] (by simp) rd _ 0 _ 0 r hr
      (relabel (sigmaOf hg hgm) P) 0 (restr_root _) with hnp | hl
  · exact Or.inl (not_planar_of_relabel _ P hnp)
  · exact Or.inr (listedRows_relabel P hg hgm ▸ hl)

/-- **Soundness of the check with filters.** -/
theorem not_combThr_of_checkF {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List (Filt × ReaderX))
    (rd : ReaderX) (h : checkF n es fs rd = true) : ¬ CombThr E := by
  rintro ⟨P, hP⟩
  unfold checkF at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hfs, hw⟩ := h
  have hfs' : ∀ φ ∈ fs.map Prod.fst, φ.valid m = true ∧ FiltSound E φ := by
    intro φ hφ
    obtain ⟨⟨φ', rdφ⟩, hmem, rfl⟩ := List.mem_map.1 hφ
    exact filtSound_of_checkFilter hes φ' rdφ (hfs _ hmem)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hw
  rw [hes.size] at hr
  rcases walkG_sound hes m le_rfl [] _ hfs' rd _ 0 _ 0 r hr P 0 (restr_root P) with hnp | hl
  · exact hnp hP
  · simp at hl

/-- **Soundness of the check with filters for the computed listings.** -/
theorem not_combThr_mkE_of_checkF (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × ReaderX)) (rd : ReaderX) (h : checkF n l.toArray fs rd = true) : ¬ CombThr (mkE n l) :=
  not_combThr_of_checkF (matches_mkE n l hl) fs rd h

end Thrackle78.Checker
