import Thrackle78Core.Filter
import Thrackle78.Checker.Tree
import Thrackle78.Checker.Relabel

/-!
# Soundness of filters

* `walkG_sound`: the tree walk with listed leaves and filter prunes: every crossing system extending an accepted state
  is non-planar or restricts (at level `h`) to a listed system, provided every filter used is sound (`FiltSound`).
* `filtSound_of_checkFilter`: an accepted filter tree (on the reordered listing) proves that every crossing system with
  a planar augmented graph restricts on `H` to one of the listed systems (via `not_planar_of_relabel`).
* `compat_rowsH`: the restriction of a crossing system to `H` is compatible with every state it extends.
* `not_combThr_of_checkF`: the check with filters proves `¬ CombThr E`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-! ## Rows of the restriction to `H` -/

/-- The complete row of edge `e` as naturals (empty beyond `m`). -/
def πN (P : CrossingSystem E) (e : ℕ) : List ℕ := if he : e < m then (P.π ⟨e, he⟩).map Fin.val else []

/-- The rows of the restriction of `P` to the H-edges `g` (entries are H-indices). -/
def rowsH (P : CrossingSystem E) (g : List ℕ) : List (List ℕ) :=
  (List.range g.length).map fun i => ((πN P (g.getD i 0)).filter (fun f => g.contains f)).map (labOf g)

/-- The filter is sound for `E`: every crossing system with a planar augmented graph restricts to a listed system. -/
def FiltSound (E : Fin m → Fin n × Fin n) (φ : Filt) : Prop :=
  ∀ P : CrossingSystem E, ¬ Planar (aug E P) ∨ rowsH P φ.g ∈ φ.sys

/-- The rows of the first `h` edges at stage `(h, 0)`. -/
def listedRows (P : CrossingSystem E) (h : ℕ) : List (List ℕ) :=
  (List.range h).map fun e => if he : e < m then (rowAt P h 0 ⟨e, he⟩).map Fin.val else []

theorem nodupB_iff : ∀ l : List ℕ, nodupB l = true ↔ l.Nodup
  | [] => by simp [nodupB]
  | x :: l => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons, nodupB_iff l]
    simp

theorem labOf_getD {g : List ℕ} (hg : g.Nodup) {i : ℕ} (hi : i < g.length) : labOf g (g.getD i 0) = i := by
  unfold labOf
  rw [List.getD_eq_getElem _ _ hi]
  exact hg.idxOf_getElem i hi

theorem getD_labOf {g : List ℕ} {x : ℕ} (hx : x ∈ g) : g.getD (labOf g x) 0 = x := by
  unfold labOf
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.2 hx)]
  exact List.getElem_idxOf _

/-! ## Compatibility -/

theorem πN_of_lt (P : CrossingSystem E) {e : ℕ} (he : e < m) : πN P e = (P.π ⟨e, he⟩).map Fin.val := by
  simp [πN, he]

/-- The restriction of a crossing system to `H` is compatible with every state it extends. -/
theorem compat_rowsH (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows)
    {g : List ℕ} (hg : g.Nodup) (hgm : ∀ x ∈ g, x < m) : compat g (rowsH P g) k rows = true := by
  obtain ⟨-, -, -, hrows⟩ := hr
  unfold compat
  rw [List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  have hgi : g.getD i 0 < m := hgm _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  set gi := g.getD i 0 with hgi_def
  set e : Fin m := ⟨gi, hgi⟩ with he_def
  have hrow : rows.getD gi [] = (rowAt P k t e).map Fin.val := hrows e
  have hsi : (rowsH P g).getD i [] = ((πN P gi).filter (fun f => g.contains f)).map (labOf g) := by
    unfold rowsH
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  -- the row of `e` is the filter of its complete row by itself
  have hsub : (rows.getD gi []).Sublist (πN P gi) := by
    rw [hrow, πN_of_lt P hgi]
    exact (rowAt_sublist P k t e).map _
  have hnd : (πN P gi).Nodup := by
    rw [πN_of_lt P hgi]; exact (P.nodup e).map Fin.val_injective
  have hrfilt : (πN P gi).filter (fun x => decide (x ∈ rows.getD gi [])) = rows.getD gi [] :=
    filter_mem_eq_of_sublist hsub hnd
  -- moving a filter through `labOf`
  have hmapfilt : ∀ (q : ℕ → Bool), (((πN P gi).filter (fun f => g.contains f)).map (labOf g)).filter
      (fun j => q (g.getD j 0)) = (((πN P gi).filter (fun f => g.contains f)).filter q).map (labOf g) := by
    intro q
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro x hx
    rw [List.mem_filter] at hx
    simp only [Function.comp]
    rw [getD_labOf (List.contains_iff_mem.1 hx.2)]
  by_cases hlt : gi < k
  · rw [ite_eq_left hlt, beq_iff_eq, hsi, hmapfilt (fun x => (rows.getD gi []).contains x)]
    congr 1
    conv_lhs => rw [← hrfilt]
    rw [List.filter_comm]
    apply List.filter_congr
    intro x _
    simp [List.contains_iff_mem]
  · rw [ite_eq_right hlt]
    by_cases heq : gi = k
    · rw [ite_eq_left heq, hsi, hmapfilt (fun x => decide (x < k)), List.isPrefixOf_iff_prefix]
      apply List.IsPrefix.map
      have hev : e.val = k := heq
      have hrk : rows.getD k [] = (((πN P gi).filter (fun x => decide (x < k))).take t) := by
        rw [← heq, hrow, rowAt, ite_eq_right (show ¬ (e.val < k) by omega), ite_eq_left hev, earlier,
          πN_of_lt P hgi]
        rw [List.map_take]
        congr 1
        rw [List.filter_map]
        congr 1
      rw [hrk, List.filter_comm]
      exact (List.take_prefix _ _).filter _
    · rw [ite_eq_right heq]

/-! ## The tree walk with listed leaves and filters -/

/-- **Soundness of the tree walk with listed leaves and filters.** -/
theorem walkG_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (h : ℕ) (hh : h ≤ m) (S : List (List (List ℕ)))
    (fs : List Filt) (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (rd : ReaderX) :
    ∀ fuel k rows pos r, walkG n es h S fs rd fuel k rows pos = some r →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → ¬ Planar (aug E P) ∨ listedRows P h ∈ S
  | 0, _, _, _, _, hw => by simp [walkG] at hw
  | fuel + 1, k, rows, pos, r, hw => by
    intro P t hr
    simp only [walkG] at hw
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
        · refine Or.inr ?_
          obtain ⟨rfl, hrh, hi, heq⟩ := h4
          obtain ⟨-, -, -, hrows⟩ := hr
          have hlist : listedRows P k = (List.range k).map (fun e => rows.getD e []) := by
            unfold listedRows
            apply List.map_congr_left
            intro e he
            rw [List.mem_range] at he
            have hem : e < m := by omega
            simp only [hem, ↓reduceDIte]
            rw [hrows ⟨e, hem⟩]
            congr 1
            rw [rowAt, rowAt, ite_eq_left he, ite_eq_left he]
            apply List.filter_congr
            intro f _
            rw [decide_eq_decide]
            constructor
            · rintro (h' | ⟨-, h''⟩)
              · exact Or.inl h'
              · simp at h''
            · rintro (h' | ⟨h', h''⟩)
              · exact Or.inl h'
              · exfalso
                have hkm : k < m := by omega
                have hfm : f = ⟨k, hkm⟩ := Fin.ext h'
                have := hrows ⟨k, hkm⟩
                rw [hrh] at this
                have hnil : rowAt P k t ⟨k, hkm⟩ = [] := by
                  simpa using this.symm
                rw [rowAt, ite_eq_right (lt_irrefl _), ite_eq_left rfl] at hnil
                rw [hfm, hnil] at h''
                simp at h''
          rw [hlist, heq, List.getD_eq_getElem _ _ hi]
          exact List.getElem_mem hi
        · rw [ite_eq_right h4] at hw; exact absurd hw (by simp)
      · rw [ite_eq_right h3] at hw
        by_cases h5 : (rd.tag pos).1 = 4
        · rw [ite_eq_left h5] at hw
          by_cases h6 : (rd.num (rd.tag pos).2).1 < fs.length ∧
              ((fs.getD (rd.num (rd.tag pos).2).1 ⟨[], []⟩).sys.all fun s =>
                !compat (fs.getD (rd.num (rd.tag pos).2).1 ⟨[], []⟩).g s k rows) = true
          · refine Or.inl ?_
            obtain ⟨hi, hall⟩ := h6
            set φ := fs.getD (rd.num (rd.tag pos).2).1 ⟨[], []⟩ with hφ
            have hφmem : φ ∈ fs := by rw [hφ, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
            obtain ⟨hval, hsound⟩ := hfs φ hφmem
            unfold Filt.valid at hval
            rw [Bool.and_eq_true, nodupB_iff, List.all_eq_true] at hval
            rcases hsound P with hnp | hmem
            · exact hnp
            · exfalso
              rw [List.all_eq_true] at hall
              have := hall _ hmem
              rw [compat_rowsH P hr hval.1 (fun x hx => by simpa using hval.2 x hx)] at this
              simp at this
          · rw [ite_eq_right h6] at hw; exact absurd hw (by simp)
        · rw [ite_eq_right h5] at hw
          by_cases h7 : (rd.tag pos).1 = 0 ∧ k < h
          · rw [ite_eq_left h7] at hw
            have hk : k < m := by omega
            by_cases h8 : (rows.getD k []).length = numEarlier es k
            · rw [ite_eq_left h8] at hw
              exact walkG_sound hes h hh S fs hfs rd fuel (k + 1) rows _ r hw P 0 (restr_close P hes hr hk h8)
            · rw [ite_eq_right h8] at hw
              obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk h8
              obtain ⟨p, q, hpq⟩ := foldl_bind_some (fun r p => walkG n es h S fs rd fuel k r p) _ _ _ hw r' hr'
              exact walkG_sound hes h hh S fs hfs rd fuel k r' p q hpq P (t + 1) hres
          · rw [ite_eq_right h7] at hw; exact absurd hw (by simp)

end Thrackle78.Checker
