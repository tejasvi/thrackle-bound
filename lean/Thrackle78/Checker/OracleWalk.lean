import Thrackle78Core.OracleWalk
import Thrackle78.Checker.Filter3
import Thrackle78.Checker.Native
import Thrackle78.Checker.StateEdge

/-!
# Soundness of the search with a certificate oracle and incremental filters

For every oracle (and every `look` function): `walkIO_sound`, `walkHO_sound`, `filtSound_of_checkFilterO`, and the
statements for the listings: `not_combThr_mkE_of_checkIO` (whole tree) and `not_combThr_mkE_of_shardsIO` (top tree
down to shard roots, one search per shard).
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

theorem not_planar_of_oracleOK (P : CrossingSystem E) {es : Array (ℕ × ℕ)} (hes : Matches es E) {k t : ℕ}
    {rows : Array (List ℕ)} (hr : Restr P k t rows) {orc : Oracle}
    (h : oracleOK n es orc k rows = true) : ¬ Planar (aug E P) := by
  unfold oracleOK at h
  cases hc : orc k rows with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
    rw [hc] at h
    exact not_planar_aug_of_stateE P t hes hr (not_planar_of_checkMinorE h)

/-- At level `h`, rows with an empty row `h` are the listed rows of the crossing system. -/
theorem listedRows_eq_of_restr (P : CrossingSystem E) {h t : ℕ} {rows : Array (List ℕ)} (hr : Restr P h t rows)
    (hrh : rows.getD h [] = []) : listedRows P h = (List.range h).map (fun e => rows.getD e []) := by
  have hrows := hr.2.2.2
  unfold listedRows
  apply List.map_congr_left
  intro e he
  rw [List.mem_range] at he
  by_cases hem : e < m
  · simp only [hem, ↓reduceDIte]
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
        have hkm : h < m := by have := f.isLt; omega
        have hfm : f = ⟨h, hkm⟩ := Fin.ext h'
        have := hrows ⟨h, hkm⟩
        rw [hrh] at this
        have hnil : rowAt P h t ⟨h, hkm⟩ = [] := by simpa using this.symm
        rw [rowAt, ite_eq_right (lt_irrefl _), ite_eq_left rfl] at hnil
        rw [hfm, hnil] at h''
        simp at h''
  · exfalso
    have := hr.2.1
    omega

/-- **Soundness of the oracle search with incremental filters.** -/
theorem walkIO_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt)
    (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle) :
    ∀ fuel k rows alive, walkIO n es fs orc fuel k rows alive = true →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → AliveOK P fs alive → ¬ Planar (aug E P)
  | 0, _, _, _, hw => by simp [walkIO] at hw
  | fuel + 1, k, rows, alive, hw => by
    intro P t hr ha
    have hal := aliveOK_aliveAt P hr fs hfs ha
    simp only [walkIO, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.mem_range] at hw
    rcases hw with (⟨i, hi, hempty⟩ | horc) | ⟨hk, hw⟩
    · obtain ⟨-, hsound⟩ := hfs _ (getD_mem_of_lt ⟨[], []⟩ hi)
      rcases hsound P with hnp | hmem
      · exact hnp
      · exfalso
        have := hal i hi hmem
        rw [List.isEmpty_iff.1 hempty] at this
        simp at this
    · exact not_planar_of_oracleOK P hes hr horc
    · have hk' : k < m := hes.size ▸ hk
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkIO_sound hes fs hfs orc fuel (k + 1) rows _ hw P 0 (restr_close P hes hr hk' h8) hal
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        exact walkIO_sound hes fs hfs orc fuel k r' _ (hw r' hr') P (t + 1) hres hal

/-- **Soundness of the oracle search tree of a filter.** -/
theorem walkHO_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (h : ℕ) (hh : h ≤ m)
    (S : Array (List (List ℕ))) (look : List (List ℕ) → ℕ) (orc : Oracle) :
    ∀ fuel k rows, walkHO n es h S look orc fuel k rows = true →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → ¬ Planar (aug E P) ∨ listedRows P h ∈ S.toList
  | 0, _, _, hw => by simp [walkHO] at hw
  | fuel + 1, k, rows, hw => by
    intro P t hr
    simp only [walkHO, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hw
    rcases hw with (horc | ⟨⟨⟨rfl, hrh⟩, hi⟩, heq⟩) | ⟨hk, hw⟩
    · exact Or.inl (not_planar_of_oracleOK P hes hr horc)
    · refine Or.inr ?_
      rw [listedRows_eq_of_restr P hr hrh, ← heq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
        Option.getD_some]
      exact Array.getElem_mem_toList hi
    · have hk' : k < m := by omega
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkHO_sound hes h hh S look orc fuel (k + 1) rows hw P 0 (restr_close P hes hr hk' h8)
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        exact walkHO_sound hes h hh S look orc fuel k r' (hw r' hr') P (t + 1) hres

/-- An accepted oracle filter tree proves that the filter is sound. -/
theorem filtSound_of_checkFilterO {es : Array (ℕ × ℕ)} (hes : Matches es E) (φ : Filt)
    (look : List (List ℕ) → ℕ) (orcF : Array (ℕ × ℕ) → Oracle) (h : checkFilterO n es φ look orcF = true) :
    φ.valid m = true ∧ FiltSound E φ := by
  unfold checkFilterO at h
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
  have hh : φ.g.length ≤ m := length_le_of_reorder hg hgm
  rcases walkHO_sound hes' φ.g.length hh φ.sys.toArray look _ _ 0 _ hw (relabel (sigmaOf hg hgm) P) 0
      (restr_root _) with hnp | hl
  · exact Or.inl (not_planar_of_relabel _ P hnp)
  · refine Or.inr ?_
    rw [listedRows_relabel P hg hgm] at hl
    simpa using hl

/-- The oracle search from a state with fresh compatible sets proves that the state is sound. -/
theorem stateSound_of_checkIOFrom {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt)
    (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle) {k : ℕ} {rows : Array (List ℕ)}
    (h : checkIOFrom n es fs orc k rows = true) : StateSound E k rows := by
  intro P t hr
  refine walkIO_sound hes fs hfs orc _ k rows _ h P t hr ?_
  intro i hi hmem
  have : (fs.map (·.sys)).getD i [] = (fs.getD i ⟨[], []⟩).sys := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]
  rw [this]
  exact hmem

theorem filtSound_list {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List (Filt × (List (List ℕ) → ℕ)))
    (orcF : Array (ℕ × ℕ) → Oracle) (h : fs.all (fun φl => checkFilterO n es φl.1 φl.2 orcF) = true) :
    ∀ φ ∈ fs.map Prod.fst, φ.valid m = true ∧ FiltSound E φ := by
  rw [List.all_eq_true] at h
  intro φ hφ
  rw [List.mem_map] at hφ
  obtain ⟨φl, hmem, hφl⟩ := hφ
  rw [← hφl]
  exact filtSound_of_checkFilterO hes φl.1 φl.2 orcF (h φl hmem)

/-- **The oracle search with filters proves `¬ CombThr (mkE n l)`.** -/
theorem not_combThr_mkE_of_checkIO (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (h : checkIO n l.toArray fs orcF = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  unfold checkIO at h
  rw [Bool.and_eq_true] at h
  exact not_combThr_of_rootSound hes
    (stateSound_of_checkIOFrom hes _ (filtSound_list hes fs orcF h.1) (orcF l.toArray) h.2)

/-- **Sharded oracle search with filters**: the top of the tree reaches only the shard roots `L`; the oracle search
from every shard root is accepted. -/
theorem not_combThr_mkE_of_shardsIO (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (hf : fs.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true)
    (L : List (ℕ × Array (List ℕ))) (d : ℕ)
    (htop : walkS l.toArray L d 0 (Array.replicate l.length []) = true)
    (hsh : ∀ s ∈ L, checkIOFrom n l.toArray (fs.map Prod.fst) (orcF l.toArray) s.1 s.2 = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list hes fs orcF hf
  apply not_combThr_of_rootSound hes
  have := walkS_sound hes L (fun s hs => stateSound_of_checkIOFrom hes _ hfs _ (hsh s hs)) d 0 _
    (by simpa using htop)
  simpa using this

end Thrackle78.Checker
