import Thrackle78.Checker.FilterBF
import T78FX

/-!
# Soundness of indexed filters

* `keyOf_rowsH`: at a state of stage `k` with an empty open row, the prefix key of the restriction of every extension
  `P` to `H` is the key of the state.
* `restrict_sound`: if the buckets pass `idxOK` and the logical filter is sound, the restriction of the filter to the
  state keeps the restriction of every extension (`¬ Planar` or listed).
* `walkHOX_sound`, `walkHOXT_sound`, `filtSoundX`: the (sharded) filter tree of an indexed filter proves that its
  logical filter is sound.
* `not_combThr_mkE_of_topBSymRFX`: the symmetry-reduced sharded search with indexed filters and family hints.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- At a state of stage `k` with an empty open row, the rows of the closed edges restricted to the edges `< k` are
those of every extension. -/
theorem rows_filter_lt (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows)
    (hrk : rows.getD k [] = []) {e : ℕ} (he : e < k) (q : ℕ → Bool) :
    (rows.getD e []).filter (fun f => q f && decide (f < k)) = (πN P e).filter (fun f => q f && decide (f < k)) := by
  obtain ⟨-, hkm, -, hrows⟩ := hr
  have hem : e < m := lt_of_lt_of_le he hkm
  rw [hrows ⟨e, hem⟩]
  unfold rowAt πN
  rw [ite_eq_left he, dite_eq_left hem, List.filter_map, List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro f _
  simp only [Function.comp_apply]
  by_cases hfk : f.val < k
  · simp [hfk]
  · simp [hfk]

/-- At a state of stage `k` with an empty open row, the closed edges cross only edges `< k`. -/
theorem lt_of_mem_rows (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows)
    (hrk : rows.getD k [] = []) {e f : ℕ} (he : e < k) (hf : f ∈ rows.getD e []) : f < k := by
  obtain ⟨-, hkm, -, hrows⟩ := hr
  have hem : e < m := lt_of_lt_of_le he hkm
  rw [hrows ⟨e, hem⟩] at hf
  unfold rowAt at hf
  rw [ite_eq_left he, List.mem_map] at hf
  obtain ⟨f', hf', rfl⟩ := hf
  rw [List.mem_filter, decide_eq_true_eq] at hf'
  rcases hf'.2 with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hkm' : k < m := h1 ▸ f'.isLt
    have := hrows ⟨k, hkm'⟩
    rw [hrk] at this
    have hnil : rowAt P k t ⟨k, hkm'⟩ = [] := by simpa using this.symm
    rw [rowAt, ite_eq_right (lt_irrefl _), ite_eq_left rfl] at hnil
    have hfk : f' = ⟨k, hkm'⟩ := Fin.ext h1
    rw [hfk, hnil] at h2
    simp at h2

theorem keyOf_rowsH (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows)
    (hrk : rows.getD k [] = []) {g : List ℕ} :
    keyOf g k (rowsH P g) = keyRoot g k rows := by
  unfold keyOf keyRoot
  apply List.filterMap_congr
  intro i hi
  rw [List.mem_range] at hi
  by_cases hgi : g.getD i 0 < k
  · simp only [hgi, ite_true, Option.some.injEq]
    unfold rowsH
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range, List.filter_map,
      List.filter_filter]
    have hr2 : ((rows.getD (g.getD i 0) []).filter fun f => g.contains f) =
        (rows.getD (g.getD i 0) []).filter (fun f => g.contains f && decide (f < k)) := by
      apply List.filter_congr
      intro f hf
      simp [lt_of_mem_rows P hr hrk hgi hf]
    rw [hr2, rows_filter_lt P hr hrk hgi (fun f => g.contains f)]
    congr 1
    apply List.filter_congr
    intro f _
    by_cases hg : g.contains f = true
    · have hfg : f ∈ g := by simpa using hg
      have h3 : g.getD (labOf g f) 0 = f := getD_labOf hfg
      simp only [h3, hg, Bool.true_and, Bool.and_true, Function.comp_apply]
    · simp only [Bool.not_eq_true] at hg
      simp only [hg, Bool.and_false, Bool.false_and]
  · simp only [hgi, ite_false]

/-- **The restriction of an indexed filter to a state keeps the restriction of every extension** (given the bucket
check and the soundness of the logical filter). -/
theorem restrict_sound (φ : FiltX) (hidx : φ.idxOK = true) (hval : φ.toFilt.valid m = true)
    (hs : FiltSound E φ.toFilt) (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows) :
    ¬ Planar (aug E P) ∨ rowsH P (φ.restrict k rows).g ∈ (φ.restrict k rows).sys := by
  unfold FiltX.restrict
  by_cases hc : (k == φ.K && (rows.getD k []).isEmpty) = true
  · rw [ite_eq_left hc]
    rw [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
    obtain ⟨hkK, hrk⟩ := hc
    rcases hs P with hnp | hmem
    · exact Or.inl hnp
    · right
      simp only [FiltX.toFilt, List.mem_map, List.mem_range] at hmem
      obtain ⟨j, hj, hjeq⟩ := hmem
      have hix := (List.all_eq_true.1 hidx) j (List.mem_range.2 hj)
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hix
      obtain ⟨⟨⟨hb, hlo⟩, hhi⟩, hkey⟩ := hix
      have hkey' : φ.bkeys.getD (bsearch φ.bl j) [] = keyRoot φ.g k rows := by
        rw [← hkey, hjeq, ← hkK]
        exact keyOf_rowsH P hr hrk
      simp only [List.mem_flatMap, List.mem_range]
      refine ⟨bsearch φ.bl j, hb, ?_⟩
      rw [ite_eq_left (by rw [hkey']; exact beq_self_eq_true _)]
      unfold FiltX.bucket
      rw [List.mem_map]
      refine ⟨j - φ.bl.getD (bsearch φ.bl j) 0, List.mem_range.2 (by omega), ?_⟩
      rw [Nat.add_sub_cancel' hlo]
      exact hjeq
  · rw [ite_eq_right hc]
    exact restrictFilt_sound P hr ⟨hval, hs⟩

theorem stateSound_of_checkBFromListRX {α : Type} {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List FiltX)
    (hfs : ∀ φ ∈ fs, φ.idxOK = true ∧ φ.toFilt.valid m = true ∧ FiltSound E φ.toFilt) (orc : Oracle)
    (famOrc : ℕ → Array (List ℕ) → ℕ → α) (adapt : α → ℕ → Array (List ℕ) → Option MinorCert)
    {L : List (ℕ × Array (List ℕ))} (h : checkBFromListRX n es fs orc famOrc adapt L = true) :
    ∀ s ∈ L, StateSound E s.1 s.2 := by
  unfold checkBFromListRX at h
  rw [List.all_eq_true] at h
  intro s hs P t hr
  refine walkBF_soundP hes _ orc famOrc adapt P ?_ _ s.1 s.2 _ _ (h s hs) t hr (aliveB_allOf P _)
  intro φ' hφ'
  rw [List.mem_map] at hφ'
  obtain ⟨φ, hφ, rfl⟩ := hφ'
  obtain ⟨h1, h2, h3⟩ := hfs φ hφ
  exact restrict_sound φ h1 h2 h3 P hr

/-! ## The filter tree of an indexed filter -/

/-- **Soundness of the filter tree with a membership test.** -/
theorem walkHOX_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (h : ℕ) (hh : h ≤ m)
    (inS : List (List ℕ) → Bool) (orc : Oracle) :
    ∀ fuel k rows, walkHOX n es h inS orc fuel k rows = true →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → ¬ Planar (aug E P) ∨ inS (listedRows P h) = true
  | 0, _, _, hw => by simp [walkHOX] at hw
  | fuel + 1, k, rows, hw => by
    intro P t hr
    simp only [walkHOX, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hw
    rcases hw with (horc | ⟨⟨rfl, hrh⟩, hin⟩) | ⟨hk, hw⟩
    · exact Or.inl (not_planar_of_oracleOK P hes hr horc)
    · refine Or.inr ?_
      rw [listedRows_eq_of_restr P hr hrh]
      exact hin
    · have hk' : k < m := by omega
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkHOX_sound hes h hh inS orc fuel (k + 1) rows hw P 0 (restr_close P hes hr hk' h8)
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        exact walkHOX_sound hes h hh inS orc fuel k r' (hw r' hr') P (t + 1) hres

/-- **Soundness of the top of the filter tree**: the delegated states are sound by hypothesis. -/
theorem walkHOXT_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (h : ℕ) (hh : h ≤ m)
    (inS : List (List ℕ) → Bool) (orc : Oracle) (LA : Array (ℕ × Array (List ℕ)))
    (look : ℕ × Array (List ℕ) → ℕ)
    (hL : ∀ s ∈ LA.toList, ∀ (P : CrossingSystem E) (t : ℕ), Restr P s.1 t s.2 →
      ¬ Planar (aug E P) ∨ inS (listedRows P h) = true) :
    ∀ fuel k rows, walkHOXT n es h inS orc LA look fuel k rows = true →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → ¬ Planar (aug E P) ∨ inS (listedRows P h) = true
  | 0, _, _, hw => by simp [walkHOXT] at hw
  | fuel + 1, k, rows, hw => by
    intro P t hr
    simp only [walkHOXT, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
    rcases hw with ((⟨hi, heq⟩ | horc) | ⟨⟨rfl, hrh⟩, hin⟩) | ⟨hk, hw⟩
    · have hmem : (k, rows) ∈ LA.toList := by
        rw [← heq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
        exact Array.getElem_mem_toList hi
      exact hL _ hmem P t hr
    · exact Or.inl (not_planar_of_oracleOK P hes hr horc)
    · refine Or.inr ?_
      rw [listedRows_eq_of_restr P hr hrh]
      exact hin
    · have hk' : k < m := by omega
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkHOXT_sound hes h hh inS orc LA look hL fuel (k + 1) rows hw P 0 (restr_close P hes hr hk' h8)
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        exact walkHOXT_sound hes h hh inS orc LA look hL fuel k r' (hw r' hr') P (t + 1) hres

/-- Filter soundness is monotone in the list of systems. -/
theorem filtSound_mono {φ ψ : Filt} (hg : ψ.g = φ.g) (hsub : ∀ s ∈ φ.sys, s ∈ ψ.sys) (h : FiltSound E φ) :
    FiltSound E ψ := fun P => by
  rcases h P with hnp | hmem
  · exact Or.inl hnp
  · exact Or.inr (hg ▸ hsub _ hmem)

theorem mem_of_inS (φ : FiltX) (look : List (List ℕ) → ℕ) {x : List (List ℕ)} (h : φ.inS look x = true) :
    x ∈ φ.toFilt.sys := by
  unfold FiltX.inS at h
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [FiltX.toFilt, List.mem_map, List.mem_range]
  exact ⟨look x, h.1, h.2⟩

/-- **An accepted sharded filter tree proves that the logical filter of an indexed filter is sound.** -/
theorem filtSoundX {es : Array (ℕ × ℕ)} (hes : Matches es E) (φ : FiltX) (look : List (List ℕ) → ℕ)
    (orcF : Array (ℕ × ℕ) → Oracle) (Ls : List (List (ℕ × Array (List ℕ))))
    (lookS : ℕ × Array (List ℕ) → ℕ)
    (htop : checkFilterXTop n es φ look orcF Ls.flatten.toArray lookS = true)
    (hsh : ∀ L ∈ Ls, checkFilterXShards n es φ look orcF L = true) :
    φ.toFilt.valid m = true ∧ FiltSound E φ.toFilt := by
  unfold checkFilterXTop at htop
  rw [Bool.and_eq_true] at htop
  obtain ⟨hval, hw⟩ := htop
  rw [hes.size] at hval hw
  refine ⟨hval, fun P => ?_⟩
  have hval' := hval
  unfold Filt.valid at hval'
  rw [Bool.and_eq_true, nodupB_iff, List.all_eq_true] at hval'
  have hg : φ.g.Nodup := hval'.1
  have hgm : ∀ x ∈ φ.g, x < m := fun x hx => by simpa using hval'.2 x hx
  have hes' := matches_reorder hes hg hgm
  have hh : φ.g.length ≤ m := length_le_of_reorder hg hgm
  have hL : ∀ s ∈ Ls.flatten.toArray.toList, ∀ (Q : CrossingSystem (E ∘ ⇑(sigmaOf hg hgm))) (t : ℕ),
      Restr Q s.1 t s.2 → ¬ Planar (aug (E ∘ ⇑(sigmaOf hg hgm)) Q) ∨ φ.inS look (listedRows Q φ.g.length) = true := by
    intro s hs Q t hr
    rw [List.toList_toArray] at hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
    have := hsh L hL
    unfold checkFilterXShards at this
    rw [List.all_eq_true] at this
    have h2 := this s hsL
    rw [hes.size] at h2
    exact walkHOX_sound hes' φ.g.length hh _ _ _ s.1 s.2 h2 Q t hr
  rcases walkHOXT_sound hes' φ.g.length hh _ _ _ lookS hL _ 0 _ hw (relabel (sigmaOf hg hgm) P) 0
      (restr_root _) with hnp | hl
  · exact Or.inl (not_planar_of_relabel _ P hnp)
  · refine Or.inr ?_
    rw [listedRows_relabel P hg hgm] at hl
    exact mem_of_inS φ look hl

/-- **The symmetry-reduced sharded search with indexed filters in the batches (and family hints) proves
`¬ CombThr (mkE n l)`.** The top tree prunes with the filters `fsT` (checked by their filter trees); the batches use
the indexed filters `fsX` (bucket check and soundness of their logical filters as hypotheses, e.g. from
`filtSoundX`). -/
theorem not_combThr_mkE_of_topBSymRFX {α : Type} (n : ℕ) [NeZero n] (l : List (ℕ × ℕ))
    (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n) (fsT : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (hfT : fsT.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true) (fsX : List FiltX)
    (hfX : ∀ φ ∈ fsX, φ.idxOK = true ∧ φ.toFilt.valid l.length = true ∧ FiltSound (mkE n l) φ.toFilt)
    (famOrc : ℕ → Array (List ℕ) → ℕ → α) (adapt : α → ℕ → Array (List ℕ) → Option MinorCert)
    (Ls : List (List (ℕ × Array (List ℕ)))) (look : ℕ × Array (List ℕ) → ℕ)
    (K : ℕ) (R : List ℕ) (σ : ℕ → ℕ) (flip : ℕ → Bool) (hR : ∀ e ∈ R, e < K) (hσR : ∀ e ∈ R, σ e ∈ R)
    (hsym : ∀ P : CrossingSystem (mkE n l), Planar (aug (mkE n l) P) →
      ∃ P', QSym R σ flip P' ∧ Planar (aug (mkE n l) P'))
    (htop : checkTopQ n l.toArray (fsT.map Prod.fst) (orcF l.toArray) Ls.flatten.toArray look (symSkip K R σ flip) =
      true)
    (hsh : ∀ L ∈ Ls, checkBFromListRX n l.toArray fsX (orcF l.toArray) famOrc adapt L = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list hes fsT orcF hfT
  have hL : ∀ s ∈ Ls.flatten.toArray.toList, StateSound (mkE n l) s.1 s.2 := by
    intro s hs
    rw [List.toList_toArray] at hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
    exact stateSound_of_checkBFromListRX hes fsX hfX _ famOrc adapt (hsh L hL) s hsL
  rintro ⟨P, hP⟩
  obtain ⟨P', hq, hP'⟩ := hsym P hP
  have h0 : Restr P' 0 0 (Array.replicate l.toArray.size []) := restr_root P'
  exact walkBQ_sound hes _ hfs _ _ look hL (symSkip K R σ flip) (QSym R σ flip)
    (fun k rows P t hs hr => symSkip_sound hR hσR flip k rows P t hs hr) _ 0 _ _ htop P' 0 h0
    (aliveB_compat P' _ hfs h0) hq hP'

end Thrackle78.Checker
