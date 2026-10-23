import Thrackle78.Checker.FilterX
import T78FXF

/-!
# Soundness of the filter tree with family hints

`walkHOXF_sound`: as `walkHOX_sound`; a hint is one more proposed certificate, checked like the oracle's.
`filtSoundXF`: `filtSoundX` with the shards checked by `checkFilterXShardsF`.
`not_combThr_mkE_of_topBSymLFX`: the sharded search with indexed filters in the batches, symmetry-reduced by several edge
maps (`symSkipL`), with top filters whose soundness is a hypothesis (e.g. from `filtSound_prefix`).
`filtSound_prefix`: the keys of a sound filter whose H-edges `< K` come first form a sound filter on those H-edges;
`topFilt_sound`: hence the top filter of a sound indexed filter is sound.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- **Soundness of the filter tree with family hints.** -/
theorem walkHOXF_sound {α : Type} {es : Array (ℕ × ℕ)} (hes : Matches es E) (h : ℕ) (hh : h ≤ m)
    (inS : List (List ℕ) → Bool) (orc : Oracle)
    (famOrc : ℕ → Array (List ℕ) → ℕ → α) (adapt : α → ℕ → Array (List ℕ) → Option MinorCert) :
    ∀ fuel k rows hint, walkHOXF n es h inS orc famOrc adapt fuel k rows hint = true →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → ¬ Planar (aug E P) ∨ inS (listedRows P h) = true
  | 0, _, _, _, hw => by simp [walkHOXF] at hw
  | fuel + 1, k, rows, hint, hw => by
    intro P t hr
    simp only [walkHOXF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hw
    rcases hw with ((hhint | horc) | ⟨⟨rfl, hrh⟩, hin⟩) | ⟨hk, hw⟩
    · exact Or.inl (not_planar_of_oracleOK P hes hr hhint)
    · exact Or.inl (not_planar_of_oracleOK P hes hr horc)
    · refine Or.inr ?_
      rw [listedRows_eq_of_restr P hr hrh]
      exact hin
    · have hk' : k < m := by omega
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkHOXF_sound hes h hh inS orc famOrc adapt fuel (k + 1) rows none hw P 0
          (restr_close P hes hr hk' h8)
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        rw [children_eq_map, List.mem_map] at hr'
        obtain ⟨c, hc, rfl⟩ := hr'
        exact walkHOXF_sound hes h hh inS orc famOrc adapt fuel k c.2.2 _ (hw c hc) P (t + 1) hres

/-- **An accepted sharded filter tree (shards with family hints) proves that the logical filter of an indexed filter
is sound.** -/
theorem filtSoundXF {α : Type} {es : Array (ℕ × ℕ)} (hes : Matches es E) (φ : FiltX) (look : List (List ℕ) → ℕ)
    (orcF : Array (ℕ × ℕ) → Oracle) (famOrcF : Array (ℕ × ℕ) → ℕ → Array (List ℕ) → ℕ → α)
    (adaptF : Array (ℕ × ℕ) → α → ℕ → Array (List ℕ) → Option MinorCert)
    (Ls : List (List (ℕ × Array (List ℕ)))) (lookS : ℕ × Array (List ℕ) → ℕ)
    (htop : checkFilterXTop n es φ look orcF Ls.flatten.toArray lookS = true)
    (hsh : ∀ L ∈ Ls, checkFilterXShardsF n es φ look orcF famOrcF adaptF L = true) :
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
    unfold checkFilterXShardsF at this
    rw [List.all_eq_true] at this
    have h2 := this s hsL
    rw [hes.size] at h2
    exact walkHOXF_sound hes' φ.g.length hh _ _ _ _ _ s.1 s.2 none h2 Q t hr
  rcases walkHOXT_sound hes' φ.g.length hh _ _ _ lookS hL _ 0 _ hw (relabel (sigmaOf hg hgm) P) 0
      (restr_root _) with hnp | hl
  · exact Or.inl (not_planar_of_relabel _ P hnp)
  · refine Or.inr ?_
    rw [listedRows_relabel P hg hgm] at hl
    exact mem_of_inS φ look hl

/-- No system whose restriction is canonical for every edge map of `syms` extends a node skipped by `symSkipL`. -/
theorem symSkipL_sound {K : ℕ} {R : List ℕ} (hR : ∀ e ∈ R, e < K) {syms : List ((ℕ → ℕ) × (ℕ → Bool))}
    (hσR : ∀ s ∈ syms, ∀ e ∈ R, s.1 e ∈ R) (k : ℕ) (rows : Array (List ℕ)) (P : CrossingSystem E) (t : ℕ)
    (hs : symSkipL K R syms k rows = true) (hr : Restr P k t rows) : ¬ ∀ s ∈ syms, QSym R s.1 s.2 P := by
  unfold symSkipL at hs
  rw [List.any_eq_true] at hs
  obtain ⟨s, hs, hsk⟩ := hs
  exact fun hq => symSkip_sound hR (hσR s hs) s.2 k rows P t hsk hr (hq s hs)

/-- **The sharded search, symmetry-reduced by several edge maps, with indexed filters in the batches (and family
hints) proves `¬ CombThr (mkE n l)`.** The top tree prunes with the filters `fsT`, the batches with the indexed filters
`fsX`; the soundness of both is a hypothesis (e.g. from `filtSoundXF`). -/
theorem not_combThr_mkE_of_topBSymLFX {α : Type} (n : ℕ) [NeZero n] (l : List (ℕ × ℕ))
    (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n) (fsT : List Filt)
    (hfT : ∀ φ ∈ fsT, φ.valid l.length = true ∧ FiltSound (mkE n l) φ) (orc : Oracle) (fsX : List FiltX)
    (hfX : ∀ φ ∈ fsX, φ.idxOK = true ∧ φ.toFilt.valid l.length = true ∧ FiltSound (mkE n l) φ.toFilt)
    (famOrc : ℕ → Array (List ℕ) → ℕ → α) (adapt : α → ℕ → Array (List ℕ) → Option MinorCert)
    (Ls : List (List (ℕ × Array (List ℕ)))) (look : ℕ × Array (List ℕ) → ℕ)
    (K : ℕ) (R : List ℕ) (syms : List ((ℕ → ℕ) × (ℕ → Bool))) (hR : ∀ e ∈ R, e < K)
    (hσR : ∀ s ∈ syms, ∀ e ∈ R, s.1 e ∈ R)
    (hsym : ∀ P : CrossingSystem (mkE n l), Planar (aug (mkE n l) P) →
      ∃ P', (∀ s ∈ syms, QSym R s.1 s.2 P') ∧ Planar (aug (mkE n l) P'))
    (htop : checkTopQ n l.toArray fsT orc Ls.flatten.toArray look (symSkipL K R syms) = true)
    (hsh : ∀ L ∈ Ls, checkBFromListRX n l.toArray fsX orc famOrc adapt L = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hL : ∀ s ∈ Ls.flatten.toArray.toList, StateSound (mkE n l) s.1 s.2 := by
    intro s hs
    rw [List.toList_toArray] at hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
    exact stateSound_of_checkBFromListRX hes fsX hfX _ famOrc adapt (hsh L hL) s hsL
  rintro ⟨P, hP⟩
  obtain ⟨P', hq, hP'⟩ := hsym P hP
  have h0 : Restr P' 0 0 (Array.replicate l.toArray.size []) := restr_root P'
  exact walkBQ_sound hes _ hfT _ _ look hL (symSkipL K R syms) (fun P => ∀ s ∈ syms, QSym R s.1 s.2 P)
    (fun k rows P t hs hr => symSkipL_sound hR hσR k rows P t hs hr) _ 0 _ _ htop P' 0 h0
    (aliveB_compat P' _ hfT h0) hq hP'

/-- The key of a filter whose H-edges `< K` are its first `j` ones: the rows of the first `j` H-edges, restricted to
them. -/
theorem keyOf_eq_prefix {g : List ℕ} {K j : ℕ} (hj : j ≤ g.length) (hpre : ∀ i < g.length, (g.getD i 0 < K ↔ i < j))
    (s : List (List ℕ)) :
    keyOf g K s = (List.range j).map fun i => (s.getD i []).filter fun j' => decide (g.getD j' 0 < K) := by
  unfold keyOf
  have hsplit : List.range g.length = List.range j ++ (List.range (g.length - j)).map (j + ·) := by
    rw [← List.range_add, Nat.add_sub_cancel' hj]
  rw [hsplit, List.filterMap_append]
  have h2 : ((List.range (g.length - j)).map (j + ·)).filterMap (fun i => if g.getD i 0 < K then
      some ((s.getD i []).filter fun j' => decide (g.getD j' 0 < K)) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro i hi
    rw [List.mem_map] at hi
    obtain ⟨d, hd, rfl⟩ := hi
    rw [List.mem_range] at hd
    have : ¬ g.getD (j + d) 0 < K := fun h => by have := (hpre (j + d) (by omega)).1 h; omega
    simp only [this, ite_false]
  rw [h2, List.append_nil, ← List.filterMap_eq_map]
  apply List.filterMap_congr
  intro i hi
  rw [List.mem_range] at hi
  have : g.getD i 0 < K := (hpre i (by omega)).2 hi
  simp only [this, ite_true, Function.comp_apply]

/-- With the H-edges `< K` the first `j` ones, the H-rows of the first `j` H-edges are the key of the H-rows. -/
theorem rowsH_take_eq_keyOf (P : CrossingSystem E) {g : List ℕ} {K j : ℕ} (hj : j ≤ g.length)
    (hpre : ∀ i < g.length, (g.getD i 0 < K ↔ i < j)) :
    rowsH P (g.take j) = keyOf g K (rowsH P g) := by
  rw [keyOf_eq_prefix hj hpre]
  unfold rowsH
  rw [List.length_take, Nat.min_eq_left hj]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hig : i < g.length := by omega
  have htk : (g.take j).getD i 0 = g.getD i 0 := by
    rw [List.getD_eq_getElem (g.take j) 0 (by simp; omega), List.getD_eq_getElem g 0 hig, List.getElem_take]
  rw [htk]
  rw [List.getD_eq_getElem ((List.range g.length).map fun i =>
      ((πN P (g.getD i 0)).filter (fun f => g.contains f)).map (labOf g)) [] (by simpa using hig),
    List.getElem_map, List.getElem_range]
  have hpred : ∀ f, (g.take j).contains f = (g.contains f && decide (g.getD (labOf g f) 0 < K)) := by
    intro f
    by_cases hf : f ∈ g
    · have hq : labOf g f < g.length := List.idxOf_lt_length_of_mem hf
      have hgf : g.contains f = true := by simpa using hf
      rw [hgf, Bool.true_and]
      have h1 : f ∈ g.take j ↔ labOf g f < j := List.mem_take_iff_idxOf_lt hf
      have h2 := hpre _ hq
      by_cases ht : f ∈ g.take j
      · have : (g.take j).contains f = true := by simpa using ht
        rw [this]
        exact (decide_eq_true (h2.2 (h1.1 ht))).symm
      · have : (g.take j).contains f = false := by simpa using ht
        rw [this]
        exact (decide_eq_false fun h => ht (h1.2 (h2.1 h))).symm
    · have hgf : g.contains f = false := by simpa using hf
      have ht : f ∉ g.take j := fun h => hf (List.mem_of_mem_take h)
      have : (g.take j).contains f = false := by simpa using ht
      rw [this, hgf, Bool.false_and]
  have hfl : (πN P (g.getD i 0)).filter (fun f => (g.take j).contains f) =
      ((πN P (g.getD i 0)).filter (fun f => g.contains f)).filter (fun f => decide (g.getD (labOf g f) 0 < K)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro f _
    rw [hpred f, Bool.and_comm]
  rw [hfl, List.filter_map]
  apply List.map_congr_left
  intro f hf
  rw [List.mem_filter] at hf
  have hf1 : f ∈ g := by simpa using (List.mem_filter.1 hf.1).2
  have hf2 : f ∈ g.take j := by
    have := (List.mem_take_iff_idxOf_lt (n := j) hf1).2
    exact this ((hpre _ (List.idxOf_lt_length_of_mem hf1)).1 (of_decide_eq_true hf.2))
  unfold labOf
  conv_rhs => rw [← List.take_append_drop j g]
  rw [List.idxOf_append_of_mem hf2]

/-- **A prefix projection of a sound filter is sound**: with the H-edges `< K` the first `j` ones, the keys of the
systems (a list containing them) form a sound filter on the first `j` H-edges. -/
theorem filtSound_prefix (φ : Filt) {K j : ℕ} (keys : List (List (List ℕ))) (hj : j ≤ φ.g.length)
    (hpre : ∀ i < φ.g.length, (φ.g.getD i 0 < K ↔ i < j)) (hkeys : ∀ s ∈ φ.sys, keyOf φ.g K s ∈ keys)
    (hs : FiltSound E φ) : FiltSound E ⟨φ.g.take j, keys⟩ := fun P => by
  rcases hs P with hnp | hmem
  · exact Or.inl hnp
  · refine Or.inr ?_
    show rowsH P (φ.g.take j) ∈ keys
    rw [rowsH_take_eq_keyOf P hj hpre]
    exact hkeys _ hmem

/-- The bucket keys of an indexed filter contain the key of each of its systems (given the bucket check). -/
theorem keyOf_mem_keys (φ : FiltX) (hidx : φ.idxOK = true) :
    ∀ s ∈ φ.toFilt.sys, keyOf φ.g φ.K s ∈ (List.range φ.nb).map fun b => φ.bkeys.getD b [] := by
  intro s hs
  simp only [FiltX.toFilt, List.mem_map, List.mem_range] at hs
  obtain ⟨j, hj, rfl⟩ := hs
  have hix := (List.all_eq_true.1 hidx) j (List.mem_range.2 hj)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hix
  obtain ⟨⟨⟨hb, -⟩, -⟩, hkey⟩ := hix
  exact List.mem_map.2 ⟨bsearch φ.bl j, List.mem_range.2 hb, hkey.symm⟩

/-- **The top filter of a sound indexed filter is sound** (its H-edges `< K` its first `j` ones). -/
theorem topFilt_sound (φ : FiltX) (hidx : φ.idxOK = true) (hval : φ.toFilt.valid m = true)
    (hs : FiltSound E φ.toFilt) {j : ℕ} (hj : j ≤ φ.g.length)
    (hpre : ∀ i < φ.g.length, (φ.g.getD i 0 < φ.K ↔ i < j)) :
    (φ.topFilt j).valid m = true ∧ FiltSound E (φ.topFilt j) := by
  refine ⟨?_, filtSound_prefix φ.toFilt _ hj hpre (keyOf_mem_keys φ hidx) hs⟩
  unfold Filt.valid FiltX.topFilt at *
  unfold FiltX.toFilt at hval
  rw [Bool.and_eq_true, nodupB_iff, List.all_eq_true] at hval ⊢
  exact ⟨hval.1.sublist (List.take_sublist j _), fun x hx => hval.2 x (List.mem_of_mem_take hx)⟩

end Thrackle78.Checker
