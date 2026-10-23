import Thrackle78.Checker.FilterB
import T78Sym

/-!
# Soundness of the top tree with skipped nodes, and the symmetry reduction

`walkBQ_sound`: the top tree shows that no crossing system with property `Q` that extends the root has a planar
augmented graph, if no system with `Q` extends a skipped node. `not_combThr_mkE_of_topBQ`: with a symmetry hypothesis
(every planar system has a planar image with `Q`) this gives `¬ CombThr`. `not_combThr_mkE_of_topBSym`: the instance
with the canonical-restriction test `symSkip` and `Q = QSym` (the restriction of `P` to `R` is lexicographically at
most its image under `σ`).
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- **Soundness of the top tree with skipped nodes.** -/
theorem walkBQ_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt)
    (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle) (LA : Array (ℕ × Array (List ℕ)))
    (look : ℕ × Array (List ℕ) → ℕ) (hL : ∀ s ∈ LA.toList, StateSound E s.1 s.2)
    (skip : ℕ → Array (List ℕ) → Bool) (Q : CrossingSystem E → Prop)
    (hskip : ∀ k rows (P : CrossingSystem E) t, skip k rows = true → Restr P k t rows → ¬ Q P) :
    ∀ fuel k rows alive, walkBQ n es (fs.map prepB) orc LA look skip fuel k rows alive = true →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → AliveB P fs alive → Q P → ¬ Planar (aug E P)
  | 0, _, _, _, hw => by simp [walkBQ] at hw
  | fuel + 1, k, rows, alive, hw => by
    intro P t hr ha hq
    simp only [walkBQ, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, List.length_map] at hw
    rcases hw with ((((hsk | ⟨hi, heq⟩) | ⟨i, hi, hzero⟩) | horc) | ⟨hk, hw⟩)
    · exact absurd hq (hskip k rows P t hsk hr)
    · have hmem : (k, rows) ∈ LA.toList := by
        rw [← heq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
        exact Array.getElem_mem_toList hi
      exact hL _ hmem P t hr
    · obtain ⟨-, hsound⟩ := hfs _ (getD_mem_of_lt ⟨[], []⟩ hi)
      rcases hsound P with hnp | hmem
      · exact hnp
      · exfalso
        obtain ⟨s, hs, hseq⟩ := List.getElem_of_mem hmem
        have := ha i hi s hs (by rw [List.getD_eq_getElem _ _ hs]; exact hseq)
        rw [hzero, Nat.zero_testBit] at this
        exact absurd this (by simp)
    · exact not_planar_of_oracleOK P hes hr horc
    · have hk' : k < m := hes.size ▸ hk
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkBQ_sound hes fs hfs orc LA look hL skip Q hskip fuel (k + 1) rows _ hw P 0
          (restr_close P hes hr hk' h8) ha hq
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        rw [children_eq_map, List.mem_map] at hr'
        obtain ⟨c, hc, rfl⟩ := hr'
        refine walkBQ_sound hes fs hfs orc LA look hL skip Q hskip fuel k c.2.2 _ (hw c hc) P (t + 1) hres ?_ hq
        intro i hi s hs hseq
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
          Nat.testBit_land, ha i hi s hs hseq, Bool.true_and, prepB_getD fs hi]
        exact testBit_stepMask hes P hk' hr hc hres _ hs hseq

/-- **Sharded oracle search with bitset filters, pruned top tree with skipped nodes, and a symmetry**: every planar
system has a planar image with `Q`, no system with `Q` extends a skipped node, the top search reaches only shard
states of `LA`, skipped nodes, or prunes, and every batch of shard states passes. -/
theorem not_combThr_mkE_of_topBQ (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (hf : fs.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true)
    (Ls : List (List (ℕ × Array (List ℕ)))) (look : ℕ × Array (List ℕ) → ℕ)
    (skip : ℕ → Array (List ℕ) → Bool) (Q : CrossingSystem (mkE n l) → Prop)
    (hskip : ∀ k rows (P : CrossingSystem (mkE n l)) t, skip k rows = true → Restr P k t rows → ¬ Q P)
    (hsym : ∀ P : CrossingSystem (mkE n l), Planar (aug (mkE n l) P) → ∃ P', Q P' ∧ Planar (aug (mkE n l) P'))
    (htop : checkTopQ n l.toArray (fs.map Prod.fst) (orcF l.toArray) Ls.flatten.toArray look skip = true)
    (hsh : ∀ L ∈ Ls, checkBFromList n l.toArray (fs.map Prod.fst) (orcF l.toArray) L = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list hes fs orcF hf
  have hL : ∀ s ∈ Ls.flatten.toArray.toList, StateSound (mkE n l) s.1 s.2 := by
    intro s hs
    rw [List.toList_toArray] at hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
    exact stateSound_of_checkBFromList hes _ hfs _ (hsh L hL) s hsL
  rintro ⟨P, hP⟩
  obtain ⟨P', hq, hP'⟩ := hsym P hP
  have h0 : Restr P' 0 0 (Array.replicate l.toArray.size []) := restr_root P'
  exact walkBQ_sound hes _ hfs _ _ look hL skip Q hskip _ 0 _ _ htop P' 0 h0 (aliveB_compat P' _ hfs h0) hq hP'

/-! ## The canonical-restriction test -/

/-- The restriction of `P` to `R` is canonical. -/
def QSym (R : List ℕ) (σ : ℕ → ℕ) (flip : ℕ → Bool) (P : CrossingSystem E) : Prop :=
  canonR R σ flip (πN P) = true

/-- At a stage where the edges of `R` are closed, the rows restricted to `R` are those of every extension. -/
theorem filter_rows_eq (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows)
    {R : List ℕ} (hR : ∀ f ∈ R, f < k) {e : ℕ} (he : e < k) :
    (rows.getD e []).filter (fun f => R.contains f) = (πN P e).filter (fun f => R.contains f) := by
  obtain ⟨-, hkm, -, hrows⟩ := hr
  have hem : e < m := lt_of_lt_of_le he hkm
  rw [hrows ⟨e, hem⟩]
  unfold rowAt πN
  rw [ite_eq_left he, dite_eq_left hem, List.filter_map, List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro f _
  by_cases hf : f.val ∈ R
  · have hlt : f.val < k := hR _ hf
    simp [hf, hlt]
  · simp [hf]

theorem canonR_rows_eq (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows)
    {R : List ℕ} (hR : ∀ f ∈ R, f < k) {σ : ℕ → ℕ} (hσR : ∀ e ∈ R, σ e ∈ R) (flip : ℕ → Bool) :
    canonR R σ flip (fun e => rows.getD e []) = canonR R σ flip (πN P) := by
  have hre : restrR R (fun e => rows.getD e []) = restrR R (πN P) := by
    unfold restrR
    exact List.map_congr_left fun e he => filter_rows_eq P hr hR (hR e he)
  have him : imageR R σ flip (fun e => rows.getD e []) = imageR R σ flip (πN P) := by
    unfold imageR
    refine List.map_congr_left fun e he => ?_
    simp only
    rw [filter_rows_eq P hr hR (hR _ (hσR e he))]
  unfold canonR
  rw [hre, him]

/-- No system with a canonical restriction extends a node skipped by `symSkip`. -/
theorem symSkip_sound {K : ℕ} {R : List ℕ} (hR : ∀ e ∈ R, e < K) {σ : ℕ → ℕ} (hσR : ∀ e ∈ R, σ e ∈ R)
    (flip : ℕ → Bool) (k : ℕ) (rows : Array (List ℕ)) (P : CrossingSystem E) (t : ℕ)
    (hs : symSkip K R σ flip k rows = true) (hr : Restr P k t rows) : ¬ QSym R σ flip P := by
  unfold symSkip at hs
  rw [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hs
  obtain ⟨hK, hc⟩ := hs
  unfold QSym
  rw [← canonR_rows_eq P hr (fun f hf => lt_of_lt_of_le (hR f hf) hK) hσR flip, hc]
  simp

/-- **The symmetry-reduced sharded search proves `¬ CombThr (mkE n l)`**, given that every planar system has a planar
image whose restriction to `R` is canonical (`R`: edges `< K`, closed under `σ`). -/
theorem not_combThr_mkE_of_topBSym (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (hf : fs.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true)
    (Ls : List (List (ℕ × Array (List ℕ)))) (look : ℕ × Array (List ℕ) → ℕ)
    (K : ℕ) (R : List ℕ) (σ : ℕ → ℕ) (flip : ℕ → Bool) (hR : ∀ e ∈ R, e < K) (hσR : ∀ e ∈ R, σ e ∈ R)
    (hsym : ∀ P : CrossingSystem (mkE n l), Planar (aug (mkE n l) P) →
      ∃ P', QSym R σ flip P' ∧ Planar (aug (mkE n l) P'))
    (htop : checkTopQ n l.toArray (fs.map Prod.fst) (orcF l.toArray) Ls.flatten.toArray look (symSkip K R σ flip) =
      true)
    (hsh : ∀ L ∈ Ls, checkBFromList n l.toArray (fs.map Prod.fst) (orcF l.toArray) L = true) :
    ¬ CombThr (mkE n l) :=
  not_combThr_mkE_of_topBQ n l hl fs orcF hf Ls look (symSkip K R σ flip) (QSym R σ flip)
    (fun k rows P t hs hr => symSkip_sound hR hσR flip k rows P t hs hr) hsym htop hsh

/-! ## Filters restricted at the shard roots -/

/-- **Soundness of the bitset walk for one crossing system**: only the filter lists of `P`'s own restrictions are used. -/
theorem walkB_soundP {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt) (orc : Oracle)
    (P : CrossingSystem E) (hfsP : ∀ φ ∈ fs, ¬ Planar (aug E P) ∨ rowsH P φ.g ∈ φ.sys) :
    ∀ fuel k rows alive, walkB n es (fs.map prepB) orc fuel k rows alive = true →
      ∀ t : ℕ, Restr P k t rows → AliveB P fs alive → ¬ Planar (aug E P)
  | 0, _, _, _, hw => by simp [walkB] at hw
  | fuel + 1, k, rows, alive, hw => by
    intro t hr ha
    simp only [walkB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, List.length_map] at hw
    rcases hw with (⟨i, hi, hzero⟩ | horc) | ⟨hk, hw⟩
    · rcases hfsP _ (getD_mem_of_lt ⟨[], []⟩ hi) with hnp | hmem
      · exact hnp
      · exfalso
        obtain ⟨s, hs, hseq⟩ := List.getElem_of_mem hmem
        have := ha i hi s hs (by rw [List.getD_eq_getElem _ _ hs]; exact hseq)
        rw [hzero, Nat.zero_testBit] at this
        exact absurd this (by simp)
    · exact not_planar_of_oracleOK P hes hr horc
    · have hk' : k < m := hes.size ▸ hk
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkB_soundP hes fs orc P hfsP fuel (k + 1) rows _ hw 0 (restr_close P hes hr hk' h8) ha
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        rw [children_eq_map, List.mem_map] at hr'
        obtain ⟨c, hc, rfl⟩ := hr'
        refine walkB_soundP hes fs orc P hfsP fuel k c.2.2 _ (hw c hc) (t + 1) hres ?_
        intro i hi s hs hseq
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
          Nat.testBit_land, ha i hi s hs hseq, Bool.true_and, prepB_getD fs hi]
        exact testBit_stepMask hes P hk' hr hc hres _ hs hseq

/-- A system extending the state keeps its restriction in the filter restricted to the state. -/
theorem restrictFilt_sound (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows)
    {φ : Filt} (hφ : φ.valid m = true ∧ FiltSound E φ) :
    ¬ Planar (aug E P) ∨ rowsH P (restrictFilt φ k rows).g ∈ (restrictFilt φ k rows).sys := by
  obtain ⟨hval, hsound⟩ := hφ
  rcases hsound P with hnp | hmem
  · exact Or.inl hnp
  · right
    unfold Filt.valid at hval
    rw [Bool.and_eq_true, nodupB_iff, List.all_eq_true] at hval
    unfold restrictFilt
    simp only [List.mem_filter]
    exact ⟨hmem, compat_rowsH P hr hval.1 (fun x hx => by simpa using hval.2 x hx)⟩

theorem aliveB_allOf (P : CrossingSystem E) (fs : List Filt) : AliveB P fs (fs.map fun φ => allOf φ.sys) := by
  intro i hi s hs _
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, testBit_allOf,
    ← List.getD_eq_getElem _ ⟨[], []⟩ hi]
  simpa using hs

theorem stateSound_of_checkBFromListR {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt)
    (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle) {L : List (ℕ × Array (List ℕ))}
    (h : checkBFromListR n es fs orc L = true) : ∀ s ∈ L, StateSound E s.1 s.2 := by
  unfold checkBFromListR at h
  rw [List.all_eq_true] at h
  intro s hs P t hr
  refine walkB_soundP hes _ orc P ?_ _ s.1 s.2 _ (h s hs) t hr (aliveB_allOf P _)
  intro φ' hφ'
  rw [List.mem_map] at hφ'
  obtain ⟨φ, hφ, rfl⟩ := hφ'
  exact restrictFilt_sound P hr (hfs φ hφ)

/-- **The symmetry-reduced sharded search with filters restricted at the shard roots proves `¬ CombThr (mkE n l)`.** -/
theorem not_combThr_mkE_of_topBSymR (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (hf : fs.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true)
    (Ls : List (List (ℕ × Array (List ℕ)))) (look : ℕ × Array (List ℕ) → ℕ)
    (K : ℕ) (R : List ℕ) (σ : ℕ → ℕ) (flip : ℕ → Bool) (hR : ∀ e ∈ R, e < K) (hσR : ∀ e ∈ R, σ e ∈ R)
    (hsym : ∀ P : CrossingSystem (mkE n l), Planar (aug (mkE n l) P) →
      ∃ P', QSym R σ flip P' ∧ Planar (aug (mkE n l) P'))
    (htop : checkTopQ n l.toArray (fs.map Prod.fst) (orcF l.toArray) Ls.flatten.toArray look (symSkip K R σ flip) =
      true)
    (hsh : ∀ L ∈ Ls, checkBFromListR n l.toArray (fs.map Prod.fst) (orcF l.toArray) L = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list hes fs orcF hf
  have hL : ∀ s ∈ Ls.flatten.toArray.toList, StateSound (mkE n l) s.1 s.2 := by
    intro s hs
    rw [List.toList_toArray] at hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
    exact stateSound_of_checkBFromListR hes _ hfs _ (hsh L hL) s hsL
  rintro ⟨P, hP⟩
  obtain ⟨P', hq, hP'⟩ := hsym P hP
  have h0 : Restr P' 0 0 (Array.replicate l.toArray.size []) := restr_root P'
  exact walkBQ_sound hes _ hfs _ _ look hL (symSkip K R σ flip) (QSym R σ flip)
    (fun k rows P t hs hr => symSkip_sound hR hσR flip k rows P t hs hr) _ 0 _ _ htop P' 0 h0
    (aliveB_compat P' _ hfs h0) hq hP'

end Thrackle78.Checker
