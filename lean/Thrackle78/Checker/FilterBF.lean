import Thrackle78.Checker.FilterBQ
import T78Fam

/-!
# Soundness of the bitset walk with family hints

`walkBF_soundP`: as `walkB_soundP`; a hint is one more proposed certificate, checked like the oracle's.
`not_combThr_mkE_of_topBSymRF`: the symmetry-reduced sharded search with root-restricted filters and family hints.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- **Soundness of the bitset walk with family hints, for one crossing system.** -/
theorem walkBF_soundP {α : Type} {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt) (orc : Oracle)
    (famOrc : ℕ → Array (List ℕ) → ℕ → α) (adapt : α → ℕ → Array (List ℕ) → Option MinorCert)
    (P : CrossingSystem E) (hfsP : ∀ φ ∈ fs, ¬ Planar (aug E P) ∨ rowsH P φ.g ∈ φ.sys) :
    ∀ fuel k rows alive hint, walkBF n es (fs.map prepB) orc famOrc adapt fuel k rows alive hint = true →
      ∀ t : ℕ, Restr P k t rows → AliveB P fs alive → ¬ Planar (aug E P)
  | 0, _, _, _, _, hw => by simp [walkBF] at hw
  | fuel + 1, k, rows, alive, hint, hw => by
    intro t hr ha
    simp only [walkBF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, List.length_map] at hw
    rcases hw with ((⟨i, hi, hzero⟩ | hhint) | horc) | ⟨hk, hw⟩
    · rcases hfsP _ (getD_mem_of_lt ⟨[], []⟩ hi) with hnp | hmem
      · exact hnp
      · exfalso
        obtain ⟨s, hs, hseq⟩ := List.getElem_of_mem hmem
        have := ha i hi s hs (by rw [List.getD_eq_getElem _ _ hs]; exact hseq)
        rw [hzero, Nat.zero_testBit] at this
        exact absurd this (by simp)
    · exact not_planar_of_oracleOK P hes hr hhint
    · exact not_planar_of_oracleOK P hes hr horc
    · have hk' : k < m := hes.size ▸ hk
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkBF_soundP hes fs orc famOrc adapt P hfsP fuel (k + 1) rows _ _ hw 0
          (restr_close P hes hr hk' h8) ha
      · rw [ite_eq_right h8] at hw
        simp only [List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        rw [children_eq_map, List.mem_map] at hr'
        obtain ⟨c, hc, rfl⟩ := hr'
        refine walkBF_soundP hes fs orc famOrc adapt P hfsP fuel k c.2.2 _ _
          (hw (c, childAlive es (fs.map prepB) alive k rows c) (List.mem_map_of_mem hc)) (t + 1) hres ?_
        intro i hi s hs hseq
        unfold childAlive
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
          Nat.testBit_land, ha i hi s hs hseq, Bool.true_and, prepB_getD fs hi]
        exact testBit_stepMask hes P hk' hr hc hres _ hs hseq

theorem stateSound_of_checkBFromListRF {α : Type} {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt)
    (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle)
    (famOrc : ℕ → Array (List ℕ) → ℕ → α) (adapt : α → ℕ → Array (List ℕ) → Option MinorCert)
    {L : List (ℕ × Array (List ℕ))} (h : checkBFromListRF n es fs orc famOrc adapt L = true) :
    ∀ s ∈ L, StateSound E s.1 s.2 := by
  unfold checkBFromListRF at h
  rw [List.all_eq_true] at h
  intro s hs P t hr
  refine walkBF_soundP hes _ orc famOrc adapt P ?_ _ s.1 s.2 _ _ (h s hs) t hr (aliveB_allOf P _)
  intro φ' hφ'
  rw [List.mem_map] at hφ'
  obtain ⟨φ, hφ, rfl⟩ := hφ'
  exact restrictFilt_sound P hr (hfs φ hφ)

/-- **The symmetry-reduced sharded search with root-restricted filters and family hints proves
`¬ CombThr (mkE n l)`.** -/
theorem not_combThr_mkE_of_topBSymRF {α : Type} (n : ℕ) [NeZero n] (l : List (ℕ × ℕ))
    (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n) (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (famOrc : ℕ → Array (List ℕ) → ℕ → α) (adapt : α → ℕ → Array (List ℕ) → Option MinorCert)
    (hf : fs.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true)
    (Ls : List (List (ℕ × Array (List ℕ)))) (look : ℕ × Array (List ℕ) → ℕ)
    (K : ℕ) (R : List ℕ) (σ : ℕ → ℕ) (flip : ℕ → Bool) (hR : ∀ e ∈ R, e < K) (hσR : ∀ e ∈ R, σ e ∈ R)
    (hsym : ∀ P : CrossingSystem (mkE n l), Planar (aug (mkE n l) P) →
      ∃ P', QSym R σ flip P' ∧ Planar (aug (mkE n l) P'))
    (htop : checkTopQ n l.toArray (fs.map Prod.fst) (orcF l.toArray) Ls.flatten.toArray look (symSkip K R σ flip) =
      true)
    (hsh : ∀ L ∈ Ls, checkBFromListRF n l.toArray (fs.map Prod.fst) (orcF l.toArray) famOrc adapt L = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list hes fs orcF hf
  have hL : ∀ s ∈ Ls.flatten.toArray.toList, StateSound (mkE n l) s.1 s.2 := by
    intro s hs
    rw [List.toList_toArray] at hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
    exact stateSound_of_checkBFromListRF hes _ hfs _ famOrc adapt (hsh L hL) s hsL
  rintro ⟨P, hP⟩
  obtain ⟨P', hq, hP'⟩ := hsym P hP
  have h0 : Restr P' 0 0 (Array.replicate l.toArray.size []) := restr_root P'
  exact walkBQ_sound hes _ hfs _ _ look hL (symSkip K R σ flip) (QSym R σ flip)
    (fun k rows P t hs hr => symSkip_sound hR hσR flip k rows P t hs hr) _ 0 _ _ htop P' 0 h0
    (aliveB_compat P' _ hfs h0) hq hP'

end Thrackle78.Checker
