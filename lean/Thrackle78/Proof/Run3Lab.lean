import Thrackle78.Proof.Run3Defs

/-!
# The run lemma for `4/3`: labels of a walk along a 6-cycle

For a walk `w : ℕ → V` with `w t = c t` (`t ≤ 3`) along an injective `c : Fin 6 → V`: the label of position `t` is `t`
for `t ≤ 3`; for `4 ≤ t`, the index `j` if `w t = c j`, else `t₀ + 2` for the first position `t₀ ≥ 4` with
`w t₀ = w t`. `phiL3` maps labels back to vertices. The labels of `w₄ … w₉` form a valid pattern, and `phiL3` is
injective on the occurring labels.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

variable {V : Type} [DecidableEq V]

section Labels

variable (w : ℕ → V) (c : Fin 6 → V)

/-- The label of position `t`. -/
noncomputable def labOf3 (t : ℕ) : ℕ := by
  classical
  exact if ht : t < 4 then t else if h : ∃ j : Fin 6, w t = c j then h.choose.val
    else Nat.find (p := fun u => 4 ≤ u ∧ w u = w t) ⟨t, by omega, rfl⟩ + 2

/-- The vertex of a label. -/
def phiL3 (l : ℕ) : V := if h : l < 6 then c ⟨l, h⟩ else w (l - 2)

/-- The pattern: the labels of `w₄ … w₉`. -/
noncomputable def xsOf3 : List ℕ :=
  [labOf3 w c 4, labOf3 w c 5, labOf3 w c 6, labOf3 w c 7, labOf3 w c 8, labOf3 w c 9]

variable {w c}

lemma labOf3_lt4 {t : ℕ} (ht : t < 4) : labOf3 w c t = t := by
  unfold labOf3; simp [ht]

lemma labOf3_on {t : ℕ} (ht : 4 ≤ t) {j : Fin 6} (hj : w t = c j) (hc : Function.Injective c) :
    labOf3 w c t = j.val := by
  unfold labOf3
  have hex : ∃ j : Fin 6, w t = c j := ⟨j, hj⟩
  simp only [show ¬ t < 4 by omega, dite_false, hex, dite_true]
  congr 1
  exact hc (hex.choose_spec.symm.trans hj)

/-- A new vertex: its first position. -/
lemma labOf3_new {t : ℕ} (ht : 4 ≤ t) (hn : ∀ j : Fin 6, w t ≠ c j) :
    ∃ t₀, 4 ≤ t₀ ∧ t₀ ≤ t ∧ w t₀ = w t ∧ (∀ u, 4 ≤ u → w u = w t → t₀ ≤ u) ∧ labOf3 w c t = t₀ + 2 := by
  classical
  have hex : ¬ ∃ j : Fin 6, w t = c j := fun ⟨j, hj⟩ => hn j hj
  have hP : ∃ u, 4 ≤ u ∧ w u = w t := ⟨t, ht, rfl⟩
  refine ⟨Nat.find hP, (Nat.find_spec hP).1, Nat.find_min' hP ⟨ht, rfl⟩, (Nat.find_spec hP).2,
    fun u hu hwu => Nat.find_min' hP ⟨hu, hwu⟩, ?_⟩
  unfold labOf3
  simp only [show ¬ t < 4 by omega, dite_false, hex]

lemma labOf3_cases {t : ℕ} (ht : 4 ≤ t) (hc : Function.Injective c) :
    (∃ j : Fin 6, w t = c j ∧ labOf3 w c t = j.val) ∨
      (∃ t₀, 4 ≤ t₀ ∧ t₀ ≤ t ∧ w t₀ = w t ∧ (∀ j : Fin 6, w t ≠ c j) ∧ (∀ u, 4 ≤ u → w u = w t → t₀ ≤ u) ∧
        labOf3 w c t = t₀ + 2) := by
  by_cases h : ∃ j : Fin 6, w t = c j
  · obtain ⟨j, hj⟩ := h
    exact Or.inl ⟨j, hj, labOf3_on ht hj hc⟩
  · push Not at h
    obtain ⟨t₀, h1, h2, h3, h4, h5⟩ := labOf3_new ht h
    exact Or.inr ⟨t₀, h1, h2, h3, h, h4, h5⟩

variable (hc : Function.Injective c) (hw : ∀ t (ht : t < 4), c ⟨t, by omega⟩ = w t)
include hc hw

/-- The label of a position names its vertex. -/
lemma phiL3_labOf3 (t : ℕ) : phiL3 w c (labOf3 w c t) = w t := by
  by_cases ht : t < 4
  · rw [labOf3_lt4 ht]
    unfold phiL3
    rw [dite_eq_left (by omega)]
    exact hw t ht
  · rcases labOf3_cases (w := w) (by omega : 4 ≤ t) hc with ⟨j, hj, hl⟩ | ⟨t₀, h1, h2, h3, h4, h5, hl⟩
    · rw [hl]; unfold phiL3; rw [dite_eq_left j.isLt]; exact hj.symm
    · rw [hl]; unfold phiL3; rw [dite_eq_right (by omega)]
      simp only [Nat.add_sub_cancel]
      exact h3

omit hw in
lemma labOf3_lt (t : ℕ) (ht : t < 10) : labOf3 w c t < 12 := by
  by_cases h4 : t < 4
  · rw [labOf3_lt4 h4]; omega
  · rcases labOf3_cases (w := w) (by omega : 4 ≤ t) hc with ⟨j, -, hl⟩ | ⟨t₀, -, h2, -, -, -, hl⟩
    · rw [hl]; have := j.isLt; omega
    · rw [hl]; omega

/-- A new label is the first position of its vertex. -/
lemma labOf3_first (t : ℕ) (ht : 4 ≤ t) (h6 : 6 ≤ labOf3 w c t) :
    4 ≤ labOf3 w c t - 2 ∧ labOf3 w c t - 2 ≤ t ∧ w (labOf3 w c t - 2) = w t ∧
      (∀ j : Fin 6, w t ≠ c j) ∧ labOf3 w c (labOf3 w c t - 2) = labOf3 w c t := by
  rcases labOf3_cases (w := w) ht hc with ⟨j, -, hl⟩ | ⟨t₀, h1, h2, h3, h4, h5, hl⟩
  · exfalso; have := j.isLt; omega
  · rw [hl, Nat.add_sub_cancel]
    refine ⟨h1, h2, h3, h4, ?_⟩
    rcases labOf3_cases (w := w) h1 hc with ⟨j, hj, -⟩ | ⟨t₁, g1, g2, g3, -, g5, gl⟩
    · exact absurd (h3.symm.trans hj) (h4 j)
    · rw [gl]
      have := h5 t₁ g1 (g3.trans h3)
      omega

/-- The pattern is valid. -/
lemma validB3_xsOf3 : validB3 (xsOf3 w c) = true := by
  unfold validB3 xsOf3
  simp only [List.length_cons, List.length_nil, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, true_and]
  intro k hk
  have key : ∀ t, 4 ≤ t → t < 10 → (labOf3 w c t < 6 ∨ labOf3 w c t = t + 2 ∨
      ∃ t' < t, 4 ≤ t' ∧ labOf3 w c t = t' + 2 ∧ labOf3 w c t' = t' + 2) := by
    intro t ht4 ht10
    by_cases h6 : labOf3 w c t < 6
    · exact Or.inl h6
    · obtain ⟨g1, g2, g3, g4, g5⟩ := labOf3_first hc hw t ht4 (by omega)
      rcases Nat.lt_or_ge (labOf3 w c t - 2) t with hlt | hge
      · exact Or.inr (Or.inr ⟨labOf3 w c t - 2, hlt, g1, by omega, by omega⟩)
      · exact Or.inr (Or.inl (by omega))
  interval_cases k
  · rcases key 4 (by norm_num) (by norm_num) with h | h | ⟨t', ht', h4, -, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · omega
  · rcases key 5 (by norm_num) (by norm_num) with h | h | ⟨t', ht', h4, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · obtain rfl : t' = 4 := by omega
      exact Or.inr (Or.inr ⟨0, by norm_num, h1, h2⟩)
  · rcases key 6 (by norm_num) (by norm_num) with h | h | ⟨t', ht', h4, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · interval_cases t'
      · exact Or.inr (Or.inr ⟨0, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨1, by norm_num, h1, h2⟩)
  · rcases key 7 (by norm_num) (by norm_num) with h | h | ⟨t', ht', h4, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · interval_cases t'
      · exact Or.inr (Or.inr ⟨0, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨1, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨2, by norm_num, h1, h2⟩)
  · rcases key 8 (by norm_num) (by norm_num) with h | h | ⟨t', ht', h4, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · interval_cases t'
      · exact Or.inr (Or.inr ⟨0, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨1, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨2, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨3, by norm_num, h1, h2⟩)
  · rcases key 9 (by norm_num) (by norm_num) with h | h | ⟨t', ht', h4, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · interval_cases t'
      · exact Or.inr (Or.inr ⟨0, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨1, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨2, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨3, by norm_num, h1, h2⟩)
      · exact Or.inr (Or.inr ⟨4, by norm_num, h1, h2⟩)

omit hc hw in
/-- The label at position `t` of the pattern's walk. -/
lemma wlAt3_xsOf3 (t : ℕ) : wlAt3 (xsOf3 w c) t = labOf3 w c (t % 10) := by
  have h10 : t % 10 < 10 := Nat.mod_lt _ (by norm_num)
  unfold wlAt3 wl3 xsOf3
  generalize t % 10 = s at h10 ⊢
  interval_cases s <;> simp [labOf3_lt4]

omit hc hw in
/-- The occurring labels are labels of positions. -/
lemma used3_iff (l : ℕ) (hl : usedB3 (xsOf3 w c) l = true) :
    l < 6 ∨ ∃ t, 4 ≤ t ∧ t < 10 ∧ labOf3 w c t = l := by
  unfold usedB3 xsOf3 at hl
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  rcases hl with hl | hl | hl | hl | hl | hl | hl
  · exact Or.inl hl
  · exact Or.inr ⟨4, by norm_num, by norm_num, hl.symm⟩
  · exact Or.inr ⟨5, by norm_num, by norm_num, hl.symm⟩
  · exact Or.inr ⟨6, by norm_num, by norm_num, hl.symm⟩
  · exact Or.inr ⟨7, by norm_num, by norm_num, hl.symm⟩
  · exact Or.inr ⟨8, by norm_num, by norm_num, hl.symm⟩
  · exact Or.inr ⟨9, by norm_num, by norm_num, hl.symm⟩

/-- An occurring new label is the first position of a vertex off `c`. -/
lemma used3_new {l : ℕ} (hl : usedB3 (xsOf3 w c) l = true) (h6 : 6 ≤ l) :
    4 ≤ l - 2 ∧ (∀ j : Fin 6, w (l - 2) ≠ c j) ∧ (∀ u, 4 ≤ u → w u = w (l - 2) → l - 2 ≤ u) := by
  rcases used3_iff l hl with hl6 | ⟨t, ht4, ht10, rfl⟩
  · omega
  · obtain ⟨g1, g2, g3, g4, g5⟩ := labOf3_first hc hw t ht4 h6
    refine ⟨g1, fun j hj => g4 j (g3.symm.trans hj), fun u hu hwu => ?_⟩
    rcases labOf3_cases (w := w) g1 hc with ⟨j, hj, -⟩ | ⟨t₁, k1, k2, k3, k4, k5, kl⟩
    · exact absurd (g3.symm.trans hj) (g4 j)
    · have := k5 u hu hwu
      omega

/-- `phiL3` is injective on the occurring labels. -/
lemma phiL3_inj {l₁ l₂ : ℕ} (h₁ : usedB3 (xsOf3 w c) l₁ = true) (h₂ : usedB3 (xsOf3 w c) l₂ = true)
    (h : phiL3 w c l₁ = phiL3 w c l₂) : l₁ = l₂ := by
  by_cases a₁ : l₁ < 6 <;> by_cases a₂ : l₂ < 6
  · unfold phiL3 at h
    rw [dite_eq_left a₁, dite_eq_left a₂] at h
    have := congrArg Fin.val (hc h)
    simpa using this
  · obtain ⟨-, n₂, -⟩ := used3_new hc hw h₂ (by omega)
    unfold phiL3 at h
    rw [dite_eq_left a₁, dite_eq_right a₂] at h
    exact absurd h.symm (n₂ _)
  · obtain ⟨-, n₁, -⟩ := used3_new hc hw h₁ (by omega)
    unfold phiL3 at h
    rw [dite_eq_right a₁, dite_eq_left a₂] at h
    exact absurd h (n₁ _)
  · obtain ⟨g₁, -, m₁⟩ := used3_new hc hw h₁ (by omega)
    obtain ⟨g₂, -, m₂⟩ := used3_new hc hw h₂ (by omega)
    unfold phiL3 at h
    rw [dite_eq_right a₁, dite_eq_right a₂] at h
    have e1 := m₁ (l₂ - 2) g₂ h.symm
    have e2 := m₂ (l₁ - 2) g₁ h
    omega

end Labels

end Thrackle78.Proof
