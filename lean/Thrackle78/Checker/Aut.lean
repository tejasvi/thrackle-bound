import Thrackle78.Checker.SubRestrict

/-!
# Automorphisms of a listing preserve planarity of the augmented graph

`IsAut E σ τ fl`: edge `e` goes to edge `σ e`, its ends by `τ`, reversed if `fl e`. The image `P.aut` of a crossing
system has the row of `σ e` equal to the row of `e` mapped by `σ`, reversed if `fl e`. **`planar_aut`**: if `aug E P`
is planar, so is `aug E (P.aut …)`. The relabelling `psiAut` (original vertices by `τ⁻¹`, crossings by `σ⁻¹`,
subdivision vertices of reversed edges counted from the other end) maps the path of `e'` in `aug E (P.aut …)` onto the
path of `σ⁻¹ e'` in `aug E P`, reversed if flipped, and the diamonds onto diamonds.
-/

namespace Thrackle78

variable {n m : ℕ}

/-- `(σ, τ, fl)` is an automorphism of the listing `E`: edge `e` goes to edge `σ e`, with its ends mapped by `τ` and
reversed if `fl e`. -/
def IsAut (E : Fin m → Fin n × Fin n) (σ : Fin m ≃ Fin m) (τ : Fin n ≃ Fin n) (fl : Fin m → Bool) : Prop :=
  ∀ e, E (σ e) = if fl e then (τ (E e).2, τ (E e).1) else (τ (E e).1, τ (E e).2)

lemma IsAut.nonInc {E : Fin m → Fin n × Fin n} {σ : Fin m ≃ Fin m} {τ : Fin n ≃ Fin n} {fl : Fin m → Bool}
    (h : IsAut E σ τ fl) (e f : Fin m) : NonInc E (σ e) (σ f) ↔ NonInc E e f := by
  unfold NonInc
  rw [h e, h f]
  have hσ : σ e ≠ σ f ↔ e ≠ f := σ.injective.ne_iff
  cases fl e <;> cases fl f <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, ne_eq, Equiv.apply_eq_iff_eq, hσ] <;> tauto

/-- The image of a crossing system under an automorphism of the listing. -/
def CrossingSystem.aut {E : Fin m → Fin n × Fin n} (P : CrossingSystem E) (σ : Fin m ≃ Fin m) (τ : Fin n ≃ Fin n)
    (fl : Fin m → Bool) (h : IsAut E σ τ fl) : CrossingSystem E where
  π e' := if fl (σ.symm e') then ((P.π (σ.symm e')).map σ).reverse else (P.π (σ.symm e')).map σ
  nodup e' := by
    split_ifs
    · exact List.nodup_reverse.2 ((P.nodup _).map σ.injective)
    · exact (P.nodup _).map σ.injective
  mem e' f' := by
    have key : f' ∈ (P.π (σ.symm e')).map σ ↔ NonInc E e' f' := by
      rw [List.mem_map]
      constructor
      · rintro ⟨g, hg, rfl⟩
        have := (h.nonInc (σ.symm e') g).2 ((P.mem _ _).1 hg)
        simpa using this
      · intro hn
        refine ⟨σ.symm f', (P.mem _ _).2 ((h.nonInc (σ.symm e') (σ.symm f')).1 (by simpa using hn)), by simp⟩
    split_ifs
    · rw [List.mem_reverse]; exact key
    · exact key

end Thrackle78

namespace Thrackle78.Checker

open SimpleGraph

variable {n m : ℕ} {E : Fin m → Fin n × Fin n} {σ : Fin m ≃ Fin m} {τ : Fin n ≃ Fin n} {fl : Fin m → Bool}
  (h : IsAut E σ τ fl) (P : CrossingSystem E)

/-- The relabelling of `aug E (P.aut …)` into `aug E P`. -/
def psiAut (P : CrossingSystem E) (σ : Fin m ≃ Fin m) (τ : Fin n ≃ Fin n) (fl : Fin m → Bool) :
    AV n m → AV n m
  | Sum.inl v => Sum.inl (τ.symm v)
  | Sum.inr (Sum.inl (a, b)) => xv (σ.symm a) (σ.symm b)
  | Sum.inr (Sum.inr (e', t)) =>
    sv (σ.symm e') (if fl (σ.symm e') then (P.π (σ.symm e')).length - 2 - t.val else t.val)

lemma aut_π (e' : Fin m) : (P.aut σ τ fl h).π e' =
    if fl (σ.symm e') then ((P.π (σ.symm e')).map σ).reverse else (P.π (σ.symm e')).map σ := rfl

lemma aut_length (e' : Fin m) : ((P.aut σ τ fl h).π e').length = (P.π (σ.symm e')).length := by
  rw [aut_π]; split_ifs <;> simp

lemma aut_pathLen (e' : Fin m) :
    (pathNodes E (P.aut σ τ fl h) e').length = (pathNodes E P (σ.symm e')).length := by
  have h1 := len_cases (P.aut σ τ fl h) e'
  have h2 := len_cases P (σ.symm e')
  have h3 := aut_length h P e'
  omega

/-- The position on the path of `σ⁻¹ e'` of position `q` on the path of `e'`. -/
def posA (P : CrossingSystem E) (σ : Fin m ≃ Fin m) (fl : Fin m → Bool) (e' : Fin m) (q : ℕ) : ℕ :=
  if fl (σ.symm e') then (pathNodes E P (σ.symm e')).length - 1 - q else q

lemma psiAut_ov (v : Fin n) : psiAut P σ τ fl (ov v) = ov (τ.symm v) := rfl

lemma psiAut_xv (a b : Fin m) : psiAut P σ τ fl (xv a b) = xv (σ.symm a) (σ.symm b) := by
  show xv (σ.symm (min a b)) (σ.symm (max a b)) = xv (σ.symm a) (σ.symm b)
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab]
  · rw [min_eq_right hab, max_eq_left hab]
    exact xv_comm _ _

lemma psiAut_sv (e' : Fin m) (t : ℕ) (ht : t < m) : psiAut P σ τ fl (sv e' t) =
    sv (σ.symm e') (if fl (σ.symm e') then (P.π (σ.symm e')).length - 2 - t else t) := by
  show sv (σ.symm e') (if fl (σ.symm e') then (P.π (σ.symm e')).length - 2 - t % m else t % m) = _
  rw [Nat.mod_eq_of_lt ht]

/-- **The relabelling on the paths.** -/
lemma psiAut_node (e' : Fin m) (q : ℕ) (hq : q < (pathNodes E (P.aut σ τ fl h) e').length) :
    psiAut P σ τ fl (node (P.aut σ τ fl h) e' q) = node P (σ.symm e') (posA P σ fl e' q) := by
  have hl := len_cases P (σ.symm e')
  have hlen := aut_pathLen h P e'
  have hk := aut_length h P e'
  have hm : ∀ j, j < (P.π (σ.symm e')).length → j < m := fun j hj =>
    lt_of_lt_of_le hj ((P.nodup _).length_le_card.trans (by simp))
  have hE : E e' = if fl (σ.symm e') then (τ (E (σ.symm e')).2, τ (E (σ.symm e')).1)
      else (τ (E (σ.symm e')).1, τ (E (σ.symm e')).2) := by
    have := h (σ.symm e'); rwa [Equiv.apply_symm_apply] at this
  unfold posA
  rcases node_cases (P.aut σ τ fl h) e' q hq with ⟨h0, ha⟩ | ⟨h0, ha⟩ | ⟨h0, hq1, hpar, hj, ha⟩ |
      ⟨h0, hq1, hpar, hj, ha⟩
  · subst h0
    rw [ha, psiAut_ov, hE]
    split_ifs with hf
    · simp only [Equiv.symm_apply_apply]
      rw [node_last P _ _ (by omega)]
    · simp only [Equiv.symm_apply_apply]
      rw [node_zero]
  · rw [ha, psiAut_ov, hE]
    split_ifs with hf
    · simp only [Equiv.symm_apply_apply]
      rw [show (pathNodes E P (σ.symm e')).length - 1 - q = 0 by omega, node_zero]
    · simp only [Equiv.symm_apply_apply]
      rw [node_last P _ _ (by omega)]
  · rw [ha, psiAut_xv]
    simp only [aut_π] at hj ⊢
    split_ifs with hf
    · have hj' : q / 2 < (P.π (σ.symm e')).length := by simpa [hf] using hj
      have := node_odd P (σ.symm e') ((P.π (σ.symm e')).length - 1 - q / 2) (by omega)
      rw [show 2 * ((P.π (σ.symm e')).length - 1 - q / 2) + 1 = (pathNodes E P (σ.symm e')).length - 1 - q by
        omega] at this
      rw [this]
      simp only [List.getElem_reverse, List.getElem_map, Equiv.symm_apply_apply, List.length_map]
    · have := node_odd P (σ.symm e') (q / 2) (by simpa [hf] using hj)
      rw [show 2 * (q / 2) + 1 = q by omega] at this
      rw [this]
      simp only [List.getElem_map, Equiv.symm_apply_apply]
  · rw [ha, psiAut_sv P e' _ (by have := hm (q / 2) (by omega); omega)]
    split_ifs with hf
    · have := node_even P (σ.symm e') ((P.π (σ.symm e')).length - 2 - (q / 2 - 1)) (by omega)
      rw [show 2 * ((P.π (σ.symm e')).length - 2 - (q / 2 - 1)) + 2 = (pathNodes E P (σ.symm e')).length - 1 - q by
        omega] at this
      rw [this]
    · have := node_even P (σ.symm e') (q / 2 - 1) (by omega)
      rw [show 2 * (q / 2 - 1) + 2 = q by omega] at this
      rw [this]


lemma posA_lt (e' : Fin m) (q : ℕ) (hq : q < (pathNodes E (P.aut σ τ fl h) e').length) :
    posA P σ fl e' q < (pathNodes E P (σ.symm e')).length := by
  have := aut_pathLen h P e'
  unfold posA; split_ifs <;> omega

lemma posA_inj (e' : Fin m) {q₁ q₂ : ℕ} (h₁ : q₁ < (pathNodes E (P.aut σ τ fl h) e').length)
    (h₂ : q₂ < (pathNodes E (P.aut σ τ fl h) e').length) (hq : posA P σ fl e' q₁ = posA P σ fl e' q₂) : q₁ = q₂ := by
  have := aut_pathLen h P e'
  unfold posA at hq; split_ifs at hq <;> omega

/-- The ends of the paths are original vertices. -/
lemma node_end_ov (Q : CrossingSystem E) (e : Fin m) (q : ℕ) (hq : q = 0 ∨ q + 1 = (pathNodes E Q e).length) :
    ∃ v, node Q e q = ov v := by
  rcases hq with rfl | hq
  · exact ⟨_, node_zero Q e⟩
  · exact ⟨_, node_last Q e q hq⟩

/-- **Injectivity on the nodes.** -/
lemma psiAut_node_inj (e₁ e₂ : Fin m) (q₁ q₂ : ℕ) (hq₁ : q₁ < (pathNodes E (P.aut σ τ fl h) e₁).length)
    (hq₂ : q₂ < (pathNodes E (P.aut σ τ fl h) e₂).length)
    (heq : psiAut P σ τ fl (node (P.aut σ τ fl h) e₁ q₁) = psiAut P σ τ fl (node (P.aut σ τ fl h) e₂ q₂)) :
    node (P.aut σ τ fl h) e₁ q₁ = node (P.aut σ τ fl h) e₂ q₂ := by
  have heq' := heq
  rw [psiAut_node h P e₁ q₁ hq₁, psiAut_node h P e₂ q₂ hq₂] at heq'
  have hl₁ := aut_pathLen h P e₁
  have hl₂ := aut_pathLen h P e₂
  rcases node_eq_cases P (σ.symm e₁) (σ.symm e₂) _ _ (posA_lt h P e₁ q₁ hq₁) (posA_lt h P e₂ q₂ hq₂) heq' with
      ⟨he, hp⟩ | ⟨h1, h2⟩ | ⟨hpar₁, hpar₂, hj₁, hj₂, hf₁, hf₂⟩
  · have he' := σ.symm.injective he
    subst he'
    rw [posA_inj h P e₁ hq₁ hq₂ hp]
  · have g1 : q₁ = 0 ∨ q₁ + 1 = (pathNodes E (P.aut σ τ fl h) e₁).length := by
      unfold posA at h1; split_ifs at h1 <;> omega
    have g2 : q₂ = 0 ∨ q₂ + 1 = (pathNodes E (P.aut σ τ fl h) e₂).length := by
      unfold posA at h2; split_ifs at h2 <;> omega
    obtain ⟨v₁, hv₁⟩ := node_end_ov _ e₁ q₁ g1
    obtain ⟨v₂, hv₂⟩ := node_end_ov _ e₂ q₂ g2
    rw [hv₁, hv₂, psiAut_ov, psiAut_ov] at heq
    rw [hv₁, hv₂, τ.symm.injective (ov_inj heq)]
  · -- both are crossings: the node of `e₁` is the crossing with `e₂`
    have cross : ∀ (a b : Fin m) (q : ℕ) (hq : q < (pathNodes E (P.aut σ τ fl h) a).length),
        posA P σ fl a q % 2 = 1 → ∀ (hj : posA P σ fl a q / 2 < (P.π (σ.symm a)).length),
        (P.π (σ.symm a))[posA P σ fl a q / 2] = σ.symm b → node (P.aut σ τ fl h) a q = xv a b := by
      intro a b q hq hpar hj hf
      have hla := aut_pathLen h P a
      have hka := aut_length h P a
      have hlc := len_cases P (σ.symm a)
      have hps := psiAut_node h P a q hq
      have hnode : node P (σ.symm a) (posA P σ fl a q) = xv (σ.symm a) (σ.symm b) := by
        have := node_odd P (σ.symm a) (posA P σ fl a q / 2) hj
        rw [show 2 * (posA P σ fl a q / 2) + 1 = posA P σ fl a q by omega, hf] at this
        exact this
      have hne : σ.symm a ≠ σ.symm b := by
        intro hab
        have hmem : σ.symm b ∈ P.π (σ.symm a) := hf ▸ List.getElem_mem _
        exact ((P.mem _ _).1 hmem).1 hab
      rcases node_cases (P.aut σ τ fl h) a q hq with ⟨h0, ha⟩ | ⟨h0, ha⟩ | ⟨h0, hq1, hp, hjq, ha⟩ |
          ⟨h0, hq1, hp, hjq, ha⟩
      · exfalso; unfold posA at hpar hj; split_ifs at hpar hj <;> omega
      · exfalso; unfold posA at hpar hj; split_ifs at hpar hj <;> omega
      · rw [ha] at hps ⊢
        rw [psiAut_xv, hnode] at hps
        rcases xv_inj hps with ⟨-, hg⟩ | ⟨hab, -⟩
        · rw [σ.symm.injective hg]
        · exact absurd hab hne
      · rw [ha, psiAut_sv P a _ (by
          have := (P.nodup (σ.symm a)).length_le_card; simp at this; omega), hnode] at hps
        exact absurd hps.symm (xv_ne_sv _ _ _ _)
    rw [cross e₁ e₂ q₁ hq₁ hpar₁ hj₁ hf₁, cross e₂ e₁ q₂ hq₂ hpar₂ hj₂ hf₂, xv_comm]


omit h in
/-- Consecutive nodes of a path form a path edge. -/
lemma mem_pathEdges_consec (Q : CrossingSystem E) (e : Fin m) (p : ℕ) (hp : p + 1 < (pathNodes E Q e).length) :
    s(node Q e p, node Q e (p + 1)) ∈ pathEdges E Q e := by
  unfold pathEdges
  rw [List.mem_map]
  refine ⟨((pathNodes E Q e)[p], (pathNodes E Q e)[p + 1]), ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    refine ⟨p, by simp; omega, ?_⟩
    simp [List.getElem_zip, List.getElem_tail]
  · simp [node_eq_getElem Q e p (by omega), node_eq_getElem Q e (p + 1) hp]

omit h in
/-- The cross pairs of a diamond are edges of the augmented graph. -/
lemma diamond_cross (Q : CrossingSystem E) {e f : Fin m} (hn : NonInc E e f) {a b : AV n m}
    (ha : a = (nbrs E Q e f).1 ∨ a = (nbrs E Q e f).2) (hb : b = (nbrs E Q f e).1 ∨ b = (nbrs E Q f e).2) :
    s(a, b) ∈ augEdges E Q := by
  rcases lt_or_gt_of_ne hn.1 with hlt | hgt
  · refine Or.inr ⟨e, f, hlt, hn, ?_⟩
    unfold diamondEdges
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr Sym2.eq_swap))
    · exact Or.inr (Or.inl Sym2.eq_swap)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · refine Or.inr ⟨f, e, hgt, nonInc_symm hn, ?_⟩
    unfold diamondEdges
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl Sym2.eq_swap
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))

/-- The neighbours of a crossing go to the neighbours of the image crossing (swapped if flipped). -/
lemma psiAut_nbrs (e' f' : Fin m) (c : ℕ) (hc : c < ((P.aut σ τ fl h).π e').length)
    (hcf : ((P.aut σ τ fl h).π e')[c] = f') (a : AV n m)
    (ha : a = (nbrs E (P.aut σ τ fl h) e' f').1 ∨ a = (nbrs E (P.aut σ τ fl h) e' f').2) :
    psiAut P σ τ fl a = (nbrs E P (σ.symm e') (σ.symm f')).1 ∨
      psiAut P σ τ fl a = (nbrs E P (σ.symm e') (σ.symm f')).2 := by
  have hk := aut_length h P e'
  have hlen := aut_pathLen h P e'
  have hl := len_cases P (σ.symm e')
  have A1' := nbrs_fst_node (P.aut σ τ fl h) e' c hc
  have A2' := nbrs_snd_node (P.aut σ τ fl h) e' c hc
  rw [hcf] at A1' A2'
  have p1 := psiAut_node h P e' (2 * c) (by omega)
  have p2 := psiAut_node h P e' (2 * c + 2) (by have := len_cases (P.aut σ τ fl h) e'; omega)
  -- the index of the crossing in `P`
  obtain ⟨j, hj, hjf, hpos⟩ : ∃ j, ∃ hj : j < (P.π (σ.symm e')).length,
      (P.π (σ.symm e'))[j] = σ.symm f' ∧
      ((posA P σ fl e' (2 * c) = 2 * j ∧ posA P σ fl e' (2 * c + 2) = 2 * j + 2) ∨
        (posA P σ fl e' (2 * c) = 2 * j + 2 ∧ posA P σ fl e' (2 * c + 2) = 2 * j)) := by
    have hcf' := hcf
    simp only [aut_π] at hcf' hc
    unfold posA
    split_ifs at hcf' hc ⊢ with hf
    · have hc' : c < (P.π (σ.symm e')).length := by simpa using hc
      refine ⟨(P.π (σ.symm e')).length - 1 - c, by omega, ?_, Or.inr ⟨by omega, by omega⟩⟩
      simp only [List.getElem_reverse, List.getElem_map, List.length_map] at hcf'
      rw [← hcf', Equiv.symm_apply_apply]
    · refine ⟨c, by simpa using hc, ?_, Or.inl ⟨rfl, rfl⟩⟩
      simp only [List.getElem_map] at hcf'
      rw [← hcf', Equiv.symm_apply_apply]
  have B1 := nbrs_fst_node P (σ.symm e') j hj
  have B2 := nbrs_snd_node P (σ.symm e') j hj
  rw [hjf] at B1 B2
  rcases ha with rfl | rfl
  · rw [A1', p1, B1, B2]
    rcases hpos with ⟨q1, -⟩ | ⟨q1, -⟩
    · exact Or.inl (by rw [q1])
    · exact Or.inr (by rw [q1])
  · rw [A2', p2, B1, B2]
    rcases hpos with ⟨-, q2⟩ | ⟨-, q2⟩
    · exact Or.inr (by rw [q2])
    · exact Or.inl (by rw [q2])

/-- **Adjacency.** Edges of `aug E (P.aut …)` go to edges of `aug E P`. -/
theorem psiAut_adj {x y : AV n m} (hxy : (aug E (P.aut σ τ fl h)).Adj x y) :
    (aug E P).Adj (psiAut P σ τ fl x) (psiAut P σ τ fl y) := by
  have hne' : psiAut P σ τ fl x ≠ psiAut P σ τ fl y := by
    obtain ⟨e₁, q₁, hq₁, hx⟩ := node_of_adj _ hxy
    obtain ⟨e₂, q₂, hq₂, hy⟩ := node_of_adj _ hxy.symm
    intro heq
    rw [← hx, ← hy] at heq
    exact hxy.ne (by rw [← hx, ← hy]; exact psiAut_node_inj h P e₁ e₂ q₁ q₂ hq₁ hq₂ heq)
  refine aug_adj_of_mem P ?_ hne'
  have hz := hxy
  unfold aug at hz
  rw [SimpleGraph.fromEdgeSet_adj] at hz
  obtain ⟨hz, -⟩ := hz
  rcases hz with ⟨e', he⟩ | ⟨e', f', hef, hn, hd⟩
  · obtain ⟨i, hi, hzi⟩ := mem_pathEdges _ e' he
    have hl := aut_pathLen h P e'
    have p1 := psiAut_node h P e' i (by omega)
    have p2 := psiAut_node h P e' (i + 1) hi
    have hpe : s(node P (σ.symm e') (posA P σ fl e' i), node P (σ.symm e') (posA P σ fl e' (i + 1))) ∈
        pathEdges E P (σ.symm e') := by
      unfold posA
      split_ifs with hf
      · have := mem_pathEdges_consec P (σ.symm e') ((pathNodes E P (σ.symm e')).length - 1 - (i + 1)) (by omega)
        rw [show (pathNodes E P (σ.symm e')).length - 1 - (i + 1) + 1 =
          (pathNodes E P (σ.symm e')).length - 1 - i by omega, Sym2.eq_swap] at this
        exact this
      · exact mem_pathEdges_consec P (σ.symm e') i (by omega)
    rcases Sym2.eq_iff.1 hzi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [p1, p2]; exact Or.inl ⟨_, hpe⟩
    · rw [p1, p2, Sym2.eq_swap]; exact Or.inl ⟨_, hpe⟩
  · have hfe : f' ∈ (P.aut σ τ fl h).π e' := ((P.aut σ τ fl h).mem e' f').2 hn
    have hef' : e' ∈ (P.aut σ τ fl h).π f' := ((P.aut σ τ fl h).mem f' e').2 (nonInc_symm hn)
    obtain ⟨c, hc, hcf⟩ := List.mem_iff_getElem.1 hfe
    obtain ⟨c₂, hc₂, hc₂e⟩ := List.mem_iff_getElem.1 hef'
    have hnE : NonInc E (σ.symm e') (σ.symm f') := (h.nonInc _ _).1 (by simpa using hn)
    have imA := psiAut_nbrs h P e' f' c hc hcf
    have imB := psiAut_nbrs h P f' e' c₂ hc₂ hc₂e
    unfold diamondEdges at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd | hd <;> rcases Sym2.eq_iff.1 hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact diamond_cross P hnE (imA _ (Or.inl rfl)) (imB _ (Or.inl rfl))
    · rw [Sym2.eq_swap]; exact diamond_cross P hnE (imA _ (Or.inl rfl)) (imB _ (Or.inl rfl))
    · rw [Sym2.eq_swap]; exact diamond_cross P hnE (imA _ (Or.inr rfl)) (imB _ (Or.inl rfl))
    · exact diamond_cross P hnE (imA _ (Or.inr rfl)) (imB _ (Or.inl rfl))
    · exact diamond_cross P hnE (imA _ (Or.inr rfl)) (imB _ (Or.inr rfl))
    · rw [Sym2.eq_swap]; exact diamond_cross P hnE (imA _ (Or.inr rfl)) (imB _ (Or.inr rfl))
    · rw [Sym2.eq_swap]; exact diamond_cross P hnE (imA _ (Or.inl rfl)) (imB _ (Or.inr rfl))
    · exact diamond_cross P hnE (imA _ (Or.inl rfl)) (imB _ (Or.inr rfl))

/-- **Automorphisms preserve planarity of the augmented graph.** -/
theorem planar_aut : Planar (aug E P) → Planar (aug E (P.aut σ τ fl h)) := by
  intro hP
  by_contra hnp
  refine not_planar_of_map hnp (fun x => {psiAut P σ τ fl x}) (fun x _ => Set.singleton_nonempty _)
    (fun x _ => ?_) (fun x x' hx hx' hxx' => ?_) (fun x x' hxx' => ⟨_, rfl, _, rfl, psiAut_adj h P hxx'⟩) hP
  · have : Nonempty ({psiAut P σ τ fl x} : Set (AV n m)) := ⟨⟨_, rfl⟩⟩
    refine SimpleGraph.Connected.mk fun u v => ?_
    have : u = v := Subtype.ext (u.2.trans v.2.symm)
    rw [this]
  · rw [Set.disjoint_singleton]
    obtain ⟨y, hy⟩ := hx
    obtain ⟨y', hy'⟩ := hx'
    obtain ⟨e₁, q₁, hq₁, rfl⟩ := node_of_adj _ hy
    obtain ⟨e₂, q₂, hq₂, rfl⟩ := node_of_adj _ hy'
    exact fun heq => hxx' (psiAut_node_inj h P e₁ e₂ q₁ q₂ hq₁ hq₂ heq)

end Thrackle78.Checker
