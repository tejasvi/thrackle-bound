import Thrackle78.Proof.Run610Lab

/-!
# The run lemma: soundness of the checks

For a walk `w` along a 6-cycle `c` of `G` (`w t = c t`, `t ≤ 4`) with adjacent consecutive vertices, period 10, no
spikes, edges of `c` used at most once and other edges at most twice among the ten steps: `violB` fails on its
pattern, and every certificate contradicts triangle-freeness, the absence of `C4`, the 6-6 lemma or the 6-8 lemma.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

section Sound

variable {w : ℕ → V} {c : Fin 6 → V} (hcyc : IsCycleMap G c) (hw : ∀ t (ht : t < 5), c ⟨t, by omega⟩ = w t)
  (hadj : ∀ t, G.Adj (w t) (w (t + 1))) (hper : ∀ t, w (t % 10) = w t)
include hcyc hw

omit [Fintype V] in
/-- Edges of the union are edges of `G`. -/
lemma uEdge610_adj (hadj : ∀ t, G.Adj (w t) (w (t + 1))) (hper : ∀ t, w (t % 10) = w t) {l₁ l₂ : ℕ}
    (h : uEdgeB610 (xsOf w c) l₁ l₂ = true) : G.Adj (phiL w c l₁) (phiL w c l₂) := by
  unfold uEdgeB610 at h
  rw [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨t, ht, hpq⟩
  · unfold cEdgeB at h
    rw [decide_eq_true_iff] at h
    obtain ⟨hp, hq, hpq⟩ := h
    have hrot : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
    unfold phiL
    rw [dite_eq_left hp, dite_eq_left hq]
    rcases hpq with e | e
    · have := hcyc.2.2 ⟨l₁, hp⟩
      convert this using 2
      ext; rw [hrot]; simp [e]
    · have := hcyc.2.2 ⟨l₂, hq⟩
      refine SimpleGraph.Adj.symm ?_
      convert this using 2
      ext; rw [hrot]; simp [e]
  · rw [decide_eq_true_iff] at hpq
    have hc := hcyc.2.1
    have e1 : phiL w c (wlAt (xsOf w c) t) = w t := by
      rw [wlAt_xsOf, phiL_labOf hc hw, hper]
    have e2 : phiL w c (wlAt (xsOf w c) (t + 1)) = w (t + 1) := by
      rw [wlAt_xsOf, phiL_labOf hc hw, hper]
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e1, e2]; exact hadj t
    · rw [e1, e2]; exact (hadj t).symm

omit [Fintype V] in
/-- A certified cycle of the union is a cycle of `G`. -/
lemma cycOK_cycleMap (hadj : ∀ t, G.Adj (w t) (w (t + 1))) (hper : ∀ t, w (t % 10) = w t) {k : ℕ} (hk : 3 ≤ k)
    {cl : List ℕ} (h : cycOK (xsOf w c) k cl = true) :
    IsCycleMap G (fun i : Fin k => phiL w c (cl.getD i.val 0)) := by
  unfold cycOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hlen, hnd⟩, hused⟩, hedge⟩ := h
  have hget : ∀ i : Fin k, cl.getD i.val 0 ∈ cl := fun i => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  refine ⟨hk, fun i j hij => ?_, fun i => ?_⟩
  · have := phiL_inj hcyc.2.1 hw (hused _ (hget i)) (hused _ (hget j)) hij
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 this)
  · have hrot : (finRotate k i).val = (i.val + 1) % k := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [finRotate_val]
      split_ifs with h1
      · rw [Nat.mod_eq_of_lt (by omega)]
      · have : i.val = m := by omega
        rw [this, Nat.mod_self]
    have := uEdge610_adj hcyc hw hadj hper (hedge i.val i.isLt)
    simp only at this ⊢
    rw [hrot]
    exact this


omit [Fintype V] in
/-- The vertices of equal labels. -/
lemma phiL_wlAt (hper : ∀ t, w (t % 10) = w t) (t : ℕ) : phiL w c (wlAt (xsOf w c) t) = w t := by
  rw [wlAt_xsOf, phiL_labOf hcyc.2.1 hw, hper]

omit [Fintype V] in
/-- **No violation**: the pattern of a facial walk along a 6-face passes `violB`. -/
lemma violB_xsOf (hadj : ∀ t, G.Adj (w t) (w (t + 1))) (hper : ∀ t, w (t % 10) = w t)
    (hspike : ∀ t, w t ≠ w (t + 2))
    (hcC : ∀ x ∈ cycleEdges c, ((List.range 10).filter fun u => decide (s(w u, w (u + 1)) = x)).length ≤ 1)
    (hcA : ∀ x, ((List.range 10).filter fun u => decide (s(w u, w (u + 1)) = x)).length ≤ 2) :
    violB (xsOf w c) = false := by
  have lab := phiL_wlAt hcyc hw hper
  have step_eq : ∀ t u, sameStep (xsOf w c) t u = true → s(w u, w (u + 1)) = s(w t, w (t + 1)) := by
    intro t u h
    unfold sameStep at h
    rw [decide_eq_true_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← lab t, ← lab (t + 1), ← lab u, ← lab (u + 1), h1, h2]
    · rw [← lab t, ← lab (t + 1), ← lab u, ← lab (u + 1), h1, h2]
      exact Sym2.eq_swap
  have mult_le : ∀ t, stepMult (xsOf w c) t ≤
      ((List.range 10).filter fun u => decide (s(w u, w (u + 1)) = s(w t, w (t + 1)))).length := by
    intro t
    unfold stepMult
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro u _ hu
    rw [decide_eq_true_iff]
    exact step_eq t u hu
  unfold violB
  simp only [Bool.or_eq_false_iff, List.any_eq_false, List.mem_range, decide_eq_true_eq, Bool.and_eq_true,
    not_and]
  refine ⟨⟨⟨fun t _ h => ?_, fun t _ h => ?_⟩, fun t _ hC h2 => ?_⟩, fun t _ h3 => ?_⟩
  · exact (hadj t).ne (by rw [← lab t, ← lab (t + 1), h])
  · exact hspike t (by rw [← lab t, ← lab (t + 2), h])
  · have hx : s(w t, w (t + 1)) ∈ cycleEdges c := by
      rw [← lab t, ← lab (t + 1)]
      unfold cEdgeB at hC
      rw [decide_eq_true_iff] at hC
      obtain ⟨hp, hq, hpq⟩ := hC
      have hrot : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
      unfold phiL
      rw [dite_eq_left hp, dite_eq_left hq]
      simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and]
      rcases hpq with e | e
      · refine ⟨⟨_, hp⟩, ?_⟩
        congr 2
        ext; rw [hrot]; simp [e]
      · refine ⟨⟨_, hq⟩, ?_⟩
        rw [Sym2.eq_swap]
        congr 2
        ext; rw [hrot]; simp [e]
    have := hcC _ hx
    have := mult_le t
    omega
  · have := hcA (s(w t, w (t + 1)))
    have := mult_le t
    omega

omit [Fintype V] in
/-- **Certificates are impossible.** -/
lemma cert610_false (hadj : ∀ t, G.Adj (w t) (w (t + 1))) (hper : ∀ t, w (t % 10) = w t)
    (htri : G.CliqueFree 3) (hc4 : ∀ d : Fin 4 → V, IsCycleMap G d → False)
    (h66 : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → (∃ i j, c i = d j) → cycleEdges c = cycleEdges d)
    (h68 : ∀ (c : Fin 6 → V) (d : Fin 8 → V), IsCycleMap G c → IsCycleMap G d →
      Disjoint (cycleEdges c) (cycleEdges d))
    {cert : ℕ × List ℕ × List ℕ} (h : checkCert610 (xsOf w c) cert = true) : False := by
  have hrot : ∀ {k : ℕ} (hk : 0 < k) (i : Fin k), (finRotate k i).val = (i.val + 1) % k := by
    intro k hk i
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [finRotate_val]
    split_ifs with h1
    · rw [Nat.mod_eq_of_lt (by omega)]
    · have : i.val = m := by omega
      rw [this, Nat.mod_self]
  -- edges of certified cycles
  have edge_of : ∀ {k : ℕ} (hk : 3 ≤ k) {cl : List ℕ}, cycOK (xsOf w c) k cl = true → ∀ i : Fin k,
      s(phiL w c (cl.getD i.val 0), phiL w c (cl.getD ((i.val + 1) % k) 0)) ∈
        cycleEdges (fun i : Fin k => phiL w c (cl.getD i.val 0)) := by
    intro k hk cl hcl i
    simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, by rw [hrot (by omega) i]⟩
  have used_of : ∀ {k : ℕ} {cl : List ℕ}, cycOK (xsOf w c) k cl = true → ∀ i, i < k →
      usedB610 (xsOf w c) (cl.getD i 0) = true := by
    intro k cl hcl i hi
    unfold cycOK at hcl
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcl
    exact hcl.1.2 _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  unfold checkCert610 at h
  split at h
  · -- a triangle
    have hd := cycOK_cycleMap hcyc hw hadj hper (by norm_num) h
    obtain ⟨-, hinj, hadj3⟩ := hd
    have a01 := hadj3 0
    have a12 := hadj3 1
    have a20 := hadj3 2
    simp only [show finRotate 3 0 = 1 by decide, show finRotate 3 1 = 2 by decide,
      show finRotate 3 2 = 0 by decide] at a01 a12 a20
    apply htri {phiL w c (cert.2.1.getD 0 0), phiL w c (cert.2.1.getD 1 0), phiL w c (cert.2.1.getD 2 0)}
    rw [is3Clique_triple_iff]
    exact ⟨a01, a20.symm, a12⟩
  · exact hc4 _ (cycOK_cycleMap hcyc hw hadj hper (by norm_num) h)
  · -- two 6-cycles with a common vertex and different edges
    simp only [Bool.and_eq_true, List.any_eq_true, List.contains_iff_mem, List.mem_range, Bool.not_eq_true',
      List.any_eq_false, not_exists, not_and] at h
    obtain ⟨⟨⟨h1, h2⟩, l, hl1, hl2⟩, i, hi, hno⟩ := h
    have d1 := cycOK_cycleMap hcyc hw hadj hper (by norm_num) h1
    have d2 := cycOK_cycleMap hcyc hw hadj hper (by norm_num) h2
    obtain ⟨i1, hi1, e1⟩ := List.mem_iff_getElem.1 hl1
    obtain ⟨i2, hi2, e2⟩ := List.mem_iff_getElem.1 hl2
    have hlen1 : cert.2.1.length = 6 := by unfold cycOK at h1; simp at h1; exact h1.1.1.1
    have hlen2 : cert.2.2.length = 6 := by unfold cycOK at h2; simp at h2; exact h2.1.1.1
    have heq := h66 _ _ d1 d2 ⟨⟨i1, by omega⟩, ⟨i2, by omega⟩, by
      simp only
      rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2, e1, e2]⟩
    have hx := edge_of (by norm_num) h1 ⟨i, hi⟩
    rw [heq] at hx
    simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, hj⟩ := hx
    rw [hrot (by norm_num) j] at hj
    apply hno j.val j.isLt
    unfold sameCEdge
    rw [decide_eq_true_iff]
    rcases Sym2.eq_iff.1 hj with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact Or.inl ⟨phiL_inj hcyc.2.1 hw (used_of h1 i hi) (used_of h2 j.val j.isLt) k1.symm,
        phiL_inj hcyc.2.1 hw (used_of h1 _ (Nat.mod_lt _ (by norm_num)))
          (used_of h2 _ (Nat.mod_lt _ (by norm_num))) k2.symm⟩
    · exact Or.inr ⟨phiL_inj hcyc.2.1 hw (used_of h1 i hi) (used_of h2 _ (Nat.mod_lt _ (by norm_num))) k2.symm,
        phiL_inj hcyc.2.1 hw (used_of h1 _ (Nat.mod_lt _ (by norm_num))) (used_of h2 j.val j.isLt) k1.symm⟩
  · -- a 6-cycle and an 8-cycle with a common edge
    simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range] at h
    obtain ⟨⟨h1, h2⟩, i, hi, j, hj, hs⟩ := h
    have d1 := cycOK_cycleMap hcyc hw hadj hper (by norm_num) h1
    have d2 := cycOK_cycleMap hcyc hw hadj hper (by norm_num) h2
    have x1 := edge_of (by norm_num) h1 ⟨i, hi⟩
    have x2 := edge_of (by norm_num) h2 ⟨j, hj⟩
    unfold sameCEdge at hs
    rw [decide_eq_true_iff] at hs
    simp only at x1 x2
    apply Finset.disjoint_left.1 (h68 _ _ d1 d2) x1
    rcases hs with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · rw [k1, k2]; exact x2
    · rw [k1, k2, Sym2.eq_swap]; exact x2
  · exact absurd h (by decide)

end Sound

end Thrackle78.Proof
