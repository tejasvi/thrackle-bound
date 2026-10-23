import Thrackle78.Proof.Hex66Defs

/-!
# The 6-6 edge-overlap enumeration: the certificate check and its soundness

Two 6-cycles `c = v₀ … v₅` and `d = w₀ … w₅` with `w₀ = v₀`, `w₁ = v₁`: for `t < 4`, `w_{t+2}` is `v_{j+2}`
(`xs[t] = some j`) or a new vertex (`xs[t] = none`, label `6 + t`). A certificate is `(99, [])` when `d` has the same
edges as `c`, or `(k, ψ)` embedding class `k` (a triangle, `C4`, `DB(6,6,-1)`, `DB(6,6,-2)`, `DB(6,6,-3)`, `u66v_4`,
`u66v_5`) into the union `U(xs)` on the labels `0 … 9`.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

/-! ## The union and the check -/

/-- The label of `w_k` in the union. -/
def posOf66e (xs : List (Option (Fin 4))) (k : ℕ) : ℕ :=
  if k < 2 then k else
    match xs.getD (k - 2) none with
    | some j => j.val + 2
    | none => 6 + (k - 2)

/-- The label `p` is a vertex of the union. -/
def usedB66e (xs : List (Option (Fin 4))) (p : ℕ) : Bool :=
  decide (p < 6) || (decide (6 ≤ p ∧ p < 10) && (xs.getD (p - 6) none).isNone)

/-- `pq` is an edge of the union. -/
def uEdgeB66e (xs : List (Option (Fin 4))) (p q : ℕ) : Bool :=
  cEdgeB p q ||
    (List.range 6).any fun k => decide ((p = posOf66e xs k ∧ q = posOf66e xs ((k + 1) % 6)) ∨
      (q = posOf66e xs k ∧ p = posOf66e xs ((k + 1) % 6)))

/-- The second 6-cycle uses only edges of the first. -/
def eqB66e (xs : List (Option (Fin 4))) : Bool :=
  (List.range 6).all fun k => cEdgeB (posOf66e xs k) (posOf66e xs ((k + 1) % 6))

/-- The certificate `ψ` embeds the graph of the listing `E` into the union. -/
def checkE66e (xs : List (Option (Fin 4))) (n : ℕ) {m : ℕ} (E : Fin m → Fin n × Fin n) (ψ : List ℕ) : Bool :=
  decide (ψ.length = n) && decide ψ.Nodup && ψ.all (usedB66e xs) &&
    (List.finRange m).all fun e => uEdgeB66e xs (ψ.getD (E e).1 0) (ψ.getD (E e).2 0)

/-- The check of a certificate. -/
def checkCert66e (xs : List (Option (Fin 4))) (cert : ℕ × List ℕ) : Bool :=
  match cert.1 with
  | 0 => checkE66e xs 3 (mkE 3 lK3) cert.2
  | 1 => checkE66e xs 4 (mkE 4 lC4) cert.2
  | 2 => checkE66e xs 10 (mkE 10 lDB661) cert.2
  | 3 => checkE66e xs 9 (mkE 9 lDB662) cert.2
  | 4 => checkE66e xs 8 (mkE 8 lDB663) cert.2
  | 5 => checkE66e xs 8 (mkE 8 lV4) cert.2
  | 6 => checkE66e xs 9 (mkE 9 lV5) cert.2
  | 99 => eqB66e xs
  | _ => false

/-- The assignment is consistent. -/
def validB66e (xs : List (Option (Fin 4))) : Bool := decide (xs.filterMap id).Nodup

/-! ## Soundness -/

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- The labels of the union in `G`. -/
def phi66e (c d : Fin 6 → V) (p : ℕ) : V :=
  if h : p < 6 then c ⟨p, h⟩ else if h' : p < 10 then d ⟨p - 6 + 2, by omega⟩ else c 0

/-- The assignment of two 6-cycles with `c 0 = d 0`, `c 1 = d 1`. -/
noncomputable def asg66e (c d : Fin 6 → V) (t : Fin 4) : Option (Fin 4) := by
  classical
  exact if h : ∃ j : Fin 4, d ⟨t.val + 2, by omega⟩ = c ⟨j.val + 2, by omega⟩ then some h.choose else none

/-- The assignment as a list. -/
noncomputable def asgL66e (c d : Fin 6 → V) : List (Option (Fin 4)) :=
  [asg66e c d 0, asg66e c d 1, asg66e c d 2, asg66e c d 3]

lemma asg66e_some {c d : Fin 6 → V} {t j : Fin 4} (h : asg66e c d t = some j) :
    d ⟨t.val + 2, by omega⟩ = c ⟨j.val + 2, by omega⟩ := by
  unfold asg66e at h
  split_ifs at h with hh
  · cases h; exact hh.choose_spec

lemma asg66e_none {c d : Fin 6 → V} {t : Fin 4} (h : asg66e c d t = none) (j : Fin 4) :
    d ⟨t.val + 2, by omega⟩ ≠ c ⟨j.val + 2, by omega⟩ := by
  unfold asg66e at h
  split_ifs at h with hh
  exact fun e => hh ⟨j, e⟩

lemma asgL66e_getD (c d : Fin 6 → V) (t : ℕ) (ht : t < 4) :
    (asgL66e c d).getD t none = asg66e c d ⟨t, ht⟩ := by
  interval_cases t <;> rfl

lemma asgL66e_valid {c d : Fin 6 → V} (hd : Function.Injective d) : validB66e (asgL66e c d) = true := by
  have key : ∀ t t' : Fin 4, ∀ j : Fin 4, j ∈ asg66e c d t → j ∈ asg66e c d t' → t = t' := by
    intro t t' j h h'
    have e := (asg66e_some h).trans (asg66e_some h').symm
    have := congrArg Fin.val (hd e)
    exact Fin.ext (by simpa using this)
  have hl : asgL66e c d = (List.finRange 4).map (asg66e c d) := by
    simp [asgL66e, List.finRange_succ]
  unfold validB66e
  rw [decide_eq_true_iff, hl, List.filterMap_map]
  exact (List.nodup_finRange 4).filterMap fun a a' b hb hb' => key a a' b hb hb'

section Sound

variable {c d : Fin 6 → V}

lemma phi66e_posOf (h0 : c 0 = d 0) (h1 : c 1 = d 1) (k : ℕ) (hk : k < 6) :
    phi66e c d (posOf66e (asgL66e c d) k) = d ⟨k, hk⟩ := by
  unfold posOf66e
  split_ifs with hk2
  · have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simp [phi66e, h0]
    · simp [phi66e, h1]
  · rw [asgL66e_getD c d (k - 2) (by omega)]
    rcases ha : asg66e c d ⟨k - 2, by omega⟩ with _ | j
    · simp only [phi66e]
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 1
      ext; simp; omega
    · simp only [phi66e]
      rw [dite_eq_left (by omega)]
      have := asg66e_some ha
      simp only at this
      rw [← this]
      congr 1
      ext; simp; omega

omit [DecidableEq V] in
lemma phi66e_c (p : ℕ) (hp : p < 6) : phi66e c d p = c ⟨p, hp⟩ := by simp [phi66e, hp]

omit [DecidableEq V] in
lemma cEdge_adj_e (hc : IsCycleMap G c) {p q : ℕ} (h : cEdgeB p q = true) :
    G.Adj (phi66e c d p) (phi66e c d q) := by
  unfold cEdgeB at h
  rw [decide_eq_true_iff] at h
  obtain ⟨hp, hq, hpq⟩ := h
  have hrot : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
  rw [phi66e_c p hp, phi66e_c q hq]
  rcases hpq with e | e
  · have := hc.2.2 ⟨p, hp⟩
    convert this using 2
    ext; rw [hrot]; simp [e]
  · have := hc.2.2 ⟨q, hq⟩
    refine SimpleGraph.Adj.symm ?_
    convert this using 2
    ext; rw [hrot]; simp [e]

lemma uEdge66e_adj (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1) {p q : ℕ}
    (h : uEdgeB66e (asgL66e c d) p q = true) : G.Adj (phi66e c d p) (phi66e c d q) := by
  unfold uEdgeB66e at h
  rw [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨k, hk, hpq⟩
  · exact cEdge_adj_e hc h
  · rw [List.mem_range] at hk
    rw [decide_eq_true_iff] at hpq
    have hrot6 : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
    have hcyc := hd.2.2 ⟨k, hk⟩
    have e1 := phi66e_posOf h0 h1 k hk
    have e2 := phi66e_posOf h0 h1 ((k + 1) % 6) (Nat.mod_lt _ (by norm_num))
    have e3 : finRotate 6 ⟨k, hk⟩ = ⟨(k + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext (hrot6 _)
    rw [e3] at hcyc
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e1, e2]; exact hcyc
    · rw [e1, e2]; exact hcyc.symm

lemma phi66e_inj (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1) {p q : ℕ}
    (hp : usedB66e (asgL66e c d) p = true) (hq : usedB66e (asgL66e c d) q = true)
    (h : phi66e c d p = phi66e c d q) : p = q := by
  have used : ∀ r, usedB66e (asgL66e c d) r = true →
      r < 6 ∨ ∃ h : 6 ≤ r ∧ r < 10, asg66e c d ⟨r - 6, by omega⟩ = none := by
    intro r hr
    unfold usedB66e at hr
    rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, Option.isNone_iff_eq_none] at hr
    rcases hr with hr | ⟨hr1, hr2⟩
    · exact Or.inl hr
    · refine Or.inr ⟨hr1, ?_⟩
      rwa [asgL66e_getD c d (r - 6) (by omega)] at hr2
  -- `d` at a new label is not on the first cycle
  have cross : ∀ (r s : ℕ) (hr : r < 6) (hs1 : 6 ≤ s) (hs2 : s < 10), asg66e c d ⟨s - 6, by omega⟩ = none →
      c ⟨r, hr⟩ ≠ d ⟨s - 6 + 2, by omega⟩ := by
    intro r s hr hs1 hs2 hnone e
    by_cases hr0 : r = 0
    · subst hr0
      have : d ⟨s - 6 + 2, by omega⟩ = d 0 := by rw [← e]; exact h0
      have := congrArg Fin.val (hd.2.1 this)
      simp at this
    · by_cases hr1 : r = 1
      · subst hr1
        have : d ⟨s - 6 + 2, by omega⟩ = d 1 := by rw [← e]; exact h1
        have := congrArg Fin.val (hd.2.1 this)
        simp at this
      · exact asg66e_none hnone ⟨r - 2, by omega⟩ (by rw [← e]; congr 1; ext; simp; omega)
  rcases used p hp with hp6 | ⟨⟨hp1, hp2⟩, hpn⟩ <;> rcases used q hq with hq6 | ⟨⟨hq1, hq2⟩, hqn⟩
  · simp only [phi66e, dite_eq_left hp6, dite_eq_left hq6] at h
    have := congrArg Fin.val (hc.2.1 h); simpa using this
  · simp only [phi66e, dite_eq_left hp6, dite_eq_right (by omega : ¬ q < 6), dite_eq_left hq2] at h
    exact absurd h (cross p q hp6 hq1 hq2 hqn)
  · simp only [phi66e, dite_eq_left hq6, dite_eq_right (by omega : ¬ p < 6), dite_eq_left hp2] at h
    exact absurd h.symm (cross q p hq6 hp1 hp2 hpn)
  · simp only [phi66e, dite_eq_right (by omega : ¬ p < 6), dite_eq_left hp2, dite_eq_right (by omega : ¬ q < 6),
      dite_eq_left hq2] at h
    have := congrArg Fin.val (hd.2.1 h); simp at this; omega

/-- **Soundness of the embedding check.** -/
lemma copy_of_checkE66e (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1) {n m : ℕ}
    (E : Fin m → Fin n × Fin n) (ψ : List ℕ) (h : checkE66e (asgL66e c d) n E ψ = true) : ofListing E ⊑ G := by
  unfold checkE66e at h
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hnd⟩, hused⟩, hedge⟩ := h
  have hget : ∀ u : Fin n, ψ.getD u.val 0 ∈ ψ := fun u => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  refine ⟨⟨⟨fun u => phi66e c d (ψ.getD u.val 0), fun {u v} huv => ?_⟩, fun u v huv => ?_⟩⟩
  · rw [ofListing, fromEdgeSet_adj] at huv
    obtain ⟨⟨e, he⟩, -⟩ := huv
    have hadj := uEdge66e_adj hc hd h0 h1 (hedge e (List.mem_finRange e))
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  · have := phi66e_inj hc hd h0 h1 (hused _ (hget u)) (hused _ (hget v)) huv
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 this)

/-- **The equal case.** -/
lemma eq_of_eqB66e (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1)
    (h : eqB66e (asgL66e c d) = true) : cycleEdges c = cycleEdges d := by
  have hsub : cycleEdges d ⊆ cycleEdges c := by
    intro x hx
    simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨k, rfl⟩ := hx
    unfold eqB66e at h
    rw [List.all_eq_true] at h
    have hk := h k.val (List.mem_range.2 k.isLt)
    have hrot6 : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
    have e1 := phi66e_posOf h0 h1 k.val k.isLt
    have e2 := phi66e_posOf h0 h1 ((k.val + 1) % 6) (Nat.mod_lt _ (by norm_num))
    have e3 : finRotate 6 k = ⟨(k.val + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext (hrot6 _)
    unfold cEdgeB at hk
    rw [decide_eq_true_iff] at hk
    obtain ⟨hp, hq, hpq⟩ := hk
    rw [e3, ← e2, ← show phi66e c d (posOf66e (asgL66e c d) k.val) = d k from e1,
      phi66e_c _ hp, phi66e_c _ hq]
    rcases hpq with e | e
    · refine ⟨⟨_, hp⟩, ?_⟩
      congr 2
      ext; rw [hrot6]; simp [e]
    · refine ⟨⟨_, hq⟩, ?_⟩
      rw [Sym2.eq_swap]
      congr 2
      ext; rw [hrot6]; simp [e]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [card_cycleEdges6 hc, card_cycleEdges6 hd])).symm

end Sound

end Thrackle78.Proof
