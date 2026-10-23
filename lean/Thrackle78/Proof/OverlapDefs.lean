import Thrackle78.Proof.Basic

/-!
# The overlap enumeration: classes, the certificate check, and its soundness

An 8-cycle `d₀ … d₇` and a 6-cycle `w₀ … w₅` with `w₀ = d₀`, `w₁ = d₁`: for `t < 4`, `w_{t+2}` is `d_{j+2}`
(`xs[t] = some j`) or a new vertex (`xs[t] = none`, label `8 + t`). The union `U(xs)` has the labels `0 … 11`. A
certificate `(k, ψ)` maps the vertices of class `k` (a triangle, `C4`, one of the 13 computed graphs, or one of the
four unions containing two 6-cycles through a common vertex) injectively into the used labels, edges to edges of `U`.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

/-! ## The classes -/

/-- The four unions with two 6-cycles through a common vertex (`graphs/u2c6_k.txt`). -/
def lu2c6_0 : List (ℕ × ℕ) :=
  [(0, 1), (0, 7), (0, 10), (1, 2), (1, 8), (2, 3), (3, 4), (4, 5), (4, 9), (4, 10), (5, 6), (6, 7), (8, 9)]
def lu2c6_1 : List (ℕ × ℕ) :=
  [(0, 1), (0, 7), (0, 9), (1, 2), (1, 8), (2, 3), (3, 4), (4, 5), (4, 9), (5, 6), (5, 8), (6, 7)]
def lu2c6_2 : List (ℕ × ℕ) := [(0, 1), (0, 7), (1, 2), (1, 8), (2, 3), (3, 4), (4, 5), (5, 6), (5, 8), (6, 7)]
def lu2c6_3 : List (ℕ × ℕ) := [(0, 1), (0, 4), (0, 7), (1, 2), (2, 3), (2, 6), (3, 4), (4, 5), (5, 6), (6, 7)]

/-! ## The union and the check -/

/-- The label of `w_k` in the union. -/
def posOf (xs : List (Option (Fin 6))) (k : ℕ) : ℕ :=
  if k < 2 then k else
    match xs.getD (k - 2) none with
    | some j => j.val + 2
    | none => 8 + (k - 2)

/-- The label `p` is a vertex of the union. -/
def usedB (xs : List (Option (Fin 6))) (p : ℕ) : Bool :=
  decide (p < 8) || (decide (8 ≤ p ∧ p < 12) && (xs.getD (p - 8) none).isNone)

/-- `pq` is an edge of the union: an edge of the 8-cycle or of the 6-cycle. -/
def uEdgeB (xs : List (Option (Fin 6))) (p q : ℕ) : Bool :=
  decide (p < 8 ∧ q < 8 ∧ (q = (p + 1) % 8 ∨ p = (q + 1) % 8)) ||
    (List.range 6).any fun k => decide ((p = posOf xs k ∧ q = posOf xs ((k + 1) % 6)) ∨
      (q = posOf xs k ∧ p = posOf xs ((k + 1) % 6)))

/-- The certificate `ψ` embeds the graph of the listing `E` into the union. -/
def checkE (xs : List (Option (Fin 6))) (n : ℕ) {m : ℕ} (E : Fin m → Fin n × Fin n) (ψ : List ℕ) : Bool :=
  decide (ψ.length = n) && decide ψ.Nodup && ψ.all (usedB xs) &&
    (List.finRange m).all fun e => uEdgeB xs (ψ.getD (E e).1 0) (ψ.getD (E e).2 0)

/-- The check of a certificate `(k, ψ)`. -/
def checkCert (xs : List (Option (Fin 6))) (cert : ℕ × List ℕ) : Bool :=
  match cert.1 with
  | 0 => checkE xs 3 (mkE 3 lK3) cert.2
  | 1 => checkE xs 4 (mkE 4 lC4) cert.2
  | 2 => checkE xs 12 (mkE 12 lDB681) cert.2
  | 3 => checkE xs 11 (mkE 11 lDB682) cert.2
  | 4 => checkE xs 10 (mkE 10 lDB683) cert.2
  | 5 => checkE xs 11 (mkE 11 lU7) cert.2
  | 6 => checkE xs 11 (mkE 11 lU8) cert.2
  | 7 => checkE xs 10 (mkE 10 lU9) cert.2
  | 8 => checkE xs 10 (mkE 10 lU10) cert.2
  | 9 => checkE xs 11 (mkE 11 lU11) cert.2
  | 10 => checkE xs 10 (mkE 10 lU12) cert.2
  | 11 => checkE xs 10 (mkE 10 lU13) cert.2
  | 12 => checkE xs 10 (mkE 10 lU14) cert.2
  | 13 => checkE xs 9 (mkE 9 lU15) cert.2
  | 14 => checkE xs 10 (mkE 10 lU16) cert.2
  | 15 => checkE xs 11 (mkE 11 lu2c6_0) cert.2
  | 16 => checkE xs 10 (mkE 10 lu2c6_1) cert.2
  | 17 => checkE xs 9 (mkE 9 lu2c6_2) cert.2
  | 18 => checkE xs 8 (mkE 8 lu2c6_3) cert.2
  | _ => false

/-- The assignment is consistent (distinct targets on the 8-cycle). -/
def validB (xs : List (Option (Fin 6))) : Bool := decide (xs.filterMap id).Nodup

/-! ## Soundness -/

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- The labels of the union in `G`. -/
def phi (c : Fin 6 → V) (d : Fin 8 → V) (p : ℕ) : V :=
  if h : p < 8 then d ⟨p, h⟩ else if h' : p < 12 then c ⟨p - 8 + 2, by omega⟩ else d 0

/-- The assignment of a pair of cycles with `c 0 = d 0`, `c 1 = d 1`. -/
noncomputable def asg (c : Fin 6 → V) (d : Fin 8 → V) (t : Fin 4) : Option (Fin 6) := by
  classical
  exact if h : ∃ j : Fin 6, c ⟨t.val + 2, by omega⟩ = d ⟨j.val + 2, by omega⟩ then some h.choose else none

/-- The assignment as a list. -/
noncomputable def asgL (c : Fin 6 → V) (d : Fin 8 → V) : List (Option (Fin 6)) :=
  [asg c d 0, asg c d 1, asg c d 2, asg c d 3]

lemma asg_some {c : Fin 6 → V} {d : Fin 8 → V} {t : Fin 4} {j : Fin 6} (h : asg c d t = some j) :
    c ⟨t.val + 2, by omega⟩ = d ⟨j.val + 2, by omega⟩ := by
  unfold asg at h
  split_ifs at h with hh
  · cases h; exact hh.choose_spec

lemma asg_none {c : Fin 6 → V} {d : Fin 8 → V} {t : Fin 4} (h : asg c d t = none) (j : Fin 6) :
    c ⟨t.val + 2, by omega⟩ ≠ d ⟨j.val + 2, by omega⟩ := by
  unfold asg at h
  split_ifs at h with hh
  exact fun e => hh ⟨j, e⟩

lemma asgL_getD (c : Fin 6 → V) (d : Fin 8 → V) (t : ℕ) (ht : t < 4) :
    (asgL c d).getD t none = asg c d ⟨t, ht⟩ := by
  interval_cases t <;> rfl

lemma asgL_valid {c : Fin 6 → V} {d : Fin 8 → V} (hc : Function.Injective c) : validB (asgL c d) = true := by
  have key : ∀ t t' : Fin 4, ∀ j : Fin 6, j ∈ asg c d t → j ∈ asg c d t' → t = t' := by
    intro t t' j h h'
    have e := (asg_some h).trans (asg_some h').symm
    have := congrArg Fin.val (hc e)
    exact Fin.ext (by simpa using this)
  have hl : asgL c d = (List.finRange 4).map (asg c d) := by
    simp [asgL, List.finRange_succ]
  unfold validB
  rw [decide_eq_true_iff, hl, List.filterMap_map]
  exact (List.nodup_finRange 4).filterMap fun a a' b hb hb' => key a a' b hb hb'

section Sound

variable {c : Fin 6 → V} {d : Fin 8 → V}

/-- `phi` sends the label of `w_k` to `c k`. -/
lemma phi_posOf (h0 : c 0 = d 0) (h1 : c 1 = d 1) (k : ℕ) (hk : k < 6) :
    phi c d (posOf (asgL c d) k) = c ⟨k, hk⟩ := by
  unfold posOf
  split_ifs with h2
  · interval_cases k
    · simp [phi, h0]
    · simp [phi, h1]
  · rw [asgL_getD c d (k - 2) (by omega)]
    rcases ha : asg c d ⟨k - 2, by omega⟩ with _ | j
    · simp only [phi]
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 1
      ext; simp; omega
    · simp only [phi]
      rw [dite_eq_left (by omega)]
      have := asg_some ha
      simp only at this
      rw [← this]
      congr 1
      ext; simp; omega

/-- Edges of the union go to edges of `G`. -/
lemma uEdge_adj (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1) {p q : ℕ}
    (h : uEdgeB (asgL c d) p q = true) : G.Adj (phi c d p) (phi c d q) := by
  unfold uEdgeB at h
  rw [Bool.or_eq_true, decide_eq_true_iff, List.any_eq_true] at h
  rcases h with ⟨hp, hq, hpq⟩ | ⟨k, hk, hpq⟩
  · have hrot : ∀ a : Fin 8, (finRotate 8 a).val = (a.val + 1) % 8 := by decide
    simp only [phi, dite_eq_left hp, dite_eq_left hq]
    rcases hpq with e | e
    · have := hd.2.2 ⟨p, hp⟩
      convert this using 2
      ext; rw [hrot]; simp [e]
    · have := hd.2.2 ⟨q, hq⟩
      refine SimpleGraph.Adj.symm ?_
      convert this using 2
      ext; rw [hrot]; simp [e]
  · rw [List.mem_range] at hk
    rw [decide_eq_true_iff] at hpq
    have hrot6 : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
    have hcyc := hc.2.2 ⟨k, hk⟩
    have e1 := phi_posOf h0 h1 k hk
    have e2 := phi_posOf h0 h1 ((k + 1) % 6) (Nat.mod_lt _ (by norm_num))
    have e3 : finRotate 6 ⟨k, hk⟩ = ⟨(k + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext (hrot6 _)
    rw [e3] at hcyc
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e1, e2]; exact hcyc
    · rw [e1, e2]; exact hcyc.symm

/-- `phi` is injective on the labels of the union. -/
lemma phi_inj (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1) {p q : ℕ}
    (hp : usedB (asgL c d) p = true) (hq : usedB (asgL c d) q = true) (h : phi c d p = phi c d q) : p = q := by
  have used : ∀ r, usedB (asgL c d) r = true →
      r < 8 ∨ ∃ h : 8 ≤ r ∧ r < 12, asg c d ⟨r - 8, by omega⟩ = none := by
    intro r hr
    unfold usedB at hr
    rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, Option.isNone_iff_eq_none] at hr
    rcases hr with hr | ⟨hr1, hr2⟩
    · exact Or.inl hr
    · refine Or.inr ⟨hr1, ?_⟩
      rwa [asgL_getD c d (r - 8) (by omega)] at hr2
  -- `c` at a new label is not on the 8-cycle
  have cross : ∀ (r s : ℕ) (hr : r < 8) (hs1 : 8 ≤ s) (hs2 : s < 12), asg c d ⟨s - 8, by omega⟩ = none →
      d ⟨r, hr⟩ ≠ c ⟨s - 8 + 2, by omega⟩ := by
    intro r s hr hs1 hs2 hnone e
    by_cases hr2 : r < 2
    · have : c ⟨s - 8 + 2, by omega⟩ = c ⟨r, by omega⟩ := by
        interval_cases r
        · rw [← e]; exact h0.symm
        · rw [← e]; exact h1.symm
      have := congrArg Fin.val (hc.2.1 this)
      simp at this; omega
    · exact asg_none hnone ⟨r - 2, by omega⟩ (by rw [← e]; congr 1; ext; simp; omega)
  rcases used p hp with hp8 | ⟨⟨hp1, hp2⟩, hpn⟩ <;> rcases used q hq with hq8 | ⟨⟨hq1, hq2⟩, hqn⟩
  · simp only [phi, dite_eq_left hp8, dite_eq_left hq8] at h
    have := congrArg Fin.val (hd.2.1 h); simpa using this
  · simp only [phi, dite_eq_left hp8, dite_eq_right (by omega : ¬ q < 8), dite_eq_left hq2] at h
    exact absurd h (cross p q hp8 hq1 hq2 hqn)
  · simp only [phi, dite_eq_left hq8, dite_eq_right (by omega : ¬ p < 8), dite_eq_left hp2] at h
    exact absurd h.symm (cross q p hq8 hp1 hp2 hpn)
  · simp only [phi, dite_eq_right (by omega : ¬ p < 8), dite_eq_left hp2, dite_eq_right (by omega : ¬ q < 8), dite_eq_left hq2] at h
    have := congrArg Fin.val (hc.2.1 h); simp at this; omega

/-- **Soundness of the check.** -/
lemma copy_of_checkE (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) (h1 : c 1 = d 1) {n m : ℕ}
    (E : Fin m → Fin n × Fin n) (ψ : List ℕ) (h : checkE (asgL c d) n E ψ = true) : ofListing E ⊑ G := by
  unfold checkE at h
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hnd⟩, hused⟩, hedge⟩ := h
  have hget : ∀ u : Fin n, ψ.getD u.val 0 ∈ ψ := fun u => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  refine ⟨⟨⟨fun u => phi c d (ψ.getD u.val 0), fun {u v} huv => ?_⟩, fun u v huv => ?_⟩⟩
  · rw [ofListing, fromEdgeSet_adj] at huv
    obtain ⟨⟨e, he⟩, -⟩ := huv
    have hadj := uEdge_adj hc hd h0 h1 (hedge e (List.mem_finRange e))
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  · have := phi_inj hc hd h0 h1 (hused _ (hget u)) (hused _ (hget v)) huv
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 this)

end Sound

end Thrackle78.Proof
