import Thrackle78.Proof.Basic

/-!
# The 6-6 overlap enumeration: the certificate check and its soundness

Two 6-cycles `c = v₀ … v₅` and `d = w₀ … w₅` with `w₀ = v₀`: for `t < 5`, `w_{t+1}` is `v_{j+1}` (`xs[t] = some j`)
or a new vertex (`xs[t] = none`, label `6 + t`). A certificate is `(99, [])` when `d` has the same edges as `c`, or
`(k, ψ)` embedding class `k` (a triangle, `C4`, `DB(6,6,0)`, …, `DB(6,6,-3)`, or one of three further unions) into the
union `U(xs)` on the labels `0 … 10`.
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

/-! ## The union and the check -/

/-- The label of `w_k` in the union. -/
def posOf66 (xs : List (Option (Fin 5))) (k : ℕ) : ℕ :=
  if k = 0 then 0 else
    match xs.getD (k - 1) none with
    | some j => j.val + 1
    | none => 6 + (k - 1)

/-- The label `p` is a vertex of the union. -/
def usedB66 (xs : List (Option (Fin 5))) (p : ℕ) : Bool :=
  decide (p < 6) || (decide (6 ≤ p ∧ p < 11) && (xs.getD (p - 6) none).isNone)

/-- `pq` is an edge of the first 6-cycle. -/
def cEdgeB (p q : ℕ) : Bool := decide (p < 6 ∧ q < 6 ∧ (q = (p + 1) % 6 ∨ p = (q + 1) % 6))

/-- `pq` is an edge of the union. -/
def uEdgeB66 (xs : List (Option (Fin 5))) (p q : ℕ) : Bool :=
  cEdgeB p q ||
    (List.range 6).any fun k => decide ((p = posOf66 xs k ∧ q = posOf66 xs ((k + 1) % 6)) ∨
      (q = posOf66 xs k ∧ p = posOf66 xs ((k + 1) % 6)))

/-- The second 6-cycle uses only edges of the first. -/
def eqB66 (xs : List (Option (Fin 5))) : Bool :=
  (List.range 6).all fun k => cEdgeB (posOf66 xs k) (posOf66 xs ((k + 1) % 6))

/-- The certificate `ψ` embeds the graph of the listing `E` into the union. -/
def checkE66 (xs : List (Option (Fin 5))) (n : ℕ) {m : ℕ} (E : Fin m → Fin n × Fin n) (ψ : List ℕ) : Bool :=
  decide (ψ.length = n) && decide ψ.Nodup && ψ.all (usedB66 xs) &&
    (List.finRange m).all fun e => uEdgeB66 xs (ψ.getD (E e).1 0) (ψ.getD (E e).2 0)

/-- The check of a certificate. -/
def checkCert66 (xs : List (Option (Fin 5))) (cert : ℕ × List ℕ) : Bool :=
  match cert.1 with
  | 0 => checkE66 xs 3 (mkE 3 lK3) cert.2
  | 1 => checkE66 xs 4 (mkE 4 lC4) cert.2
  | 2 => checkE66 xs 11 (mkE 11 lDB660) cert.2
  | 3 => checkE66 xs 10 (mkE 10 lDB661) cert.2
  | 4 => checkE66 xs 9 (mkE 9 lDB662) cert.2
  | 5 => checkE66 xs 8 (mkE 8 lDB663) cert.2
  | 6 => checkE66 xs 8 (mkE 8 lV4) cert.2
  | 7 => checkE66 xs 9 (mkE 9 lV5) cert.2
  | 8 => checkE66 xs 10 (mkE 10 lV7) cert.2
  | 99 => eqB66 xs
  | _ => false

/-- The assignment is consistent. -/
def validB66 (xs : List (Option (Fin 5))) : Bool := decide (xs.filterMap id).Nodup

/-! ## Soundness -/

variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

/-- The labels of the union in `G`. -/
def phi66 (c d : Fin 6 → V) (p : ℕ) : V :=
  if h : p < 6 then c ⟨p, h⟩ else if h' : p < 11 then d ⟨p - 6 + 1, by omega⟩ else c 0

/-- The assignment of two 6-cycles with `c 0 = d 0`. -/
noncomputable def asg66 (c d : Fin 6 → V) (t : Fin 5) : Option (Fin 5) := by
  classical
  exact if h : ∃ j : Fin 5, d ⟨t.val + 1, by omega⟩ = c ⟨j.val + 1, by omega⟩ then some h.choose else none

/-- The assignment as a list. -/
noncomputable def asgL66 (c d : Fin 6 → V) : List (Option (Fin 5)) :=
  [asg66 c d 0, asg66 c d 1, asg66 c d 2, asg66 c d 3, asg66 c d 4]

lemma asg66_some {c d : Fin 6 → V} {t j : Fin 5} (h : asg66 c d t = some j) :
    d ⟨t.val + 1, by omega⟩ = c ⟨j.val + 1, by omega⟩ := by
  unfold asg66 at h
  split_ifs at h with hh
  · cases h; exact hh.choose_spec

lemma asg66_none {c d : Fin 6 → V} {t : Fin 5} (h : asg66 c d t = none) (j : Fin 5) :
    d ⟨t.val + 1, by omega⟩ ≠ c ⟨j.val + 1, by omega⟩ := by
  unfold asg66 at h
  split_ifs at h with hh
  exact fun e => hh ⟨j, e⟩

lemma asgL66_getD (c d : Fin 6 → V) (t : ℕ) (ht : t < 5) : (asgL66 c d).getD t none = asg66 c d ⟨t, ht⟩ := by
  interval_cases t <;> rfl

lemma asgL66_valid {c d : Fin 6 → V} (hd : Function.Injective d) : validB66 (asgL66 c d) = true := by
  have key : ∀ t t' : Fin 5, ∀ j : Fin 5, j ∈ asg66 c d t → j ∈ asg66 c d t' → t = t' := by
    intro t t' j h h'
    have e := (asg66_some h).trans (asg66_some h').symm
    have := congrArg Fin.val (hd e)
    exact Fin.ext (by simpa using this)
  have hl : asgL66 c d = (List.finRange 5).map (asg66 c d) := by
    simp [asgL66, List.finRange_succ]
  unfold validB66
  rw [decide_eq_true_iff, hl, List.filterMap_map]
  exact (List.nodup_finRange 5).filterMap fun a a' b hb hb' => key a a' b hb hb'

section Sound

variable {c d : Fin 6 → V}

lemma phi66_posOf (h0 : c 0 = d 0) (k : ℕ) (hk : k < 6) : phi66 c d (posOf66 (asgL66 c d) k) = d ⟨k, hk⟩ := by
  unfold posOf66
  split_ifs with hk0
  · subst hk0; simp [phi66, h0]
  · rw [asgL66_getD c d (k - 1) (by omega)]
    rcases ha : asg66 c d ⟨k - 1, by omega⟩ with _ | j
    · simp only [phi66]
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 1
      ext; simp; omega
    · simp only [phi66]
      rw [dite_eq_left (by omega)]
      have := asg66_some ha
      simp only at this
      rw [← this]
      congr 1
      ext; simp; omega

omit [DecidableEq V] in
lemma phi66_c (p : ℕ) (hp : p < 6) : phi66 c d p = c ⟨p, hp⟩ := by simp [phi66, hp]

omit [DecidableEq V] in
lemma cEdge_adj (hc : IsCycleMap G c) {p q : ℕ} (h : cEdgeB p q = true) :
    G.Adj (phi66 c d p) (phi66 c d q) := by
  unfold cEdgeB at h
  rw [decide_eq_true_iff] at h
  obtain ⟨hp, hq, hpq⟩ := h
  have hrot : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
  rw [phi66_c p hp, phi66_c q hq]
  rcases hpq with e | e
  · have := hc.2.2 ⟨p, hp⟩
    convert this using 2
    ext; rw [hrot]; simp [e]
  · have := hc.2.2 ⟨q, hq⟩
    refine SimpleGraph.Adj.symm ?_
    convert this using 2
    ext; rw [hrot]; simp [e]

lemma uEdge66_adj (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) {p q : ℕ}
    (h : uEdgeB66 (asgL66 c d) p q = true) : G.Adj (phi66 c d p) (phi66 c d q) := by
  unfold uEdgeB66 at h
  rw [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨k, hk, hpq⟩
  · exact cEdge_adj hc h
  · rw [List.mem_range] at hk
    rw [decide_eq_true_iff] at hpq
    have hrot6 : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
    have hcyc := hd.2.2 ⟨k, hk⟩
    have e1 := phi66_posOf h0 k hk
    have e2 := phi66_posOf h0 ((k + 1) % 6) (Nat.mod_lt _ (by norm_num))
    have e3 : finRotate 6 ⟨k, hk⟩ = ⟨(k + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext (hrot6 _)
    rw [e3] at hcyc
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e1, e2]; exact hcyc
    · rw [e1, e2]; exact hcyc.symm

lemma phi66_inj (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) {p q : ℕ}
    (hp : usedB66 (asgL66 c d) p = true) (hq : usedB66 (asgL66 c d) q = true) (h : phi66 c d p = phi66 c d q) :
    p = q := by
  have used : ∀ r, usedB66 (asgL66 c d) r = true →
      r < 6 ∨ ∃ h : 6 ≤ r ∧ r < 11, asg66 c d ⟨r - 6, by omega⟩ = none := by
    intro r hr
    unfold usedB66 at hr
    rw [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, Option.isNone_iff_eq_none] at hr
    rcases hr with hr | ⟨hr1, hr2⟩
    · exact Or.inl hr
    · refine Or.inr ⟨hr1, ?_⟩
      rwa [asgL66_getD c d (r - 6) (by omega)] at hr2
  -- `d` at a new label is not on the first cycle
  have cross : ∀ (r s : ℕ) (hr : r < 6) (hs1 : 6 ≤ s) (hs2 : s < 11), asg66 c d ⟨s - 6, by omega⟩ = none →
      c ⟨r, hr⟩ ≠ d ⟨s - 6 + 1, by omega⟩ := by
    intro r s hr hs1 hs2 hnone e
    by_cases hr0 : r = 0
    · subst hr0
      have : d ⟨s - 6 + 1, by omega⟩ = d 0 := by rw [← e]; exact h0
      have := congrArg Fin.val (hd.2.1 this)
      simp at this
    · exact asg66_none hnone ⟨r - 1, by omega⟩ (by rw [← e]; congr 1; ext; simp; omega)
  rcases used p hp with hp6 | ⟨⟨hp1, hp2⟩, hpn⟩ <;> rcases used q hq with hq6 | ⟨⟨hq1, hq2⟩, hqn⟩
  · simp only [phi66, dite_eq_left hp6, dite_eq_left hq6] at h
    have := congrArg Fin.val (hc.2.1 h); simpa using this
  · simp only [phi66, dite_eq_left hp6, dite_eq_right (by omega : ¬ q < 6), dite_eq_left hq2] at h
    exact absurd h (cross p q hp6 hq1 hq2 hqn)
  · simp only [phi66, dite_eq_left hq6, dite_eq_right (by omega : ¬ p < 6), dite_eq_left hp2] at h
    exact absurd h.symm (cross q p hq6 hp1 hp2 hpn)
  · simp only [phi66, dite_eq_right (by omega : ¬ p < 6), dite_eq_left hp2, dite_eq_right (by omega : ¬ q < 6),
      dite_eq_left hq2] at h
    have := congrArg Fin.val (hd.2.1 h); simp at this; omega

/-- **Soundness of the embedding check.** -/
lemma copy_of_checkE66 (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0) {n m : ℕ}
    (E : Fin m → Fin n × Fin n) (ψ : List ℕ) (h : checkE66 (asgL66 c d) n E ψ = true) : ofListing E ⊑ G := by
  unfold checkE66 at h
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hnd⟩, hused⟩, hedge⟩ := h
  have hget : ∀ u : Fin n, ψ.getD u.val 0 ∈ ψ := fun u => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  refine ⟨⟨⟨fun u => phi66 c d (ψ.getD u.val 0), fun {u v} huv => ?_⟩, fun u v huv => ?_⟩⟩
  · rw [ofListing, fromEdgeSet_adj] at huv
    obtain ⟨⟨e, he⟩, -⟩ := huv
    have hadj := uEdge66_adj hc hd h0 (hedge e (List.mem_finRange e))
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  · have := phi66_inj hc hd h0 (hused _ (hget u)) (hused _ (hget v)) huv
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 this)

/-- A 6-cycle map has six distinct edges. -/
lemma card_cycleEdges6 (hc : IsCycleMap G c) : (cycleEdges c).card = 6 := by
  unfold cycleEdges
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j h
  simp only at h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hc.2.1 h1
  · have e1 := hc.2.1 h1
    have e2 := hc.2.1 h2
    exact absurd (by rw [← e1, e2] : finRotate 6 (finRotate 6 j) = j) (finRotate_twice_ne (by norm_num) j)

/-- **The equal case.** -/
lemma eq_of_eqB66 (hc : IsCycleMap G c) (hd : IsCycleMap G d) (h0 : c 0 = d 0)
    (h : eqB66 (asgL66 c d) = true) : cycleEdges c = cycleEdges d := by
  have hsub : cycleEdges d ⊆ cycleEdges c := by
    intro x hx
    simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨k, rfl⟩ := hx
    unfold eqB66 at h
    rw [List.all_eq_true] at h
    have hk := h k.val (List.mem_range.2 k.isLt)
    have hrot6 : ∀ a : Fin 6, (finRotate 6 a).val = (a.val + 1) % 6 := by decide
    have e1 := phi66_posOf h0 k.val k.isLt
    have e2 := phi66_posOf h0 ((k.val + 1) % 6) (Nat.mod_lt _ (by norm_num))
    have e3 : finRotate 6 k = ⟨(k.val + 1) % 6, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext (hrot6 _)
    unfold cEdgeB at hk
    rw [decide_eq_true_iff] at hk
    obtain ⟨hp, hq, hpq⟩ := hk
    rw [e3, ← e2, ← show phi66 c d (posOf66 (asgL66 c d) k.val) = d k from e1,
      phi66_c _ hp, phi66_c _ hq]
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
