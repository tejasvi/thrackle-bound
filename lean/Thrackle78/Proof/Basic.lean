import Thrackle78.Hyp

/-!
# Basic lemmas shared by the overlap enumerations and the face arguments
-/

namespace Thrackle78.Proof

open SimpleGraph Thrackle78

lemma finRotate_val {m : ℕ} (j : Fin (m + 1)) :
    (finRotate (m + 1) j).val = if j.val < m then j.val + 1 else 0 := by
  obtain ⟨k, hk⟩ := j
  split_ifs with h
  · rw [finRotate_of_lt h]
  · have : k = m := by simp only at h; omega
    subst this
    rw [finRotate_last']

/-- `finRotate` applied twice is not the identity on `Fin n`, `n ≥ 3`. -/
lemma finRotate_twice_ne {n : ℕ} (hn : 3 ≤ n) (j : Fin n) : finRotate n (finRotate n j) ≠ j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  have hv := congrArg Fin.val h
  rw [finRotate_val, finRotate_val] at hv
  have := j.isLt
  split_ifs at hv <;> omega


/-- A triangle and a 4-cycle as listings. -/
def lK3 : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0)]
def lC4 : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 0)]
instance ofListing_decRel {n m : ℕ} (E : Fin m → Fin n × Fin n) : DecidableRel (ofListing E).Adj := fun u v =>
  decidable_of_iff ((∃ e, s(u, v) = s((E e).1, (E e).2)) ∧ u ≠ v)
    (by rw [ofListing, fromEdgeSet_adj, Set.mem_ofPred_eq])

lemma isEdgeListing_ofListing {n m : ℕ} (E : Fin m → Fin n × Fin n) (hloop : ∀ e, (E e).1 ≠ (E e).2)
    (hinj : ∀ e f, s((E e).1, (E e).2) = s((E f).1, (E f).2) → e = f) : IsEdgeListing (ofListing E) E := by
  refine ⟨fun e => ?_, hinj, fun u v huv => ?_⟩
  · rw [ofListing, fromEdgeSet_adj]
    exact ⟨⟨e, rfl⟩, hloop e⟩
  · rw [ofListing, fromEdgeSet_adj] at huv
    obtain ⟨⟨e, he⟩, -⟩ := huv
    exact ⟨e, he.symm⟩


variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

/-! ## The excluded graphs -/

omit [Fintype V] in
lemma not_K3 (htri : G.CliqueFree 3) (h : ofListing (mkE 3 lK3) ⊑ G) : False := by
  obtain ⟨f⟩ := h
  have a01 : (ofListing (mkE 3 lK3)).Adj 0 1 := by decide
  have a02 : (ofListing (mkE 3 lK3)).Adj 0 2 := by decide
  have a12 : (ofListing (mkE 3 lK3)).Adj 1 2 := by decide
  apply htri {f 0, f 1, f 2}
  rw [is3Clique_triple_iff]
  exact ⟨f.toHom.map_adj a01, f.toHom.map_adj a02, f.toHom.map_adj a12⟩

lemma not_C4 (ax : ThrackleAxioms Thr) (hT : Thr G) (h : ofListing (mkE 4 lC4) ⊑ G) : False := by
  have hc : cycleGraph 4 ⊑ ofListing (mkE 4 lC4) :=
    ⟨⟨⟨id, fun {u v} huv => by revert u v; decide⟩, Function.injective_id⟩⟩
  exact ax.c4 (ax.sub _ _ (hc.trans h) hT)

lemma not_listed (ax : ThrackleAxioms Thr) (hT : Thr G) {n m : ℕ} (E : Fin m → Fin n × Fin n) (hm : 0 < m)
    (hloop : ∀ e, (E e).1 ≠ (E e).2) (hinj : ∀ e f, s((E e).1, (E e).2) = s((E f).1, (E f).2) → e = f)
    (hE : ¬ CombThr E) (h : ofListing E ⊑ G) : False :=
  hE (ax.link _ E hm (isEdgeListing_ofListing E hloop hinj) (ax.sub _ _ h hT))

/-! ## Rotations and reflections of cycles -/

omit [Fintype V] [DecidableEq V] in
lemma cycle_rot {k : ℕ} [NeZero k] {c : Fin k → V} (hc : IsCycleMap G c) (i : Fin k) :
    IsCycleMap G (fun j => c (j + i)) := by
  refine ⟨hc.1, fun a b hab => add_right_cancel (hc.2.1 hab), fun j => ?_⟩
  have h := hc.2.2 (j + i)
  rw [finRotate_apply] at h
  show G.Adj (c (j + i)) (c (finRotate k j + i))
  rw [finRotate_apply, add_right_comm]
  exact h

omit [Fintype V] [DecidableEq V] in
lemma cycle_refl {k : ℕ} [NeZero k] {d : Fin k → V} (hd : IsCycleMap G d) (j : Fin k) :
    IsCycleMap G (fun i => d (j + 1 - i)) := by
  refine ⟨hd.1, fun a b hab => ?_, fun i => ?_⟩
  · have := hd.2.1 hab
    simpa using this
  · have h := hd.2.2 (j - i)
    rw [finRotate_apply, sub_add_eq_add_sub] at h
    show G.Adj (d (j + 1 - i)) (d (j + 1 - finRotate k i))
    rw [finRotate_apply, add_sub_add_right_eq_sub]
    exact h.symm

omit [Fintype V] in
/-- Rotating a cycle map does not change its edges. -/
lemma cycleEdges_rot {k : ℕ} [NeZero k] (c : Fin k → V) (i : Fin k) :
    cycleEdges (fun j => c (j + i)) = cycleEdges c := by
  ext x
  simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and, finRotate_apply]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j + i, by rw [add_right_comm]⟩
  · rintro ⟨j, rfl⟩
    refine ⟨j - i, ?_⟩
    rw [sub_add_cancel, add_right_comm, sub_add_cancel]

omit [Fintype V] in
/-- Reflecting a cycle map does not change its edges. -/
lemma cycleEdges_refl {k : ℕ} [NeZero k] (d : Fin k → V) (j : Fin k) :
    cycleEdges (fun i => d (j + 1 - i)) = cycleEdges d := by
  ext x
  simp only [cycleEdges, Finset.mem_image, Finset.mem_univ, true_and, finRotate_apply]
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨j - i, ?_⟩
    have e1 : j + 1 - i = j - i + 1 := by abel
    have e2 : j + 1 - (i + 1) = j - i := by abel
    rw [e1, e2]
    exact Sym2.eq_swap
  · rintro ⟨i, rfl⟩
    refine ⟨j - i, ?_⟩
    have e1 : j + 1 - (j - i) = i + 1 := by abel
    have e2 : j + 1 - (j - i + 1) = i := by abel
    rw [e1, e2]
    exact Sym2.eq_swap

/-- The facts of the `27/20` bound include those of the `15/11` bound. -/
theorem _root_.Thrackle78.CompFacts.to15 (h : CompFacts) : CompFacts15 :=
  ⟨h.db681, h.db682, h.db683, h.u7, h.u8, h.u9, h.u10, h.u11, h.u12, h.u13, h.u14, h.u15, h.u16, h.db661, h.db662,
    h.db663, h.v4, h.v5⟩

end Thrackle78.Proof
