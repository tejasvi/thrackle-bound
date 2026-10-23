import Thrackle78Core.StateEdge
import Thrackle78.Checker.Minor

/-!
# Soundness of the minor-model checker against an edge test

`eSG adj` is the graph of the edge test `adj` (read symmetrically, no loops); `not_planar_of_checkMinorE`: an accepted
certificate shows that it is not planar. Same proof as for `checkMinor`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

theorem hasE_symm (adj : ℕ → ℕ → Bool) {x y : ℕ} (h : hasE adj x y = true) : hasE adj y x = true := by
  unfold hasE at h ⊢
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at h ⊢
  exact ⟨fun e => h.1 e.symm, h.2.symm⟩

theorem hasE_irrefl (adj : ℕ → ℕ → Bool) (x : ℕ) : ¬ hasE adj x x = true := by
  unfold hasE; simp

/-- The graph of an edge test. -/
def eSG (adj : ℕ → ℕ → Bool) : SimpleGraph ℕ where
  Adj x y := hasE adj x y = true
  symm := ⟨fun _ _ h => hasE_symm adj h⟩
  loopless := ⟨fun x h => hasE_irrefl adj x h⟩

@[simp] theorem eSG_adj (adj : ℕ → ℕ → Bool) (x y : ℕ) : (eSG adj).Adj x y ↔ hasE adj x y = true := Iff.rfl

theorem connOKE_connected (adj : ℕ → ℕ → Bool) (B : Array (ℕ × ℕ)) (hpos : 0 < B.size)
    (hc : connOKE adj B = true) :
    ((eSG adj).induce {x | ∃ j < B.size, (B.getD j (0, 0)).1 = x}).Connected := by
  have hmem : ∀ j < B.size, (B.getD j (0, 0)).1 ∈ {x | ∃ j < B.size, (B.getD j (0, 0)).1 = x} :=
    fun j hj => ⟨j, hj, rfl⟩
  have step : ∀ j < B.size, j ≠ 0 → (B.getD j (0, 0)).2 < j ∧
      hasE adj (B.getD j (0, 0)).1 (B.getD (B.getD j (0, 0)).2 (0, 0)).1 = true := by
    intro j hj hj0
    unfold connOKE at hc
    rw [List.all_eq_true] at hc
    have := hc j (List.mem_range.2 hj)
    simpa [hj0] using this
  have reach : ∀ j (hj : j < B.size), ((eSG adj).induce {x | ∃ j < B.size, (B.getD j (0, 0)).1 = x}).Reachable
      ⟨(B.getD 0 (0, 0)).1, hmem 0 hpos⟩ ⟨(B.getD j (0, 0)).1, hmem j hj⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hj0 : j = 0
      · subst hj0; rfl
      · obtain ⟨hlt, hedge⟩ := step j hj hj0
        refine (ih _ hlt (lt_trans hlt hj)).trans (SimpleGraph.Adj.reachable ?_)
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, eSG_adj]
        exact hasE_symm adj hedge
  have : Nonempty {x | ∃ j < B.size, (B.getD j (0, 0)).1 = x} := ⟨⟨_, hmem 0 hpos⟩⟩
  refine Connected.mk fun p q => ?_
  obtain ⟨p, j, hj, rfl⟩ := p
  obtain ⟨q, k, hk, rfl⟩ := q
  exact (reach j hj).symm.trans (reach k hk)

variable {nv : ℕ} {adj : ℕ → ℕ → Bool} {c : MinorCert}

theorem checkMinorE_parts (h : checkMinorE nv adj c = true) :
    c.branch.size = numBranch c.k5 ∧ c.wit.size = (hEdges c.k5).size ∧
    (∀ i (hi : i < c.branch.size), 0 < c.branch[i].size) ∧
    (∀ i (hi : i < c.branch.size), connOKE adj c.branch[i] = true) ∧
    (labelBranches c.branch.toList 0 (Array.replicate nv 0)).isSome ∧
    ∀ e < (hEdges c.k5).size, witOKE adj c e = true := by
  unfold checkMinorE at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem brSet_disjointE (h : checkMinorE nv adj c = true) {i j : ℕ} (hi : i < c.branch.size)
    (hj : j < c.branch.size) (hij : i ≠ j) : Disjoint (brSet c i) (brSet c j) := by
  obtain ⟨-, -, -, -, h5, -⟩ := checkMinorE_parts h
  obtain ⟨lab', hlab⟩ := Option.isSome_iff_exists.1 h5
  obtain ⟨-, hmem⟩ := labelBranches_spec _ 0 _ _ hlab
  have key : ∀ i (hi : i < c.branch.size), ∀ x ∈ brSet c i, lab'.getD x 0 = i + 1 := by
    intro i hi x ⟨a, ha, hax⟩
    have hil : i < c.branch.toList.length := by simpa using hi
    have hmem' := hmem i hil ((brList c i).getD a (0, 0)) (by
      have hb : brList c i = c.branch.toList[i] := by simp [brList, Array.getD, hi]
      rw [← hb]
      simp only [Array.getD, ha, dite_true]
      exact Array.getElem_mem_toList ha)
    rw [← hax, hmem']
    omega
  rw [Set.disjoint_left]
  intro x hxi hxj
  have := (key i hi x hxi).symm.trans (key j hj x hxj)
  omega

theorem brSet_nonempty_connectedE (h : checkMinorE nv adj c = true) {i : ℕ} (hi : i < c.branch.size) :
    (brSet c i).Nonempty ∧ ((eSG adj).induce (brSet c i)).Connected := by
  obtain ⟨-, -, h3, h4, -, -⟩ := checkMinorE_parts h
  have hb : brList c i = c.branch[i] := by simp [brList, Array.getD, hi]
  have hpos : 0 < (brList c i).size := hb ▸ h3 i hi
  refine ⟨⟨_, 0, hpos, rfl⟩, ?_⟩
  exact connOKE_connected adj (brList c i) hpos (hb ▸ h4 i hi)

theorem brSet_adjE (h : checkMinorE nv adj c = true) {e : ℕ} (he : e < (hEdges c.k5).size) :
    ∃ x ∈ brSet c ((hEdges c.k5).getD e (0, 0)).1, ∃ y ∈ brSet c ((hEdges c.k5).getD e (0, 0)).2,
      (eSG adj).Adj x y := by
  obtain ⟨-, -, -, -, -, h6⟩ := checkMinorE_parts h
  have hw := h6 e he
  unfold witOKE at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨h1, h2⟩, h3⟩ := hw
  exact ⟨_, ⟨_, h1, rfl⟩, _, ⟨_, h2, rfl⟩, h3⟩

theorem isMinor_of_checkMinorE {U : Type} (H : SimpleGraph U) (idx : U → ℕ) (hinj : Function.Injective idx)
    (h : checkMinorE nv adj c = true) (hidx : ∀ u, idx u < c.branch.size)
    (hH : ∀ u u', H.Adj u u' → ∃ e < (hEdges c.k5).size,
      (hEdges c.k5).getD e (0, 0) = (idx u, idx u') ∨ (hEdges c.k5).getD e (0, 0) = (idx u', idx u)) :
    IsMinor H (eSG adj) := by
  refine ⟨fun u => brSet c (idx u), fun u => (brSet_nonempty_connectedE h (hidx u)).1,
    fun u => (brSet_nonempty_connectedE h (hidx u)).2, fun u u' huu' => ?_, fun u u' huu' => ?_⟩
  · exact brSet_disjointE h (hidx u) (hidx u') (fun e => huu' (hinj e))
  · obtain ⟨e, he, hlook | hlook⟩ := hH u u' huu'
    · obtain ⟨x, hx, y, hy, hxy⟩ := brSet_adjE h he
      rw [hlook] at hx hy
      exact ⟨x, hx, y, hy, hxy⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := brSet_adjE h he
      rw [hlook] at hx hy
      exact ⟨y, hy, x, hx, hasE_symm adj hxy⟩

/-- **An accepted certificate (edge test version) shows that the graph is not planar.** -/
theorem not_planar_of_checkMinorE (h : checkMinorE nv adj c = true) : ¬ Planar (eSG adj) := by
  obtain ⟨h1, -, -, -, -, -⟩ := checkMinorE_parts h
  rintro ⟨h5, h33⟩
  cases hk : c.k5
  · refine h33 (isMinor_of_checkMinorE _ idx33 idx33_injective h
      (fun u => by
        rw [h1, hk]
        rcases u with a | a <;> have := a.isLt <;> show _ < 6 <;> simp only [idx33, Sum.elim_inl, Sum.elim_inr] <;>
          omega) (fun u u' huu' => ?_))
    rw [hk]
    exact hEdges_k33 u u' huu'
  · refine h5 (isMinor_of_checkMinorE _ (fun u : Fin 5 => u.val) (fun a b e => Fin.ext e) h
      (fun u => by rw [h1, hk]; exact u.isLt) (fun u u' huu' => ?_))
    rw [hk]
    exact hEdges_k5 u u' (by simpa using huu')

end Thrackle78.Checker
