import Thrackle78.Defs
import Thrackle78Core.Minor

/-!
# Minor models: transfer along branch-set maps, and soundness of `Thrackle78Core.checkMinor`

* `isMinor_of_map`: a minor model of `H` (without isolated vertices) in `G'` transfers to `G` along a map `φ` that sends
  the non-isolated vertices of `G'` to nonempty, connected, pairwise disjoint vertex sets of `G`, and every edge of `G'`
  to an edge of `G` between the two image sets.
* `not_planar_of_map`: hence non-planarity transfers along such maps.
* `checkMinor_sound`: an accepted certificate gives a `K₅` or a `K₃,₃` minor of `G.toSG`; `not_planar_of_checkMinor`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

/-! ## Transfer of minor models -/

section Transfer

variable {U V W : Type}

/-- In a minor model of a graph without isolated vertices, every branch vertex has a neighbour. -/
theorem exists_adj_of_mem_branch {H : SimpleGraph U} {G : SimpleGraph V} {B : U → Set V}
    (hconn : ∀ u, (G.induce (B u)).Connected)
    (hadj : ∀ u u', H.Adj u u' → ∃ x ∈ B u, ∃ y ∈ B u', G.Adj x y) (hH : ∀ u, ∃ u', H.Adj u u')
    {u : U} {x : V} (hx : x ∈ B u) : ∃ y, G.Adj x y := by
  obtain ⟨u', hu'⟩ := hH u
  obtain ⟨x', hx', y', -, hxy'⟩ := hadj u u' hu'
  by_cases hxx : x = x'
  · exact ⟨y', hxx ▸ hxy'⟩
  · have hr : (G.induce (B u)).Reachable ⟨x, hx⟩ ⟨x', hx'⟩ := (hconn u).preconnected _ _
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, hc, -⟩
    · exact absurd (congrArg Subtype.val h) hxx
    · exact ⟨c.1, by simpa using hc⟩

/-- **Transfer of a minor model** along a branch-set map `φ` given on the non-isolated vertices of `G'`. -/
theorem isMinor_of_map {H : SimpleGraph U} {G' : SimpleGraph V} {G : SimpleGraph W}
    (hH : ∀ u, ∃ u', H.Adj u u') (h : IsMinor H G') (φ : V → Set W)
    (hne : ∀ x, (∃ y, G'.Adj x y) → (φ x).Nonempty)
    (hcon : ∀ x, (∃ y, G'.Adj x y) → (G.induce (φ x)).Connected)
    (hdis : ∀ x x', (∃ y, G'.Adj x y) → (∃ y, G'.Adj x' y) → x ≠ x' → Disjoint (φ x) (φ x'))
    (hadj : ∀ x x', G'.Adj x x' → ∃ a ∈ φ x, ∃ b ∈ φ x', G.Adj a b) :
    IsMinor H G := by
  obtain ⟨B, hBne, hBcon, hBdis, hBadj⟩ := h
  have hS : ∀ u, ∀ x ∈ B u, ∃ y, G'.Adj x y := fun u x hx =>
    exists_adj_of_mem_branch hBcon hBadj hH hx
  refine ⟨fun u => ⋃ x ∈ B u, φ x, fun u => ?_, fun u => ?_, fun u u' huu' => ?_, fun u u' huu' => ?_⟩
  · obtain ⟨x, hx⟩ := hBne u
    obtain ⟨a, ha⟩ := hne x (hS u x hx)
    exact ⟨a, Set.mem_biUnion hx ha⟩
  · obtain ⟨x₀, hx₀⟩ := hBne u
    obtain ⟨a₀, ha₀⟩ := hne x₀ (hS u x₀ hx₀)
    have hsub : ∀ x ∈ B u, φ x ⊆ ⋃ x ∈ B u, φ x := fun x hx a ha => Set.mem_biUnion hx ha
    have hloc : ∀ x (hx : x ∈ B u) a (ha : a ∈ φ x) b (hb : b ∈ φ x),
        (G.induce (⋃ x ∈ B u, φ x)).Reachable ⟨a, hsub x hx ha⟩ ⟨b, hsub x hx hb⟩ := by
      intro x hx a ha b hb
      exact ((hcon x (hS u x hx)).preconnected ⟨a, ha⟩ ⟨b, hb⟩).map
        (SimpleGraph.induceHomOfLE G (hsub x hx)).toHom
    have key : ∀ c : B u, Relation.ReflTransGen (G'.induce (B u)).Adj ⟨x₀, hx₀⟩ c → ∀ b (hb : b ∈ φ c.1),
        (G.induce (⋃ x ∈ B u, φ x)).Reachable ⟨a₀, hsub x₀ hx₀ ha₀⟩ ⟨b, hsub c.1 c.2 hb⟩ := by
      intro c hc
      induction hc with
      | refl => exact fun b hb => hloc x₀ hx₀ a₀ ha₀ b hb
      | @tail c d _ hcd ih =>
        intro b hb
        have hcd' : G'.Adj c.1 d.1 := by simpa using hcd
        obtain ⟨a', ha', b', hb', hab'⟩ := hadj c.1 d.1 hcd'
        refine ((ih a' ha').trans ?_).trans (hloc d.1 d.2 b' hb' b hb)
        exact SimpleGraph.Adj.reachable (by simpa using hab')
    have : Nonempty (⋃ x ∈ B u, φ x : Set W) := ⟨⟨a₀, hsub x₀ hx₀ ha₀⟩⟩
    refine Connected.mk fun p q => ?_
    obtain ⟨p, hp⟩ := p
    obtain ⟨q, hq⟩ := q
    have hp' := hp
    have hq' := hq
    rw [Set.mem_iUnion₂] at hp' hq'
    obtain ⟨y, hy, hpy⟩ := hp'
    obtain ⟨z, hz, hqz⟩ := hq'
    have r1 := key ⟨y, hy⟩ (by
      rw [← SimpleGraph.reachable_iff_reflTransGen]; exact (hBcon u).preconnected _ _) p hpy
    have r2 := key ⟨z, hz⟩ (by
      rw [← SimpleGraph.reachable_iff_reflTransGen]; exact (hBcon u).preconnected _ _) q hqz
    exact r1.symm.trans r2
  · show Disjoint (⋃ x ∈ B u, φ x) (⋃ x ∈ B u', φ x)
    rw [Set.disjoint_left]
    intro a ha ha'
    rw [Set.mem_iUnion₂] at ha ha'
    obtain ⟨x, hx, hax⟩ := ha
    obtain ⟨x', hx', hax'⟩ := ha'
    have hxx' : x ≠ x' := by
      rintro rfl
      exact Set.disjoint_left.mp (hBdis huu') hx hx'
    exact Set.disjoint_left.mp (hdis x x' (hS u x hx) (hS u' x' hx') hxx') hax hax'
  · obtain ⟨x, hx, x', hx', hxx'⟩ := hBadj u u' huu'
    obtain ⟨a, ha, b, hb, hab⟩ := hadj x x' hxx'
    exact ⟨a, Set.mem_biUnion hx ha, b, Set.mem_biUnion hx' hb, hab⟩

/-- `K₅` has no isolated vertices. -/
theorem k5_noIso : ∀ u : Fin 5, ∃ u', (completeGraph (Fin 5)).Adj u u' := by decide

/-- `K₃,₃` has no isolated vertices. -/
theorem k33_noIso : ∀ u : Fin 3 ⊕ Fin 3, ∃ u', (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u u' := by
  rintro (a | a)
  · exact ⟨Sum.inr 0, by simp⟩
  · exact ⟨Sum.inl 0, by simp⟩

/-- **Non-planarity transfers** along a branch-set map given on the non-isolated vertices of `G'`. -/
theorem not_planar_of_map {G' : SimpleGraph V} {G : SimpleGraph W} (h : ¬ Planar G') (φ : V → Set W)
    (hne : ∀ x, (∃ y, G'.Adj x y) → (φ x).Nonempty)
    (hcon : ∀ x, (∃ y, G'.Adj x y) → (G.induce (φ x)).Connected)
    (hdis : ∀ x x', (∃ y, G'.Adj x y) → (∃ y, G'.Adj x' y) → x ≠ x' → Disjoint (φ x) (φ x'))
    (hadj : ∀ x x', G'.Adj x x' → ∃ a ∈ φ x, ∃ b ∈ φ x', G.Adj a b) :
    ¬ Planar G := by
  rintro ⟨h5, h33⟩
  exact h ⟨fun hm => h5 (isMinor_of_map k5_noIso hm φ hne hcon hdis hadj),
    fun hm => h33 (isMinor_of_map k33_noIso hm φ hne hcon hdis hadj)⟩

end Transfer

/-! ## The graph of an `AGraph` -/

theorem hasEdge_symm (G : AGraph) {x y : ℕ} (h : G.hasEdge x y = true) : G.hasEdge y x = true := by
  unfold AGraph.hasEdge at h ⊢
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at h ⊢
  exact ⟨fun e => h.1 e.symm, h.2.symm⟩

theorem hasEdge_irrefl (G : AGraph) (x : ℕ) : ¬ G.hasEdge x x = true := by
  unfold AGraph.hasEdge
  simp

/-- The graph of `G : AGraph` on `ℕ` (adjacency lists read symmetrically, no loops). -/
def _root_.Thrackle78Core.AGraph.toSG (G : AGraph) : SimpleGraph ℕ where
  Adj x y := G.hasEdge x y = true
  symm := ⟨fun _ _ h => hasEdge_symm G h⟩
  loopless := ⟨fun x h => hasEdge_irrefl G x h⟩

@[simp] theorem _root_.Thrackle78Core.AGraph.toSG_adj (G : AGraph) (x y : ℕ) :
    G.toSG.Adj x y ↔ G.hasEdge x y = true := Iff.rfl

/-! ## Soundness of the checker -/

section Sound

/-- `Array.getD` after `set!`. -/
theorem getD_set! (a : Array ℕ) (i j v : ℕ) :
    (a.set! i v).getD j 0 = if i = j ∧ j < a.size then v else a.getD j 0 := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set! i v).size := by simpa using hj
    rw [Array.getD, Array.getD, dite_eq_left_of_eq_true (eq_true hj'), dite_eq_left_of_eq_true (eq_true hj)]
    simp only [Array.set!]
    by_cases hij : i = j <;> simp [hij, hj]
  · simp [Array.getD, hj]

theorem labelList_spec (u : ℕ) : ∀ (B : List (ℕ × ℕ)) (lab lab' : Array ℕ), labelList u B lab = some lab' →
    (∀ q, lab.getD q 0 ≠ 0 → lab'.getD q 0 = lab.getD q 0) ∧ ∀ p ∈ B, lab'.getD p.1 0 = u + 1
  | [], lab, lab', h => by
    simp only [labelList, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ => rfl, by simp⟩
  | p :: rest, lab, lab', h => by
    simp only [labelList] at h
    split_ifs at h with hc
    obtain ⟨hp, h0⟩ := hc
    obtain ⟨hkeep, hmem⟩ := labelList_spec u rest _ _ h
    have hpv : (lab.set! p.1 (u + 1)).getD p.1 0 = u + 1 := by rw [getD_set!]; simp [hp]
    refine ⟨fun q hq => ?_, fun p' hp' => ?_⟩
    · have hqp : p.1 ≠ q := by rintro rfl; exact hq h0
      have hq1 : (lab.set! p.1 (u + 1)).getD q 0 = lab.getD q 0 := by rw [getD_set!]; simp [hqp]
      rw [hkeep q (by rw [hq1]; exact hq), hq1]
    · rcases List.mem_cons.1 hp' with rfl | hp'
      · rw [hkeep _ (by rw [hpv]; omega), hpv]
      · exact hmem p' hp'

theorem labelBranches_spec : ∀ (Bs : List (Array (ℕ × ℕ))) (u : ℕ) (lab lab' : Array ℕ),
    labelBranches Bs u lab = some lab' →
    (∀ q, lab.getD q 0 ≠ 0 → lab'.getD q 0 = lab.getD q 0) ∧
    ∀ i (hi : i < Bs.length), ∀ p ∈ (Bs[i]).toList, lab'.getD p.1 0 = u + i + 1
  | [], u, lab, lab', h => by
    simp only [labelBranches, Option.some.injEq] at h
    subst h
    exact ⟨fun _ _ => rfl, fun i hi => absurd hi (by simp)⟩
  | B :: Bs, u, lab, lab', h => by
    simp only [labelBranches] at h
    split at h
    · simp at h
    · rename_i lab₁ h₁
      obtain ⟨hkeep₁, hmem₁⟩ := labelList_spec u B.toList lab lab₁ h₁
      obtain ⟨hkeep₂, hmem₂⟩ := labelBranches_spec Bs (u + 1) lab₁ lab' h
      refine ⟨fun q hq => (hkeep₂ q (by rw [hkeep₁ q hq]; exact hq)).trans (hkeep₁ q hq), fun i hi p hp => ?_⟩
      cases i with
      | zero =>
        have h1 := hmem₁ p (by simpa using hp)
        rw [hkeep₂ _ (by rw [h1]; omega), h1]
      | succ i =>
        rw [hmem₂ i (by simpa using hi) p (by simpa using hp)]
        omega

/-- The `i`-th branch list of a certificate. -/
def brList (c : MinorCert) (i : ℕ) : Array (ℕ × ℕ) := c.branch.getD i #[]

/-- The vertex set of the `i`-th branch. -/
def brSet (c : MinorCert) (i : ℕ) : Set ℕ := {x | ∃ j < (brList c i).size, ((brList c i).getD j (0, 0)).1 = x}

/-- A connection order makes a branch set connected. -/
theorem connOK_connected (G : AGraph) (B : Array (ℕ × ℕ)) (hpos : 0 < B.size) (hc : connOK G B = true) :
    (G.toSG.induce {x | ∃ j < B.size, (B.getD j (0, 0)).1 = x}).Connected := by
  have hmem : ∀ j < B.size, (B.getD j (0, 0)).1 ∈ {x | ∃ j < B.size, (B.getD j (0, 0)).1 = x} :=
    fun j hj => ⟨j, hj, rfl⟩
  have step : ∀ j < B.size, j ≠ 0 → (B.getD j (0, 0)).2 < j ∧
      G.hasEdge (B.getD j (0, 0)).1 (B.getD (B.getD j (0, 0)).2 (0, 0)).1 = true := by
    intro j hj hj0
    unfold connOK at hc
    rw [List.all_eq_true] at hc
    have := hc j (List.mem_range.2 hj)
    simpa [hj0] using this
  have reach : ∀ j (hj : j < B.size), (G.toSG.induce {x | ∃ j < B.size, (B.getD j (0, 0)).1 = x}).Reachable
      ⟨(B.getD 0 (0, 0)).1, hmem 0 hpos⟩ ⟨(B.getD j (0, 0)).1, hmem j hj⟩ := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases hj0 : j = 0
      · subst hj0; rfl
      · obtain ⟨hlt, hedge⟩ := step j hj hj0
        refine (ih _ hlt (lt_trans hlt hj)).trans (SimpleGraph.Adj.reachable ?_)
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, AGraph.toSG_adj]
        exact hasEdge_symm G hedge
  have : Nonempty {x | ∃ j < B.size, (B.getD j (0, 0)).1 = x} := ⟨⟨_, hmem 0 hpos⟩⟩
  refine Connected.mk fun p q => ?_
  obtain ⟨p, j, hj, rfl⟩ := p
  obtain ⟨q, k, hk, rfl⟩ := q
  exact (reach j hj).symm.trans (reach k hk)

variable {G : AGraph} {c : MinorCert}

theorem checkMinor_parts (h : checkMinor G c = true) :
    c.branch.size = numBranch c.k5 ∧ c.wit.size = (hEdges c.k5).size ∧
    (∀ i (hi : i < c.branch.size), 0 < c.branch[i].size) ∧ (∀ i (hi : i < c.branch.size), connOK G c.branch[i] = true) ∧
    (labelBranches c.branch.toList 0 (Array.replicate G.nv 0)).isSome ∧
    ∀ e < (hEdges c.k5).size, witOK G c e = true := by
  unfold checkMinor at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- Distinct branch indices give disjoint branch sets. -/
theorem brSet_disjoint (h : checkMinor G c = true) {i j : ℕ} (hi : i < c.branch.size) (hj : j < c.branch.size)
    (hij : i ≠ j) : Disjoint (brSet c i) (brSet c j) := by
  obtain ⟨-, -, -, -, h5, -⟩ := checkMinor_parts h
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

/-- The branch sets of an accepted certificate are nonempty and connected. -/
theorem brSet_nonempty_connected (h : checkMinor G c = true) {i : ℕ} (hi : i < c.branch.size) :
    (brSet c i).Nonempty ∧ (G.toSG.induce (brSet c i)).Connected := by
  obtain ⟨-, -, h3, h4, -, -⟩ := checkMinor_parts h
  have hb : brList c i = c.branch[i] := by simp [brList, Array.getD, hi]
  have hpos : 0 < (brList c i).size := hb ▸ h3 i hi
  refine ⟨⟨_, 0, hpos, rfl⟩, ?_⟩
  exact connOK_connected G (brList c i) hpos (hb ▸ h4 i hi)

/-- The witness of an `H`-edge. -/
theorem brSet_adj (h : checkMinor G c = true) {e : ℕ} (he : e < (hEdges c.k5).size) :
    ∃ x ∈ brSet c ((hEdges c.k5).getD e (0, 0)).1, ∃ y ∈ brSet c ((hEdges c.k5).getD e (0, 0)).2,
      G.toSG.Adj x y := by
  obtain ⟨-, -, -, -, -, h6⟩ := checkMinor_parts h
  have hw := h6 e he
  unfold witOK at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨h1, h2⟩, h3⟩ := hw
  exact ⟨_, ⟨_, h1, rfl⟩, _, ⟨_, h2, rfl⟩, h3⟩

/-- **Generic soundness**: an accepted certificate gives a minor model of any `H` whose vertices are numbered
injectively by branch indices so that every `H`-edge is an edge of `hEdges c.k5` (in either orientation). -/
theorem isMinor_of_checkMinor {U : Type} (H : SimpleGraph U) (idx : U → ℕ) (hinj : Function.Injective idx)
    (h : checkMinor G c = true) (hidx : ∀ u, idx u < c.branch.size)
    (hH : ∀ u u', H.Adj u u' → ∃ e < (hEdges c.k5).size,
      (hEdges c.k5).getD e (0, 0) = (idx u, idx u') ∨ (hEdges c.k5).getD e (0, 0) = (idx u', idx u)) :
    IsMinor H G.toSG := by
  refine ⟨fun u => brSet c (idx u), fun u => (brSet_nonempty_connected h (hidx u)).1,
    fun u => (brSet_nonempty_connected h (hidx u)).2, fun u u' huu' => ?_, fun u u' huu' => ?_⟩
  · exact brSet_disjoint h (hidx u) (hidx u') (fun e => huu' (hinj e))
  · obtain ⟨e, he, hlook | hlook⟩ := hH u u' huu'
    · obtain ⟨x, hx, y, hy, hxy⟩ := brSet_adj h he
      rw [hlook] at hx hy
      exact ⟨x, hx, y, hy, hxy⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := brSet_adj h he
      rw [hlook] at hx hy
      exact ⟨y, hy, x, hx, hasEdge_symm G hxy⟩

theorem hEdges_k5 : ∀ u u' : Fin 5, u ≠ u' → ∃ e < (hEdges true).size,
    (hEdges true).getD e (0, 0) = (u.val, u'.val) ∨ (hEdges true).getD e (0, 0) = (u'.val, u.val) := by
  decide

/-- The branch index of a vertex of `K₃,₃` (sides `{0, 1, 2}` and `{3, 4, 5}`). -/
def idx33 : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim (fun i => i.val) (fun j => 3 + j.val)

theorem idx33_injective : Function.Injective idx33 := by
  rintro (a | a) (b | b) h <;> simp [idx33] at h <;> first | (congr 1; exact Fin.ext h) | omega

theorem hEdges_k33 : ∀ u u' : Fin 3 ⊕ Fin 3, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u u' →
    ∃ e < (hEdges false).size,
      (hEdges false).getD e (0, 0) = (idx33 u, idx33 u') ∨ (hEdges false).getD e (0, 0) = (idx33 u', idx33 u) := by
  rintro (a | a) (b | b) h
  · simp at h
  · have key : ∀ a b : Fin 3, ∃ e < (hEdges false).size, (hEdges false).getD e (0, 0) = (a.val, 3 + b.val) ∨
        (hEdges false).getD e (0, 0) = (3 + b.val, a.val) := by decide
    simpa [idx33] using key a b
  · have key : ∀ a b : Fin 3, ∃ e < (hEdges false).size, (hEdges false).getD e (0, 0) = (3 + a.val, b.val) ∨
        (hEdges false).getD e (0, 0) = (b.val, 3 + a.val) := by decide
    simpa [idx33] using key a b
  · simp at h

/-- **Soundness of the minor-model checker.** -/
theorem checkMinor_sound (h : checkMinor G c = true) :
    (c.k5 = true → IsMinor (completeGraph (Fin 5)) G.toSG) ∧
    (c.k5 = false → IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) G.toSG) := by
  obtain ⟨h1, -, -, -, -, -⟩ := checkMinor_parts h
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · refine isMinor_of_checkMinor _ (fun u : Fin 5 => u.val) (fun a b e => Fin.ext e) h
      (fun u => by rw [h1, hk]; exact u.isLt) (fun u u' huu' => ?_)
    rw [hk]
    exact hEdges_k5 u u' (by simpa using huu')
  · refine isMinor_of_checkMinor _ idx33 idx33_injective h
      (fun u => by
        rw [h1, hk]
        rcases u with a | a <;> have := a.isLt <;> show _ < 6 <;> simp only [idx33, Sum.elim_inl, Sum.elim_inr] <;>
          omega) (fun u u' huu' => ?_)
    rw [hk]
    exact hEdges_k33 u u' huu'

/-- An accepted certificate shows that `G.toSG` is not planar. -/
theorem not_planar_of_checkMinor (h : checkMinor G c = true) : ¬ Planar G.toSG := by
  rintro ⟨h5, h33⟩
  cases hk : c.k5
  · exact h33 ((checkMinor_sound h).2 hk)
  · exact h5 ((checkMinor_sound h).1 hk)

end Sound

end Thrackle78.Checker
