import Thrackle78.Proof.Overlap
import Thrackle78.Proof.Faces
import Thrackle78.Proof.Split

/-!
# Cases 1-3 by induction on the number of vertices

Scaled by 11 (`c = 15/11`):
* Case 1 (triangle-free): `11 m + 15 ≤ 15 n` (`n ≥ 1`);
* Case 2 (bipartite, the potential `D = 15 (n - 2) - 11 m`): `D ≥ -11` (`n ≥ 2`), `D ≥ -6` and `D ≥ -2` when `m ≥ n`
  (the latter unless `m = n = 6`); a connected thrackle with a triangle and `n ≥ 4` then has `11 m + 16 ≤ 15 n`
  (Conway doubling);
* Case 3 (all graphs): `11 m + 15 ≤ 15 n + 3`, and `11 m + 15 ≤ 15 n` for `n ≥ 4`.
Each induction splits a disconnected graph into two sides and a connected, not 2-connected graph at a cut vertex.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

section Induced

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
lemma induce_copy (S : Finset V) : G.induce (S : Set V) ⊑ G :=
  ⟨⟨(Embedding.induce (G := G) (S : Set V)).toHom, (Embedding.induce (G := G) (S : Set V)).injective⟩⟩

omit [Fintype V] [DecidableEq V] in
lemma card_induce_vert (S : Finset V) : Fintype.card (S : Set V) = S.card := by simp

/-- Every edge has both ends inside `S` or both inside `Sᶜ`, when `S` is closed under adjacency. -/
lemma edges_closed [DecidableRel G.Adj] (S : Finset V) (hS : ∀ x ∈ S, ∀ y, G.Adj x y → y ∈ S) :
    (∀ e ∈ G.edgeFinset, e.toFinset ⊆ S ∨ e.toFinset ⊆ Sᶜ) ∧
      ∀ e ∈ G.edgeFinset, ¬ (e.toFinset ⊆ S ∧ e.toFinset ⊆ Sᶜ) := by
  constructor
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      by_cases hx : x ∈ S
      · left
        intro z hz
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hS _ hx _ he
      · right
        intro z hz
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
        rw [Finset.mem_compl]
        rcases hz with rfl | rfl
        · exact hx
        · exact fun hy => hx (hS _ hy _ he.symm)
  · intro e he ⟨h1, h2⟩
    induction e using Sym2.ind with
    | h x y =>
      have hx : x ∈ S := h1 (by simp)
      have hx' : x ∈ Sᶜ := h2 (by simp)
      exact (Finset.mem_compl.1 hx') hx

/-- At a cut vertex `v` with side `C`: every edge lies inside `insert v C` or inside `Cᶜ`, not both. -/
lemma edges_cut [DecidableRel G.Adj] (v : V) (C : Finset V) (_hv : v ∉ C)
    (hC : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ C ∨ y = v) :
    (∀ e ∈ G.edgeFinset, e.toFinset ⊆ insert v C ∨ e.toFinset ⊆ Cᶜ) ∧
      ∀ e ∈ G.edgeFinset, ¬ (e.toFinset ⊆ insert v C ∧ e.toFinset ⊆ Cᶜ) := by
  constructor
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      by_cases hx : x ∈ C
      · left
        intro z hz
        rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_insert_of_mem hx
        · rcases hC _ hx _ he with h | h
          · exact Finset.mem_insert_of_mem h
          · rw [h]; exact Finset.mem_insert_self _ _
      · by_cases hy : y ∈ C
        · left
          intro z hz
          rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · rcases hC _ hy _ he.symm with h | h
            · exact Finset.mem_insert_of_mem h
            · rw [h]; exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem hy
        · right
          intro z hz
          rw [Sym2.mem_toFinset, Sym2.mem_iff] at hz
          rw [Finset.mem_compl]
          rcases hz with rfl | rfl
          · exact hx
          · exact hy
  · intro e he ⟨h1, h2⟩
    induction e using Sym2.ind with
    | h x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      have only_v : ∀ z, z ∈ insert v C → z ∈ Cᶜ → z = v := by
        intro z hz1 hz2
        rcases Finset.mem_insert.1 hz1 with h | h
        · exact h
        · exact absurd h (Finset.mem_compl.1 hz2)
      have ex := only_v x (h1 (by simp)) (h2 (by simp))
      have ey := only_v y (h1 (by simp)) (h2 (by simp))
      exact he.ne (ex.trans ey.symm)

omit [DecidableEq V] in
lemma edges_le_of_card_le_two [DecidableRel G.Adj] (h : Fintype.card V ≤ 2) :
    #G.edgeFinset ≤ Fintype.card V - 1 := by
  have h1 := card_edgeFinset_le_card_choose_two (G := G)
  have h2 : (Fintype.card V).choose 2 ≤ Fintype.card V - 1 := by
    interval_cases Fintype.card V <;> decide
  omega

omit [DecidableEq V] in
lemma edges_le_three [DecidableRel G.Adj] (h : Fintype.card V ≤ 3) : #G.edgeFinset ≤ 3 := by
  have h1 := card_edgeFinset_le_card_choose_two (G := G)
  have h2 : (Fintype.card V).choose 2 ≤ 3 := by
    interval_cases Fintype.card V <;> decide
  omega

end Induced

/-! ## Case 1: triangle-free -/

theorem case1 (ax : ThrackleAxioms Thr) (comp : CompFacts15) :
    ∀ (n : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 1 ≤ n → Thr G → G.CliqueFree 3 → 11 * #G.edgeFinset + 15 ≤ 15 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hcard hn hT htri
  -- the bound for an induced subgraph on a smaller set
  have sub : ∀ S : Finset V, S.card < n → 1 ≤ S.card →
      11 * #(G.induce (S : Set V)).edgeFinset + 15 ≤ 15 * S.card := fun S hS hS1 =>
    ih S.card hS (G.induce (S : Set V)) (card_induce_vert S) hS1 (ax.sub _ _ (induce_copy S) hT)
      (htri.comap (induce_copy S))
  by_cases hconn : G.Connected
  · by_cases h2 : TwoConn G
    · have := (twoConn_bound Thr ax hT h2 htri (hex_edge Thr ax comp hT htri)
        (no_six_eight Thr ax comp hT htri)).1
      omega
    · by_cases h3 : 3 ≤ n
      · obtain ⟨v, C, hv, hCne, hcompl, hC⟩ := cut_split hconn (by omega) h2
        obtain ⟨hcov, hdis⟩ := edges_cut v C hv hC
        have hsplit := edge_split _ _ hcov hdis
        have hc1 : (insert v C).card = C.card + 1 := Finset.card_insert_of_notMem hv
        have hc2 : (Cᶜ).card = n - C.card := by rw [Finset.card_compl, hcard]
        have hlt1 : (insert v C).card < n := by
          have h1 : 0 < ((insert v C)ᶜ).card := Finset.card_pos.2 hcompl
          rw [Finset.card_compl, hcard] at h1
          omega
        have hCle : C.card ≤ n := hcard ▸ Finset.card_le_univ C
        have hC1 : 1 ≤ C.card := Finset.card_pos.2 hCne
        have b1 := sub (insert v C) hlt1 (by omega)
        have b2 := sub Cᶜ (by omega) (by omega)
        omega
      · have := edges_le_of_card_le_two (G := G) (by omega)
        omega
  · have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨S, hSne, hScne, hS⟩ := disconnected_split hconn
    obtain ⟨hcov, hdis⟩ := edges_closed S hS
    have hsplit := edge_split _ _ hcov hdis
    have hc : S.card + (Sᶜ).card = n := by rw [Finset.card_compl, hcard]; have := Finset.card_le_univ S; omega
    have hS1 := Finset.card_pos.2 hSne
    have hS2 := Finset.card_pos.2 hScne
    have b1 := sub S (by omega) hS1
    have b2 := sub Sᶜ (by omega) hS2
    omega

/-! ## Case 2: bipartite graphs and the potential `D` -/

theorem case2 (ax : ThrackleAxioms Thr) (comp : CompFacts15) :
    ∀ (n : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 1 ≤ n → Thr G → G.Colorable 2 →
      (2 ≤ n → 11 * #G.edgeFinset + 30 ≤ 15 * n + 11) ∧
      (n ≤ #G.edgeFinset → 11 * #G.edgeFinset + 30 ≤ 15 * n + 6) ∧
      (n ≤ #G.edgeFinset → ¬ (#G.edgeFinset = 6 ∧ n = 6) → 11 * #G.edgeFinset + 30 ≤ 15 * n + 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hcard hn hT hbip
  have htri : G.CliqueFree 3 := hbip.cliqueFree (by norm_num)
  have sub : ∀ S : Finset V, S.card < n → 1 ≤ S.card →
      (2 ≤ S.card → 11 * #(G.induce (S : Set V)).edgeFinset + 30 ≤ 15 * S.card + 11) ∧
      (S.card ≤ #(G.induce (S : Set V)).edgeFinset →
        11 * #(G.induce (S : Set V)).edgeFinset + 30 ≤ 15 * S.card + 6) := fun S hS hS1 =>
    let h := ih S.card hS (G.induce (S : Set V)) (card_induce_vert S) hS1 (ax.sub _ _ (induce_copy S) hT)
      (hbip.of_hom (Embedding.induce (S : Set V)).toHom)
    ⟨h.1, h.2.1⟩
  -- one vertex has no edges
  have one : ∀ S : Finset V, S.card = 1 → #(G.induce (S : Set V)).edgeFinset = 0 := fun S hS => by
    have := edges_le_of_card_le_two (G := G.induce (S : Set V)) (by rw [card_induce_vert]; omega)
    rw [card_induce_vert] at this; omega
  by_cases hconn : G.Connected
  · by_cases h2 : TwoConn G
    · obtain ⟨b, hb6⟩ := (twoConn_bound Thr ax hT h2 htri (hex_edge Thr ax comp hT htri)
        (no_six_eight Thr ax comp hT htri)).2 hbip
      refine ⟨fun _ => by omega, fun _ => by omega, fun _ hne => ?_⟩
      rcases hb6 with h | h
      · omega
      · exact absurd ⟨h.1, hcard ▸ h.2⟩ hne
    · by_cases h3 : 3 ≤ n
      · obtain ⟨v, C, hv, hCne, hcompl, hC⟩ := cut_split hconn (by omega) h2
        obtain ⟨hcov, hdis⟩ := edges_cut v C hv hC
        have hsplit := edge_split _ _ hcov hdis
        have hc1 : (insert v C).card = C.card + 1 := Finset.card_insert_of_notMem hv
        have hc2 : (Cᶜ).card = n - C.card := by rw [Finset.card_compl, hcard]
        have hlt1 : (insert v C).card < n := by
          have h1 : 0 < ((insert v C)ᶜ).card := Finset.card_pos.2 hcompl
          rw [Finset.card_compl, hcard] at h1
          omega
        have hCle : C.card ≤ n := hcard ▸ Finset.card_le_univ C
        have hC1 : 1 ≤ C.card := Finset.card_pos.2 hCne
        have hCc : 2 ≤ (Cᶜ).card := by
          obtain ⟨w, hw⟩ := hcompl
          have hw' : w ∈ Cᶜ := Finset.mem_compl.2 fun h => Finset.mem_compl.1 hw (Finset.mem_insert_of_mem h)
          have hv' : v ∈ Cᶜ := Finset.mem_compl.2 hv
          have hwv : w ≠ v := fun h => by rw [h] at hw; simp at hw
          exact Finset.one_lt_card.2 ⟨w, hw', v, hv', hwv⟩
        obtain ⟨a1, b1⟩ := sub (insert v C) hlt1 (by omega)
        obtain ⟨a2, b2⟩ := sub Cᶜ (by omega) (by omega)
        have A1 := a1 (by omega)
        have A2 := a2 (by omega)
        refine ⟨fun _ => by omega, fun hmn => ?_, fun hmn _ => ?_⟩
        · by_cases hm1 : (insert v C).card ≤ #(G.induce ((insert v C : Finset V) : Set V)).edgeFinset
          · have := b1 hm1; omega
          · have := b2 (by omega); omega
        · by_cases hm1 : (insert v C).card ≤ #(G.induce ((insert v C : Finset V) : Set V)).edgeFinset
          · have := b1 hm1; omega
          · have := b2 (by omega); omega
      · have := edges_le_of_card_le_two (G := G) (by omega)
        refine ⟨fun _ => by omega, fun _ => by omega, fun _ _ => by omega⟩
  · have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨S, hSne, hScne, hS⟩ := disconnected_split hconn
    obtain ⟨hcov, hdis⟩ := edges_closed S hS
    have hsplit := edge_split _ _ hcov hdis
    have hc : S.card + (Sᶜ).card = n := by rw [Finset.card_compl, hcard]; have := Finset.card_le_univ S; omega
    have hS1 := Finset.card_pos.2 hSne
    have hS2 := Finset.card_pos.2 hScne
    obtain ⟨a1, b1⟩ := sub S (by omega) hS1
    obtain ⟨a2, b2⟩ := sub Sᶜ (by omega) hS2
    have e1 : S.card = 1 → #(G.induce (S : Set V)).edgeFinset = 0 := one S
    have e2 : (Sᶜ).card = 1 → #(G.induce ((Sᶜ : Finset V) : Set V)).edgeFinset = 0 := one Sᶜ
    have hA : 2 ≤ n → 11 * #G.edgeFinset + 30 ≤ 15 * n + 11 := by
      intro _
      by_cases h1 : 2 ≤ S.card <;> by_cases h2 : 2 ≤ (Sᶜ).card
      · have := a1 h1; have := a2 h2; omega
      · have := a1 h1; have := e2 (by omega); omega
      · have := a2 h2; have := e1 (by omega); omega
      · omega
    have hB : n ≤ #G.edgeFinset → 11 * #G.edgeFinset + 30 ≤ 15 * n + 2 := by
      intro hmn
      by_cases hm1 : S.card ≤ #(G.induce (S : Set V)).edgeFinset
      · have B1 := b1 hm1
        by_cases h2 : 2 ≤ (Sᶜ).card
        · have := a2 h2; omega
        · have := e2 (by omega); omega
      · have B2 := b2 (by omega)
        by_cases h1 : 2 ≤ S.card
        · have := a1 h1; omega
        · have := e1 (by omega); omega
    exact ⟨hA, fun h => by have := hB h; omega, fun h _ => hB h⟩

/-- **Case 2.** A connected thrackle with a triangle and `n ≥ 4` vertices has `11 m + 16 ≤ 15 n`. -/
theorem triangle_bound (ax : ThrackleAxioms Thr) (comp : CompFacts15) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : Thr G) (hconn : G.Connected) (hn : 4 ≤ Fintype.card V)
    (htri : ¬ G.CliqueFree 3) : 11 * #G.edgeFinset + 16 ≤ 15 * Fintype.card V := by
  classical
  obtain ⟨N, H, hTH, hHc, hHb, hN, hM⟩ := ax.double G hT hconn hn htri
  have hmG : Nat.card G.edgeSet = #G.edgeFinset := by
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  have hmH : Nat.card H.edgeSet = #H.edgeFinset := by
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  -- `G` contains a cycle, so `m ≥ n`
  have hmn : Fintype.card V ≤ #G.edgeFinset := by
    have h1 := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, hmG] at h1
    by_contra hlt
    have htree : G.IsTree := (isTree_iff_connected_and_card).2 ⟨hconn, by
      rw [hmG, Nat.card_eq_fintype_card]; omega⟩
    exact htri (htree.isAcyclic.cliqueFree le_rfl)
  have h := (case2 Thr ax comp N H (Fintype.card_fin N) (by omega) hTH hHb).2.2 (by omega)
    (by intro h; omega)
  omega

/-! ## Case 3: all graphs -/

theorem case3 (ax : ThrackleAxioms Thr) (comp : CompFacts15) :
    ∀ (n : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 1 ≤ n → Thr G →
      11 * #G.edgeFinset + 15 ≤ 15 * n + 3 ∧ (4 ≤ n → 11 * #G.edgeFinset + 15 ≤ 15 * n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hcard hn hT
  by_cases hconn : G.Connected
  · by_cases htri : G.CliqueFree 3
    · have := case1 Thr ax comp n G hcard hn hT htri
      exact ⟨by omega, fun _ => this⟩
    · by_cases h4 : 4 ≤ n
      · have := triangle_bound Thr ax comp G hT hconn (by omega) htri
        exact ⟨by omega, fun _ => by omega⟩
      · have := edges_le_three (G := G) (by omega)
        refine ⟨?_, fun h => absurd h h4⟩
        by_cases h3 : n = 3
        · omega
        · have := edges_le_of_card_le_two (G := G) (by omega)
          omega
  · have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨S, hSne, hScne, hS⟩ := disconnected_split hconn
    obtain ⟨hcov, hdis⟩ := edges_closed S hS
    have hsplit := edge_split _ _ hcov hdis
    have hc : S.card + (Sᶜ).card = n := by rw [Finset.card_compl, hcard]; have := Finset.card_le_univ S; omega
    have hS1 := Finset.card_pos.2 hSne
    have hS2 := Finset.card_pos.2 hScne
    have b1 := (ih S.card (by omega) (G.induce (S : Set V)) (card_induce_vert S) hS1
      (ax.sub _ _ (induce_copy S) hT)).1
    have b2 := (ih (Sᶜ).card (by omega) (G.induce ((Sᶜ : Finset V) : Set V)) (card_induce_vert Sᶜ) hS2
      (ax.sub _ _ (induce_copy Sᶜ) hT)).1
    exact ⟨by omega, fun _ => by omega⟩

end Thrackle78.Proof
