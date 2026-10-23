import Thrackle78.Proof.Cases
import Thrackle78.Proof.Faces2720
import Thrackle78.Proof.Hex66

/-!
# Cases 1-3 for `27/20` by induction on the number of vertices

Scaled by 20 (`c = 27/20`):
* Case 1 (triangle-free): `20 m + 27 ≤ 27 n` (`n ≥ 1`);
* Case 2 (bipartite, the potential `D = 27 (n - 2) - 20 m`): `D ≥ -20` (`n ≥ 2`), `D ≥ -12` and `D ≥ -5` when `m ≥ n`
  (the latter unless `m = n = 6`); a connected thrackle with a triangle and `n ≥ 4` then has `20 m + 28 ≤ 27 n`
  (Conway doubling);
* Case 3 (all graphs): `20 m + 27 ≤ 27 n + 6`, and `20 m + 27 ≤ 27 n` for `n ≥ 4`.
The inductions are those of `Cases` with the `27/20` bound for 2-connected graphs.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

/-! ## Case 1: triangle-free -/

theorem case1_2720 (ax : ThrackleAxioms Thr) (comp : CompFacts) :
    ∀ (n : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 1 ≤ n → Thr G → G.CliqueFree 3 → 20 * #G.edgeFinset + 27 ≤ 27 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hcard hn hT htri
  -- the bound for an induced subgraph on a smaller set
  have sub : ∀ S : Finset V, S.card < n → 1 ≤ S.card →
      20 * #(G.induce (S : Set V)).edgeFinset + 27 ≤ 27 * S.card := fun S hS hS1 =>
    ih S.card hS (G.induce (S : Set V)) (card_induce_vert S) hS1 (ax.sub _ _ (induce_copy S) hT)
      (htri.comap (induce_copy S))
  by_cases hconn : G.Connected
  · by_cases h2 : TwoConn G
    · have := (twoConn_bound2720 Thr ax hT h2 htri (hex_tf Thr ax comp hT htri)
        (no_six_eight Thr ax comp.to15 hT htri)).1
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

theorem case2_2720 (ax : ThrackleAxioms Thr) (comp : CompFacts) :
    ∀ (n : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 1 ≤ n → Thr G → G.Colorable 2 →
      (2 ≤ n → 20 * #G.edgeFinset + 54 ≤ 27 * n + 20) ∧
      (n ≤ #G.edgeFinset → 20 * #G.edgeFinset + 54 ≤ 27 * n + 12) ∧
      (n ≤ #G.edgeFinset → ¬ (#G.edgeFinset = 6 ∧ n = 6) → 20 * #G.edgeFinset + 54 ≤ 27 * n + 5) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hcard hn hT hbip
  have htri : G.CliqueFree 3 := hbip.cliqueFree (by norm_num)
  have sub : ∀ S : Finset V, S.card < n → 1 ≤ S.card →
      (2 ≤ S.card → 20 * #(G.induce (S : Set V)).edgeFinset + 54 ≤ 27 * S.card + 20) ∧
      (S.card ≤ #(G.induce (S : Set V)).edgeFinset →
        20 * #(G.induce (S : Set V)).edgeFinset + 54 ≤ 27 * S.card + 12) := fun S hS hS1 =>
    let h := ih S.card hS (G.induce (S : Set V)) (card_induce_vert S) hS1 (ax.sub _ _ (induce_copy S) hT)
      (hbip.of_hom (Embedding.induce (S : Set V)).toHom)
    ⟨h.1, h.2.1⟩
  -- one vertex has no edges
  have one : ∀ S : Finset V, S.card = 1 → #(G.induce (S : Set V)).edgeFinset = 0 := fun S hS => by
    have := edges_le_of_card_le_two (G := G.induce (S : Set V)) (by rw [card_induce_vert]; omega)
    rw [card_induce_vert] at this; omega
  by_cases hconn : G.Connected
  · by_cases h2 : TwoConn G
    · have hb6 := (twoConn_bound2720 Thr ax hT h2 htri (hex_tf Thr ax comp hT htri)
        (no_six_eight Thr ax comp.to15 hT htri)).2 hbip
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
    have hA : 2 ≤ n → 20 * #G.edgeFinset + 54 ≤ 27 * n + 20 := by
      intro _
      by_cases h1 : 2 ≤ S.card <;> by_cases h2 : 2 ≤ (Sᶜ).card
      · have := a1 h1; have := a2 h2; omega
      · have := a1 h1; have := e2 (by omega); omega
      · have := a2 h2; have := e1 (by omega); omega
      · omega
    have hB : n ≤ #G.edgeFinset → 20 * #G.edgeFinset + 54 ≤ 27 * n + 5 := by
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

/-- **Case 2.** A connected thrackle with a triangle and `n ≥ 4` vertices has `20 m + 28 ≤ 27 n`. -/
theorem triangle_bound2720 (ax : ThrackleAxioms Thr) (comp : CompFacts) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hT : Thr G) (hconn : G.Connected) (hn : 4 ≤ Fintype.card V)
    (htri : ¬ G.CliqueFree 3) : 20 * #G.edgeFinset + 28 ≤ 27 * Fintype.card V := by
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
  have h := (case2_2720 Thr ax comp N H (Fintype.card_fin N) (by omega) hTH hHb).2.2 (by omega)
    (by intro h; omega)
  omega

/-! ## Case 3: all graphs -/

theorem case3_2720 (ax : ThrackleAxioms Thr) (comp : CompFacts) :
    ∀ (n : ℕ) {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V = n → 1 ≤ n → Thr G →
      20 * #G.edgeFinset + 27 ≤ 27 * n + 6 ∧ (4 ≤ n → 20 * #G.edgeFinset + 27 ≤ 27 * n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ G _ hcard hn hT
  by_cases hconn : G.Connected
  · by_cases htri : G.CliqueFree 3
    · have := case1_2720 Thr ax comp n G hcard hn hT htri
      exact ⟨by omega, fun _ => this⟩
    · by_cases h4 : 4 ≤ n
      · have := triangle_bound2720 Thr ax comp G hT hconn (by omega) htri
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
