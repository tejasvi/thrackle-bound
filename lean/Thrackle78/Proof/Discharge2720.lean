import Thrackle78.Proof.Discharge

/-!
# The discharging count for `27/20`

Charges `(7 len - 54)/20` on the faces. Every 6-edge (a traversal, by a face of length `≥ 10`, of an edge whose other
side is a 6-face) carries `1/10` to the 6-face; a 6-face has six of them, a 10-face at most eight (`h10`), and a face of
length `d ≥ 12` at most `d`. All final charges are nonnegative, so `∑ (7 len - 54) ≥ 0`, i.e. `27 f ≤ 7 m`.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The edge of the traversal `i` of a closed walk. -/
def trav (W : CWalk G) (i : Fin W.len) : Sym2 V := s(W.v i, W.v (finRotate W.len i))

/-- The number of 6-edges of a closed walk: traversals of edges with a 6-face side. -/
def halfCount (D : FaceData G) (W : CWalk G) : ℕ :=
  #(univ.filter fun i : Fin W.len => 1 ≤ kindCount D (· = 6) (trav W i))

lemma halfCount_le_len (D : FaceData G) (W : CWalk G) : halfCount D W ≤ W.len := by
  unfold halfCount
  exact (card_filter_le _ _).trans (by simp)

/-- The 6-edges of a closed walk, counted through the edges. -/
lemma halfCount_eq_sum (D : FaceData G) (W : CWalk G) :
    halfCount D W = ∑ x ∈ G.edgeFinset, if 1 ≤ kindCount D (· = 6) x then W.count x else 0 := by
  unfold halfCount
  rw [card_eq_sum_card_fiberwise (t := G.edgeFinset) (f := trav W) (fun i _ => cwalk_edge_mem W i)]
  refine sum_congr rfl fun x _ => ?_
  rw [filter_filter]
  split_ifs with hx
  · unfold CWalk.count
    congr 1
    refine filter_congr fun i _ => ?_
    constructor
    · exact fun h => h.2
    · intro h
      have h' : trav W i = x := h
      exact ⟨h' ▸ hx, h'⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro i - ⟨h1, h2⟩
    exact hx (h2 ▸ h1)

/-- **Discharging for `27/20`.** -/
theorem discharge2720 (D : FaceData G) (hlen : ∀ i : Fin D.faces.length, 6 ≤ (D.faces.get i).len)
    (hAC : ∀ x ∈ G.edgeFinset, kindCount D (· = 6) x ≤ kindCount D (10 ≤ ·) x)
    (h10 : ∀ i : Fin D.faces.length, (D.faces.get i).len = 10 → halfCount D (D.faces.get i) ≤ 8) :
    27 * D.faces.length ≤ 7 * G.edgeFinset.card := by
  -- the lengths add up to 2m
  have hsum : ∑ i : Fin D.faces.length, (D.faces.get i).len = 2 * G.edgeFinset.card := by
    have h1 : ∑ i : Fin D.faces.length, (D.faces.get i).len =
        ∑ x ∈ G.edgeFinset, ∑ i : Fin D.faces.length, (D.faces.get i).count x := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => (cwalk_sum_count _).symm
    rw [h1, Finset.sum_congr rfl fun x hx => (list_map_sum_eq_fin D.faces (fun F => F.count x)).symm.trans
      (D.cover x hx), Finset.sum_const, smul_eq_mul, mul_comm]
  -- 6-faces against the 6-edges of 10⁺-faces
  have h6 : ∑ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 6), (D.faces.get i).len ≤
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len), halfCount D (D.faces.get i) := by
    rw [← sum_kindCount D (· = 6)]
    calc ∑ x ∈ G.edgeFinset, kindCount D (· = 6) x
        ≤ ∑ x ∈ G.edgeFinset, if 1 ≤ kindCount D (· = 6) x then kindCount D (10 ≤ ·) x else 0 :=
          Finset.sum_le_sum fun x hx => by
            split_ifs with h
            · exact hAC x hx
            · omega
      _ = ∑ i ∈ univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len),
            halfCount D (D.faces.get i) := by
          simp_rw [halfCount_eq_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          unfold kindCount
          split_ifs with h
          · rfl
          · simp
  -- every face has length 6, 8 or ≥ 10
  have hsplit : ∀ i : Fin D.faces.length, (D.faces.get i).len = 6 ∨ (D.faces.get i).len = 8 ∨
      10 ≤ (D.faces.get i).len := by
    intro i
    obtain ⟨k, hk⟩ := D.even (D.faces.get i) (List.get_mem _ i)
    have := hlen i
    omega
  have hA6 : ∑ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 6), (D.faces.get i).len =
      6 * (univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 6)).card := by
    rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hB8 : ∑ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 8), (D.faces.get i).len =
      8 * (univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 8)).card := by
    rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2, Finset.sum_const, smul_eq_mul, mul_comm]
  -- final charges of the 10⁺-faces
  have hC : ∑ i ∈ univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len),
      (2 * halfCount D (D.faces.get i) + 54) ≤
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len), 7 * (D.faces.get i).len := by
    refine Finset.sum_le_sum fun i hi => ?_
    have h10i := (Finset.mem_filter.1 hi).2
    have hle := halfCount_le_len D (D.faces.get i)
    by_cases he : (D.faces.get i).len = 10
    · have := h10 i he
      omega
    · omega
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum] at hC
  -- the three classes partition the faces
  have hpart : ∀ g : Fin D.faces.length → ℕ, ∑ i, g i =
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 6), g i +
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 8), g i +
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len), g i := by
    intro g
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => (D.faces.get i).len = 6),
      ← Finset.sum_filter_add_sum_filter_not (univ.filter fun i => ¬ (D.faces.get i).len = 6)
        (fun i => (D.faces.get i).len = 8),
      Finset.filter_filter, Finset.filter_filter, add_assoc]
    congr 2
    · refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
      have := hsplit i
      constructor
      · intro h; omega
      · intro h; omega
    · refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
      have := hsplit i
      constructor
      · intro h; omega
      · intro h; omega
  have hcard := hpart (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at hcard
  have hlens := hpart (fun i => (D.faces.get i).len)
  omega

end Thrackle78.Proof
