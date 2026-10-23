import Thrackle78.Proof.Discharge2720

/-!
# The discharging count for `4/3`

Charges `len - 8`; every 6-edge carries `1/3`: a 6-face has six 6-edges, a 10-face at most six (`h10`), a face of
length `d ≥ 12` at most `d`. All final charges are nonnegative, so `8 f ≤ 2 m`, i.e. `4 f ≤ m`.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Discharging for `4/3`.** -/
theorem discharge43 (D : FaceData G) (hlen : ∀ i : Fin D.faces.length, 6 ≤ (D.faces.get i).len)
    (hAC : ∀ x ∈ G.edgeFinset, kindCount D (· = 6) x ≤ kindCount D (10 ≤ ·) x)
    (h10 : ∀ i : Fin D.faces.length, (D.faces.get i).len = 10 → halfCount D (D.faces.get i) ≤ 6) :
    4 * D.faces.length ≤ G.edgeFinset.card := by
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
      (halfCount D (D.faces.get i) + 24) ≤
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len), 3 * (D.faces.get i).len := by
    refine Finset.sum_le_sum fun i hi => ?_
    have h10i := (Finset.mem_filter.1 hi).2
    have hle := halfCount_le_len D (D.faces.get i)
    obtain ⟨k, hk⟩ := D.even (D.faces.get i) (List.get_mem _ i)
    by_cases he : (D.faces.get i).len = 10
    · have := h10 i he
      omega
    · omega
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hC
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
