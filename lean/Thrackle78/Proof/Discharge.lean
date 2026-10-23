import Thrackle78.Hyp

/-!
# The discharging count

For face data in which every face has even length at least `6`, and every edge lies on at least as many sides of faces
of length `≥ 10` as of 6-faces (rule: every `10⁺`-face sends `1/11` through each edge it shares with a 6-face), the
face lengths satisfy `∑ (4 len - 30) ≥ 0`, i.e. `15 f ≤ 4 m`; with Euler's `m + k ≤ n + f` this gives
`11 m ≤ 15 (n - k)`.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

lemma list_map_sum_eq_fin {α : Type*} (L : List α) (g : α → ℕ) :
    (L.map g).sum = ∑ i : Fin L.length, g (L.get i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have e : ∑ i : Fin (a :: L).length, g ((a :: L).get i) = ∑ i : Fin (L.length + 1), g ((a :: L).get i) := rfl
    rw [List.map_cons, List.sum_cons, ih, e, Fin.sum_univ_succ]
    simp

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma cwalk_edge_mem (W : CWalk G) (i : Fin W.len) : s(W.v i, W.v (finRotate W.len i)) ∈ G.edgeFinset := by
  rw [mem_edgeFinset]; exact W.adj i

/-- The traversal counts of a closed walk add up to its length. -/
lemma cwalk_sum_count (W : CWalk G) : ∑ x ∈ G.edgeFinset, W.count x = W.len := by
  unfold CWalk.count
  rw [← Finset.card_eq_sum_card_fiberwise (fun i _ => cwalk_edge_mem W i)]
  simp

/-- The number of faces of a given kind, weighted by the traversals of `x`. -/
def kindCount (D : FaceData G) (p : ℕ → Prop) [DecidablePred p] (x : Sym2 V) : ℕ :=
  ∑ i ∈ univ.filter (fun i : Fin D.faces.length => p (D.faces.get i).len), (D.faces.get i).count x

lemma sum_kindCount (D : FaceData G) (p : ℕ → Prop) [DecidablePred p] :
    ∑ x ∈ G.edgeFinset, kindCount D p x =
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => p (D.faces.get i).len), (D.faces.get i).len := by
  unfold kindCount
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => cwalk_sum_count _

/-- **Discharging.** -/
theorem discharge (D : FaceData G) (hlen : ∀ i : Fin D.faces.length, 6 ≤ (D.faces.get i).len)
    (hAC : ∀ x ∈ G.edgeFinset, kindCount D (· = 6) x ≤ kindCount D (10 ≤ ·) x) :
    15 * D.faces.length ≤ 4 * G.edgeFinset.card := by
  -- the lengths add up to 2m
  have hsum : ∑ i : Fin D.faces.length, (D.faces.get i).len = 2 * G.edgeFinset.card := by
    have h1 : ∑ i : Fin D.faces.length, (D.faces.get i).len =
        ∑ x ∈ G.edgeFinset, ∑ i : Fin D.faces.length, (D.faces.get i).count x := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => (cwalk_sum_count _).symm
    rw [h1, Finset.sum_congr rfl fun x hx => (list_map_sum_eq_fin D.faces (fun F => F.count x)).symm.trans
      (D.cover x hx), Finset.sum_const, smul_eq_mul, mul_comm]
  -- 6-faces against 10⁺-faces
  have h6 : ∑ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 6), (D.faces.get i).len ≤
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len), (D.faces.get i).len := by
    rw [← sum_kindCount D (· = 6), ← sum_kindCount D (10 ≤ ·)]
    exact Finset.sum_le_sum hAC
  -- every face has length 6, 8 or ≥ 10
  have hsplit : ∀ i : Fin D.faces.length, (D.faces.get i).len = 6 ∨ (D.faces.get i).len = 8 ∨
      10 ≤ (D.faces.get i).len := by
    intro i
    obtain ⟨k, hk⟩ := D.even (D.faces.get i) (List.get_mem _ i)
    have := hlen i
    omega
  have hA : ∑ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 6), (D.faces.get i).len =
      6 * (univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 6)).card := by
    rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hB : ∑ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 8), (D.faces.get i).len =
      8 * (univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 8)).card := by
    rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hC : 10 * (univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len)).card ≤
      ∑ i ∈ univ.filter (fun i : Fin D.faces.length => 10 ≤ (D.faces.get i).len), (D.faces.get i).len := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i hi => (Finset.mem_filter.1 hi).2
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

/-- **Euler and discharging.** With Euler's inequality `m + k ≤ n + f`: `11 m ≤ 15 (n - k)`. -/
theorem euler_bound (D : FaceData G) (k : ℕ) (heul : G.edgeFinset.card + k ≤ Fintype.card V + D.faces.length)
    (hlen : ∀ i : Fin D.faces.length, 6 ≤ (D.faces.get i).len)
    (hAC : ∀ x ∈ G.edgeFinset, kindCount D (· = 6) x ≤ kindCount D (10 ≤ ·) x) :
    11 * G.edgeFinset.card + 15 * k ≤ 15 * Fintype.card V := by
  have := discharge D hlen hAC
  omega

end Thrackle78.Proof
