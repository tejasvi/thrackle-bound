import Thrackle78.Proof.Discharge
import Thrackle78.Proof.Basic

/-!
# Faces of a 2-connected triangle-free thrackle

From `FaceData` and the axioms: no face has length `4` (`C4`), so all faces have length `≥ 6`; the 6-faces are 6-cycles,
pairwise edge-disjoint unless `G` is a single cycle (the 6-6 edge lemma and `distinct`); a 6-face and an 8-face share
no edge (the 6-8 overlap lemma). Both lemmas are inputs here. Hence the discharging rule applies, and
`11 m ≤ 15 (n - 1)` (`11 m ≤ 15 (n - 2)` if bipartite), except for `G = C6` in the bipartite bound.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Closed walks of length `k` as maps on `Fin k` -/

/-- A closed walk of length `k` as a map on `Fin k`. -/
def toFin (W : CWalk G) {k : ℕ} (h : W.len = k) : Fin k → V := fun i => W.v (Fin.cast h.symm i)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma toFin_cycleMap (W : CWalk G) {k : ℕ} (h : W.len = k) (hk : 3 ≤ k) (hinj : Function.Injective W.v) :
    IsCycleMap G (toFin W h) := by
  obtain ⟨len, pos, v, adj⟩ := W
  simp only at h
  subst h
  refine ⟨hk, fun a b hab => hinj ?_, fun i => ?_⟩
  · simpa only [toFin, Fin.cast_eq_self] using hab
  · simpa only [toFin, Fin.cast_eq_self] using adj i

omit [Fintype V] [DecidableRel G.Adj] in
lemma toFin_edges (W : CWalk G) {k : ℕ} (h : W.len = k) : cycleEdges (toFin W h) = W.edges := by
  obtain ⟨len, pos, v, adj⟩ := W
  simp only at h
  subst h
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma toFin_apply (W : CWalk G) {k : ℕ} (h : W.len = k) (i : Fin k) : toFin W h i = W.v (Fin.cast h.symm i) := rfl

omit [Fintype V] [DecidableRel G.Adj] in
lemma mem_edges_iff (W : CWalk G) (x : Sym2 V) :
    x ∈ W.edges ↔ ∃ i, s(W.v i, W.v (finRotate W.len i)) = x := by
  simp [CWalk.edges]

omit [Fintype V] [DecidableRel G.Adj] in
lemma count_pos_iff (W : CWalk G) (x : Sym2 V) : 1 ≤ W.count x ↔ x ∈ W.edges := by
  rw [mem_edges_iff, CWalk.count, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

omit [Fintype V] [DecidableRel G.Adj] in
/-- An injective closed walk of length `≥ 3` traverses every edge at most once. -/
lemma count_le_one (W : CWalk G) (hinj : Function.Injective W.v) (h3 : 3 ≤ W.len) (x : Sym2 V) :
    W.count x ≤ 1 := by
  unfold CWalk.count
  rw [Finset.card_le_one]
  intro i hi j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  rw [← hj] at hi
  rcases Sym2.eq_iff.1 hi with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hinj h1
  · have e1 := hinj h1
    have e2 := hinj h2
    exact absurd (by rw [← e1, e2] : finRotate W.len (finRotate W.len j) = j) (finRotate_twice_ne h3 j)

omit [Fintype V] [DecidableRel G.Adj] in
lemma card_edges_of_injective (W : CWalk G) (hinj : Function.Injective W.v) (h3 : 3 ≤ W.len) :
    W.edges.card = W.len := by
  unfold CWalk.edges
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro i j h
  simp only at h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact hinj h1
  · have e1 := hinj h1
    have e2 := hinj h2
    exact absurd (by rw [← e1, e2] : finRotate W.len (finRotate W.len j) = j) (finRotate_twice_ne h3 j)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Two closed walks traversing a common edge have a common vertex. -/
lemma common_vertex (W W' : CWalk G) {x : Sym2 V} (hx : x ∈ W.edges) (hx' : x ∈ W'.edges) :
    ∃ i j, W.v i = W'.v j := by
  rw [mem_edges_iff] at hx hx'
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, hj⟩ := hx'
  rcases Sym2.eq_iff.1 hj with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact ⟨i, j, h1.symm⟩
  · exact ⟨i, finRotate W'.len j, h2.symm⟩

/-! ## Faces -/

variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

omit [DecidableRel G.Adj] in
/-- `C4` is not contained in a thrackle. -/
lemma no_C4 (ax : ThrackleAxioms Thr) (hT : Thr G) (c : Fin 4 → V) (hc : IsCycleMap G c) : False := by
  have hadj : ∀ u v : Fin 4, (cycleGraph 4).Adj u v → v = finRotate 4 u ∨ u = finRotate 4 v := by decide
  have hcopy : cycleGraph 4 ⊑ G := ⟨⟨⟨c, fun {u v} huv => by
    rcases hadj u v huv with rfl | rfl
    · exact hc.2.2 u
    · exact (hc.2.2 v).symm⟩, hc.2.1⟩⟩
  exact ax.c4 (ax.sub _ _ hcopy hT)

/-- Every face has length at least `6`. -/
lemma face_len_ge_six (ax : ThrackleAxioms Thr) (hT : Thr G) (D : FaceData G) (i : Fin D.faces.length) :
    6 ≤ (D.faces.get i).len := by
  have h3 := D.three_le _ (List.get_mem _ i)
  obtain ⟨k, hk⟩ := D.even _ (List.get_mem _ i)
  by_contra hlt
  have h4 : (D.faces.get i).len = 4 := by omega
  exact no_C4 Thr ax hT (toFin _ h4) (toFin_cycleMap _ h4 (by norm_num) (D.short_simple _ (List.get_mem _ i) (by omega)))

lemma sum_le_one_of {ι : Type*} (s : Finset ι) (f : ι → ℕ) (h1 : ∀ i ∈ s, f i ≤ 1)
    (hu : ∀ i ∈ s, ∀ j ∈ s, 1 ≤ f i → 1 ≤ f j → i = j) : ∑ i ∈ s, f i ≤ 1 := by
  by_cases h : ∃ i ∈ s, 1 ≤ f i
  · obtain ⟨i, hi, hfi⟩ := h
    rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => by
      by_contra hne
      exact hji (hu j hj i hi (by omega) hfi)]
    exact h1 i hi
  · push Not at h
    rw [Finset.sum_eq_zero fun i hi => by have := h i hi; omega]
    norm_num

/-- **The discharging rule applies.** -/
lemma rule_applies (ax : ThrackleAxioms Thr) (hT : Thr G) (D : FaceData G)
    (h66 : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → ∀ x, x ∈ cycleEdges c → x ∈ cycleEdges d →
      cycleEdges c = cycleEdges d)
    (h68 : ∀ (c : Fin 6 → V) (d : Fin 8 → V), IsCycleMap G c → IsCycleMap G d → Disjoint (cycleEdges c) (cycleEdges d))
    (hB : ∀ i j : Fin D.faces.length, i ≠ j → Function.Injective (D.faces.get i).v →
      Function.Injective (D.faces.get j).v → (D.faces.get i).edges ≠ (D.faces.get j).edges) :
    ∀ x ∈ G.edgeFinset, kindCount D (· = 6) x ≤ kindCount D (10 ≤ ·) x := by
  intro x hx
  have hlen := face_len_ge_six Thr ax hT D
  have inj : ∀ i : Fin D.faces.length, (D.faces.get i).len ≤ 8 → Function.Injective (D.faces.get i).v :=
    fun i h => D.short_simple _ (List.get_mem _ i) h
  have hsplit : ∀ i : Fin D.faces.length, (D.faces.get i).len = 6 ∨ (D.faces.get i).len = 8 ∨
      10 ≤ (D.faces.get i).len := by
    intro i
    obtain ⟨k, hk⟩ := D.even (D.faces.get i) (List.get_mem _ i)
    have := hlen i
    omega
  -- the counts of `x` on the faces add up to 2
  have hcov : ∑ i : Fin D.faces.length, (D.faces.get i).count x = 2 :=
    (list_map_sum_eq_fin D.faces (fun F => F.count x)).symm.trans (D.cover x hx)
  have hpart : ∑ i : Fin D.faces.length, (D.faces.get i).count x =
      kindCount D (· = 6) x + kindCount D (· = 8) x + kindCount D (10 ≤ ·) x := by
    unfold kindCount
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
  -- at most one 6-face traverses `x`, at most once
  have hA : kindCount D (· = 6) x ≤ 1 := by
    apply sum_le_one_of
    · intro i hi
      have h6 := (Finset.mem_filter.1 hi).2
      exact count_le_one _ (inj i (by omega)) (by omega) x
    · intro i hi j hj hci hcj
      have h6i := (Finset.mem_filter.1 hi).2
      have h6j := (Finset.mem_filter.1 hj).2
      by_contra hij
      have hci' := toFin_cycleMap _ h6i (by norm_num) (inj i (by omega))
      have hcj' := toFin_cycleMap _ h6j (by norm_num) (inj j (by omega))
      have hex := h66 _ _ hci' hcj' x (by rw [toFin_edges]; exact (count_pos_iff _ x).1 hci)
        (by rw [toFin_edges]; exact (count_pos_iff _ x).1 hcj)
      rw [toFin_edges, toFin_edges] at hex
      exact hB i j hij (inj i (by omega)) (inj j (by omega)) hex
  -- a 6-face and an 8-face do not share `x`
  have hAB : 1 ≤ kindCount D (· = 6) x → kindCount D (· = 8) x = 0 := by
    intro h6
    obtain ⟨i, hi, hci⟩ : ∃ i ∈ univ.filter (fun i : Fin D.faces.length => (D.faces.get i).len = 6),
        1 ≤ (D.faces.get i).count x := by
      by_contra hne
      push Not at hne
      have : kindCount D (· = 6) x = 0 := Finset.sum_eq_zero fun i hi => by have := hne i hi; omega
      omega
    apply Finset.sum_eq_zero
    intro j hj
    have h6i := (Finset.mem_filter.1 hi).2
    have h8j := (Finset.mem_filter.1 hj).2
    by_contra hcj
    have hci' := toFin_cycleMap _ h6i (by norm_num) (inj i (by omega))
    have hcj' := toFin_cycleMap _ h8j (by norm_num) (inj j (by omega))
    have hd := h68 _ _ hci' hcj'
    rw [toFin_edges, toFin_edges] at hd
    exact Finset.disjoint_left.1 hd ((count_pos_iff _ x).1 hci) ((count_pos_iff _ x).1 (by omega))
  omega

/-- **2-connected bound.** For a 2-connected triangle-free thrackle without a 6-cycle and an 8-cycle sharing an edge:
`11 m ≤ 15 (n - 1)`; if bipartite, `11 m ≤ 15 (n - 2) + 6`, and `11 m ≤ 15 (n - 2) + 2` unless `m = n = 6`. -/
theorem twoConn_bound (ax : ThrackleAxioms Thr) (hT : Thr G) (h2 : TwoConn G) (htri : G.CliqueFree 3)
    (h66 : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → ∀ x, x ∈ cycleEdges c → x ∈ cycleEdges d →
      cycleEdges c = cycleEdges d)
    (h68 : ∀ (c : Fin 6 → V) (d : Fin 8 → V), IsCycleMap G c → IsCycleMap G d →
      Disjoint (cycleEdges c) (cycleEdges d)) :
    11 * G.edgeFinset.card + 15 ≤ 15 * Fintype.card V ∧
      (G.Colorable 2 → 11 * G.edgeFinset.card + 30 ≤ 15 * Fintype.card V + 6 ∧
        (11 * G.edgeFinset.card + 30 ≤ 15 * Fintype.card V + 2 ∨
          (G.edgeFinset.card = 6 ∧ Fintype.card V = 6))) := by
  obtain ⟨D⟩ := ax.faces G hT h2 htri
  have hlen := face_len_ge_six Thr ax hT D
  by_cases hcase : ∃ i j : Fin D.faces.length, i ≠ j ∧ Function.Injective (D.faces.get i).v ∧
      Function.Injective (D.faces.get j).v ∧ (D.faces.get i).edges = (D.faces.get j).edges
  · -- `G` is a single cycle: `m = len ≤ n`
    obtain ⟨i, j, hij, hi, hj, he⟩ := hcase
    have hE := D.distinct i j hij hi hj he
    have hm : G.edgeFinset.card = (D.faces.get i).len := by
      rw [hE, card_edges_of_injective _ hi (by have := hlen i; omega)]
    have hn : (D.faces.get i).len ≤ Fintype.card V := by
      simpa using Fintype.card_le_of_injective _ hi
    have h6 := hlen i
    refine ⟨by omega, fun _ => ⟨by omega, ?_⟩⟩
    by_cases h7 : 7 ≤ Fintype.card V
    · left; omega
    · right; omega
  · push Not at hcase
    have hAC := rule_applies Thr ax hT D h66 h68 fun i j hij hi hj => hcase i j hij hi hj
    have b1 := euler_bound D 1 D.euler hlen hAC
    refine ⟨by omega, fun hbip => ?_⟩
    have b2 := euler_bound D 2 (D.euler_bip hbip) hlen hAC
    exact ⟨by omega, Or.inl (by omega)⟩

end Thrackle78.Proof
