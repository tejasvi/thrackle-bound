import Thrackle78.Proof.Faces
import Thrackle78.Proof.Discharge2720

/-!
# The 10-face lemma and the `27/20` bound for 2-connected triangle-free thrackles

Given that two 6-cycles with a common vertex have the same edges (the 6-6 lemma): two consecutive 6-edges of a face
border 6-faces through a common vertex, hence with the same edges, and a 6-face borders a 10-face along at most six
traversals (each edge has two sides). So a 10-face with nine 6-edges would contain seven consecutive ones bordering one
6-face, which is impossible: a 10-face has at most eight 6-edges. With the discharging,
`20 m ≤ 27 (n - 1)`, and `20 m ≤ 27 (n - 2)` if bipartite, except for `G = C6` in the bipartite bound.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Both ends of an edge of a closed walk are vertices of the walk. -/
lemma mem_edges_ends (W : CWalk G) {a b : V} (h : s(a, b) ∈ W.edges) : (∃ k, W.v k = a) ∧ (∃ k, W.v k = b) := by
  rw [mem_edges_iff] at h
  obtain ⟨k, hk⟩ := h
  rcases Sym2.eq_iff.1 hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨k, h1⟩, ⟨_, h2⟩⟩
  · exact ⟨⟨_, h2⟩, ⟨k, h1⟩⟩

/-- The edges of a closed walk are edges of the graph. -/
lemma edges_sub (W : CWalk G) {x : Sym2 V} (h : x ∈ W.edges) : x ∈ G.edgeFinset := by
  rw [mem_edges_iff] at h
  obtain ⟨k, rfl⟩ := h
  exact cwalk_edge_mem W k

omit [Fintype V] in
/-- Two cycle maps with a common edge have a common vertex. -/
lemma common_vertex_cyc {k l : ℕ} (c : Fin k → V) (d : Fin l → V) (x : Sym2 V) (hxc : x ∈ cycleEdges c)
    (hxd : x ∈ cycleEdges d) : ∃ i j, c i = d j := by
  simp only [cycleEdges, mem_image, mem_univ, true_and] at hxc hxd
  obtain ⟨i, rfl⟩ := hxc
  obtain ⟨j, hj⟩ := hxd
  rcases Sym2.eq_iff.1 hj with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ⟨i, j, h1.symm⟩
  · exact ⟨finRotate k i, j, h1.symm⟩

variable (Thr : ∀ {V : Type} [Fintype V] [DecidableEq V], SimpleGraph V → Prop)

open Fin.NatCast in
/-- **The 10-face lemma.** A face of length 10 has at most eight 6-edges. -/
theorem ten_face (D : FaceData G)
    (h66 : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → (∃ i j, c i = d j) → cycleEdges c = cycleEdges d)
    (a : Fin D.faces.length) (h10 : (D.faces.get a).len = 10) : halfCount D (D.faces.get a) ≤ 8 := by
  set W := D.faces.get a with hW
  have : NeZero W.len := ⟨W.pos.ne'⟩
  have inj6 : ∀ b : Fin D.faces.length, (D.faces.get b).len = 6 → Function.Injective (D.faces.get b).v :=
    fun b hb => D.short_simple _ (List.get_mem _ b) (by omega)
  -- a 6-face through every 6-edge
  have six_of_half : ∀ x, 1 ≤ kindCount D (· = 6) x →
      ∃ b : Fin D.faces.length, (D.faces.get b).len = 6 ∧ x ∈ (D.faces.get b).edges := by
    intro x hx
    unfold kindCount at hx
    obtain ⟨b, hb, hbx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.one_le_iff_ne_zero.1 hx)
    exact ⟨b, (mem_filter.1 hb).2, (count_pos_iff _ x).1 (Nat.one_le_iff_ne_zero.2 hbx)⟩
  -- `W` traverses an edge of a 6-face at most once
  have count_le : ∀ b : Fin D.faces.length, (D.faces.get b).len = 6 → ∀ x ∈ (D.faces.get b).edges,
      W.count x ≤ 1 := by
    intro b hb x hx
    have hab : a ≠ b := fun h => by
      have : W.len = (D.faces.get b).len := by rw [hW, h]
      omega
    have hcov : ∑ i : Fin D.faces.length, (D.faces.get i).count x = 2 :=
      (list_map_sum_eq_fin D.faces (fun F => F.count x)).symm.trans (D.cover x (edges_sub _ hx))
    have hpair : W.count x + (D.faces.get b).count x ≤ ∑ i, (D.faces.get i).count x := by
      have := Finset.sum_le_sum_of_subset (f := fun i => (D.faces.get i).count x) (Finset.subset_univ {a, b})
      rw [Finset.sum_pair hab] at this
      exact this
    have hb1 := (count_pos_iff _ x).2 hx
    omega
  -- consecutive 6-edges border 6-faces with the same edges
  have prop : ∀ b : Fin D.faces.length, (D.faces.get b).len = 6 → ∀ i : Fin W.len,
      trav W i ∈ (D.faces.get b).edges → 1 ≤ kindCount D (· = 6) (trav W (finRotate W.len i)) →
      trav W (finRotate W.len i) ∈ (D.faces.get b).edges := by
    intro b hb i hi hhalf
    obtain ⟨b', hb', hx'⟩ := six_of_half _ hhalf
    obtain ⟨-, ⟨k, hk⟩⟩ := mem_edges_ends _ hi
    obtain ⟨⟨k', hk'⟩, -⟩ := mem_edges_ends _ hx'
    have hc := toFin_cycleMap _ hb (by norm_num) (inj6 b hb)
    have hc' := toFin_cycleMap _ hb' (by norm_num) (inj6 b' hb')
    have heq := h66 _ _ hc hc' ⟨Fin.cast hb k, Fin.cast hb' k', by
      simp only [toFin_apply, Fin.cast_cast, Fin.cast_eq_self]; rw [hk, hk']⟩
    rw [toFin_edges, toFin_edges] at heq
    rw [heq]
    exact hx'
  by_contra hgt
  push Not at hgt
  -- at most one traversal is not a 6-edge
  have hS : (univ.filter fun i : Fin W.len => ¬ 1 ≤ kindCount D (· = 6) (trav W i)).card ≤ 1 := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin W.len)))
      (fun i => 1 ≤ kindCount D (· = 6) (trav W i))
    rw [card_univ, Fintype.card_fin] at this
    unfold halfCount at hgt
    omega
  -- seven consecutive 6-edges
  obtain ⟨p, hp⟩ : ∃ p : Fin W.len, ∀ t : ℕ, t < 7 → 1 ≤ kindCount D (· = 6) (trav W (p + (t : Fin W.len))) := by
    by_cases hq : ∃ q : Fin W.len, ¬ 1 ≤ kindCount D (· = 6) (trav W q)
    · obtain ⟨q, hq⟩ := hq
      refine ⟨q + 1, fun t ht => ?_⟩
      by_contra hn
      have heq : q + 1 + (t : Fin W.len) = q :=
        Finset.card_le_one.1 hS _ (by simpa using hn) _ (by simpa using hq)
      rw [add_assoc, add_eq_left, ← Nat.cast_one, ← Nat.cast_add, Fin.natCast_eq_zero, h10] at heq
      omega
    · push Not at hq
      exact ⟨0, fun t _ => hq _⟩
  -- they all border one 6-face
  obtain ⟨b, hb, hbx⟩ := six_of_half _ (hp 0 (by norm_num))
  have hrun : ∀ t : ℕ, t < 7 → trav W (p + (t : Fin W.len)) ∈ (D.faces.get b).edges := by
    intro t
    induction t with
    | zero => intro _; exact hbx
    | succ t ih =>
      intro ht
      have hnext : p + ((t + 1 : ℕ) : Fin W.len) = finRotate W.len (p + (t : Fin W.len)) := by
        rw [finRotate_apply, Nat.cast_succ, add_assoc]
      rw [hnext]
      exact prop b hb _ (ih (by omega)) (by rw [← hnext]; exact hp (t + 1) ht)
  -- counting the traversals along the 6-face
  have hcard7 : 7 ≤ (univ.filter fun i : Fin W.len => trav W i ∈ (D.faces.get b).edges).card := by
    have hsub : (range 7).image (fun t : ℕ => p + (t : Fin W.len)) ⊆
        univ.filter fun i : Fin W.len => trav W i ∈ (D.faces.get b).edges := by
      intro i hi
      simp only [mem_image, mem_range] at hi
      obtain ⟨t, ht, rfl⟩ := hi
      exact mem_filter.2 ⟨mem_univ _, hrun t ht⟩
    have hinj : Set.InjOn (fun t : ℕ => p + (t : Fin W.len)) (range 7) := by
      intro t ht t' ht' h
      simp only [coe_range, Set.mem_Iio] at ht ht'
      have hv := congrArg Fin.val (add_left_cancel h)
      rw [Fin.val_natCast, Fin.val_natCast, h10] at hv
      omega
    calc 7 = ((range 7).image fun t : ℕ => p + (t : Fin W.len)).card := by
          rw [card_image_of_injOn hinj, card_range]
      _ ≤ _ := card_le_card hsub
  have hcard6 : (univ.filter fun i : Fin W.len => trav W i ∈ (D.faces.get b).edges).card ≤ 6 := by
    have h1 : (univ.filter fun i : Fin W.len => trav W i ∈ (D.faces.get b).edges).card ≤
        (D.faces.get b).edges.card := by
      apply Finset.card_le_card_of_injOn (trav W)
      · intro i hi
        exact (mem_filter.1 hi).2
      · intro i hi j hj hij
        by_contra hne
        have hx := (mem_filter.1 hi).2
        have hle := count_le b hb _ hx
        have h2 : 2 ≤ W.count (trav W i) := by
          unfold CWalk.count
          exact Finset.one_lt_card.2 ⟨i, mem_filter.2 ⟨mem_univ _, rfl⟩, j, mem_filter.2 ⟨mem_univ _, hij.symm⟩,
            hne⟩
        omega
    rw [card_edges_of_injective _ (inj6 b hb) (by omega), hb] at h1
    exact h1
  omega

/-- **2-connected bound for `27/20`.** For a 2-connected triangle-free thrackle in which two 6-cycles with a common
vertex have the same edges and no 6-cycle shares an edge with an 8-cycle: `20 m + 27 ≤ 27 n`; if bipartite,
`20 m + 54 ≤ 27 n` unless `m = n = 6`. -/
theorem twoConn_bound2720 (ax : ThrackleAxioms Thr) (hT : Thr G) (h2 : TwoConn G) (htri : G.CliqueFree 3)
    (h66 : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → (∃ i j, c i = d j) → cycleEdges c = cycleEdges d)
    (h68 : ∀ (c : Fin 6 → V) (d : Fin 8 → V), IsCycleMap G c → IsCycleMap G d →
      Disjoint (cycleEdges c) (cycleEdges d)) :
    20 * G.edgeFinset.card + 27 ≤ 27 * Fintype.card V ∧
      (G.Colorable 2 → 20 * G.edgeFinset.card + 54 ≤ 27 * Fintype.card V ∨
        (G.edgeFinset.card = 6 ∧ Fintype.card V = 6)) := by
  have h66e : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → ∀ x, x ∈ cycleEdges c → x ∈ cycleEdges d →
      cycleEdges c = cycleEdges d :=
    fun c d hc hd x hxc hxd => h66 c d hc hd (common_vertex_cyc c d x hxc hxd)
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
    obtain ⟨k, hk⟩ := D.even _ (List.get_mem _ i)
    refine ⟨by omega, fun _ => ?_⟩
    by_cases h8 : 8 ≤ (D.faces.get i).len
    · left; omega
    · by_cases h7 : 7 ≤ Fintype.card V
      · left; omega
      · right; omega
  · push Not at hcase
    have hAC := rule_applies Thr ax hT D h66e h68 fun i j hij hi hj => hcase i j hij hi hj
    have hd := discharge2720 D hlen hAC fun a ha => ten_face D h66 a ha
    have e1 := D.euler
    refine ⟨by omega, fun hbip => Or.inl ?_⟩
    have e2 := D.euler_bip hbip
    omega

end Thrackle78.Proof
