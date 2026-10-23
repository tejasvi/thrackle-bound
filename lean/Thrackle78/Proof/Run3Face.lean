import Thrackle78.Proof.Run3Sound
import Thrackle78.Proof.Run3Check
import Thrackle78.Proof.Run610Face

/-!
# The run lemma for `4/3` on 10-faces, and `h₁₀ ≤ 6`

In the embedding of a 2-connected triangle-free thrackle (face data without spikes), three consecutive 6-edges of a
10-face run along one 6-face `C`, so the facial walk follows three consecutive edges of `C`; the rest of the walk is a
pattern of the enumeration (`certOf3_ok`), all of which are impossible (with no copy of the three theta graphs).
Hence a 10-face has no three consecutive 6-edges, and at most six 6-edges.
-/

namespace Thrackle78.Proof

open SimpleGraph Finset Thrackle78

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

open Fin.NatCast in
/-- **The run lemma for `4/3`.** A 10-face has no three consecutive 6-edges. -/
theorem no_run_three (D : FaceData G) (hns : D.NoSpike)
    (h66 : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → (∃ i j, c i = d j) → cycleEdges c = cycleEdges d)
    (h68 : ∀ (c : Fin 6 → V) (d : Fin 8 → V), IsCycleMap G c → IsCycleMap G d →
      Disjoint (cycleEdges c) (cycleEdges d))
    (htri : G.CliqueFree 3) (hc4 : ∀ c : Fin 4 → V, IsCycleMap G c → False)
    (h233 : ¬ ofListing (mkE 7 lTH233) ⊑ G) (h234 : ¬ ofListing (mkE 8 lTH234) ⊑ G)
    (h337 : ¬ ofListing (mkE 12 lTH337) ⊑ G)
    (a : Fin D.faces.length) (h10 : (D.faces.get a).len = 10) [NeZero (D.faces.get a).len]
    (p : Fin (D.faces.get a).len) (hrun : ∀ t : ℕ, t < 3 →
      1 ≤ kindCount D (· = 6) (trav (D.faces.get a) (p + (t : Fin (D.faces.get a).len)))) : False := by
  have inj6 : ∀ b : Fin D.faces.length, (D.faces.get b).len = 6 → Function.Injective (D.faces.get b).v :=
    fun b hb => D.short_simple _ (List.get_mem _ b) (by omega)
  have six_of_half : ∀ x, 1 ≤ kindCount D (· = 6) x →
      ∃ b : Fin D.faces.length, (D.faces.get b).len = 6 ∧ x ∈ (D.faces.get b).edges := by
    intro x hx
    unfold kindCount at hx
    obtain ⟨b, hb, hbx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.one_le_iff_ne_zero.1 hx)
    exact ⟨b, (mem_filter.1 hb).2, (count_pos_iff _ x).1 (Nat.one_le_iff_ne_zero.2 hbx)⟩
  have hcov : ∀ x ∈ G.edgeFinset, ∑ i : Fin D.faces.length, (D.faces.get i).count x = 2 := fun x hx =>
    (list_map_sum_eq_fin D.faces (fun F => F.count x)).symm.trans (D.cover x hx)
  have count_le : ∀ b : Fin D.faces.length, (D.faces.get b).len = 6 → ∀ x ∈ (D.faces.get b).edges,
      (D.faces.get a).count x ≤ 1 := by
    intro b hb x hx
    have hab : a ≠ b := fun h => by
      have : (D.faces.get a).len = (D.faces.get b).len := by rw [h]
      omega
    have hpair : (D.faces.get a).count x + (D.faces.get b).count x ≤ ∑ i, (D.faces.get i).count x := by
      have := Finset.sum_le_sum_of_subset (f := fun i => (D.faces.get i).count x) (Finset.subset_univ {a, b})
      rw [Finset.sum_pair hab] at this
      exact this
    have := hcov x (edges_sub _ hx)
    have hb1 := (count_pos_iff _ x).2 hx
    omega
  have count_two : ∀ x, (D.faces.get a).count x ≤ 2 := by
    intro x
    by_cases hx : x ∈ G.edgeFinset
    · have h1 : (D.faces.get a).count x ≤ ∑ i, (D.faces.get i).count x :=
        Finset.single_le_sum (f := fun i => (D.faces.get i).count x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      have := hcov x hx
      omega
    · have : (D.faces.get a).count x = 0 := by
        by_contra hne
        exact hx (edges_sub (D.faces.get a) ((count_pos_iff (D.faces.get a) x).1 (by omega)))
      omega
  have prop : ∀ b : Fin D.faces.length, (D.faces.get b).len = 6 → ∀ i : Fin (D.faces.get a).len,
      trav (D.faces.get a) i ∈ (D.faces.get b).edges → 1 ≤ kindCount D (· = 6) (trav (D.faces.get a) (finRotate (D.faces.get a).len i)) →
      trav (D.faces.get a) (finRotate (D.faces.get a).len i) ∈ (D.faces.get b).edges := by
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
  -- the 6-face of the run, and the run along it
  obtain ⟨b, hb, hbx⟩ := six_of_half _ (hrun 0 (by norm_num))
  have hnext : ∀ t : ℕ, p + ((t + 1 : ℕ) : Fin (D.faces.get a).len) = finRotate (D.faces.get a).len (p + (t : Fin (D.faces.get a).len)) := by
    intro t
    rw [finRotate_apply, Nat.cast_succ, add_assoc]
  have hall : ∀ t : ℕ, t < 3 → trav (D.faces.get a) (p + (t : Fin (D.faces.get a).len)) ∈ (D.faces.get b).edges := by
    intro t
    induction t with
    | zero => intro _; exact hbx
    | succ t ih =>
      intro ht
      rw [hnext]
      exact prop b hb _ (ih (by omega)) (by rw [← hnext]; exact hrun (t + 1) ht)
  -- the walk
  set w : ℕ → V := fun t => (D.faces.get a).v (p + (t : Fin (D.faces.get a).len)) with hwdef
  have htrav : ∀ t : ℕ, trav (D.faces.get a) (p + (t : Fin (D.faces.get a).len)) = s(w t, w (t + 1)) := by
    intro t
    simp only [trav, hwdef]
    rw [hnext t]
  have hadj : ∀ t : ℕ, G.Adj (w t) (w (t + 1)) := by
    intro t
    simp only [hwdef]
    rw [hnext t]
    exact (D.faces.get a).adj _
  have hper : ∀ t : ℕ, w (t % 10) = w t := by
    intro t
    simp only [hwdef]
    congr 2
    apply Fin.ext
    rw [Fin.val_natCast, Fin.val_natCast, h10, Nat.mod_mod]
  have hspike : ∀ t : ℕ, w t ≠ w (t + 2) := by
    intro t
    have := hns (D.faces.get a) (List.get_mem _ a) (p + (t : Fin (D.faces.get a).len))
    simp only [hwdef]
    rwa [show p + ((t + 2 : ℕ) : Fin (D.faces.get a).len) = finRotate (D.faces.get a).len (finRotate (D.faces.get a).len (p + (t : Fin (D.faces.get a).len))) by
      rw [← hnext, ← hnext]]
  -- the 6-cycle `c₀` of the face, rotated (and reflected) to start with `w 0, w 1`
  have hc₀ := toFin_cycleMap (D.faces.get b) hb (by norm_num) (inj6 b hb)
  have hE : cycleEdges (toFin (D.faces.get b) hb) = (D.faces.get b).edges := toFin_edges _ hb
  have hmem : ∀ t : ℕ, t < 3 → s(w t, w (t + 1)) ∈ cycleEdges (toFin (D.faces.get b) hb) := by
    intro t ht
    rw [hE, ← htrav]
    exact hall t ht
  obtain ⟨c, hc, hcE, hc0, hc1⟩ : ∃ c : Fin 6 → V, IsCycleMap G c ∧
      cycleEdges c = cycleEdges (toFin (D.faces.get b) hb) ∧ c 0 = w 0 ∧ c 1 = w 1 := by
    have h01 := hmem 0 (by norm_num)
    simp only [cycleEdges, mem_image, mem_univ, true_and] at h01
    obtain ⟨i, hi⟩ := h01
    rw [finRotate_apply] at hi
    rcases Sym2.eq_iff.1 hi with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · refine ⟨fun j => toFin (D.faces.get b) hb (j + i), cycle_rot hc₀ i,
        cycleEdges_rot _ i, by simp only [zero_add]; exact e0, ?_⟩
      simp only [add_comm (1 : Fin 6)]
      exact e1
    · refine ⟨fun j => toFin (D.faces.get b) hb (i + 1 - j), cycle_refl hc₀ i,
        cycleEdges_refl _ i, by simp only [sub_zero]; exact e1, ?_⟩
      simp only [add_sub_cancel_right]
      exact e0
  have hmem' : ∀ t : ℕ, t < 3 → s(w t, w (t + 1)) ∈ cycleEdges c := fun t ht => hcE ▸ hmem t ht
  -- the walk follows `c` for three steps
  have hc2 : c 2 = w 2 := by
    have := cycle6_next hc 1 (w 2) (by rw [hc1]; exact hmem' 1 (by norm_num))
    rcases this with h | h
    · exact h.symm
    · exact absurd (by rw [h]; exact hc0 : w 2 = w 0).symm (hspike 0)
  have hc3 : c 3 = w 3 := by
    have := cycle6_next hc 2 (w 3) (by rw [hc2]; exact hmem' 2 (by norm_num))
    rcases this with h | h
    · exact h.symm
    · exact absurd (by rw [h]; exact hc1 : w 3 = w 1).symm (hspike 1)
  have hw : ∀ t (ht : t < 4), c ⟨t, by omega⟩ = w t := by
    intro t ht
    interval_cases t
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
  -- counts along the ten steps
  have hlen : ∀ x, ((List.range 10).filter fun u => decide (s(w u, w (u + 1)) = x)).length ≤ (D.faces.get a).count x := by
    intro x
    have hnd : ((List.range 10).filter fun u => decide (s(w u, w (u + 1)) = x)).Nodup :=
      (List.nodup_range).filter _
    rw [← List.toFinset_card_of_nodup hnd]
    unfold CWalk.count
    apply Finset.card_le_card_of_injOn (fun u : ℕ => p + (u : Fin (D.faces.get a).len))
    · intro u hu
      simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at hu
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      rw [← hu.2, ← htrav u]
      rfl
    · intro u hu u' hu' huu
      simp only [List.coe_toFinset, Set.mem_setOf_eq, List.mem_filter, List.mem_range] at hu hu'
      have hv := congrArg Fin.val (add_left_cancel huu)
      rw [Fin.val_natCast, Fin.val_natCast, h10] at hv
      omega
  have hcC : ∀ x ∈ cycleEdges c, ((List.range 10).filter fun u => decide (s(w u, w (u + 1)) = x)).length ≤ 1 := by
    intro x hx
    have := count_le b hb x (by rw [← hE, ← hcE]; exact hx)
    exact (hlen x).trans this
  have hcA : ∀ x, ((List.range 10).filter fun u => decide (s(w u, w (u + 1)) = x)).length ≤ 2 :=
    fun x => (hlen x).trans (count_two x)
  -- the enumeration
  have hv := validB3_xsOf3 hc.2.1 hw
  have hnv := violB3_xsOf3 hc hw hadj hper hspike hcC hcA
  have hok := certOf3_ok ⟨labOf3 w c 4, labOf3_lt hc.2.1 4 (by norm_num)⟩
    ⟨labOf3 w c 5, labOf3_lt hc.2.1 5 (by norm_num)⟩ ⟨labOf3 w c 6, labOf3_lt hc.2.1 6 (by norm_num)⟩
    ⟨labOf3 w c 7, labOf3_lt hc.2.1 7 (by norm_num)⟩ ⟨labOf3 w c 8, labOf3_lt hc.2.1 8 (by norm_num)⟩
    ⟨labOf3 w c 9, labOf3_lt hc.2.1 9 (by norm_num)⟩ hv hnv
  exact cert3_false hc hw hadj hper htri hc4 h66 h68 h233 h234 h337 hok



/-- Ten positions on a circle with at most three marked ones contain three consecutive unmarked ones. -/
lemma window_three : ∀ S ∈ (Finset.range 10).powerset, S.card ≤ 3 → ∃ q < 10, ∀ d < 3, (q + d) % 10 ∉ S := by
  decide +kernel

open Fin.NatCast in
/-- **`h₁₀ ≤ 6`.** A 10-face has at most six 6-edges. -/
theorem ten_face_six (D : FaceData G) (hns : D.NoSpike)
    (h66 : ∀ c d : Fin 6 → V, IsCycleMap G c → IsCycleMap G d → (∃ i j, c i = d j) → cycleEdges c = cycleEdges d)
    (h68 : ∀ (c : Fin 6 → V) (d : Fin 8 → V), IsCycleMap G c → IsCycleMap G d →
      Disjoint (cycleEdges c) (cycleEdges d))
    (htri : G.CliqueFree 3) (hc4 : ∀ c : Fin 4 → V, IsCycleMap G c → False)
    (h233 : ¬ ofListing (mkE 7 lTH233) ⊑ G) (h234 : ¬ ofListing (mkE 8 lTH234) ⊑ G)
    (h337 : ¬ ofListing (mkE 12 lTH337) ⊑ G)
    (a : Fin D.faces.length) (h10 : (D.faces.get a).len = 10) : halfCount D (D.faces.get a) ≤ 6 := by
  have : NeZero (D.faces.get a).len := ⟨(D.faces.get a).pos.ne'⟩
  by_contra hgt
  push Not at hgt
  -- at most three traversals are not 6-edges
  have hT : (univ.filter fun i : Fin (D.faces.get a).len =>
      ¬ 1 ≤ kindCount D (· = 6) (trav (D.faces.get a) i)).card ≤ 3 := by
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (D.faces.get a).len)))
      (fun i => 1 ≤ kindCount D (· = 6) (trav (D.faces.get a) i))
    rw [card_univ, Fintype.card_fin] at this
    unfold halfCount at hgt
    omega
  set T := univ.filter fun i : Fin (D.faces.get a).len => ¬ 1 ≤ kindCount D (· = 6) (trav (D.faces.get a) i)
  have hTv : T.image (fun i => i.val) ∈ (Finset.range 10).powerset := by
    rw [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Finset.mem_range]
    have := i.isLt
    omega
  obtain ⟨q, hq, hwin⟩ := window_three _ hTv ((Finset.card_image_le).trans hT)
  refine no_run_three D hns h66 h68 htri hc4 h233 h234 h337 a h10 (q : Fin (D.faces.get a).len) fun t ht => ?_
  by_contra hnot
  have hmem : ((q : Fin (D.faces.get a).len) + (t : Fin (D.faces.get a).len)) ∈ T :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hnot⟩
  apply hwin t ht
  rw [Finset.mem_image]
  refine ⟨_, hmem, ?_⟩
  show ((q : Fin (D.faces.get a).len) + (t : Fin (D.faces.get a).len)).val = (q + t) % 10
  rw [Fin.val_add, Fin.val_natCast, Fin.val_natCast, h10]
  omega

end Thrackle78.Proof
