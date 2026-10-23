import Thrackle78.NoSpike

/-!
# Probes of the statements

* `faces` is satisfiable as stated: `C6` (plane: two facial 6-cycles) and `C5` (projective: one facial walk of length
  `10`) carry `FaceData`.
* `CombThr` is not vacuous: a single edge is combinatorially thrackleable, so the computational hypotheses
  `¬ CombThr …` are not true for trivial reasons.
* The listings `lV4`, `lV5`, `lV7` (as run, written by src/prep.py) have the same edges as the graph files
  graphs/u66v_4, u66v_5, u66v_7 of the computations of the 6-6 lemma.
* `NoSpikeFaces` is not vacuous: the face data of `C6` and of `C5` have no spikes.
-/

namespace Thrackle78.Probe

open SimpleGraph Thrackle78

/-! ## `FaceData` for `C6` and `C5` -/

/-- The 6-cycle as a closed walk. -/
def w6 : CWalk (cycleGraph 6) where
  len := 6
  pos := by norm_num
  v := id
  adj := by decide

lemma w6_count : ∀ x ∈ (cycleGraph 6).edgeFinset, w6.count x = 1 := by decide +kernel

lemma w6_edges : (cycleGraph 6).edgeFinset = w6.edges := by decide +kernel

lemma c6_card : (cycleGraph 6).edgeFinset.card = 6 := by decide +kernel

/-- **Probe.** `C6` has plane face data: two faces bounded by the 6-cycle. -/
def faceC6 : FaceData (cycleGraph 6) where
  faces := [w6, w6]
  cover := fun x hx => by simp [w6_count x hx]
  euler := by rw [c6_card]; simp
  even := fun F hF => by simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hF; subst hF; decide
  three_le := fun F hF => by simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hF; subst hF; decide
  short_simple := fun F hF _ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hF; subst hF; exact Function.injective_id
  euler_bip := fun _ => by rw [c6_card]; simp
  distinct := fun i j _ _ _ _ => by
    have : ∀ k : Fin [w6, w6].length, [w6, w6].get k = w6 := fun k => by fin_cases k <;> rfl
    rw [this i]; exact w6_edges

/-- The 5-cycle traversed twice, as a closed walk of length `10`. -/
def w10 : CWalk (cycleGraph 5) where
  len := 10
  pos := by norm_num
  v := fun i => ⟨i.val % 5, Nat.mod_lt _ (by norm_num)⟩
  adj := by decide

lemma w10_count : ∀ x ∈ (cycleGraph 5).edgeFinset, w10.count x = 2 := by decide +kernel

lemma c5_card : (cycleGraph 5).edgeFinset.card = 5 := by decide +kernel

lemma c5_not_bip : ¬ (cycleGraph 5).Colorable 2 := by
  rintro ⟨c⟩
  have h : ∀ i : Fin 5, c i ≠ c (finRotate 5 i) := fun i => c.valid (by revert i; decide)
  have h01 := h 0; have h12 := h 1; have h23 := h 2; have h34 := h 3; have h40 := h 4
  simp only [show finRotate 5 0 = 1 by decide, show finRotate 5 1 = 2 by decide, show finRotate 5 2 = 3 by decide,
    show finRotate 5 3 = 4 by decide, show finRotate 5 4 = 0 by decide] at h01 h12 h23 h34 h40
  have v01 := Fin.val_injective.ne h01; have v12 := Fin.val_injective.ne h12
  have v23 := Fin.val_injective.ne h23; have v34 := Fin.val_injective.ne h34
  have v40 := Fin.val_injective.ne h40
  have b0 := (c 0).isLt; have b1 := (c 1).isLt; have b2 := (c 2).isLt; have b3 := (c 3).isLt
  have b4 := (c 4).isLt
  omega

/-- **Probe.** `C5` has projective face data: one face whose boundary walk runs twice around the 5-cycle. -/
def faceC5 : FaceData (cycleGraph 5) where
  faces := [w10]
  cover := fun x hx => by simp [w10_count x hx]
  euler := by rw [c5_card]; simp
  even := fun F hF => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hF; subst hF; decide
  three_le := fun F hF => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hF; subst hF; decide
  short_simple := fun F hF h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF; subst hF; exact absurd h (by decide)
  euler_bip := fun h => absurd h c5_not_bip
  distinct := fun i j hij => by fin_cases i; fin_cases j; exact absurd rfl hij

/-! ## A single edge is combinatorially thrackleable -/

/-- One edge `0 → 1`. -/
def eK2 : Fin 1 → Fin 2 × Fin 2 := mkE 2 [(0, 1)]

/-- Its only crossing system (no non-incident pairs). -/
def pK2 : CrossingSystem eK2 where
  π := fun _ => []
  nodup := fun _ => List.nodup_nil
  mem := by decide

lemma aug_K2_adj {x y : AV 2 1} (h : (aug eK2 pK2).Adj x y) : s(x, y) = s(ov 0, ov 1) := by
  rw [aug, fromEdgeSet_adj] at h
  obtain ⟨h, -⟩ := h
  rcases h with ⟨e, he⟩ | ⟨e, f, hef, -⟩
  · fin_cases e
    simpa [pathEdges, pathNodes, pK2, eK2, mkE] using he
  · fin_cases e; fin_cases f; exact absurd hef (by decide)

lemma mem_of_adj {x y : AV 2 1} {S T : Set (AV 2 1)} (hx : x ∈ S) (hy : y ∈ T) (h : (aug eK2 pK2).Adj x y) :
    ov 0 ∈ S ∪ T := by
  rcases Sym2.eq_iff.1 (aug_K2_adj h) with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · exact Or.inl hx
  · exact Or.inr hy

/-- **Probe.** A single edge is combinatorially thrackleable. -/
theorem combThr_K2 : CombThr eK2 := by
  refine ⟨pK2, ?_, ?_⟩
  · rintro ⟨B, -, -, hdisj, hadj⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj 0 1 (by decide)
    obtain ⟨x', hx', y', hy', hxy'⟩ := hadj 2 3 (by decide)
    rcases mem_of_adj hx hy hxy with h | h <;> rcases mem_of_adj hx' hy' hxy' with h' | h'
    · exact Set.disjoint_left.1 (hdisj (by decide : (0 : Fin 5) ≠ 2)) h h'
    · exact Set.disjoint_left.1 (hdisj (by decide : (0 : Fin 5) ≠ 3)) h h'
    · exact Set.disjoint_left.1 (hdisj (by decide : (1 : Fin 5) ≠ 2)) h h'
    · exact Set.disjoint_left.1 (hdisj (by decide : (1 : Fin 5) ≠ 3)) h h'
  · rintro ⟨B, -, -, hdisj, hadj⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hadj (.inl 0) (.inr 0) (by simp)
    obtain ⟨x', hx', y', hy', hxy'⟩ := hadj (.inl 1) (.inr 1) (by simp)
    rcases mem_of_adj hx hy hxy with h | h <;> rcases mem_of_adj hx' hy' hxy' with h' | h'
    · exact Set.disjoint_left.1 (hdisj (by simp : (Sum.inl 0 : Fin 3 ⊕ Fin 3) ≠ .inl 1)) h h'
    · exact Set.disjoint_left.1 (hdisj (by simp : (Sum.inl 0 : Fin 3 ⊕ Fin 3) ≠ .inr 1)) h h'
    · exact Set.disjoint_left.1 (hdisj (by simp : (Sum.inr 0 : Fin 3 ⊕ Fin 3) ≠ .inl 1)) h h'
    · exact Set.disjoint_left.1 (hdisj (by simp : (Sum.inr 0 : Fin 3 ⊕ Fin 3) ≠ .inr 1)) h h'

/-! ## The run listings of `u66v_4`, `u66v_5`, `u66v_7` -/

/-- graphs/u66v_4.txt, graphs/u66v_5.txt, graphs/u66v_7.txt (the computations of the 6-6 lemma), before src/prep.py. -/
def gV4 : List (ℕ × ℕ) := [(0,1),(0,5),(0,6),(1,2),(2,3),(2,7),(3,4),(3,6),(4,5),(5,7)]
def gV5 : List (ℕ × ℕ) := [(0,1),(0,5),(0,6),(1,2),(2,3),(2,7),(2,8),(3,4),(4,5),(5,8),(6,7)]
def gV7 : List (ℕ × ℕ) := [(0,1),(0,5),(0,6),(0,9),(1,2),(2,3),(3,4),(3,8),(3,9),(4,5),(6,7),(7,8)]

/-- The unordered edges of a listing. -/
def uEdges (l : List (ℕ × ℕ)) : Finset (Sym2 ℕ) := (l.map fun p => s(p.1, p.2)).toFinset

/-- **Probe.** The listings as run have the edges of the graph files (and as many entries). -/
theorem lV_edges : uEdges lV4 = uEdges gV4 ∧ uEdges lV5 = uEdges gV5 ∧ uEdges lV7 = uEdges gV7 ∧
    lV4.length = gV4.length ∧ lV5.length = gV5.length ∧ lV7.length = gV7.length := by
  decide

/-! ## Facial walks without spikes -/

/-- **Probe.** The face data of `C6` has no spikes. -/
theorem faceC6_noSpike : faceC6.NoSpike := by
  intro F hF i
  simp only [faceC6, List.mem_cons, List.not_mem_nil, or_false, or_self] at hF
  subst hF
  revert i
  decide

/-- **Probe.** The face data of `C5` (one walk of length `10`) has no spikes. -/
theorem faceC5_noSpike : faceC5.NoSpike := by
  intro F hF i
  simp only [faceC5, List.mem_cons, List.not_mem_nil, or_false] at hF
  subst hF
  revert i
  decide

end Thrackle78.Probe
