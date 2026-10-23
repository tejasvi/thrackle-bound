import Thrackle78.Checker.AugPath
import Thrackle78.Checker.Minor

/-!
# Planarity of the augmented graph passes to sub-listings

A sub-listing `E'` of `E` (`IsSubListing`): the edges `ι e`, vertices renamed by `φ`, the same orientations (as written
by make_sub.py). A crossing system `P` of `E` restricts to `P.restrict`: the crossings with kept edges, in the order of
`P`. **`planar_restrict`**: if `aug E P` is planar, so is `aug E' (P.restrict …)`.

Proof: a `K₅` or `K₃,₃` minor of `aug E' P'` transfers to `aug E P` (`not_planar_of_map`) along `C x`, the nodes of
the paths of the kept edges whose position `p` corresponds to the node `x` of the restricted path (`qpos`): an end
vertex takes the path up to the first and after the last kept crossing, a kept crossing itself, a subdivision vertex
the path between two consecutive kept crossings. Prefixes of the search order (`φ = id`) give the pruning by the
partial augmented graph; cycles give the cycle filters.
-/

namespace Thrackle78

variable {n m n' m' : ℕ}

/-- `E'` is the sub-listing of `E` on the edges `ι`, with vertices renamed by `φ` and the same orientations. -/
def IsSubListing (E : Fin m → Fin n × Fin n) (E' : Fin m' → Fin n' × Fin n') (ι : Fin m' ↪ Fin m)
    (φ : Fin n' ↪ Fin n) : Prop :=
  ∀ e, E (ι e) = (φ (E' e).1, φ (E' e).2)

/-- The partial inverse of `ι`. -/
def invE (ι : Fin m' ↪ Fin m) (g : Fin m) : Option (Fin m') := (List.finRange m').find? fun e => ι e = g

lemma invE_eq_some {ι : Fin m' ↪ Fin m} {g : Fin m} {e : Fin m'} : invE ι g = some e ↔ ι e = g := by
  unfold invE
  constructor
  · intro h
    simpa using List.find?_some h
  · intro h
    subst h
    cases hf : (List.finRange m').find? (fun e' => decide (ι e' = ι e)) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp) (hf e (List.mem_finRange e))
    | some e' =>
      have := List.find?_some hf
      simp only [decide_eq_true_eq] at this
      rw [ι.injective this]

lemma invE_apply (ι : Fin m' ↪ Fin m) (e : Fin m') : invE ι (ι e) = some e := invE_eq_some.2 rfl

/-- The restriction of a crossing system to a sub-listing. -/
def CrossingSystem.restrict {E : Fin m → Fin n × Fin n} {E' : Fin m' → Fin n' × Fin n'} (P : CrossingSystem E)
    (ι : Fin m' ↪ Fin m) (φ : Fin n' ↪ Fin n) (h : IsSubListing E E' ι φ) : CrossingSystem E' where
  π e := (P.π (ι e)).filterMap (invE ι)
  nodup e := (P.nodup (ι e)).filterMap fun a a' b hb hb' => by
    rw [Option.mem_def, invE_eq_some] at hb hb'
    exact hb.symm.trans hb'
  mem e f := by
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨g, hg, hgf⟩
      rw [invE_eq_some] at hgf
      subst hgf
      have := (P.mem (ι e) (ι f)).1 hg
      unfold NonInc at this ⊢
      rw [h e, h f] at this
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq] at this
      exact this
    · intro hf
      refine ⟨ι f, (P.mem (ι e) (ι f)).2 ?_, invE_eq_some.2 rfl⟩
      unfold NonInc at hf ⊢
      rw [h e, h f]
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
      exact hf

end Thrackle78

namespace Thrackle78.Checker

open SimpleGraph

/-! ## Lists: kept entries of a `filterMap` -/

section Lists

variable {α β : Type} (f : α → Option β)

/-- The number of kept entries among the first `j`. -/
def cntK (l : List α) (j : ℕ) : ℕ := (l.take j).countP fun a => (f a).isSome

lemma cntK_zero (l : List α) : cntK f l 0 = 0 := by simp [cntK]

lemma cntK_succ (l : List α) (j : ℕ) (hj : j < l.length) :
    cntK f l (j + 1) = cntK f l j + if (f l[j]).isSome then 1 else 0 := by
  unfold cntK
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.countP_append]
  simp

lemma cntK_length (l : List α) : cntK f l l.length = (l.filterMap f).length := by
  unfold cntK
  rw [List.take_length, List.length_filterMap_eq_countP]

lemma cntK_le (l : List α) (j : ℕ) : cntK f l j ≤ (l.filterMap f).length := by
  unfold cntK
  rw [List.length_filterMap_eq_countP]
  exact List.Sublist.countP_le (List.take_sublist _ _)

lemma cntK_mono (l : List α) {i j : ℕ} (hij : i ≤ j) : cntK f l i ≤ cntK f l j := by
  unfold cntK
  exact List.Sublist.countP_le (List.take_sublist_take_left hij)

/-- The kept entry at `j` is entry `cntK j` of the `filterMap`. -/
lemma filterMap_getElem?_cntK : ∀ (l : List α) (j : ℕ) (hj : j < l.length) (b : β), f l[j] = some b →
    (l.filterMap f)[cntK f l j]? = some b
  | [], _, hj, _, _ => absurd hj (by simp)
  | a :: l, 0, _, b, hb => by
    simp only [List.getElem_cons_zero] at hb
    simp [cntK, hb]
  | a :: l, j + 1, hj, b, hb => by
    simp only [List.getElem_cons_succ] at hb
    have ih := filterMap_getElem?_cntK l j (by simpa using hj) b hb
    rcases ha : f a with _ | c
    · simp [cntK, ha] at ih ⊢
      exact ih
    · simp [cntK, ha] at ih ⊢
      exact ih

/-- Every entry of the `filterMap` is a kept entry. -/
lemma exists_of_filterMap_getElem : ∀ (l : List α) (c : ℕ) (hc : c < (l.filterMap f).length),
    ∃ j, ∃ hj : j < l.length, f l[j] = some (l.filterMap f)[c] ∧ cntK f l j = c
  | [], _, hc => absurd hc (by simp)
  | a :: l, c, hc => by
    rcases ha : f a with _ | b
    · have hc' : c < (l.filterMap f).length := by simpa [List.filterMap_cons, ha] using hc
      obtain ⟨j, hj, h1, h2⟩ := exists_of_filterMap_getElem l c hc'
      refine ⟨j + 1, by simp; omega, ?_, ?_⟩
      · simp only [List.getElem_cons_succ, h1]
        congr 1
        simp [ha]
      · simp [cntK, ha] at h2 ⊢
        exact h2
    · cases c with
      | zero =>
        refine ⟨0, by simp, ?_, by simp [cntK]⟩
        simp [ha]
      | succ c =>
        have hc' : c < (l.filterMap f).length := by simpa [List.filterMap_cons, ha] using hc
        obtain ⟨j, hj, h1, h2⟩ := exists_of_filterMap_getElem l c hc'
        refine ⟨j + 1, by simp; omega, ?_, ?_⟩
        · simp only [List.getElem_cons_succ, h1]
          congr 1
          simp [ha]
        · simp [cntK, ha] at h2 ⊢
          omega

end Lists


/-! ## The position map -/

section Position

/-- `1` if the crossing `j` of `ι e` is with a kept edge, else `0`. -/
def keptN {n m m' : ℕ} {E : Fin m → Fin n × Fin n} (P : CrossingSystem E) (ι : Fin m' ↪ Fin m) (e : Fin m')
    (j : ℕ) : ℕ :=
  if ((P.π (ι e))[j]?.bind (invE ι)).isSome then 1 else 0

/-- The number of kept crossings of `ι e` among its first `j`. -/
def keptCnt {n m m' : ℕ} {E : Fin m → Fin n × Fin n} (P : CrossingSystem E) (ι : Fin m' ↪ Fin m) (e : Fin m')
    (j : ℕ) : ℕ :=
  cntK (invE ι) (P.π (ι e)) j

variable {n m n' m' : ℕ} {E : Fin m → Fin n × Fin n} {E' : Fin m' → Fin n' × Fin n'} {ι : Fin m' ↪ Fin m}
  {φ : Fin n' ↪ Fin n} (h : IsSubListing E E' ι φ) (P : CrossingSystem E)

/-- The position on the path of `e` in `aug E' P'` of the node owning position `p` of the path of `ι e`. -/
def qpos (e : Fin m') (p : ℕ) : ℕ :=
  if p = 0 then 0
  else if p + 1 = (pathNodes E P (ι e)).length then (pathNodes E' (P.restrict ι φ h) e).length - 1
  else if p % 2 = 1 ∧ keptN P ι e (p / 2) = 1 then 2 * keptCnt P ι e (p / 2) + 1
  else if keptCnt P ι e (p / 2) = 0 then 0
  else if keptCnt P ι e (p / 2) = ((P.restrict ι φ h).π e).length then (pathNodes E' (P.restrict ι φ h) e).length - 1
  else 2 * keptCnt P ι e (p / 2)

lemma restrict_π (e : Fin m') : (P.restrict ι φ h).π e = (P.π (ι e)).filterMap (invE ι) := rfl

lemma keptN_le (e : Fin m') (j : ℕ) : keptN P ι e j ≤ 1 := by
  unfold keptN; split_ifs <;> omega

lemma keptN_eq (e : Fin m') (j : ℕ) (hj : j < (P.π (ι e)).length) :
    keptN P ι e j = if (invE ι (P.π (ι e))[j]).isSome then 1 else 0 := by
  simp [keptN, List.getElem?_eq_getElem hj]

lemma keptN_eq_one (e : Fin m') (j : ℕ) (hj : j < (P.π (ι e)).length) :
    keptN P ι e j = 1 ↔ ∃ g, invE ι (P.π (ι e))[j] = some g := by
  rw [keptN_eq P e j hj]
  rcases hg : invE ι (P.π (ι e))[j] with _ | g <;> simp

lemma keptCnt_succ (e : Fin m') (j : ℕ) (hj : j < (P.π (ι e)).length) :
    keptCnt P ι e (j + 1) = keptCnt P ι e j + keptN P ι e j := by
  unfold keptCnt
  rw [cntK_succ _ _ _ hj, keptN_eq P e j hj]

lemma keptCnt_zero (e : Fin m') : keptCnt P ι e 0 = 0 := cntK_zero _ _

lemma keptCnt_le (e : Fin m') (j : ℕ) : keptCnt P ι e j ≤ ((P.restrict ι φ h).π e).length := cntK_le _ _ _

lemma keptCnt_length (e : Fin m') : keptCnt P ι e (P.π (ι e)).length = ((P.restrict ι φ h).π e).length :=
  cntK_length _ _

lemma keptCnt_mono (e : Fin m') {i j : ℕ} (hij : i ≤ j) : keptCnt P ι e i ≤ keptCnt P ι e j := cntK_mono _ _ hij

lemma restrict_length_le (e : Fin m') : ((P.restrict ι φ h).π e).length ≤ (P.π (ι e)).length := by
  rw [← keptCnt_length h P e]
  unfold keptCnt cntK
  exact (List.countP_le_length).trans (by simp)

lemma len_cases (Q : CrossingSystem E) (e : Fin m) :
    ((Q.π e).length = 0 ∧ (pathNodes E Q e).length = 2) ∨
      (0 < (Q.π e).length ∧ (pathNodes E Q e).length = 2 * (Q.π e).length + 1) := by
  rw [pathNodes_length]
  by_cases he : Q.π e = []
  · left; simp [he]
  · right
    have := List.length_pos_iff.2 he
    exact ⟨this, by simp [he]⟩

lemma len_cases' (e : Fin m') :
    (((P.restrict ι φ h).π e).length = 0 ∧ (pathNodes E' (P.restrict ι φ h) e).length = 2) ∨
      (0 < ((P.restrict ι φ h).π e).length ∧
        (pathNodes E' (P.restrict ι φ h) e).length = 2 * ((P.restrict ι φ h).π e).length + 1) :=
  len_cases (P.restrict ι φ h) e

lemma qpos_zero (e : Fin m') : qpos h P e 0 = 0 := by simp [qpos]

lemma qpos_last (e : Fin m') :
    qpos h P e ((pathNodes E P (ι e)).length - 1) = (pathNodes E' (P.restrict ι φ h) e).length - 1 := by
  have := len_cases P (ι e)
  unfold qpos
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- A kept crossing is followed by one more count. -/
lemma keptCnt_lt_of_kept (e : Fin m') (j : ℕ) (hj : j < (P.π (ι e)).length) (hk : keptN P ι e j = 1) :
    keptCnt P ι e j + 1 ≤ ((P.restrict ι φ h).π e).length := by
  have := keptCnt_succ P e j hj
  have := keptCnt_le h P e (j + 1)
  omega

/-- The positions of the restricted path that `qpos` takes stay inside the path. -/
lemma qpos_lt (e : Fin m') (p : ℕ) (hp : p < (pathNodes E P (ι e)).length) :
    qpos h P e p < (pathNodes E' (P.restrict ι φ h) e).length := by
  have hl := len_cases P (ι e)
  have hl' := len_cases' h P e
  have hc := keptCnt_le h P e (p / 2)
  unfold qpos
  split_ifs with h0 h1 h2 h3 h4
  · omega
  · omega
  · have hj : p / 2 < (P.π (ι e)).length := by
      by_contra hj
      have : keptN P ι e (p / 2) = 0 := by
        simp [keptN, List.getElem?_eq_none (by omega : (P.π (ι e)).length ≤ p / 2)]
      omega
    have := keptCnt_lt_of_kept h P e (p / 2) hj h2.2
    omega
  · omega
  · omega
  · omega

/-- **Unit steps.** Along the path of `ι e`, `qpos` stays or moves on by one. -/
lemma qpos_step (e : Fin m') (p : ℕ) (hp1 : p + 1 < (pathNodes E P (ι e)).length) :
    qpos h P e p ≤ qpos h P e (p + 1) ∧ qpos h P e (p + 1) ≤ qpos h P e p + 1 := by
  have hl := len_cases P (ι e)
  have hl' := len_cases' h P e
  have hk' := restrict_length_le h P e
  have hck := keptCnt_length h P e
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hc0 : keptCnt P ι e ((0 + 1) / 2) = 0 := keptCnt_zero P e
    rw [qpos_zero]
    unfold qpos
    split_ifs <;> omega
  · have hj : p / 2 < (P.π (ι e)).length := by omega
    have hcle := keptCnt_le h P e (p / 2)
    have hkle := keptN_le (ι := ι) P e (p / 2)
    have hkept : keptN P ι e (p / 2) = 1 → keptCnt P ι e (p / 2) + 1 ≤ ((P.restrict ι φ h).π e).length :=
      keptCnt_lt_of_kept h P e (p / 2) hj
    rcases Nat.mod_two_eq_zero_or_one p with hpar | hpar
    · have hd : (p + 1) / 2 = p / 2 := by omega
      unfold qpos
      rw [hd]
      split_ifs <;> first | omega | contradiction
    · have hd : (p + 1) / 2 = p / 2 + 1 := by omega
      have hs := keptCnt_succ P e (p / 2) hj
      have hlast : p + 1 + 1 = (pathNodes E P (ι e)).length → keptCnt P ι e (p / 2 + 1) =
          ((P.restrict ι φ h).π e).length := by
        intro h2
        rw [← hck]
        congr 1
        omega
      have hcle1 := keptCnt_le h P e (p / 2 + 1)
      unfold qpos
      rw [hd]
      split_ifs <;> first | omega | contradiction

/-- `qpos` is monotone along the path. -/
lemma qpos_mono (e : Fin m') {p q : ℕ} (hpq : p ≤ q) (hq : q < (pathNodes E P (ι e)).length) :
    qpos h P e p ≤ qpos h P e q := by
  induction q, hpq using Nat.le_induction with
  | base => exact le_refl _
  | succ q hpq ih => exact (ih (by omega)).trans (qpos_step h P e q hq).1

/-- Every position of the restricted path is taken (and every step between consecutive ones). -/
lemma exists_qpos_step (e : Fin m') (i : ℕ) (hi : i + 1 < (pathNodes E' (P.restrict ι φ h) e).length) :
    ∃ p, p + 1 < (pathNodes E P (ι e)).length ∧ qpos h P e p = i ∧ qpos h P e (p + 1) = i + 1 := by
  have hl := len_cases P (ι e)
  obtain ⟨p, -, hp, h1, h2⟩ := exists_step (qpos h P e) i 0 ((pathNodes E P (ι e)).length - 1) (Nat.zero_le _)
    (by rw [qpos_zero]; omega) (by rw [qpos_last]; omega)
    (fun p _ hp => (qpos_step h P e p (by omega)).2)
  exact ⟨p, by omega, h1, h2⟩

lemma exists_qpos (e : Fin m') (i : ℕ) (hi : i < (pathNodes E' (P.restrict ι φ h) e).length) :
    ∃ p, p < (pathNodes E P (ι e)).length ∧ qpos h P e p = i := by
  have hl := len_cases P (ι e)
  by_cases hi' : i + 1 < (pathNodes E' (P.restrict ι φ h) e).length
  · obtain ⟨p, hp, h1, -⟩ := exists_qpos_step h P e i hi'
    exact ⟨p, by omega, h1⟩
  · exact ⟨(pathNodes E P (ι e)).length - 1, by omega, by rw [qpos_last]; omega⟩

end Position


/-! ## Nodes of the augmented paths -/

section Nodes

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

lemma ov_ne_xv (a : Fin n) (e f : Fin m) : (ov a : AV n m) ≠ xv e f := by simp [ov, xv]

lemma ov_ne_sv (a : Fin n) (e : Fin m) (t : ℕ) : (ov a : AV n m) ≠ sv e t := by simp [ov, sv]

lemma xv_ne_sv (e f g : Fin m) (t : ℕ) : (xv e f : AV n m) ≠ sv g t := by simp [xv, sv]

lemma ov_inj {a b : Fin n} (h : (ov a : AV n m) = ov b) : a = b := by simpa [ov] using h

lemma sv_inj {e g : Fin m} {t u : ℕ} (h : (sv e t : AV n m) = sv g u) : e = g ∧ t % m = u % m := by
  simp only [sv, Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
  exact h

lemma xv_comm (e f : Fin m) : (xv e f : AV n m) = xv f e := by simp [xv, min_comm, max_comm]

lemma xv_inj {e f e' f' : Fin m} (h : (xv e f : AV n m) = xv e' f') : (e = e' ∧ f = f') ∨ (e = f' ∧ f = e') := by
  simp only [xv, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rcases le_total e f with hef | hef <;> rcases le_total e' f' with hef' | hef'
  · rw [min_eq_left hef, min_eq_left hef'] at h1
    rw [max_eq_right hef, max_eq_right hef'] at h2
    exact Or.inl ⟨h1, h2⟩
  · rw [min_eq_left hef, min_eq_right hef'] at h1
    rw [max_eq_right hef, max_eq_left hef'] at h2
    exact Or.inr ⟨h1, h2⟩
  · rw [min_eq_right hef, min_eq_left hef'] at h1
    rw [max_eq_left hef, max_eq_right hef'] at h2
    exact Or.inr ⟨h2, h1⟩
  · rw [min_eq_right hef, min_eq_right hef'] at h1
    rw [max_eq_left hef, max_eq_left hef'] at h2
    exact Or.inl ⟨h2, h1⟩

/-- The nodes of a path, by position: the ends, crossings (odd), subdivision vertices (even). -/
lemma node_cases (Q : CrossingSystem E) (e : Fin m) (p : ℕ) (hp : p < (pathNodes E Q e).length) :
    (p = 0 ∧ node Q e p = ov (E e).1) ∨ (p + 1 = (pathNodes E Q e).length ∧ node Q e p = ov (E e).2) ∨
      (0 < p ∧ p + 1 < (pathNodes E Q e).length ∧ p % 2 = 1 ∧
        ∃ hj : p / 2 < (Q.π e).length, node Q e p = xv e (Q.π e)[p / 2]) ∨
      (0 < p ∧ p + 1 < (pathNodes E Q e).length ∧ p % 2 = 0 ∧ p / 2 < (Q.π e).length ∧
        node Q e p = sv e (p / 2 - 1)) := by
  have hl := len_cases Q e
  by_cases h0 : p = 0
  · subst h0; exact Or.inl ⟨rfl, node_zero Q e⟩
  by_cases h1 : p + 1 = (pathNodes E Q e).length
  · exact Or.inr (Or.inl ⟨h1, node_last Q e p h1⟩)
  rcases Nat.mod_two_eq_zero_or_one p with hpar | hpar
  · refine Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hpar, by omega, ?_⟩))
    have := node_even Q e (p / 2 - 1) (by omega)
    rwa [show 2 * (p / 2 - 1) + 2 = p by omega] at this
  · refine Or.inr (Or.inr (Or.inl ⟨by omega, by omega, hpar, by omega, ?_⟩))
    have := node_odd Q e (p / 2) (by omega)
    rwa [show 2 * (p / 2) + 1 = p by omega] at this

/-- **Equal nodes.** Two positions with the same node: the same position of the same path, or two ends, or the
crossing of the two edges. -/
lemma node_eq_cases (Q : CrossingSystem E) (e₁ e₂ : Fin m) (p₁ p₂ : ℕ) (hp₁ : p₁ < (pathNodes E Q e₁).length)
    (hp₂ : p₂ < (pathNodes E Q e₂).length) (heq : node Q e₁ p₁ = node Q e₂ p₂) :
    (e₁ = e₂ ∧ p₁ = p₂) ∨
      ((p₁ = 0 ∨ p₁ + 1 = (pathNodes E Q e₁).length) ∧ (p₂ = 0 ∨ p₂ + 1 = (pathNodes E Q e₂).length)) ∨
      (p₁ % 2 = 1 ∧ p₂ % 2 = 1 ∧ ∃ (hj₁ : p₁ / 2 < (Q.π e₁).length) (hj₂ : p₂ / 2 < (Q.π e₂).length),
        (Q.π e₁)[p₁ / 2] = e₂ ∧ (Q.π e₂)[p₂ / 2] = e₁) := by
  have hm₁ : ∀ j (hj : j < (Q.π e₁).length), j < m := fun j hj =>
    lt_of_lt_of_le hj ((Q.nodup e₁).length_le_card.trans (by simp))
  rcases node_cases Q e₁ p₁ hp₁ with ⟨h0, ha⟩ | ⟨h0, ha⟩ | ⟨h0, hl, hpar, hj, ha⟩ | ⟨h0, hl, hpar, hj, ha⟩ <;>
    rcases node_cases Q e₂ p₂ hp₂ with ⟨h0', hb⟩ | ⟨h0', hb⟩ | ⟨h0', hl', hpar', hj', hb⟩ |
      ⟨h0', hl', hpar', hj', hb⟩ <;> rw [ha, hb] at heq
  all_goals first
    | exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    | exact absurd heq (ov_ne_xv _ _ _)
    | exact absurd heq (ov_ne_sv _ _ _)
    | exact absurd heq.symm (ov_ne_xv _ _ _)
    | exact absurd heq.symm (ov_ne_sv _ _ _)
    | exact absurd heq (xv_ne_sv _ _ _ _)
    | exact absurd heq.symm (xv_ne_sv _ _ _ _)
    | skip
  · -- two crossings
    rcases xv_inj heq with ⟨he, hf⟩ | ⟨he, hf⟩
    · subst he
      have := (List.Nodup.getElem_inj_iff (Q.nodup e₁)).1 hf
      exact Or.inl ⟨rfl, by omega⟩
    · exact Or.inr (Or.inr ⟨hpar, hpar', hj, hj', hf, he.symm⟩)
  · -- two subdivision vertices
    obtain ⟨he, ht⟩ := sv_inj heq
    subst he
    have h1 := hm₁ (p₁ / 2) hj
    have h2 := hm₁ (p₂ / 2) hj'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
    exact Or.inl ⟨rfl, by omega⟩

/-- The edges of a path join consecutive nodes. -/
lemma mem_pathEdges (Q : CrossingSystem E) (e : Fin m) {z : Sym2 (AV n m)} (hz : z ∈ pathEdges E Q e) :
    ∃ i, i + 1 < (pathNodes E Q e).length ∧ z = s(node Q e i, node Q e (i + 1)) := by
  unfold pathEdges at hz
  rw [List.mem_map] at hz
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
  rw [List.mem_iff_getElem] at hab
  obtain ⟨i, hi, hiab⟩ := hab
  simp only [List.length_zip, List.length_tail] at hi
  rw [List.getElem_zip] at hiab
  simp only [Prod.mk.injEq] at hiab
  obtain ⟨ha, hb⟩ := hiab
  refine ⟨i, by omega, ?_⟩
  rw [node_eq_getElem Q e i (by omega), node_eq_getElem Q e (i + 1) (by omega), ← ha, ← hb, List.getElem_tail]

/-- A non-isolated vertex of an augmented graph is a node of some path. -/
lemma node_of_adj (Q : CrossingSystem E) {x y : AV n m} (hxy : (aug E Q).Adj x y) :
    ∃ e q, q < (pathNodes E Q e).length ∧ node Q e q = x := by
  unfold aug at hxy
  rw [SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨hz, -⟩ := hxy
  rcases hz with ⟨e, he⟩ | ⟨e, f, hef, hn, hd⟩
  · obtain ⟨i, hi, hz⟩ := mem_pathEdges Q e he
    rcases Sym2.eq_iff.1 hz with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨e, i, by omega, h1.symm⟩
    · exact ⟨e, i + 1, hi, h1.symm⟩
  · have hfe : f ∈ Q.π e := (Q.mem e f).2 hn
    have hef' : e ∈ Q.π f := (Q.mem f e).2 (by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hn
      exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h4, Ne.symm h3, Ne.symm h5⟩)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hfe
    obtain ⟨j', hj', hj'e⟩ := List.mem_iff_getElem.1 hef'
    have a1 := nbrs_fst_node Q e j hj
    have a2 := nbrs_snd_node Q e j hj
    have b1 := nbrs_fst_node Q (Q.π e)[j] j' hj'
    have b2 := nbrs_snd_node Q (Q.π e)[j] j' hj'
    rw [hj'e] at b1 b2
    have hl := len_cases Q e
    have hl' := len_cases Q (Q.π e)[j]
    unfold diamondEdges at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd | hd <;> rcases Sym2.eq_iff.1 hd with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨e, 2 * j, by omega, by rw [← a1, h1]⟩
    · exact ⟨(Q.π e)[j], 2 * j', by omega, by rw [← b1, h1]⟩
    · exact ⟨(Q.π e)[j], 2 * j', by omega, by rw [← b1, h1]⟩
    · exact ⟨e, 2 * j + 2, by omega, by rw [← a2, h1]⟩
    · exact ⟨e, 2 * j + 2, by omega, by rw [← a2, h1]⟩
    · exact ⟨(Q.π e)[j], 2 * j' + 2, by omega, by rw [← b2, h1]⟩
    · exact ⟨(Q.π e)[j], 2 * j' + 2, by omega, by rw [← b2, h1]⟩
    · exact ⟨e, 2 * j, by omega, by rw [← a1, h1]⟩

end Nodes


/-! ## The branch sets -/

section Branch

variable {n m n' m' : ℕ} {E : Fin m → Fin n × Fin n} {E' : Fin m' → Fin n' × Fin n'} {ι : Fin m' ↪ Fin m}
  {φ : Fin n' ↪ Fin n} (h : IsSubListing E E' ι φ) (P : CrossingSystem E)

lemma owner_zero (e : Fin m') : node (P.restrict ι φ h) e (qpos h P e 0) = ov (E' e).1 := by
  rw [qpos_zero, node_zero]

lemma owner_last (e : Fin m') :
    node (P.restrict ι φ h) e (qpos h P e ((pathNodes E P (ι e)).length - 1)) = ov (E' e).2 := by
  rw [qpos_last]
  exact node_last _ e _ (by have := len_cases' h P e; omega)

lemma restrict_getElem (e : Fin m') (j : ℕ) (hj : j < (P.π (ι e)).length) (g : Fin m')
    (hg : invE ι (P.π (ι e))[j] = some g) :
    ∃ hc : keptCnt P ι e j < ((P.restrict ι φ h).π e).length, ((P.restrict ι φ h).π e)[keptCnt P ι e j] = g := by
  have := filterMap_getElem?_cntK (invE ι) (P.π (ι e)) j hj g hg
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 this
  exact ⟨hlt, hget⟩

/-- At a kept crossing the owner is the crossing vertex of the restricted path. -/
lemma owner_kept (e : Fin m') (p : ℕ) (_hp0 : 0 < p) (hp1 : p + 1 < (pathNodes E P (ι e)).length)
    (hpar : p % 2 = 1) (hj : p / 2 < (P.π (ι e)).length) (g : Fin m') (hg : invE ι (P.π (ι e))[p / 2] = some g) :
    node (P.restrict ι φ h) e (qpos h P e p) = xv e g := by
  have hk : keptN P ι e (p / 2) = 1 := (keptN_eq_one P e (p / 2) hj).2 ⟨g, hg⟩
  have hq : qpos h P e p = 2 * keptCnt P ι e (p / 2) + 1 := by
    unfold qpos
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨hpar, hk⟩]
  obtain ⟨hc, hget⟩ := restrict_getElem h P e (p / 2) hj g hg
  rw [hq, node_odd _ e _ hc, hget]

/-- **Owner consistency.** Equal nodes of `aug E P` on kept paths have equal owners. -/
theorem owner_eq (e₁ e₂ : Fin m') (p₁ p₂ : ℕ) (hp₁ : p₁ < (pathNodes E P (ι e₁)).length)
    (hp₂ : p₂ < (pathNodes E P (ι e₂)).length) (heq : node P (ι e₁) p₁ = node P (ι e₂) p₂) :
    node (P.restrict ι φ h) e₁ (qpos h P e₁ p₁) = node (P.restrict ι φ h) e₂ (qpos h P e₂ p₂) := by
  rcases node_eq_cases P (ι e₁) (ι e₂) p₁ p₂ hp₁ hp₂ heq with ⟨he, hp⟩ | ⟨h1, h2⟩ |
      ⟨hpar₁, hpar₂, hj₁, hj₂, hf₁, hf₂⟩
  · obtain rfl := ι.injective he
    subst hp
    rfl
  · have end_owner : ∀ (e : Fin m') (p : ℕ), (p = 0 ∨ p + 1 = (pathNodes E P (ι e)).length) →
        ∃ v, node P (ι e) p = ov (φ v) ∧ node (P.restrict ι φ h) e (qpos h P e p) = ov v := by
      intro e p hp
      rcases hp with rfl | hp
      · exact ⟨(E' e).1, by rw [node_zero, h e], owner_zero h P e⟩
      · refine ⟨(E' e).2, by rw [node_last P (ι e) p hp, h e], ?_⟩
        rw [show p = (pathNodes E P (ι e)).length - 1 by omega]
        exact owner_last h P e
    obtain ⟨v₁, hv₁, ho₁⟩ := end_owner e₁ p₁ h1
    obtain ⟨v₂, hv₂, ho₂⟩ := end_owner e₂ p₂ h2
    rw [ho₁, ho₂]
    rw [hv₁, hv₂] at heq
    rw [φ.injective (ov_inj heq)]
  · have hl₁ := len_cases P (ι e₁)
    have hl₂ := len_cases P (ι e₂)
    rw [owner_kept h P e₁ p₁ (by omega) (by omega) hpar₁ hj₁ e₂ (by rw [hf₁]; exact invE_apply ι e₂),
      owner_kept h P e₂ p₂ (by omega) (by omega) hpar₂ hj₂ e₁ (by rw [hf₂]; exact invE_apply ι e₁)]
    exact xv_comm e₁ e₂

/-- The branch set of a node `x` of `aug E' P'`: the nodes of the kept paths that it owns. -/
def brC (x : AV n' m') : Set (AV n m) :=
  {a | ∃ e p, p < (pathNodes E P (ι e)).length ∧ node (P.restrict ι φ h) e (qpos h P e p) = x ∧
    node P (ι e) p = a}

lemma mem_brC (e : Fin m') (p : ℕ) (hp : p < (pathNodes E P (ι e)).length) :
    node P (ι e) p ∈ brC h P (node (P.restrict ι φ h) e (qpos h P e p)) := ⟨e, p, hp, rfl, rfl⟩

lemma brC_disj {x y : AV n' m'} {a : AV n m} (hx : a ∈ brC h P x) (hy : a ∈ brC h P y) : x = y := by
  obtain ⟨e₁, p₁, hp₁, rfl, ha₁⟩ := hx
  obtain ⟨e₂, p₂, hp₂, rfl, ha₂⟩ := hy
  exact owner_eq h P e₁ e₂ p₁ p₂ hp₁ hp₂ (ha₁.trans ha₂.symm)

/-- Positions with the same owner are joined inside its branch set. -/
lemma reach_interval (e : Fin m') (p₁ : ℕ) (x : AV n' m')
    (hx : node (P.restrict ι φ h) e (qpos h P e p₁) = x) :
    ∀ d (_ : p₁ + d < (pathNodes E P (ι e)).length), qpos h P e (p₁ + d) = qpos h P e p₁ →
      ∀ (ha : node P (ι e) p₁ ∈ brC h P x) (hb : node P (ι e) (p₁ + d) ∈ brC h P x),
        ((aug E P).induce (brC h P x)).Reachable ⟨_, ha⟩ ⟨_, hb⟩
  | 0, _, _, _, _ => SimpleGraph.Reachable.refl _
  | d + 1, hd, hq, ha, hb => by
    have hm1 := qpos_mono h P e (show p₁ ≤ p₁ + d by omega) (by omega)
    have hm2 := (qpos_step h P e (p₁ + d) (by omega)).1
    have hq' : qpos h P e (p₁ + d) = qpos h P e p₁ := by
      have : p₁ + (d + 1) = p₁ + d + 1 := by omega
      rw [this] at hq
      omega
    have hmid : node P (ι e) (p₁ + d) ∈ brC h P x := ⟨e, p₁ + d, by omega, by rw [hq', hx], rfl⟩
    refine (reach_interval e p₁ x hx d (by omega) hq' ha hmid).trans ?_
    rcases node_adj P (ι e) (p₁ + d) (by omega) with heq | hadj
    · have : (⟨node P (ι e) (p₁ + d), hmid⟩ : brC h P x) = ⟨node P (ι e) (p₁ + (d + 1)), hb⟩ :=
        Subtype.ext heq
      rw [this]
    · apply SimpleGraph.Adj.reachable
      simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
      exact hadj


/-- Positions with the same owner, in either order. -/
lemma reach_between (e : Fin m') (p₁ p₂ : ℕ) (hp₁ : p₁ < (pathNodes E P (ι e)).length)
    (hp₂ : p₂ < (pathNodes E P (ι e)).length) (hq : qpos h P e p₁ = qpos h P e p₂) (x : AV n' m')
    (hx : node (P.restrict ι φ h) e (qpos h P e p₁) = x) (ha : node P (ι e) p₁ ∈ brC h P x)
    (hb : node P (ι e) p₂ ∈ brC h P x) :
    ((aug E P).induce (brC h P x)).Reachable ⟨_, ha⟩ ⟨_, hb⟩ := by
  rcases le_total p₁ p₂ with h12 | h21
  · obtain ⟨d, rfl⟩ : ∃ d, p₂ = p₁ + d := ⟨p₂ - p₁, by omega⟩
    exact reach_interval h P e p₁ x hx d hp₂ hq.symm ha hb
  · obtain ⟨d, rfl⟩ : ∃ d, p₁ = p₂ + d := ⟨p₁ - p₂, by omega⟩
    exact (reach_interval h P e p₂ x (by rw [← hq]; exact hx) d hp₁ hq hb ha).symm

/-- An odd interior position of the restricted path is only taken at a kept crossing. -/
lemma qpos_odd_kept (e : Fin m') (p : ℕ) (hp : p < (pathNodes E P (ι e)).length)
    (hodd : qpos h P e p % 2 = 1) (hint : qpos h P e p + 1 < (pathNodes E' (P.restrict ι φ h) e).length) :
    0 < p ∧ p + 1 < (pathNodes E P (ι e)).length ∧ p % 2 = 1 ∧ keptN P ι e (p / 2) = 1 ∧
      qpos h P e p = 2 * keptCnt P ι e (p / 2) + 1 := by
  unfold qpos at hodd hint ⊢
  split_ifs at hodd hint ⊢ <;> omega

/-- The node of `aug E P` at a position owned by a crossing of the restricted path. -/
lemma node_of_qpos_odd (e : Fin m') (p : ℕ) (hp : p < (pathNodes E P (ι e)).length)
    (hodd : qpos h P e p % 2 = 1) (hj : qpos h P e p / 2 < ((P.restrict ι φ h).π e).length) (g : Fin m')
    (hg : ((P.restrict ι φ h).π e)[qpos h P e p / 2] = g) : node P (ι e) p = xv (ι e) (ι g) := by
  have hl' := len_cases' h P e
  obtain ⟨hp0, hp1, hpar, hk, hq⟩ := qpos_odd_kept h P e p hp hodd (by omega)
  have hj' : p / 2 < (P.π (ι e)).length := by have := len_cases P (ι e); omega
  obtain ⟨g', hg'⟩ := (keptN_eq_one P e (p / 2) hj').1 hk
  obtain ⟨hc, hget⟩ := restrict_getElem h P e (p / 2) hj' g' hg'
  have hidx : qpos h P e p / 2 = keptCnt P ι e (p / 2) := by omega
  have hgg : g' = g := by
    rw [← hget, ← hg]
    congr 1
    exact hidx.symm
  subst hgg
  have := node_odd P (ι e) (p / 2) hj'
  rw [show 2 * (p / 2) + 1 = p by omega] at this
  rw [this, (invE_eq_some.1 hg').symm]

/-- An end of a restricted path: its branch set joins the position to the end vertex. -/
lemma end_reach (e : Fin m') (p : ℕ) (hp : p < (pathNodes E P (ι e)).length)
    (hend : qpos h P e p = 0 ∨ qpos h P e p + 1 = (pathNodes E' (P.restrict ι φ h) e).length) :
    ∃ v, node (P.restrict ι φ h) e (qpos h P e p) = ov v ∧
      ∃ (hv : ov (φ v) ∈ brC h P (ov v)) (ha : node P (ι e) p ∈ brC h P (ov v)),
        ((aug E P).induce (brC h P (ov v))).Reachable ⟨_, hv⟩ ⟨_, ha⟩ := by
  have hl := len_cases P (ι e)
  have hl' := len_cases' h P e
  rcases hend with h0 | h1
  · have hx : node (P.restrict ι φ h) e (qpos h P e p) = ov (E' e).1 := by rw [h0, node_zero]
    refine ⟨(E' e).1, hx, ?_⟩
    have hv : node P (ι e) 0 = ov (φ (E' e).1) := by rw [node_zero, h e]
    have hm0 : ov (φ (E' e).1) ∈ brC h P (ov (E' e).1) :=
      ⟨e, 0, by omega, by rw [qpos_zero, node_zero], hv⟩
    have hmp : node P (ι e) p ∈ brC h P (ov (E' e).1) := ⟨e, p, hp, hx, rfl⟩
    refine ⟨hm0, hmp, ?_⟩
    have hm0' : node P (ι e) 0 ∈ brC h P (ov (E' e).1) := by rw [hv]; exact hm0
    have := reach_between h P e 0 p (by omega) hp (by rw [qpos_zero, h0]) (ov (E' e).1)
      (by rw [qpos_zero, node_zero]) hm0' hmp
    have e0 : (⟨ov (φ (E' e).1), hm0⟩ : brC h P (ov (E' e).1)) = ⟨node P (ι e) 0, hm0'⟩ := Subtype.ext hv.symm
    rw [e0]
    exact this
  · have hx : node (P.restrict ι φ h) e (qpos h P e p) = ov (E' e).2 := by
      rw [show qpos h P e p = (pathNodes E' (P.restrict ι φ h) e).length - 1 by omega]
      exact node_last _ e _ (by omega)
    refine ⟨(E' e).2, hx, ?_⟩
    have hv : node P (ι e) ((pathNodes E P (ι e)).length - 1) = ov (φ (E' e).2) := by
      rw [node_last P (ι e) _ (by omega), h e]
    have hql : qpos h P e ((pathNodes E P (ι e)).length - 1) = qpos h P e p := by
      rw [qpos_last]; omega
    have hm0 : ov (φ (E' e).2) ∈ brC h P (ov (E' e).2) :=
      ⟨e, (pathNodes E P (ι e)).length - 1, by omega, by rw [hql, hx], hv⟩
    have hmp : node P (ι e) p ∈ brC h P (ov (E' e).2) := ⟨e, p, hp, hx, rfl⟩
    refine ⟨hm0, hmp, ?_⟩
    have hm0' : node P (ι e) ((pathNodes E P (ι e)).length - 1) ∈ brC h P (ov (E' e).2) := by
      rw [hv]; exact hm0
    have := reach_between h P e ((pathNodes E P (ι e)).length - 1) p (by omega) hp hql (ov (E' e).2)
      (by rw [hql, hx]) hm0' hmp
    have e0 : (⟨ov (φ (E' e).2), hm0⟩ : brC h P (ov (E' e).2)) =
        ⟨node P (ι e) ((pathNodes E P (ι e)).length - 1), hm0'⟩ := Subtype.ext hv.symm
    rw [e0]
    exact this

/-- **Connectivity** of the branch sets of the non-isolated nodes. -/
theorem brC_connected (x : AV n' m') (hx : ∃ y, (aug E' (P.restrict ι φ h)).Adj x y) :
    ((aug E P).induce (brC h P x)).Connected := by
  obtain ⟨y, hxy⟩ := hx
  obtain ⟨e₀, q₀, hq₀, hx₀⟩ := node_of_adj (P.restrict ι φ h) hxy
  obtain ⟨p₀, hp₀, hpq₀⟩ := exists_qpos h P e₀ q₀ hq₀
  have hm₀ : node P (ι e₀) p₀ ∈ brC h P x := ⟨e₀, p₀, hp₀, by rw [hpq₀, hx₀], rfl⟩
  have key : ∀ a (ha : a ∈ brC h P x), ((aug E P).induce (brC h P x)).Reachable ⟨_, hm₀⟩ ⟨a, ha⟩ := by
    intro a ha
    obtain ⟨e, p, hp, hpx, hpa⟩ := ha
    subst hpa
    rcases node_eq_cases (P.restrict ι φ h) e₀ e q₀ (qpos h P e p) hq₀ (qpos_lt h P e p hp)
        (hx₀.trans hpx.symm) with ⟨rfl, hq⟩ | ⟨h1, h2⟩ | ⟨hpar₁, hpar₂, hj₁, hj₂, hf₁, hf₂⟩
    · exact reach_between h P e₀ p₀ p hp₀ hp (by rw [hpq₀, hq]) x (by rw [hpq₀, hx₀]) hm₀ _
    · rw [← hpq₀] at h1
      obtain ⟨v₀, hv₀, hw₀, hb₀, r₀⟩ := end_reach h P e₀ p₀ hp₀ h1
      obtain ⟨v, hv, hw, hb, r⟩ := end_reach h P e p hp h2
      have hx0' : node (P.restrict ι φ h) e₀ (qpos h P e₀ p₀) = x := by rw [hpq₀]; exact hx₀
      have hvv : v₀ = v := ov_inj (hv₀.symm.trans (hx0'.trans (hpx.symm.trans hv)))
      subst hvv
      have hxv : x = ov v₀ := hpx.symm.trans hv
      subst hxv
      exact r₀.symm.trans r
    · have hl₀ := len_cases' h P e₀
      have hl := len_cases' h P e
      have n₀ := node_of_qpos_odd h P e₀ p₀ hp₀ (by rw [hpq₀]; exact hpar₁) (by rw [hpq₀]; exact hj₁) e
        (by simp only [hpq₀]; exact hf₁)
      have n₁ := node_of_qpos_odd h P e p hp hpar₂ hj₂ e₀ hf₂
      have : (⟨node P (ι e₀) p₀, hm₀⟩ : brC h P x) = ⟨node P (ι e) p, ⟨e, p, hp, hpx, rfl⟩⟩ := by
        apply Subtype.ext
        simp only
        rw [n₀, n₁, xv_comm]
      rw [this]
  have : Nonempty (brC h P x) := ⟨⟨_, hm₀⟩⟩
  refine SimpleGraph.Connected.mk fun u v => ?_
  exact (key u.1 u.2).symm.trans (key v.1 v.2)

lemma brC_nonempty (x : AV n' m') (hx : ∃ y, (aug E' (P.restrict ι φ h)).Adj x y) : (brC h P x).Nonempty := by
  obtain ⟨y, hxy⟩ := hx
  obtain ⟨e₀, q₀, hq₀, hx₀⟩ := node_of_adj (P.restrict ι φ h) hxy
  obtain ⟨p₀, hp₀, hpq₀⟩ := exists_qpos h P e₀ q₀ hq₀
  exact ⟨_, e₀, p₀, hp₀, by rw [hpq₀, hx₀], rfl⟩

/-- The positions next to a kept crossing are owned by the neighbours of the restricted crossing. -/
lemma qpos_around_kept (e : Fin m') (j : ℕ) (hj : j < (P.π (ι e)).length) (hk : keptN P ι e j = 1) :
    qpos h P e (2 * j) = 2 * keptCnt P ι e j ∧ qpos h P e (2 * j + 2) = 2 * keptCnt P ι e j + 2 := by
  have hl := len_cases P (ι e)
  have hl' := len_cases' h P e
  have hc := keptCnt_lt_of_kept h P e j hj hk
  have hs := keptCnt_succ P e j hj
  have hck := keptCnt_length h P e
  have hlast : j + 1 = (P.π (ι e)).length → keptCnt P ι e (j + 1) = ((P.restrict ι φ h).π e).length := by
    intro hj1; rw [hj1]; exact hck
  constructor
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.mul_zero, qpos_zero, keptCnt_zero]
    · unfold qpos
      rw [show 2 * j / 2 = j by omega]
      split_ifs <;> omega
  · unfold qpos
    rw [show (2 * j + 2) / 2 = j + 1 by omega]
    split_ifs <;> omega

lemma nonInc_symm {e f : Fin m} (hn : NonInc E e f) : NonInc E f e := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hn
  exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h4, Ne.symm h3, Ne.symm h5⟩

/-- **Adjacency** of the branch sets along the edges of `aug E' P'`. -/
theorem brC_adj (x y : AV n' m') (hxy : (aug E' (P.restrict ι φ h)).Adj x y) :
    ∃ a ∈ brC h P x, ∃ b ∈ brC h P y, (aug E P).Adj a b := by
  have hne : x ≠ y := hxy.ne
  have adj_of : ∀ a b, a ∈ brC h P x → b ∈ brC h P y → s(a, b) ∈ augEdges E P → (aug E P).Adj a b := by
    intro a b ha hb hab
    refine aug_adj_of_mem P hab ?_
    rintro rfl
    exact hne (brC_disj h P ha hb)
  have pair : ∀ (u u' : AV n m) (U U' : AV n' m'), u ∈ brC h P U → u' ∈ brC h P U' →
      s(u, u') ∈ augEdges E P → s(x, y) = s(U, U') → ∃ a ∈ brC h P x, ∃ b ∈ brC h P y, (aug E P).Adj a b := by
    intro u u' U U' hu hu' huu' hxy'
    rcases Sym2.eq_iff.1 hxy' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      exact ⟨u, hu, u', hu', adj_of u u' hu hu' huu'⟩
    · subst h1; subst h2
      exact ⟨u', hu', u, hu, adj_of u' u hu' hu (by rw [Sym2.eq_swap]; exact huu')⟩
  unfold aug at hxy
  rw [SimpleGraph.fromEdgeSet_adj] at hxy
  obtain ⟨hz, -⟩ := hxy
  rcases hz with ⟨e, he⟩ | ⟨e, f, hef, hn, hd⟩
  · -- a path edge of `aug E' P'`
    obtain ⟨i, hi, hz⟩ := mem_pathEdges (P.restrict ι φ h) e he
    obtain ⟨p, hp, hq1, hq2⟩ := exists_qpos_step h P e i hi
    have ha : node P (ι e) p ∈ brC h P (node (P.restrict ι φ h) e i) := by
      rw [← hq1]; exact mem_brC h P e p (by omega)
    have hb : node P (ι e) (p + 1) ∈ brC h P (node (P.restrict ι φ h) e (i + 1)) := by
      rw [← hq2]; exact mem_brC h P e (p + 1) hp
    rcases node_adj P (ι e) p hp with heq | hadj
    · exfalso
      rw [heq] at ha
      have := brC_disj h P ha hb
      rcases Sym2.eq_iff.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hne (by rw [h1, h2, this])
      · exact hne (by rw [h1, h2, this])
    · refine pair _ _ _ _ ha hb ?_ hz
      unfold aug at hadj
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      exact hadj.1
  · -- a diamond edge of `aug E' P'`
    have hfe : f ∈ (P.restrict ι φ h).π e := ((P.restrict ι φ h).mem e f).2 hn
    have hef' : e ∈ (P.restrict ι φ h).π f := ((P.restrict ι φ h).mem f e).2 (nonInc_symm hn)
    obtain ⟨c, hc, hcf⟩ := List.mem_iff_getElem.1 hfe
    obtain ⟨c₂, hc₂, hc₂e⟩ := List.mem_iff_getElem.1 hef'
    obtain ⟨j, hj, hjf, hjc⟩ := exists_of_filterMap_getElem (invE ι) (P.π (ι e)) c hc
    obtain ⟨j₂, hj₂, hj₂e, hj₂c⟩ := exists_of_filterMap_getElem (invE ι) (P.π (ι f)) c₂ hc₂
    change invE ι (P.π (ι e))[j] = some ((P.restrict ι φ h).π e)[c] at hjf
    change invE ι (P.π (ι f))[j₂] = some ((P.restrict ι φ h).π f)[c₂] at hj₂e
    rw [hcf] at hjf
    rw [hc₂e] at hj₂e
    change keptCnt P ι e j = c at hjc
    change keptCnt P ι f j₂ = c₂ at hj₂c
    have hk : keptN P ι e j = 1 := (keptN_eq_one P e j hj).2 ⟨f, hjf⟩
    have hk₂ : keptN P ι f j₂ = 1 := (keptN_eq_one P f j₂ hj₂).2 ⟨e, hj₂e⟩
    have hLj : (P.π (ι e))[j] = ι f := (invE_eq_some.1 hjf).symm
    have hLj₂ : (P.π (ι f))[j₂] = ι e := (invE_eq_some.1 hj₂e).symm
    obtain ⟨hq1, hq2⟩ := qpos_around_kept h P e j hj hk
    obtain ⟨hq1', hq2'⟩ := qpos_around_kept h P f j₂ hj₂ hk₂
    have hl := len_cases P (ι e)
    have hl₂ := len_cases P (ι f)
    -- the neighbours in `aug E P` and in `aug E' P'`
    have A1 := nbrs_fst_node P (ι e) j hj
    have A2 := nbrs_snd_node P (ι e) j hj
    have B1 := nbrs_fst_node P (ι f) j₂ hj₂
    have B2 := nbrs_snd_node P (ι f) j₂ hj₂
    rw [hLj] at A1 A2
    rw [hLj₂] at B1 B2
    have A1' := nbrs_fst_node (P.restrict ι φ h) e c hc
    have A2' := nbrs_snd_node (P.restrict ι φ h) e c hc
    have B1' := nbrs_fst_node (P.restrict ι φ h) f c₂ hc₂
    have B2' := nbrs_snd_node (P.restrict ι φ h) f c₂ hc₂
    rw [hcf] at A1' A2'
    rw [hc₂e] at B1' B2'
    have mA1 : (nbrs E P (ι e) (ι f)).1 ∈ brC h P (nbrs E' (P.restrict ι φ h) e f).1 := by
      rw [A1, A1', ← hjc, ← hq1]; exact mem_brC h P e _ (by omega)
    have mA2 : (nbrs E P (ι e) (ι f)).2 ∈ brC h P (nbrs E' (P.restrict ι φ h) e f).2 := by
      rw [A2, A2', ← hjc, ← hq2]; exact mem_brC h P e _ (by omega)
    have mB1 : (nbrs E P (ι f) (ι e)).1 ∈ brC h P (nbrs E' (P.restrict ι φ h) f e).1 := by
      rw [B1, B1', ← hj₂c, ← hq1']; exact mem_brC h P f _ (by omega)
    have mB2 : (nbrs E P (ι f) (ι e)).2 ∈ brC h P (nbrs E' (P.restrict ι φ h) f e).2 := by
      rw [B2, B2', ← hj₂c, ← hq2']; exact mem_brC h P f _ (by omega)
    -- the diamond of `ι e`, `ι f` in `aug E P`
    have hnE : NonInc E (ι e) (ι f) := by
      unfold NonInc at hn ⊢
      rw [h e, h f]
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
      exact hn
    have hdE : ∀ z ∈ diamondEdges E P (ι e) (ι f), z ∈ augEdges E P := by
      intro z hz
      rcases lt_or_gt_of_ne (ι.injective.ne (ne_of_lt hef)) with hlt | hgt
      · exact Or.inr ⟨ι e, ι f, hlt, hnE, hz⟩
      · refine Or.inr ⟨ι f, ι e, hgt, nonInc_symm hnE, ?_⟩
        unfold diamondEdges at hz ⊢
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
        rcases hz with rfl | rfl | rfl | rfl
        · exact Or.inl Sym2.eq_swap
        · exact Or.inr (Or.inr (Or.inr Sym2.eq_swap))
        · exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
        · exact Or.inr (Or.inl Sym2.eq_swap)
    have d1 := hdE s((nbrs E P (ι e) (ι f)).1, (nbrs E P (ι f) (ι e)).1) (by unfold diamondEdges; simp)
    have d2 := hdE s((nbrs E P (ι f) (ι e)).1, (nbrs E P (ι e) (ι f)).2) (by unfold diamondEdges; simp)
    have d3 := hdE s((nbrs E P (ι e) (ι f)).2, (nbrs E P (ι f) (ι e)).2) (by unfold diamondEdges; simp)
    have d4 := hdE s((nbrs E P (ι f) (ι e)).2, (nbrs E P (ι e) (ι f)).1) (by unfold diamondEdges; simp)
    unfold diamondEdges at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with hd | hd | hd | hd
    · exact pair _ _ _ _ mA1 mB1 d1 hd
    · exact pair _ _ _ _ mB1 mA2 d2 hd
    · exact pair _ _ _ _ mA2 mB2 d3 hd
    · exact pair _ _ _ _ mB2 mA1 d4 hd

end Branch

/-! ## The theorem -/

/-- **Restriction.** Planarity of the augmented graph passes to sub-listings. -/
theorem planar_restrict {n m n' m' : ℕ} {E : Fin m → Fin n × Fin n} {E' : Fin m' → Fin n' × Fin n'}
    {ι : Fin m' ↪ Fin m} {φ : Fin n' ↪ Fin n} (h : IsSubListing E E' ι φ) (P : CrossingSystem E) :
    Planar (aug E P) → Planar (aug E' (P.restrict ι φ h)) := by
  intro hP
  by_contra hnp
  exact not_planar_of_map hnp (brC h P) (fun x hx => brC_nonempty h P x hx) (fun x hx => brC_connected h P x hx)
    (fun x x' _ _ hxx' => Set.disjoint_left.2 fun a ha ha' => hxx' (brC_disj h P ha ha'))
    (fun x x' hxx' => brC_adj h P x x' hxx') hP

/-- Combinatorial thrackleability passes to sub-listings. -/
theorem combThr_restrict {n m n' m' : ℕ} {E : Fin m → Fin n × Fin n} {E' : Fin m' → Fin n' × Fin n'}
    {ι : Fin m' ↪ Fin m} {φ : Fin n' ↪ Fin n} (h : IsSubListing E E' ι φ) : CombThr E → CombThr E' :=
  fun ⟨P, hP⟩ => ⟨P.restrict ι φ h, planar_restrict h P hP⟩


end Thrackle78.Checker
