import Thrackle78.Checker.Minor
import Thrackle78.Checker.Restrict
import Thrackle78.Checker.AugPath

/-!
# The branch-set map from `aug E P` onto the partial augmented graph of a stage (positions)

Fix a stage `(k, t)` of a crossing system `P`, with rows `R e = rowAt P k t e`. On the path of edge `e` in `aug E P`,
`cnt e j` counts the drawn crossings among the first `j` crossings. The aug vertex at position `p` belongs to the branch
set of the partial vertex `qnode e (mu e p)`, the node at position `mu e p` of the partial path `Q e` (core
`pathIds`), whenever `p` is covered (all positions of a drawn edge `e < k`; on edge `k`, the positions up to its last
drawn crossing): `asg_node`. `asg` is the assignment as a function of the aug vertex; `mu` moves by at most one
between neighbouring positions (`mu_step`) and covers `Q e` (`exists_cover_end`).
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

/-! ## Vertex ids -/

theorem xId_eq {n m p q : ℕ} (hpq : p < q) : xId n m p q = n + (p * m + q) := by
  simp [xId, hpq]

theorem xId_comm (n m p q : ℕ) : xId n m p q = xId n m q p := by
  unfold xId
  rcases lt_trichotomy p q with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right (by omega)]
  · rfl
  · rw [ite_eq_right (by omega), ite_eq_left h]

theorem le_xId (n m p q : ℕ) : n ≤ xId n m p q := by unfold xId; split_ifs <;> omega

theorem lt_mul_add {m a b : ℕ} (ha : a < m) (hb : b < m) : a * m + b < m * m := by
  calc a * m + b < a * m + m := by omega
    _ = (a + 1) * m := by ring
    _ ≤ m * m := Nat.mul_le_mul_right m ha

theorem xId_lt {n m p q : ℕ} (hp : p < m) (hq : q < m) : xId n m p q < n + m * m := by
  unfold xId
  split_ifs
  · have := lt_mul_add hp hq; omega
  · have := lt_mul_add hq hp; omega

theorem le_sId (n m e i : ℕ) : n + m * m ≤ sId n m e i := by unfold sId; omega

theorem mul_add_inj {m a b a' b' : ℕ} (hb : b < m) (hb' : b' < m) (h : a * m + b = a' * m + b') :
    a = a' ∧ b = b' := by
  have hm : 0 < m := by omega
  have h1 : (a * m + b) / m = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hb, Nat.zero_add]
  have h2 : (a' * m + b') / m = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hb', Nat.zero_add]
  have : a = a' := by rw [← h1, ← h2, h]
  subst this
  exact ⟨rfl, by omega⟩

theorem xId_inj {n m p q p' q' : ℕ} (hpq : p < q) (hpq' : p' < q') (hq : q < m) (hq' : q' < m)
    (h : xId n m p q = xId n m p' q') : p = p' ∧ q = q' := by
  rw [xId_eq hpq, xId_eq hpq'] at h
  exact mul_add_inj hq hq' (by omega)

theorem sId_inj {n m e i e' i' : ℕ} (hi : i < m) (hi' : i' < m) (h : sId n m e i = sId n m e' i') :
    e = e' ∧ i = i' := by
  unfold sId at h
  exact mul_add_inj hi hi' (by omega)

/-! ## The partial path `midIds`, `pathIds` by position -/

theorem midIds_length (n m e : ℕ) : ∀ (r : List ℕ) (i : ℕ), r ≠ [] → (midIds n m e r i).length = 2 * r.length - 1
  | [], _, h => absurd rfl h
  | [f], _, _ => rfl
  | f :: g :: rest, i, _ => by
    simp only [midIds, List.length_cons]
    rw [midIds_length n m e (g :: rest) (i + 1) (by simp)]
    simp only [List.length_cons]
    omega

theorem midIds_getElem?_even (n m e : ℕ) : ∀ (r : List ℕ) (i a : ℕ) (ha : a < r.length),
    (midIds n m e r i)[2 * a]? = some (xId n m e r[a])
  | [], _, _, ha => absurd ha (by simp)
  | [f], i, a, ha => by
    simp only [List.length_singleton] at ha
    obtain rfl : a = 0 := by omega
    rfl
  | f :: g :: rest, i, a, ha => by
    cases a with
    | zero => rfl
    | succ a =>
      have := midIds_getElem?_even n m e (g :: rest) (i + 1) a (by simp at ha ⊢; omega)
      rw [show 2 * (a + 1) = 2 * a + 1 + 1 by ring]
      simp only [midIds, List.getElem?_cons_succ]
      rw [this]
      simp

theorem midIds_getElem?_odd (n m e : ℕ) : ∀ (r : List ℕ) (i a : ℕ), a + 1 < r.length →
    (midIds n m e r i)[2 * a + 1]? = some (sId n m e (i + a))
  | [], _, _, ha => absurd ha (by simp)
  | [f], _, _, ha => absurd ha (by simp)
  | f :: g :: rest, i, a, ha => by
    cases a with
    | zero => rfl
    | succ a =>
      have := midIds_getElem?_odd n m e (g :: rest) (i + 1) a (by simp at ha ⊢; omega)
      rw [show 2 * (a + 1) + 1 = 2 * a + 1 + 1 + 1 by ring]
      simp only [midIds, List.getElem?_cons_succ]
      rw [this, show i + 1 + a = i + (a + 1) by omega]

variable {n m : ℕ} {E : Fin m → Fin n × Fin n} (P : CrossingSystem E) (k t : ℕ)

/-! ## Counting drawn crossings along a path -/

/-- The number of drawn crossings among the first `j` crossings of `e`. -/
def cnt (e : Fin m) (j : ℕ) : ℕ := ((P.π e).take j).countP (fun g => decide (g ∈ rowAt P k t e))

theorem rowAt_eq_filter (e : Fin m) : (P.π e).filter (fun g => decide (g ∈ rowAt P k t e)) = rowAt P k t e :=
  filter_mem_eq_of_sublist (rowAt_sublist P k t e) (P.nodup e)

theorem length_π_le (e : Fin m) : (P.π e).length ≤ m := by
  simpa using (P.nodup e).length_le_card

theorem cnt_zero (e : Fin m) : cnt P k t e 0 = 0 := by simp [cnt]

theorem cnt_succ (e : Fin m) (j : ℕ) (hj : j < (P.π e).length) :
    cnt P k t e (j + 1) = cnt P k t e j + if (P.π e)[j] ∈ rowAt P k t e then 1 else 0 := by
  unfold cnt
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.countP_append]
  simp only [Option.toList_some, List.countP_singleton]
  by_cases h : (P.π e)[j] ∈ rowAt P k t e <;> simp [h]

theorem cnt_of_le (e : Fin m) {j : ℕ} (hj : (P.π e).length ≤ j) : cnt P k t e j = (rowAt P k t e).length := by
  unfold cnt
  rw [List.take_of_length_le hj, List.countP_eq_length_filter, rowAt_eq_filter]

theorem cnt_succ_le (e : Fin m) (j : ℕ) : cnt P k t e (j + 1) ≤ cnt P k t e j + 1 := by
  by_cases hj : j < (P.π e).length
  · rw [cnt_succ P k t e j hj]; split_ifs <;> omega
  · rw [cnt_of_le P k t e (by omega), cnt_of_le P k t e (by omega)]; omega

theorem cnt_le_succ (e : Fin m) (j : ℕ) : cnt P k t e j ≤ cnt P k t e (j + 1) := by
  unfold cnt
  exact (List.take_sublist_take_left (by omega)).countP_le

theorem cnt_mono (e : Fin m) {j j' : ℕ} (h : j ≤ j') : cnt P k t e j ≤ cnt P k t e j' := by
  unfold cnt
  exact (List.take_sublist_take_left h).countP_le

theorem cnt_le_length (e : Fin m) (j : ℕ) : cnt P k t e j ≤ (rowAt P k t e).length := by
  rw [← cnt_of_le P k t e (le_refl (P.π e).length)]
  by_cases h : j ≤ (P.π e).length
  · exact cnt_mono P k t e h
  · rw [cnt_of_le P k t e (by omega), cnt_of_le P k t e (le_refl _)]

/-- The position in the row of a drawn crossing is the count of drawn crossings before it. -/
theorem idxOf_rowAt (e : Fin m) {g : Fin m} (hg : g ∈ rowAt P k t e) :
    (rowAt P k t e).idxOf g = cnt P k t e ((P.π e).idxOf g) := by
  have hgπ : g ∈ P.π e := (rowAt_sublist P k t e).subset hg
  conv_lhs => rw [← rowAt_eq_filter P k t e]
  exact idxOf_filter _ (P.nodup e) hgπ (by simpa using hg)

theorem rowAt_getElem_cnt (e : Fin m) (j : ℕ) (hj : j < (P.π e).length) (hd : (P.π e)[j] ∈ rowAt P k t e)
    (hc : cnt P k t e j < (rowAt P k t e).length) : (rowAt P k t e)[cnt P k t e j] = (P.π e)[j] := by
  have h := idxOf_rowAt P k t e hd
  rw [(P.nodup e).idxOf_getElem j hj] at h
  have hlt : (rowAt P k t e).idxOf (P.π e)[j] < (rowAt P k t e).length := List.idxOf_lt_length_iff.2 hd
  simp only [← h]
  exact List.getElem_idxOf hlt

/-- The `i`-th drawn crossing of `e` sits at position `j` of `π e` with `i` drawn crossings before it. -/
theorem exists_pos_of_lt (e : Fin m) (i : ℕ) (hi : i < (rowAt P k t e).length) :
    ∃ j, ∃ hj : j < (P.π e).length, (P.π e)[j] = (rowAt P k t e)[i] ∧ cnt P k t e j = i := by
  have hmem : (rowAt P k t e)[i] ∈ rowAt P k t e := List.getElem_mem hi
  have hgπ : (rowAt P k t e)[i] ∈ P.π e := (rowAt_sublist P k t e).subset hmem
  refine ⟨(P.π e).idxOf (rowAt P k t e)[i], List.idxOf_lt_length_iff.2 hgπ, List.getElem_idxOf _, ?_⟩
  rw [← idxOf_rowAt P k t e hmem, (rowAt_nodup P k t e).idxOf_getElem i hi]

/-! ## The assignment -/

/-- The partial vertex (id) of an aug vertex on the path of `e` with `c` drawn crossings before it, if covered. -/
def segAsg (e : Fin m) (c : ℕ) : Option ℕ :=
  if e.val < k then
    some (if c = 0 then (E e).1.val else if c = (rowAt P k t e).length then (E e).2.val else sId n m e.val (c - 1))
  else if e.val = k ∧ c < (rowAt P k t e).length then
    some (if c = 0 then (E e).1.val else sId n m e.val (c - 1))
  else none

/-- **The assignment**: the partial vertex (id) whose branch set contains an aug vertex. -/
def asg : AV n m → Option ℕ
  | Sum.inl v => some v.val
  | Sum.inr (Sum.inl (p, q)) =>
    if p < q ∧ NonInc E p q then
      if q ∈ rowAt P k t p then some (xId n m p.val q.val) else segAsg P k t p (cnt P k t p ((P.π p).idxOf q))
    else none
  | Sum.inr (Sum.inr (e, j)) =>
    if j.val + 1 < (P.π e).length then segAsg P k t e (cnt P k t e (j.val + 1)) else none

theorem asg_ov (v : Fin n) : asg P k t (ov v : AV n m) = some v.val := rfl

theorem asg_xv_drawn {e g : Fin m} (hg : g ∈ rowAt P k t e) : asg P k t (xv e g : AV n m) = some (xId n m e g) := by
  have hgπ : g ∈ P.π e := (rowAt_sublist P k t e).subset hg
  have hne : g ≠ e := ne_of_mem_π P hgπ
  have hni : NonInc E e g := (P.mem e g).1 hgπ
  unfold xv
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_right h.le, max_eq_left h.le]
    simp only [asg]
    rw [ite_eq_left ⟨h, NonInc.symm' hni⟩, ite_eq_left ((mem_rowAt_symm P).1 hg), xId_comm]
  · rw [min_eq_left h.le, max_eq_right h.le]
    simp only [asg]
    rw [ite_eq_left ⟨h, hni⟩, ite_eq_left hg]

theorem asg_xv_undrawn {e g : Fin m} (hgπ : g ∈ P.π e) (hg : g ∉ rowAt P k t e) (heg : e < g) :
    asg P k t (xv e g : AV n m) = segAsg P k t e (cnt P k t e ((P.π e).idxOf g)) := by
  unfold xv
  rw [min_eq_left heg.le, max_eq_right heg.le]
  simp only [asg]
  rw [ite_eq_left ⟨heg, (P.mem e g).1 hgπ⟩, ite_eq_right hg]

theorem asg_sv (e : Fin m) (j : ℕ) (hj : j + 1 < (P.π e).length) :
    asg P k t (sv e j : AV n m) = segAsg P k t e (cnt P k t e (j + 1)) := by
  have hjm : j < m := by have := length_π_le P e; omega
  unfold sv
  simp only [asg, Nat.mod_eq_of_lt hjm]
  rw [ite_eq_left hj]

/-! ## The partial path `Q e` -/

variable (es : Array (ℕ × ℕ))

/-- The node list of the partial path of `e` (core `pathIds`). -/
def Q (e : Fin m) : List ℕ := pathIds n m es e.val ((rowAt P k t e).map Fin.val) (decide (e.val < k))

/-- The node at position `i` of the partial path of `e`. -/
def qnode (e : Fin m) (i : ℕ) : ℕ := (Q P k t es e).getD i 0

variable {es}

theorem qnode_of_getElem? {e : Fin m} {i x : ℕ} (h : (Q P k t es e)[i]? = some x) : qnode P k t es e i = x := by
  simp [qnode, List.getD_eq_getElem?_getD, h]

theorem Q_closed (hes : Matches es E) {e : Fin m} (he : e.val < k) :
    Q P k t es e = (E e).1.val :: (midIds n m e.val ((rowAt P k t e).map Fin.val) 0 ++ [(E e).2.val]) := by
  simp [Q, pathIds, he, hes.get e]

theorem Q_open (hes : Matches es E) {e : Fin m} (he : e.val = k) (hr : rowAt P k t e ≠ []) :
    Q P k t es e = (E e).1.val :: midIds n m e.val ((rowAt P k t e).map Fin.val) 0 := by
  have hnk : ¬ e.val < k := by omega
  simp [Q, pathIds, hnk, hes.get e, hr]

theorem Q_length_closed (hes : Matches es E) {e : Fin m} (he : e.val < k) :
    (Q P k t es e).length = if rowAt P k t e = [] then 2 else 2 * (rowAt P k t e).length + 1 := by
  rw [Q_closed P k t hes he]
  split_ifs with hr
  · simp [hr, midIds]
  · have hr' : (rowAt P k t e).map Fin.val ≠ [] := by simpa using hr
    have h1 := midIds_length n m e.val _ 0 hr'
    have h2 : 0 < (rowAt P k t e).length := List.length_pos_iff.2 hr
    simp only [List.length_cons, List.length_append, List.length_nil, h1, List.length_map]
    omega

theorem Q_length_open (hes : Matches es E) {e : Fin m} (he : e.val = k) (hr : rowAt P k t e ≠ []) :
    (Q P k t es e).length = 2 * (rowAt P k t e).length := by
  rw [Q_open P k t hes he hr]
  have hr' : (rowAt P k t e).map Fin.val ≠ [] := by simpa using hr
  have h1 := midIds_length n m e.val _ 0 hr'
  have h2 : 0 < (rowAt P k t e).length := List.length_pos_iff.2 hr
  simp only [List.length_cons, h1, List.length_map]
  omega

/-- The partial path of `e` is drawn: `e < k`, or `e = k` with a crossing. -/
def Drawn (e : Fin m) : Prop := e.val < k ∨ (e.val = k ∧ rowAt P k t e ≠ [])

theorem qnode_zero (hes : Matches es E) {e : Fin m} (hd : Drawn P k t e) : qnode P k t es e 0 = (E e).1.val := by
  apply qnode_of_getElem?
  rcases hd with he | ⟨he, hr⟩
  · rw [Q_closed P k t hes he]; rfl
  · rw [Q_open P k t hes he hr]; rfl

theorem qnode_odd (hes : Matches es E) {e : Fin m} (hd : Drawn P k t e) (a : ℕ) (ha : a < (rowAt P k t e).length) :
    qnode P k t es e (2 * a + 1) = xId n m e.val (rowAt P k t e)[a].val := by
  apply qnode_of_getElem?
  have hr : (rowAt P k t e).map Fin.val ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff]; exact List.ne_nil_of_length_pos (by omega)
  have h1 := midIds_length n m e.val _ 0 hr
  have hm := midIds_getElem?_even n m e.val ((rowAt P k t e).map Fin.val) 0 a (by simpa using ha)
  rcases hd with he | ⟨he, hr'⟩
  · rw [Q_closed P k t hes he, List.getElem?_cons_succ, List.getElem?_append_left (by simp at h1 ⊢; omega), hm]
    simp
  · rw [Q_open P k t hes he hr', List.getElem?_cons_succ, hm]
    simp

theorem qnode_even (hes : Matches es E) {e : Fin m} (hd : Drawn P k t e) (a : ℕ)
    (ha : a + 1 < (rowAt P k t e).length) : qnode P k t es e (2 * a + 2) = sId n m e.val a := by
  apply qnode_of_getElem?
  have hr : (rowAt P k t e).map Fin.val ≠ [] := by
    simp only [ne_eq, List.map_eq_nil_iff]; exact List.ne_nil_of_length_pos (by omega)
  have h1 := midIds_length n m e.val _ 0 hr
  have hm := midIds_getElem?_odd n m e.val ((rowAt P k t e).map Fin.val) 0 a (by simpa using ha)
  rcases hd with he | ⟨he, hr'⟩
  · rw [Q_closed P k t hes he, show 2 * a + 2 = (2 * a + 1) + 1 by ring, List.getElem?_cons_succ,
      List.getElem?_append_left (by simp at h1 ⊢; omega), hm]
    simp
  · rw [Q_open P k t hes he hr', show 2 * a + 2 = (2 * a + 1) + 1 by ring, List.getElem?_cons_succ, hm]
    simp

theorem qnode_last (hes : Matches es E) {e : Fin m} (he : e.val < k) (i : ℕ) (hi : i + 1 = (Q P k t es e).length) :
    qnode P k t es e i = (E e).2.val := by
  apply qnode_of_getElem?
  rw [Q_closed P k t hes he] at hi ⊢
  simp only [List.length_cons, List.length_append, List.length_nil] at hi
  rw [show i = (midIds n m e.val ((rowAt P k t e).map Fin.val) 0).length + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (le_refl _)]
  simp

/-- The partial vertex of `c` drawn crossings before, on a covered segment, is the node at position `2c`. -/
theorem segAsg_eq (hes : Matches es E) (e : Fin m) (c : ℕ)
    (hc : (e.val < k ∧ c ≤ (rowAt P k t e).length) ∨ (e.val = k ∧ c < (rowAt P k t e).length)) :
    segAsg P k t e c = some (qnode P k t es e (2 * c)) := by
  rcases hc with ⟨he, hcL⟩ | ⟨he, hcL⟩
  · have hd : Drawn P k t e := Or.inl he
    simp only [segAsg, ite_eq_left he]
    congr 1
    split_ifs with h0 hL
    · subst h0; exact (qnode_zero P k t hes hd).symm
    · symm
      apply qnode_last P k t hes he
      rw [Q_length_closed P k t hes he]
      have : rowAt P k t e ≠ [] := List.ne_nil_of_length_pos (by omega)
      rw [ite_eq_right this]; omega
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [show 2 * (c' + 1) = 2 * c' + 2 by ring, qnode_even P k t hes hd c' (by omega)]
      simp
  · have hr : rowAt P k t e ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hd : Drawn P k t e := Or.inr ⟨he, hr⟩
    simp only [segAsg, ite_eq_right (show ¬ e.val < k by omega), ite_eq_left (show e.val = k ∧ c < _ from ⟨he, hcL⟩)]
    congr 1
    split_ifs with h0
    · subst h0; exact (qnode_zero P k t hes hd).symm
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      rw [show 2 * (c' + 1) = 2 * c' + 2 by ring, qnode_even P k t hes hd c' (by omega)]
      simp

/-! ## Positions: `mu` and coverage -/

/-- The position on the partial path of `e` of the partial vertex owning the aug position `p`. -/
def mu (e : Fin m) (p : ℕ) : ℕ :=
  if e.val < k ∧ rowAt P k t e = [] ∧ p + 1 = (pathNodes E P e).length then 1
  else cnt P k t e (p / 2) + cnt P k t e ((p + 1) / 2)

/-- The aug position `p` of the path of `e` is covered by the partial path. -/
def Covered (e : Fin m) (p : ℕ) : Prop :=
  if e.val < k then p < (pathNodes E P e).length else e.val = k ∧ cnt P k t e (p / 2) < (rowAt P k t e).length

theorem pathNodes_length_ge (e : Fin m) : 2 ≤ (pathNodes E P e).length := by
  rw [pathNodes_length]
  split_ifs with h
  · exact le_refl 2
  · have := List.length_pos_iff.2 h; omega

theorem covered_lt {e : Fin m} {p : ℕ} (h : Covered P k t e p) : p < (pathNodes E P e).length := by
  unfold Covered at h
  split_ifs at h with he
  · exact h
  · obtain ⟨-, hc⟩ := h
    rw [pathNodes_length]
    by_cases hp : (P.π e).length ≤ p / 2
    · rw [cnt_of_le P k t e hp] at hc; omega
    · have : P.π e ≠ [] := List.ne_nil_of_length_pos (by omega)
      rw [ite_eq_right this]; omega

theorem covered_mono {e : Fin m} {p p' : ℕ} (h : Covered P k t e p) (hp : p' ≤ p) : Covered P k t e p' := by
  unfold Covered at h ⊢
  split_ifs at h ⊢ with he
  · omega
  · exact ⟨h.1, lt_of_le_of_lt (cnt_mono P k t e (by omega)) h.2⟩

theorem covered_drawn {e : Fin m} {p : ℕ} (h : Covered P k t e p) : Drawn P k t e := by
  unfold Covered at h
  split_ifs at h with he
  · exact Or.inl he
  · exact Or.inr ⟨h.1, List.ne_nil_of_length_pos (lt_of_le_of_lt (Nat.zero_le _) h.2)⟩

theorem mu_zero (e : Fin m) : mu P k t e 0 = 0 := by
  have := pathNodes_length_ge P e
  simp only [mu]
  rw [ite_eq_right (by omega)]
  simp [cnt_zero]

theorem mu_step (e : Fin m) (p : ℕ) (hp : p + 1 < (pathNodes E P e).length) :
    mu P k t e (p + 1) ≤ mu P k t e p + 1 ∧ mu P k t e p ≤ mu P k t e (p + 1) := by
  have h1 := cnt_succ_le P k t e (p / 2)
  have h2 := cnt_le_succ P k t e (p / 2)
  have hq : (p + 1 + 1) / 2 = p / 2 + 1 := by omega
  have hmp : mu P k t e p = cnt P k t e (p / 2) + cnt P k t e ((p + 1) / 2) := by
    unfold mu; rw [ite_eq_right (fun h => absurd h.2.2 (by omega))]
  rw [hmp]
  unfold mu
  split_ifs with hs
  · obtain ⟨-, hr, -⟩ := hs
    have hz : ∀ j, cnt P k t e j = 0 := fun j => by
      have := cnt_le_length P k t e j; rw [hr] at this; simpa using this
    simp [hz]
  · rw [hq]; omega

/-- The node of a covered aug position belongs to the branch set of `qnode e (mu e p)`. -/
theorem asg_node (hes : Matches es E) (e : Fin m) (p : ℕ) (hp : Covered P k t e p) :
    asg P k t (node P e p) = some (qnode P k t es e (mu P k t e p)) := by
  have hlt := covered_lt P k t hp
  have hd := covered_drawn P k t hp
  by_cases hlast : p + 1 = (pathNodes E P e).length
  · -- the head: only on a closed edge
    have he : e.val < k := by
      unfold Covered at hp
      split_ifs at hp with he
      · exact he
      · exfalso
        obtain ⟨-, hc⟩ := hp
        rw [pathNodes_length] at hlast
        split_ifs at hlast with hπ
        · have : (rowAt P k t e).length = 0 := by
            have := (rowAt_sublist P k t e).length_le; rw [hπ] at this; simpa using this
          omega
        · rw [cnt_of_le P k t e (by omega)] at hc; omega
    rw [node_last P e p hlast, asg_ov]
    congr 1
    symm
    apply qnode_last P k t hes he
    rw [Q_length_closed P k t hes he]
    unfold mu
    split_ifs with hs hr hr
    · simp [hr]
    · exact absurd hs.2.1 hr
    · exact absurd ⟨he, hr, hlast⟩ hs
    · rw [pathNodes_length] at hlast
      have hπ : P.π e ≠ [] := fun h => hr (by
        have := (rowAt_sublist P k t e).length_le; rw [h] at this; simpa using this)
      rw [ite_eq_right hπ] at hlast
      rw [show p / 2 = (P.π e).length by omega, show (p + 1) / 2 = (P.π e).length by omega,
        cnt_of_le P k t e (le_refl _)]
      omega
  · have hlt' : p + 1 < (pathNodes E P e).length := by omega
    have hmu : mu P k t e p = cnt P k t e (p / 2) + cnt P k t e ((p + 1) / 2) := by
      unfold mu; rw [ite_eq_right (by omega)]
    have hπ : p ≠ 0 → P.π e ≠ [] := by
      intro hp0 h
      rw [pathNodes_length, ite_eq_left h] at hlt'; omega
    rcases Nat.even_or_odd' p with ⟨j, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [hmu, show 2 * 0 = 0 by rfl, node_zero, asg_ov, cnt_zero, qnode_zero P k t hes hd]
      · -- a subdivision vertex
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hπ' := hπ (by omega)
        rw [pathNodes_length, ite_eq_right hπ'] at hlt'
        have hj' : j' + 1 < (P.π e).length := by omega
        rw [show 2 * (j' + 1) = 2 * j' + 2 by ring] at hmu hp ⊢
        rw [node_even P e j' hj', asg_sv P k t e j' hj', hmu, show (2 * j' + 2) / 2 = j' + 1 by omega,
          show (2 * j' + 2 + 1) / 2 = j' + 1 by omega, ← two_mul]
        apply segAsg_eq P k t hes
        unfold Covered at hp
        split_ifs at hp with he
        · exact Or.inl ⟨he, cnt_le_length P k t e _⟩
        · rw [show (2 * j' + 2) / 2 = j' + 1 by omega] at hp
          exact Or.inr hp
    · -- a crossing
      have hπ' := hπ (by omega)
      rw [pathNodes_length, ite_eq_right hπ'] at hlt'
      have hj : j < (P.π e).length := by omega
      rw [hmu, show (2 * j + 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega,
        cnt_succ P k t e j hj, node_odd P e j hj]
      by_cases hg : (P.π e)[j] ∈ rowAt P k t e
      · rw [ite_eq_left hg, asg_xv_drawn P k t hg]
        have hcL : cnt P k t e j < (rowAt P k t e).length := by
          have h1 := cnt_succ P k t e j hj
          rw [ite_eq_left hg] at h1
          have := cnt_le_length P k t e (j + 1); omega
        rw [show cnt P k t e j + (cnt P k t e j + 1) = 2 * cnt P k t e j + 1 by ring,
          qnode_odd P k t hes hd _ hcL, rowAt_getElem_cnt P k t e j hj hg hcL]
      · rw [ite_eq_right hg, Nat.add_zero, ← two_mul]
        have hgπ : (P.π e)[j] ∈ P.π e := List.getElem_mem hj
        have hlt_g : e < (P.π e)[j] := by
          unfold Covered at hp
          split_ifs at hp with he
          · have := le_of_not_mem_rowAt P he hgπ hg
            show e.val < ((P.π e)[j]).val; omega
          · obtain ⟨he', hc⟩ := hp
            rw [show (2 * j + 1) / 2 = j by omega] at hc
            obtain ⟨jy, hjy, hy, hcy⟩ := exists_pos_of_lt P k t e _ hc
            have hyR : (rowAt P k t e)[cnt P k t e j] ∈ rowAt P k t e := List.getElem_mem hc
            have hjjy : j < jy := by
              by_contra hcon
              rcases Nat.lt_or_ge jy j with h | h
              · have h1 := cnt_succ P k t e jy hjy
                rw [hy, ite_eq_left hyR] at h1
                have := cnt_mono P k t e (show jy + 1 ≤ j by omega)
                omega
              · have : jy = j := by omega
                subst this
                exact hg (hy ▸ hyR)
            have := lt_of_not_mem_rowAt_open P he' hgπ hg hyR (by
              rw [(P.nodup e).idxOf_getElem j hj, ← hy, (P.nodup e).idxOf_getElem jy hjy]; exact hjjy)
            show e.val < ((P.π e)[j]).val; omega
        rw [asg_xv_undrawn P k t hgπ hg hlt_g, (P.nodup e).idxOf_getElem j hj]
        apply segAsg_eq P k t hes
        unfold Covered at hp
        split_ifs at hp with he
        · exact Or.inl ⟨he, cnt_le_length P k t e _⟩
        · rw [show (2 * j + 1) / 2 = j by omega] at hp
          exact Or.inr hp

/-- The partial path is covered up to its last node. -/
theorem exists_cover_end (hes : Matches es E) (e : Fin m) (hd : Drawn P k t e) :
    ∃ D, Covered P k t e D ∧ mu P k t e D + 1 = (Q P k t es e).length := by
  rcases hd with he | ⟨he, hr⟩
  · refine ⟨(pathNodes E P e).length - 1, ?_, ?_⟩
    · have := pathNodes_length_ge P e
      unfold Covered; rw [ite_eq_left he]; omega
    · have hlen := pathNodes_length_ge P e
      rw [Q_length_closed P k t hes he]
      unfold mu
      split_ifs with hs hr hr
      · rfl
      · exact absurd hs.2.1 hr
      · exact absurd ⟨he, hr, by omega⟩ hs
      · have hπ : P.π e ≠ [] := fun h => hr (by
          have := (rowAt_sublist P k t e).length_le; rw [h] at this; simpa using this)
        have hl := pathNodes_length P e
        rw [ite_eq_right hπ] at hl
        rw [hl, show (2 * (P.π e).length + 1 - 1) / 2 = (P.π e).length by omega,
          show (2 * (P.π e).length + 1 - 1 + 1) / 2 = (P.π e).length by omega, cnt_of_le P k t e (le_refl _)]
        omega
  · have hL : 0 < (rowAt P k t e).length := List.length_pos_iff.2 hr
    obtain ⟨j, hj, hy, hcj⟩ := exists_pos_of_lt P k t e ((rowAt P k t e).length - 1) (by omega)
    have hyR : (P.π e)[j] ∈ rowAt P k t e := hy ▸ List.getElem_mem (by omega)
    refine ⟨2 * j + 1, ?_, ?_⟩
    · unfold Covered
      rw [ite_eq_right (by omega), show (2 * j + 1) / 2 = j by omega, hcj]
      exact ⟨he, by omega⟩
    · rw [Q_length_open P k t hes he hr]
      unfold mu
      rw [ite_eq_right (by omega), show (2 * j + 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega,
        cnt_succ P k t e j hj, ite_eq_left hyR, hcj]
      omega

end Thrackle78.Checker
