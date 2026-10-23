import Thrackle78.Defs
import Thrackle78Core.Search
import Thrackle78.Checker.Lists

/-!
# Restrictions of a crossing system to the states of the search

For a crossing system `P` of `E`, `rowAt P k t e` is the row of edge `e` at stage `(k, t)`: the edges `e < k` are drawn
completely (crossings with the drawn edges, in the order of `P`), edge `k` has crossed its first `t` earlier partners
(in its own order). `Restr P k t rows` says that the core rows `rows` are these rows. The empty state is the
restriction at stage `(0, 0)` (`restr_root`), closing edge `k` gives stage `(k + 1, 0)` (`restr_close`), and some child
of a state with `t <` (number of earlier partners) is the restriction at stage `(k, t + 1)` (`restr_child`).
-/

namespace Thrackle78.Checker

open Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- The core listing `es` (pairs of naturals) is the listing `E`. -/
structure Matches (es : Array (ℕ × ℕ)) (E : Fin m → Fin n × Fin n) : Prop where
  size : es.size = m
  get : ∀ i : Fin m, es.getD i.val (0, 0) = ((E i).1.val, (E i).2.val)

theorem nonInc_iff {es : Array (ℕ × ℕ)} (hes : Matches es E) (e f : Fin m) :
    nonInc es e.val f.val = true ↔ NonInc E e f := by
  unfold nonInc NonInc
  rw [hes.get e, hes.get f]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Fin.val_inj]
  tauto

theorem NonInc.symm' {e f : Fin m} (h : NonInc E e f) : NonInc E f e := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨Ne.symm h1, Ne.symm h2, Ne.symm h4, Ne.symm h3, Ne.symm h5⟩

variable (P : CrossingSystem E)

theorem mem_π_symm {e f : Fin m} : f ∈ P.π e ↔ e ∈ P.π f := by
  rw [P.mem, P.mem]; exact ⟨NonInc.symm', NonInc.symm'⟩

theorem ne_of_mem_π {e f : Fin m} (h : f ∈ P.π e) : f ≠ e := fun hfe => ((P.mem e f).1 h).1 hfe.symm

/-- The earlier partners of edge `k`, in crossing order along `k`. -/
def earlier (k : Fin m) : List (Fin m) := (P.π k).filter (fun f => decide (f < k))

/-- The crossing row of edge `e` at stage `(k, t)`: the edges `e < k` are drawn, edge `k` has crossed its first `t`
earlier partners. -/
def rowAt (k t : ℕ) (e : Fin m) : List (Fin m) :=
  if e.val < k then (P.π e).filter (fun f => decide (f.val < k ∨ (f.val = k ∧ e ∈ (earlier P f).take t)))
  else if e.val = k then (earlier P e).take t else []

theorem mem_earlier {k f : Fin m} : f ∈ earlier P k ↔ f ∈ P.π k ∧ f < k := by
  simp [earlier]

theorem earlier_nodup (k : Fin m) : (earlier P k).Nodup := (P.nodup k).filter _

theorem rowAt_sublist (k t : ℕ) (e : Fin m) : (rowAt P k t e).Sublist (P.π e) := by
  unfold rowAt
  split_ifs
  · exact List.filter_sublist
  · exact (List.take_sublist _ _).trans List.filter_sublist
  · exact List.nil_sublist _

theorem rowAt_nodup (k t : ℕ) (e : Fin m) : (rowAt P k t e).Nodup := (P.nodup e).sublist (rowAt_sublist P k t e)

theorem rowAt_of_lt {k t : ℕ} {e : Fin m} (he : k < e.val) : rowAt P k t e = [] := by
  unfold rowAt
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem mem_rowAt_lt {k t : ℕ} {e f : Fin m} (he : e.val < k) :
    f ∈ rowAt P k t e ↔ f ∈ P.π e ∧ (f.val < k ∨ (f.val = k ∧ e ∈ (earlier P f).take t)) := by
  unfold rowAt
  rw [ite_eq_left he]
  simp

theorem mem_rowAt_eq {k t : ℕ} {e f : Fin m} (he : e.val = k) : f ∈ rowAt P k t e ↔ f ∈ (earlier P e).take t := by
  unfold rowAt
  rw [ite_eq_right (by omega), ite_eq_left he]

/-- Crossings are symmetric in every restriction. -/
theorem mem_rowAt_symm {k t : ℕ} {e f : Fin m} : f ∈ rowAt P k t e ↔ e ∈ rowAt P k t f := by
  have key : ∀ e f : Fin m, e.val < k → f.val = k → (f ∈ rowAt P k t e ↔ e ∈ rowAt P k t f) := by
    intro e f he hf
    rw [mem_rowAt_lt P he, mem_rowAt_eq P hf]
    constructor
    · rintro ⟨-, h | ⟨-, h⟩⟩
      · omega
      · exact h
    · intro h
      have he' : e ∈ P.π f := ((mem_earlier P).1 (List.mem_of_mem_take h)).1
      exact ⟨(mem_π_symm P).2 he', Or.inr ⟨hf, h⟩⟩
  have hne : ∀ e f : Fin m, e.val = k → f.val = k → ¬ f ∈ rowAt P k t e := by
    intro e f he hf h
    rw [mem_rowAt_eq P he] at h
    have := ((mem_earlier P).1 (List.mem_of_mem_take h)).2
    have : f.val < e.val := this
    omega
  have hgt : ∀ e f : Fin m, k < e.val → ¬ e ∈ rowAt P k t f := by
    intro e f he h
    rcases lt_trichotomy f.val k with hf | hf | hf
    · rw [mem_rowAt_lt P hf] at h
      rcases h.2 with h' | ⟨h', -⟩ <;> omega
    · rw [mem_rowAt_eq P hf] at h
      have := ((mem_earlier P).1 (List.mem_of_mem_take h)).2
      have : e.val < f.val := this
      omega
    · rw [rowAt_of_lt P hf] at h
      simp at h
  rcases lt_trichotomy e.val k with he | he | he
  · rcases lt_trichotomy f.val k with hf | hf | hf
    · rw [mem_rowAt_lt P he, mem_rowAt_lt P hf, mem_π_symm P]
      constructor
      · rintro ⟨h, -⟩; exact ⟨h, Or.inl he⟩
      · rintro ⟨h, -⟩; exact ⟨h, Or.inl hf⟩
    · exact key e f he hf
    · exact iff_of_false (hgt f e hf) (by rw [rowAt_of_lt P hf]; simp)
  · rcases lt_trichotomy f.val k with hf | hf | hf
    · exact (key f e hf he).symm
    · exact iff_of_false (hne e f he hf) (hne f e hf he)
    · exact iff_of_false (hgt f e hf) (by rw [rowAt_of_lt P hf]; simp)
  · exact iff_of_false (by rw [rowAt_of_lt P he]; simp) (hgt e f he)

theorem le_of_mem_rowAt {k t : ℕ} {e f : Fin m} (h : f ∈ rowAt P k t e) : e.val ≤ k ∧ f.val ≤ k := by
  have h1 : ∀ e f : Fin m, f ∈ rowAt P k t e → e.val ≤ k := by
    intro e f h
    by_contra hc
    rw [rowAt_of_lt P (by omega)] at h
    simp at h
  exact ⟨h1 e f h, h1 f e ((mem_rowAt_symm P).1 h)⟩

/-- On a drawn edge `e < k`, the crossings that are not drawn are with edges `≥ k`. -/
theorem le_of_not_mem_rowAt {k t : ℕ} {e g : Fin m} (he : e.val < k) (hg : g ∈ P.π e) (hn : g ∉ rowAt P k t e) :
    k ≤ g.val := by
  by_contra hc
  exact hn ((mem_rowAt_lt P he).2 ⟨hg, Or.inl (by omega)⟩)

theorem mem_take_iff_idxOf_lt {α : Type} [DecidableEq α] {l : List α} (hl : l.Nodup) {x : α} (hx : x ∈ l) (t : ℕ) :
    x ∈ l.take t ↔ l.idxOf x < t := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, hix⟩
    have hi' : i < l.length := by omega
    have : l.idxOf x = i := by
      rw [← hix]; exact hl.idxOf_getElem i hi'
    omega
  · intro h
    have hlt : l.idxOf x < l.length := List.idxOf_lt_length_iff.2 hx
    exact ⟨l.idxOf x, by simp [h, hlt], List.getElem_idxOf hlt⟩

theorem countP_take_lt {α : Type} (p : α → Bool) {l : List α} {i j : ℕ} (hij : i < j) (hj : j ≤ l.length)
    (hp : p (l[i]'(by omega)) = true) : (l.take i).countP p < (l.take j).countP p := by
  have h1 : l.take j = l.take i ++ (l.drop i).take (j - i) := by
    conv_lhs => rw [show j = i + (j - i) by omega]
    rw [List.take_add]
  rw [h1, List.countP_append]
  have h2 : 0 < ((l.drop i).take (j - i)).countP p := by
    rw [List.countP_pos_iff]
    refine ⟨l[i]'(by omega), ?_, hp⟩
    rw [List.mem_take_iff_getElem]
    refine ⟨0, by simp; omega, by simp⟩
  omega

/-- On the open edge `k`, an undrawn crossing before a drawn one is with an edge `> k`. -/
theorem lt_of_not_mem_rowAt_open {k t : ℕ} {e g y : Fin m} (he : e.val = k) (hg : g ∈ P.π e)
    (hn : g ∉ rowAt P k t e) (hy : y ∈ rowAt P k t e) (hgy : (P.π e).idxOf g < (P.π e).idxOf y) : k < g.val := by
  have hgk : g.val ≠ k := fun h => ne_of_mem_π P hg (Fin.ext (h.trans he.symm))
  by_contra hc
  have hglt : g < e := by
    show g.val < e.val; omega
  apply hn
  rw [mem_rowAt_eq P he] at hy ⊢
  have hyE : y ∈ earlier P e := List.mem_of_mem_take hy
  have hgE : g ∈ earlier P e := (mem_earlier P).2 ⟨hg, hglt⟩
  rw [mem_take_iff_idxOf_lt (earlier_nodup P e) hyE] at hy
  rw [mem_take_iff_idxOf_lt (earlier_nodup P e) hgE]
  have hyπ : y ∈ P.π e := ((mem_earlier P).1 hyE).1
  have hyp : decide (y < e) = true := by simpa using ((mem_earlier P).1 hyE).2
  have hgp : decide (g < e) = true := by simpa using hglt
  unfold earlier at hy ⊢
  rw [idxOf_filter _ (P.nodup e) hyπ hyp] at hy
  rw [idxOf_filter _ (P.nodup e) hg hgp]
  have hylt : (P.π e).idxOf y ≤ (P.π e).length := (List.idxOf_lt_length_iff.2 hyπ).le
  have := countP_take_lt (fun f => decide (f < e)) hgy hylt (by
    rw [List.getElem_idxOf]; exact hgp)
  omega

/-! ## Core rows -/

/-- The core rows `rows` are the restriction of `P` to stage `(k, t)`. -/
def Restr (k t : ℕ) (rows : Array (List ℕ)) : Prop :=
  rows.size = m ∧ k ≤ m ∧ (∀ hk : k < m, t ≤ (earlier P ⟨k, hk⟩).length) ∧
    ∀ e : Fin m, rows.getD e.val [] = (rowAt P k t e).map Fin.val

theorem restr_root : Restr P 0 0 (Array.replicate m []) := by
  refine ⟨by simp, Nat.zero_le _, fun _ => Nat.zero_le _, fun e => ?_⟩
  have : rowAt P 0 0 e = [] := by
    unfold rowAt
    split_ifs <;> simp
  rw [this]
  simp [Array.getD, e.isLt]

theorem numEarlier_eq {es : Array (ℕ × ℕ)} (hes : Matches es E) (k : Fin m) :
    numEarlier es k.val = (earlier P k).length := by
  unfold numEarlier
  rw [← List.length_map (f := Fin.val)]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) ((earlier_nodup P k).map Fin.val_injective)]
  intro x
  simp only [List.mem_filter, List.mem_range, List.mem_map, mem_earlier]
  constructor
  · rintro ⟨hx, hnx⟩
    have hxm : x < m := lt_trans hx k.isLt
    refine ⟨⟨x, hxm⟩, ⟨(P.mem k _).2 ((nonInc_iff hes k ⟨x, hxm⟩).1 hnx), hx⟩, rfl⟩
  · rintro ⟨f, ⟨hf, hfk⟩, rfl⟩
    exact ⟨hfk, (nonInc_iff hes k f).2 ((P.mem k f).1 hf)⟩

theorem length_rowAt_open {k t : ℕ} (hk : k < m) (ht : t ≤ (earlier P ⟨k, hk⟩).length) :
    (rowAt P k t ⟨k, hk⟩).length = t := by
  rw [rowAt, ite_eq_right (by simp), ite_eq_left rfl, List.length_take]
  omega

/-- Closing edge `k`. -/
theorem restr_close {es : Array (ℕ × ℕ)} (hes : Matches es E) {k t : ℕ} {rows : Array (List ℕ)}
    (h : Restr P k t rows) (hk : k < m) (hlen : (rows.getD k []).length = numEarlier es k) :
    Restr P (k + 1) 0 rows := by
  obtain ⟨hsz, -, ht, hrows⟩ := h
  have hrk := hrows ⟨k, hk⟩
  have htl : t = (earlier P ⟨k, hk⟩).length := by
    rw [hrk, List.length_map, length_rowAt_open P hk (ht hk), numEarlier_eq P hes ⟨k, hk⟩] at hlen
    exact hlen
  refine ⟨hsz, hk, fun _ => Nat.zero_le _, fun e => ?_⟩
  rw [hrows e]
  congr 1
  rcases lt_trichotomy e.val k with he | he | he
  · rw [rowAt, rowAt, ite_eq_left he, ite_eq_left (by omega)]
    apply List.filter_congr
    intro f hf
    rw [decide_eq_decide]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
    · rintro (h | ⟨-, h'⟩)
      · rcases Nat.lt_or_ge f.val k with h' | h'
        · exact Or.inl h'
        · have hfk : f = ⟨k, hk⟩ := Fin.ext (show f.val = k by omega)
          subst hfk
          refine Or.inr ⟨rfl, ?_⟩
          rw [htl, List.take_length, mem_earlier]
          exact ⟨(mem_π_symm P).1 hf, he⟩
      · simp at h'
  · have hek : e = ⟨k, hk⟩ := Fin.ext he
    subst hek
    rw [rowAt, rowAt, ite_eq_right (by simp), ite_eq_left rfl, ite_eq_left (by simp), htl, List.take_length, earlier]
    apply List.filter_congr
    intro f hf
    have hfe : f.val ≠ k := fun h => ne_of_mem_π P hf (Fin.ext h)
    rw [decide_eq_decide]
    show f.val < k ↔ (f.val < k + 1 ∨ (f.val = k + 1 ∧ (⟨k, hk⟩ : Fin m) ∈ (earlier P f).take 0))
    constructor
    · intro h; exact Or.inl (by omega)
    · rintro (h | ⟨-, h'⟩)
      · omega
      · simp at h'
  · rw [rowAt_of_lt P he]
    unfold rowAt
    rw [ite_eq_right (by omega)]
    split_ifs <;> simp

/-- Crossing the next earlier partner: some child of the state is the restriction at stage `(k, t + 1)`. -/
theorem restr_child {es : Array (ℕ × ℕ)} (hes : Matches es E) {k t : ℕ} {rows : Array (List ℕ)}
    (h : Restr P k t rows) (hk : k < m) (hlen : (rows.getD k []).length ≠ numEarlier es k) :
    ∃ r ∈ children es k rows, Restr P k (t + 1) r := by
  obtain ⟨hsz, -, ht, hrows⟩ := h
  set kk : Fin m := ⟨k, hk⟩ with hkk
  have hrk := hrows kk
  have htl : t < (earlier P kk).length := by
    rw [hrk, List.length_map, length_rowAt_open P hk (ht hk), numEarlier_eq P hes kk] at hlen
    exact lt_of_le_of_ne (ht hk) hlen
  set g := (earlier P kk)[t] with hg
  have hgE : g ∈ earlier P kk := List.getElem_mem htl
  have hgπ : g ∈ P.π kk := ((mem_earlier P).1 hgE).1
  have hgk : g < kk := ((mem_earlier P).1 hgE).2
  have hgk' : g.val < k := hgk
  have hgt : g ∉ (earlier P kk).take t := by
    rw [mem_take_iff_idxOf_lt (earlier_nodup P kk) hgE, hg, (earlier_nodup P kk).idxOf_getElem t htl]
    omega
  have hgt1 : (earlier P kk).take (t + 1) = (earlier P kk).take t ++ [g] := by
    rw [List.take_add_one, List.getElem?_eq_getElem htl]
    rfl
  have hkπ : kk ∈ P.π g := (mem_π_symm P).1 hgπ
  -- the old and the new row of `g`
  have hold : rowAt P k t g = (P.π g).filter (fun f => decide (f.val < k)) := by
    rw [rowAt, ite_eq_left hgk']
    apply List.filter_congr
    intro f hf
    simp only [decide_eq_decide]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact h
      · have : f = kk := Fin.ext h1
        subst this; exact absurd h2 hgt
    · exact Or.inl
  set p := ((P.π g).take ((P.π g).idxOf kk)).countP (fun f => decide (f.val < k)) with hp
  have hnew : rowAt P k (t + 1) g =
      ((P.π g).filter (fun f => decide (f.val < k))).take p ++ kk ::
        ((P.π g).filter (fun f => decide (f.val < k))).drop p := by
    rw [← filter_or_eq_insert (fun f => decide (f.val < k)) (P.nodup g) hkπ (by simp [hkk])]
    rw [rowAt, ite_eq_left hgk']
    apply List.filter_congr
    intro f hf
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨h1, -⟩)
      · exact Or.inl h
      · exact Or.inr (Fin.ext h1)
    · rintro (h | h)
      · exact Or.inl h
      · subst h
        refine Or.inr ⟨rfl, ?_⟩
        rw [hgt1]; simp
  have hpl : p ≤ ((P.π g).filter (fun f => decide (f.val < k))).length := by
    rw [hp, ← List.countP_eq_length_filter]
    exact (List.take_sublist _ _).countP_le
  have hrg := hrows g
  rw [hold] at hrg
  refine ⟨(rows.set! k (rows.getD k [] ++ [g.val])).set! g.val
      ((rows.getD g.val []).take p ++ k :: (rows.getD g.val []).drop p), ?_, ?_⟩
  · unfold children
    rw [List.mem_flatMap]
    refine ⟨g.val, List.mem_range.2 hgk', ?_⟩
    have hni : nonInc es k g.val = true := (nonInc_iff hes kk g).2 ((P.mem kk g).1 hgπ)
    have hnc : (rows.getD k []).contains g.val = false := by
      rw [hrk]
      simp only [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map]
      rintro ⟨f, hf, hfg⟩
      have : f = g := Fin.ext hfg
      subst this
      rw [rowAt, ite_eq_right (by simp [hkk]), ite_eq_left rfl] at hf
      exact hgt hf
    rw [hni, hnc]
    simp only [Bool.not_false, Bool.and_self, ite_true, List.mem_map, List.mem_range]
    refine ⟨p, ?_, rfl⟩
    rw [hrg, List.length_map]
    omega
  · refine ⟨by simp [hsz], hk.le, fun _ => show t + 1 ≤ (earlier P kk).length by omega, fun e => ?_⟩
    rw [getD_set!_eq, getD_set!_eq]
    simp only [Array.size_set!, hsz, e.isLt, and_true]
    by_cases heg : g.val = e.val
    · have : e = g := Fin.ext heg.symm
      subst this
      rw [ite_eq_left rfl, hrg, hnew]
      simp [List.map_take, List.map_drop, hkk]
    · rw [ite_eq_right heg]
      by_cases hek : k = e.val
      · have : e = kk := Fin.ext hek.symm
        subst this
        rw [ite_eq_left rfl, hrk, rowAt, rowAt, ite_eq_right (lt_irrefl k), ite_eq_left rfl, ite_eq_right (lt_irrefl k), ite_eq_left rfl, hgt1]
        simp
      · rw [ite_eq_right hek, hrows e]
        congr 1
        rcases lt_trichotomy e.val k with he | he | he
        · rw [rowAt, rowAt, ite_eq_left he, ite_eq_left he]
          apply List.filter_congr
          intro f _
          rw [decide_eq_decide]
          by_cases hfk : f.val = k
          · have : f = kk := Fin.ext hfk
            subst this
            rw [hgt1, List.mem_append, List.mem_singleton]
            have : e ≠ g := fun h => heg (congrArg Fin.val h).symm
            simp [this]
          · simp [hfk]
        · exact absurd he.symm hek
        · rw [rowAt_of_lt P he, rowAt_of_lt P he]

end Thrackle78.Checker
