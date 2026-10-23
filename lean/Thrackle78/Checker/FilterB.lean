import Thrackle78Core.FilterB
import Thrackle78.Checker.OracleWalk

/-!
# Soundness of the bitset filters

* `testBit_maskOf`, `getD_masksOf`, `testBit_allOf`: the masks are the bitsets of the precedences;
* `testBit_stepMask`: the bit of the restriction of a crossing system survives every crossing step it extends;
* `walkB_sound`, `not_combThr_mkE_of_checkB`, `not_combThr_mkE_of_shardsB`.
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78Core

/-! ## Masks -/

theorem testBit_bitsDC (p : ℕ → Bool) : ∀ (len lo j : ℕ),
    (bitsDC p lo len).testBit j = (decide (j < len) && p (lo + j))
  | 0, lo, j => by simp [bitsDC]
  | 1, lo, j => by
    rw [bitsDC]
    by_cases hj : j = 0
    · subst hj
      split_ifs with hp <;> simp [hp]
    · have : decide (j < 1) = false := by simp; omega
      rw [this, Bool.false_and]
      split_ifs
      · rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow]; simp; omega
      · simp
  | len + 2, lo, j => by
    rw [bitsDC, Nat.testBit_lor, Nat.testBit_shiftLeft,
      testBit_bitsDC p ((len + 2) / 2) lo j,
      testBit_bitsDC p (len + 2 - (len + 2) / 2) (lo + (len + 2) / 2) (j - (len + 2) / 2)]
    by_cases hj : j < (len + 2) / 2
    · have h0 : decide (j < (len + 2) / 2) = true := by simp; omega
      have h1 : decide (j ≥ (len + 2) / 2) = false := by simp; omega
      have h2 : decide (j < len + 2) = true := by simp; omega
      rw [h0, h1, h2]
      simp only [Bool.true_and, Bool.false_and, Bool.or_false]
    · have h1 : decide (j < (len + 2) / 2) = false := by simp; omega
      have h2 : decide (j ≥ (len + 2) / 2) = true := by simp; omega
      rw [h1, h2, show lo + (len + 2) / 2 + (j - (len + 2) / 2) = lo + j by omega]
      simp only [Bool.false_and, Bool.false_or, Bool.true_and]
      congr 1
      simp only [decide_eq_decide]
      omega
termination_by len => len
decreasing_by all_goals omega

theorem toArray_getD {α : Type} (l : List α) (s : ℕ) (d : α) : l.toArray.getD s d = l.getD s d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem testBit_maskOf (S : List (List (List ℕ))) (i x y s : ℕ) :
    (maskOf S i x y).testBit s = (decide (s < S.length) && precB ((S.getD s []).getD i []) x y) := by
  unfold maskOf maskOfA
  rw [testBit_bitsDC, Nat.zero_add, toArray_getD, List.size_toArray]

theorem getD_masksOf (S : List (List (List ℕ))) {h i x y : ℕ} (hi : i < h) (hx : x < h) (hy : y < h) :
    (masksOf S h).getD ((i * h + x) * h + y) 0 = maskOf S i x y := by
  have hlt : (i * h + x) * h + y < h * h * h := by
    have h1 : i * h + x < h * h := by
      calc i * h + x < i * h + h := by omega
        _ = (i + 1) * h := by ring
        _ ≤ h * h := Nat.mul_le_mul_right h hi
    calc (i * h + x) * h + y < (i * h + x) * h + h := by omega
      _ = (i * h + x + 1) * h := by ring
      _ ≤ h * h * h := Nat.mul_le_mul_right h h1
  have hpos : 0 < h := by omega
  unfold masksOf maskOf
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some]
  congr 1
  · rw [show (i * h + x) * h + y = y + (i * h + x) * h by ring, show h * h = h * h by rfl]
    rw [show y + (i * h + x) * h = (y + x * h) + i * (h * h) by ring, Nat.add_mul_div_right _ _ (by positivity)]
    have : y + x * h < h * h := by
      calc y + x * h < h + x * h := by omega
        _ = (x + 1) * h := by ring
        _ ≤ h * h := Nat.mul_le_mul_right h hx
    rw [Nat.div_eq_of_lt this, Nat.zero_add]
  · rw [show (i * h + x) * h + y = y + (i * h + x) * h by ring, Nat.add_mul_div_right _ _ hpos,
      Nat.div_eq_of_lt hy, Nat.zero_add, show i * h + x = x + i * h by ring, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hx]
  · rw [show (i * h + x) * h + y = y + (i * h + x) * h by ring, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

theorem testBit_allOf (S : List (List (List ℕ))) (s : ℕ) : (allOf S).testBit s = decide (s < S.length) := by
  unfold allOf
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]

/-! ## Precedences -/

theorem precB_iff {l : List ℕ} {x y : ℕ} : precB l x y = true ↔ x ∈ l ∧ y ∈ l ∧ l.idxOf x < l.idxOf y := by
  simp [precB, List.contains_iff_mem, and_assoc]

theorem precB_of_sublist {l l' : List ℕ} (hs : l'.Sublist l) (hnd : l.Nodup) {x y : ℕ} (h : precB l' x y = true) :
    precB l x y = true := by
  rw [precB_iff] at h ⊢
  obtain ⟨hx, hy, hxy⟩ := h
  refine ⟨hs.subset hx, hs.subset hy, ?_⟩
  have hnd' := hnd.sublist hs
  have e1 := filter_mem_eq_of_sublist hs hnd
  have hxl := hs.subset hx
  have hyl := hs.subset hy
  rw [← e1, idxOf_filter _ hnd hxl (by simpa using hx), idxOf_filter _ hnd hyl (by simpa using hy)] at hxy
  by_contra hc
  have hle : l.idxOf y ≤ l.idxOf x := by omega
  have := (List.take_sublist_take_left (l := l) hle).countP_le (p := fun z => decide (z ∈ l'))
  omega

theorem precB_filter {l : List ℕ} (hnd : l.Nodup) (q : ℕ → Bool) {x y : ℕ} (h : precB l x y = true)
    (hx : q x = true) (hy : q y = true) : precB (l.filter q) x y = true := by
  rw [precB_iff] at h ⊢
  obtain ⟨hxl, hyl, hxy⟩ := h
  refine ⟨List.mem_filter.2 ⟨hxl, hx⟩, List.mem_filter.2 ⟨hyl, hy⟩, ?_⟩
  rw [idxOf_filter _ hnd hxl hx, idxOf_filter _ hnd hyl hy]
  have h1 : l.take (l.idxOf y) = l.take (l.idxOf x) ++ (l.drop (l.idxOf x)).take (l.idxOf y - l.idxOf x) := by
    conv_lhs => rw [show l.idxOf y = l.idxOf x + (l.idxOf y - l.idxOf x) by omega]
    rw [List.take_add]
  rw [h1, List.countP_append]
  have hpos : 0 < ((l.drop (l.idxOf x)).take (l.idxOf y - l.idxOf x)).countP q := by
    rw [List.countP_pos_iff]
    refine ⟨x, ?_, hx⟩
    have hxlt : l.idxOf x < l.length := List.idxOf_lt_length_iff.2 hxl
    rw [List.mem_take_iff_getElem]
    refine ⟨0, by simp; omega, ?_⟩
    simp [List.getElem_idxOf]
  omega

theorem precB_map {l : List ℕ} (f : ℕ → ℕ) (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) {x y : ℕ}
    (h : precB l x y = true) : precB (l.map f) (f x) (f y) = true := by
  rw [precB_iff] at h ⊢
  obtain ⟨hxl, hyl, hxy⟩ := h
  refine ⟨List.mem_map_of_mem hxl, List.mem_map_of_mem hyl, ?_⟩
  have key : ∀ z ∈ l, (l.map f).idxOf (f z) = l.idxOf z := by
    intro z hz
    clear hxy hxl hyl
    induction l with
    | nil => simp at hz
    | cons a l ih =>
      by_cases haz : a = z
      · subst haz; simp [List.idxOf_cons]
      · have hfa : f a ≠ f z := fun e => haz (hf a (by simp) z hz e)
        rw [List.map_cons, List.idxOf_cons_ne _ hfa, List.idxOf_cons_ne _ haz]
        rcases List.mem_cons.1 hz with rfl | hz'
        · exact absurd rfl haz
        · rw [ih (fun a' ha' b' hb' e => hf a' (List.mem_cons_of_mem _ ha') b' (List.mem_cons_of_mem _ hb') e) hz']
  rw [key x hxl, key y hyl]
  exact hxy

/-! ## Children with their crossing data -/

theorem children_eq_map (es : Array (ℕ × ℕ)) (k : ℕ) (rows : Array (List ℕ)) :
    children es k rows = (childrenFP es k rows).map (·.2.2) := by
  unfold children childrenFP
  rw [List.map_flatMap]
  congr 1
  funext f
  split_ifs
  · rw [List.map_map]; rfl
  · rfl

theorem mem_childrenFP {es : Array (ℕ × ℕ)} {k : ℕ} {rows : Array (List ℕ)} {c : ℕ × ℕ × Array (List ℕ)}
    (hc : c ∈ childrenFP es k rows) :
    c.1 < k ∧ nonInc es k c.1 = true ∧ c.1 ∉ rows.getD k [] ∧ c.2.1 ≤ (rows.getD c.1 []).length ∧
      c.2.2 = (rows.set! k (rows.getD k [] ++ [c.1])).set! c.1
        ((rows.getD c.1 []).take c.2.1 ++ k :: (rows.getD c.1 []).drop c.2.1) := by
  unfold childrenFP at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨f, hf, hc⟩ := hc
  rw [List.mem_range] at hf
  split_ifs at hc with hcond
  · rw [List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    rw [List.mem_range] at hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
    have h2 : f ∉ rows.getD k [] := fun hm => by
      rw [List.contains_iff_mem.2 hm] at hcond; exact absurd hcond.2 (by simp)
    exact ⟨hf, hcond.1, h2, show p ≤ (rows.getD f []).length by omega, rfl⟩
  · simp at hc

/-! ## The step lemma -/

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

theorem πN_nodup (P : CrossingSystem E) (e : ℕ) : (πN P e).Nodup := by
  unfold πN
  split_ifs with he
  · exact (P.nodup _).map Fin.val_injective
  · exact List.nodup_nil

theorem rows_sublist_πN (P : CrossingSystem E) {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows) {e : ℕ}
    (he : e < m) : (rows.getD e []).Sublist (πN P e) := by
  rw [hr.2.2.2 ⟨e, he⟩, πN_of_lt P he]
  exact (rowAt_sublist P k t _).map _

theorem labOf_inj {g : List ℕ} {a b : ℕ} (ha : a ∈ g) (hb : b ∈ g) (h : labOf g a = labOf g b) : a = b := by
  rw [← getD_labOf ha, ← getD_labOf hb, h]

theorem rowsH_getD (P : CrossingSystem E) {g : List ℕ} {f : ℕ} (hf : f ∈ g) :
    (rowsH P g).getD (labOf g f) [] = ((πN P f).filter (fun x => g.contains x)).map (labOf g) := by
  have hl : labOf g f < g.length := List.idxOf_lt_length_iff.2 hf
  unfold rowsH
  rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_range, getD_labOf hf]

/-- A precedence on the complete row of `e` gives the precedence of the H-indices in the restriction to `H`. -/
theorem precB_rowsH (P : CrossingSystem E) {g : List ℕ} {e x y : ℕ} (he : e ∈ g) (hx : x ∈ g) (hy : y ∈ g)
    (h : precB (πN P e) x y = true) :
    precB ((rowsH P g).getD (labOf g e) []) (labOf g x) (labOf g y) = true := by
  rw [rowsH_getD P he]
  apply precB_map
  · intro a ha b hb hab
    exact labOf_inj (List.contains_iff_mem.1 (List.mem_filter.1 ha).2)
      (List.contains_iff_mem.1 (List.mem_filter.1 hb).2) hab
  · exact precB_filter (πN_nodup P e) _ h (List.contains_iff_mem.2 hx) (List.contains_iff_mem.2 hy)

theorem precB_append_left {l₁ l₂ : List ℕ} (hnd : (l₁ ++ l₂).Nodup) {x y : ℕ} (hx : x ∈ l₁) (hy : y ∈ l₂) :
    precB (l₁ ++ l₂) x y = true := by
  rw [precB_iff]
  refine ⟨List.mem_append_left _ hx, List.mem_append_right _ hy, ?_⟩
  rw [List.idxOf_append_of_mem hx]
  have hyl : y ∉ l₁ := fun h' => (List.nodup_append.1 hnd).2.2 y h' y hy rfl
  have : (l₁ ++ l₂).idxOf y = l₁.length + l₂.idxOf y := by
    clear hx
    induction l₁ with
    | nil => simp
    | cons a l ih =>
      have hay : a ≠ y := fun e => hyl (e ▸ List.mem_cons_self)
      rw [List.cons_append, List.idxOf_cons_ne _ hay, ih (List.nodup_cons.1 hnd).2 (fun h' => hyl
        (List.mem_cons_of_mem _ h'))]
      simp; omega
  rw [this]
  have := List.idxOf_lt_length_iff.2 hx
  omega

theorem testBit_mask_of_prec {S : List (List (List ℕ))} {h i x y s : ℕ} (hi : i < h) (hx : x < h) (hy : y < h)
    (hs : s < S.length) (hp : precB ((S.getD s []).getD i []) x y = true) :
    ((masksOf S h).getD ((i * h + x) * h + y) 0).testBit s = true := by
  rw [getD_masksOf S hi hx hy, testBit_maskOf, hp]
  simp [hs]

theorem labOf_lt {g : List ℕ} {x : ℕ} (hx : x ∈ g) : labOf g x < g.length := List.idxOf_lt_length_iff.2 hx

/-- **The step lemma**: the bit of the restriction of `P` survives every crossing step that `P` extends. -/
theorem testBit_stepMask {es : Array (ℕ × ℕ)} (hes : Matches es E) (P : CrossingSystem E) {k t : ℕ}
    {rows : Array (List ℕ)} (hk : k < m) (hr : Restr P k t rows) {c : ℕ × ℕ × Array (List ℕ)}
    (hc : c ∈ childrenFP es k rows) (hr' : Restr P k (t + 1) c.2.2) {g : List ℕ}
    (S : List (List (List ℕ))) {s : ℕ} (hs : s < S.length) (hS : S.getD s [] = rowsH P g) :
    (stepMask es g (masksOf S g.length) (allOf S) k c.1 c.2.1 rows).testBit s = true := by
  obtain ⟨hfk, hni, hfrk, hp, hbuild⟩ := mem_childrenFP hc
  have hall : (allOf S).testBit s = true := by rw [testBit_allOf]; simpa using hs
  unfold stepMask
  split_ifs with hcond
  swap
  · exact hall
  rw [Bool.and_eq_true, List.contains_iff_mem, List.contains_iff_mem] at hcond
  obtain ⟨hkg, hfg⟩ := hcond
  set f := c.1 with hf_def
  set p := c.2.1 with hp_def
  have hfm : f < m := lt_trans hfk hk
  have hsz : rows.size = m := hr.1
  -- the child rows of `f` and `k`
  have hrowf : c.2.2.getD f [] = (rows.getD f []).take p ++ k :: (rows.getD f []).drop p := by
    rw [hbuild, getD_set!_eq, ite_eq_left ⟨rfl, by simp [hsz, hfm]⟩]
  have hrowk : c.2.2.getD k [] = rows.getD k [] ++ [f] := by
    rw [hbuild, getD_set!_eq, ite_eq_right (fun h' => (Nat.ne_of_lt hfk) h'.1), getD_set!_eq,
      ite_eq_left ⟨rfl, by rw [hsz]; exact hk⟩]
  have hsubf := rows_sublist_πN P hr' hfm
  have hsubk := rows_sublist_πN P hr' hk
  rw [hrowf] at hsubf
  rw [hrowk] at hsubk
  have hndf := (πN_nodup P f).sublist hsubf
  have hndk := (πN_nodup P k).sublist hsubk
  have hS' : ∀ i, (S.getD s []).getD i [] = (rowsH P g).getD i [] := fun i => by rw [hS]
  have hkl := labOf_lt hkg
  have hfl := labOf_lt hfg
  simp only [Nat.testBit_land, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the last H-partner before position `p` on `f` comes before `k`
    rcases ha : (((rows.getD f []).take p).filter g.contains).getLast? with _ | a
    · exact hall
    · have ha' := List.mem_filter.1 (List.mem_of_getLast? ha)
      have hag := List.contains_iff_mem.1 ha'.2
      refine testBit_mask_of_prec hfl (labOf_lt hag) hkl hs ?_
      rw [hS']
      exact precB_rowsH P hfg hag hkg (precB_of_sublist hsubf (πN_nodup P f)
        (precB_append_left hndf ha'.1 List.mem_cons_self))
  · -- `k` comes before the first H-partner after position `p` on `f`
    rcases hb : (((rows.getD f []).drop p).filter g.contains).head? with _ | b
    · exact hall
    · have hb' := List.mem_filter.1 (List.mem_of_mem_head? hb)
      have hbg := List.contains_iff_mem.1 hb'.2
      refine testBit_mask_of_prec hfl hkl (labOf_lt hbg) hs ?_
      rw [hS']
      have heq : (rows.getD f []).take p ++ k :: (rows.getD f []).drop p =
          ((rows.getD f []).take p ++ [k]) ++ (rows.getD f []).drop p := by simp
      rw [heq] at hsubf hndf
      exact precB_rowsH P hfg hkg hbg (precB_of_sublist hsubf (πN_nodup P f)
        (precB_append_left hndf (by simp) hb'.1))
  · -- on `k`, the last H-partner crossed comes before `f`
    rcases hy : ((rows.getD k []).filter g.contains).getLast? with _ | y
    · exact hall
    · have hy' := List.mem_filter.1 (List.mem_of_getLast? hy)
      have hyg := List.contains_iff_mem.1 hy'.2
      refine testBit_mask_of_prec hkl (labOf_lt hyg) hfl hs ?_
      rw [hS']
      exact precB_rowsH P hkg hyg hfg (precB_of_sublist hsubk (πN_nodup P k)
        (precB_append_left hndk hy'.1 (by simp)))
  · -- on `k`, `f` comes before every earlier H-partner not crossed yet
    have hq : ∀ q ∈ (List.range k).filter (fun q => nonInc es k q && !(rows.getD k []).contains q && q != f &&
        g.contains q), q ∈ g ∧ precB ((S.getD s []).getD (labOf g k) []) (labOf g f) (labOf g q) = true := by
      intro q hqmem
      rw [List.mem_filter, List.mem_range] at hqmem
      obtain ⟨hqk, hqc⟩ := hqmem
      simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hqc
      obtain ⟨⟨⟨hqni, hqrk⟩, hqf⟩, hqg⟩ := hqc
      have hqg' := List.contains_iff_mem.1 hqg
      have hqrk' : q ∉ rows.getD k [] := fun hm => by rw [List.contains_iff_mem.2 hm] at hqrk; simp at hqrk
      have hqm : q < m := lt_trans hqk hk
      set kk : Fin m := ⟨k, hk⟩ with hkk
      have hrk' : c.2.2.getD k [] = ((earlier P kk).take (t + 1)).map Fin.val := by
        rw [hr'.2.2.2 kk, rowAt, ite_eq_right (lt_irrefl k), ite_eq_left rfl]
      rw [hrowk] at hrk'
      set L := (earlier P kk).map Fin.val with hL
      have hLnd : L.Nodup := (earlier_nodup P kk).map Fin.val_injective
      have hfL : f ∈ L.take (t + 1) := by
        rw [hL, ← List.map_take, ← hrk']; simp
      have hqL : q ∈ L := by
        rw [hL, List.mem_map]
        refine ⟨⟨q, hqm⟩, (mem_earlier P).2 ⟨(P.mem kk _).2 ((nonInc_iff hes kk ⟨q, hqm⟩).1 hqni), hqk⟩, rfl⟩
      have hqL' : q ∉ L.take (t + 1) := by
        rw [hL, ← List.map_take, ← hrk']
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hqrk', hqf⟩
      have hprec : precB L f q = true := by
        rw [precB_iff]
        refine ⟨List.mem_of_mem_take hfL, hqL, ?_⟩
        rw [mem_take_iff_idxOf_lt hLnd (List.mem_of_mem_take hfL)] at hfL
        rw [mem_take_iff_idxOf_lt hLnd hqL] at hqL'
        omega
      have hLsub : L.Sublist (πN P k) := by
        rw [hL, πN_of_lt P hk, earlier]
        exact List.filter_sublist.map _
      rw [hS']
      exact ⟨hqg', precB_rowsH P hkg hfg hqg' (precB_of_sublist hLsub (πN_nodup P k) hprec)⟩
    generalize ((List.range k).filter (fun q => nonInc es k q && !(rows.getD k []).contains q && q != f &&
      g.contains q)) = qs at hq
    suffices h : ∀ (qs' : List ℕ) (acc : ℕ), (∀ q ∈ qs', q ∈ g ∧ precB ((S.getD s []).getD (labOf g k) [])
        (labOf g f) (labOf g q) = true) → acc.testBit s = true →
        (qs'.foldl (fun acc q => acc &&& (masksOf S g.length).getD ((labOf g k * g.length + labOf g f) * g.length +
          labOf g q) 0) acc).testBit s = true from h qs _ hq hall
    intro qs'
    induction qs' with
    | nil => intro acc _ hacc; exact hacc
    | cons q qs' ih =>
      intro acc hq' hacc
      rw [List.foldl_cons]
      apply ih _ (fun q' hq'' => hq' q' (List.mem_cons_of_mem _ hq''))
      rw [Nat.testBit_land, hacc, Bool.true_and]
      obtain ⟨hqg, hpq⟩ := hq' q List.mem_cons_self
      exact testBit_mask_of_prec hkl hfl (labOf_lt hqg) hs hpq

/-! ## The bitset walk -/

/-- The bitsets contain the restriction of `P` to each filter, when it is listed. -/
def AliveB (P : CrossingSystem E) (fs : List Filt) (alive : List ℕ) : Prop :=
  ∀ i < fs.length, ∀ s < (fs.getD i ⟨[], []⟩).sys.length,
    (fs.getD i ⟨[], []⟩).sys.getD s [] = rowsH P (fs.getD i ⟨[], []⟩).g → (alive.getD i 0).testBit s = true

theorem prepB_getD (fs : List Filt) {i : ℕ} (hi : i < fs.length) :
    (fs.map prepB).getD i ⟨[], [], #[], 0⟩ = prepB (fs.getD i ⟨[], []⟩) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- **Soundness of the oracle search with bitset filters.** -/
theorem walkB_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt)
    (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle) :
    ∀ fuel k rows alive, walkB n es (fs.map prepB) orc fuel k rows alive = true →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → AliveB P fs alive → ¬ Planar (aug E P)
  | 0, _, _, _, hw => by simp [walkB] at hw
  | fuel + 1, k, rows, alive, hw => by
    intro P t hr ha
    simp only [walkB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, List.length_map] at hw
    rcases hw with (⟨i, hi, hzero⟩ | horc) | ⟨hk, hw⟩
    · obtain ⟨-, hsound⟩ := hfs _ (getD_mem_of_lt ⟨[], []⟩ hi)
      rcases hsound P with hnp | hmem
      · exact hnp
      · exfalso
        obtain ⟨s, hs, hseq⟩ := List.getElem_of_mem hmem
        have := ha i hi s hs (by rw [List.getD_eq_getElem _ _ hs]; exact hseq)
        rw [hzero, Nat.zero_testBit] at this
        exact absurd this (by simp)
    · exact not_planar_of_oracleOK P hes hr horc
    · have hk' : k < m := hes.size ▸ hk
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkB_sound hes fs hfs orc fuel (k + 1) rows _ hw P 0 (restr_close P hes hr hk' h8) ha
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        rw [children_eq_map, List.mem_map] at hr'
        obtain ⟨c, hc, rfl⟩ := hr'
        refine walkB_sound hes fs hfs orc fuel k c.2.2 _ (hw c hc) P (t + 1) hres ?_
        intro i hi s hs hseq
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
          Nat.testBit_land, ha i hi s hs hseq, Bool.true_and, prepB_getD fs hi]
        exact testBit_stepMask hes P hk' hr hc hres _ hs hseq

theorem testBit_bitsOf (p : ℕ → Bool) (N s : ℕ) : (bitsOf p N).testBit s = (decide (s < N) && p s) := by
  unfold bitsOf
  rw [testBit_bitsDC, Nat.zero_add]

theorem aliveB_compat (P : CrossingSystem E) (fs : List Filt) (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ)
    {k t : ℕ} {rows : Array (List ℕ)} (hr : Restr P k t rows) :
    AliveB P fs (fs.map fun φ => compatMask φ k rows) := by
  intro i hi s hs hseq
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, compatMask, testBit_bitsOf]
  simp only [toArray_getD, List.size_toArray]
  obtain ⟨hval, -⟩ := hfs _ (getD_mem_of_lt ⟨[], []⟩ hi)
  unfold Filt.valid at hval
  rw [Bool.and_eq_true, nodupB_iff, List.all_eq_true] at hval
  rw [List.getD_eq_getElem _ _ hi] at hs hseq hval
  rw [hseq, compat_rowsH P hr hval.1 (fun x hx => by simpa using hval.2 x hx)]
  simpa using hs

theorem stateSound_of_checkBFrom {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt)
    (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle) {k : ℕ} {rows : Array (List ℕ)}
    (h : checkBFrom n es fs orc k rows = true) : StateSound E k rows := fun P t hr =>
  walkB_sound hes fs hfs orc _ k rows _ h P t hr (aliveB_compat P fs hfs hr)

/-- **The oracle search with bitset filters proves `¬ CombThr (mkE n l)`.** -/
theorem not_combThr_mkE_of_checkB (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (h : checkB n l.toArray fs orcF = true) : ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  unfold checkB at h
  rw [Bool.and_eq_true] at h
  exact not_combThr_of_rootSound hes
    (stateSound_of_checkBFrom hes _ (filtSound_list hes fs orcF h.1) (orcF l.toArray) h.2)

/-- **Sharded oracle search with bitset filters.** -/
theorem not_combThr_mkE_of_shardsB (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (hf : fs.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true)
    (L : List (ℕ × Array (List ℕ))) (d : ℕ)
    (htop : walkS l.toArray L d 0 (Array.replicate l.length []) = true)
    (hsh : ∀ s ∈ L, checkBFrom n l.toArray (fs.map Prod.fst) (orcF l.toArray) s.1 s.2 = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list hes fs orcF hf
  apply not_combThr_of_rootSound hes
  have := walkS_sound hes L (fun s hs => stateSound_of_checkBFrom hes _ hfs _ (hsh s hs)) d 0 _
    (by simpa using htop)
  simpa using this

end Thrackle78.Checker

namespace Thrackle78.Checker

open Thrackle78Core

theorem filtSound_list_data {n m : ℕ} {E : Fin m → Fin n × Fin n} {es : Array (ℕ × ℕ)} (hes : Matches es E)
    (fs : List (Filt × ReaderX)) (h : fs.all (fun φr => checkFilter n es φr.1 φr.2) = true) :
    ∀ φ ∈ fs.map Prod.fst, φ.valid m = true ∧ FiltSound E φ := by
  rw [List.all_eq_true] at h
  intro φ hφ
  rw [List.mem_map] at hφ
  obtain ⟨φr, hmem, hφr⟩ := hφ
  rw [← hφr]
  exact filtSound_of_checkFilter hes φr.1 φr.2 (h φr hmem)

/-- **The oracle search with bitset filters (filter trees from data) proves `¬ CombThr (mkE n l)`.** -/
theorem not_combThr_mkE_of_checkBD (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × ReaderX)) (orc : Oracle) (h : checkBD n l.toArray fs orc = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  unfold checkBD at h
  rw [Bool.and_eq_true] at h
  exact not_combThr_of_rootSound hes
    (stateSound_of_checkBFrom hes _ (filtSound_list_data hes fs h.1) orc h.2)

/-- **Sharded oracle search with bitset filters (filter trees from data).** -/
theorem not_combThr_mkE_of_shardsBD (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × ReaderX)) (orc : Oracle)
    (hf : fs.all (fun φr => checkFilter n l.toArray φr.1 φr.2) = true)
    (L : List (ℕ × Array (List ℕ))) (d : ℕ)
    (htop : walkS l.toArray L d 0 (Array.replicate l.length []) = true)
    (hsh : ∀ s ∈ L, checkBFrom n l.toArray (fs.map Prod.fst) orc s.1 s.2 = true) : ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list_data hes fs hf
  apply not_combThr_of_rootSound hes
  have := walkS_sound hes L (fun s hs => stateSound_of_checkBFrom hes _ hfs orc (hsh s hs)) d 0 _
    (by simpa using htop)
  simpa using this

end Thrackle78.Checker

namespace Thrackle78.Checker

open Thrackle78Core

theorem stateSound_of_checkBFromList {n m : ℕ} {E : Fin m → Fin n × Fin n} {es : Array (ℕ × ℕ)}
    (hes : Matches es E) (fs : List Filt) (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle)
    {L : List (ℕ × Array (List ℕ))} (h : checkBFromList n es fs orc L = true) :
    ∀ s ∈ L, StateSound E s.1 s.2 := by
  unfold checkBFromList at h
  rw [List.all_eq_true] at h
  intro s hs P t hr
  exact walkB_sound hes fs hfs orc _ s.1 s.2 _ (h s hs) P t hr (aliveB_compat P fs hfs hr)

/-- **Sharded oracle search with bitset filters, by batches of shard roots** (masks computed once per batch). -/
theorem not_combThr_mkE_of_batchesB (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (hf : fs.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true)
    (Ls : List (List (ℕ × Array (List ℕ)))) (d : ℕ)
    (htop : walkS l.toArray Ls.flatten d 0 (Array.replicate l.length []) = true)
    (hsh : ∀ L ∈ Ls, checkBFromList n l.toArray (fs.map Prod.fst) (orcF l.toArray) L = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list hes fs orcF hf
  apply not_combThr_of_rootSound hes
  have := walkS_sound hes Ls.flatten (fun s hs => by
      obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
      exact stateSound_of_checkBFromList hes _ hfs _ (hsh L hL) s hsL) d 0 _ (by simpa using htop)
  simpa using this

/-- **Sharded oracle search with bitset filters (filter trees from data), by batches of shard roots.** -/
theorem not_combThr_mkE_of_batchesBD (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × ReaderX)) (orc : Oracle)
    (hf : fs.all (fun φr => checkFilter n l.toArray φr.1 φr.2) = true)
    (Ls : List (List (ℕ × Array (List ℕ)))) (d : ℕ)
    (htop : walkS l.toArray Ls.flatten d 0 (Array.replicate l.length []) = true)
    (hsh : ∀ L ∈ Ls, checkBFromList n l.toArray (fs.map Prod.fst) orc L = true) : ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list_data hes fs hf
  apply not_combThr_of_rootSound hes
  have := walkS_sound hes Ls.flatten (fun s hs => by
      obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
      exact stateSound_of_checkBFromList hes _ hfs orc (hsh L hL) s hsL) d 0 _ (by simpa using htop)
  simpa using this

end Thrackle78.Checker

namespace Thrackle78.Checker

open Thrackle78Core

variable {n m : ℕ} {E : Fin m → Fin n × Fin n}

/-- **Soundness of the top of a sharded search**: delegated states are sound by hypothesis. -/
theorem walkBS_sound {es : Array (ℕ × ℕ)} (hes : Matches es E) (fs : List Filt)
    (hfs : ∀ φ ∈ fs, φ.valid m = true ∧ FiltSound E φ) (orc : Oracle) (LA : Array (ℕ × Array (List ℕ)))
    (look : ℕ × Array (List ℕ) → ℕ) (hL : ∀ s ∈ LA.toList, StateSound E s.1 s.2) :
    ∀ fuel k rows alive, walkBS n es (fs.map prepB) orc LA look fuel k rows alive = true →
      ∀ (P : CrossingSystem E) (t : ℕ), Restr P k t rows → AliveB P fs alive → ¬ Planar (aug E P)
  | 0, _, _, _, hw => by simp [walkBS] at hw
  | fuel + 1, k, rows, alive, hw => by
    intro P t hr ha
    simp only [walkBS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      beq_iff_eq, List.length_map] at hw
    rcases hw with (((⟨hi, heq⟩ | ⟨i, hi, hzero⟩) | horc) | ⟨hk, hw⟩)
    · have hmem : (k, rows) ∈ LA.toList := by
        rw [← heq, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
        exact Array.getElem_mem_toList hi
      exact hL _ hmem P t hr
    · obtain ⟨-, hsound⟩ := hfs _ (getD_mem_of_lt ⟨[], []⟩ hi)
      rcases hsound P with hnp | hmem
      · exact hnp
      · exfalso
        obtain ⟨s, hs, hseq⟩ := List.getElem_of_mem hmem
        have := ha i hi s hs (by rw [List.getD_eq_getElem _ _ hs]; exact hseq)
        rw [hzero, Nat.zero_testBit] at this
        exact absurd this (by simp)
    · exact not_planar_of_oracleOK P hes hr horc
    · have hk' : k < m := hes.size ▸ hk
      by_cases h8 : (rows.getD k []).length = numEarlier es k
      · rw [ite_eq_left h8] at hw
        exact walkBS_sound hes fs hfs orc LA look hL fuel (k + 1) rows _ hw P 0 (restr_close P hes hr hk' h8) ha
      · rw [ite_eq_right h8, List.all_eq_true] at hw
        obtain ⟨r', hr', hres⟩ := restr_child P hes hr hk' h8
        rw [children_eq_map, List.mem_map] at hr'
        obtain ⟨c, hc, rfl⟩ := hr'
        refine walkBS_sound hes fs hfs orc LA look hL fuel k c.2.2 _ (hw c hc) P (t + 1) hres ?_
        intro i hi s hs hseq
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
          Nat.testBit_land, ha i hi s hs hseq, Bool.true_and, prepB_getD fs hi]
        exact testBit_stepMask hes P hk' hr hc hres _ hs hseq

/-- **Sharded oracle search with bitset filters, pruned top tree**: the top search reaches only shard states of
`LA` (or prunes), and every batch of shard states passes. -/
theorem not_combThr_mkE_of_topB (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × (List (List ℕ) → ℕ))) (orcF : Array (ℕ × ℕ) → Oracle)
    (hf : fs.all (fun φl => checkFilterO n l.toArray φl.1 φl.2 orcF) = true)
    (Ls : List (List (ℕ × Array (List ℕ)))) (look : ℕ × Array (List ℕ) → ℕ)
    (htop : checkTop n l.toArray (fs.map Prod.fst) (orcF l.toArray) Ls.flatten.toArray look = true)
    (hsh : ∀ L ∈ Ls, checkBFromList n l.toArray (fs.map Prod.fst) (orcF l.toArray) L = true) :
    ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list hes fs orcF hf
  have hL : ∀ s ∈ Ls.flatten.toArray.toList, StateSound (mkE n l) s.1 s.2 := by
    intro s hs
    rw [List.toList_toArray] at hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
    exact stateSound_of_checkBFromList hes _ hfs _ (hsh L hL) s hsL
  apply not_combThr_of_rootSound hes
  intro P t hr
  exact walkBS_sound hes _ hfs _ _ look hL _ 0 _ _ htop P t hr (aliveB_compat P _ hfs hr)

/-- The same with the filter trees certified by data. -/
theorem not_combThr_mkE_of_topBD (n : ℕ) [NeZero n] (l : List (ℕ × ℕ)) (hl : ∀ p ∈ l, p.1 < n ∧ p.2 < n)
    (fs : List (Filt × ReaderX)) (orc : Oracle)
    (hf : fs.all (fun φr => checkFilter n l.toArray φr.1 φr.2) = true)
    (Ls : List (List (ℕ × Array (List ℕ)))) (look : ℕ × Array (List ℕ) → ℕ)
    (htop : checkTop n l.toArray (fs.map Prod.fst) orc Ls.flatten.toArray look = true)
    (hsh : ∀ L ∈ Ls, checkBFromList n l.toArray (fs.map Prod.fst) orc L = true) : ¬ CombThr (mkE n l) := by
  have hes := matches_mkE n l hl
  have hfs := filtSound_list_data hes fs hf
  have hL : ∀ s ∈ Ls.flatten.toArray.toList, StateSound (mkE n l) s.1 s.2 := by
    intro s hs
    rw [List.toList_toArray] at hs
    obtain ⟨L, hL, hsL⟩ := List.mem_flatten.1 hs
    exact stateSound_of_checkBFromList hes _ hfs orc (hsh L hL) s hsL
  apply not_combThr_of_rootSound hes
  intro P t hr
  exact walkBS_sound hes _ hfs orc _ look hL _ 0 _ _ htop P t hr (aliveB_compat P _ hfs hr)

end Thrackle78.Checker
