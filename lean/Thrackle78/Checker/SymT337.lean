import Thrackle78.Checker.FilterAut
import Thrackle78.Checker.FilterBQ
import Thrackle78.Theta

/-!
# The symmetries of `theta(3,3,7)` (listing `lTH337` as run)

The Klein four-group of `theta(3,3,7)` with poles `0` and `3`:
* `a` swaps the paths `A = 0-1-2-3` and `B = 0-4-5-3` (vertices `1 ↔ 4`, `2 ↔ 5`; edges `0 ↔ 3`, `1 ↔ 4`, `2 ↔ 5`; no
  edge reversed);
* `b` swaps the poles (vertices `0 ↔ 3`, `1 ↔ 2`, `4 ↔ 5`, `6 ↔ 11`, `7 ↔ 10`, `8 ↔ 9`; every edge reversed);
* `ab = a ∘ b` (every edge reversed).
Every planar crossing system has planar images under them (`planar_aut`). The member of the orbit whose restriction to
`RT337 = [0, 1, 2, 3, 4, 5, 9]` is least is canonical for all three at once (`hsymT337`): the symmetry hypothesis of
the symmetry-reduced search. Filters transfer along `a` (`filtSound_autT337a`).
-/

namespace Thrackle78.Checker

open SimpleGraph Thrackle78 Thrackle78Core

/-- The edges whose rows are compared. -/
def RT337 : List ℕ := [0, 1, 2, 3, 4, 5, 9]

/-- The edge map of `a` (an involution of `0 … 12`, the identity beyond). -/
def σaT : ℕ → ℕ
  | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 0 | 4 => 1 | 5 => 2 | e => e

/-- The edge map of `b`. -/
def σbT : ℕ → ℕ
  | 0 => 2 | 2 => 0 | 3 => 5 | 5 => 3 | 6 => 12 | 7 => 11 | 8 => 10 | 10 => 8 | 11 => 7 | 12 => 6 | e => e

/-- The edge map of `ab`. -/
def σabT : ℕ → ℕ
  | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0 | 6 => 12 | 7 => 11 | 8 => 10 | 10 => 8 | 11 => 7
  | 12 => 6 | e => e

/-- The edges reversed by `a` (none), `b` and `ab` (all). -/
def faT : ℕ → Bool := fun _ => false
def fbT : ℕ → Bool := fun _ => true
def fabT : ℕ → Bool := fun _ => true

/-- The vertex maps. -/
def τaT : ℕ → ℕ
  | 1 => 4 | 2 => 5 | 4 => 1 | 5 => 2 | v => v
def τbT : ℕ → ℕ
  | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 5 | 5 => 4 | 6 => 11 | 7 => 10 | 8 => 9 | 9 => 8 | 10 => 7 | 11 => 6
  | v => v
def τabT : ℕ → ℕ
  | 0 => 3 | 1 => 5 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 1 | 6 => 11 | 7 => 10 | 8 => 9 | 9 => 8 | 10 => 7 | 11 => 6
  | v => v

lemma lTH337_length : lTH337.length = 13 := rfl

/-! ## Involutions of the edges and of the vertices -/

/-- An involution of the edges `0 … 12`. -/
structure EInv (σ : ℕ → ℕ) : Prop where
  lt : ∀ e, e < 13 → σ e < 13
  inv : ∀ e, σ (σ e) = e

/-- An involution of the vertices `0 … 11`. -/
structure VInv (τ : ℕ → ℕ) : Prop where
  lt : ∀ v, v < 12 → τ v < 12
  inv : ∀ v, v < 12 → τ (τ v) = v

/-- The edge involution as a permutation of the edges of `lTH337`. -/
def eEquiv (σ : ℕ → ℕ) (h : EInv σ) : Fin lTH337.length ≃ Fin lTH337.length where
  toFun e := ⟨σ e.val, (h.lt _ (lt_of_lt_of_eq e.isLt lTH337_length) : σ e.val < 13)⟩
  invFun e := ⟨σ e.val, (h.lt _ (lt_of_lt_of_eq e.isLt lTH337_length) : σ e.val < 13)⟩
  left_inv e := Fin.ext (h.inv e.val)
  right_inv e := Fin.ext (h.inv e.val)

/-- The vertex involution as a permutation of the vertices. -/
def vEquiv (τ : ℕ → ℕ) (h : VInv τ) : Fin 12 ≃ Fin 12 where
  toFun v := ⟨τ v.val, h.lt _ v.isLt⟩
  invFun v := ⟨τ v.val, h.lt _ v.isLt⟩
  left_inv v := Fin.ext (h.inv _ v.isLt)
  right_inv v := Fin.ext (h.inv _ v.isLt)

lemma σaT_big {e : ℕ} (h : 13 ≤ e) : σaT e = e := by
  unfold σaT; split <;> omega

lemma σbT_big {e : ℕ} (h : 13 ≤ e) : σbT e = e := by
  unfold σbT; split <;> omega

lemma σabT_big {e : ℕ} (h : 13 ≤ e) : σabT e = e := by
  unfold σabT; split <;> omega

theorem einvA : EInv σaT :=
  ⟨fun e he => by interval_cases e <;> decide, fun e => by
    rcases Nat.lt_or_ge e 13 with h | h
    · interval_cases e <;> rfl
    · rw [σaT_big h, σaT_big h]⟩

theorem einvB : EInv σbT :=
  ⟨fun e he => by interval_cases e <;> decide, fun e => by
    rcases Nat.lt_or_ge e 13 with h | h
    · interval_cases e <;> rfl
    · rw [σbT_big h, σbT_big h]⟩

theorem einvAB : EInv σabT :=
  ⟨fun e he => by interval_cases e <;> decide, fun e => by
    rcases Nat.lt_or_ge e 13 with h | h
    · interval_cases e <;> rfl
    · rw [σabT_big h, σabT_big h]⟩

theorem vinvA : VInv τaT :=
  ⟨fun v hv => by interval_cases v <;> decide, fun v hv => by interval_cases v <;> rfl⟩

theorem vinvB : VInv τbT :=
  ⟨fun v hv => by interval_cases v <;> decide, fun v hv => by interval_cases v <;> rfl⟩

theorem vinvAB : VInv τabT :=
  ⟨fun v hv => by interval_cases v <;> decide, fun v hv => by interval_cases v <;> rfl⟩

/-- `a` is an automorphism of the listing. -/
theorem isAutA : IsAut (mkE 12 lTH337) (eEquiv σaT einvA) (vEquiv τaT vinvA) (fun e => faT e.val) := by
  unfold IsAut
  decide

/-- `b` is an automorphism of the listing. -/
theorem isAutB : IsAut (mkE 12 lTH337) (eEquiv σbT einvB) (vEquiv τbT vinvB) (fun e => fbT e.val) := by
  unfold IsAut
  decide

/-- `ab` is an automorphism of the listing. -/
theorem isAutAB : IsAut (mkE 12 lTH337) (eEquiv σabT einvAB) (vEquiv τabT vinvAB) (fun e => fabT e.val) := by
  unfold IsAut
  decide

lemma RT337_σa (f : ℕ) : RT337.contains (σaT f) = RT337.contains f := by
  rcases Nat.lt_or_ge f 13 with h | h
  · interval_cases f <;> rfl
  · rw [σaT_big h]

lemma RT337_σb (f : ℕ) : RT337.contains (σbT f) = RT337.contains f := by
  rcases Nat.lt_or_ge f 13 with h | h
  · interval_cases f <;> rfl
  · rw [σbT_big h]

lemma RT337_σab (f : ℕ) : RT337.contains (σabT f) = RT337.contains f := by
  rcases Nat.lt_or_ge f 13 with h | h
  · interval_cases f <;> rfl
  · rw [σabT_big h]

/-! ## Rows of the images -/

/-- The rows of the image system. -/
lemma πN_autT {σ : ℕ → ℕ} (hσ : EInv σ) {τ : Fin 12 ≃ Fin 12} {fl : ℕ → Bool}
    (h : IsAut (mkE 12 lTH337) (eEquiv σ hσ) τ (fun e => fl e.val)) (P : CrossingSystem (mkE 12 lTH337))
    (e : ℕ) (he : e < 13) :
    πN (P.aut (eEquiv σ hσ) τ (fun e => fl e.val) h) e =
      if fl (σ e) then ((πN P (σ e)).map σ).reverse else (πN P (σ e)).map σ := by
  have he' : e < lTH337.length := he
  have hσ' : σ e < lTH337.length := hσ.lt e he
  unfold πN
  rw [dite_eq_left he', dite_eq_left hσ', aut_π]
  have hs : (eEquiv σ hσ).symm ⟨e, he'⟩ = ⟨σ e, hσ'⟩ := rfl
  rw [hs]
  have hmap : ∀ l : List (Fin lTH337.length), (l.map (eEquiv σ hσ)).map Fin.val = (l.map Fin.val).map σ := by
    intro l
    simp only [List.map_map]
    rfl
  split_ifs <;> simp only [List.map_reverse, hmap]

/-- The restriction as the image under the identity. -/
lemma restrR_eq_imageR (row : ℕ → List ℕ) : restrR RT337 row = imageR RT337 id (fun _ => false) row := by
  unfold restrR imageR
  apply List.map_congr_left
  intro e _
  simp

/-- **Images of images.** Under an automorphism `g` (edge map `σ`, flips `fl`), the image of the rows of `g P` under
`(σh, flh)` is the image of the rows of `P` under `(σk, flk)`, when `σ ∘ σh = σk` on `RT337`, `σh ∘ σ = σk` on the
entries, and the flips add up. -/
lemma imageR_autT {σ : ℕ → ℕ} (hσ : EInv σ) {τ : Fin 12 ≃ Fin 12} {fl : ℕ → Bool}
    (h : IsAut (mkE 12 lTH337) (eEquiv σ hσ) τ (fun e => fl e.val)) (P : CrossingSystem (mkE 12 lTH337))
    (hR : ∀ f, RT337.contains (σ f) = RT337.contains f)
    (σh : ℕ → ℕ) (flh : ℕ → Bool) (σk : ℕ → ℕ) (flk : ℕ → Bool)
    (hlt : ∀ e ∈ RT337, σh e < 13)
    (h1 : ∀ e ∈ RT337, σ (σh e) = σk e) (h2 : ∀ f ∈ RT337, σh (σ f) = σk f)
    (h3 : ∀ e ∈ RT337, (fl (σ (σh e)) ^^ flh (σh e)) = flk (σk e)) :
    imageR RT337 σh flh (πN (P.aut (eEquiv σ hσ) τ (fun e => fl e.val) h)) = imageR RT337 σk flk (πN P) := by
  unfold imageR
  apply List.map_congr_left
  intro e he
  have hf : ∀ l : List ℕ, (l.map σ).filter (fun f => RT337.contains f) =
      (l.filter fun f => RT337.contains f).map σ := by
    intro l
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro f _
    simp only [Function.comp, hR]
  have hm : ∀ l : List ℕ, ((l.filter fun f => RT337.contains f).map σ).map σh =
      (l.filter fun f => RT337.contains f).map σk := by
    intro l
    rw [List.map_map]
    apply List.map_congr_left
    intro f hf'
    have hfR : f ∈ RT337 := by
      have := (List.mem_filter.1 hf').2
      simpa using this
    exact h2 f hfR
  have e3 := h3 e he
  rw [h1 e he] at e3
  simp only
  rw [πN_autT hσ h P (σh e) (hlt e he), h1 e he]
  cases hA : fl (σk e) <;> cases hB : flh (σh e) <;> rw [hA, hB] at e3 <;> simp only [Bool.xor_false,
    Bool.false_xor, Bool.xor_true, Bool.true_xor, Bool.not_false, Bool.not_true] at e3 <;>
    simp only [← e3, ite_true, ite_false, Bool.false_eq_true, List.filter_reverse, hf, hm, List.map_reverse,
      List.reverse_reverse]

/-! ## The orbit minimum -/

/-- Among four lists, one is at most all four (the order of core `List`, as in `canonR`). -/
lemma min4 (x0 x1 x2 x3 : List (List ℕ)) :
    (@LE.le _ List.instLE x0 x1 ∧ @LE.le _ List.instLE x0 x2 ∧ @LE.le _ List.instLE x0 x3) ∨
    (@LE.le _ List.instLE x1 x0 ∧ @LE.le _ List.instLE x1 x2 ∧ @LE.le _ List.instLE x1 x3) ∨
    (@LE.le _ List.instLE x2 x0 ∧ @LE.le _ List.instLE x2 x1 ∧ @LE.le _ List.instLE x2 x3) ∨
    (@LE.le _ List.instLE x3 x0 ∧ @LE.le _ List.instLE x3 x1 ∧ @LE.le _ List.instLE x3 x2) := by
  rcases List.le_total x0 x1 with h01 | h01 <;> rcases List.le_total x2 x3 with h23 | h23
  · rcases List.le_total x0 x2 with h | h
    · exact Or.inl ⟨h01, h, List.le_trans h h23⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h, List.le_trans h h01, h23⟩))
  · rcases List.le_total x0 x3 with h | h
    · exact Or.inl ⟨h01, List.le_trans h h23, h⟩
    · exact Or.inr (Or.inr (Or.inr ⟨h, List.le_trans h h01, h23⟩))
  · rcases List.le_total x1 x2 with h | h
    · exact Or.inr (Or.inl ⟨h01, h, List.le_trans h h23⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨List.le_trans h h01, h, h23⟩))
  · rcases List.le_total x1 x3 with h | h
    · exact Or.inr (Or.inl ⟨h01, List.le_trans h h23, h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨List.le_trans h h01, h, h23⟩))

/-- **The symmetry hypothesis for `lTH337`.** Every planar crossing system has a planar image whose restriction to
`RT337` is lexicographically at most its images under `a`, `b` and `ab` (the order of core `List`, as in `canonR`). -/
theorem hsymT337_core : ∀ P : CrossingSystem (mkE 12 lTH337), Planar (aug (mkE 12 lTH337) P) →
    ∃ P', (@LE.le _ List.instLE (restrR RT337 (πN P')) (imageR RT337 σaT faT (πN P')) ∧
      @LE.le _ List.instLE (restrR RT337 (πN P')) (imageR RT337 σbT fbT (πN P')) ∧
      @LE.le _ List.instLE (restrR RT337 (πN P')) (imageR RT337 σabT fabT (πN P'))) ∧
      Planar (aug (mkE 12 lTH337) P') := by
  intro P hP
  -- the images of `P` and their restrictions
  have ra : restrR RT337 (πN (P.aut _ _ _ isAutA)) = imageR RT337 σaT faT (πN P) := by
    rw [restrR_eq_imageR]
    exact imageR_autT einvA isAutA P RT337_σa id _ σaT faT (by decide) (by decide) (by decide) (by decide)
  have rb : restrR RT337 (πN (P.aut _ _ _ isAutB)) = imageR RT337 σbT fbT (πN P) := by
    rw [restrR_eq_imageR]
    exact imageR_autT einvB isAutB P RT337_σb id _ σbT fbT (by decide) (by decide) (by decide) (by decide)
  have rab : restrR RT337 (πN (P.aut _ _ _ isAutAB)) = imageR RT337 σabT fabT (πN P) := by
    rw [restrR_eq_imageR]
    exact imageR_autT einvAB isAutAB P RT337_σab id _ σabT fabT (by decide) (by decide) (by decide) (by decide)
  -- images of the images
  have i0 : imageR RT337 id (fun _ => false) (πN P) = restrR RT337 (πN P) := (restrR_eq_imageR _).symm
  have aa : imageR RT337 σaT faT (πN (P.aut _ _ _ isAutA)) = restrR RT337 (πN P) := by
    rw [← i0]
    exact imageR_autT einvA isAutA P RT337_σa σaT faT id _ (by decide) (by decide) (by decide) (by decide)
  have ab : imageR RT337 σbT fbT (πN (P.aut _ _ _ isAutA)) = imageR RT337 σabT fabT (πN P) :=
    imageR_autT einvA isAutA P RT337_σa σbT fbT σabT fabT (by decide) (by decide) (by decide) (by decide)
  have aab : imageR RT337 σabT fabT (πN (P.aut _ _ _ isAutA)) = imageR RT337 σbT fbT (πN P) :=
    imageR_autT einvA isAutA P RT337_σa σabT fabT σbT fbT (by decide) (by decide) (by decide) (by decide)
  have ba : imageR RT337 σaT faT (πN (P.aut _ _ _ isAutB)) = imageR RT337 σabT fabT (πN P) :=
    imageR_autT einvB isAutB P RT337_σb σaT faT σabT fabT (by decide) (by decide) (by decide) (by decide)
  have bb : imageR RT337 σbT fbT (πN (P.aut _ _ _ isAutB)) = restrR RT337 (πN P) := by
    rw [← i0]
    exact imageR_autT einvB isAutB P RT337_σb σbT fbT id _ (by decide) (by decide) (by decide) (by decide)
  have bab : imageR RT337 σabT fabT (πN (P.aut _ _ _ isAutB)) = imageR RT337 σaT faT (πN P) :=
    imageR_autT einvB isAutB P RT337_σb σabT fabT σaT faT (by decide) (by decide) (by decide) (by decide)
  have aba : imageR RT337 σaT faT (πN (P.aut _ _ _ isAutAB)) = imageR RT337 σbT fbT (πN P) :=
    imageR_autT einvAB isAutAB P RT337_σab σaT faT σbT fbT (by decide) (by decide) (by decide) (by decide)
  have abb : imageR RT337 σbT fbT (πN (P.aut _ _ _ isAutAB)) = imageR RT337 σaT faT (πN P) :=
    imageR_autT einvAB isAutAB P RT337_σab σbT fbT σaT faT (by decide) (by decide) (by decide) (by decide)
  have abab : imageR RT337 σabT fabT (πN (P.aut _ _ _ isAutAB)) = restrR RT337 (πN P) := by
    rw [← i0]
    exact imageR_autT einvAB isAutAB P RT337_σab σabT fabT id _ (by decide) (by decide) (by decide) (by decide)
  rcases min4 (restrR RT337 (πN P)) (imageR RT337 σaT faT (πN P)) (imageR RT337 σbT fbT (πN P))
      (imageR RT337 σabT fabT (πN P)) with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨P, ⟨h1, h2, h3⟩, hP⟩
  · refine ⟨_, ⟨?_, ?_, ?_⟩, planar_aut isAutA P hP⟩
    · rw [ra, aa]; exact h1
    · rw [ra, ab]; exact h3
    · rw [ra, aab]; exact h2
  · refine ⟨_, ⟨?_, ?_, ?_⟩, planar_aut isAutB P hP⟩
    · rw [rb, ba]; exact h3
    · rw [rb, bb]; exact h1
    · rw [rb, bab]; exact h2
  · refine ⟨_, ⟨?_, ?_, ?_⟩, planar_aut isAutAB P hP⟩
    · rw [rab, aba]; exact h3
    · rw [rab, abb]; exact h2
    · rw [rab, abab]; exact h1

/-- **`hsym` for `lTH337`**, with `RT337` and the three symmetries `a`, `b`, `ab`. -/
theorem hsymT337 : ∀ P : CrossingSystem (mkE 12 lTH337), Planar (aug (mkE 12 lTH337) P) →
    ∃ P', (QSym RT337 σaT faT P' ∧ QSym RT337 σbT fbT P' ∧ QSym RT337 σabT fabT P') ∧
      Planar (aug (mkE 12 lTH337) P') := fun P hP =>
  let ⟨P', ⟨ha, hb, hab⟩, hP'⟩ := hsymT337_core P hP
  ⟨P', ⟨decide_eq_true ha, decide_eq_true hb, decide_eq_true hab⟩, hP'⟩

/-- The side conditions for `K = 10`. -/
theorem hRT337 : ∀ e ∈ RT337, e < 10 := by decide

theorem hσaR : ∀ e ∈ RT337, σaT e ∈ RT337 := by decide

theorem hσbR : ∀ e ∈ RT337, σbT e ∈ RT337 := by decide

theorem hσabR : ∀ e ∈ RT337, σabT e ∈ RT337 := by decide

/-! ## Filters transfer along `a` -/

lemma mem_map_invol {σ : ℕ → ℕ} (hi : ∀ e, σ (σ e) = e) (g : List ℕ) (f : ℕ) : f ∈ g.map σ ↔ σ f ∈ g := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [hi]
  · intro h
    exact ⟨σ f, h, hi f⟩

lemma idxOf_map_invol {σ : ℕ → ℕ} (hi : ∀ e, σ (σ e) = e) (g : List ℕ) (f : ℕ) :
    (g.map σ).idxOf f = g.idxOf (σ f) := by
  induction g with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih]
    congr 1
    have : (σ a == f) = (a == σ f) := by
      by_cases h : a = σ f
      · subst h; rw [hi]; simp
      · have h' : σ a ≠ f := fun e => h (by rw [← e, hi])
        simp [h, h']
    rw [this]

lemma getD_map_fn (σ : ℕ → ℕ) (g : List ℕ) (i : ℕ) (hi : i < g.length) :
    (g.map σ).getD i 0 = σ (g.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- **Filters transfer along `a`** (no edge reversed): if `φ` is sound for `lTH337`, so is `autFilt σaT faT φ`. -/
theorem filtSound_autT337a (φ : Thrackle78Core.Filt) (hg : ∀ x ∈ φ.g, x < 13) (h : FiltSound (mkE 12 lTH337) φ) :
    FiltSound (mkE 12 lTH337) (autFilt σaT faT φ) := by
  intro P
  by_cases hP : Planar (aug (mkE 12 lTH337) P)
  · right
    have hQ := planar_aut isAutA P hP
    rcases h (P.aut (eEquiv σaT einvA) (vEquiv τaT vinvA) (fun e => faT e.val) isAutA) with hn | hmem
    · exact absurd hQ hn
    · show rowsH P (φ.g.map σaT) ∈ φ.sys.map _
      have key : rowsH P (φ.g.map σaT) = (List.range φ.g.length).map fun i =>
          if faT (σaT (φ.g.getD i 0)) then
            ((rowsH (P.aut (eEquiv σaT einvA) (vEquiv τaT vinvA) (fun e => faT e.val) isAutA) φ.g).getD i []).reverse
          else (rowsH (P.aut (eEquiv σaT einvA) (vEquiv τaT vinvA) (fun e => faT e.val) isAutA) φ.g).getD i [] := by
        unfold rowsH
        rw [List.length_map]
        apply List.map_congr_left
        intro i hi
        rw [List.mem_range] at hi
        have hgi : φ.g.getD i 0 ∈ φ.g := by
          rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
        have h13 := hg _ hgi
        rw [getD_map_fn σaT φ.g i hi, getD_range_map _ i hi, πN_autT einvA isAutA P _ h13]
        have hfilt : ∀ l : List ℕ, (l.map σaT).filter (fun f => φ.g.contains f) =
            (l.filter fun f => (φ.g.map σaT).contains f).map σaT := by
          intro l
          rw [List.filter_map]
          congr 1
          apply List.filter_congr
          intro f _
          simp only [Function.comp]
          by_cases hm : σaT f ∈ φ.g
          · have h2 : f ∈ φ.g.map σaT := (mem_map_invol einvA.inv _ _).2 hm
            simp [hm, h2]
          · have h2 : f ∉ φ.g.map σaT := fun h => hm ((mem_map_invol einvA.inv _ _).1 h)
            simp [hm, h2]
        have hlab : ∀ l : List ℕ, (l.map σaT).map (labOf φ.g) = l.map (labOf (φ.g.map σaT)) := by
          intro l
          rw [List.map_map]
          apply List.map_congr_left
          intro f _
          simp only [Function.comp, labOf, idxOf_map_invol einvA.inv]
        split_ifs with hf
        · rw [List.filter_reverse, hfilt, List.map_reverse, hlab, List.reverse_reverse]
        · rw [hfilt, hlab]
      rw [key]
      exact List.mem_map_of_mem hmem
  · exact Or.inl hP

end Thrackle78.Checker
