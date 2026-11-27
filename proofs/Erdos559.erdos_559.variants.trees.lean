import FormalConjectures.ErdosProblems.«559»

/-!
# Erdős 559, tree variant (Friedman–Pippenger)

For a tree `G` with `n` vertices and maximum degree at most `d`, the size Ramsey number
`sizeRamsey G G` is at most `C * n` with `C` depending on `d` only.
-/

open SimpleGraph

open scoped Classical

namespace OMA

/-! ### Open and external neighbourhoods -/

section Basics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The open neighbourhood of a finite vertex set. -/
noncomputable def nbr (F : SimpleGraph V) (X : Finset V) : Finset V :=
  Finset.univ.filter (fun y => ∃ x ∈ X, F.Adj x y)

lemma mem_nbr {F : SimpleGraph V} {X : Finset V} {y : V} :
    y ∈ nbr F X ↔ ∃ x ∈ X, F.Adj x y := by
  classical simp [nbr]

lemma nbr_mono {F : SimpleGraph V} {A B : Finset V} (h : A ⊆ B) : nbr F A ⊆ nbr F B := by
  classical
  intro y hy
  rw [mem_nbr] at hy ⊢
  exact ⟨hy.choose, h hy.choose_spec.1, hy.choose_spec.2⟩

lemma nbr_union (F : SimpleGraph V) (A B : Finset V) :
    nbr F (A ∪ B) = nbr F A ∪ nbr F B := by
  classical
  ext y
  simp only [mem_nbr, Finset.mem_union]
  constructor
  · rintro ⟨x, hx | hx, hxy⟩
    exacts [Or.inl ⟨x, hx, hxy⟩, Or.inr ⟨x, hx, hxy⟩]
  · rintro (⟨x, hx, hxy⟩ | ⟨x, hx, hxy⟩)
    · exact ⟨x, Or.inl hx, hxy⟩
    · exact ⟨x, Or.inr hx, hxy⟩

lemma nbr_empty (F : SimpleGraph V) : nbr F ∅ = ∅ := by
  classical
  ext y
  simp [mem_nbr]

lemma nbr_singleton (F : SimpleGraph V) (x : V) :
    nbr F {x} = Finset.univ.filter (fun y => F.Adj x y) := by
  classical
  ext y
  simp [mem_nbr]

/-- The external neighbourhood: neighbours that do not belong to the set itself. -/
noncomputable def ext (F : SimpleGraph V) (X : Finset V) : Finset V := nbr F X \ X

/-- The external neighbourhood inside a fixed ambient set `W`. -/
noncomputable def extIn (F : SimpleGraph V) (W X : Finset V) : Finset V := (nbr F X \ X) ∩ W

lemma extIn_univ (F : SimpleGraph V) (X : Finset V) : extIn F Finset.univ X = ext F X := by
  classical simp [extIn, ext]

lemma extIn_card_le_ext (F : SimpleGraph V) (W X : Finset V) :
    (extIn F W X).card ≤ (ext F X).card := by
  classical exact Finset.card_le_card Finset.inter_subset_left

/-- Submodularity of the size of neighbourhoods after removing a fixed set. -/
lemma nbr_sdiff_submod (F : SimpleGraph V) (W A B : Finset V) :
    (nbr F (A ∪ B) \ W).card + (nbr F (A ∩ B) \ W).card ≤
      (nbr F A \ W).card + (nbr F B \ W).card := by
  classical
  have hun : nbr F (A ∪ B) \ W = (nbr F A \ W) ∪ (nbr F B \ W) := by
    rw [nbr_union, Finset.union_sdiff_distrib]
  have hsub : nbr F (A ∩ B) \ W ⊆ (nbr F A \ W) ∩ (nbr F B \ W) := by
    intro y hy
    simp only [Finset.mem_sdiff, mem_nbr, Finset.mem_inter] at hy ⊢
    obtain ⟨⟨x, hx, hxy⟩, hyW⟩ := hy
    exact ⟨⟨⟨x, hx.1, hxy⟩, hyW⟩, ⟨x, hx.2, hxy⟩, hyW⟩
  have h' : (nbr F (A ∩ B) \ W).card ≤ ((nbr F A \ W) ∩ (nbr F B \ W)).card :=
    Finset.card_le_card hsub
  have h := Finset.card_union_add_card_inter (nbr F A \ W) (nbr F B \ W)
  rw [hun]
  omega

/-- The external neighbourhood of a union is contained in the union of the pieces. -/
lemma extIn_union_sub (F : SimpleGraph V) (W S X : Finset V) (hSW : S ⊆ W) (hXW : X ⊆ W) :
    extIn F W (S ∪ X) ⊆ extIn F W S ∪ extIn F (W \ S) X := by
  classical
  intro y hy
  simp only [extIn, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union, mem_nbr] at hy ⊢
  obtain ⟨⟨⟨x, hx, hxy⟩, hyNot⟩, hyW⟩ := hy
  have hyS : y ∉ S := fun h => hyNot (Or.inl h)
  have hyX : y ∉ X := fun h => hyNot (Or.inr h)
  rcases hx with hx | hx
  · exact Or.inl ⟨⟨⟨x, hx, hxy⟩, hyS⟩, hyW⟩
  · exact Or.inr ⟨⟨⟨x, hx, hxy⟩, hyX⟩, hyW, hyS⟩

lemma nbr_card_le_insert (F : SimpleGraph V) (X W : Finset V) (y : V) :
    (nbr F X \ W).card ≤ (nbr F X \ insert y W).card + 1 := by
  classical
  have h : nbr F X \ insert y W = (nbr F X \ W) \ {y} := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [h]
  have hcard := Finset.card_le_card_sdiff_add_card (s := nbr F X \ W) (t := ({y} : Finset V))
  simpa using hcard

/-- Every two disjoint `m`-element sets are joined by an edge. -/
def HoleFree (F : SimpleGraph V) (m : ℕ) : Prop :=
  ∀ A B : Finset V, A.card = m → B.card = m → Disjoint A B →
    ∃ a ∈ A, ∃ b ∈ B, F.Adj a b

/-- `F` expands by a factor `k` on all sets of size at most `s` inside `U`. -/
def IsExpOn (F : SimpleGraph V) (U : Finset V) (s k : ℕ) : Prop :=
  ∀ X : Finset V, X ⊆ U → X.card ≤ s → k * X.card ≤ (extIn F U X).card

lemma not_exp_iff {F : SimpleGraph V} {U : Finset V} {s k : ℕ} :
    ¬ IsExpOn F U s k ↔
      ∃ X : Finset V, X ⊆ U ∧ X.card ≤ s ∧ (extIn F U X).card < k * X.card := by
  constructor
  · intro h
    by_contra hc
    apply h
    intro X hXU hXs
    by_contra hlt
    exact hc ⟨X, hXU, hXs, not_le.mp hlt⟩
  · rintro ⟨X, hXU, hXs, hlt⟩ hE
    exact absurd (hE X hXU hXs) (not_le.mpr hlt)

end Basics

/-! ### The Friedman–Pippenger embedding invariant -/

section Embed

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The number of tree edges from the placed vertices whose image lies in `X`. -/
noncomputable def Dsum (T : SimpleGraph β) (S : Finset β) (φ : β → V) (X : Finset V) : ℕ :=
  ∑ a ∈ S, if φ a ∈ X then (S.filter (fun b => T.Adj a b)).card else 0

lemma Dsum_empty (T : SimpleGraph β) (S : Finset β) (φ : β → V) : Dsum T S φ ∅ = 0 := by
  classical simp [Dsum]

/-- The embedding invariant of Friedman–Pippenger. -/
def Inv (F : SimpleGraph V) (T : SimpleGraph β) (S : Finset β) (φ : β → V) (d n : ℕ) : Prop :=
  ∀ X : Finset V, X.card ≤ 2 * n →
    (d + 1) * X.card ≤ (nbr F X \ S.image φ).card + Dsum T S φ X

/-- A set on which the embedding invariant is tight. -/
def Tight (F : SimpleGraph V) (T : SimpleGraph β) (S : Finset β) (φ : β → V) (d n : ℕ)
    (X : Finset V) : Prop :=
  (d + 1) * X.card = (nbr F X \ S.image φ).card + Dsum T S φ X

lemma Dsum_mono (T : SimpleGraph β) (S : Finset β) (φ : β → V) {X Y : Finset V} (h : X ⊆ Y) :
    Dsum T S φ X ≤ Dsum T S φ Y := by
  classical
  refine Finset.sum_le_sum (fun a _ => ?_)
  by_cases hX : φ a ∈ X
  · rw [if_pos hX, if_pos (h hX)]
  · rw [if_neg hX]
    exact Nat.zero_le _

lemma Dsum_union_inter (T : SimpleGraph β) (S : Finset β) (φ : β → V) (A B : Finset V) :
    Dsum T S φ (A ∪ B) + Dsum T S φ (A ∩ B) = Dsum T S φ A + Dsum T S φ B := by
  classical
  simp only [Dsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hA : φ a ∈ A <;> by_cases hB : φ a ∈ B <;> simp [hA, hB]

lemma Dsum_collapse (T : SimpleGraph β) (S : Finset β) (φ : β → V) (X : Finset V)
    {u : β} (hu : u ∈ S) (hXu : φ u ∉ X)
    (hinj : ∀ a ∈ S, ∀ b ∈ S, φ a = φ b → a = b) :
    Dsum T S φ (insert (φ u) X) = Dsum T S φ X + (S.filter (fun b => T.Adj u b)).card := by
  classical
  have hpt : ∀ a ∈ S,
      (if φ a ∈ insert (φ u) X then (S.filter (fun b => T.Adj a b)).card else 0)
        = (if φ a ∈ X then (S.filter (fun b => T.Adj a b)).card else 0)
          + (if φ a = φ u then (S.filter (fun b => T.Adj a b)).card else 0) := by
    intro a _
    by_cases hX : φ a ∈ X
    · have h1 : φ a ∈ insert (φ u) X := Finset.mem_insert_of_mem hX
      have h2 : φ a ≠ φ u := fun h => hXu (h ▸ hX)
      simp [h1, hX, h2]
    · by_cases he : φ a = φ u
      · rw [he] at hX ⊢
        simp [hX]
      · have h1 : ¬ (φ a ∈ insert (φ u) X) := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨he, hX⟩
        simp [h1, hX, he]
  have hcollapse : (∑ a ∈ S, if φ a = φ u then (S.filter (fun b => T.Adj a b)).card else 0)
      = (S.filter (fun b => T.Adj u b)).card := by
    rw [Finset.sum_eq_single u]
    · simp
    · intro b hb hbu
      have hne : φ b ≠ φ u := fun h => hbu (hinj b hb u hu h)
      simp [hne]
    · intro h; exact absurd hu h
  unfold Dsum
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, hcollapse]

lemma card_filter_adj_le (T : SimpleGraph β) (S : Finset β) (u : β) :
    (S.filter (fun b => T.Adj u b)).card ≤ (Finset.univ.filter (fun b => T.Adj u b)).card :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))

/-- Tight sets with at most `2n` elements have at most `S.card` elements. -/
lemma tight_card_le (F : SimpleGraph V) (T : SimpleGraph β) (S : Finset β) (φ : β → V) (d n : ℕ)
    (hexp : ∀ X : Finset V, X.card ≤ 2 * n → (d + 2) * X.card ≤ (ext F X).card)
    {X : Finset V} (hX : Tight F T S φ d n X) (hc : X.card ≤ 2 * n) :
    X.card ≤ S.card := by
  classical
  have h2 : (d + 2) * X.card ≤ (ext F X).card := hexp X hc
  have h3 : (ext F X).card ≤ (nbr F X).card := Finset.card_le_card Finset.sdiff_subset
  have h4 : (nbr F X).card ≤ (nbr F X \ S.image φ).card + (S.image φ).card :=
    Finset.card_le_card_sdiff_add_card
  have h5 : (S.image φ).card ≤ S.card := Finset.card_image_le
  have h6 : (nbr F X \ S.image φ).card + Dsum T S φ X = (d + 1) * X.card := hX.symm
  have hmul : (d + 2) * X.card = (d + 1) * X.card + X.card := by ring
  omega

/-- The union of two tight sets of size at most `n` is tight and of size at most `n`. -/
lemma tight_union (F : SimpleGraph V) (T : SimpleGraph β) (S : Finset β) (φ : β → V) (d n : ℕ)
    (hexp : ∀ X : Finset V, X.card ≤ 2 * n → (d + 2) * X.card ≤ (ext F X).card)
    (hS : S.card ≤ n)
    (hInv : Inv F T S φ d n) {A B : Finset V}
    (hA : Tight F T S φ d n A) (hB : Tight F T S φ d n B)
    (hAn : A.card ≤ n) (hBn : B.card ≤ n) :
    Tight F T S φ d n (A ∪ B) ∧ (A ∪ B).card ≤ n := by
  classical
  unfold Tight at hA hB ⊢
  have hca : (A ∪ B).card ≤ 2 * n := by
    have h := Finset.card_union_le A B
    omega
  have hci : (A ∩ B).card ≤ 2 * n := by
    have h1 : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
    omega
  have hIA := hInv (A ∪ B) hca
  have hIB := hInv (A ∩ B) hci
  have hsub := nbr_sdiff_submod F (S.image φ) A B
  have hmod := Dsum_union_inter T S φ A B
  have hci2 := Finset.card_union_add_card_inter A B
  have hkeyN : (d + 1) * (A ∪ B).card + (d + 1) * (A ∩ B).card
      = (d + 1) * A.card + (d + 1) * B.card := by
    rw [← Nat.mul_add, ← Nat.mul_add, hci2]
  have htight : (d + 1) * (A ∪ B).card
      = (nbr F (A ∪ B) \ S.image φ).card + Dsum T S φ (A ∪ B) := by
    have hle : (nbr F (A ∪ B) \ S.image φ).card + Dsum T S φ (A ∪ B)
        + ((nbr F (A ∩ B) \ S.image φ).card + Dsum T S φ (A ∩ B))
        ≤ (d + 1) * (A ∪ B).card + (d + 1) * (A ∩ B).card := by
      rw [hkeyN, hA, hB]
      omega
    have hge : (d + 1) * (A ∪ B).card + (d + 1) * (A ∩ B).card
        ≤ (nbr F (A ∪ B) \ S.image φ).card + Dsum T S φ (A ∪ B)
          + ((nbr F (A ∩ B) \ S.image φ).card + Dsum T S φ (A ∩ B)) := by
      omega
    have heq := le_antisymm hle hge
    omega
  exact ⟨htight, (tight_card_le F T S φ d n hexp htight hca).trans hS⟩

/-- The degree sum after adding the leaf `v` at position `y`. -/
lemma Dsum_insert_vertex (T : SimpleGraph β) (S : Finset β) (φ : β → V) (v : β) (y : V)
    (X : Finset V) (hv : v ∉ S) :
    Dsum T (insert v S) (Function.update φ v y) X
      = Dsum T S φ X + (if y ∈ X then (S.filter (fun b => T.Adj v b)).card else 0)
        + (S.filter (fun a => T.Adj a v ∧ φ a ∈ X)).card := by
  classical
  have hψ : ∀ a ∈ S, Function.update φ v y a = φ a := fun a ha =>
    Function.update_of_ne (fun h => hv (by rw [← h]; exact ha)) y φ
  have hcard : ∀ a : β, ((insert v S).filter (fun b => T.Adj a b)).card
      = (S.filter (fun b => T.Adj a b)).card + (if T.Adj a v then 1 else 0) := by
    intro a
    rw [Finset.filter_insert]
    by_cases ha : T.Adj a v
    · rw [if_pos ha, if_pos ha, Finset.card_insert_of_notMem (by simp [hv])]
    · rw [if_neg ha, if_neg ha, Nat.add_zero]
  have hvterm : ((insert v S).filter (fun b => T.Adj v b)).card
      = (S.filter (fun b => T.Adj v b)).card := by
    rw [hcard v, if_neg (SimpleGraph.irrefl T), Nat.add_zero]
  unfold Dsum
  rw [Finset.sum_insert hv, Function.update_self, hvterm]
  have hstep : ∀ a ∈ S,
      (if Function.update φ v y a ∈ X then ((insert v S).filter (fun b => T.Adj a b)).card else 0)
        = (if φ a ∈ X then (S.filter (fun b => T.Adj a b)).card else 0)
          + (if T.Adj a v ∧ φ a ∈ X then 1 else 0) := by
    intro a ha
    rw [hψ a ha, hcard a]
    by_cases hX : φ a ∈ X <;> by_cases hav : T.Adj a v <;> simp [hX, hav]
  have hsum2 : (∑ a ∈ S, (if T.Adj a v ∧ φ a ∈ X then 1 else 0))
      = (S.filter (fun a => T.Adj a v ∧ φ a ∈ X)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, hsum2]
  omega

/-- If extending at `y` fails, some tight set catches `y` while avoiding the placed
tree-neighbours of the new leaf. -/
lemma fail_set (F : SimpleGraph V) (T : SimpleGraph β) (S : Finset β) (φ : β → V) (d n : ℕ)
    (v : β) (y : V) (hv : v ∉ S) (hInv : Inv F T S φ d n)
    (hyW : y ∉ S.image φ)
    (hfail : ¬ Inv F T (insert v S) (Function.update φ v y) d n) :
    ∃ X : Finset V, X.card ≤ 2 * n ∧ Tight F T S φ d n X ∧ y ∈ nbr F X ∧
      Disjoint X ((S.filter (fun b => T.Adj v b)).image φ) := by
  classical
  have hfail' : ∃ X : Finset V, X.card ≤ 2 * n ∧
      ¬ ((d + 1) * X.card ≤ (nbr F X \ (insert v S).image (Function.update φ v y)).card
          + Dsum T (insert v S) (Function.update φ v y) X) := by
    have h := hfail
    simp only [Inv, not_forall] at h
    obtain ⟨X, hXc, hXf⟩ := h
    exact ⟨X, hXc, hXf⟩
  obtain ⟨X, hXc, hXf⟩ := hfail'
  have hDv := Dsum_insert_vertex T S φ v y X hv
  have hWnew : (insert v S).image (Function.update φ v y) = insert y (S.image φ) := by
    rw [Finset.image_insert, Function.update_self]
    congr 1
    exact Finset.image_congr (fun a ha =>
      Function.update_of_ne (fun h => hv (by rw [← h]; exact ha)) y φ)
  rw [hDv, hWnew] at hXf
  set P : ℕ := (if y ∈ X then (S.filter (fun b => T.Adj v b)).card else 0) with hP
  set Q : ℕ := (S.filter (fun a => T.Adj a v ∧ φ a ∈ X)).card with hQ
  have hI := hInv X hXc
  have hA := nbr_card_le_insert F X (S.image φ) y
  have hlt := not_le.mp hXf
  have hPQ : P + Q = 0 := by omega
  have hP0 : (if y ∈ X then (S.filter (fun b => T.Adj v b)).card else 0) = 0 := by omega
  have hQ0 : Q = 0 := by omega
  have hyNbr : y ∈ nbr F X := by
    by_contra hyN
    have hsame : nbr F X \ insert y (S.image φ) = nbr F X \ S.image φ := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inr h)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rintro (rfl | h3)
        · exact hyN h1
        · exact h2 h3
    rw [hsame] at hlt
    omega
  have htight : Tight F T S φ d n X := by
    have hmemy : y ∈ nbr F X \ S.image φ := Finset.mem_sdiff.mpr ⟨hyNbr, hyW⟩
    have hcard1 : (nbr F X \ S.image φ).card = (nbr F X \ insert y (S.image φ)).card + 1 := by
      rw [Finset.sdiff_insert]
      exact (Finset.card_erase_add_one hmemy).symm
    unfold Tight
    omega
  refine ⟨X, hXc, htight, hyNbr, ?_⟩
  rw [Finset.disjoint_left]
  intro a haX haIm
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp haIm
  have hb' : b ∈ S.filter (fun a => T.Adj a v ∧ φ a ∈ X) :=
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2.symm, haX⟩
  have hpos := Finset.card_pos.mpr ⟨b, hb'⟩
  omega

/-- A tree with at least two vertices has a leaf whose removal leaves a connected graph. -/
lemma peel_leaf (T : SimpleGraph β) (S : Finset β) (hT : T.IsTree)
    (hconn : (T.induce (↑S : Set β)).Connected) (hS2 : 2 ≤ S.card) :
    ∃ v ∈ S, ∃ u ∈ S, u ≠ v ∧ T.Adj u v ∧ (∀ b ∈ S, T.Adj v b → b = u) ∧
      (T.induce (↑(S.erase v) : Set β)).Connected := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hnt : Nontrivial ↥(↑S : Set β) :=
    ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have htree : (T.induce (↑S : Set β)).IsTree := ⟨hconn, hT.isAcyclic.induce _⟩
  obtain ⟨v, hvdeg⟩ := htree.exists_vert_degree_one_of_nontrivial
  obtain ⟨u, huadj, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hvdeg
  have hvS : (v : β) ∈ S := v.2
  have huS : (u : β) ∈ S := u.2
  have hadj : T.Adj (v : β) (u : β) := SimpleGraph.induce_adj.mp huadj
  have hne : (u : β) ≠ (v : β) := hadj.ne.symm
  have huniq' : ∀ b ∈ S, T.Adj (v : β) b → b = (u : β) := by
    intro b hb hba
    have h1 : (T.induce (↑S : Set β)).Adj v ⟨b, hb⟩ := by
      rw [SimpleGraph.induce_adj]
      exact hba
    exact congrArg Subtype.val (huniq ⟨b, hb⟩ h1)
  have hcomp : ((T.induce (↑S : Set β)).induce ({v}ᶜ : Set ↥(↑S : Set β))).Connected :=
    Connected.induce_compl_singleton_of_degree_eq_one hconn hvdeg
  have hiso : ((T.induce (↑S : Set β)).induce ({v}ᶜ : Set ↥(↑S : Set β))) ≃g
      (T.induce (↑(S.erase (v : β)) : Set β)) :=
    { toEquiv :=
        { toFun := fun x => ⟨x.val.val, Finset.mem_erase.mpr ⟨fun h => x.2 (by
              rw [Set.mem_singleton_iff]; exact Subtype.ext h), x.val.2⟩⟩
          invFun := fun y => ⟨⟨y.val, (Finset.mem_erase.mp y.2).2⟩, by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro h
            exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val h)⟩
          left_inv := fun x => Subtype.ext (Subtype.ext rfl)
          right_inv := fun y => Subtype.ext rfl }
      map_rel_iff' := fun {_ _} => by
        simp only [SimpleGraph.induce_adj]
        rfl }
  exact ⟨(v : β), hvS, (u : β), huS, hne, hadj.symm, huniq', hiso.connected_iff.mp hcomp⟩

/-- One step of the Friedman–Pippenger induction: extend a good embedding by a leaf. -/
lemma extend_step (F : SimpleGraph V) (T : SimpleGraph β) (d n : ℕ)
    (hexp : ∀ X : Finset V, X.card ≤ 2 * n → (d + 2) * X.card ≤ (ext F X).card)
    (hn : 1 ≤ n) (hdeg : ∀ v : β, (Finset.univ.filter (fun b => T.Adj v b)).card ≤ d)
    (S : Finset β) (φ : β → V) (v u : β)
    (hinj : ∀ a ∈ S, ∀ b ∈ S, φ a = φ b → a = b)
    (hhom : ∀ a ∈ S, ∀ b ∈ S, T.Adj a b → F.Adj (φ a) (φ b))
    (hInv : Inv F T S φ d n)
    (hS : S.card ≤ n) (hv : v ∉ S) (hu : u ∈ S) (hadj : T.Adj u v)
    (hleaf : ∀ b ∈ S, T.Adj v b → b = u) :
    ∃ φ' : β → V,
      (∀ a ∈ insert v S, ∀ b ∈ insert v S, φ' a = φ' b → a = b) ∧
      (∀ a ∈ insert v S, ∀ b ∈ insert v S, T.Adj a b → F.Adj (φ' a) (φ' b)) ∧
      Inv F T (insert v S) φ' d n := by
  classical
  have huniqS : ∀ a ∈ S, a ≠ u → φ a ≠ φ u := fun a ha hne h => hne (hinj a ha u hu h)
  have hdegS : (S.filter (fun b => T.Adj u b)).card ≤ d := (card_filter_adj_le T S u).trans (hdeg u)
  have hY : (nbr F {φ u} \ S.image φ).Nonempty := by
    have h1 := hInv ({φ u} : Finset V) (by simp only [Finset.card_singleton]; omega)
    have h2 : Dsum T S φ {φ u} = (S.filter (fun b => T.Adj u b)).card := by
      have hcol := Dsum_collapse (T := T) (S := S) (φ := φ) (X := ∅) (u := u) hu
        (by simp) hinj
      rw [Dsum_empty, Nat.zero_add] at hcol
      simpa using hcol
    rw [h2, Finset.card_singleton, Nat.mul_one] at h1
    have : 0 < (nbr F {φ u} \ S.image φ).card := by omega
    exact Finset.card_pos.mp this
  -- Every candidate image `y` of `v` gives a valid injective homomorphism on `insert v S`.
  have hinjU : ∀ y ∈ nbr F {φ u} \ S.image φ, ∀ a ∈ insert v S, ∀ b ∈ insert v S,
      Function.update φ v y a = Function.update φ v y b → a = b := by
    intro y hy a ha b hb hab
    have hyW : y ∉ S.image φ := (Finset.mem_sdiff.mp hy).2
    have key : ∀ x ∈ S, Function.update φ v y x = φ x := fun x hx =>
      Function.update_of_ne (fun hh => hv (by rw [← hh]; exact hx)) y φ
    rcases Finset.mem_insert.mp ha with hva | haS
    · rcases Finset.mem_insert.mp hb with hvb | hbS
      · rw [hva, hvb]
      · exfalso
        rw [hva, Function.update_self, key b hbS] at hab
        exact hyW (by rw [hab]; exact Finset.mem_image_of_mem φ hbS)
    · rcases Finset.mem_insert.mp hb with hvb | hbS
      · exfalso
        rw [hvb, Function.update_self, key a haS] at hab
        exact hyW (by rw [← hab]; exact Finset.mem_image_of_mem φ haS)
      · rw [key a haS, key b hbS] at hab
        exact hinj a haS b hbS hab
  have hhomU : ∀ y ∈ nbr F {φ u} \ S.image φ, ∀ a ∈ insert v S, ∀ b ∈ insert v S,
      T.Adj a b → F.Adj (Function.update φ v y a) (Function.update φ v y b) := by
    intro y hy a ha b hb hab
    have hyN : F.Adj y (φ u) := by
      obtain ⟨x, hx, hxy⟩ := mem_nbr.mp (Finset.mem_sdiff.mp hy).1
      rw [Finset.mem_singleton] at hx
      rw [hx] at hxy
      exact hxy.symm
    have key : ∀ x ∈ S, Function.update φ v y x = φ x := fun x hx =>
      Function.update_of_ne (fun hh => hv (by rw [← hh]; exact hx)) y φ
    rcases Finset.mem_insert.mp ha with hva | haS
    · rcases Finset.mem_insert.mp hb with hvb | hbS
      · rw [hva, hvb] at hab
        exact absurd hab (SimpleGraph.irrefl T)
      · rw [hva] at hab ⊢
        rw [Function.update_self, key b hbS]
        rw [hleaf b hbS hab]
        exact hyN
    · rcases Finset.mem_insert.mp hb with hvb | hbS
      · rw [hvb] at hab ⊢
        rw [Function.update_self, key a haS]
        rw [hleaf a haS hab.symm]
        exact hyN.symm
      · rw [key a haS, key b hbS]
        exact hhom a haS b hbS hab
  by_contra hcon
  rw [not_exists] at hcon
  have hconU : ∀ y ∈ nbr F {φ u} \ S.image φ,
      ¬ Inv F T (insert v S) (Function.update φ v y) d n := by
    intro y hy hInv'
    exact hcon (Function.update φ v y) ⟨hinjU y hy, hhomU y hy, hInv'⟩
  set fam : Finset (Finset V) := (Finset.univ : Finset (Finset V)).filter
    (fun X => X.card ≤ 2 * n ∧ Tight F T S φ d n X ∧
      Disjoint X ((S.filter (fun b => T.Adj v b)).image φ)) with hfam
  have hmem : ∀ X ∈ fam, X.card ≤ 2 * n ∧ Tight F T S φ d n X ∧
      Disjoint X ((S.filter (fun b => T.Adj v b)).image φ) := by
    intro X hX
    simp only [hfam, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    exact hX
  have hXn : ∀ X ∈ fam, X.card ≤ n := fun X hX =>
    (tight_card_le F T S φ d n hexp (hmem X hX).2.1 (hmem X hX).1).trans hS
  have hunion : ∀ t : Finset (Finset V), t ⊆ fam →
      Tight F T S φ d n (t.sup id) ∧ (t.sup id).card ≤ n := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      constructor
      · unfold Tight
        simp [Finset.sup_empty, Dsum_empty, nbr_empty]
      · rw [Finset.sup_empty]
        simp
    | insert a t hat ih =>
      intro ht
      have ha : a ∈ fam := ht (Finset.mem_insert_self a t)
      have ht' : t ⊆ fam := fun x hx => ht (Finset.mem_insert_of_mem hx)
      have h1 := ih ht'
      have h2 : Tight F T S φ d n a := (hmem a ha).2.1
      have h3 : a.card ≤ n := hXn a ha
      rw [Finset.sup_insert]
      exact tight_union F T S φ d n hexp hS hInv h2 h1.1 h3 h1.2
  have hXstarTight : Tight F T S φ d n (fam.sup id) := (hunion fam (Finset.Subset.refl fam)).1
  have hXstarN : (fam.sup id).card ≤ n := (hunion fam (Finset.Subset.refl fam)).2
  have hXstarDisj : Disjoint (fam.sup id) ((S.filter (fun b => T.Adj v b)).image φ) := by
    rw [Finset.disjoint_left]
    intro a haX haIm
    rw [Finset.mem_sup] at haX
    obtain ⟨b, hb, hab⟩ := haX
    exact Finset.disjoint_left.mp (hmem b hb).2.2 hab haIm
  have hcov : ∀ y ∈ nbr F {φ u} \ S.image φ, y ∈ nbr F (fam.sup id) := by
    intro y hy
    have hyW : y ∉ S.image φ := (Finset.mem_sdiff.mp hy).2
    obtain ⟨X, hXc, hXt, hyN, hXd⟩ :=
      fail_set F T S φ d n v y hv hInv hyW (hconU y hy)
    have hXf : X ∈ fam := by
      simp only [hfam, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hXc, hXt, hXd⟩
    exact nbr_mono (Finset.le_sup (f := id) hXf) hyN
  have hXu : φ u ∉ fam.sup id := by
    intro hmem'
    exact Finset.disjoint_left.mp hXstarDisj hmem'
      (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hadj.symm⟩, rfl⟩)
  have hsub : nbr F (insert (φ u) (fam.sup id)) \ S.image φ
      ⊆ nbr F (fam.sup id) \ S.image φ := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hz
    refine Finset.mem_sdiff.mpr ⟨?_, h2⟩
    rw [← Finset.singleton_union, nbr_union] at h1
    rcases Finset.mem_union.mp h1 with h1 | h1
    · exact hcov z (Finset.mem_sdiff.mpr ⟨h1, h2⟩)
    · exact h1
  have hdegS' : (S.filter (fun b => T.Adj u b)).card + 1 ≤ d := by
    have h1 : (S.filter (fun b => T.Adj u b)).card + 1
        = ((insert v S).filter (fun b => T.Adj u b)).card := by
      rw [Finset.filter_insert, if_pos hadj, Finset.card_insert_of_notMem]
      simp only [Finset.mem_filter, hv, false_and, not_false_eq_true]
    rw [h1]
    exact (card_filter_adj_le T (insert v S) u).trans (hdeg u)
  have hXc : (insert (φ u) (fam.sup id)).card ≤ 2 * n := by
    rw [Finset.card_insert_of_notMem hXu]
    omega
  have hI := hInv (insert (φ u) (fam.sup id)) hXc
  have hcollapse := Dsum_collapse (T := T) (S := S) (φ := φ) (X := fam.sup id) hu hXu hinj
  have hNbrle : (nbr F (insert (φ u) (fam.sup id)) \ S.image φ).card
      ≤ (nbr F (fam.sup id) \ S.image φ).card :=
    Finset.card_le_card hsub
  have hins : (insert (φ u) (fam.sup id)).card = (fam.sup id).card + 1 :=
    Finset.card_insert_of_notMem hXu
  unfold Tight at hXstarTight
  rw [hcollapse] at hI
  have hL : (d + 1) * (insert (φ u) (fam.sup id)).card
      = (d + 1) * (fam.sup id).card + (d + 1) := by rw [hins, Nat.mul_succ]
  omega

/-- **Friedman–Pippenger**: a `(2n, d+2)`-expander contains every tree with at most `n`
vertices and maximum degree at most `d`. -/
theorem embed_tree (F : SimpleGraph V) (T : SimpleGraph β) (d n : ℕ)
    (hexp : ∀ X : Finset V, X.card ≤ 2 * n → (d + 2) * X.card ≤ (ext F X).card)
    (hn : 1 ≤ n) (hV : Nonempty V) (hT : T.IsTree)
    (hdeg : ∀ v : β, (Finset.univ.filter (fun b => T.Adj v b)).card ≤ d)
    (hcard : Fintype.card β ≤ n) :
    ∃ φ : β → V, Function.Injective φ ∧ ∀ a b, T.Adj a b → F.Adj (φ a) (φ b) := by
  classical
  have key : ∀ i : ℕ, ∀ S : Finset β, S.card = i → (T.induce (↑S : Set β)).Connected →
      ∃ φ : β → V, (∀ a ∈ S, ∀ b ∈ S, φ a = φ b → a = b) ∧
        (∀ a ∈ S, ∀ b ∈ S, T.Adj a b → F.Adj (φ a) (φ b)) ∧ Inv F T S φ d n := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro S hScard hconn
      rcases Nat.eq_or_lt_of_le (Nat.zero_le i) with h0 | hpos
      · have hS0 : S.card = 0 := by omega
        rw [Finset.card_eq_zero] at hS0
        subst hS0
        exact absurd hconn.nonempty (by simp)
      rcases Nat.lt_or_ge 1 i with h2 | h1
      · obtain ⟨v, hvS, u, huS, hne, hadjv, huniq, hconn'⟩ :=
          peel_leaf T S hT hconn (by omega)
        have hu' : u ∈ S.erase v := Finset.mem_erase.mpr ⟨hne, huS⟩
        have hv' : v ∉ S.erase v := by simp
        have hcard' : (S.erase v).card = i - 1 := by
          rw [Finset.card_erase_of_mem hvS, hScard]
        obtain ⟨φ, hinj, hhom, hInv⟩ := ih (i - 1) (by omega) (S.erase v) hcard' hconn'
        obtain ⟨φ', hinj', hhom', hInv'⟩ :=
          extend_step F T d n hexp hn hdeg (S.erase v) φ v u hinj hhom hInv
            (by
              have hle : i ≤ Fintype.card β := hScard ▸ Finset.card_le_univ S
              rw [hcard']
              omega) hv' hu' hadjv (by
              intro b hb hba
              exact huniq b (Finset.mem_erase.mp hb).2 hba)
        refine ⟨φ', ?_, ?_, ?_⟩
        · intro a ha b hb
          refine hinj' a ?_ b ?_
          · rw [Finset.insert_erase hvS]; exact ha
          · rw [Finset.insert_erase hvS]; exact hb
        · intro a ha b hb
          refine hhom' a ?_ b ?_
          · rw [Finset.insert_erase hvS]; exact ha
          · rw [Finset.insert_erase hvS]; exact hb
        · have h : insert v (S.erase v) = S := Finset.insert_erase hvS
          rw [h] at hInv'
          exact hInv'
      · -- base case: `S` is a single vertex
        have hi1 : i = 1 := by omega
        have hS1 : S.card = 1 := by omega
        obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp hS1
        refine ⟨fun _ => hV.some, ?_, ?_, ?_⟩
        · intro a ha b hb _
          rw [Finset.mem_singleton] at ha hb
          rw [ha, hb]
        · intro a ha b hb hab
          rw [Finset.mem_singleton] at ha hb
          rw [ha, hb] at hab
          exact absurd hab (SimpleGraph.irrefl T)
        · intro X hXc
          have himg : ({(r)} : Finset β).image (fun _ => hV.some) = {hV.some} := by simp
          have hD : Dsum T {r} (fun _ => hV.some) X = 0 := by
            rw [Dsum, Finset.sum_singleton]
            simp [SimpleGraph.irrefl T]
          rw [himg, hD, Nat.add_zero]
          have h1 : (d + 2) * X.card ≤ (nbr F X).card := by
            have h2 := hexp X hXc
            have h3 : (ext F X).card ≤ (nbr F X).card :=
              Finset.card_le_card Finset.sdiff_subset
            exact h2.trans h3
          have h4 : (nbr F X).card ≤ (nbr F X \ {hV.some}).card + 1 := by
            have h5 := nbr_card_le_insert F X ∅ hV.some
            simpa using h5
          have hmul : (d + 2) * X.card = (d + 1) * X.card + X.card := by ring
          rcases Nat.eq_zero_or_pos X.card with hz | hzp
          · rw [hz, Nat.mul_zero]
            exact Nat.zero_le _
          · omega
  have hconnUniv : (T.induce (↑(Finset.univ : Finset β) : Set β)).Connected := by
    rw [Finset.coe_univ]
    exact (SimpleGraph.induceUnivIso T).connected_iff.mpr hT.connected
  obtain ⟨φ, hinj, hhom, _⟩ := key (Fintype.card β) Finset.univ rfl hconnUniv
  refine ⟨φ, ?_, ?_⟩
  · intro a b hab
    exact hinj a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  · intro a b hab
    exact hhom a (Finset.mem_univ a) b (Finset.mem_univ b) hab

end Embed

/-! ### Bridges from `embed_tree` to copies inside subgraphs

`embed_tree` produces an injective graph homomorphism out of a tree.  We package that as a
`SimpleGraph.Copy`, and we transfer the expander hypothesis to induced subgraphs so that the
2-colouring argument can work inside an arbitrary vertex set. -/

section Bridge

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {β : Type*} [Fintype β] [DecidableEq β]

/-- A `(2n, d+2)`-expander, in the shape consumed by `embed_tree`. -/
def Expander (F : SimpleGraph α) (d n : ℕ) : Prop :=
  ∀ X : Finset α, X.card ≤ 2 * n → (d + 2) * X.card ≤ (ext F X).card

/-- `IsExpOn` on the whole vertex set is the same as being an expander. -/
lemma expander_iff_isExpOn_univ (F : SimpleGraph α) (d n : ℕ) :
    Expander F d n ↔ IsExpOn F Finset.univ (2 * n) (d + 2) := by
  unfold Expander IsExpOn
  refine forall_congr' (fun X => ?_)
  have hU : X ⊆ (Finset.univ : Finset α) := Finset.subset_univ X
  rw [extIn_univ]
  exact ⟨fun h _ hc => h hc, fun h hc => h hU hc⟩

/-- The external neighbourhood of an induced subgraph, mapped back to the ambient vertex type. -/
lemma image_ext_induce (F : SimpleGraph α) (U : Finset α) (X : Finset ↥U) :
    (ext (F.induce (U : Set α)) X).image Subtype.val = extIn F U (X.image Subtype.val) := by
  classical
  ext z
  simp only [ext, extIn, Finset.mem_image, Finset.mem_sdiff, Finset.mem_inter, mem_nbr]
  constructor
  · rintro ⟨y, ⟨⟨x, hx, hxy⟩, hyX⟩, rfl⟩
    refine ⟨⟨⟨x.1, ⟨x, hx, rfl⟩, hxy⟩, ?_⟩, y.2⟩
    rintro ⟨x', hx', hx'z⟩
    exact hyX (Subtype.ext hx'z ▸ hx')
  · rintro ⟨⟨⟨x', hx', hxz⟩, hzX⟩, hzU⟩
    obtain ⟨x, hx, rfl⟩ := hx'
    exact ⟨⟨z, hzU⟩, ⟨⟨x, hx, hxz⟩, fun hy => hzX ⟨(⟨z, hzU⟩ : ↥U), hy, rfl⟩⟩, rfl⟩

lemma card_ext_induce (F : SimpleGraph α) (U : Finset α) (X : Finset ↥U) :
    (ext (F.induce (U : Set α)) X).card = (extIn F U (X.image Subtype.val)).card := by
  have h := congrArg Finset.card (image_ext_induce F U X)
  rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h

/-- The expander property transfers to the subgraph induced on a set. -/
lemma expander_induce {F : SimpleGraph α} {U : Finset α} {d n : ℕ}
    (h : IsExpOn F U (2 * n) (d + 2)) : Expander (F.induce (U : Set α)) d n := by
  classical
  intro X hX
  have himg : X.image Subtype.val ⊆ U := by
    intro z hz
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    exact y.2
  have hcard : (X.image Subtype.val).card = X.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hstep := h _ himg (by rw [hcard]; exact hX)
  rw [hcard] at hstep
  rw [card_ext_induce]
  exact hstep

/-- An expander contains every small tree, as a `Copy`. -/
lemma isContained_of_expander {F : SimpleGraph α} {T : SimpleGraph β} {d n : ℕ}
    (hexp : Expander F d n) (hn : 1 ≤ n) (hV : Nonempty α) (hT : T.IsTree)
    (hdeg : ∀ v : β, (Finset.univ.filter (fun b => T.Adj v b)).card ≤ d)
    (hcard : Fintype.card β ≤ n) : SimpleGraph.IsContained T F := by
  obtain ⟨φ, hinj, hhom⟩ := embed_tree F T d n hexp hn hV hT hdeg hcard
  exact ⟨SimpleGraph.Copy.mk ⟨φ, fun {a b} h => hhom a b h⟩ hinj⟩

end Bridge

/-! ### A sparse graph with no empty `(n, n)` bipartition

We sample a graph on `Fin N` from `r` self-maps `Fin N → Fin N`: the edges are the unordered
pairs `{u, f i u}`.  Such a graph has at most `r * N` edges, and a counting argument shows that
for a suitable `r` one of the samples has an edge between *every* two disjoint `n`-element sets.
-/

section Sparse

/-- The graph on `Fin N` generated by `r` self-maps: `u ~ v` when one is the image of the other
under one of the maps. -/
def funGraph (f : Fin r → Fin N → Fin N) : SimpleGraph (Fin N) where
  Adj u v := u ≠ v ∧ ∃ i : Fin r, f i u = v ∨ f i v = u
  symm := ⟨by
    rintro u v ⟨hne, i, hi | hi⟩
    · exact ⟨hne.symm, i, Or.inr hi⟩
    · exact ⟨hne.symm, i, Or.inl hi⟩⟩
  loopless := ⟨by
    rintro u ⟨h, -⟩
    exact h rfl⟩

@[simp] lemma funGraph_adj {N r : ℕ} (f : Fin r → Fin N → Fin N) (u v : Fin N) :
    (funGraph f).Adj u v ↔ u ≠ v ∧ ∃ i : Fin r, f i u = v ∨ f i v = u := Iff.rfl

lemma funGraph_edgeFinset_card_le {N r : ℕ} (f : Fin r → Fin N → Fin N) :
    (funGraph f).edgeFinset.card ≤ r * N := by
  classical
  have himg : (funGraph f).edgeFinset ⊆
      (Finset.univ : Finset (Fin r × Fin N)).image (fun p => s(p.2, f p.1 p.2)) := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨-, i, hi | hi⟩ := he
      · exact Finset.mem_image.mpr ⟨(i, a), Finset.mem_univ _, by rw [hi]⟩
      · exact Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, by rw [hi, Sym2.eq_swap]⟩
  calc (funGraph f).edgeFinset.card
      ≤ ((Finset.univ : Finset (Fin r × Fin N)).image (fun p => s(p.2, f p.1 p.2))).card :=
        Finset.card_le_card himg
    _ ≤ (Finset.univ : Finset (Fin r × Fin N)).card := Finset.card_image_le
    _ = r * N := by simp [Fintype.card_prod]

lemma funGraph_edgeSet_ncard_le {N r : ℕ} (f : Fin r → Fin N → Fin N) :
    (funGraph f).edgeSet.ncard ≤ r * N := by
  rw [Set.ncard_eq_toFinset_card']
  exact funGraph_edgeFinset_card_le f

end Sparse

/-! ### The counting argument

For a fixed pair of disjoint `n`-element sets `A`, `B` we bound the number of self-maps that avoid
`A × B`; a union bound over all such pairs then shows that some tuple of `r` maps has an edge
between every two disjoint `n`-element sets. -/

section Count

lemma card_funTuples (N r : ℕ) :
    Fintype.card (Fin r → Fin N → Fin N) = N ^ (r * N) := by
  rw [Fintype.card_pi]
  have h : ∀ i : Fin r, Fintype.card (Fin N → Fin N) = N ^ N := by
    intro i
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

/-- The number of self-maps of `Fin N` that avoid `B` on all of `A`, crudely bounded. -/
lemma goodFun_card_le {N n : ℕ} {A B : Finset (Fin N)} (hA : A.card = n) (hB : B.card = n) :
    (Finset.univ.filter (fun g : Fin N → Fin N => ∀ a ∈ A, g a ∉ B)).card
      ≤ (N - n) ^ n * N ^ (N - n) := by
  classical
  have hcompB : ((Finset.univ : Finset (Fin N)) \ B).card = N - n := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hB]
  have hAcard : Aᶜ.card = N - n := by
    rw [Finset.card_compl, Fintype.card_fin, hA]
  have hinj : Function.Injective
      (fun g : ↥(Finset.univ.filter (fun g : Fin N → Fin N => ∀ a ∈ A, g a ∉ B)) =>
        ((fun a : ↥A => (⟨g.1 a.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
              (Finset.mem_filter.mp g.2).2 a.1 a.2⟩⟩ :
            ↥((Finset.univ : Finset (Fin N)) \ B))),
         (fun x : ↥(Aᶜ) => g.1 x.1))) := by
    rintro g g' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine Subtype.ext (funext fun x => ?_)
    by_cases hx : x ∈ A
    · have hh := congrFun h1 ⟨x, hx⟩
      simpa using congrArg Subtype.val hh
    · have hh := congrFun h2 ⟨x, Finset.mem_compl.mpr hx⟩
      simpa using hh
  rw [← Fintype.card_coe (Finset.univ.filter (fun g : Fin N → Fin N => ∀ a ∈ A, g a ∉ B))]
  calc Fintype.card ↥(Finset.univ.filter (fun g : Fin N → Fin N => ∀ a ∈ A, g a ∉ B))
      ≤ Fintype.card ((↥A → ↥((Finset.univ : Finset (Fin N)) \ B)) × (↥(Aᶜ) → Fin N)) :=
        Fintype.card_le_of_injective _ hinj
    _ = (N - n) ^ n * N ^ (N - n) := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_coe,
          Fintype.card_coe, Fintype.card_coe, Fintype.card_fin, hA, hcompB, hAcard]

/-- The same bound for tuples of `r` self-maps: the constraint decouples over the `r` coordinates. -/
lemma badTuple_card_le {N r n : ℕ} {A B : Finset (Fin N)} (hA : A.card = n) (hB : B.card = n) :
    (Finset.univ.filter (fun f : Fin r → Fin N → Fin N => ∀ i, ∀ a ∈ A, f i a ∉ B)).card
      ≤ ((N - n) ^ n * N ^ (N - n)) ^ r := by
  classical
  have hcompB : ((Finset.univ : Finset (Fin N)) \ B).card = N - n := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hB]
  have hAcard : Aᶜ.card = N - n := by
    rw [Finset.card_compl, Fintype.card_fin, hA]
  have hinj : Function.Injective
      (fun f : ↥(Finset.univ.filter (fun f : Fin r → Fin N → Fin N => ∀ i, ∀ a ∈ A, f i a ∉ B)) =>
        (fun i : Fin r =>
          ((fun a : ↥A => (⟨f.1 i a.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
                (Finset.mem_filter.mp f.2).2 i a.1 a.2⟩⟩ :
              ↥((Finset.univ : Finset (Fin N)) \ B))),
           (fun x : ↥(Aᶜ) => f.1 i x.1)))) := by
    rintro f f' h
    simp only [funext_iff, Prod.mk.injEq] at h
    refine Subtype.ext (funext fun i => funext fun x => ?_)
    by_cases hx : x ∈ A
    · have hh : (⟨f.1 i x, ⋯⟩ : ↥((Finset.univ : Finset (Fin N)) \ B)) =
          ⟨f'.1 i x, ⋯⟩ := (h i).1 ⟨x, hx⟩
      simpa using congrArg Subtype.val hh
    · have hh : f.1 i x = f'.1 i x := (h i).2 ⟨x, Finset.mem_compl.mpr hx⟩
      simpa using hh
  rw [← Fintype.card_coe
    (Finset.univ.filter (fun f : Fin r → Fin N → Fin N => ∀ i, ∀ a ∈ A, f i a ∉ B))]
  calc Fintype.card ↥(Finset.univ.filter (fun f : Fin r → Fin N → Fin N => ∀ i, ∀ a ∈ A, f i a ∉ B))
      ≤ Fintype.card (Fin r → ((↥A → ↥((Finset.univ : Finset (Fin N)) \ B)) × (↥(Aᶜ) → Fin N))) :=
        Fintype.card_le_of_injective _ hinj
    _ = ((N - n) ^ n * N ^ (N - n)) ^ r := by
        rw [Fintype.card_pi]
        have h : ∀ i : Fin r, Fintype.card ((↥A → ↥((Finset.univ : Finset (Fin N)) \ B)) × (↥(Aᶜ) → Fin N))
            = (N - n) ^ n * N ^ (N - n) := by
          intro i
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_coe,
            Fintype.card_coe, Fintype.card_coe, Fintype.card_fin, hA, hcompB, hAcard]
        rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- The pairs of disjoint `n`-element vertex sets. -/
def pairs (N n : ℕ) : Finset (Finset (Fin N) × Finset (Fin N)) :=
  ((Finset.univ.filter (fun A : Finset (Fin N) => A.card = n)).product
    (Finset.univ.filter (fun B : Finset (Fin N) => B.card = n))).filter
      (fun p => Disjoint p.1 p.2)

lemma mem_pairs {N n : ℕ} {p : Finset (Fin N) × Finset (Fin N)} :
    p ∈ pairs N n ↔ p.1.card = n ∧ p.2.card = n ∧ Disjoint p.1 p.2 := by
  classical
  simp [pairs, and_assoc]

lemma pairs_card_le (N n : ℕ) : (pairs N n).card ≤ 4 ^ N := by
  classical
  have h1 : pairs N n ⊆
      (Finset.univ.filter (fun A : Finset (Fin N) => A.card = n)).product
        (Finset.univ.filter (fun B : Finset (Fin N) => B.card = n)) :=
    Finset.filter_subset _ _
  have h2 : (Finset.univ.filter (fun A : Finset (Fin N) => A.card = n)).card ≤ 2 ^ N := by
    have h := Finset.card_le_card
      (Finset.filter_subset (fun A : Finset (Fin N) => A.card = n) Finset.univ)
    rwa [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h
  calc (pairs N n).card
      ≤ ((Finset.univ.filter (fun A : Finset (Fin N) => A.card = n)).product
          (Finset.univ.filter (fun B : Finset (Fin N) => B.card = n))).card :=
        Finset.card_le_card h1
    _ = _ * _ := Finset.card_product _ _
    _ ≤ 2 ^ N * 2 ^ N := Nat.mul_le_mul h2 h2
    _ = 4 ^ N := by rw [← pow_add, show N + N = 2 * N by ring, pow_mul]; norm_num

/-- The numerical core.  For a constant `c ≥ 2`, `n ≥ 1` and `r = (c-1)(2c+1)`,
`4 ^ (c*n) * ((c-1)*n) ^ (n*r) * (c*n) ^ ((c-1)*n*r) < (c*n) ^ (r*(c*n))`.
The loss comes from `(c/(c-1)) ^ r ≥ 2 ^ (2c+1) > 4 ^ c`, via Bernoulli's inequality. -/
lemma pow_arith (c n r : ℕ) (hc : 2 ≤ c) (hn : 1 ≤ n) (hr : r = (c - 1) * (2 * c + 1)) :
    (4 : ℝ) ^ (c * n) * (((c - 1 : ℕ) : ℝ) * n) ^ (n * r) *
        ((c : ℝ) * n) ^ ((c - 1) * n * r)
      < ((c : ℝ) * n) ^ (r * (c * n)) := by
  have hc1 : 1 ≤ c := by omega
  have hcR : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hk : (0 : ℝ) < (c : ℝ) - 1 := by linarith
  have hk' : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    rw [Nat.cast_sub hc1, Nat.cast_one]
  have hbern : (2 : ℝ) ≤ (1 + 1 / ((c : ℝ) - 1)) ^ (c - 1) := by
    have h1 : (1 : ℝ) + ((c - 1 : ℕ) : ℝ) * (1 / ((c : ℝ) - 1)) ≤
        (1 + 1 / ((c : ℝ) - 1)) ^ (c - 1) :=
      one_add_mul_le_pow (a := 1 / ((c : ℝ) - 1)) (by
        have hpos : (0 : ℝ) < 1 / ((c : ℝ) - 1) := by positivity
        linarith) (c - 1)
    have h2 : (1 : ℝ) + ((c - 1 : ℕ) : ℝ) * (1 / ((c : ℝ) - 1)) = 2 := by
      rw [hk']
      field_simp
      norm_num
    linarith
  have hpow2 : (4 : ℝ) ^ c < (1 + 1 / ((c : ℝ) - 1)) ^ r := by
    have h3 : (1 + 1 / ((c : ℝ) - 1)) ^ r =
        ((1 + 1 / ((c : ℝ) - 1)) ^ (c - 1)) ^ (2 * c + 1) := by
      rw [hr, pow_mul]
    rw [h3]
    have h5 : (4 : ℝ) ^ c < (2 : ℝ) ^ (2 * c + 1) := by
      have h6 : (4 : ℝ) ^ c = 2 ^ (2 * c) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      rw [h6]
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    have h4 : (2 : ℝ) ^ (2 * c + 1) ≤ ((1 + 1 / ((c : ℝ) - 1)) ^ (c - 1)) ^ (2 * c + 1) :=
      pow_le_pow_left₀ (by norm_num) hbern _
    linarith
  have hfield : ((c : ℝ) - 1) * (1 + 1 / ((c : ℝ) - 1)) = (c : ℝ) := by
    field_simp
    ring
  have hbase : (4 : ℝ) ^ c * ((c : ℝ) - 1) ^ r < (c : ℝ) ^ r := by
    have hmul : ((c : ℝ) - 1) ^ r * (4 : ℝ) ^ c <
        ((c : ℝ) - 1) ^ r * (1 + 1 / ((c : ℝ) - 1)) ^ r :=
      mul_lt_mul_of_pos_left hpow2 (pow_pos hk r)
    calc (4 : ℝ) ^ c * ((c : ℝ) - 1) ^ r = ((c : ℝ) - 1) ^ r * (4 : ℝ) ^ c := by ring
      _ < ((c : ℝ) - 1) ^ r * (1 + 1 / ((c : ℝ) - 1)) ^ r := hmul
      _ = (((c : ℝ) - 1) * (1 + 1 / ((c : ℝ) - 1))) ^ r := (mul_pow _ _ r).symm
      _ = (c : ℝ) ^ r := by rw [hfield]
  have hkey : (4 : ℝ) ^ c * (((c - 1 : ℕ) : ℝ)) ^ r < (c : ℝ) ^ r := by
    rw [hk']
    exact hbase
  have hstep : (4 : ℝ) ^ (c * n) * (((c - 1 : ℕ) : ℝ)) ^ (r * n) < (c : ℝ) ^ (r * n) := by
    have h := pow_lt_pow_left₀ hkey (by positivity) (by omega : n ≠ 0)
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at h
    exact h
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hstep2 : (4 : ℝ) ^ (c * n) * (((c - 1 : ℕ) : ℝ) * n) ^ (r * n) <
      ((c : ℝ) * n) ^ (r * n) := by
    have hmul := mul_lt_mul_of_pos_right hstep (pow_pos hnpos (r * n))
    calc (4 : ℝ) ^ (c * n) * (((c - 1 : ℕ) : ℝ) * n) ^ (r * n)
        = (4 : ℝ) ^ (c * n) * ((((c - 1 : ℕ) : ℝ)) ^ (r * n) * (n : ℝ) ^ (r * n)) := by
          rw [mul_pow]
      _ = ((4 : ℝ) ^ (c * n) * (((c - 1 : ℕ) : ℝ)) ^ (r * n)) * (n : ℝ) ^ (r * n) := by ring
      _ < ((c : ℝ) ^ (r * n)) * (n : ℝ) ^ (r * n) := hmul
      _ = ((c : ℝ) * n) ^ (r * n) := (mul_pow _ _ _).symm
  have hlast : (0 : ℝ) < ((c : ℝ) * n) ^ ((c - 1) * n * r) := by
    apply pow_pos
    have hcpos : (0 : ℝ) < (c : ℝ) := by linarith
    positivity
  have hidx : r * n + (c - 1) * n * r = r * (c * n) := by
    have h1 : n + (c - 1) * n = c * n := by
      calc n + (c - 1) * n = 1 * n + (c - 1) * n := by rw [Nat.one_mul]
        _ = (1 + (c - 1)) * n := (Nat.add_mul 1 (c - 1) n).symm
        _ = c * n := by rw [show 1 + (c - 1) = c by omega]
    calc r * n + (c - 1) * n * r = r * n + r * ((c - 1) * n) := by ring
      _ = r * (n + (c - 1) * n) := by ring
      _ = r * (c * n) := by rw [h1]
  calc (4 : ℝ) ^ (c * n) * (((c - 1 : ℕ) : ℝ) * n) ^ (n * r) *
        ((c : ℝ) * n) ^ ((c - 1) * n * r)
      = (4 : ℝ) ^ (c * n) * (((c - 1 : ℕ) : ℝ) * n) ^ (r * n) *
          ((c : ℝ) * n) ^ ((c - 1) * n * r) := by rw [Nat.mul_comm n r]
    _ < ((c : ℝ) * n) ^ (r * n) * ((c : ℝ) * n) ^ ((c - 1) * n * r) :=
        mul_lt_mul_of_pos_right hstep2 hlast
    _ = ((c : ℝ) * n) ^ (r * n + (c - 1) * n * r) := (pow_add _ _ _).symm
    _ = ((c : ℝ) * n) ^ (r * (c * n)) := by rw [hidx]

/-- **The sparse hole-free graph.**  With `N = c₁ * n` and `r = (c₁-1)(2c₁+1)`, some tuple of
`r` self-maps of `Fin N` has an edge between every two disjoint `n`-element sets. -/
lemma exists_holeFree {N r n : ℕ} (hn : 1 ≤ n) (hN : n < N)
    (hmain : 4 ^ N * ((N - n) ^ n * N ^ (N - n)) ^ r < N ^ (r * N)) :
    ∃ f : Fin r → Fin N → Fin N, HoleFree (funGraph f) n := by
  classical
  set Bad : Finset (Fin r → Fin N → Fin N) :=
    Finset.univ.filter (fun f => ¬ HoleFree (funGraph f) n) with hBad
  have hsub : Bad ⊆ (pairs N n).biUnion
      (fun p => Finset.univ.filter
        (fun f : Fin r → Fin N → Fin N => ∀ i, ∀ a ∈ p.1, f i a ∉ p.2)) := by
    intro f hf
    simp only [hBad, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [HoleFree] at hf
    push_neg at hf
    obtain ⟨A, B, hAc, hBc, hdisj, hno⟩ := hf
    rw [Finset.mem_biUnion]
    refine ⟨(A, B), mem_pairs.mpr ⟨hAc, hBc, hdisj⟩, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i a ha hga
    have hane : a ≠ f i a := fun h => (Finset.disjoint_left.mp hdisj ha) (h ▸ hga)
    exact hno a ha (f i a) hga ⟨hane, i, Or.inl rfl⟩
  have hbound : Bad.card ≤ 4 ^ N * ((N - n) ^ n * N ^ (N - n)) ^ r := by
    calc Bad.card
        ≤ ((pairs N n).biUnion (fun p => Finset.univ.filter
            (fun f : Fin r → Fin N → Fin N => ∀ i, ∀ a ∈ p.1, f i a ∉ p.2))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p ∈ pairs N n,
            (Finset.univ.filter
              (fun f : Fin r → Fin N → Fin N => ∀ i, ∀ a ∈ p.1, f i a ∉ p.2)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ pairs N n, ((N - n) ^ n * N ^ (N - n)) ^ r := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          exact badTuple_card_le (mem_pairs.mp hp).1 (mem_pairs.mp hp).2.1
      _ = (pairs N n).card * ((N - n) ^ n * N ^ (N - n)) ^ r := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 4 ^ N * ((N - n) ^ n * N ^ (N - n)) ^ r :=
          Nat.mul_le_mul_right _ (pairs_card_le N n)
  by_contra hcon
  push_neg at hcon
  have hAll : Bad = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro f _
    exact hcon f
  have hbig : Bad.card = N ^ (r * N) := by
    rw [hAll, Finset.card_univ, card_funTuples]
  have : Bad.card < N ^ (r * N) := lt_of_le_of_lt hbound hmain
  rw [hbig] at this
  exact absurd this (lt_irrefl _)

end Count

/-! ### Growing a set with a small external neighbourhood

If a colour class is not an expander, its failure is witnessed by a set `U` with
`|N(U) \ U| ≤ (d+2)|U|` that can be taken maximal below `M + 2n`.  Either every such maximal set
has size below `M`, in which case the complement is an expander, or we obtain a set of size at
least `M` with a small external neighbourhood. -/

section Grow

variable {N : ℕ}

lemma nbr_union_sdiff_subset (R : SimpleGraph (Fin N)) (U S : Finset (Fin N))
    (hSW : S ⊆ Finset.univ \ U) :
    nbr R (U ∪ S) \ (U ∪ S) ⊆ (nbr R U \ U) ∪ extIn R (Finset.univ \ U) S := by
  intro y hy
  rw [Finset.mem_sdiff] at hy
  obtain ⟨hyN, hyNot⟩ := hy
  rw [Finset.mem_union] at hyNot
  push_neg at hyNot
  obtain ⟨hyU, hyS⟩ := hyNot
  rw [mem_nbr] at hyN
  obtain ⟨x, hxUS, hxy⟩ := hyN
  rw [Finset.mem_union] at hxUS
  rcases hxUS with hxU | hxS
  · rw [Finset.mem_union]
    exact Or.inl (by
      rw [Finset.mem_sdiff]
      exact ⟨by rw [mem_nbr]; exact ⟨x, hxU, hxy⟩, hyU⟩)
  · rw [Finset.mem_union]
    exact Or.inr (by
      rw [extIn, Finset.mem_inter, Finset.mem_sdiff]
      exact ⟨⟨by rw [mem_nbr]; exact ⟨x, hxS, hxy⟩, hyS⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyU⟩⟩)

/-- **Red dichotomy**: `R` is an expander on some nonempty vertex set, or there is a set of size
between `M` and `M + 2n` with a small external red neighbourhood. -/
lemma red_dichotomy (R : SimpleGraph (Fin N)) (d n M : ℕ) (hn : 1 ≤ n) (hMN : M < N) :
    (∃ W : Finset (Fin N), W.Nonempty ∧ Expander (R.induce (W : Set (Fin N))) d n) ∨
      ∃ U : Finset (Fin N), M ≤ U.card ∧ U.card < M + 2 * n ∧
        (nbr R U \ U).card ≤ (d + 2) * U.card := by
  classical
  obtain ⟨U, hUA, hUmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun U : Finset (Fin N) =>
      U.card < M + 2 * n ∧ (nbr R U \ U).card ≤ (d + 2) * U.card))
    (fun U => U.card)
    ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simp only [Finset.card_empty]; omega, by simp [nbr_empty]⟩⟩
  have hUcard : U.card < M + 2 * n := (Finset.mem_filter.mp hUA).2.1
  have hUnbr : (nbr R U \ U).card ≤ (d + 2) * U.card := (Finset.mem_filter.mp hUA).2.2
  rcases Nat.lt_or_ge U.card M with hlt | hge
  · refine Or.inl ⟨Finset.univ \ U, ?_, ?_⟩
    · refine Finset.nonempty_iff_ne_empty.mpr ?_
      intro hsub
      have hsub' : (Finset.univ : Finset (Fin N)) ⊆ U := Finset.sdiff_eq_empty_iff_subset.mp hsub
      have hUuniv : U = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ U) hsub'
      rw [hUuniv, Finset.card_univ, Fintype.card_fin] at hlt
      omega
    · apply expander_induce
      intro S hSW hSc
      by_contra hcon
      have hlt2 : (extIn R (Finset.univ \ U) S).card < (d + 2) * S.card := not_le.mp hcon
      have hSpos : 0 < S.card := by
        rcases Nat.eq_zero_or_pos S.card with h0 | hpos
        · rw [h0, Nat.mul_zero] at hlt2
          omega
        · exact hpos
      have hdisj : Disjoint U S := by
        rw [Finset.disjoint_left]
        intro x hxU hxS
        have hx := hSW hxS
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
        exact hx hxU
      have hmem : U ∪ S ∈ Finset.univ.filter (fun U : Finset (Fin N) =>
          U.card < M + 2 * n ∧ (nbr R U \ U).card ≤ (d + 2) * U.card) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨by rw [Finset.card_union_of_disjoint hdisj]; omega, ?_⟩
        rw [Finset.card_union_of_disjoint hdisj]
        have h1 : (nbr R (U ∪ S) \ (U ∪ S)).card ≤
            (nbr R U \ U).card + (extIn R (Finset.univ \ U) S).card :=
          calc (nbr R (U ∪ S) \ (U ∪ S)).card
              ≤ ((nbr R U \ U) ∪ extIn R (Finset.univ \ U) S).card :=
                Finset.card_le_card (nbr_union_sdiff_subset R U S hSW)
            _ ≤ _ := Finset.card_union_le _ _
        calc (nbr R (U ∪ S) \ (U ∪ S)).card
            ≤ (nbr R U \ U).card + (extIn R (Finset.univ \ U) S).card := h1
          _ ≤ (d + 2) * U.card + (d + 2) * S.card := Nat.add_le_add hUnbr (le_of_lt hlt2)
          _ = (d + 2) * (U.card + S.card) := by ring
      have hbig := hUmax (U ∪ S) hmem
      rw [Finset.card_union_of_disjoint hdisj] at hbig
      omega
  · exact Or.inr ⟨U, hge, hUcard, hUnbr⟩

lemma nbr_inter_sdiff_subset (Bl : SimpleGraph (Fin N)) (V T S : Finset (Fin N))
    (hST : S ⊆ V \ T) :
    (nbr Bl (T ∪ S) ∩ V) \ (T ∪ S) ⊆ ((nbr Bl T ∩ V) \ T) ∪ extIn Bl (V \ T) S := by
  intro y hy
  rw [Finset.mem_sdiff, Finset.mem_inter] at hy
  obtain ⟨⟨hyN, hyV⟩, hyNot⟩ := hy
  rw [Finset.mem_union] at hyNot
  push_neg at hyNot
  obtain ⟨hyT, hyS⟩ := hyNot
  rw [mem_nbr] at hyN
  obtain ⟨x, hxTS, hxy⟩ := hyN
  rw [Finset.mem_union] at hxTS
  rcases hxTS with hxT | hxS
  · rw [Finset.mem_union]
    exact Or.inl (by
      rw [Finset.mem_sdiff, Finset.mem_inter]
      exact ⟨⟨by rw [mem_nbr]; exact ⟨x, hxT, hxy⟩, hyV⟩, hyT⟩)
  · rw [Finset.mem_union]
    exact Or.inr (by
      rw [extIn, Finset.mem_inter, Finset.mem_sdiff]
      exact ⟨⟨by rw [mem_nbr]; exact ⟨x, hxS, hxy⟩, hyS⟩,
        Finset.mem_sdiff.mpr ⟨hyV, hyT⟩⟩)

/-- **Blue step.**  Let `U` and `W` be disjoint with no red edge between them, `|U| ≥ M` and
`|W| ≥ M + 4(d+3)n`, where `M ≥ 4(d+3)n + n`.  Then the blue graph is an expander on some
nonempty subset of `U ∪ W`.  (The alternative would produce an empty `(n, n)` bipartition of
`F`, which is excluded by `HoleFree`.) -/
lemma blue_dichotomy {F R Bl : SimpleGraph (Fin N)} {d n M : ℕ} (U W : Finset (Fin N))
    (hUW : Disjoint U W) (hnoRed : ∀ a ∈ U, ∀ b ∈ W, ¬ R.Adj a b)
    (hcover : ∀ a b, F.Adj a b → R.Adj a b ∨ Bl.Adj a b)
    (hhole : HoleFree F n) (hn : 1 ≤ n)
    (hM1 : 2 * n ≤ M) (hM2 : 4 * (d + 3) * n + n ≤ M)
    (hU : M ≤ U.card) (hW : M + 4 * (d + 3) * n ≤ W.card) :
    ∃ V₁ : Finset (Fin N), V₁.Nonempty ∧ V₁ ⊆ U ∪ W ∧
      Expander (Bl.induce (V₁ : Set (Fin N))) d n := by
  classical
  set V : Finset (Fin N) := U ∪ W with hV
  have hVcard : V.card = U.card + W.card := by
    rw [hV, Finset.card_union_of_disjoint hUW]
  have hVbig : M ≤ V.card := by rw [hVcard]; omega
  obtain ⟨T, hTA, hTmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun T : Finset (Fin N) =>
      T ⊆ V ∧ T.card < 4 * n ∧ ((nbr Bl T ∩ V) \ T).card ≤ (d + 2) * T.card))
    (fun T => T.card)
    ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Finset.empty_subset _, by rw [Finset.card_empty]; omega,
        by rw [nbr_empty]; simp⟩⟩
  obtain ⟨hTV, hTcard, hTnbr⟩ := (Finset.mem_filter.mp hTA).2
  rcases Nat.lt_or_ge T.card (2 * n) with hlt | hge
  · refine ⟨V \ T, ?_, Finset.sdiff_subset, ?_⟩
    · refine Finset.nonempty_iff_ne_empty.mpr ?_
      intro hempty
      have hsub : V ⊆ T := Finset.sdiff_eq_empty_iff_subset.mp hempty
      have hle := Finset.card_le_card hsub
      omega
    · apply expander_induce
      intro S hST hSc
      by_contra hcon
      have hlt2 : (extIn Bl (V \ T) S).card < (d + 2) * S.card := not_le.mp hcon
      have hSpos : 0 < S.card := by
        rcases Nat.eq_zero_or_pos S.card with h0 | hpos
        · rw [h0, Nat.mul_zero] at hlt2
          omega
        · exact hpos
      have hdisj : Disjoint T S := by
        rw [Finset.disjoint_left]
        intro x hxT hxS
        have hx := hST hxS
        simp only [Finset.mem_sdiff] at hx
        exact hx.2 hxT
      have hmem : T ∪ S ∈ Finset.univ.filter (fun T : Finset (Fin N) =>
          T ⊆ V ∧ T.card < 4 * n ∧ ((nbr Bl T ∩ V) \ T).card ≤ (d + 2) * T.card) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, by rw [Finset.card_union_of_disjoint hdisj]; omega, ?_⟩
        · intro x hx
          rw [Finset.mem_union] at hx
          rcases hx with hx | hx
          · exact hTV hx
          · exact Finset.mem_sdiff.mp (hST hx) |>.1
        · rw [Finset.card_union_of_disjoint hdisj]
          have h1 : ((nbr Bl (T ∪ S) ∩ V) \ (T ∪ S)).card ≤
              ((nbr Bl T ∩ V) \ T).card + (extIn Bl (V \ T) S).card :=
            calc ((nbr Bl (T ∪ S) ∩ V) \ (T ∪ S)).card
                ≤ (((nbr Bl T ∩ V) \ T) ∪ extIn Bl (V \ T) S).card :=
                  Finset.card_le_card (nbr_inter_sdiff_subset Bl V T S hST)
              _ ≤ _ := Finset.card_union_le _ _
          calc ((nbr Bl (T ∪ S) ∩ V) \ (T ∪ S)).card
              ≤ ((nbr Bl T ∩ V) \ T).card + (extIn Bl (V \ T) S).card := h1
            _ ≤ (d + 2) * T.card + (d + 2) * S.card := Nat.add_le_add hTnbr (le_of_lt hlt2)
            _ = (d + 2) * (T.card + S.card) := by ring
      have hbig := hTmax (T ∪ S) hmem
      rw [Finset.card_union_of_disjoint hdisj] at hbig
      omega
  · exfalso
    have hTsub : T ⊆ U ∪ W := hV ▸ hTV
    have hXcard : (T ∪ (nbr Bl T ∩ V)).card < 4 * (d + 3) * n := by
      have heq : T ∪ (nbr Bl T ∩ V) = T ∪ ((nbr Bl T ∩ V) \ T) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_sdiff]
        tauto
      rw [heq]
      have hdisj : Disjoint T ((nbr Bl T ∩ V) \ T) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [Finset.mem_sdiff] at hx'
        exact hx'.2 hx
      rw [Finset.card_union_of_disjoint hdisj]
      have hle : T.card + ((nbr Bl T ∩ V) \ T).card ≤ (d + 3) * T.card := by
        calc T.card + ((nbr Bl T ∩ V) \ T).card ≤ T.card + (d + 2) * T.card :=
              Nat.add_le_add_left hTnbr _
          _ = (d + 3) * T.card := by ring
      have hlt4 : (d + 3) * T.card < (d + 3) * (4 * n) :=
        Nat.mul_lt_mul_of_pos_left hTcard (by omega)
      calc T.card + ((nbr Bl T ∩ V) \ T).card ≤ (d + 3) * T.card := hle
        _ < (d + 3) * (4 * n) := hlt4
        _ = 4 * (d + 3) * n := by ring
    have hsplit : n ≤ (T ∩ U).card ∨ n ≤ (T ∩ W).card := by
      by_contra hc
      push_neg at hc
      obtain ⟨h1, h2⟩ := hc
      have heq : T = T ∩ U ∪ T ∩ W := by
        ext x
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · intro hx
          rcases Finset.mem_union.mp (hTsub hx) with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩
        · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      have hdisj : Disjoint (T ∩ U) (T ∩ W) := by
        rw [Finset.disjoint_left]
        intro x hx hy
        exact (Finset.disjoint_left.mp hUW) (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hy).2
      have hcard : T.card = (T ∩ U).card + (T ∩ W).card := by
        conv_lhs => rw [heq]
        rw [Finset.card_union_of_disjoint hdisj]
      omega
    rcases hsplit with hcase | hcase
    · obtain ⟨A, hATU, hAcard⟩ := Finset.exists_subset_card_eq hcase
      have hAU : A ⊆ U := fun x hx => (Finset.mem_inter.mp (hATU hx)).2
      have hAT : A ⊆ T := fun x hx => (Finset.mem_inter.mp (hATU hx)).1
      have hWn : n ≤ (W \ (T ∪ (nbr Bl T ∩ V))).card := by
        have hsub : W ⊆ (W \ (T ∪ (nbr Bl T ∩ V))) ∪ (T ∪ (nbr Bl T ∩ V)) := by
          intro x hx
          by_cases hxX : x ∈ T ∪ (nbr Bl T ∩ V)
          · exact Finset.mem_union_right _ hxX
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxX⟩)
        have h1 : W.card ≤ ((W \ (T ∪ (nbr Bl T ∩ V))) ∪ (T ∪ (nbr Bl T ∩ V))).card :=
          Finset.card_le_card hsub
        have h2 : ((W \ (T ∪ (nbr Bl T ∩ V))) ∪ (T ∪ (nbr Bl T ∩ V))).card ≤
            (W \ (T ∪ (nbr Bl T ∩ V))).card + (T ∪ (nbr Bl T ∩ V)).card :=
          Finset.card_union_le _ _
        omega
      obtain ⟨B', hBX, hBcard⟩ := Finset.exists_subset_card_eq hWn
      have hBW : B' ⊆ W := fun x hx => (Finset.mem_sdiff.mp (hBX hx)).1
      have hBnotX : ∀ x ∈ B', x ∉ T ∪ (nbr Bl T ∩ V) := fun x hx =>
        (Finset.mem_sdiff.mp (hBX hx)).2
      have hdisjAB : Disjoint A B' := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        exact (Finset.disjoint_left.mp hUW) (hAU hx) (hBW hx')
      obtain ⟨a, haA, b, hbB, hab⟩ := hhole A B' hAcard hBcard hdisjAB
      rcases hcover a b hab with hR | hBl
      · exact hnoRed a (hAU haA) b (hBW hbB) hR
      · have hbT : b ∈ nbr Bl T := by rw [mem_nbr]; exact ⟨a, hAT haA, hBl⟩
        have hbV : b ∈ V := by rw [hV]; exact Finset.mem_union_right _ (hBW hbB)
        exact hBnotX b hbB (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hbT, hbV⟩))
    · obtain ⟨A, hATW, hAcard⟩ := Finset.exists_subset_card_eq hcase
      have hAW : A ⊆ W := fun x hx => (Finset.mem_inter.mp (hATW hx)).2
      have hAT : A ⊆ T := fun x hx => (Finset.mem_inter.mp (hATW hx)).1
      have hUn : n ≤ (U \ (T ∪ (nbr Bl T ∩ V))).card := by
        have hsub : U ⊆ (U \ (T ∪ (nbr Bl T ∩ V))) ∪ (T ∪ (nbr Bl T ∩ V)) := by
          intro x hx
          by_cases hxX : x ∈ T ∪ (nbr Bl T ∩ V)
          · exact Finset.mem_union_right _ hxX
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxX⟩)
        have h1 : U.card ≤ ((U \ (T ∪ (nbr Bl T ∩ V))) ∪ (T ∪ (nbr Bl T ∩ V))).card :=
          Finset.card_le_card hsub
        have h2 : ((U \ (T ∪ (nbr Bl T ∩ V))) ∪ (T ∪ (nbr Bl T ∩ V))).card ≤
            (U \ (T ∪ (nbr Bl T ∩ V))).card + (T ∪ (nbr Bl T ∩ V)).card :=
          Finset.card_union_le _ _
        omega
      obtain ⟨B', hBX, hBcard⟩ := Finset.exists_subset_card_eq hUn
      have hBU : B' ⊆ U := fun x hx => (Finset.mem_sdiff.mp (hBX hx)).1
      have hBnotX : ∀ x ∈ B', x ∉ T ∪ (nbr Bl T ∩ V) := fun x hx =>
        (Finset.mem_sdiff.mp (hBX hx)).2
      have hdisjAB : Disjoint A B' := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        exact (Finset.disjoint_left.mp hUW) (hBU hx') (hAW hx)
      obtain ⟨a, haA, b, hbB, hab⟩ := hhole A B' hAcard hBcard hdisjAB
      rcases hcover a b hab with hR | hBl
      · exact hnoRed b (hBU hbB) a (hAW haA) hR.symm
      · have hbT : b ∈ nbr Bl T := by rw [mem_nbr]; exact ⟨a, hAT haA, hBl⟩
        have hbV : b ∈ V := by rw [hV]; exact Finset.mem_union_left _ (hBU hbB)
        exact hBnotX b hbB (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hbT, hbV⟩))

end Grow

/-! ### Assembling the argument -/

section Final

/-- A copy in an induced subgraph is a copy in the ambient graph. -/
lemma isContained_of_induce {α β : Type*} {G : SimpleGraph α} {W : Finset α}
    {T : SimpleGraph β} (h : SimpleGraph.IsContained T (G.induce (W : Set α))) :
    SimpleGraph.IsContained T G := by
  classical
  obtain ⟨c⟩ := h
  refine ⟨SimpleGraph.Copy.mk
    ⟨fun x => (c x).1, fun {a b} hab => (c.toHom.map_adj hab : G.Adj (c a).1 (c b).1)⟩
    (fun a b hab => c.injective (Subtype.ext hab))⟩

/-- **Monochromatic copy.**  A 2-colouring of a hole-free graph on `c₁ n` vertices contains a
monochromatic copy of every tree with at most `n` vertices and maximum degree at most `d`. -/
theorem colour_copy {β : Type*} [Fintype β] [DecidableEq β] {N n d : ℕ}
    (T : SimpleGraph β) (F R : SimpleGraph (Fin N))
    (hhole : HoleFree F n) (hn : 1 ≤ n) (hT : T.IsTree)
    (hdeg : ∀ v : β, (Finset.univ.filter (fun b => T.Adj v b)).card ≤ d)
    (hcard : Fintype.card β ≤ n)
    (hN : N = ((d + 3) * (4 * d + 15) + (4 * d + 13) + 4 * (d + 3)) * n) :
    SimpleGraph.IsContained T R ∨ SimpleGraph.IsContained T (F \ R) := by
  classical
  have hMN : (4 * d + 13) * n < N := by
    rw [hN]
    have h1 : 4 * d + 13 + 1 ≤ (d + 3) * (4 * d + 15) + (4 * d + 13) + 4 * (d + 3) := by
      have h2 : (4 * d + 13 : ℕ) ≤ (d + 3) * (4 * d + 15) + (4 * d + 13) := Nat.le_add_left _ _
      have h3 : (d + 3) * (4 * d + 15) + (4 * d + 13) ≤
          (d + 3) * (4 * d + 15) + (4 * d + 13) + 4 * (d + 3) := Nat.le_add_right _ _
      omega
    calc (4 * d + 13) * n < (4 * d + 13 + 1) * n :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega : 0 < n)
      _ ≤ _ * n := Nat.mul_le_mul_right _ h1
  rcases red_dichotomy R d n ((4 * d + 13) * n) hn hMN with
      ⟨W, hWne, hWexp⟩ | ⟨U, hUcard, hUlt, hUnbr⟩
  · obtain ⟨w, hw⟩ := hWne
    exact Or.inl (isContained_of_induce (W := W)
      (isContained_of_expander hWexp hn ⟨⟨w, hw⟩⟩ hT hdeg hcard))
  · refine Or.inr ?_
    have hUW' : Disjoint U (Finset.univ \ (U ∪ nbr R U)) := by
      rw [Finset.disjoint_left]
      intro x hxU hxW
      exact (Finset.mem_sdiff.mp hxW).2 (Finset.mem_union_left _ hxU)
    have hnoRed : ∀ a ∈ U, ∀ b ∈ Finset.univ \ (U ∪ nbr R U), ¬ R.Adj a b := by
      intro a ha b hb hab
      exact (Finset.mem_sdiff.mp hb).2
        (Finset.mem_union_right _ (by rw [mem_nbr]; exact ⟨a, ha, hab⟩))
    have hcover : ∀ a b, F.Adj a b → R.Adj a b ∨ (F \ R).Adj a b := by
      intro a b hab
      by_cases h : R.Adj a b
      · exact Or.inl h
      · exact Or.inr ((SimpleGraph.sdiff_adj F R a b).mpr ⟨hab, h⟩)
    have hUunion : (U ∪ nbr R U).card ≤ (d + 3) * ((4 * d + 13) * n + 2 * n) := by
      have heq : U ∪ nbr R U = U ∪ (nbr R U \ U) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_sdiff]
        tauto
      rw [heq]
      have hdisj : Disjoint U (nbr R U \ U) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [Finset.mem_sdiff] at hx'
        exact hx'.2 hx
      rw [Finset.card_union_of_disjoint hdisj]
      calc U.card + (nbr R U \ U).card ≤ U.card + (d + 2) * U.card :=
            Nat.add_le_add_left hUnbr _
        _ = (d + 3) * U.card := by ring
        _ ≤ (d + 3) * ((4 * d + 13) * n + 2 * n) := Nat.mul_le_mul_left _ (by omega)
    have hNdecomp : N =
        (d + 3) * ((4 * d + 13) * n + 2 * n) + (4 * d + 13) * n + 4 * (d + 3) * n := by
      rw [hN]
      have h1 : (4 * d + 13) * n + 2 * n = (4 * d + 15) * n := by ring
      rw [h1]
      ring
    have hWcard : (4 * d + 13) * n + 4 * (d + 3) * n ≤ (Finset.univ \ (U ∪ nbr R U)).card := by
      have hcardeq : (Finset.univ \ (U ∪ nbr R U)).card = N - (U ∪ nbr R U).card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      omega
    have hM1 : 2 * n ≤ (4 * d + 13) * n := Nat.mul_le_mul_right n (by omega)
    have hM2 : 4 * (d + 3) * n + n ≤ (4 * d + 13) * n := by
      have h1 : 4 * (d + 3) * n + n = (4 * d + 13) * n := by ring
      omega
    obtain ⟨V₁, hV₁ne, -, hV₁exp⟩ :=
      blue_dichotomy (M := (4 * d + 13) * n) U (Finset.univ \ (U ∪ nbr R U))
        hUW' hnoRed hcover hhole hn hM1 hM2 hUcard hWcard
    obtain ⟨v, hv⟩ := hV₁ne
    exact isContained_of_induce (W := V₁) (G := F \ R)
      (isContained_of_expander hV₁exp hn ⟨⟨v, hv⟩⟩ hT hdeg hcard)

end Final

end OMA

/-- **Erdős 559, tree variant** (Friedman–Pippenger): for a tree `G` with `n` vertices and
maximum degree at most `d`, the size Ramsey number `sizeRamsey G G` is at most `C * n` with `C`
depending on `d` only. -/
theorem OMA.solution : type_of% @Erdos559.erdos_559.variants.trees := by
  intro d
  classical
  let c₁ : ℕ := (d + 3) * (4 * d + 15) + (4 * d + 13) + 4 * (d + 3)
  let r : ℕ := (c₁ - 1) * (2 * c₁ + 1)
  refine ⟨((r * c₁ : ℕ) : ℝ), ?_⟩
  intro V _ G hT hdeg
  haveI := hT.connected.nonempty
  have hn1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  have hc : 2 ≤ c₁ := by
    have h1 : c₁ = (d + 3) * (4 * d + 15) + (4 * d + 13) + 4 * (d + 3) := rfl
    rw [h1]
    have h2 : 2 ≤ 4 * d + 13 := by omega
    have h3 : (4 * d + 13 : ℕ) ≤ (d + 3) * (4 * d + 15) + (4 * d + 13) := Nat.le_add_left _ _
    have h4 : (d + 3) * (4 * d + 15) + (4 * d + 13) ≤
        (d + 3) * (4 * d + 15) + (4 * d + 13) + 4 * (d + 3) := Nat.le_add_right _ _
    omega
  have hr : r = (c₁ - 1) * (2 * c₁ + 1) := rfl
  have hsub : (c₁ * Fintype.card V) - Fintype.card V = (c₁ - 1) * Fintype.card V := by
    rw [Nat.sub_mul, Nat.one_mul]
  have hmain : 4 ^ (c₁ * Fintype.card V) *
      (((c₁ * Fintype.card V) - Fintype.card V) ^ Fintype.card V *
        (c₁ * Fintype.card V) ^ ((c₁ * Fintype.card V) - Fintype.card V)) ^ r
      < (c₁ * Fintype.card V) ^ (r * (c₁ * Fintype.card V)) := by
    rw [hsub, mul_pow, ← pow_mul, ← pow_mul]
    have hreal := OMA.pow_arith c₁ (Fintype.card V) r hc hn1 hr
    have hcast : ((4 ^ (c₁ * Fintype.card V) *
        (((c₁ - 1) * Fintype.card V) ^ (Fintype.card V * r) *
          (c₁ * Fintype.card V) ^ (((c₁ - 1) * Fintype.card V) * r)) : ℕ) : ℝ)
        < (((c₁ * Fintype.card V) ^ (r * (c₁ * Fintype.card V)) : ℕ) : ℝ) := by
      push_cast
      rw [← mul_assoc]
      exact hreal
    exact Nat.cast_lt.mp hcast
  obtain ⟨f, hhole⟩ := OMA.exists_holeFree (N := c₁ * Fintype.card V) (r := r) hn1 (by
    have h1 : (0 : ℕ) < c₁ := by omega
    have h2 : Fintype.card V < c₁ * Fintype.card V := by
      calc Fintype.card V = 1 * Fintype.card V := by rw [Nat.one_mul]
        _ < c₁ * Fintype.card V := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    exact h2) hmain
  have hdeg' : ∀ v : V, (Finset.univ.filter (fun b => G.Adj v b)).card ≤ d := by
    intro v
    have h3 : G.degree v = (Finset.univ.filter (fun b => G.Adj v b)).card := by
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    rw [← h3]
    exact (G.degree_le_maxDegree v).trans hdeg
  have hNdef : c₁ * Fintype.card V =
      ((d + 3) * (4 * d + 15) + (4 * d + 13) + 4 * (d + 3)) * Fintype.card V := rfl
  have hsize : sizeRamsey G G ≤ (OMA.funGraph f).edgeSet.ncard := by
    refine Nat.sInf_le ⟨c₁ * Fintype.card V, OMA.funGraph f, rfl, fun R _ => ?_⟩
    exact OMA.colour_copy G (OMA.funGraph f) R hhole hn1 hT hdeg' (le_of_eq rfl) hNdef
  have hedge : (OMA.funGraph f).edgeSet.ncard ≤ r * (c₁ * Fintype.card V) :=
    OMA.funGraph_edgeSet_ncard_le f
  calc (sizeRamsey G G : ℝ) ≤ ((OMA.funGraph f).edgeSet.ncard : ℝ) := by exact_mod_cast hsize
    _ ≤ ((r * (c₁ * Fintype.card V) : ℕ) : ℝ) := by exact_mod_cast hedge
    _ = ((r * c₁ : ℕ) : ℝ) * (Fintype.card V : ℝ) := by push_cast; ring
