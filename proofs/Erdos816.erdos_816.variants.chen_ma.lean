import FormalConjectures.ErdosProblems.«816»
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Chen-Ma Strengthening of Erdos Problem 816

Formal proof that for every `n ≥ 600`, any graph on `2n + 1` vertices with at least `n^2 + n`
edges that is not isomorphic to `K_{n, n+1}` contains two distinct equal-degree vertices joined
by a simple path of length `3`.
-/

namespace OMA816

open Finset SimpleGraph
open scoped BigOperators

def JoinedByPathThree {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ x y, u ≠ x ∧ u ≠ y ∧ u ≠ v ∧ x ≠ y ∧ x ≠ v ∧ y ≠ v ∧
    G.Adj u x ∧ G.Adj x y ∧ G.Adj y v

lemma joinedByPathThree_of_adj {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hux : G.Adj u x) (hxy : G.Adj x y) (hyv : G.Adj y v)
    (hux' : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) (hxy' : x ≠ y)
    (hxv : x ≠ v) (hyv' : y ≠ v) : JoinedByPathThree G u v :=
  ⟨x, y, hux', huy, huv, hxy', hxv, hyv', hux, hxy, hyv⟩

open scoped Classical in
lemma hasEqualDegreePathThree_of_joined {V : Type*} [Fintype V]
    (G : SimpleGraph V) {u v : V}
    (hdeg : G.degree u = G.degree v)
    (hp : JoinedByPathThree G u v) : Erdos816.HasEqualDegreePathThree G := by
  rcases hp with ⟨x, y, hux, huy, huv, hxy, hxv, hyv, h1, h2, h3⟩
  refine ⟨u, v, huv, hdeg,
    Walk.cons h1 (Walk.cons h2 (Walk.cons h3 Walk.nil)), ?_, rfl⟩
  rw [Walk.isPath_def]
  simp [hux, huy, huv, hxy, hxv, hyv]

lemma sum_le_card_mul {α : Type*}
    (s : Finset α) (f : α → ℕ) (m : ℕ)
    (hbound : ∀ x ∈ s, f x ≤ m) : ∑ x ∈ s, f x ≤ s.card * m := by
  calc
    ∑ x ∈ s, f x ≤ ∑ _x ∈ s, m := Finset.sum_le_sum fun x hx ↦ hbound x hx
    _ = s.card * m := by simp

lemma eq_of_sum_ge_card_mul {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (m : ℕ)
    (hle : ∀ x ∈ s, f x ≤ m)
    (hsum : s.card * m ≤ ∑ x ∈ s, f x) :
    ∀ x ∈ s, f x = m := by
  intro x hx
  by_contra hne
  have hlt : f x < m := Nat.lt_of_le_of_ne (hle x hx) hne
  have hrest : ∑ y ∈ s.erase x, f y ≤ (s.erase x).card * m :=
    sum_le_card_mul (s.erase x) f m fun y hy ↦ hle y (Finset.mem_of_mem_erase hy)
  have hsplit := Finset.sum_erase_add s f hx
  have hcard := Finset.card_erase_add_one hx
  nlinarith only [hsum, hlt, hrest, hsplit, hcard]

lemma card_filter_eq_ge_of_sum_ge {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hle : ∀ x ∈ s, f x ≤ m)
    (hsum : s.card * m ≤ (∑ x ∈ s, f x) + 1) :
    s.card - 1 ≤ (s.filter fun x ↦ f x = m).card := by
  let good := s.filter fun x ↦ f x = m
  let bad := s.filter fun x ↦ f x ≠ m
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro x hxg hxb
    exact (Finset.mem_filter.mp hxb).2 (Finset.mem_filter.mp hxg).2
  have hunion : good ∪ bad = s := by
    ext x
    simp only [good, bad, Finset.mem_union, Finset.mem_filter]
    by_cases hx : x ∈ s <;> by_cases hfx : f x = m <;> simp [hx, hfx]
  have hcard : good.card + bad.card = s.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hgood : ∑ x ∈ good, f x ≤ good.card * m :=
    sum_le_card_mul good f m fun x hx ↦ hle x (Finset.mem_filter.mp hx).1
  have hbad_le : ∀ x ∈ bad, f x ≤ m - 1 := by
    intro x hx
    have hxs := (Finset.mem_filter.mp hx).1
    have hne := (Finset.mem_filter.mp hx).2
    have h1 := hle x hxs
    omega
  have hbad : ∑ x ∈ bad, f x ≤ bad.card * (m - 1) :=
    sum_le_card_mul bad f (m - 1) hbad_le
  have hsplit : ∑ x ∈ s, f x = (∑ x ∈ good, f x) + ∑ x ∈ bad, f x := by
    rw [← hunion, Finset.sum_union hdisj]
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hbad_card : bad.card ≤ 1 := by
    nlinarith only [hcard, hgood, hbad, hsplit, hsum, hm1]
  change s.card - 1 ≤ good.card
  omega

private lemma choose_card_le_sum (s : Finset ℕ) : s.card.choose 2 ≤ ∑ x ∈ s, x := by
  rw [← Finset.card_product_filter_lt]
  calc
    #{p ∈ s ×ˢ s | p.1 < p.2} = ∑ x ∈ s, #{y ∈ s | y < x} := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      exact Finset.sum_comm
    _ ≤ ∑ x ∈ s, x := by
      gcongr with x _
      calc
        #{y ∈ s | y < x} ≤ (Finset.range x).card := Finset.card_le_card (by
          intro y hy
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hy).2)
        _ = x := Finset.card_range x

private lemma sum_injective_nat_defect {A : Type*}
    (s : Finset A) (f : A → ℕ) (m : ℕ)
    (hinj : Set.InjOn f s) (hle : ∀ x ∈ s, f x ≤ m) :
    2 * (∑ x ∈ s, f x) + s.card * (s.card - 1) ≤ 2 * s.card * m := by
  classical
  let g : A → ℕ := fun x ↦ m - f x
  have hginj : Set.InjOn g s := by
    intro x hx y hy hxy
    apply hinj hx hy
    exact (tsub_right_inj (hle x hx) (hle y hy)).mp hxy
  have hcard : (s.image g).card = s.card := Finset.card_image_of_injOn hginj
  have hsum : ∑ y ∈ s.image g, y = ∑ x ∈ s, (m - f x) := by
    rw [Finset.sum_image hginj]
  have hchoose := choose_card_le_sum (s.image g)
  rw [hsum, Finset.sum_tsub_distrib s hle] at hchoose
  rw [Finset.sum_const_nat (m := m) (fun _ _ ↦ rfl)] at hchoose
  rw [hcard, Nat.choose_two_right] at hchoose
  have htwice := Nat.mul_le_mul_left 2 hchoose
  rw [mul_comm 2, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self s.card)] at htwice
  have hsumle := sum_le_card_mul s f m hle
  calc
    2 * (∑ x ∈ s, f x) + s.card * (s.card - 1) ≤
        2 * (∑ x ∈ s, f x) + 2 * (s.card * m - ∑ x ∈ s, f x) :=
      Nat.add_le_add_left htwice _
    _ = 2 * ((∑ x ∈ s, f x) + (s.card * m - ∑ x ∈ s, f x)) := by
      rw [Nat.mul_add]
    _ = 2 * (s.card * m) := by rw [Nat.add_sub_of_le hsumle]
    _ = 2 * s.card * m := by rw [Nat.mul_assoc]

section PairPartition

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)

def common : Finset V := G.neighborFinset u ∩ G.neighborFinset v
def leftOnly : Finset V := (G.neighborFinset u \ G.neighborFinset v).erase v
def rightOnly : Finset V := (G.neighborFinset v \ G.neighborFinset u).erase u
def neither : Finset V :=
  univ.filter fun w ↦ w ≠ u ∧ w ≠ v ∧ ¬G.Adj u w ∧ ¬G.Adj v w

@[simp] lemma mem_common {w : V} : w ∈ common G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [common, G.mem_neighborFinset]

@[simp] lemma mem_leftOnly {w : V} :
    w ∈ leftOnly G u v ↔ G.Adj u w ∧ ¬G.Adj v w ∧ w ≠ v := by
  simp [leftOnly, G.mem_neighborFinset, and_left_comm, and_comm]

@[simp] lemma mem_rightOnly {w : V} :
    w ∈ rightOnly G u v ↔ G.Adj v w ∧ ¬G.Adj u w ∧ w ≠ u := by
  simp [rightOnly, G.mem_neighborFinset, and_assoc, and_comm]

@[simp] lemma mem_neither {w : V} :
    w ∈ neither G u v ↔ w ≠ u ∧ w ≠ v ∧ ¬G.Adj u w ∧ ¬G.Adj v w := by
  simp [neither]

lemma pairwise_disjoint_parts :
    Disjoint (common G u v) (leftOnly G u v) ∧
    Disjoint (common G u v) (rightOnly G u v) ∧
    Disjoint (common G u v) (neither G u v) ∧
    Disjoint (leftOnly G u v) (rightOnly G u v) ∧
    Disjoint (leftOnly G u v) (neither G u v) ∧
    Disjoint (rightOnly G u v) (neither G u v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Finset.disjoint_left] <;> intro w hw1 hw2
  · exact (mem_leftOnly G u v).mp hw2 |>.2.1 ((mem_common G u v).mp hw1).2
  · exact (mem_rightOnly G u v).mp hw2 |>.2.1 ((mem_common G u v).mp hw1).1
  · exact (mem_neither G u v).mp hw2 |>.2.2.1 ((mem_common G u v).mp hw1).1
  · exact (mem_leftOnly G u v).mp hw1 |>.2.1 ((mem_rightOnly G u v).mp hw2).1
  · exact (mem_neither G u v).mp hw2 |>.2.2.1 ((mem_leftOnly G u v).mp hw1).1
  · exact (mem_neither G u v).mp hw2 |>.2.2.2 ((mem_rightOnly G u v).mp hw1).1

lemma parts_union :
    {u, v} ∪ (common G u v ∪ (leftOnly G u v ∪
      (rightOnly G u v ∪ neither G u v))) = univ := by
  ext w
  simp only [mem_union, mem_insert, mem_singleton, mem_common, mem_leftOnly,
    mem_rightOnly, mem_neither, mem_univ, iff_true]
  by_cases hwu : w = u
  · exact Or.inl (Or.inl hwu)
  by_cases hwv : w = v
  · exact Or.inl (Or.inr hwv)
  by_cases huw : G.Adj u w
  · by_cases hvw : G.Adj v w
    · exact Or.inr (Or.inl ⟨huw, hvw⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨huw, hvw, hwv⟩))
  · by_cases hvw : G.Adj v w
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hvw, huw, hwu⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hwu, hwv, huw, hvw⟩)))

lemma card_parts (huv : u ≠ v) :
    Fintype.card V = 2 + (common G u v).card + (leftOnly G u v).card +
      (rightOnly G u v).card + (neither G u v).card := by
  have hp := pairwise_disjoint_parts G u v
  have hu : ({u, v} : Finset V).card = 2 := by simp [huv]
  have huC : Disjoint ({u, v} : Finset V) (common G u v) := by simp [Finset.disjoint_left]
  have huL : Disjoint ({u, v} : Finset V) (leftOnly G u v) := by simp [Finset.disjoint_left]
  have huR : Disjoint ({u, v} : Finset V) (rightOnly G u v) := by simp [Finset.disjoint_left]
  have huD : Disjoint ({u, v} : Finset V) (neither G u v) := by simp [Finset.disjoint_left]
  have hRD : Disjoint (rightOnly G u v) (neither G u v) := hp.2.2.2.2.2
  have hLRD : Disjoint (leftOnly G u v) (rightOnly G u v ∪ neither G u v) :=
    disjoint_sup_right.mpr ⟨hp.2.2.2.1, hp.2.2.2.2.1⟩
  have hCLRD : Disjoint (common G u v)
      (leftOnly G u v ∪ (rightOnly G u v ∪ neither G u v)) :=
    disjoint_sup_right.mpr ⟨hp.1, disjoint_sup_right.mpr ⟨hp.2.1, hp.2.2.1⟩⟩
  have huRest : Disjoint ({u, v} : Finset V)
      (common G u v ∪ (leftOnly G u v ∪ (rightOnly G u v ∪ neither G u v))) :=
    disjoint_sup_right.mpr ⟨huC,
      disjoint_sup_right.mpr ⟨huL, disjoint_sup_right.mpr ⟨huR, huD⟩⟩⟩
  rw [← card_univ, ← parts_union G u v]
  rw [card_union_of_disjoint huRest, card_union_of_disjoint hCLRD,
    card_union_of_disjoint hLRD, card_union_of_disjoint hRD]
  simp [hu]
  omega

lemma sum_parts (huv : u ≠ v) (f : V → ℕ) :
    ∑ w, f w = f u + f v + (∑ w ∈ common G u v, f w) +
      (∑ w ∈ leftOnly G u v, f w) + (∑ w ∈ rightOnly G u v, f w) +
      ∑ w ∈ neither G u v, f w := by
  have hp := pairwise_disjoint_parts G u v
  have huC : Disjoint ({u, v} : Finset V) (common G u v) := by simp [Finset.disjoint_left]
  have huL : Disjoint ({u, v} : Finset V) (leftOnly G u v) := by simp [Finset.disjoint_left]
  have huR : Disjoint ({u, v} : Finset V) (rightOnly G u v) := by simp [Finset.disjoint_left]
  have huD : Disjoint ({u, v} : Finset V) (neither G u v) := by simp [Finset.disjoint_left]
  have hRD : Disjoint (rightOnly G u v) (neither G u v) := hp.2.2.2.2.2
  have hLRD : Disjoint (leftOnly G u v) (rightOnly G u v ∪ neither G u v) :=
    disjoint_sup_right.mpr ⟨hp.2.2.2.1, hp.2.2.2.2.1⟩
  have hCLRD : Disjoint (common G u v)
      (leftOnly G u v ∪ (rightOnly G u v ∪ neither G u v)) :=
    disjoint_sup_right.mpr ⟨hp.1, disjoint_sup_right.mpr ⟨hp.2.1, hp.2.2.1⟩⟩
  have huRest : Disjoint ({u, v} : Finset V)
      (common G u v ∪ (leftOnly G u v ∪ (rightOnly G u v ∪ neither G u v))) :=
    disjoint_sup_right.mpr ⟨huC,
      disjoint_sup_right.mpr ⟨huL, disjoint_sup_right.mpr ⟨huR, huD⟩⟩⟩
  change (∑ w ∈ (univ : Finset V), f w) = _
  rw [← parts_union G u v, Finset.sum_union huRest, Finset.sum_union hCLRD,
    Finset.sum_union hLRD, Finset.sum_union hRD]
  simp [huv]
  omega

lemma degree_eq_card_common_add_leftOnly (huv : u ≠ v) :
    G.degree u = (common G u v).card + (leftOnly G u v).card +
      if G.Adj u v then 1 else 0 := by
  rw [← G.card_neighborFinset_eq_degree]
  by_cases huvA : G.Adj u v
  · have hdecomp : G.neighborFinset u = common G u v ∪ leftOnly G u v ∪ {v} := by
      ext w
      simp only [G.mem_neighborFinset, mem_union, mem_common, mem_leftOnly, mem_singleton]
      constructor
      · intro huw
        by_cases hvw : G.Adj v w
        · exact Or.inl (Or.inl ⟨huw, hvw⟩)
        · by_cases hwv : w = v
          · exact Or.inr hwv
          · exact Or.inl (Or.inr ⟨huw, hvw, hwv⟩)
      · intro hw
        rcases hw with (⟨huw, -⟩ | ⟨huw, -, -⟩) | rfl
        · exact huw
        · exact huw
        · exact huvA
    have hCL := (pairwise_disjoint_parts G u v).1
    have hCv : Disjoint (common G u v) {v} := by
      rw [Finset.disjoint_singleton_right]
      intro hv
      exact G.loopless.irrefl v ((mem_common G u v).mp hv).2
    have hLv : Disjoint (leftOnly G u v) {v} := by simp [Finset.disjoint_left]
    have hCLv : Disjoint (common G u v ∪ leftOnly G u v) {v} :=
      disjoint_sup_left.mpr ⟨hCv, hLv⟩
    rw [hdecomp, card_union_of_disjoint hCLv, card_union_of_disjoint hCL]
    simp [huvA]
  · have hdecomp : G.neighborFinset u = common G u v ∪ leftOnly G u v := by
      ext w
      simp only [G.mem_neighborFinset, mem_union, mem_common, mem_leftOnly]
      constructor
      · intro huw
        by_cases hvw : G.Adj v w
        · exact Or.inl ⟨huw, hvw⟩
        · refine Or.inr ⟨huw, hvw, ?_⟩
          rintro rfl
          exact huvA huw
      · rintro (⟨huw, -⟩ | ⟨huw, -, -⟩) <;> exact huw
    rw [hdecomp, card_union_of_disjoint (pairwise_disjoint_parts G u v).1]
    simp [huvA]

lemma degree_eq_card_common_add_rightOnly (huv : u ≠ v) :
    G.degree v = (common G u v).card + (rightOnly G u v).card +
      if G.Adj u v then 1 else 0 := by
  simpa [common, leftOnly, rightOnly, G.adj_comm, inter_comm] using
    degree_eq_card_common_add_leftOnly G v u huv.symm

lemma card_leftOnly_eq_card_rightOnly (huv : u ≠ v) (hdeg : G.degree u = G.degree v) :
    (leftOnly G u v).card = (rightOnly G u v).card := by
  rw [degree_eq_card_common_add_leftOnly G u v huv,
    degree_eq_card_common_add_rightOnly G u v huv] at hdeg
  omega

lemma neighborFinset_subset_of_mem_common
    (huv : u ≠ v) (hnopath : ¬ JoinedByPathThree G u v)
    {x : V} (hx : x ∈ common G u v) :
    G.neighborFinset x ⊆ {u, v} ∪ neither G u v := by
  have hxA := (mem_common G u v).mp hx
  intro z hz
  have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
  simp only [mem_union, mem_insert, mem_singleton]
  by_cases hzu : z = u
  · exact Or.inl (Or.inl hzu)
  by_cases hzv : z = v
  · exact Or.inl (Or.inr hzv)
  refine Or.inr ?_
  have hnuz : ¬ G.Adj u z := fun huz ↦ hnopath
    (joinedByPathThree_of_adj huz hxz.symm hxA.2.symm huz.ne hxA.1.ne huv hxz.symm.ne hzv hxA.2.ne.symm)
  have hnvz : ¬ G.Adj v z := fun hvz ↦ hnopath
    (joinedByPathThree_of_adj hxA.1 hxz hvz.symm hxA.1.ne (Ne.symm hzu) huv hxz.ne hxA.2.ne.symm hvz.ne.symm)
  exact (mem_neither G u v).mpr ⟨hzu, hzv, hnuz, hnvz⟩

lemma degree_le_of_mem_common
    (huv : u ≠ v) (hnopath : ¬ JoinedByPathThree G u v)
    {x : V} (hx : x ∈ common G u v) :
    G.degree x ≤ 2 + (neither G u v).card := by
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset x).card ≤ ({u, v} ∪ neither G u v).card :=
      Finset.card_le_card (neighborFinset_subset_of_mem_common G u v huv hnopath hx)
    _ ≤ ({u, v} : Finset V).card + (neither G u v).card :=
      Finset.card_union_le _ _
    _ = 2 + (neither G u v).card := by simp [huv]

lemma degree_le_of_mem_leftOnly
    (huv : u ≠ v) (hnopath : ¬ JoinedByPathThree G u v)
    {x : V} (hx : x ∈ leftOnly G u v) :
    G.degree x ≤ (leftOnly G u v).card + (neither G u v).card := by
  have hxA := (mem_leftOnly G u v).mp hx
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset x).card ≤ ({u} ∪ ((leftOnly G u v).erase x ∪ neither G u v)).card := by
      apply Finset.card_le_card
      intro z hz
      have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
      simp only [mem_union, mem_singleton, mem_erase]
      by_cases hzu : z = u
      · exact Or.inl hzu
      refine Or.inr ?_
      have hnvz : ¬ G.Adj v z := fun hvz ↦ hnopath
        (joinedByPathThree_of_adj hxA.1 hxz hvz.symm hxA.1.ne (Ne.symm hzu) huv hxz.ne hxA.2.2 hvz.ne.symm)
      have hzv : z ≠ v := by
        rintro rfl
        exact hxA.2.1 hxz.symm
      by_cases huz : G.Adj u z
      · exact Or.inl ⟨hxz.ne.symm, (mem_leftOnly G u v).mpr ⟨huz, hnvz, hzv⟩⟩
      · exact Or.inr ((mem_neither G u v).mpr ⟨hzu, hzv, huz, hnvz⟩)
    _ ≤ 1 + ((leftOnly G u v).erase x).card + (neither G u v).card := by
      have h1 := Finset.card_union_le ({u} : Finset V) ((leftOnly G u v).erase x ∪ neither G u v)
      have h2 := Finset.card_union_le ((leftOnly G u v).erase x) (neither G u v)
      simp only [card_singleton] at h1
      omega
    _ = (leftOnly G u v).card + (neither G u v).card := by
      rw [Finset.card_erase_of_mem hx]
      have hxpos : 0 < (leftOnly G u v).card := Finset.card_pos.mpr ⟨x, hx⟩
      omega

lemma degree_le_of_mem_rightOnly
    (huv : u ≠ v) (hnopath : ¬ JoinedByPathThree G u v)
    {x : V} (hx : x ∈ rightOnly G u v) :
    G.degree x ≤ (rightOnly G u v).card + (neither G u v).card := by
  have hnopath' : ¬ JoinedByPathThree G v u := fun hp ↦ by
    rcases hp with ⟨a, b, hva, hvb, hvu, hab, hau, hbu, h1, h2, h3⟩
    exact hnopath ⟨b, a, hbu.symm, hau.symm, hvu.symm, hab.symm, hvb.symm, hva.symm,
      h3.symm, h2.symm, h1.symm⟩
  have hx' : x ∈ leftOnly G v u := by
    simpa [leftOnly, rightOnly] using hx
  have h := degree_le_of_mem_leftOnly G v u huv.symm hnopath' hx'
  have hle : leftOnly G v u = rightOnly G u v := rfl
  have hne : neither G v u = neither G u v := by
    ext w
    simp [neither, and_left_comm, and_comm]
  simpa [hle, hne] using h

lemma degree_le_of_mem_neither (huv : u ≠ v) {x : V} (hx : x ∈ neither G u v) :
    G.degree x ≤ Fintype.card V - 3 := by
  have hxN := (mem_neither G u v).mp hx
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset x).card ≤ ((univ : Finset V) \ {u, v, x}).card := by
      apply Finset.card_le_card
      intro z hz
      have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
      simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or]
      exact ⟨fun hzu ↦ hxN.2.2.1 (hzu ▸ hxz.symm),
        fun hzv ↦ hxN.2.2.2 (hzv ▸ hxz.symm), hxz.ne.symm⟩
    _ = Fintype.card V - 3 := by
      rw [Finset.card_sdiff]
      simp [huv, hxN.1.symm, hxN.2.1.symm]

end PairPartition

lemma iso_completeBipartite_of_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (A B : Finset V)
    (hdisj : Disjoint A B)
    (hunion : A ∪ B = univ)
    (hAcard : A.card = n)
    (hBcard : B.card = n + 1)
    (hBnbhd : ∀ x ∈ B, G.neighborFinset x = A)
    (hAdeg : ∀ y ∈ A, G.degree y ≤ n + 1) :
    Nonempty (G ≃g completeBipartiteGraph (Fin n) (Fin (n + 1))) := by
  have hAnbhd : ∀ y ∈ A, G.neighborFinset y = B := by
    intro y hy
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro x hxB
      have hyx : y ∈ G.neighborFinset x := by rw [hBnbhd x hxB]; exact hy
      exact (G.mem_neighborFinset y x).mpr ((G.mem_neighborFinset x y).mp hyx).symm
    · rw [G.card_neighborFinset_eq_degree, hBcard]
      exact hAdeg y hy
  have hmemB : ∀ w : V, w ∉ A → w ∈ B := by
    intro w hwA
    have hw : w ∈ A ∪ B := hunion ▸ Finset.mem_univ w
    exact (Finset.mem_union.mp hw).resolve_left hwA
  have hnotA : ∀ w : V, w ∈ B → w ∉ A :=
    fun w hwB hwA ↦ Finset.disjoint_left.mp hdisj hwA hwB
  let eA : {w : V // w ∈ A} ≃ Fin n :=
    Fintype.equivOfCardEq (by simp [Fintype.card_coe, hAcard])
  let eB : {w : V // w ∈ B} ≃ Fin (n + 1) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_coe, hBcard])
  let toF : V → Fin n ⊕ Fin (n + 1) :=
    fun w ↦ if hw : w ∈ A then Sum.inl (eA ⟨w, hw⟩) else Sum.inr (eB ⟨w, hmemB w hw⟩)
  let invF : Fin n ⊕ Fin (n + 1) → V :=
    Sum.elim (fun i ↦ (eA.symm i).1) (fun j ↦ (eB.symm j).1)
  refine ⟨{
    toFun := toF
    invFun := invF
    left_inv := fun w ↦ by
      dsimp [toF, invF]
      split_ifs with hw
      · simp
      · simp
    right_inv := fun s ↦ by
      rcases s with i | j
      · dsimp [toF, invF]
        rw [dif_pos (eA.symm i).2]
        simp
      · dsimp [toF, invF]
        rw [dif_neg (hnotA _ (eB.symm j).2)]
        simp
    map_rel_iff' := by
      intro w1 w2
      dsimp [toF]
      split_ifs with hw1 hw2 hw2
      · refine ⟨by simp, fun hadj ↦ ?_⟩
        have hw2B : w2 ∈ B := hAnbhd w1 hw1 ▸ (G.mem_neighborFinset w1 w2).mpr hadj
        exact False.elim (hnotA w2 hw2B hw2)
      · refine ⟨fun _ ↦ ?_, fun _ ↦ by simp⟩
        have hw2B : w2 ∈ G.neighborFinset w1 := hAnbhd w1 hw1 ▸ hmemB w2 hw2
        exact (G.mem_neighborFinset w1 w2).mp hw2B
      · refine ⟨fun _ ↦ ?_, fun _ ↦ by simp⟩
        have hw2A : w2 ∈ G.neighborFinset w1 := hBnbhd w1 (hmemB w1 hw1) ▸ hw2
        exact (G.mem_neighborFinset w1 w2).mp hw2A
      · refine ⟨by simp, fun hadj ↦ ?_⟩
        have hw2A : w2 ∈ A := hBnbhd w1 (hmemB w1 hw1) ▸ (G.mem_neighborFinset w1 w2).mpr hadj
        exact False.elim (hw2 hw2A)
  }⟩

lemma sum_le_baseline_add_all_excesses
    {α : Type*}
    (s : Finset α) (f : α → ℕ) (γ d : ℕ)
    (hbound : ∀ x ∈ s, f x ≤ d)
    (hinj : Set.InjOn f {x | x ∈ s ∧ γ < f x}) :
    (∑ x ∈ s, f x) ≤
      γ * s.card + ∑ k ∈ Finset.Ioc γ d, (k - γ) := by
  classical
  let high : Finset α := s.filter fun x ↦ γ < f x
  have hsplit : (∑ x ∈ s, (f x - γ)) = ∑ x ∈ high, (f x - γ) := by
    symm
    apply Finset.sum_subset
    · intro x hx
      exact (Finset.mem_filter.mp hx).1
    · intro x hxS hxNot
      have hle : f x ≤ γ := by
        simp only [high, Finset.mem_filter, not_and] at hxNot
        exact Nat.le_of_not_gt (hxNot hxS)
      simp [Nat.sub_eq_zero_of_le hle]
  have hhighInj : Set.InjOn f (↑high : Set α) := by
    intro x hx y hy hxy
    apply hinj
    · simpa only [high, Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq] using hx
    · simpa only [high, Finset.mem_coe, Finset.mem_filter, Set.mem_ofPred_eq] using hy
    · exact hxy
  have himage : high.image f ⊆ Finset.Ioc γ d := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_filter.mp hx).2,
      hbound x (Finset.mem_filter.mp hx).1⟩
  have hexcess :
      (∑ x ∈ high, (f x - γ)) ≤ ∑ k ∈ Finset.Ioc γ d, (k - γ) := by
    calc
      (∑ x ∈ high, (f x - γ)) = ∑ k ∈ high.image f, (k - γ) := by
        rw [Finset.sum_image hhighInj]
      _ ≤ ∑ k ∈ Finset.Ioc γ d, (k - γ) :=
        Finset.sum_le_sum_of_subset himage
  calc
    ∑ x ∈ s, f x ≤ ∑ x ∈ s, (γ + (f x - γ)) :=
      Finset.sum_le_sum fun x _ ↦ by omega
    _ = γ * s.card + ∑ x ∈ s, (f x - γ) := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ ≤ γ * s.card + ∑ k ∈ Finset.Ioc γ d, (k - γ) := by
      rw [hsplit]
      exact Nat.add_le_add_left hexcess _

lemma degree_ne_of_two_common_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hno : ∀ {u w : V}, u ≠ w → G.degree u = G.degree w →
      ¬ JoinedByPathThree G u w)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : u ≠ w)
    (hcommon : 2 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card) :
    G.degree u ≠ G.degree w := by
  intro hdeg
  apply hno huw hdeg
  have hnot : ¬ (G.neighborFinset u ∩ G.neighborFinset v) ⊆ {w} := by
    intro hsub
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨x, hxC, hxw⟩ := Finset.not_subset.mp hnot
  have hxw' : x ≠ w := by simpa only [Finset.mem_singleton] using hxw
  have hux : G.Adj u x := (G.mem_neighborFinset u x).mp (Finset.mem_inter.mp hxC).1
  have hvx : G.Adj v x := (G.mem_neighborFinset v x).mp (Finset.mem_inter.mp hxC).2
  exact joinedByPathThree_of_adj hux hvx.symm hvw
    hux.ne hvu.ne.symm huw hvx.ne.symm hxw' hvw.ne

lemma sum_Ioc_sub_eq_sum_range_succ (a r : ℕ) :
    (∑ k ∈ Finset.Ioc a (a + r), (k - a)) =
      ∑ i ∈ Finset.range r, (i + 1) := by
  have hIoc : Finset.Ioc a (a + r) =
      (Finset.range r).image (fun i ↦ a + i + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      refine ⟨k - a - 1, ?_, ?_⟩ <;> omega
    · rintro ⟨i, hi, rfl⟩
      omega
  have hinj : Set.InjOn (fun i ↦ a + i + 1) (↑(Finset.range r) : Set ℕ) := by
    intro i _ j _ hij
    exact Nat.add_left_cancel (Nat.add_right_cancel hij)
  rw [hIoc, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro i _
  omega

lemma twice_sum_range_succ (r : ℕ) :
    2 * (∑ i ∈ Finset.range r, (i + 1)) = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ]
      nlinarith

lemma repeated_max_degree_case
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n Δ : ℕ}
    (hn : 600 ≤ n)
    (hcard : Fintype.card V = 2 * n + 1)
    (hlower : 2 * (n ^ 2 + n) ≤ ∑ w, G.degree w)
    (hnoBip : ¬ Nonempty (G ≃g completeBipartiteGraph (Fin n) (Fin (n + 1))))
    (hno : ∀ {a b : V}, a ≠ b → G.degree a = G.degree b →
      ¬ JoinedByPathThree G a b)
    {u v : V} (huv : u ≠ v)
    (hdu : G.degree u = Δ) (hdv : G.degree v = Δ)
    (hmax : ∀ w : V, G.degree w ≤ Δ) : False := by
  have hlarge : n + 1 ≤ Δ := by
    by_contra hle
    have hall : ∀ w : V, G.degree w ≤ n := fun w ↦ (hmax w).trans (by omega)
    have hup : ∑ w, G.degree w ≤ (2 * n + 1) * n := by
      simpa [Finset.card_univ, hcard] using
        sum_le_card_mul (univ : Finset V) (fun w ↦ G.degree w) n (fun w _ ↦ hall w)
    nlinarith only [hlower, hup, hn]
  have huvdeg : G.degree u = G.degree v := hdu.trans hdv.symm
  have hnopath : ¬ JoinedByPathThree G u v := hno huv huvdeg
  let C := common G u v
  let L := leftOnly G u v
  let R := rightOnly G u v
  let D := neither G u v
  have hLR : L.card = R.card := card_leftOnly_eq_card_rightOnly G u v huv huvdeg
  have hparts : Fintype.card V = 2 + C.card + L.card + R.card + D.card :=
    card_parts G u v huv
  have hsize : 2 * n + 1 = 2 + C.card + 2 * L.card + D.card := by
    rw [hcard, hLR] at hparts; omega
  have hCbound : ∀ x ∈ C, G.degree x ≤ 2 + D.card :=
    fun x hx ↦ degree_le_of_mem_common G u v huv hnopath hx
  have hLbound : ∀ x ∈ L, G.degree x ≤ L.card + D.card :=
    fun x hx ↦ degree_le_of_mem_leftOnly G u v huv hnopath hx
  have hRbound : ∀ x ∈ R, G.degree x ≤ R.card + D.card :=
    fun x hx ↦ degree_le_of_mem_rightOnly G u v huv hnopath hx
  have hDbound : ∀ x ∈ D, G.degree x ≤ Δ := fun x _ ↦ hmax x
  have hDstruct : ∀ x ∈ D, G.degree x ≤ 2 * n - 2 := by
    intro x hx
    have h := degree_le_of_mem_neither G u v huv hx
    omega
  have hsumC : ∑ x ∈ C, G.degree x ≤ C.card * (2 + D.card) :=
    sum_le_card_mul C (fun x ↦ G.degree x) (2 + D.card) hCbound
  have hsumL : ∑ x ∈ L, G.degree x ≤ L.card * (L.card + D.card) :=
    sum_le_card_mul L (fun x ↦ G.degree x) (L.card + D.card) hLbound
  have hsumR : ∑ x ∈ R, G.degree x ≤ L.card * (L.card + D.card) := by
    rw [hLR]
    exact sum_le_card_mul R (fun x ↦ G.degree x) (R.card + D.card) hRbound
  have hsumD : ∑ x ∈ D, G.degree x ≤ D.card * Δ :=
    sum_le_card_mul D (fun x ↦ G.degree x) Δ hDbound
  have hsumDstruct : ∑ x ∈ D, G.degree x ≤ D.card * (2 * n - 2) :=
    sum_le_card_mul D (fun x ↦ G.degree x) (2 * n - 2) hDstruct
  have hsumParts :
      ∑ w, G.degree w = Δ + Δ + (∑ w ∈ C, G.degree w) +
        (∑ w ∈ L, G.degree w) + (∑ w ∈ R, G.degree w) +
        ∑ w ∈ D, G.degree w := by
    simpa [C, L, R, D, hdu, hdv] using sum_parts G u v huv (fun w ↦ G.degree w)
  rw [hsumParts] at hlower
  by_cases huvA : G.Adj u v
  · have hDelta : Δ = C.card + L.card + 1 := by
      rw [← hdu, degree_eq_card_common_add_leftOnly G u v huv, if_pos huvA]
    have hCinj : Set.InjOn (fun x ↦ G.degree x) (↑C : Set V) := by
      intro x hx y hy hdeg
      by_contra hxy
      have hxA := (mem_common G u v).mp hx
      have hyA := (mem_common G u v).mp hy
      exact hno hxy hdeg (joinedByPathThree_of_adj hxA.1.symm huvA hyA.2
        hxA.1.ne.symm hxA.2.ne.symm hxy huv hyA.1.ne hyA.2.ne)
    have hCsharp :
        2 * (∑ x ∈ C, G.degree x) + C.card * (C.card - 1) ≤
          2 * C.card * (2 + D.card) :=
      sum_injective_nat_defect C (fun x ↦ G.degree x) (2 + D.card) hCinj hCbound
    have hCpos : 1 ≤ C.card := by omega
    have hCsub : C.card - 1 + 1 = C.card := Nat.sub_add_cancel hCpos
    have hnsub : 2 * n - 2 + 2 = 2 * n := Nat.sub_add_cancel (by omega)
    by_cases hDcase : Δ ≤ 2 * n - 2
    · nlinarith only [hDelta, hsize, hlower, hCsharp, hsumL, hsumR,
        hsumD, hn, hlarge, hDcase, hCsub, hnsub]
    · have hDcase' : 2 * n - 2 ≤ Δ := by omega
      nlinarith only [hDelta, hsize, hlower, hCsharp, hsumL, hsumR,
        hsumDstruct, hn, hlarge, hDcase', hCsub, hnsub]
  · have hDelta : Δ = C.card + L.card := by
      rw [← hdu, degree_eq_card_common_add_leftOnly G u v huv, if_neg huvA, Nat.add_zero]
    have hDeltaEq : Δ = n + 1 := by
      by_contra hne
      have hge : n + 2 ≤ Δ := by omega
      nlinarith only [hDelta, hsize, hlower, hsumC, hsumL, hsumR, hsumD, hge]
    have hLzero : L.card = 0 := by
      by_contra hne
      have hge : 1 ≤ L.card := by omega
      nlinarith only [hDelta, hsize, hlower, hsumC, hsumL, hsumR, hsumD, hDeltaEq, hge]
    have hRzero : R.card = 0 := by omega
    have hCcard : C.card = n + 1 := by omega
    have hDcard : D.card = n - 2 := by omega
    have hLemp : leftOnly G u v = ∅ := Finset.card_eq_zero.mp hLzero
    have hRemp : rightOnly G u v = ∅ := Finset.card_eq_zero.mp hRzero
    have hsumL0 : ∑ w ∈ L, G.degree w = 0 := by simp [L, hLemp]
    have hsumR0 : ∑ w ∈ R, G.degree w = 0 := by simp [R, hRemp]
    have hCsumGe : C.card * (2 + D.card) ≤ ∑ x ∈ C, G.degree x := by
      have hnsub2 : n - 2 + 2 = n := Nat.sub_add_cancel (by omega)
      nlinarith only [hlower, hsumD, hDeltaEq, hCcard, hDcard, hsumL0, hsumR0, hnsub2]
    have hCdegEq : ∀ x ∈ C, G.degree x = 2 + D.card :=
      eq_of_sum_ge_card_mul C (fun x ↦ G.degree x) (2 + D.card) hCbound hCsumGe
    let A : Finset V := {u, v} ∪ D
    have huD : Disjoint ({u, v} : Finset V) D := by
      simp [D, Finset.disjoint_left]
    have hAcard : A.card = n := by
      rw [Finset.card_union_of_disjoint huD]
      simp [huv, hDcard]
      omega
    have hdisjAB : Disjoint A C := by
      refine disjoint_sup_left.mpr ⟨?_, (pairwise_disjoint_parts G u v).2.2.1.symm⟩
      simp [C, Finset.disjoint_left]
    have hunionAB : A ∪ C = univ := by
      have hp := parts_union G u v
      rw [hLemp, hRemp] at hp
      rw [Finset.eq_univ_iff_forall]
      intro w
      have hw : w ∈ {u, v} ∪ (common G u v ∪ (∅ ∪ (∅ ∪ neither G u v))) :=
        hp.symm ▸ Finset.mem_univ w
      simp only [mem_union, Finset.notMem_empty, false_or] at hw
      change w ∈ ({u, v} ∪ D) ∪ C
      simp only [mem_union]
      rcases hw with hwuv | (hwC | hwD)
      · exact Or.inl (Or.inl hwuv)
      · exact Or.inr hwC
      · exact Or.inl (Or.inr hwD)
    have hBnbhd : ∀ x ∈ C, G.neighborFinset x = A := by
      intro x hx
      apply Finset.eq_of_subset_of_card_le
      · exact neighborFinset_subset_of_mem_common G u v huv hnopath hx
      · rw [G.card_neighborFinset_eq_degree, hCdegEq x hx, hAcard, hDcard]
        omega
    have hAdeg : ∀ y ∈ A, G.degree y ≤ n + 1 := fun y _ ↦ hDeltaEq ▸ hmax y
    exact hnoBip (iso_completeBipartite_of_parts G A C hdisjAB hunionAB hAcard hCcard hBnbhd hAdeg)

lemma near_max_pair_case
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n d : ℕ}
    (hn : 600 ≤ n)
    (hcard : Fintype.card V = 2 * n + 1)
    (hlower : 2 * (n ^ 2 + n) ≤ ∑ w, G.degree w)
    (hno : ∀ {a b : V}, a ≠ b → G.degree a = G.degree b →
      ¬ JoinedByPathThree G a b)
    (v u1 u2 : V)
    (hu12 : u1 ≠ u2)
    (hdlo : n + 1 ≤ d)
    (hdu1 : G.degree u1 = d)
    (hdu2 : G.degree u2 = d)
    (hdv : G.degree v = d + 1)
    (hvD1 : v ∈ neither G u1 u2)
    (hother : ∀ w : V, w ≠ v → G.degree w ≤ d) : False := by
  have hu12deg : G.degree u1 = G.degree u2 := hdu1.trans hdu2.symm
  have hnopath12 : ¬ JoinedByPathThree G u1 u2 := hno hu12 hu12deg
  let C1 := common G u1 u2
  let L1 := leftOnly G u1 u2
  let R1 := rightOnly G u1 u2
  let D1 := neither G u1 u2
  have hLR1 : L1.card = R1.card := card_leftOnly_eq_card_rightOnly G u1 u2 hu12 hu12deg
  have hparts1 : Fintype.card V = 2 + C1.card + L1.card + R1.card + D1.card :=
    card_parts G u1 u2 hu12
  have hsize1 : 2 * n + 1 = 2 + C1.card + 2 * L1.card + D1.card := by
    rw [hcard, hLR1] at hparts1; omega
  have hC1bound : ∀ x ∈ C1, G.degree x ≤ 2 + D1.card :=
    fun x hx ↦ degree_le_of_mem_common G u1 u2 hu12 hnopath12 hx
  have hL1bound : ∀ x ∈ L1, G.degree x ≤ L1.card + D1.card :=
    fun x hx ↦ degree_le_of_mem_leftOnly G u1 u2 hu12 hnopath12 hx
  have hR1bound : ∀ x ∈ R1, G.degree x ≤ R1.card + D1.card :=
    fun x hx ↦ degree_le_of_mem_rightOnly G u1 u2 hu12 hnopath12 hx
  have hsumD1 : ∑ x ∈ D1, G.degree x ≤ D1.card * d + 1 := by
    have hsub : ∀ x ∈ D1.erase v, G.degree x ≤ d :=
      fun x hx ↦ hother x (Finset.mem_erase.mp hx).1
    have heraseSum : ∑ x ∈ D1.erase v, G.degree x ≤ (D1.erase v).card * d :=
      sum_le_card_mul (D1.erase v) (fun x ↦ G.degree x) d hsub
    have hsplitD := Finset.sum_erase_add D1 (fun x ↦ G.degree x) hvD1
    have hcardD := Finset.card_erase_add_one hvD1
    nlinarith only [heraseSum, hsplitD, hcardD, hdv]
  have hsumD1struct : ∑ x ∈ D1, G.degree x ≤ D1.card * (2 * n - 2) := by
    apply sum_le_card_mul D1 (fun x ↦ G.degree x) (2 * n - 2)
    intro x hx
    have h := degree_le_of_mem_neither G u1 u2 hu12 hx
    omega
  have hsumC1 : ∑ x ∈ C1, G.degree x ≤ C1.card * (2 + D1.card) :=
    sum_le_card_mul C1 (fun x ↦ G.degree x) (2 + D1.card) hC1bound
  have hsumL1 : ∑ x ∈ L1, G.degree x ≤ L1.card * (L1.card + D1.card) :=
    sum_le_card_mul L1 (fun x ↦ G.degree x) (L1.card + D1.card) hL1bound
  have hsumR1 : ∑ x ∈ R1, G.degree x ≤ L1.card * (L1.card + D1.card) := by
    rw [hLR1]
    exact sum_le_card_mul R1 (fun x ↦ G.degree x) (R1.card + D1.card) hR1bound
  have hsumParts1 :
      ∑ w, G.degree w = d + d + (∑ w ∈ C1, G.degree w) +
        (∑ w ∈ L1, G.degree w) + (∑ w ∈ R1, G.degree w) +
        ∑ w ∈ D1, G.degree w := by
    simpa [C1, L1, R1, D1, hdu1, hdu2] using sum_parts G u1 u2 hu12 (fun w ↦ G.degree w)
  rw [hsumParts1] at hlower
  by_cases hu12A : G.Adj u1 u2
  · have hdDelta1 : d = C1.card + L1.card + 1 := by
      rw [← hdu1, degree_eq_card_common_add_leftOnly G u1 u2 hu12, if_pos hu12A]
    have hC1inj : Set.InjOn (fun x ↦ G.degree x) (↑C1 : Set V) := by
      intro x hx y hy hdeg
      by_contra hxy
      have hxA := (mem_common G u1 u2).mp hx
      have hyA := (mem_common G u1 u2).mp hy
      exact hno hxy hdeg (joinedByPathThree_of_adj hxA.1.symm hu12A hyA.2
        hxA.1.ne.symm hxA.2.ne.symm hxy hu12 hyA.1.ne hyA.2.ne)
    have hC1sharp :
        2 * (∑ x ∈ C1, G.degree x) + C1.card * (C1.card - 1) ≤
          2 * C1.card * (2 + D1.card) :=
      sum_injective_nat_defect C1 (fun x ↦ G.degree x) (2 + D1.card) hC1inj hC1bound
    have hC1pos : 1 ≤ C1.card := by omega
    have hC1sub : C1.card - 1 + 1 = C1.card := Nat.sub_add_cancel hC1pos
    have hnsub : 2 * n - 2 + 2 = 2 * n := Nat.sub_add_cancel (by omega)
    by_cases hDcase : d ≤ 2 * n - 2
    · nlinarith only [hdDelta1, hsize1, hlower, hC1sharp, hsumL1, hsumR1,
        hsumD1, hn, hdlo, hDcase, hC1sub, hnsub]
    · have hDcase' : 2 * n - 2 ≤ d := by omega
      nlinarith only [hdDelta1, hsize1, hlower, hC1sharp, hsumL1, hsumR1,
        hsumD1struct, hn, hdlo, hDcase', hC1sub, hnsub]
  · have hdDelta1 : d = C1.card + L1.card := by
      rw [← hdu1, degree_eq_card_common_add_leftOnly G u1 u2 hu12, if_neg hu12A, Nat.add_zero]
    have hdEqN1 : d = n + 1 := by
      by_contra hne
      have hdge : n + 2 ≤ d := by omega
      nlinarith only [hdDelta1, hsize1, hlower, hsumC1, hsumL1, hsumR1, hsumD1, hdge]
    have hL1zero : L1.card = 0 := by
      by_contra hne
      have hlge : 1 ≤ L1.card := by omega
      nlinarith only [hdDelta1, hsize1, hlower, hsumC1, hsumL1, hsumR1, hsumD1, hdEqN1, hlge]
    have hR1zero : R1.card = 0 := by omega
    have hC1card : C1.card = n + 1 := by omega
    have hD1card : D1.card = n - 2 := by omega
    have hL1emp : leftOnly G u1 u2 = ∅ := Finset.card_eq_zero.mp hL1zero
    have hR1emp : rightOnly G u1 u2 = ∅ := Finset.card_eq_zero.mp hR1zero
    have hsumL10 : ∑ w ∈ L1, G.degree w = 0 := by simp [L1, hL1emp]
    have hsumR10 : ∑ w ∈ R1, G.degree w = 0 := by simp [R1, hR1emp]
    have hnsub2 : n - 2 + 2 = n := Nat.sub_add_cancel (by omega)
    have hC1boundN : ∀ x ∈ C1, G.degree x ≤ n := by
      intro x hx; have h := hC1bound x hx; omega
    have hC1sumGe : C1.card * n ≤ (∑ x ∈ C1, G.degree x) + 1 := by
      nlinarith only [hlower, hsumD1, hdEqN1, hC1card, hD1card, hsumL10, hsumR10, hnsub2]
    have hC1fullCard : C1.card - 1 ≤ (C1.filter fun x ↦ G.degree x = n).card :=
      card_filter_eq_ge_of_sum_ge C1 (fun x ↦ G.degree x) n (by omega) hC1boundN hC1sumGe
    have hvNvCard : (G.neighborFinset v).card = n + 2 := by
      rw [G.card_neighborFinset_eq_degree, hdv, hdEqN1]
    have hvSub : G.neighborFinset v ⊆ C1 ∪ D1.erase v := by
      intro z hz
      have hvz : G.Adj v z := (G.mem_neighborFinset v z).mp hz
      have hp1 := parts_union G u1 u2
      rw [hL1emp, hR1emp] at hp1
      have hmem : z ∈ {u1, u2} ∪ (common G u1 u2 ∪ (∅ ∪ (∅ ∪ neither G u1 u2))) :=
        hp1.symm ▸ Finset.mem_univ z
      have hvN := (mem_neither G u1 u2).mp hvD1
      simp only [mem_union, mem_insert, mem_singleton, Finset.notMem_empty, false_or,
        mem_erase] at hmem ⊢
      change z ∈ C1 ∨ z ≠ v ∧ z ∈ D1
      rcases hmem with (rfl | rfl) | (hzC | hzD)
      · exact False.elim (hvN.2.2.1 hvz.symm)
      · exact False.elim (hvN.2.2.2 hvz.symm)
      · exact Or.inl hzC
      · exact Or.inr ⟨hvz.ne.symm, hzD⟩
    have hnotSubC1 : ¬ G.neighborFinset v ⊆ C1 := by
      intro hsub
      have hc := Finset.card_le_card hsub
      omega
    obtain ⟨w, hwNv, hwNotC1⟩ := Finset.not_subset.mp hnotSubC1
    have hwErase : w ∈ D1.erase v := (Finset.mem_union.mp (hvSub hwNv)).resolve_left hwNotC1
    have hwv : w ≠ v := (Finset.mem_erase.mp hwErase).1
    have hwD1 : w ∈ D1 := (Finset.mem_erase.mp hwErase).2
    have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hwNv
    have hvDiffSub : G.neighborFinset v \ C1 ⊆ D1.erase v := by
      intro z hz
      exact (Finset.mem_union.mp (hvSub (Finset.mem_sdiff.mp hz).1)).resolve_left
        (Finset.mem_sdiff.mp hz).2
    have hvDiffCard : (G.neighborFinset v \ C1).card ≤ n - 3 := by
      have hc := Finset.card_le_card hvDiffSub
      rw [Finset.card_erase_of_mem hvD1, hD1card] at hc
      omega
    have hvInterCard : 5 ≤ (G.neighborFinset v ∩ C1).card := by
      have hsp := Finset.card_inter_add_card_sdiff (G.neighborFinset v) C1
      omega
    have hC1diffCard : (C1 \ C1.filter (fun x ↦ G.degree x = n)).card ≤ 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
      omega
    have hSinterCard : 4 ≤ ((G.neighborFinset v ∩ C1) ∩ C1.filter (fun x ↦ G.degree x = n)).card := by
      have hsp := Finset.card_inter_add_card_sdiff (G.neighborFinset v ∩ C1)
        (C1.filter fun x ↦ G.degree x = n)
      have hSdiffSub : (G.neighborFinset v ∩ C1) \ C1.filter (fun x ↦ G.degree x = n) ⊆
          C1 \ C1.filter (fun x ↦ G.degree x = n) :=
        Finset.sdiff_subset_sdiff Finset.inter_subset_right (Finset.Subset.refl _)
      have hc := (Finset.card_le_card hSdiffSub).trans hC1diffCard
      omega
    obtain ⟨x1, hx1S, x2, hx2S, hx12⟩ := Finset.one_lt_card.mp
      (by omega : 1 < ((G.neighborFinset v ∩ C1) ∩ C1.filter (fun x ↦ G.degree x = n)).card)
    have hx1Nv : x1 ∈ G.neighborFinset v := (Finset.mem_inter.mp (Finset.mem_inter.mp hx1S).1).1
    have hx1C1 : x1 ∈ C1 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx1S).1).2
    have hx1deg : G.degree x1 = n := (Finset.mem_filter.mp (Finset.mem_inter.mp hx1S).2).2
    have hx2C1 : x2 ∈ C1 := (Finset.mem_inter.mp (Finset.mem_inter.mp hx2S).1).2
    have hx2deg : G.degree x2 = n := (Finset.mem_filter.mp (Finset.mem_inter.mp hx2S).2).2
    have hu12D1 : Disjoint ({u1, u2} : Finset V) D1 := by
      simp [D1, Finset.disjoint_left]
    have hA1card : ({u1, u2} ∪ D1).card = n := by
      rw [Finset.card_union_of_disjoint hu12D1]
      simp [hu12, hD1card]
      omega
    have hx2nbhd : G.neighborFinset x2 = {u1, u2} ∪ D1 := by
      apply Finset.eq_of_subset_of_card_le
      · exact neighborFinset_subset_of_mem_common G u1 u2 hu12 hnopath12 hx2C1
      · rw [G.card_neighborFinset_eq_degree, hx2deg, hA1card]
    have hwx2 : G.Adj w x2 := by
      have hwA1 : w ∈ G.neighborFinset x2 := by
        rw [hx2nbhd]
        exact Finset.mem_union.mpr (Or.inr hwD1)
      exact ((G.mem_neighborFinset x2 w).mp hwA1).symm
    have hx1v : G.Adj x1 v := ((G.mem_neighborFinset v x1).mp hx1Nv).symm
    have hdisjCD : Disjoint C1 D1 := (pairwise_disjoint_parts G u1 u2).2.2.1
    have hx1v_ne : x1 ≠ v := fun h ↦ Finset.disjoint_left.mp hdisjCD hx1C1 (h ▸ hvD1)
    have hx1w_ne : x1 ≠ w := fun h ↦ Finset.disjoint_left.mp hdisjCD hx1C1 (h ▸ hwD1)
    have hvx2_ne : v ≠ x2 := fun h ↦ Finset.disjoint_left.mp hdisjCD hx2C1 (h.symm ▸ hvD1)
    have hwx2_ne : w ≠ x2 := fun h ↦ Finset.disjoint_left.mp hdisjCD hx2C1 (h.symm ▸ hwD1)
    exact hno hx12 (hx1deg.trans hx2deg.symm)
      (joinedByPathThree_of_adj hx1v hvw hwx2 hx1v_ne hx1w_ne hx12 hwv.symm hvx2_ne hwx2_ne)

lemma unique_max_degree_case
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ}
    (hn : 600 ≤ n)
    (hcard : Fintype.card V = 2 * n + 1)
    (hlower : 2 * (n ^ 2 + n) ≤ ∑ w, G.degree w)
    (hno : ∀ {a b : V}, a ≠ b → G.degree a = G.degree b →
      ¬ JoinedByPathThree G a b)
    (v : V)
    (hmax : ∀ w : V, G.degree w ≤ G.degree v)
    (huniq : ∀ w : V, G.degree w = G.degree v → w = v) : False := by
  let Δ := G.degree v
  have hlarge : n + 2 ≤ Δ := by
    by_contra hle
    let R0 := (univ : Finset V).erase v
    have hR0card : R0.card = 2 * n := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]; omega
    have hR0bound : ∀ w ∈ R0, G.degree w ≤ n := by
      intro w hw
      have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
      have hwmax := hmax w
      have hwne : G.degree w ≠ Δ := fun hd ↦ hwv (huniq w hd)
      omega
    have hR0sum : ∑ w ∈ R0, G.degree w ≤ 2 * n * n := by
      simpa [hR0card] using sum_le_card_mul R0 (fun w ↦ G.degree w) n hR0bound
    have hsplit := Finset.sum_erase_add (univ : Finset V) (fun w ↦ G.degree w) (Finset.mem_univ v)
    have hvle : Δ ≤ n + 1 := by omega
    have hup : ∑ w, G.degree w ≤ 2 * n * n + (n + 1) := by
      rw [← hsplit]; exact Nat.add_le_add hR0sum hvle
    nlinarith only [hlower, hup, hn]
  have hΔlt : Δ < 2 * n + 1 := by
    simpa [Δ, hcard] using G.degree_lt_card_verts v
  let s := Δ - n
  let p := n - s
  let T := p + 2
  let d := Δ - 1
  let r := 2 * s - 3
  have hslo : 2 ≤ s := by simp only [s]; omega
  have hsEq : Δ = n + s := by simp only [s]; omega
  have hpEq : n = p + s := by simp only [p]; omega
  have hTEq : T = p + 2 := rfl
  have hdEq : d + 1 = Δ := by simp only [d]; omega
  have hrEq : r + 3 = 2 * s := by simp only [r]; omega
  have hdTR : d = T + r := by omega
  have hother : ∀ w : V, w ≠ v → G.degree w ≤ d := by
    intro w hwv
    have hwmax := hmax w
    have hwne : G.degree w ≠ Δ := fun hd ↦ hwv (huniq w hd)
    simp only [d]; omega
  let Nv := G.neighborFinset v
  have hNvcard : Nv.card = Δ := by simp [Nv, Δ]
  have houtsideCard : ((univ : Finset V) \ Nv).card = p + 1 := by
    rw [Finset.card_sdiff]
    simp only [inter_univ, Finset.card_univ, hcard, hNvcard]
    omega
  have hcommon (u : V) (hu : u ∈ Nv) (huHigh : T < G.degree u) :
      2 ≤ (G.neighborFinset u ∩ Nv).card := by
    have hdiffSub : G.neighborFinset u \ Nv ⊆ (univ : Finset V) \ Nv := fun x hx ↦
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    have hdiff : (G.neighborFinset u \ Nv).card ≤ p + 1 := by
      rw [← houtsideCard]; exact Finset.card_le_card hdiffSub
    have hsplit := Finset.card_inter_add_card_sdiff (G.neighborFinset u) Nv
    rw [G.card_neighborFinset_eq_degree] at hsplit
    omega
  have hbound : ∀ u ∈ Nv, G.degree u ≤ d :=
    fun u hu ↦ hother u (fun h ↦ G.loopless.irrefl v (h ▸ (G.mem_neighborFinset v u).mp hu))
  have hhighInj : Set.InjOn (fun u ↦ G.degree u) {u | u ∈ Nv ∧ T < G.degree u} := by
    intro u hu w hw hdeg
    by_contra huw
    have hvu : G.Adj v u := (G.mem_neighborFinset v u).mp hu.1
    have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw.1
    exact degree_ne_of_two_common_neighbors G hno hvu hvw huw (hcommon u hu.1 hu.2) hdeg
  let E := ∑ k ∈ Finset.Ioc T d, (k - T)
  have hNsum : (∑ u ∈ Nv, G.degree u) ≤ T * Δ + E := by
    simpa [hNvcard, E] using sum_le_baseline_add_all_excesses Nv (fun u ↦ G.degree u) T d hbound hhighInj
  have hE : 2 * E = r * (r + 1) := by
    calc
      2 * E = 2 * (∑ k ∈ Finset.Ioc T (T + r), (k - T)) := by simp only [E, hdTR]
      _ = 2 * (∑ i ∈ Finset.range r, (i + 1)) := by rw [sum_Ioc_sub_eq_sum_range_succ]
      _ = r * (r + 1) := twice_sum_range_succ r
  let closed := ({v} : Finset V) ∪ Nv
  let O := (univ : Finset V) \ closed
  have hvNv : Disjoint ({v} : Finset V) Nv := by
    rw [Finset.disjoint_singleton_left]
    exact fun hv ↦ G.loopless.irrefl v ((G.mem_neighborFinset v v).mp hv)
  have hclosedCard : closed.card = 1 + Δ := by
    rw [Finset.card_union_of_disjoint hvNv]; simp [hNvcard]
  have hOcard : O.card = p := by
    rw [Finset.card_sdiff]
    simp only [closed, inter_univ, Finset.card_univ, hcard, hclosedCard]
    omega
  have hObound : ∀ u ∈ O, G.degree u ≤ d := by
    intro u hu
    refine hother u ?_
    rintro rfl
    exact (Finset.mem_sdiff.mp hu).2 (by simp [closed])
  have hOsum : ∑ u ∈ O, G.degree u ≤ p * d := by
    simpa [hOcard] using sum_le_card_mul O (fun u ↦ G.degree u) d hObound
  have hsumSplit :
      ∑ u, G.degree u = Δ + (∑ u ∈ Nv, G.degree u) + ∑ u ∈ O, G.degree u := by
    have hsum := Finset.sum_sdiff (Finset.subset_univ closed) (f := fun u ↦ G.degree u)
    have hclosedSum : ∑ u ∈ closed, G.degree u = Δ + ∑ u ∈ Nv, G.degree u := by
      rw [Finset.sum_union hvNv]; simp [Δ]
    change (∑ u ∈ (univ : Finset V), G.degree u) = _
    simp only [O]
    rw [← hsum, hclosedSum]
    omega
  have hsle3 : s ≤ 3 := by
    by_contra hsgt
    have hs4 : 4 ≤ s := by omega
    nlinarith only [hlower, hsumSplit, hNsum, hOsum, hsEq, hpEq, hTEq, hdEq, hrEq, hs4, hE]
  have hOsumGe : O.card * d ≤ (∑ u ∈ O, G.degree u) + 1 := by
    have h2 : 2 * (p * d) ≤ 2 * (∑ u ∈ O, G.degree u) + (6 - 2 * s) := by
      have hssub : 6 - 2 * s + 2 * s = 6 := Nat.sub_add_cancel (by omega)
      nlinarith only [hlower, hsumSplit, hNsum, hsEq, hpEq, hTEq, hdEq, hrEq, hslo, hsle3, hE, hssub]
    rw [hOcard]
    omega
  have hOhighCard : O.card - 1 ≤ (O.filter fun u ↦ G.degree u = d).card :=
    card_filter_eq_ge_of_sum_ge O (fun u ↦ G.degree u) d (by omega) hObound hOsumGe
  have hOhighGt1 : 1 < (O.filter fun u ↦ G.degree u = d).card := by
    rw [hOcard] at hOhighCard
    omega
  obtain ⟨u1, hu1f, u2, hu2f, hu12⟩ := Finset.one_lt_card.mp hOhighGt1
  have hu1O : u1 ∈ O := (Finset.mem_filter.mp hu1f).1
  have hu2O : u2 ∈ O := (Finset.mem_filter.mp hu2f).1
  have hdu1 : G.degree u1 = d := (Finset.mem_filter.mp hu1f).2
  have hdu2 : G.degree u2 = d := (Finset.mem_filter.mp hu2f).2
  have hvD1 : v ∈ neither G u1 u2 := by
    have hu1nc := (Finset.mem_sdiff.mp hu1O).2
    have hu2nc := (Finset.mem_sdiff.mp hu2O).2
    have hv1 : v ≠ u1 := fun h ↦ hu1nc (by simp [closed, h.symm])
    have hv2 : v ≠ u2 := fun h ↦ hu2nc (by simp [closed, h.symm])
    have hna1 : ¬ G.Adj u1 v := fun hadj ↦ hu1nc
      (Finset.mem_union.mpr (Or.inr ((G.mem_neighborFinset v u1).mpr hadj.symm)))
    have hna2 : ¬ G.Adj u2 v := fun hadj ↦ hu2nc
      (Finset.mem_union.mpr (Or.inr ((G.mem_neighborFinset v u2).mpr hadj.symm)))
    exact (mem_neither G u1 u2).mpr ⟨hv1, hv2, hna1, hna2⟩
  exact near_max_pair_case G hn hcard hlower hno v u1 u2 hu12 (by omega)
    hdu1 hdu2 hdEq.symm hvD1 hother

end OMA816

open scoped Classical in
theorem OMA.solution : type_of% @Erdos816.erdos_816.variants.chen_ma := by
  intro n hn G hedges hnoBip
  by_contra hnot
  have hno : ∀ {a b : Fin (2 * n + 1)}, a ≠ b → G.degree a = G.degree b →
      ¬ OMA816.JoinedByPathThree G a b :=
    fun _ hdeg hp ↦ hnot (OMA816.hasEqualDegreePathThree_of_joined G hdeg hp)
  have hcard : Fintype.card (Fin (2 * n + 1)) = 2 * n + 1 := Fintype.card_fin _
  have hlower : 2 * (n ^ 2 + n) ≤ ∑ w, G.degree w := by
    calc
      2 * (n ^ 2 + n) ≤ 2 * G.edgeFinset.card := Nat.mul_le_mul_left 2 hedges
      _ = ∑ w, G.degree w := G.sum_degrees_eq_twice_card_edges.symm
  obtain ⟨v, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin (2 * n + 1)))
      (fun w ↦ G.degree w) Finset.univ_nonempty
  have hmax' : ∀ w : Fin (2 * n + 1), G.degree w ≤ G.degree v :=
    fun w ↦ hmax w (Finset.mem_univ w)
  by_cases hrep : ∃ u : Fin (2 * n + 1), u ≠ v ∧ G.degree u = G.degree v
  · obtain ⟨u, huv, hdeg⟩ := hrep
    exact OMA816.repeated_max_degree_case G hn hcard hlower hnoBip hno huv hdeg rfl hmax'
  · have huniq : ∀ w : Fin (2 * n + 1), G.degree w = G.degree v → w = v := by
      intro w hw
      by_contra hwv
      exact hrep ⟨w, hwv, hw⟩
    exact OMA816.unique_max_degree_case G hn hcard hlower hno v hmax' huniq
