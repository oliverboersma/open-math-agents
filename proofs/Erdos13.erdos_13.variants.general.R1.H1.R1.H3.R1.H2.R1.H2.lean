import OMAReductions.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1_H2_R1

-- Credit: @jenil-bodhani

section

/-  Dense choices of heights have a common central interval of attainable sums. -/
namespace Erdos13ExtraRow
open Finset

private theorem choose_pair {r t : ℕ} (hr : 4≤r) (lo : 6≤t) (hi : t≤2*r) (m n : ℕ) :
    ∃ a b : ℕ, 2≤a ∧ a≤r+1 ∧ a≠m ∧ 2≤b ∧ b≤r+1 ∧ b≠n ∧ a+b=t := by
  let a := max 2 (t-(r+1))
  have room : 2≤a ∧ a+2≤r+1 ∧ a+4≤t ∧ t≤a+(r+1) := by dsimp [a]; omega
  by_cases x : a≠m ∧ t-a≠n
  · exact ⟨a,t-a,room.1,by omega,x.1,by omega,by omega,x.2,by omega⟩
  by_cases y : a+1≠m ∧ t-(a+1)≠n
  · exact ⟨a+1,t-(a+1),by omega,by omega,y.1,by omega,by omega,y.2,by omega⟩
  exact ⟨a+2,t-(a+2),by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

/-- Every sum from 3n through rn is available when n≥2 and each summand may
use any height in [2,r+1] except for a single specified value. -/
theorem central_heights {r n : ℕ} (hr : 4≤r) (hn : 2≤n) :
    ∀ (m : Fin n → ℕ) (t : ℕ), 3*n≤t → t≤r*n →
      ∃ b : Fin n → ℕ, (∀ i,2≤b i ∧ b i≤r+1 ∧ b i≠m i) ∧ (∑ i,b i)=t := by
  induction n,hn using Nat.le_induction with
  | base =>
    intro m t lo hi
    obtain ⟨a,b,al,au,am,bl,bu,bn,eq⟩ := choose_pair hr (by omega) (by omega) (m 0) (m 1)
    exact ⟨![a,b],by intro i; fin_cases i; exact ⟨al,au,am⟩; exact ⟨bl,bu,bn⟩,by simpa [Fin.sum_univ_two] using eq⟩
  | succ n hn ih =>
    intro m t lo hi
    let l := if m 0=2 then 3 else 2
    let h := if m 0=r then r+1 else r
    have sl : 2≤l ∧ l≤3 ∧ l≠m 0 := by dsimp [l]; split <;> omega
    have sh : r≤h ∧ h≤r+1 ∧ h≠m 0 := by dsimp [h]; split <;> omega
    have bridge : 3*n+(r+1)≤r*n+3 := by
      have e := Nat.sub_add_cancel (show 3≤r by omega)
      have z := congrArg (· * n) e
      have q := Nat.mul_le_mul_left (r-3) hn
      nlinarith only [z,q,e,hr]
    let k := if t≤r*n+l then l else h
    have sk : 2≤k ∧ k≤r+1 ∧ k≠m 0 ∧ 3*n≤t-k ∧ t-k≤r*n ∧ k+(t-k)=t := by
      rw [Nat.mul_succ] at hi lo
      dsimp [k]; split <;> omega
    obtain ⟨b,hb,eq⟩ := ih (fun i=>m i.succ) (t-k) sk.2.2.2.1 sk.2.2.2.2.1
    refine ⟨Fin.cons k b,fun i=>Fin.cases (by simpa using And.intro sk.1 (And.intro sk.2.1 sk.2.2.1))
      (fun j=>by simpa using hb j) i,?_⟩
    simpa [Fin.sum_univ_succ,eq] using sk.2.2.2.2.2

end Erdos13ExtraRow

end

section

/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Adapted from gdahia/ExtendingPollardForTRepresentableSums, commit 516693eeee.
Licensed under the Apache License, Version 2.0, available at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: Mantas Bakšys, Yaël Dillies
-/

/- 
# Stabilizer of a finset

This file defines the stabilizer of a finset of a group as a finset.

## Main declarations

* `Finset.mulStab`: The stabilizer of a **nonempty** finset as a finset.
-/

open Function MulAction
open scoped Pointwise

namespace Finset
variable {ι α : Type*}

section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

instance (s : Finset α) : DecidablePred (· ∈ stabilizer α (s : Set α)) :=
  fun a ↦ decidable_of_iff (a ∈ stabilizer α s) (by simp)

/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`. -/

def mulStab (s : Finset α) : Finset α := {a ∈ s / s | a • s = s}

@[simp]
lemma mem_mulStab (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s = s := by
  rw [mulStab, mem_filter, mem_div, and_iff_right_of_imp]
  obtain ⟨b, hb⟩ := hs
  exact fun h ↦ ⟨_, by rw [← h]; exact smul_mem_smul_finset hb, _, hb, mul_div_cancel_right _ _⟩

lemma mulStab_subset_div : s.mulStab ⊆ s / s := filter_subset _ _

lemma mulStab_subset_div_right (ha : a ∈ s) : s.mulStab ⊆ s / {a} := by
  refine fun b hb ↦ mem_div.2 ⟨_, ?_, _, mem_singleton_self _, mul_div_cancel_right _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rw [← hb]
  exact smul_mem_smul_finset ha

@[simp]
lemma coe_mulStab (hs : s.Nonempty) : (s.mulStab : Set α) = stabilizer α (s : Set α) := by
  ext; simp [mem_mulStab hs]

lemma mem_mulStab_iff_subset_smul_finset (hs : s.Nonempty) : a ∈ s.mulStab ↔ s ⊆ a • s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_subset_smul_finset]

lemma mem_mulStab_iff_smul_finset_subset (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s ⊆ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_smul_finset_subset]

lemma mem_mulStab' (hs : s.Nonempty) : a ∈ s.mulStab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset, mem_stabilizer_finset']

@[simp]
lemma mulStab_empty : mulStab (∅ : Finset α) = ∅ := by simp [mulStab]

@[simp]
lemma mulStab_singleton (a : α) : mulStab ({a} : Finset α) = 1 := by
  simp [mulStab, singleton_one, filter_true_of_mem]

lemma Nonempty.of_mulStab : s.mulStab.Nonempty → s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, not_imp_not]; rintro rfl; exact mulStab_empty

@[simp]
lemma one_mem_mulStab : (1 : α) ∈ s.mulStab ↔ s.Nonempty :=
  ⟨fun h ↦ Nonempty.of_mulStab ⟨_, h⟩, fun h ↦ (mem_mulStab h).2 <| one_smul _ _⟩

lemma Nonempty.mulStab (h : s.Nonempty) : s.mulStab.Nonempty := ⟨_, (one_mem_mulStab.mpr h)⟩

@[simp]
lemma mulStab_nonempty : s.mulStab.Nonempty ↔ s.Nonempty := ⟨Nonempty.of_mulStab, Nonempty.mulStab⟩

@[simp]
lemma card_mulStab_eq_one : #s.mulStab = 1 ↔ s.mulStab = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, card_one]⟩
  obtain ⟨a, ha⟩ := card_eq_one.1 h
  rw [ha]
  rw [eq_singleton_iff_nonempty_unique_mem, mulStab_nonempty, ← one_mem_mulStab] at ha
  rw [← ha.2 _ ha.1, singleton_one]

lemma Nonempty.mulStab_nontrivial (h : s.Nonempty) : s.mulStab.Nontrivial ↔ s.mulStab ≠ 1 :=
  nontrivial_iff_ne_singleton (one_mem_mulStab.mpr h)

lemma subset_mulStab_mul_left (ht : t.Nonempty) : s.mulStab ⊆ (s * t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  simp_rw [subset_iff, mem_mulStab hs, mem_mulStab (hs.mul ht)]
  rintro a h
  rw [← smul_mul_assoc, h]

@[simp]
lemma mulStab_mul (s : Finset α) : s.mulStab * s = s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact mul_empty _
  · simp only [← coe_inj, hs, coe_mul, coe_mulStab, stabilizer_mul_self]

lemma mul_subset_right_iff (ht : t.Nonempty) : s * t ⊆ t ↔ s ⊆ t.mulStab := by
  simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_subset,
    ← mem_mulStab_iff_smul_finset_subset ht, subset_iff]

lemma mul_subset_right : s ⊆ t.mulStab → s * t ⊆ t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  · exact (mul_subset_right_iff ht).2

lemma smul_mulStab (ha : a ∈ s.mulStab) : a • s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe] at ha
  rw [← coe_inj, coe_smul_finset, coe_mulStab hs, smul_coe_set ha]

@[simp]
lemma mulStab_mul_mulStab (s : Finset α) : s.mulStab * s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_congr rfl fun _ ↦ smul_mulStab,
      ← sup_eq_biUnion, sup_const hs.mulStab]

lemma inter_mulStab_subset_mulStab_union : s.mulStab ∩ t.mulStab ⊆ (s ∪ t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  intro x hx
  rw [mem_mulStab (hs.mono subset_union_left), smul_finset_union,
    (mem_mulStab hs).mp (mem_of_mem_inter_left hx),
    (mem_mulStab ht).mp (mem_of_mem_inter_right hx)]

end Group

variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

lemma mulStab_subset_div_left (ha : a ∈ s) : s.mulStab ⊆ {a} / s := by
  refine fun b hb ↦ mem_div.2 ⟨_, mem_singleton_self _, _, ?_, div_div_cancel _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rwa [← hb, ← inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha

lemma subset_mulStab_mul_right (hs : s.Nonempty) : t.mulStab ⊆ (s * t).mulStab := by
  rw [mul_comm]; exact subset_mulStab_mul_left hs

@[simp]
lemma mul_mulStab (s : Finset α) : s * s.mulStab = s := by rw [mul_comm]; exact mulStab_mul _

@[simp]
lemma mul_mulStab_mul_mul_mul_mulStab_mul :
    s * (s * t).mulStab * (t * (s * t).mulStab) = s * t := by
  rw [mul_mul_mul_comm, mulStab_mul_mulStab, mul_mulStab]

lemma smul_finset_mulStab_subset (ha : a ∈ s) : a • s.mulStab ⊆ s :=
  (smul_finset_subset_smul ha).trans s.mul_mulStab.subset

lemma mul_subset_left_iff (hs : s.Nonempty) : s * t ⊆ s ↔ t ⊆ s.mulStab := by
  rw [mul_comm, mul_subset_right_iff hs]

lemma mul_subset_left : t ⊆ s.mulStab → s * t ⊆ s := by rw [mul_comm]; exact mul_subset_right

@[simp]
lemma mulStab_idem (s : Finset α) : s.mulStab.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.mulStab, coe_mulStab hs]
  simp

@[simp]
lemma mulStab_smul (a : α) (s : Finset α) : (a • s).mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.smul_finset, stabilizer_coe_finset,
    stabilizer_coe_finset, stabilizer_smul_eq_right]

lemma mulStab_image_coe_quotient (hs : s.Nonempty) :
    (s.image (↑) : Finset (α ⧸ stabilizer α (s : Set α))).mulStab = 1 := by
  simp_rw [← coe_inj, coe_mulStab (hs.image _), coe_image, coe_one]
  rw [stabilizer_image_coe_quotient, Subgroup.coe_bot, Set.singleton_one]

lemma preimage_image_quotientMk_stabilizer_eq_mul_mulStab (ht : t.Nonempty) (s : Finset α) :
    QuotientGroup.mk ⁻¹' (Set.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s) = s * t.mulStab := by
  rw [QuotientGroup.preimage_image_mk_eq_mul, coe_mulStab ht, stabilizer_coe_finset]

lemma preimage_image_quotientMk_mulStabilizer (s : Finset α) :
    QuotientGroup.mk ⁻¹' (Set.image ((↑) : α → α ⧸ stabilizer α (s : Set α)) s) = s := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab hs s, ← coe_mul, mul_mulStab]

lemma pairwiseDisjoint_smul_finset_mulStab (s : Finset α) :
    (Set.range fun a : α ↦ a • s.mulStab).PairwiseDisjoint id := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simp only [onFun, id_eq]
  simp_rw [← disjoint_coe, ← coe_injective.ne_iff, coe_smul_finset, coe_mulStab hs]
  exact fun h ↦ isBlock_subgroup h

lemma disjoint_smul_finset_mulStab_mul_mulStab :
    ¬a • s.mulStab ⊆ t * s.mulStab → Disjoint (a • s.mulStab) (t * s.mulStab) := by
  simp_rw [@not_imp_comm (_ ≤ _), ← smul_eq_mul, ← biUnion_smul_finset, disjoint_biUnion_right,
    Classical.not_forall]
  rintro ⟨b, hb, h⟩
  rw [s.pairwiseDisjoint_smul_finset_mulStab.eq (Set.mem_range_self _) (Set.mem_range_self _) h]
  exact subset_biUnion_of_mem (· • mulStab s) hb

lemma card_mulStab_dvd_card_mul_mulStab (s t : Finset α) : #t.mulStab ∣ #(s * t.mulStab) :=
  card_dvd_card_smul_right <|
    t.pairwiseDisjoint_smul_finset_mulStab.subset <| Set.image_subset_range _ _

lemma card_mulStab_dvd_card (s : Finset α) : #s.mulStab ∣ #s := by
  simpa only [mul_mulStab] using s.card_mulStab_dvd_card_mul_mulStab s

lemma card_mulStab_le_card : #s.mulStab ≤ #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rfl
  · exact Nat.le_of_dvd hs.card_pos s.card_mulStab_dvd_card

/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.mulStab`. -/

abbrev fintypeStabilizerOfMulStab (hs : s.Nonempty) : Fintype (stabilizer α s) where
  elems := s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩
  complete a := mem_map.2
    ⟨⟨_, (mem_mulStab hs).2 a.2⟩, mem_attach _ ⟨_, (mem_mulStab hs).2 a.2⟩, Subtype.ext rfl⟩

lemma card_mulStab_dvd_card_mulStab (hs : s.Nonempty) (h : s.mulStab ⊆ t.mulStab) :
    #s.mulStab ∣ #t.mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  rw [← coe_subset, coe_mulStab hs, coe_mulStab ht, SetLike.coe_subset_coe] at h
  let : Fintype (stabilizer α s) := fintypeStabilizerOfMulStab hs
  let : Fintype (stabilizer α t) := fintypeStabilizerOfMulStab ht
  convert Subgroup.card_dvd_of_le h using 1
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩)
    simp
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(t.mulStab.attach.map
      ⟨Subtype.map id fun _ ↦ (mem_mulStab ht).1, Subtype.map_injective _ injective_id⟩)
    simp

/-- A version of Lagrange's theorem. -/

lemma card_mulStab_mul_card_image_coe' (s t : Finset α)
    [DecidableEq (α ⧸ stabilizer α (t : Set α))] :
    #t.mulStab * #(s.image ((↑) : α → α ⧸ stabilizer α (t : Set α))) = #(s * t.mulStab) := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ (Set.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s)
  have that : ↥(stabilizer α (t : Set α)) = ↥t.mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab ht, Finset.coe_sort_coe]
  have temp := this.trans ((Equiv.cast that).prodCongr (Equiv.refl _))
  rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab ht] at temp
  simpa only [coe_sort_coe, ← coe_mul, Fintype.card_prod, Fintype.card_coe, Fintype.card_ofFinset,
    toFinset_coe, mem_image, Set.mem_image, mem_coe, forall_const, eq_comm]
    using Fintype.card_congr temp

lemma card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
    #(s * t) = #(s * t).mulStab * #((s * t).image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α))) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ <|
    Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) ↑(s * t)
  have that : ↥(stabilizer α (↑(s * t) : Set α)) = ↥(s * t).mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans <| (Equiv.cast that).prodCongr (Equiv.refl _)
  rw [preimage_image_quotientMk_mulStabilizer] at temp
  simpa [-coe_mul] using Fintype.card_congr temp

end Finset
/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Adapted from gdahia/ExtendingPollardForTRepresentableSums, commit 516693eeee.
Licensed under the Apache License, Version 2.0, available at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: Mantas Bakšys, Yaël Dillies
-/

/-
# Kneser's addition theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`. Further,
if the inequality is strict, then we in fact have `|s + H| + |t + H| ≤ |s + t|`.

## Main declarations

* `Finset.mul_kneser`: Kneser's theorem.
* `Finset.mul_strict_kneser`: Strict Kneser theorem.

## References

* [Imre Ruzsa, *Sumsets and structure*][ruzsa2009]
* Matt DeVos, *A short proof of Kneser's addition theorem*
-/

open Function MulAction
open scoped Pointwise

variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}

namespace Finset

/- ### Auxiliary results -/

lemma mulStab_mul_ssubset_mulStab (hs₁ : (s ∩ a • C.mulStab).Nonempty)
    (ht₁ : (t ∩ b • C.mulStab).Nonempty) (hab : ¬(a * b) • C.mulStab ⊆ s * t) :
    (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊂ C.mulStab := by
  have hCne : C.Nonempty := by
    contrapose! hab
    simp only [hab, mulStab_empty, smul_finset_empty, empty_subset]
  obtain ⟨x, hx⟩ := hs₁
  obtain ⟨y, hy⟩ := ht₁
  obtain ⟨c, hc, hac⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hx)
  obtain ⟨d, hd, had⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hy)
  have hsubset : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab := by
    have hxymem : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
    apply subset_trans (mulStab_subset_div_right hxymem)
    have : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (x * y) • C.mulStab := by
      apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
      rw [smul_mul_smul_comm]
      rw [← hac, ← had, smul_mul_smul_comm, smul_assoc]
      apply smul_finset_subset_smul_finset
      rw [← smul_smul]
      rw [mul_subset_iff]
      intro x hx y hy
      rw [smul_mulStab hd, smul_mulStab hc, mem_mulStab hCne, ← smul_smul,
        (mem_mulStab hCne).mp hy, (mem_mulStab hCne).mp hx]
    apply subset_trans (div_subset_div_right this) _
    simp [singleton_mul, div_eq_inv_mul, smul_smul, mul_assoc]
  have : (a * b) • C.mulStab = (a * c * (b * d)) • C.mulStab := by
    rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc, ←
      mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_cancel (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_mulStab hc, smul_mulStab hd]
  have hsub : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (a * b) • C.mulStab := by
    apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  have hxy : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
  rw [this] at hsub
  rw [this] at hab
  obtain ⟨z, hz, hzst⟩ := not_subset.1 hab
  obtain ⟨w, hw, hwz⟩ := mem_smul_finset.mp hz
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨w, hw, ?_⟩
  rw [mem_mulStab' ⟨x * y, hxy⟩]
  push Not
  refine ⟨a * c * (b * d), by simp_all, ?_⟩
  rw [smul_eq_mul, mul_comm w, ← smul_eq_mul (b := w), hwz]
  exact notMem_mono (mul_subset_mul inter_subset_left inter_subset_left) hzst

lemma mulStab_union (hs₁ : (s ∩ a • C.mulStab).Nonempty) (ht₁ : (t ∩ b • C.mulStab).Nonempty)
    (hab : ¬(a * b) • C.mulStab ⊆ s * t)
    (hC : Disjoint C (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))) :
    (C ∪ s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab =
      (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab := by
  obtain rfl | hCne := C.eq_empty_or_nonempty
  · simp
  refine
    ((subset_inter (mulStab_mul_ssubset_mulStab hs₁ ht₁ hab).subset Subset.rfl).trans
          inter_mulStab_subset_mulStab_union).antisymm'
      fun x hx => ?_
  replace hx := (mem_mulStab <| (hs₁.mul ht₁).mono subset_union_right).mp hx
  rw [smul_finset_union] at hx
  suffices hxC : x ∈ C.mulStab by
    rw [(mem_mulStab hCne).mp hxC] at hx
    rw [mem_mulStab_iff_subset_smul_finset (hs₁.mul ht₁)]
    exact hC.symm.left_le_of_le_sup_left (le_sup_right.trans hx.ge)
  rw [mem_mulStab_iff_smul_finset_subset hCne]
  obtain h | h := disjoint_or_nonempty_inter (x • C) (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))
  · exact h.left_le_of_le_sup_right (le_sup_left.trans_eq hx)
  have hUn :
    ((C.biUnion fun y => x • y • C.mulStab) ∩
        (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))).Nonempty := by
    have : (x • C.biUnion fun y => y • C.mulStab) = C.biUnion fun y => x • y • C.mulStab :=
      biUnion_image
    simpa [← this]
  simp_rw [biUnion_inter, biUnion_nonempty, ← smul_assoc, smul_eq_mul] at hUn
  obtain ⟨y, hy, hyne⟩ := hUn
  have hxyCsubC : (x * y) • C.mulStab ⊆ x • C := by
    rw [← smul_eq_mul, smul_assoc, smul_finset_subset_smul_finset_iff]
    exact smul_finset_mulStab_subset hy
  have hxyC : Disjoint ((x * y) • C.mulStab) C := by
    convert disjoint_smul_finset_mulStab_mul_mulStab fun hxyC => _
    · exact C.mul_mulStab.symm
    rw [mul_mulStab] at hxyC
    exact hyne.not_disjoint (hC.mono_left hxyC)
  have hxysub : (x * y) • C.mulStab ⊆ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) :=
    hxyC.left_le_of_le_sup_left (hxyCsubC.trans <| subset_union_left.trans hx.subset)
  suffices s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊂ (a * b) • C.mulStab by
    have := (card_le_card hxysub).not_gt ((card_lt_card this).trans_eq ?_)
    cases this
    simp_rw [card_smul_finset]
  apply ssubset_of_subset_not_subset
  · refine (mul_subset_mul inter_subset_right inter_subset_right).trans ?_
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  · contrapose hab
    exact hab.trans (mul_subset_mul inter_subset_left inter_subset_left)

lemma mul_aux1
    (ih : #(s' * (s' * t').mulStab) + #(t' * (s' * t').mulStab) ≤ #(s' * t') + #(s' * t').mulStab)
    (hconv : #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab)
    (hnotconv :
      #(C ∪ s' * t') + #(C ∪ s' * t').mulStab < #(s ∩ t) + #((s ∪ t) * (C ∪ s' * t').mulStab))
    (hCun : (C ∪ s' * t').mulStab = (s' * t').mulStab) (hdisj : Disjoint C (s' * t')) :
    (#((s ∪ t) * C.mulStab) - #((s ∪ t) * (s' * t').mulStab) : ℤ) <
      #C.mulStab - #(s' * (s' * t').mulStab) - #(t' * (s' * t').mulStab) := by
  set H := C.mulStab
  set H' := (s' * t').mulStab
  set C' := C ∪ s' * t'
  zify at hconv hnotconv ih
  calc
    (#((s ∪ t) * H) - #((s ∪ t) * H') : ℤ) < #C + #H - #(s ∩ t) - (#C' + #H' - #(s ∩ t)) := by
      rw [← hCun]
      linarith [hconv, hnotconv]
    _ = #H - #(s' * t') - #H' := by
      rw [card_union_of_disjoint hdisj, Int.natCast_add]
      abel
    _ ≤ #H - #(s' * H') - #(t' * H') := by linarith [ih]

lemma disjoint_smul_mulStab (hst : s ⊆ t) (has : ¬a • s.mulStab ⊆ t) :
    Disjoint s (a • s.mulStab) := by
  suffices Disjoint (a • s.mulStab) (s * s.mulStab) by
    simpa [mul_comm, disjoint_comm, mulStab_mul]
  apply disjoint_smul_finset_mulStab_mul_mulStab
  rw [mul_comm, mulStab_mul]
  contrapose has
  exact subset_trans has hst

lemma disjoint_mul_sub_card_le {a : α} (b : α) {s t C : Finset α} (has : a ∈ s)
    (hsC : Disjoint t (a • C.mulStab))
    (hst : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
        #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) =
        #(a • C.mulStab \
            (s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset
          (subset_trans (mul_subset_mul_left hst)
            (subset_trans (mul_subset_mul_right inter_subset_right) _)),
        card_smul_finset, Int.ofNat_sub]
      · apply le_trans (card_le_card (mul_subset_mul_left hst))
        apply
          le_trans (card_le_card inter_mul_subset)
            (le_of_le_of_eq (card_le_card inter_subset_right) _)
        rw [smul_mul_assoc, mulStab_mul_mulStab, card_smul_finset]
      · simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      gcongr #?_
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose hx'
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      replace hyst : y ∈ s := by
        apply or_iff_not_imp_right.mp (mem_union.mp hyst)
        contrapose hsC
        exact not_disjoint_iff.mpr ⟨y, hsC, hyC⟩
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

lemma inter_mul_sub_card_le {a : α} {s t C : Finset α} (has : a ∈ s)
    (hst : (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
        #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
            #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
          #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
        #(a • C.mulStab \
            ((s ∩ a • C.mulStab ∪ t ∩ a • C.mulStab) *
              (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset, Int.ofNat_sub (card_le_card _), card_smul_finset]
      · grw [union_mul, le_sub_iff_add_le, card_union_le]
        norm_num
      all_goals
        apply subset_trans (mul_subset_mul_left hst)
        rw [← union_inter_distrib_right]
        refine subset_trans (mul_subset_mul_right inter_subset_right) ?_
        simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      apply card_le_card
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose hx'
      rw [← union_inter_distrib_right]
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

lemma card_mul_add_card_lt (hC : C.Nonempty) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hCst : C ⊆ s * t) (hCst' : Disjoint C (s' * t')) :
    #(s' * t') + #s' < #(s * t) + #s :=
  add_lt_add_of_lt_of_le
      (by
        rw [← tsub_pos_iff_lt, ← card_sdiff_of_subset (mul_subset_mul hs ht), card_pos]
        exact hC.mono (subset_sdiff.2 ⟨hCst, hCst'⟩)) <|
    card_le_card hs

/- ### Kneser's theorem -/

variable (s t)

/-- **Kneser's multiplication theorem**: A lower bound on the size of `s * t` in terms of its
stabilizer. -/

theorem mul_kneser :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab)
      ≤ #(s * t) + #(s * t).mulStab := by
  -- We're doing induction on `#(s * t) + #s` generalizing the group. This is a bit tricky
  -- in Lean.
  set n : ℕ := #(s * t) + #s with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing α with | h n ih =>
  subst hn
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  classical
  -- We distinguish whether `s * t` has trivial stabilizer.
  obtain hstab | hstab := ne_or_eq (s * t).mulStab 1
  · have image_coe_mul :
      ((s * t).image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) =
        s.image (↑) * t.image (↑) :=
      image_mul (QuotientGroup.mk' _ : α →* α ⧸ stabilizer α (↑(s * t) : Set α))
    suffices hineq :
      #(s * t).mulStab *
          (#(s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) +
              #(t.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) -  1) ≤
        #(s * t) by
    -- now to prove that `#(s * (s * t).mulStab) = #(s * t).mulStab * #(s.image (↑))` and
    -- the analogous statement for `s` and `t` interchanged
    -- this will conclude the proof of the first case immediately
      rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mulStab_mul_card_image_coe',
        card_mulStab_mul_card_image_coe'] at hineq
      convert! hineq using 1
      exact add_comm _ _
    refine le_of_le_of_eq (mul_le_mul_right ?_ _) (card_mul_card_eq_mulStab_card_mul_coe s t).symm
    have := ih _ ?_ (s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) (t.image (↑)) rfl
    · classical
      simpa only [← image_coe_mul, mulStab_image_coe_quotient (hs.mul ht), mul_one,
        tsub_le_iff_right, card_one] using this
    rw [← image_coe_mul, card_mul_card_eq_mulStab_card_mul_coe]
    exact
      add_lt_add_of_lt_of_le
        (lt_mul_left ((hs.mul ht).image _).card_pos <|
          Finset.one_lt_card.2 ((hs.mul ht).mulStab_nontrivial.2 hstab))
        card_image_le
  -- Simplify the induction hypothesis a bit. We will only need it over `α` from now on.
  simp only [hstab, mul_one, card_one] at ih ⊢
  replace ih := fun s' t' h => @ih _ h α _ _ s' t' rfl
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · rw [card_singleton, card_singleton_mul, add_comm]
  have : b / a ∉ t.mulStab := by
    refine fun h => hab (Eq.symm (eq_of_div_eq_one ?_))
    replace h := subset_mulStab_mul_right hs h
    rw [hstab, mem_one] at h
    exact h
  simp only [mem_mulStab' ht, smul_eq_mul, Classical.not_forall, exists_prop] at this
  obtain ⟨c, hc, hbac⟩ := this
  set t' := (a / c) • t with ht'
  clear_value t'
  rw [← inv_smul_eq_iff] at ht'
  subst ht'
  rename' t' => t
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel] at hc
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ← mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac
  rw [smul_finset_nonempty] at ht
  simp only [mul_smul_comm, mulStab_smul, card_smul_finset] at *
  have hst : (s ∩ t).Nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left, not_subset.2 ⟨_, hb, fun h => hbac <| inter_subset_right h⟩⟩
  clear! a b
  set convergent : Set (Finset α) :=
    {C | C ⊆ s * t ∧ #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab}
  have convergent_nonempty : convergent.Nonempty := by
    refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_left (card_le_card <|
      subset_mul_left _ <| one_mem_mulStab.2 <| hst.mul <| hs.mono subset_union_left) _).trans <|
        ih (s ∩ t) (s ∪ t) ?_⟩
    exact add_lt_add_of_le_of_lt (card_le_card inter_mul_union_subset) (card_lt_card hsts)
  let C := argminOn (fun C : Finset α => #C.mulStab) _ convergent_nonempty
  set H := C.mulStab with hH
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argminOn_mem _ _ _
  have hCmin (D : Finset α) (hDH : D.mulStab ⊂ H) : D ∉ convergent := fun hD ↦
    (card_lt_card hDH).not_ge <| argminOn_le (fun D : Finset α => #D.mulStab) _ hD
  clear_value C
  clear convergent_nonempty
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp [hst.ne_empty] at hCcard
  -- If the stabilizer of `C` is trivial, then
  -- `#s + #t - 1 = #(s ∩ t) + #(s ∪ t) - 1 = ≤ #C ≤ #(s * t)`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mulStab.2 hC)
  · simp only [hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard
    grw [hCcard, hCst]
  exfalso
  have : ¬s * t * H ⊆ s * t := by
    rw [mul_subset_left_iff (hs.mul ht), hstab, ← coe_subset, coe_one]
    exact hCstab.coe.not_subset_singleton
  simp_rw [mul_subset_iff_left, Classical.not_forall, mem_mul] at this
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hab⟩ := this
  set s₁ := s ∩ a • H with hs₁
  set s₂ := s ∩ b • H with hs₂
  set t₁ := t ∩ b • H with ht₁
  set t₂ := t ∩ a • H with ht₂
  have hs₁s : s₁ ⊆ s := inter_subset_left
  have hs₂s : s₂ ⊆ s := inter_subset_left
  have ht₁t : t₁ ⊆ t := inter_subset_left
  have ht₂t : t₂ ⊆ t := inter_subset_left
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hs₁ne : s₁.Nonempty := ⟨_, has₁⟩
  have ht₁ne : t₁.Nonempty := ⟨_, hbt₁⟩
  set C₁ := C ∪ s₁ * t₁
  set C₂ := C ∪ s₂ * t₂
  set H₁ := (s₁ * t₁).mulStab with hH₁
  set H₂ := (s₂ * t₂).mulStab
  have hC₁st : C₁ ⊆ s * t := union_subset hCst (mul_subset_mul hs₁s ht₁t)
  have hC₂st : C₂ ⊆ s * t := union_subset hCst (mul_subset_mul hs₂s ht₂t)
  have hstabH₁ : s₁ * t₁ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hstabH₂ : s₂ * t₂ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm, mul_comm s₂ t₂]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hCst₁ := disjoint_of_subset_right hstabH₁ (disjoint_smul_mulStab hCst hab)
  have hCst₂ := disjoint_of_subset_right hstabH₂ (disjoint_smul_mulStab hCst hab)
  have hst₁ : #(s₁ * t₁) + #s₁ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₁s ht₁t hCst hCst₁
  have hst₂ : #(s₂ * t₂) + #s₂ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₂s ht₂t hCst hCst₂
  have hC₁stab : C₁.mulStab = H₁ := mulStab_union hs₁ne ht₁ne hab hCst₁
  have hH₁H : H₁ ⊂ H := mulStab_mul_ssubset_mulStab hs₁ne ht₁ne hab
  have aux1₁ :=
    mul_aux1 (ih _ _ hst₁) hCcard
      (not_le.1 fun h => hCmin _ (hC₁stab.trans_ssubset hH₁H) ⟨hC₁st, h⟩) hC₁stab hCst₁
  obtain ht₂ | ht₂ne := t₂.eq_empty_or_nonempty
  · have aux₁_contr :=
      disjoint_mul_sub_card_le b (hs₁s has₁) (disjoint_iff_inter_eq_empty.2 ht₂) hH₁H.subset
    linarith [aux1₁, aux₁_contr, Int.natCast_nonneg #(t₁ * (s₁ * t₁).mulStab)]
  obtain hs₂ | hs₂ne := s₂.eq_empty_or_nonempty
  · have aux1₁_contr :
      (#C.mulStab : ℤ) - #(t₁ * (s₁ * t₁).mulStab) ≤
        #((s ∪ t) * C.mulStab) - #((s ∪ t) * (s₁ * t₁).mulStab) := by
      simpa [union_comm, mul_comm s₁ t₁] using
        disjoint_mul_sub_card_le a (ht₁t hbt₁) (disjoint_iff_inter_eq_empty.2 hs₂)
          (by rw [mul_comm]; exact hH₁H.subset)
    linarith [aux1₁, aux1₁_contr, Int.natCast_nonneg #(s₁ * (s₁ * t₁).mulStab)]
  have hC₂stab : C₂.mulStab = H₂ := mulStab_union hs₂ne ht₂ne (by rwa [mul_comm]) hCst₂
  have hH₂H : H₂ ⊂ H := mulStab_mul_ssubset_mulStab hs₂ne ht₂ne (by rwa [mul_comm])
  have aux1₂ :=
    mul_aux1 (ih _ _ hst₂) hCcard
      (not_le.1 fun h => hCmin _ (hC₂stab.trans_ssubset hH₂H) ⟨hC₂st, h⟩) hC₂stab hCst₂
  obtain habH | habH := eq_or_ne (a • H) (b • H)
  · rw [hH₁, hs₁, ht₁, ← habH, hH] at hH₁H
    refine aux1₁.not_ge ?_
    simp only [hs₁, ht₁, ← habH, inter_mul_sub_card_le (hs₁s has₁) hH₁H.subset, H]
  -- temporarily skipping deduction of inequality (2)
  set S := a • H \ (s₁ ∪ t₂) with hS
  set T := b • H \ (s₂ ∪ t₁) with hT
  have hST : Disjoint S T :=
    (C.pairwiseDisjoint_smul_finset_mulStab (Set.mem_range_self _) (Set.mem_range_self _)
          habH).mono
      sdiff_le sdiff_le
  have hSst : S ⊆ a • H \ (s ∪ t) := by
    simp only [hS, hs₁, ht₂, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hTst : T ⊆ b • H \ (s ∪ t) := by
    simp only [hT, hs₂, ht₁, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hSTst : Disjoint (S ∪ T) (s ∪ t) := (subset_sdiff.1 hSst).2.sup_left (subset_sdiff.1 hTst).2
  have hstconv : s * t ∉ convergent := by
    apply hCmin (s * t)
    rw [hstab]
    refine (hC.mulStab_nontrivial.mp hCstab).symm.ssubset_of_subset ?_
    simp only [one_subset, one_mem_mulStab, hC]
  simp only [Set.mem_ofPred_eq, Subset.rfl, true_and, not_le, hstab, mul_one, card_one,
    convergent] at hstconv
  zify at hstconv
  have hSTcard : (#S : ℤ) + #T + #(s ∪ t) ≤ #((s ∪ t) * H) := by
    norm_cast
    conv_lhs => rw [← card_union_of_disjoint hST, ← card_union_of_disjoint hSTst, ← mul_one (s ∪ t)]
    refine card_le_card
      (union_subset (union_subset ?_ ?_) <| mul_subset_mul_left <| one_subset.2 (one_mem_mulStab.mpr hC))
    · exact hSst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_left _ ha)
    · exact hTst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_right _ hb)
  have hH₁ne : H₁.Nonempty := (hs₁ne.mul ht₁ne).mulStab
  have hH₂ne : H₂.Nonempty := (hs₂ne.mul ht₂ne).mulStab
  -- Now we prove inequality (2)
  have aux2₁ : (#s₁ : ℤ) + #t₁ + #H₁ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₁H.subset).trans_lt aux1₁) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₁ne.mul ht₁ne) hH₁H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    gcongr _ - (Nat.cast ?_ + Nat.cast ?_) <;> exact card_le_card_mul_right hH₁ne
  have aux2₂ : (#s₂ : ℤ) + #t₂ + #H₂ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₂H.subset).trans_lt aux1₂) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₂ne.mul ht₂ne) hH₂H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    exact sub_le_sub_left (add_le_add (Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) <|
      Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) _
  -- Now we deduce inequality (3) using the above lemma in addition to the facts that `s * t` is not
  -- convergent and then induction hypothesis applied to `sᵢ` and `tᵢ`
  have aux3₁ : (#S : ℤ) + #T + #s₁ + #t₁ - #H₁ < #H :=
    calc
      (#S : ℤ) + #T + #s₁ + #t₁ - #H₁
        < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₁ * t₁) := by
        have ih₁ :=
          (add_le_add (card_le_card_mul_right hH₁ne) <| card_le_card_mul_right hH₁ne).trans
            (ih _ _ hst₁)
        zify at ih₁
        linarith [hstconv, ih₁]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₁ * t₁) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₁] using card_le_card hC₁st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux3₂ : (#S : ℤ) + #T + #s₂ + #t₂ - #H₂ < #H :=
    calc
      (#S : ℤ) + #T + #s₂ + #t₂ - #H₂
       < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₂ * t₂) := by
        have ih₂ :=
          (add_le_add (card_le_card_mul_right hH₂ne) <| card_le_card_mul_right hH₂ne).trans
            (ih _ _ hst₂)
        zify at hstconv ih₂
        linarith [ih₂]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₂ * t₂) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₂] using card_le_card hC₂st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux4₁ : #H ≤ #S + (#s₁ + #t₂) := by
    grw [← card_smul_finset a H, card_le_card_sdiff_add_card, card_union_le]
  have aux4₂ : #H ≤ #T + (#s₂ + #t₁) := by
    grw [← card_smul_finset b H, card_le_card_sdiff_add_card, card_union_le]
  linarith [aux2₁, aux2₂, aux3₁, aux3₂, aux4₁, aux4₂]

/-- The strict version of **Kneser's multiplication theorem**. If the LHS of `Finset.mul_kneser`
does not equal the RHS, then it is in fact much smaller. -/

lemma mul_strict_kneser (h : #(s * (s * t).mulStab) + #(t * (s * t).mulStab) <
      #(s * t) + #(s * t).mulStab) :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab) ≤ #(s * t) :=
  Nat.le_of_lt_add_of_dvd h
      ((card_mulStab_dvd_card_mul_mulStab _ _).add <| card_mulStab_dvd_card_mul_mulStab _ _) <|
    card_mulStab_dvd_card _

end Finset
namespace Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The translation stabilizer of a finite set. For the empty set this
finite-set convention returns the empty set as well. -/
def addStab (s : Finset G) : Finset G :=
  @mulStab (Multiplicative G) _ _ s

lemma mem_addStab {s : Finset G} {x : G} (hs : s.Nonempty) :
    x ∈ s.addStab ↔ x +ᵥ s = s :=
  @mem_mulStab (Multiplicative G) _ _ s x hs

theorem add_kneser (s t : Finset G) :
    (s + (s + t).addStab).card + (t + (s + t).addStab).card ≤
      (s + t).card + (s + t).addStab.card :=
  @mul_kneser (Multiplicative G) _ _ s t

end Finset

/-
License supplied with the adapted Bakšys–Dillies files.

Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

end

section

open scoped Pointwise

namespace Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma coe_addStab {s : Finset G} (hs : s.Nonempty) :
    (s.addStab : Set G) = AddAction.stabilizer G (s : Set G) :=
  @coe_mulStab (Multiplicative G) _ _ s hs

lemma zero_mem_addStab {s : Finset G} : (0 : G) ∈ s.addStab ↔ s.Nonempty :=
  @one_mem_mulStab (Multiplicative G) _ _ s

lemma add_addStab (s : Finset G) : s + s.addStab = s :=
  @mul_mulStab (Multiplicative G) _ _ s

lemma addStab_add_addStab (s : Finset G) : s.addStab + s.addStab = s.addStab :=
  @mulStab_mul_mulStab (Multiplicative G) _ _ s

lemma subset_addStab_add_left {s t : Finset G} (ht : t.Nonempty) :
    s.addStab ⊆ (s + t).addStab :=
  @subset_mulStab_mul_left (Multiplicative G) _ _ s t ht

/-- Growth of iterated sums, with the defect measured by the stabilizer of the final sum. -/
lemma card_nsmul_bound {r : ℕ} (hr : 0 < r) (B : Finset G) (hB : B.Nonempty) :
    r * B.card ≤ (r • B).card + (r - 1) * (r • B).addStab.card := by
  have aux (j : ℕ) (hj : j + 1 ≤ r) :
      (j + 1) * B.card ≤ ((j + 1) • B).card + j * (r • B).addStab.card := by
    induction j with
    | zero => simp
    | succ j ih =>
      let T := (j + 1) • B
      let S := (j + 2) • B
      have hT : T.Nonempty := hB.nsmul
      have hS : S.Nonempty := hB.nsmul
      have hS' : T + B = S := (succ_nsmul B (j + 1)).symm
      have zeroS : 0 ∈ S.addStab := zero_mem_addStab.mpr hS
      have hsmall : T.card + B.card ≤ S.card + S.addStab.card := by
        have kn := add_kneser T B
        rw [hS'] at kn
        exact (Nat.add_le_add (card_le_card (subset_add_left T zeroS))
          (card_le_card (subset_add_left B zeroS))).trans kn
      have hnum : j + 2 + (r - (j + 2)) = r := by omega
      have subset : S.addStab ⊆ (r • B).addStab := by
        have hne : ((r - (j + 2)) • B).Nonempty := hB.nsmul
        have h := subset_addStab_add_left (s := S) hne
        simpa only [S, ← add_nsmul, hnum] using h
      have hcard := card_le_card subset
      have ind := ih (by omega)
      change (j + 1) * B.card ≤ T.card + j * (r • B).addStab.card at ind
      change (j + 2) * B.card ≤ S.card + (j + 1) * (r • B).addStab.card
      nlinarith only [hsmall, hcard, ind]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simpa using aux j le_rfl

/-- The r-fold Kneser inequality for the stabilizer of the final sumset. -/
lemma card_nsmul_addStab_bound {r : ℕ} (hr : 0 < r) (B : Finset G) (hB : B.Nonempty) :
    r * (B + (r • B).addStab).card ≤ (r • B).card + (r - 1) * (r • B).addStab.card := by
  let H := (r • B).addStab
  have hH : H.Nonempty := ⟨0, zero_mem_addStab.mpr hB.nsmul⟩
  have hidem : H + H = H := addStab_add_addStab _
  have powH (j : ℕ) : (j + 1) • H = H := by
    induction j with
    | zero => exact one_nsmul H
    | succ j ih => rw [succ_nsmul, ih, hidem]
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hrH : r • H = H := hj ▸ powH j
  have heq : r • (B + H) = r • B := by rw [nsmul_add, hrH]; exact add_addStab _
  simpa only [heq] using card_nsmul_bound hr (B + H) (hB.add hH)

end Finset

end

section

/- 
# Fully occupied residue classes across several layers

If all J lifts of each offset occur in A, then a forbidden relation with
multiplier at most Jr among those offsets lifts to a forbidden relation in A.
The count at the end records the cost of a missing lift in each remaining class.
-/

namespace FullColumns

open Finset

def Free (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬ a ∣ ∑ i, b i

lemma allocate (n c k : ℕ) (bound : k ≤ n * c) :
    ∃ t : Fin n → ℕ, (∀ i, t i ≤ c) ∧ ∑ i, t i = k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa using bound
    exact ⟨fun _ => 0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    obtain ⟨f, hf, hsum⟩ := ih (k - min k c) (by rw [Nat.succ_mul] at bound; omega)
    refine ⟨Fin.cons (min k c) f, Fin.forall_fin_succ.mpr ⟨by simp, by simpa using hf⟩, ?_⟩
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum]
    omega

lemma lift_forbidden {A P : Finset ℕ} {a J r : ℕ} (hJ : 0 < J)
    (allLifts : ∀ u ∈ P, ∀ i ∈ Icc 1 J, i * a + u ∈ A) (free : Free r A)
    {u k : ℕ} (hu : u ∈ P) (b : Fin r → ℕ) (hb : ∀ i, b i ∈ P)
    (hlt : ∀ i, u < b i) (lower : r ≤ k) (upper : k ≤ r * J) :
    ∑ i, b i ≠ k * u := by
  intro hsum
  have cap : k - r ≤ r * (J - 1) := by
    rw [Nat.mul_sub, Nat.mul_one]
    omega
  obtain ⟨t, ht, heq⟩ := allocate r (J - 1) (k - r) cap
  let b' (i : Fin r) := (t i + 1) * a + b i
  have hu' : a + u ∈ A := by simpa using allLifts u hu 1 (mem_Icc.mpr ⟨le_rfl, hJ⟩)
  apply free (a + u) hu' b'
  · intro i
    exact allLifts _ (hb i) _ (mem_Icc.mpr ⟨by omega, by have := ht i; omega⟩)
  · intro i
    dsimp [b']
    rw [Nat.succ_mul]
    have := hlt i
    omega
  · refine ⟨k, ?_⟩
    simp only [b', Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one, heq, hsum]
    rw [Nat.sub_add_cancel lower]
    ring

lemma free_shell {A P : Finset ℕ} {a J r : ℕ} (hJ : 0 < J)
    (allLifts : ∀ u ∈ P, ∀ i ∈ Icc 1 J, i * a + u ∈ A)
    (free : Free r A) (X : ℕ) : Free r (P.filter fun x => x ≤ X ∧ X < J*x) := by
  intro u hu b hb hlt hdiv
  obtain ⟨huP, huX, hJu⟩ := mem_filter.mp hu
  have hpos : 0 < u := by by_contra! hn; simp [show u = 0 by omega] at hJu
  obtain ⟨k, hk⟩ := hdiv
  have hlow : r*u ≤ ∑ i, b i := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin r)))
      (f := fun _ => u) (g := b) (fun i _ => (hlt i).le)
  have hhigh : ∑ i, b i ≤ r*(J*u) := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin r)))
      (f := b) (g := fun _ => J*u) (fun i _ => (mem_filter.mp (hb i)).2.1.trans hJu.le)
  rw [hk, mul_comm u k] at hlow hhigh
  exact lift_forbidden hJ allLifts free huP b (fun i => (mem_filter.mp (hb i)).1) hlt
    (Nat.le_of_mul_le_mul_right hlow hpos) (Nat.le_of_mul_le_mul_right (by
      rwa [Nat.mul_assoc] : k*u ≤ r*J*u) hpos) (by simpa [Nat.mul_comm] using hk)

/-- Integer rounding lets the permitted shell extend below X/J. -/
lemma free_wide_shell {A P : Finset ℕ} {a J r : ℕ} (hJ : 0 < J)
    (allLifts : ∀ u ∈ P, ∀ i ∈ Icc 1 J, i * a + u ∈ A)
    (free : Free r A) (X : ℕ) :
    Free r (P.filter fun x => x ≤ X ∧ r * X < (r * J + 1) * x) := by
  intro u hu b hb hlt hdiv
  obtain ⟨huP, huX, hJu⟩ := mem_filter.mp hu
  have hpos : 0 < u := by by_contra! hn; simp [show u = 0 by omega] at hJu
  obtain ⟨k, hk⟩ := hdiv
  have hlow : r * u ≤ ∑ i, b i := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin r)))
      (f := fun _ => u) (g := b) (fun i _ => (hlt i).le)
  have hhigh : ∑ i, b i ≤ r * X := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin r)))
      (f := b) (g := fun _ => X) (fun i _ => (mem_filter.mp (hb i)).2.1)
  rw [hk, mul_comm u k] at hlow hhigh
  have upper : k ≤ r * J := by
    by_contra! big
    have := Nat.mul_le_mul_right u (show r * J + 1 ≤ k by omega)
    omega
  exact lift_forbidden hJ allLifts free huP b (fun i => (mem_filter.mp (hb i)).1) hlt
    (Nat.le_of_mul_le_mul_right hlow hpos) upper (by simpa [Nat.mul_comm] using hk)

def complete (B : Finset ℕ) (a J : ℕ) : Finset ℕ :=
  (B.image (· % a)).filter fun u => ∀ k ∈ Icc 1 J, k * a + u ∈ B

lemma card_bound {B : Finset ℕ} {a J : ℕ} (hj : 0 < J)
    (layers : ∀ b ∈ B, b / a ∈ Icc 1 J) :
    B.card ≤ (J-1) * (B.image (· % a)).card + (complete B a J).card := by
  classical
  let R := B.image (· % a)
  let S (u : ℕ) := (Icc 1 J).filter fun i => i*a+u ∈ B
  have hi (u : ℕ) : (B.filter (fun b => b%a=u)).card ≤ (S u).card := by
    apply card_le_card_of_injOn (fun b => b/a)
    · intro x hx
      obtain ⟨hxB, hmod⟩ := mem_filter.mp hx
      apply mem_filter.mpr
      exact ⟨layers x hxB, by simpa [← hmod, Nat.div_add_mod'] using hxB⟩
    · intro x hx y hy he
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      change x/a=y/a at he
      have ex := Nat.div_add_mod x a
      have ey := Nat.div_add_mod y a
      rw [he, hx'] at ex
      rw [hy'] at ey
      omega
  have each (u) (hu : u ∈ R) :
      (B.filter (fun b => b%a=u)).card ≤ (J-1) + (if u ∈ complete B a J then 1 else 0) := by
    have sub : S u ⊆ Icc 1 J := filter_subset _ _
    have sizeI : (Icc 1 J).card = J := by simp
    have hsize := card_le_card sub
    have hfiber := hi u
    split_ifs with full
    · omega
    · have hne : S u ≠ Icc 1 J := by
        intro hEq
        apply full
        apply mem_filter.mpr
        refine ⟨hu, fun k hk => ?_⟩
        rw [← hEq] at hk
        exact (mem_filter.mp hk).2
      have := card_lt_card (ssubset_of_subset_of_ne sub hne)
      omega
  have sum := Finset.sum_le_sum each
  rw [← card_eq_sum_card_image] at sum
  have hsub : complete B a J ⊆ R := filter_subset _ _
  simpa [sum_add_distrib, Nat.mul_comm, inter_eq_right.mpr hsub] using sum

end FullColumns

end

section

/-  The Scherk–Kemperman bound for a uniquely represented zero and its application
to tuples of every arity up to a fixed number. -/
namespace OMA.Erdos13StrongResidues
open Finset
open scoped Pointwise

lemma unique_zero_sumset {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) (x0 : 0∈X) (y0 : 0∈Y)
    (unique : ∀ x∈X, ∀ y∈Y, x+y=0 → x=0) :
    X.card+Y.card ≤ (X+Y).card+1 := by
  classical
  let H := (X+Y).addStab
  have ne := (show X.Nonempty from ⟨0,x0⟩).add (show Y.Nonempty from ⟨0,y0⟩)
  have h0 : 0∈H := (mem_addStab ne).mpr (by simp)
  have hneg (h : G) (hh : h∈H) : -h∈H := by
    apply (mem_addStab ne).mpr
    have e := (mem_addStab ne).mp hh
    calc -h +ᵥ (X+Y) = -h +ᵥ (h +ᵥ (X+Y)) := congrArg (-h +ᵥ ·) e.symm
         _ = X+Y := by rw [←add_vadd]; simp
  have xsub : X ⊆ X+H := fun x hx => by simpa using add_mem_add hx h0
  have ysub : Y ⊆ Y+H := fun y hy => by simpa using add_mem_add hy h0
  let L := (H.erase 0).filter (·∉X)
  let R := (H.erase 0).filter (fun x => ¬x∉X)
  have left : L ⊆ (X+H)\X := by
    intro x hx
    obtain ⟨hm,hn⟩ := mem_filter.mp hx
    exact mem_sdiff.mpr ⟨by simpa using add_mem_add x0 (mem_erase.mp hm).2,hn⟩
  have right : R.card ≤ ((Y+H)\Y).card := by
    apply card_le_card_of_injOn (fun h : G => -h)
    · intro h hh
      obtain ⟨hm,hn⟩ := mem_filter.mp hh
      obtain ⟨nz,hi⟩ := mem_erase.mp hm
      refine mem_sdiff.mpr ⟨by simpa using add_mem_add y0 (hneg h hi),?_⟩
      intro hy
      exact nz (unique h (by simpa using hn) (-h) hy (by simp))
    · intro a _ b _ eq
      exact neg_injective eq
  have part : L.card+R.card=(H.erase 0).card := (H.erase 0).card_filter_add_card_filter_not (·∉X)
  have erase := card_erase_add_one h0
  have xc := card_sdiff_add_card_eq_card xsub
  have yc := card_sdiff_add_card_eq_card ysub
  have kn := add_kneser X Y
  change (X+H).card+(Y+H).card ≤ (X+Y).card+H.card at kn
  have lc := card_le_card left
  omega

lemma some_nonzero_summands {G : Type*} [AddCommGroup G] [DecidableEq G]
    (R : Finset G) (n : ℕ) {x : G} (hx : x∈n • (insert 0 R)) :
    ∃ j≤n, x∈j • R := by
  induction n generalizing x with
  | zero => exact ⟨0,le_rfl,by simpa using hx⟩
  | succ n ih =>
    rw [succ_nsmul] at hx
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_add.mp hx
    obtain ⟨j,hj,uj⟩ := ih hu
    rcases mem_insert.mp hv with rfl|vr
    · exact ⟨j,by omega,by simpa using uj⟩
    · exact ⟨j+1,by omega,by rw [succ_nsmul]; exact add_mem_add uj vr⟩

/-- Each available summand increases the size of the partial sumset by at
least the number of available nonzero residues. -/
lemma growth_without_short_zero {G : Type*} [AddCommGroup G] [DecidableEq G]
    (R : Finset G) {r : ℕ} (hr : 0<r)
    (avoid : ∀ j, 0<j → j≤r → (0:G)∉j • R) :
    r*R.card+1 ≤ (r • insert 0 R).card := by
  classical
  have no : (0:G)∉R := by simpa using avoid 1 (by decide) hr
  have step (n : ℕ) (nr : n≤r) : n*R.card+1 ≤ (n • insert 0 R).card := by
    induction n with
    | zero => simp
    | succ n ih =>
      have prev := ih (by omega)
      let X := n • insert 0 R
      let Y := insert 0 R
      have yz : (0:G)∈Y := mem_insert_self _ _
      have xz : (0:G)∈X := by simpa using (nsmul_mem_nsmul (n:=n) yz)
      have unique (x) (hx : x∈X) (y) (hy : y∈Y) (eq : x+y=0) : x=0 := by
        rcases mem_insert.mp hy with rfl|hy
        · simpa using eq
        obtain ⟨j,hj,jx⟩ := some_nonzero_summands R n hx
        exact False.elim (avoid (j+1) (by omega) (by omega) (by rw [succ_nsmul,←eq]; exact add_mem_add jx hy))
      have up := unique_zero_sumset X Y xz yz unique
      change (n • insert 0 R).card+(insert 0 R).card≤((n • insert 0 R)+insert 0 R).card+1 at up
      rw [card_insert_of_notMem no] at up
      rw [succ_nsmul,Nat.succ_mul]
      omega
  exact step r le_rfl

lemma original_residue_bound {r a : ℕ} (hr : 0<r) (ha : 0<a) (R : Finset (ZMod a))
    (avoid : ∀ j, 0<j → j≤r → (0:ZMod a)∉j • R) : r*R.card+1≤a := by
  let : NeZero a := ⟨ha.ne'⟩
  exact (growth_without_short_zero R hr avoid).trans (by simpa using (r • insert 0 R).card_le_univ)

/-- After all shorter forbidden sums are removed, the bound applies modulo a
itself at each retained base, with no period error. -/
theorem tail_bound {r a : ℕ} {A : Finset ℕ} (hr : 0<r) (ha : 0<a) (hain : a∈A)
    (strong : ∀ j, 0<j → j≤r → FullColumns.Free j A) :
    r*((A.filter (a<·)).image (·%a)).card+1 ≤ a := by
  let : NeZero a := ⟨ha.ne'⟩
  let B := A.filter (a<·)
  let R := B.image (fun b : ℕ => (b : ZMod a))
  have gap (j) (pos : 0<j) (small : j≤r) : (0:ZMod a)∉ j • R := by
    intro hz
    obtain ⟨f,hf⟩ := mem_nsmul.mp hz
    have pre (i) : ∃ b∈B,(b : ZMod a)= f i := mem_image.mp (f i).property
    choose b hb eq using pre
    apply strong j pos small a hain b (fun i => (mem_filter.mp (hb i)).1) (fun i => (mem_filter.mp (hb i)).2)
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_sum,eq,List.sum_ofFn] using hf
  have h := original_residue_bound hr ha R gap
  have eq : R.image ZMod.val = B.image (·%a) := by
    dsimp [R]
    rw [image_image]
    exact image_congr fun x _ => ZMod.val_natCast a x
  have card : (B.image (·%a)).card=R.card := eq ▸ card_image_of_injective _ (ZMod.val_injective a)
  change r*(B.image (·%a)).card+1≤a
  simpa only [card] using h

end OMA.Erdos13StrongResidues

end

section

/-  One more row gives a reserved multiple for all arities at least four. -/
namespace Erdos13ExtraRow
open Finset FullColumns

def full (r : ℕ) (A : Finset ℕ) (a x : ℕ) :=
  ∀ i∈Icc 1 (r+1),i*a+x∈A
def almost (r : ℕ) (A : Finset ℕ) (a x : ℕ) :=
  ∃ m : ℕ,∀ i∈Icc 1 (r+1),i≠m → i*a+x∈A

theorem small_multiple {r n a x : ℕ} {A : Finset ℕ} (hr : 4≤r)
    (np : 0<n) (nr : n≤r) (xp : 0<x) (xs : (4*r-1)*x<a) (fx : full r A a x)
    (free : Free r A) (y : Fin n → ℕ) (ya : ∀ i,y i<a) (hy : ∀ i,almost r A a (y i)) :
    ¬(∑ i,y i) ≡ (4*r-1)*x [MOD a] := by
  classical
  intro rel
  let k := 4*r-1
  let p := (univ.filter fun i=>x<y i).card
  have upper : (∑ i,y i)<k*x+p*a := by
    have pt (i : Fin n) : y i≤(if x<y i then a else 0)+x := by
      have yi := ya i
      split <;> omega
    have lim := sum_le_sum fun i (_ : i∈(univ : Finset (Fin n)))=>pt i
    simp only [sum_add_distrib,sum_ite,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at lim
    change (∑ i,y i)≤p*a+n*x at lim
    have diff := Nat.mul_lt_mul_of_pos_right (show n<k by dsimp [k]; omega) xp
    omega
  let c := (∑ i,y i)/a
  have eq : c*a+k*x=∑ i,y i := by
    have h := Nat.div_add_mod (∑ i,y i) a
    rw [show (∑ i,y i)%a=k*x from Eq.trans rel (Nat.mod_eq_of_lt xs)] at h
    simpa only [c,Nat.mul_comm a] using h
  have pc := Nat.lt_of_mul_lt_mul_right (show c*a<p*a by omega)
  have pn : p≤n := by simpa [p] using card_filter_le (s:=(univ : Finset (Fin n))) (fun i=>x<y i)
  let l := r-n
  have nl : n+l=r := Nat.add_sub_of_le nr
  choose m hm using hy
  let masks : Fin (n+l) → ℕ := Fin.append m (fun _ : Fin l=>r+1)
  have square := Nat.mul_le_mul_right r hr
  obtain ⟨v,hv,tot⟩ := central_heights hr (n:=n+l) (by omega) masks (k-c)
    (by dsimp [k]; omega) (by rw [nl]; exact ((Nat.sub_le k c).trans (Nat.sub_le (4*r) 1)).trans square)
  let b (i : Fin n) := v (Fin.castAdd l i)
  let e (i : Fin l) := v (Fin.natAdd n i)
  have hb (i : Fin n) : 2≤b i ∧ b i≤r+1 ∧ b i≠m i := by simpa [b,masks] using hv (Fin.castAdd l i)
  have he (i : Fin l) : 2≤e i ∧ e i≤r := by
    have h : 2≤e i ∧ e i≤r+1 ∧ e i≠r+1 := by simpa [e,masks] using hv (Fin.natAdd n i)
    omega
  have sum : (∑ i,b i)+(∑ i,e i)+c=k := by
    have s : (∑ i,b i)+(∑ i,e i)=k-c := by simpa only [Fin.sum_univ_add,b,e] using tot
    dsimp [k] at *
    omega
  let Y (i : Fin n) := b i*a+y i
  let E (i : Fin l) := (e i+1)*a+x
  let f := Fin.append Y E
  have base := fx 1 (mem_Icc.mpr ⟨le_rfl,by omega⟩)
  rw [Nat.one_mul] at base
  have occ (i) : f i∈A := Fin.addCases
    (fun j=>by simpa [f,Y] using hm j (b j) (mem_Icc.mpr ⟨(by have := (hb j).1; omega),(hb j).2.1⟩) (hb j).2.2)
    (fun j=>by simpa [f,E] using fx (e j+1) (mem_Icc.mpr ⟨by omega,by have := (he j).2; omega⟩)) i
  have xa : x<a := by have := Nat.le_mul_of_pos_left x (show 0<4*r-1 by omega); omega
  have bl (i : Fin n) : a+x<Y i := by
    have le := Nat.mul_le_mul_right a (hb i).1
    dsimp [Y]; omega
  have el (i : Fin l) : a+x<E i := by
    have le := Nat.mul_le_mul_right a (he i).1
    dsimp [E]; rw [Nat.add_mul,Nat.one_mul]; omega
  have big (i) : a+x<f i := Fin.addCases (fun j=>by simpa [f] using bl j) (fun j=>by simpa [f] using el j) i
  have fn : Free (n+l) A := by rw [nl]; exact free
  apply fn _ base f occ big
  refine ⟨k+l,?_⟩
  have scale := congrArg (·*a) sum
  simp only [Nat.add_mul] at scale
  simp [f,Fin.sum_univ_add,Y,E,sum_add_distrib,←sum_mul,Nat.add_mul]
  nlinarith only [scale,eq]

end Erdos13ExtraRow

end

section

/-  # A cyclic quotient obstruction for a forbidden iterated sum -/

namespace OMA.Erdos13Cyclic

open Finset
open scoped Pointwise

lemma quotient_periods {G : Type} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (hne : S.Nonempty) :
    let H := AddAction.stabilizer G (S : Set G)
    let p := QuotientAddGroup.mk' H
    ∀ (q : G ⧸ H), q ∈ (S.image p).addStab ↔ q = 0 := by
  classical
  intro H p
  have fix (x : G) : x ∈ H ↔ x +ᵥ S = S := by
    change x ∈ AddAction.stabilizer G (S : Set G) ↔ _
    rw [AddAction.mem_stabilizer_iff, ← Finset.coe_vadd_finset, Finset.coe_inj]
  have saturated (z : G) : p z ∈ S.image p ↔ z ∈ S := by
    constructor
    · intro hz
      obtain ⟨y, hy, heq⟩ := mem_image.mp hz
      have hmem : z - y ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp heq.symm
      have hz' := vadd_mem_vadd_finset (a := z - y) hy
      rw [(fix _).mp hmem] at hz'
      simpa [vadd_eq_add] using hz'
    · exact mem_image_of_mem _
  intro q
  rw [Finset.mem_addStab (hne.image _)]
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H q
    apply (QuotientAddGroup.eq_zero_iff x).mpr
    apply (fix x).mpr
    apply Finset.eq_of_subset_of_card_le _ (by simp)
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_vadd_finset.mp hz
    apply (saturated _).mp
    have h := vadd_mem_vadd_finset (a := p x) (mem_image_of_mem p hy)
    rw [hq] at h
    simpa only [vadd_eq_add, map_add] using h
  · rintro rfl
    simp

theorem quotient_witness {r a : ℕ} (hr : 2 ≤ r) (ha : 0 < a)
    (T : Finset ℕ) (hT : T.Nonempty)
    (free : ∀ b : Fin r → ℕ, (∀ i, b i ∈ T) → ¬ a ∣ ∑ i, b i) :
    ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ T, ¬ d ∣ b) ∧
      r * (T.image (fun x => x % d)).card ≤ d + r - 2 := by
  classical
  let : NeZero a := ⟨ha.ne'⟩
  let B := T.image (fun x : ℕ => (x : ZMod a))
  let S := r • B
  have hB : B.Nonempty := hT.image _
  have hS : S.Nonempty := hB.nsmul
  have hz : (0 : ZMod a) ∉ S := by
    intro h
    obtain ⟨f, hf⟩ := Finset.mem_nsmul.mp h
    have chooseNat (i : Fin r) : ∃ x ∈ T, (x : ZMod a) = (f i : ZMod a) :=
      mem_image.mp (f i).property
    choose b hb he using chooseNat
    apply free b hb
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sum]
    simpa only [he, List.sum_ofFn] using hf
  let H := AddAction.stabilizer (ZMod a) (S : Set (ZMod a))
  let Q := ZMod a ⧸ H
  let p := QuotientAddGroup.mk' H
  let C := B.image p
  have pmem (x : ZMod a) (hx : x ∈ H) : x +ᵥ S = S := by
    apply Finset.coe_inj.mp
    rw [Finset.coe_vadd_finset]
    exact AddAction.mem_stabilizer_iff.mp hx
  have mapS : S.image p = r • C := Finset.image_nsmul p B r
  have hzQ : (0 : Q) ∉ r • C := by
    rw [← mapS]
    rintro h
    obtain ⟨y, hy, hyp⟩ := mem_image.mp h
    have hneg := pmem (-y) (H.neg_mem ((QuotientAddGroup.eq_zero_iff y).mp hyp))
    have h0 := vadd_mem_vadd_finset (a := -y) hy
    rw [hneg] at h0
    exact hz (by simpa [vadd_eq_add] using h0)
  have per : (r • C).addStab = {0} := by
    ext q
    rw [← mapS, mem_singleton]
    exact quotient_periods S hS q
  have hC : C.Nonempty := hB.image _
  have estimate := Finset.card_nsmul_bound (r := r) (by omega) C hC
  rw [per] at estimate
  have simplified : r * C.card ≤ (r • C).card + (r - 1) := by
    simpa only [card_singleton, Nat.mul_one] using estimate
  let g : Q := p 1
  let d := addOrderOf g
  have gen (n : ℕ) : p (n : ZMod a) = n • g := by
    change p (n : ZMod a) = n • p 1
    rw [← map_nsmul]
    simp [nsmul_eq_mul]
  let : Fintype Q := Fintype.ofFinite _
  have hd : d = Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    apply addOrderOf_eq_card_of_forall_mem_zmultiples
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective H x
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(z.val : ℤ), ?_⟩
    rw [natCast_zsmul]
    change z.val • g = p z
    rw [← gen, ZMod.natCast_zmod_val]
  have cardIneq := Finset.card_lt_univ_of_notMem hzQ
  have hpos : 0 < d := hd ▸ Fintype.card_pos
  refine ⟨d, hpos, ?_, ?_, ?_⟩
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    simpa using (gen a).symm
  · intro b hb hdvd
    have hzero : p (b : ZMod a) = 0 := (gen b).trans (addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd)
    have hbt : p (b : ZMod a) ∈ C := mem_image_of_mem _ (mem_image_of_mem _ hb)
    rw [hzero] at hbt
    apply hzQ
    simpa using (nsmul_mem_nsmul (n := r) hbt)
  · have conv (n : ℕ) : (n % d) • g = p (n : ZMod a) :=
      (nsmul_eq_nsmul_iff_modEq.mpr (Nat.mod_modEq n d)).trans (gen n).symm
    have imageC : (T.image (fun x => x % d)).image (fun i => i • g) = C := by
      dsimp [C, B]
      rw [Finset.image_image, Finset.image_image]
      exact Finset.image_congr fun n _ => conv n
    have inj : (↑(T.image (fun x => x % d)) : Set ℕ).InjOn (fun i => i • g) := by
      intro x hx y hy hh
      obtain ⟨m, _, rfl⟩ := mem_image.mp hx
      obtain ⟨n, _, rfl⟩ := mem_image.mp hy
      have modEq := nsmul_eq_nsmul_iff_modEq.mp hh
      change m % d % d = n % d % d at modEq
      simpa only [Nat.mod_mod] using modEq
    have hcard := Finset.card_image_of_injOn inj
    rw [imageC] at hcard
    rw [← hcard]
    omega

end OMA.Erdos13Cyclic

end

section

/-  A cyclic quotient estimate for two sets contributing different
multiplicities to a sum that omits zero. -/
namespace OMA.Erdos13Cyclic

open Finset
open scoped Pointwise

/-- Project a missing sum to its aperiodic quotient. A residue present in
both summand sets cannot become zero in that quotient. -/
theorem mixed_quotient_witness {r a : ℕ} (hr : 2 ≤ r) (ha : 0 < a)
    (U V : Finset ℕ) (hU : U.Nonempty) (hV : V.Nonempty)
    (missing : (0 : ZMod a) ∉ (U.image (fun n : ℕ => (n : ZMod a))) +
      (r-1) • (V.image (fun n : ℕ => (n : ZMod a)))) :
    ∃ d : ℕ, 0<d ∧ d∣a ∧ (∀ x ∈ U ∩ V, ¬d∣x) ∧
      (U.image (·%d)).card + (r-1)*(V.image (·%d)).card ≤ d+r-2 := by
  classical
  let : NeZero a := ⟨ha.ne'⟩
  let X := U.image (fun n : ℕ => (n : ZMod a))
  let Y := V.image (fun n : ℕ => (n : ZMod a))
  let S := X + (r-1) • Y
  have xne : X.Nonempty := hU.image _
  have yne : Y.Nonempty := hV.image _
  have sne : S.Nonempty := xne.add yne.nsmul
  change (0 : ZMod a) ∉ S at missing
  let H := AddAction.stabilizer (ZMod a) (S : Set (ZMod a))
  let Q := ZMod a ⧸ H
  let p := QuotientAddGroup.mk' H
  let X' := X.image p
  let Y' := Y.image p
  let S' := X' + (r-1) • Y'
  have mapS : S.image p = S' := by
    dsimp [S,S',X',Y']
    rw [Finset.image_add,Finset.image_nsmul]
  have zeroMissing : (0 : Q) ∉ S' := by
    rw [← mapS]
    rintro h
    obtain ⟨y,hy,hyp⟩ := mem_image.mp h
    have neg : -y ∈ H := H.neg_mem ((QuotientAddGroup.eq_zero_iff y).mp hyp)
    have fixed : (-y) +ᵥ S = S := by
      apply Finset.coe_inj.mp
      rw [Finset.coe_vadd_finset]
      exact AddAction.mem_stabilizer_iff.mp neg
    have h0 := vadd_mem_vadd_finset (a := -y) hy
    rw [fixed] at h0
    exact missing (by simpa [vadd_eq_add] using h0)
  have aper : S'.addStab = {0} := by
    ext q
    rw [← mapS,mem_singleton]
    exact quotient_periods S sne q
  let W := (r-1) • Y'
  have xne' : X'.Nonempty := xne.image _
  have yne' : Y'.Nonempty := yne.image _
  have perW : W.addStab ⊆ S'.addStab := by
    rw [show S'=W+X' from add_comm _ _]
    exact subset_addStab_add_left xne'
  have perCard : W.addStab.card ≤ 1 := by
    simpa [aper] using card_le_card perW
  have iter := Finset.card_nsmul_bound (r := r-1) (by omega) Y' yne'
  change (r-1)*Y'.card ≤ W.card+(r-1-1)*W.addStab.card at iter
  have correction := Nat.mul_le_mul_left (r-1-1) perCard
  have kn := Finset.add_kneser X' W
  change (X'+S'.addStab).card+(W+S'.addStab).card ≤ S'.card+S'.addStab.card at kn
  rw [aper] at kn
  have simple : X'.card+W.card ≤ S'.card+1 := by simpa using kn
  let g : Q := p 1
  let d := addOrderOf g
  have gen (n : ℕ) : p (n : ZMod a) = n • g := by
    change p (n : ZMod a) = n • p 1
    rw [← map_nsmul]
    simp [nsmul_eq_mul]
  let : Fintype Q := Fintype.ofFinite _
  have hd : d = Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    apply addOrderOf_eq_card_of_forall_mem_zmultiples
    intro z
    obtain ⟨y,rfl⟩ := QuotientAddGroup.mk'_surjective H z
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(y.val : ℤ),?_⟩
    rw [natCast_zsmul]
    change y.val • g = p y
    rw [←gen, ZMod.natCast_zmod_val]
  have translate (T : Finset ℕ) :
      (T.image (·%d)).card = ((T.image (fun n : ℕ => (n : ZMod a))).image p).card := by
    have conv (n : ℕ) : (n % d) • g = p (n : ZMod a) :=
      (nsmul_eq_nsmul_iff_modEq.mpr (Nat.mod_modEq n d)).trans (gen n).symm
    have eq : (T.image (·%d)).image (fun i => i • g) =
        (T.image (fun n : ℕ => (n : ZMod a))).image p := by
      rw [Finset.image_image,Finset.image_image]
      exact Finset.image_congr fun n _ => conv n
    have inj : (↑(T.image (·%d)) : Set ℕ).InjOn (fun i => i • g) := by
      intro x hx y hy h
      obtain ⟨m,_,rfl⟩ := mem_image.mp hx
      obtain ⟨n,_,rfl⟩ := mem_image.mp hy
      have modEq := nsmul_eq_nsmul_iff_modEq.mp h
      change m % d % d = n % d % d at modEq
      simpa only [Nat.mod_mod] using modEq
    exact (Finset.card_image_of_injOn inj).symm.trans (congrArg Finset.card eq)
  have proper := Finset.card_lt_univ_of_notMem zeroMissing
  refine ⟨d,hd ▸ Fintype.card_pos,?_,?_,?_⟩
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    simpa using (gen a).symm
  · intro n hn dvd
    have z := (gen n).trans (addOrderOf_dvd_iff_nsmul_eq_zero.mp dvd)
    have x : p (n : ZMod a) ∈ X' := mem_image_of_mem _ (mem_image_of_mem _ (mem_inter.mp hn).1)
    have y : p (n : ZMod a) ∈ Y' := mem_image_of_mem _ (mem_image_of_mem _ (mem_inter.mp hn).2)
    rw [z] at x y
    have w : ((r-1) • (0:Q)) ∈ W := nsmul_mem_nsmul (n := r-1) y
    exact zeroMissing (by simpa using Finset.add_mem_add x w)
  · rw [translate U, translate V]
    change X'.card+(r-1)*Y'.card ≤ d+r-2
    simp only [Nat.mul_one] at correction
    omega

/-- The mixed quotient estimate in terms of integer representatives. -/
theorem mixed_quotient_of_natural_sums {r a : ℕ} (hr : 2 ≤ r) (ha : 0<a)
    (U V : Finset ℕ) (hU : U.Nonempty) (hV : V.Nonempty)
    (free : ∀ x ∈ U, ∀ b : Fin (r-1) → ℕ, (∀ i, b i ∈ V) → ¬a ∣ x+∑ i, b i) :
    ∃ d : ℕ, 0<d ∧ d∣a ∧ (∀ x ∈ U ∩ V, ¬d∣x) ∧
      (U.image (·%d)).card+(r-1)*(V.image (·%d)).card ≤ d+r-2 := by
  classical
  apply mixed_quotient_witness hr ha U V hU hV
  intro h
  obtain ⟨u,hu,v,hv,eq⟩ := Finset.mem_add.mp h
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
  obtain ⟨f,hf⟩ := Finset.mem_nsmul.mp hv
  have rep (i : Fin (r-1)) : ∃ b ∈ V, (b : ZMod a)=(f i : ZMod a) := mem_image.mp (f i).property
  choose b hb he using rep
  apply free x hx b hb
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_add,Nat.cast_sum]
  have e : (∑ i, (b i : ZMod a)) = v := by simpa [he,List.sum_ofFn] using hf
  rwa [e]

end OMA.Erdos13Cyclic

end

section

/-  Complete columns preserve bounded-multiplier admissibility.
Two mixed residue sums at a pivot cannot contain zero. -/

namespace FullColumns
open Finset
open scoped Pointwise

/-- Admissibility for quotients at most r². -/
def Limited (r : ℕ) (P : Finset ℕ) : Prop :=
  ∀ u ∈ P, ∀ b : Fin r → ℕ, (∀ i, b i ∈ P) → (∀ i, u < b i) →
    ∀ k ≤ r*r, (∑ i, b i) ≠ k*u

lemma limited_of_free {r : ℕ} {P : Finset ℕ} (h : Free r P) : Limited r P := by
  intro u hu b hb lt k _ eqn
  exact h u hu b hb lt ⟨k,by simpa [Nat.mul_comm] using eqn⟩

lemma limited_lifts {r a : ℕ} {A P : Finset ℕ} (hr : 0<r)
    (lifts : ∀ x ∈ P, ∀ j ∈ Icc 1 r, j*a+x ∈ A) (lim : Limited r A) :
    Limited r P := by
  intro u hu b hb lt k cap eqn
  have lower : r*u < ∑ i, b i := by
    let i : Fin r := ⟨0,hr⟩
    have h := sum_lt_sum (s := (univ : Finset (Fin r))) (f := fun _ => u) (g := b)
      (fun j _ => (lt j).le) ⟨i,mem_univ _,lt i⟩
    simpa using h
  rw [eqn] at lower
  have rk : r ≤ k := (Nat.lt_of_mul_lt_mul_right lower).le
  have capacity : k-r ≤ r*(r-1) := by rw [Nat.mul_sub,Nat.mul_one]; omega
  obtain ⟨t,ht,hs⟩ := allocate r (r-1) (k-r) capacity
  let b' (i : Fin r) := (t i+1)*a+b i
  have pivot : a+u ∈ A := by simpa using lifts u hu 1 (mem_Icc.mpr ⟨le_rfl,hr⟩)
  refine lim (a+u) pivot b' ?_ ?_ k cap ?_
  · intro i
    exact lifts _ (hb i) _ (mem_Icc.mpr ⟨by omega,by have := ht i; omega⟩)
  · intro i
    dsimp [b']
    rw [Nat.succ_mul]
    have := lt i
    omega
  · simp only [b',sum_add_distrib,←sum_mul,sum_const,card_univ,Fintype.card_fin,
      smul_eq_mul,Nat.mul_one,hs,eqn]
    rw [Nat.sub_add_cancel rk]
    ring

lemma limited_complete {r a : ℕ} {A S : Finset ℕ} (hr : 0<r) (inc : S ⊆ A)
    (lim : Limited r A) : Limited r (complete S a r) :=
  limited_lifts hr (fun _ hx j hj => inc ((mem_filter.mp hx).2 j hj)) lim

lemma limited_free_shell {r D : ℕ} {P Q : Finset ℕ} (inc : Q ⊆ P)
    (upper : ∀ b ∈ Q, b ≤ D) (wide : ∀ u ∈ Q, r*D < (r*r+1)*u)
    (lim : Limited r P) : Free r Q := by
  intro u hu b hb lt div
  obtain ⟨k,hk⟩ := div
  have bsum : ∑ i, b i ≤ r*D := by
    simpa using sum_le_sum (s := (univ : Finset (Fin r))) (f := b) (g := fun _ => D)
      (fun i _ => upper _ (hb i))
  have e : ∑ i, b i = k*u := by simpa only [mul_comm u k] using hk
  have num : k*u < (r*r+1)*u := e ▸ bsum.trans_lt (wide u hu)
  exact lim u (inc hu) b (fun i => inc (hb i)) lt k (by have := Nat.lt_of_mul_lt_mul_right num; omega) e

private lemma limited_mixed_aux {u n : ℕ} {P T V : Finset ℕ} (hu : u ∈ P)
    (ti : ∀ b ∈ T, b ∈ P ∧ u<b) (vi : ∀ b ∈ V, b ∈ P ∧ u<b)
    (bound : ∀ x ∈ T, ∀ b : Fin n → ℕ, (∀ i,b i ∈ V) →
      x+(∑ i,b i) < ((n+1)*(n+1)+1)*u) (lim : Limited (n+1) P) :
    (0 : ZMod u) ∉ T.image (fun x : ℕ => (x : ZMod u)) +
      n • V.image (fun x : ℕ => (x : ZMod u)) := by
  classical
  intro h
  obtain ⟨w,hw,y,hy,eqn⟩ := mem_add.mp h
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
  obtain ⟨f,hf⟩ := Finset.mem_nsmul.mp hy
  have pre (i : Fin n) : ∃ b ∈ V, (b : ZMod u) = (f i : ZMod u) := mem_image.mp (f i).property
  choose b hb he using pre
  have d : u ∣ x+∑ i,b i := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_add,Nat.cast_sum]
    simpa only [he,←List.sum_ofFn,hf] using eqn
  obtain ⟨k,hk⟩ := d
  have e : x+∑ i,b i = k*u := by simpa only [mul_comm u k] using hk
  have small := bound x hx b hb
  rw [e] at small
  have cap : k ≤ (n+1)*(n+1) := by have := Nat.lt_of_mul_lt_mul_right small; omega
  apply lim u hu (Fin.cons x b)
    (Fin.forall_fin_succ.mpr ⟨by simpa using (ti x hx).1,by simpa using fun i => (vi _ (hb i)).1⟩)
    (Fin.forall_fin_succ.mpr ⟨by simpa using (ti x hx).2,by simpa using fun i => (vi _ (hb i)).2⟩) k cap
  simpa [Fin.sum_univ_succ] using e

lemma limited_mixed {r D u : ℕ} {P : Finset ℕ} (hr : 3≤r) (hu : u∈P)
    (_hu0 : 0<u) (cap : D≤(r+1)*u) (within : ∀ b∈P,b≤D) (lim : Limited r P) :
    let S := P.filter (u<·)
    let S1 := S.filter (·<2*u)
    let Sm := S.filter (·<r*u)
    let cast := fun x : ℕ => (x : ZMod u)
    (0 : ZMod u) ∉ S1.image cast + (r-1) • S.image cast ∧
      (0 : ZMod u) ∉ S.image cast + (r-1) • Sm.image cast := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  dsimp only
  simp only [Nat.succ_sub_one]
  constructor
  · apply limited_mixed_aux hu (fun x hx => mem_filter.mp (mem_filter.mp hx).1)
      (fun x hx => mem_filter.mp hx) _ lim
    intro x hx b hb
    have xu := (mem_filter.mp hx).2
    have bs : ∑ i,b i ≤ n*D := by
      simpa using sum_le_sum (s := (univ : Finset (Fin n))) (f := b) (g := fun _ => D)
        (fun i _ => within _ (mem_filter.mp (hb i)).1)
    have up := Nat.mul_le_mul_left n cap
    nlinarith only [xu,bs,up]
  · apply limited_mixed_aux hu (fun x hx => mem_filter.mp hx)
      (fun x hx => mem_filter.mp (mem_filter.mp hx).1) _ lim
    intro x hx b hb
    have xu := within _ (mem_filter.mp hx).1
    have bs : ∑ i,b i < n*((n+1)*u) := by
      let i : Fin n := ⟨0,by omega⟩
      simpa using sum_lt_sum (s := (univ : Finset (Fin n))) (f := b) (g := fun _ => (n+1)*u)
        (fun j _ => (mem_filter.mp (hb j)).2.le) ⟨i,mem_univ _,(mem_filter.mp (hb i)).2⟩
    nlinarith only [xu,bs,cap]

end FullColumns

end

section

/-  The two cyclic obstructions associated with one pivot in the boundary strip. -/
namespace OMA.Erdos13Cyclic

open Finset FullColumns

/-- Both obstructing quotients exclude multiples at every later pivot in the
same strip. The two projected image bounds count different summand sets. -/
theorem mixed_pivot_witnesses {r D u : ℕ} {P : Finset ℕ}
    (hr : 3 ≤ r) (hu : u ∈ P) (pos : 0<u) (cap : D≤(r+1)*u)
    (within : ∀ b ∈ P, b≤D) (lim : Limited r P)
    (near : ((P.filter (u<·)).filter (·<2*u)).Nonempty) :
    let S := P.filter (u<·)
    let S1 := S.filter (·<2*u)
    let Sm := S.filter (·<r*u)
    ∃ d e : ℕ, 0<d ∧ d∣u ∧ 0<e ∧ e∣u ∧
      (∀ b ∈ P, u<b → b<2*u → ¬d∣b) ∧ (∀ b ∈ P, u<b → b<2*u → ¬e∣b) ∧
      (S1.image (·%d)).card + (r-1)*(S.image (·%d)).card ≤ d+r-2 ∧
      (S.image (·%e)).card + (r-1)*(Sm.image (·%e)).card ≤ e+r-2 := by
  classical
  let S := P.filter (u<·)
  let S1 := S.filter (·<2*u)
  let Sm := S.filter (·<r*u)
  have sn : S1.Nonempty := near
  have incS : S1 ⊆ S := filter_subset _ _
  have ru := Nat.mul_le_mul_right u (show 2 ≤ r by omega)
  have incM : S1 ⊆ Sm := by
    intro b hb
    have h := mem_filter.mp hb
    exact mem_filter.mpr ⟨h.1,lt_of_lt_of_le h.2 ru⟩
  have missing := limited_mixed hr hu pos cap within lim
  obtain ⟨d,dp,du,dex,dcount⟩ :=
    mixed_quotient_witness (by omega : 2≤r) pos S1 S sn (sn.mono incS) missing.1
  obtain ⟨e,ep,eu,eex,ecount⟩ :=
    mixed_quotient_witness (by omega : 2≤r) pos S Sm (sn.mono incS) (sn.mono incM) missing.2
  have low (b) (hb : b∈P) (lt : u<b) (small : b<2*u) : b ∈ S1 :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hb,lt⟩,small⟩
  dsimp only
  refine ⟨d,e,dp,du,ep,eu,?_,?_,dcount,ecount⟩
  · intro b hb later small
    have mem := low b hb later small
    exact dex b (mem_inter.mpr ⟨mem,incS mem⟩)
  · intro b hb later small
    have mem := low b hb later small
    exact eex b (mem_inter.mpr ⟨incS mem,incM mem⟩)

end OMA.Erdos13Cyclic


namespace OMA.Erdos13Mixed
open Finset

/-- The two large-quotient cardinal bounds for one pivot. -/
def Pair (r D u : ℕ) (P : Finset ℕ) : Prop :=
  let S := P.filter (u<·)
  let S1 := S.filter (·<2*u)
  let Sm := S.filter (·<r*u)
  ∃ d e : ℕ, D.sqrt < d ∧ d∣u ∧ D.sqrt < e ∧ e∣u ∧
    (S1.image (·%d)).card+(r-1)*(S.image (·%d)).card ≤ d+r-2 ∧
    (S.image (·%e)).card+(r-1)*(Sm.image (·%e)).card ≤ e+r-2

theorem pair_or_small {r D u : ℕ} {P : Finset ℕ} (hr : 3≤r) (hu : u∈P) (hu0 : 0<u)
    (cap : D≤(r+1)*u) (within : ∀ b ∈ P, b≤D) (lim : FullColumns.Limited r P)
    (hne : ((P.filter (u<·)).filter (·<2*u)).Nonempty) :
    Pair r D u P ∨ ∃ d, 0<d ∧ d≤D.sqrt ∧ d∣u ∧ ∀ v∈P, u<v → v<2*u → ¬d∣v := by
  obtain ⟨d,e,dp,du,ep,eu,dex,eex,dcount,ecount⟩ :=
    OMA.Erdos13Cyclic.mixed_pivot_witnesses hr hu hu0 cap within lim hne
  by_cases ds : d≤D.sqrt
  · exact Or.inr ⟨d,dp,ds,du,dex⟩
  by_cases es : e≤D.sqrt
  · exact Or.inr ⟨e,ep,es,eu,eex⟩
  exact Or.inl ⟨d,e,by omega,du,by omega,eu,dcount,ecount⟩

end OMA.Erdos13Mixed

end

section

namespace ThirdStrip

open Finset FullColumns

/-- Two occupied lifts also give freeness on a slightly wider shell, by
integrality of the multiplier. -/
lemma free_wider {r a X : ℕ} {A P S : Finset ℕ}
    (both : ∀ u ∈ P, ∀ k ∈ Icc 1 2, k*a+u ∈ A) (free : Free r A)
    (sub : S ⊆ P) (band : ∀ u ∈ S, 0 < u ∧ u ≤ X ∧ r*X < (2*r+1)*u) :
    Free r S := by
  intro u hu b hb hlt hd
  obtain ⟨k, hk⟩ := hd
  have lower : r*u ≤ ∑ i, b i := by
    simpa using sum_le_sum (s := (univ : Finset (Fin r))) (f := fun _ => u)
      (g := b) (fun i _ => (hlt i).le)
  have upper : ∑ i, b i ≤ r*X := by
    simpa using sum_le_sum (s := (univ : Finset (Fin r))) (f := b)
      (g := fun _ => X) (fun i _ => (band _ (hb i)).2.1)
  have eq : ∑ i, b i = k*u := by simpa [Nat.mul_comm] using hk
  rw [eq] at lower upper
  have bound : k ≤ r*2 := by
    have hlt' : k*u < (2*r+1)*u := lt_of_le_of_lt upper (band _ hu).2.2
    have hh : k < 2*r+1 := Nat.lt_of_mul_lt_mul_right hlt'
    omega
  exact lift_forbidden (by decide : 0 < 2) both free (sub hu) b
    (fun i => sub (hb i)) hlt (Nat.le_of_mul_le_mul_right lower (band _ hu).1) bound eq

/-- Iterating the shell estimate bounds the number of doubly occupied offsets.
At r=3, the strictly wider shell pays for the per-shell additive error. -/
lemma complete_half {r a C D : ℕ} (hr : 3 ≤ r) {A P : Finset ℕ}
    (both : ∀ u ∈ P, ∀ k ∈ Icc 1 2, k*a+u ∈ A) (free : Free r A)
    (wide : ∀ (X : ℕ) (S : Finset ℕ), (∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) →
      Free r S → (r+1)*S.card ≤ X+C)
    (within : ∀ u ∈ P, u ≤ D) :
    2*P.card ≤ D + (24*(C+1)+2) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have inductionBound (X : ℕ) : 2*(F X).card ≤ X + (24*(C+1)+2) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ 24*(C+1)
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have hh := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        omega
      let t := if r = 3 then 11*X/24 else X/2
      have ht : t < X := by dsimp [t]; split_ifs <;> omega
      let S := (F X).filter fun x => t < x
      have data (x : ℕ) (hx : x ∈ S) :
          0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X ∧ r*X < (2*r+1)*x := by
        obtain ⟨hFx, htx⟩ := mem_filter.mp hx
        have hxX := (mem_filter.mp hFx).2
        by_cases h3 : r = 3
        · subst r
          simp only [t, if_true] at htx
          constructor
          · omega
          constructor
          · omega
          constructor
          · exact hxX
          · omega
        · simp only [t, if_neg h3] at htx
          have hX : X ≤ 2*x := by omega
          have hh := Nat.mul_le_mul_left r hX
          have hxpos : 0 < x := by omega
          exact ⟨hxpos, by nlinarith only [hh, Nat.zero_le X], hxX, by nlinarith only [hh, hxpos]⟩
      have incl : S ⊆ P := (filter_subset _ _).trans (filter_subset _ _)
      have count := wide X S (fun x hx => ⟨(data x hx).1, (data x hx).2.1, (data x hx).2.2.1⟩)
        (free_wider both free incl (fun x hx => ⟨(data x hx).1,(data x hx).2.2⟩))
      have balance : 2*S.card + t ≤ X := by
        by_cases h3 : r = 3
        · subst r
          simp only [t, if_true]
          omega
        · simp only [t, if_neg h3]
          have hc := Nat.mul_le_mul_right S.card (show 5 ≤ r+1 by omega)
          omega
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have eq : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F, mem_filter]
        constructor
        · rintro ⟨⟨hxP, _⟩, hxt⟩
          exact ⟨hxP, by omega⟩
        · rintro ⟨hxP, hxt⟩
          exact ⟨⟨hxP, by omega⟩, by omega⟩
      rw [eq] at part
      change S.card + (F t).card = (F X).card at part
      have tail := ih t ht
      omega
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using inductionBound D

/-- Combine the two independent upper bounds on the final partial period. -/
lemma two_layers {r N a E K R P B : ℕ} (hr : 1 ≤ r) (layers : 2*a ≤ N)
    (res : r*R ≤ a+E) (duplicates : P ≤ R) (half : 2*P ≤ N-2*a+K)
    (count : B ≤ R+P) : (r+1)*B ≤ N+2*E+K := by
  have single : B ≤ 2*R := by omega
  have more := Nat.mul_le_mul_left (r-1) single
  have ident : r-1+1=r := by omega
  have iB := congrArg (fun j : ℕ => j*B) ident
  have iR := congrArg (fun j : ℕ => j*(2*R)) ident
  have dec := Nat.sub_add_cancel layers
  nlinarith only [more, iB, iR, dec, res, count, half]


/-- A tail spanning at most two complete residue layers satisfies the target
bound as soon as its image modulo the divisor obeys the cyclic sumset bound. -/
lemma strip_tail {r a N E C : ℕ} {A B : Finset ℕ} (hr : 3 ≤ r) (ha : 0 < a)
    (hain : a ∈ A) (lo : 2*a ≤ N) (hi : N ≤ 3*a) (subA : B ⊆ A)
    (sub : B ⊆ Ioc a N) (free : FullColumns.Free r A)
    (res : r*(B.image (·%a)).card ≤ a+E)
    (wide : ∀ (X : ℕ) (S : Finset ℕ), (∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) →
      FullColumns.Free r S → (r+1)*S.card ≤ X+C) :
    (r+1)*B.card ≤ N+2*E+(24*(C+1)+2) := by
  classical
  let P := FullColumns.complete B a 2
  have completeLift (u : ℕ) (hu : u ∈ P) (k : ℕ) (hk : k ∈ Icc 1 2) :
      k*a+u ∈ B := (mem_filter.mp hu).2 k hk
  have bounds (u : ℕ) (hu : u ∈ P) : u ≤ N-2*a := by
    have := (mem_Ioc.mp (sub (completeLift u hu 2 (by decide)))).2
    omega
  have half := complete_half hr
    (fun u hu k hk => subA (completeLift u hu k hk)) free wide bounds
  have layers (b : ℕ) (hb : b ∈ B) : b / a ∈ Icc 1 2 := by
    have mem := mem_Ioc.mp (sub hb)
    have strict : b < 3*a := by
      by_contra! hbr
      have eq : b = 3*a := by omega
      have dv : a ∣ b := eq ▸ dvd_mul_left _ _
      have hsum : a ∣ ∑ _i : Fin r, b := by
        simpa using dv.trans (dvd_mul_left b r)
      exact free a hain (fun _ => b) (fun _ => subA hb) (fun _ => mem.1) hsum
    refine mem_Icc.mpr ⟨Nat.div_pos mem.1.le ha, ?_⟩
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr strict)
  have count : B.card ≤ (B.image (·%a)).card + P.card := by
    simpa [P] using FullColumns.card_bound (B := B) (by decide : 0 < 2) layers
  have subR : P ⊆ B.image (·%a) := filter_subset _ _
  exact two_layers (by omega) lo res (card_le_card subR) half count

end ThirdStrip

end

section

namespace OMA.Erdos13UpperShell
open Finset

/-- Each represented residue can occur in at most k places in a window of length k*d. -/
theorem count_residues_in_blocks {B : Finset ℕ} {a d k : ℕ} (hd : 0 < d)
    (hs : B ⊆ Ioc a (a + k*d)) :
    B.card ≤ k * (B.image (fun x => x % d)).card := by
  classical
  let f := fun x : ℕ => ((x - (a+1)) / d, x % d)
  have bound : B.card ≤ ((range k) ×ˢ (B.image fun x => x % d)).card := by
    apply card_le_card_of_injOn f
    · intro x hx
      have h := mem_Ioc.mp (hs hx)
      exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hd).mpr (by omega)),
        mem_image_of_mem _ hx⟩
    · intro x hx y hy he
      have hx' := mem_Ioc.mp (hs hx)
      have hy' := mem_Ioc.mp (hs hy)
      have eqD : (x - (a+1))/d = (y - (a+1))/d := congrArg Prod.fst he
      have eqM : x ≡ y [MOD d] := congrArg Prod.snd he
      have eqP : (x-(a+1)) % d = (y-(a+1)) % d :=
        Nat.ModEq.sub_right (by omega) (by omega) eqM
      have eqT := Nat.mod_add_div (x-(a+1)) d
      rw [eqD, eqP, Nat.mod_add_div] at eqT
      omega
  simpa [card_product] using bound

theorem upper_shell_tail {r a d N : ℕ} (hr : 2 ≤ r) (ha : N ≤ 2*a)
    (han : a ≤ N) (hd : 16*r < d) (hdvd : d ∣ a) (B : Finset ℕ)
    (hs : B ⊆ Ioc a N) (hres : r * (B.image (fun x => x%d)).card ≤ d + r - 2) :
    (r+1)*B.card ≤ N + 16*r := by
  have hpos : 0 < d := by omega
  obtain ⟨h, hh⟩ := hdvd
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at hres
  have hres' : r*R.card ≤ d+r := by omega
  by_cases hsmall : h ≤ 16
  · have cover : B ⊆ Ioc a (a+h*d) := by
      intro x hx
      have hb := mem_Ioc.mp (hs hx)
      rw [mul_comm h d, ← hh]
      exact mem_Ioc.mpr ⟨hb.1, by omega⟩
    have cnt : B.card ≤ h*R.card := count_residues_in_blocks hpos cover
    have hc := Nat.mul_le_mul_left r cnt
    have hk := Nat.mul_le_mul_left h hres'
    have hrh := Nat.mul_le_mul_right r hsmall
    have len := card_le_card hs
    rw [Nat.card_Ioc] at len
    have len' : B.card + a ≤ N := by omega
    nlinarith only [hc, hk, hrh, len', hh]
  · let q := (N-a)/d
    have hq : q*d ≤ N-a := Nat.div_mul_le_self _ _
    have len : N-a < (q+1)*d := by
      rw [Nat.add_mul, Nat.one_mul]
      have := Nat.mod_add_div (N-a) d
      have := Nat.mod_lt (N-a) hpos
      change N-a < (N-a)/d*d + d
      rw [Nat.mul_comm ((N-a)/d) d]
      omega
    have cnt : B.card ≤ (q+1)*R.card := by
      apply count_residues_in_blocks hpos
      intro x hx
      have hb := mem_Ioc.mp (hs hx)
      exact mem_Ioc.mpr ⟨hb.1, by omega⟩
    have hc := Nat.mul_le_mul_left r cnt
    have hk := Nat.mul_le_mul_left (q+1) hres'
    have hqr := Nat.mul_le_mul_left q (show 16*r ≤ d by omega)
    have hdb := Nat.mul_le_mul_left d (show 16 ≤ h by omega)
    have hL : (N-a) + a = N := by omega
    have h2 := Nat.mul_le_mul_right B.card hr
    nlinarith only [hc, hk, hqr, hdb, hq, hh, hL, ha, han, h2, Nat.zero_le N, Nat.zero_le r]

/-- The only additive input is the cyclic quotient witness. -/
theorem upper_shell_of_quotients {r N : ℕ} (hr : 2 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ N ≤ 2*a ∧ a ≤ N)
    (witness : ∀ a ∈ A, (A.filter fun x => a < x).Nonempty →
      ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2) :
    (r+1)*A.card ≤ N + (r+1)*(16*r+1) + 16*r := by
  classical
  have aw (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases ht : (A.filter fun x => a < x).Nonempty
    · exact witness a ha ht
    · rw [not_nonempty_iff_eq_empty] at ht
      refine ⟨a, (sub a ha).1, dvd_refl _, ?_, by simp [ht]⟩
      intro b hb hlt
      have hmem : b ∈ (A.filter fun x => a < x) := mem_filter.mpr ⟨hb, hlt⟩
      simp [ht] at hmem
  choose! f pos div later size using aw
  let E := A.filter fun x => f x ≤ 16*r
  have low : E.card ≤ 16*r := by
    have hc : E.card ≤ (Icc 1 (16*r)).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1, h.2⟩
      · intro x hx y hy he
        have hxa := (mem_filter.mp hx).1
        have hya := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxa y hya h (he ▸ div y hya))
        · exact h
        · exact False.elim (later y hya x hxa h (he ▸ div x hxa))
    simpa using hc
  let G := A.filter fun x => 16*r < f x
  by_cases non : G.Nonempty
  · let a := G.min' non
    have hag : a ∈ G := min'_mem _ _
    have hf := mem_filter.mp hag
    let B := A.filter fun x => a < x
    have hB : B ⊆ Ioc a N := by
      intro x hx
      have hx' := mem_filter.mp hx
      exact mem_Ioc.mpr ⟨hx'.2, (sub x hx'.1).2.2⟩
    have ht := upper_shell_tail hr (sub a hf.1).2.1 (sub a hf.1).2.2 hf.2
      (div a hf.1) B hB (size a hf.1)
    have cover : A ⊆ E ∪ insert a B := by
      intro x hx
      by_cases h : f x ≤ 16*r
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have hxg : x ∈ G := mem_filter.mpr ⟨hx, by omega⟩
        have hax : a ≤ x := min'_le _ _ hxg
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cnt := (card_le_card cover).trans (card_union_le _ _)
    have ins := card_insert_le a B
    have hcard : A.card ≤ 16*r+1+B.card := by omega
    have := Nat.mul_le_mul_left (r+1) hcard
    nlinarith only [this, ht]
  · have cover : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact non ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left (r+1) ((card_le_card cover).trans low)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r]

end OMA.Erdos13UpperShell

end

section

/-  Widen the upper half by permitting a small incomplete second period. -/

namespace OMA.Erdos13UpperShell
open Finset

theorem wide_shell_tail {r a d N : ℕ} (hr : 3 ≤ r)
    (cut : 4*r*N ≤ 8*r*a + N)
    (han : a ≤ N) (hd : 16*r < d) (hdvd : d ∣ a) (B : Finset ℕ)
    (hs : B ⊆ Ioc a N) (hres : r * (B.image (fun x => x%d)).card ≤ d + r - 2) :
    (r+1)*B.card ≤ N + 32*r := by
  by_cases half : N ≤ 2*a
  · have bound := upper_shell_tail (by omega) half han hd hdvd B hs hres
    omega
  have eEq : N - 2*a + 2*a = N := by omega
  have eScaled := congrArg (fun n : ℕ => 4*r*n) eEq
  have eBudget : 4*r*(N-2*a) ≤ N := by nlinarith only [eScaled, cut]
  have eLo := Nat.mul_le_mul_right (N-2*a) (show 1 ≤ r by omega)
  have eSimple : 4*(N-2*a) ≤ N := by nlinarith only [eBudget,eLo]
  have lengthBound : 8*(N-a) ≤ 5*N := by omega
  have hpos : 0 < d := by omega
  obtain ⟨h, hh⟩ := hdvd
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at hres
  have hres' : r*R.card ≤ d+r := by omega
  by_cases hsmall : h ≤ 16
  · let P := B.filter fun x => x ≤ 2*a
    let Q := B.filter fun x => ¬ x ≤ 2*a
    have cover : P ⊆ Ioc a (a+h*d) := by
      intro x hx
      have hp := mem_filter.mp hx
      rw [mul_comm h d, ← hh]
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp (hs hp.1)).1, by omega⟩
    have hp := count_residues_in_blocks hpos cover
    have hIm : (P.image (fun x => x%d)) ⊆ R := image_subset_image (filter_subset _ _)
    have cnt := hp.trans (Nat.mul_le_mul_left h (card_le_card hIm))
    have hc := Nat.mul_le_mul_left r cnt
    have hk := Nat.mul_le_mul_left h hres'
    have hrh := Nat.mul_le_mul_right r hsmall
    have hQ : Q ⊆ Ioc (2*a) N := by
      intro x hx
      have hq := mem_filter.mp hx
      exact mem_Ioc.mpr ⟨lt_of_not_ge hq.2, (mem_Ioc.mp (hs hq.1)).2⟩
    have hQc := card_le_card hQ
    rw [Nat.card_Ioc] at hQc
    have hQr := Nat.mul_le_mul_left r hQc
    have partition : P.card+Q.card = B.card := B.card_filter_add_card_filter_not _
    have hSum := congrArg (fun s : ℕ => r*s) partition
    have h3 := Nat.mul_le_mul_right B.card hr
    have ha2 : 2*a ≤ N := by omega
    nlinarith only [hc, hk, hrh, hh, hQr, hSum, h3, ha2, eBudget, Nat.zero_le r]
  · let q := (N-a)/d
    have hq : q*d ≤ N-a := Nat.div_mul_le_self _ _
    have len : N-a < (q+1)*d := by
      rw [Nat.add_mul, Nat.one_mul]
      have := Nat.mod_add_div (N-a) d
      have := Nat.mod_lt (N-a) hpos
      change N-a < (N-a)/d*d + d
      rw [Nat.mul_comm ((N-a)/d) d]
      omega
    have cnt : B.card ≤ (q+1)*R.card := by
      apply count_residues_in_blocks hpos
      intro x hx
      have hb := mem_Ioc.mp (hs hx)
      exact mem_Ioc.mpr ⟨hb.1, by omega⟩
    have hc := Nat.mul_le_mul_left r cnt
    have hk := Nat.mul_le_mul_left (q+1) hres'
    have hqr := Nat.mul_le_mul_left q (show 16*r ≤ d by omega)
    have hdb := Nat.mul_le_mul_left d (show 16 ≤ h by omega)
    have h3 := Nat.mul_le_mul_right B.card hr
    nlinarith only [hc, hk, hqr, hdb, hq, hh, han, lengthBound, h3, Nat.zero_le N, Nat.zero_le r]

theorem wide_shell_of_quotients {r N : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ 4*r*N ≤ 8*r*a + N ∧ a ≤ N)
    (witness : ∀ a ∈ A, (A.filter fun x => a < x).Nonempty →
      ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2) :
    (r+1)*A.card ≤ N + (r+1)*(16*r+1) + 32*r := by
  classical
  have aw (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases ht : (A.filter fun x => a < x).Nonempty
    · exact witness a ha ht
    · rw [not_nonempty_iff_eq_empty] at ht
      refine ⟨a, (sub a ha).1, dvd_refl _, ?_, by simp [ht]⟩
      intro b hb hlt
      have hmem : b ∈ (A.filter fun x => a < x) := mem_filter.mpr ⟨hb, hlt⟩
      simp [ht] at hmem
  choose! f pos div later size using aw
  let E := A.filter fun x => f x ≤ 16*r
  have low : E.card ≤ 16*r := by
    have hc : E.card ≤ (Icc 1 (16*r)).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1, h.2⟩
      · intro x hx y hy he
        have hxa := (mem_filter.mp hx).1
        have hya := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxa y hya h (he ▸ div y hya))
        · exact h
        · exact False.elim (later y hya x hxa h (he ▸ div x hxa))
    simpa using hc
  let G := A.filter fun x => 16*r < f x
  by_cases non : G.Nonempty
  · let a := G.min' non
    have hag : a ∈ G := min'_mem _ _
    have hf := mem_filter.mp hag
    let B := A.filter fun x => a < x
    have hB : B ⊆ Ioc a N := by
      intro x hx
      have hx' := mem_filter.mp hx
      exact mem_Ioc.mpr ⟨hx'.2, (sub x hx'.1).2.2⟩
    have ht := wide_shell_tail hr (sub a hf.1).2.1 (sub a hf.1).2.2 hf.2
      (div a hf.1) B hB (size a hf.1)
    have cover : A ⊆ E ∪ insert a B := by
      intro x hx
      by_cases h : f x ≤ 16*r
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have hxg : x ∈ G := mem_filter.mpr ⟨hx, by omega⟩
        have hax : a ≤ x := min'_le _ _ hxg
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cnt := (card_le_card cover).trans (card_union_le _ _)
    have ins := card_insert_le a B
    have hcard : A.card ≤ 16*r+1+B.card := by omega
    have := Nat.mul_le_mul_left (r+1) hcard
    nlinarith only [this, ht]
  · have cover : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact non ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left (r+1) ((card_le_card cover).trans low)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r]

end OMA.Erdos13UpperShell

end

section

/-  # Cyclic quotient witnesses for admissible sets and their residue fibers -/
namespace OMA.Erdos13Cyclic

open Finset

theorem witness_of_free {r : ℕ} (hr : 2 ≤ r) {A : Finset ℕ} (free : FullColumns.Free r A)
    (pos : ∀ a ∈ A, 0 < a) (a : ℕ) (ha : a ∈ A)
    (hne : (A.filter fun x => a < x).Nonempty) :
    ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2 := by
  obtain ⟨d, hd, hdvd, hno, hsize⟩ := quotient_witness hr (pos a ha) _ hne
    (fun b hb => free a ha b (fun i => (mem_filter.mp (hb i)).1) (fun i => (mem_filter.mp (hb i)).2))
  exact ⟨d, hd, hdvd, fun b hb hlt => hno b (mem_filter.mpr ⟨hb,hlt⟩), hsize⟩

theorem count_residue_fibers (B : Finset ℕ) {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hdvd : d ∣ a) :
    (B.image (fun x => x % a)).card ≤ (a / d) * (B.image (fun x => x % d)).card := by
  classical
  let R := B.image (fun x => x % a)
  let T := B.image (fun x => x % d)
  have bound : R.card ≤ ((range (a / d)) ×ˢ T).card := by
    apply card_le_card_of_injOn (fun x => (x / d, x % d))
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      refine mem_product.mpr ⟨mem_range.mpr ?_, ?_⟩
      · apply (Nat.div_lt_iff_lt_mul hd).mpr
        rw [Nat.div_mul_cancel hdvd]
        exact Nat.mod_lt _ ha
      · change y % a % d ∈ T
        rw [Nat.mod_mod_of_dvd _ hdvd]
        exact mem_image_of_mem _ hy
    · intro x hx y hy hp
      have h1 : x / d = y / d := congrArg Prod.fst hp
      have h2 : x % d = y % d := congrArg Prod.snd hp
      have eq := Nat.mod_add_div x d
      rwa [h1, h2, Nat.mod_add_div, eq_comm] at eq
  simpa [card_product] using bound

theorem residue_bound_of_quotient (B : Finset ℕ) {r a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hdvd : d ∣ a) (hres : r * (B.image (fun x => x % d)).card ≤ d + r - 2) :
    r * (B.image (fun x => x % a)).card ≤ a + (a / d) * r := by
  have basic := count_residue_fibers B ha hd hdvd
  calc r * (B.image (fun x => x % a)).card ≤ r * ((a/d) * (B.image (fun x => x % d)).card) :=
         Nat.mul_le_mul_left _ basic
       _ = (a/d) * (r * (B.image (fun x => x % d)).card) := by ring
       _ ≤ (a/d) * (d+r) := Nat.mul_le_mul_left _ (by omega)
       _ = _ := by rw [Nat.mul_add, Nat.div_mul_cancel hdvd]

theorem wide_shell {r N : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ 4*r*N ≤ 8*r*a + N ∧ a ≤ N) (free : FullColumns.Free r A) :
    (r+1)*A.card ≤ N + (r+1)*(16*r+1) + 32*r :=
  OMA.Erdos13UpperShell.wide_shell_of_quotients hr A sub
    (witness_of_free (by omega) free (fun a ha => (sub a ha).1))

end OMA.Erdos13Cyclic

end

section

/-  A cardinal bound in the top two thirds of the interval. -/
namespace OMA.Erdos13UpperShell
open Finset FullColumns

lemma third_large_stabilizer {r a d N : ℕ} (hr : 3 ≤ r) (ha : N ≤ 3*a)
    (han : a ≤ N) (hd : 64*r < d) (large : 64 < a/d)
    (B : Finset ℕ) (hs : B ⊆ Ioc a N)
    (hres : r * (B.image (fun x => x%d)).card ≤ d + r - 2) :
    (r+1)*B.card ≤ N + 32*r := by
  have hpos : 0 < d := by omega
  have hD := (Nat.mul_le_mul_right d (show 64 ≤ a/d by omega)).trans (Nat.div_mul_le_self _ _)
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at hres
  have hres' : r*R.card ≤ d+r := by omega
  have lengthBound : 3*(N-a) ≤ 2*N := by omega
  let q := (N-a)/d
  have hq : q*d ≤ N-a := Nat.div_mul_le_self _ _
  have len : N-a < (q+1)*d := by
    rw [Nat.add_mul, Nat.one_mul]
    have := Nat.mod_add_div (N-a) d
    have := Nat.mod_lt (N-a) hpos
    change N-a < (N-a)/d*d + d
    rw [Nat.mul_comm ((N-a)/d) d]
    omega
  have cnt : B.card ≤ (q+1)*R.card := by
    apply count_residues_in_blocks hpos
    intro x hx
    have hb := mem_Ioc.mp (hs hx)
    exact mem_Ioc.mpr ⟨hb.1, by omega⟩
  have hc := Nat.mul_le_mul_left r cnt
  have hk := Nat.mul_le_mul_left (q+1) hres'
  have hqr := Nat.mul_le_mul_left q (show 64*r ≤ d by omega)

  have h3 := Nat.mul_le_mul_right B.card hr
  nlinarith only [hc, hk, hqr, hD, hq, han, lengthBound, h3, Nat.zero_le N, Nat.zero_le r]

lemma select_large_quotient {r N L K : ℕ} (A : Finset ℕ)
    (positive : ∀ a ∈ A, 0 < a)
    (witness : ∀ a ∈ A, (A.filter fun x => a < x).Nonempty →
      ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2)
    (tail : ∀ a ∈ A, ∀ d : ℕ, L < d → d ∣ a →
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 →
      (r+1)*(A.filter fun x => a<x).card ≤ N+K) :
    (r+1)*A.card ≤ N + K + (r+1)*(L+1) := by
  classical
  have aw (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases ht : (A.filter fun x => a < x).Nonempty
    · exact witness a ha ht
    · rw [not_nonempty_iff_eq_empty] at ht
      refine ⟨a, positive a ha, dvd_refl _, ?_, by simp [ht]⟩
      intro b hb hlt
      have hmem : b ∈ (A.filter fun x => a < x) := mem_filter.mpr ⟨hb, hlt⟩
      simp [ht] at hmem
  choose! f pos div later size using aw
  let E := A.filter fun x => f x ≤ L
  have low : E.card ≤ L := by
    have hc : E.card ≤ (Icc 1 (L)).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1, h.2⟩
      · intro x hx y hy he
        have hxa := (mem_filter.mp hx).1
        have hya := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxa y hya h (he ▸ div y hya))
        · exact h
        · exact False.elim (later y hya x hxa h (he ▸ div x hxa))
    simpa using hc
  let G := A.filter fun x => L < f x
  by_cases non : G.Nonempty
  · let a := G.min' non
    have hag : a ∈ G := min'_mem _ _
    have hf := mem_filter.mp hag
    let B := A.filter fun x => a < x
    have ht : (r+1)*B.card ≤ N+K := tail a hf.1 (f a) hf.2 (div a hf.1) (size a hf.1)
    have cover : A ⊆ E ∪ insert a B := by
      intro x hx
      by_cases h : f x ≤ L
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have hxg : x ∈ G := mem_filter.mpr ⟨hx, by omega⟩
        have hax : a ≤ x := min'_le _ _ hxg
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cnt := (card_le_card cover).trans (card_union_le _ _)
    have ins := card_insert_le a B
    have hcard : A.card ≤ L+1+B.card := by omega
    have := Nat.mul_le_mul_left (r+1) hcard
    nlinarith only [this, ht]
  · have cover : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact non ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left (r+1) ((card_le_card cover).trans low)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r, Nat.zero_le K]

/-- Every admissible set in the top two thirds satisfies the desired bound. -/
theorem bound_on_third_shell {r N : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ N ≤ 3*a ∧ a ≤ N) (free : Free r A) :
    (r+1)*A.card ≤ N + (128*r + 24*((r+1)*(16*r+1)+32*r+1)+2) + (r+1)*(64*r+1) := by
  classical
  have pos (a) (ha : a ∈ A) := (sub a ha).1
  apply select_large_quotient A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a hain d hd hdvd hres
  let B := A.filter fun x => a < x
  change (r+1)*B.card ≤ _
  have hB : B ⊆ Ioc a N := by
    intro x hx
    have hf := mem_filter.mp hx
    exact mem_Ioc.mpr ⟨hf.2,(sub x hf.1).2.2⟩
  have apos := pos a hain
  have ha := (sub a hain).2.1
  have han := (sub a hain).2.2
  by_cases upper : N ≤ 2*a
  · have := upper_shell_tail (by omega : 2≤r) upper han (by omega : 16*r<d) hdvd B hB hres
    omega
  by_cases large : 64 < a/d
  · have := third_large_stabilizer hr ha han hd large B hB hres
    omega
  · have reduced := OMA.Erdos13Cyclic.residue_bound_of_quotient B apos (by omega : 0<d) hdvd hres
    have hR := reduced.trans (Nat.add_le_add_left (Nat.mul_le_mul_right r (show a/d≤64 by omega)) a)
    have w (X : ℕ) (S : Finset ℕ)
        (hs : ∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) (hf : Free r S) :
        (r+1)*S.card ≤ X+((r+1)*(16*r+1)+32*r) := by
      simpa only [Nat.add_assoc] using OMA.Erdos13Cyclic.wide_shell hr S hs hf
    have hb := ThirdStrip.strip_tail hr apos hain (by omega : 2*a ≤ N) ha
      (show B ⊆ A by exact filter_subset _ _) hB free hR w
    omega

end OMA.Erdos13UpperShell

end

section

/-  Induction on the number of complete residue layers. -/
namespace OMA.Erdos13ManyLayers
open Finset FullColumns

def Shell (r J C : ℕ) : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), (∀ a ∈ A, 0 < a ∧ N ≤ J*a ∧ a ≤ N) →
    Free r A → (r+1)*A.card ≤ N+C

lemma gap_factor {r J : ℕ} (hJ : 3 ≤ J) (hr : J < r) :
    J*J + (r+1) + 1 ≤ J*(r+1) := by
  have hr' : r-(J+1)+(J+1)=r := by omega
  have hJ' : J-1+1=J := by omega
  have h := congrArg (fun z : ℕ => J*z) hr'
  have h' := congrArg (fun z : ℕ => z*(r-(J+1))) hJ'
  nlinarith only [hJ, hr', h, h', Nat.zero_le ((J-1)*(r-(J+1)))]

lemma pay_shell {r J X C t b : ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (cap : (r+1)*b ≤ X+C) (round : J*t ≤ X) (big : J*J*C ≤ X) :
    J*b+t ≤ X := by
  have hcap := Nat.mul_le_mul_left (J*J) cap
  have hround := Nat.mul_le_mul_left (r+1) round
  have factor := Nat.mul_le_mul_right X (gap_factor hJ hr)
  have hcombine : J*(r+1)*(J*b+t) ≤ J*(r+1)*X := by
    nlinarith only [hcap, hround, factor, big]
  exact Nat.le_of_mul_le_mul_left hcombine (by positivity)

lemma complete_bound {r a J C D : ℕ} (hJ : 3 ≤ J) (hr : J < r) {A P : Finset ℕ}
    (allLifts : ∀ u ∈ P, ∀ k ∈ Icc 1 J, k*a+u ∈ A) (free : Free r A)
    (prev : Shell r J C) (within : ∀ u ∈ P, u ≤ D) :
    J*P.card ≤ D + J*(J*J*C+1) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have step (X : ℕ) : J*(F X).card ≤ X + J*(J*J*C+1) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ J*J*C
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        have := Nat.mul_le_mul_left J (show (F X).card ≤ J*J*C+1 by omega)
        omega
      let t := X/J
      have ht : t < X := Nat.div_lt_self (by omega) (by omega)
      let S := P.filter fun u => u ≤ X ∧ X < J*u
      have bound := prev X S (by
        intro x hx
        have h := (mem_filter.mp hx).2
        have hp : 0 < x := by
          by_contra! hz
          simp [show x=0 by omega] at h
        exact ⟨hp,h.2.le,h.1⟩) (free_shell (by omega : 0<J) allLifts free X)
      have envelope := pay_shell hJ hr bound (Nat.mul_div_le X J) (le_of_not_ge small)
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have hiff (x : ℕ) : t<x ↔ X<J*x := by
        dsimp [t]
        rw [Nat.div_lt_iff_lt_mul (by omega : 0<J), Nat.mul_comm]
      have eq₁ : ((F X).filter fun x => t<x) = S := by
        ext x
        simp only [F,S,mem_filter,hiff]
        tauto
      have eq₂ : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F,mem_filter]
        constructor
        · rintro ⟨⟨hx, _⟩, hs⟩
          exact ⟨hx, by omega⟩
        · rintro ⟨hx, hs⟩
          exact ⟨⟨hx, by omega⟩, by omega⟩
      rw [eq₁,eq₂] at part
      have hi := ih t ht
      have hparts := congrArg (fun k => J*k) part
      change J*S.card + t ≤ X at envelope
      rw [Nat.mul_add] at hparts
      omega
  have h := step D
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using h

lemma layers_count {r J N a E K R P B : ℕ} (hJ : 1 ≤ J) (hr : J ≤ r+1)
    (lo : J*a ≤ N) (imageBound : r*R ≤ a+E) (fullSub : P ≤ R)
    (fullBound : J*P ≤ N-J*a+K) (count : B ≤ (J-1)*R+P) :
    (r+1)*B ≤ N + J*E + K := by
  have c := Nat.mul_le_mul_left (r+1) count
  have i := Nat.mul_le_mul_left J imageBound
  have p := Nat.mul_le_mul_left (r+1-J) fullSub
  have hj : J-1+1=J := by omega
  have ht : r+1-J+J=r+1 := by omega
  have idj := congrArg (fun k : ℕ => (r+1)*k*R) hj
  have idp := congrArg (fun k : ℕ => k*P) ht
  have idr := congrArg (fun k : ℕ => k*R) ht
  have dec := Nat.sub_add_cancel lo
  nlinarith only [c, i, p, fullBound, idj, idp, idr, dec]


lemma layer_tail {r J a N E C : ℕ} {A B : Finset ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (ha : 0 < a) (hain : a ∈ A) (lo : J*a ≤ N) (hi : N ≤ (J+1)*a)
    (subA : B ⊆ A) (sub : B ⊆ Ioc a N) (free : Free r A)
    (imageBound : r*(B.image (·%a)).card ≤ a+E) (prev : Shell r J C) :
    (r+1)*B.card ≤ N+J*E+J*(J*J*C+1) := by
  classical
  let P := FullColumns.complete B a J
  have completeLift (u : ℕ) (hu : u ∈ P) (k : ℕ) (hk : k ∈ Icc 1 J) :
      k*a+u ∈ B := (mem_filter.mp hu).2 k hk
  have bounds (u) (hu : u ∈ P) : u ≤ N-J*a := by
    have := (mem_Ioc.mp (sub (completeLift u hu J (mem_Icc.mpr ⟨by omega,le_rfl⟩)))).2
    omega
  have last := complete_bound hJ hr
    (fun u hu k hk => subA (completeLift u hu k hk)) free prev bounds
  have layers (b : ℕ) (hb : b ∈ B) : b / a ∈ Icc 1 J := by
    have mem := mem_Ioc.mp (sub hb)
    have strict : b < (J+1)*a := by
      by_contra! hbr
      have eq : b = (J+1)*a := by omega
      have dv : a ∣ b := eq ▸ dvd_mul_left _ _
      have hsum : a ∣ ∑ _i : Fin r, b := by
        simpa using dv.trans (dvd_mul_left b r)
      exact free a hain (fun _ => b) (fun _ => subA hb) (fun _ => mem.1) hsum
    refine mem_Icc.mpr ⟨Nat.div_pos mem.1.le ha, ?_⟩
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr strict)
  have subR : P ⊆ B.image (·%a) := filter_subset _ _
  exact layers_count (by omega) (by omega) lo imageBound (card_le_card subR) last
    (FullColumns.card_bound (by omega : 0<J) layers)

lemma medium_quotient {r a d N : ℕ} (hr : 3 ≤ r) (han : a ≤ N) (shell : N ≤ r*a)
    (hd : 4*r*r*(r+1) < d) (large : 4*(r+1) < a/d)
    (B : Finset ℕ) (sub : B ⊆ Ioc a N)
    (quot : r * (B.image (fun x => x%d)).card ≤ d+r-2) :
    (r+1)*B.card ≤ N+r*(r+1) := by
  classical
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at quot
  let t := (N-a)/d
  have hdpos : 0 < d := by omega
  have hperiod : t*d ≤ N-a := Nat.div_mul_le_self _ _
  have dsmall := (Nat.mul_le_mul_right d large.le).trans (Nat.div_mul_le_self _ _)
  have hMul : t*(4*r*r*(r+1)) ≤ r*a := by
    exact (Nat.mul_le_mul_left t hd.le).trans (hperiod.trans (by omega))
  have htr : t*(4*r*(r+1)) ≤ a := by
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0<r)
    convert hMul using 1 <;> ring
  have len : N-a < (t+1)*d := by
    rw [Nat.succ_mul]
    have rem := Nat.mod_add_div (N-a) d
    have hrem := Nat.mod_lt (N-a) hdpos
    dsimp [t]
    rw [Nat.mul_comm ((N-a)/d) d]
    omega
  have count : B.card ≤ (t+1)*R.card := by
    apply OMA.Erdos13UpperShell.count_residues_in_blocks hdpos
    intro x hx
    have h := mem_Ioc.mp (sub hx)
    exact mem_Ioc.mpr ⟨h.1, by omega⟩
  have hcount := Nat.mul_le_mul_left r count
  have qbound := Nat.mul_le_mul_left (t+1) (show r*R.card ≤ d+r by omega)
  have hbase : r*B.card ≤ N-a+d+t*r+r := by
    nlinarith only [hcount,qbound,hperiod]
  have L := Nat.mul_le_mul_left (r+1) hbase
  have smallSum : (r+1)*d+(r+1)*t*r ≤ a := by
    nlinarith only [htr,dsmall,Nat.zero_le ((r+1)*d), Nat.zero_le ((r+1)*t*r)]
  have hl : r*((r+1)*B.card) ≤ r*(N+(r+1)) := by
    have dec := congrArg (fun z : ℕ => (r+1)*z) (Nat.sub_add_cancel han)
    nlinarith only [L, dec, smallSum, shell]
  have bound := Nat.le_of_mul_le_mul_left hl (by omega : 0<r)
  have hr' := Nat.mul_le_mul_right (r+1) (show 1≤r by omega)
  omega

lemma next_shell {r J C : ℕ} (hJ : 3 ≤ J) (hr : J < r) (prev : Shell r J C) :
    ∃ K : ℕ, Shell r (J+1) K := by
  classical
  let L := 4*r*r*(r+1)
  let E := 4*(r+1)*r
  let K := C + r*(r+1) + J*E + J*(J*J*C+1)
  refine ⟨K + (r+1)*(L+1), ?_⟩
  intro N A sub free
  have pos (a : ℕ) (ha : a ∈ A) := (sub _ ha).1
  rw [← Nat.add_assoc N K]
  apply OMA.Erdos13UpperShell.select_large_quotient (L := L) A pos
    (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a hain d hd hdvd hres
  let B := A.filter fun x => a < x
  change (r+1)*B.card ≤ N + K
  have hB : B ⊆ Ioc a N := by
    intro x hx
    have h := mem_filter.mp hx
    exact mem_Ioc.mpr ⟨h.2,(sub x h.1).2.2⟩
  have hFree : Free r B := fun x hx b hb => free _ (mem_filter.mp hx).1 b
    (fun i => (mem_filter.mp (hb i)).1)
  have ha := (sub a hain).1
  have hi := (sub a hain).2.1
  have han := (sub a hain).2.2
  by_cases earlier : N ≤ J*a
  · have h := prev N B (by
      intro x hx
      have hI := mem_Ioc.mp (hB hx)
      exact ⟨by omega, earlier.trans (Nat.mul_le_mul_left J hI.1.le), hI.2⟩) hFree
    dsimp [K]
    omega
  by_cases large : 4*(r+1) < a/d
  · have shell : N ≤ r*a := hi.trans (Nat.mul_le_mul_right a hr)
    have h := medium_quotient (r := r) (by omega) han shell hd large B hB hres
    dsimp [K]
    omega
  · have dpos : 0 < d := by dsimp [L] at hd; omega
    have fib := OMA.Erdos13Cyclic.residue_bound_of_quotient B ha dpos hdvd hres
    have imageBound : r * (B.image (·%a)).card ≤ a+E :=
      fib.trans (Nat.add_le_add_left (Nat.mul_le_mul_right r (show a/d ≤ 4*(r+1) by omega)) a)
    have h := layer_tail hJ hr ha hain (by omega : J*a ≤ N) hi
      (show B ⊆ A by exact filter_subset _ _) hB free imageBound prev
    dsimp [K]
    omega

/-- The unrestricted estimate holds for every set supported above N/r. -/
theorem shell_to_arity (r : ℕ) (hr : 3 ≤ r) : ∃ C : ℕ, Shell r r C := by
  have go (j : ℕ) : j+3 ≤ r → ∃ C : ℕ, Shell r (j+3) C := by
    induction j with
    | zero =>
      intro _
      exact ⟨(128*r + 24*((r+1)*(16*r+1)+32*r+1)+2) + (r+1)*(64*r+1),
        fun N A h f => by simpa only [Nat.add_assoc] using
          OMA.Erdos13UpperShell.bound_on_third_shell hr A h f⟩
    | succ j ih =>
      intro h
      obtain ⟨C, old⟩ := ih (by omega)
      exact next_shell (by omega) (by omega) old
  simpa only [Nat.sub_add_cancel hr] using go (r-3) (by omega)

end OMA.Erdos13ManyLayers

end

section

/-  Counting the first, penultimate, and last rows under mixed sumset constraints. -/
namespace OMA.Erdos13MixedRows
open Finset FullColumns

lemma card_one_fiber {B : Finset ℕ} {r u x : ℕ} (hr : 3 ≤ r)
    (layer : ∀ b ∈ B, b/u ∈ Icc 1 r) (hu : 0<u) (hx : x ∈ B.image (·%u)) :
    (r+1)*(B.filter (fun b => b%u=x)).card ≤
      (if x ∈ (B.filter (·<2*u)).image (·%u) then 1 else 0) +
      (r-1)^2*(if x ∈ (B.filter (·<r*u)).image (·%u) then 1 else 0) +
      (2*r-2) + r*(if x ∈ complete B u r then 1 else 0) := by
  classical
  let F := B.filter (fun b => b%u=x)
  let T := (Icc 1 r).filter fun i => i*u+x ∈ B
  have ix : x<u := by
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    exact Nat.mod_lt _ hu
  have inj : (↑F : Set ℕ).InjOn (·/u) := by
    intro j hj k hk h
    change j/u=k/u at h
    have hj0 := Nat.div_add_mod j u
    have hk0 := Nat.div_add_mod k u
    have jm := (mem_filter.mp hj).2
    have km := (mem_filter.mp hk).2
    rw [h,jm] at hj0
    rw [km] at hk0
    omega
  have injB : F.card ≤ T.card := by
    apply card_le_card_of_injOn (·/u) _ inj
    intro y hy
    obtain ⟨yb,ym⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨layer y yb,by rwa [←ym,Nat.div_add_mod']⟩
  have ht : T ⊆ Icc 1 r := filter_subset _ _
  have hc : (Icc 1 r).card=r := by simp
  have cap : F.card ≤ r := injB.trans (hc ▸ card_le_card ht)
  have ar : (r-1+1)=r := by omega
  have ar2 := congrArg (fun z : ℕ => z*z) ar
  have ar3 : 2*r-2+2 = 2*r := by omega
  change (r+1)*F.card ≤ _
  by_cases full : x ∈ complete B u r
  · have occ := (mem_filter.mp full).2 1 (mem_Icc.mpr ⟨le_rfl,by omega⟩)
    simp only [one_mul] at occ
    have modd : (u+x)%u=x := by simp [Nat.mod_eq_of_lt ix]
    have inc : x∈(B.filter (·<2*u)).image (·%u) :=
      mem_image.mpr ⟨u+x,mem_filter.mpr ⟨occ,by omega⟩,modd⟩
    have rmul := Nat.mul_le_mul_right u hr
    have inm : x∈(B.filter (·<r*u)).image (·%u) :=
      mem_image.mpr ⟨u+x,mem_filter.mpr ⟨occ,by omega⟩,modd⟩
    rw [if_pos full,if_pos inc,if_pos inm]
    have h := Nat.mul_le_mul_left (r+1) cap
    nlinarith only [h,ar2,ar3,ar]
  have notT : T ≠ Icc 1 r := by
    intro heq
    apply full
    refine mem_filter.mpr ⟨hx,fun i hi => ?_⟩
    rw [←heq] at hi
    exact (mem_filter.mp hi).2
  have cc := (card_lt_card (ssubset_of_subset_of_ne ht notT))
  rw [hc] at cc
  have short : F.card ≤ r-1 := by omega
  rw [if_neg full,Nat.mul_zero,Nat.add_zero]
  by_cases middle : x∈(B.filter (·<r*u)).image (·%u)
  · rw [if_pos middle,Nat.mul_one]
    have h := Nat.mul_le_mul_left (r+1) short
    have q := Nat.zero_le (if x ∈ (B.filter (·<2*u)).image (·%u) then 1 else 0)
    have ar4 := congrArg (fun n : ℕ => n*(r-1)) ar
    nlinarith only [h,ar2,ar3,ar,ar4,q]
  rw [if_neg middle,Nat.mul_zero,Nat.add_zero]
  have last (b) (hb : b∈F) : b/u=r := by
    have f := mem_filter.mp hb
    have hl := (mem_Icc.mp (layer b f.1)).2
    by_contra! ne
    have low : b < r*u := (Nat.div_lt_iff_lt_mul hu).mp (by omega)
    exact middle (mem_image.mpr ⟨b,mem_filter.mpr ⟨f.1,low⟩,f.2⟩)
  have sing : F.card ≤ 1 := by
    apply card_le_one.mpr
    intro b hb c hcc
    exact inj hb hcc ((last b hb).trans (last c hcc).symm)
  have hh := Nat.mul_le_mul_left (r+1) sing
  omega

lemma mixed_rows_count {B : Finset ℕ} {r u : ℕ} (hr : 3 ≤ r) (hu : 0<u)
    (layer : ∀ b ∈ B, b/u ∈ Icc 1 r) :
    (r+1)*B.card ≤ ((B.filter (·<2*u)).image (·%u)).card +
      (r-1)^2*((B.filter (·<r*u)).image (·%u)).card +
      (2*r-2)*(B.image (·%u)).card + r*(complete B u r).card := by
  classical
  let R := B.image (·%u)
  have lo : (B.filter (·<2*u)).image (·%u) ⊆ R := image_subset_image (filter_subset _ _)
  have mi : (B.filter (·<r*u)).image (·%u) ⊆ R := image_subset_image (filter_subset _ _)
  have cc : complete B u r ⊆ R := filter_subset _ _
  have sum := sum_le_sum (s := R) (fun x hx => card_one_fiber hr layer hu hx)
  simp only [sum_add_distrib,←mul_sum,sum_ite_mem,inter_eq_right.mpr lo,
    inter_eq_right.mpr mi,inter_eq_right.mpr cc,sum_const,nsmul_eq_mul,mul_one] at sum
  have part : ∑ x ∈ R, (B.filter (fun b => b%u=x)).card = B.card := (card_eq_sum_card_image _ _).symm
  rw [part] at sum
  simpa [Nat.mul_comm] using sum
/-- Lift both terms of a mixed Kneser estimate through a common quotient. -/
lemma lift_mixed_size (U V : Finset ℕ) {r D u d : ℕ} (hu : 0<u) (ud : u ≤ D)
    (div : d ∣ u) (big : D.sqrt < d)
    (size : (U.image (·%d)).card + (r-1)*(V.image (·%d)).card ≤ d+r-2) :
    (U.image (·%u)).card + (r-1)*(V.image (·%u)).card ≤ u+r*D.sqrt := by
  have pos : 0<d := by omega
  have liftU := OMA.Erdos13Cyclic.count_residue_fibers U hu pos div
  have liftV := Nat.mul_le_mul_left (r-1) (OMA.Erdos13Cyclic.count_residue_fibers V hu pos div)
  have ef := Nat.mul_le_mul_left (u/d) (show (U.image (·%d)).card + (r-1)*(V.image (·%d)).card ≤ d+r by omega)
  have cost : u/d ≤ D.sqrt := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul pos).mpr
    have hi := Nat.lt_succ_sqrt D
    have h := Nat.mul_le_mul_left (D.sqrt+1) big
    exact lt_of_le_of_lt ud (lt_of_lt_of_le hi h)
  have ec := Nat.mul_le_mul_right r cost
  have exactD := Nat.div_mul_cancel div
  nlinarith only [liftU,liftV,ef,ec,exactD]

lemma good_pivot {r u d e D : ℕ} (hr : 3 ≤ r) (hu : 0 < u) (ud : r*u ≤ D)
    (B : Finset ℕ) (layer : ∀ b ∈ B, b/u ∈ Icc 1 r)
    (dd : d ∣ u) (ed : e ∣ u) (dbig : D.sqrt<d) (ebig : D.sqrt<e)
    (s₁ : ((B.filter (·<2*u)).image (·%d)).card +
      (r-1)*(B.image (·%d)).card ≤ d+r-2)
    (s₂ : (B.image (·%e)).card +
      (r-1)*((B.filter (·<r*u)).image (·%e)).card ≤ e+r-2) :
    (r+1)*B.card+(D-r*u) ≤ D+r*(complete B u r).card + r*r*D.sqrt := by
  have ud' := (Nat.le_mul_of_pos_left u (by omega : 0<r)).trans ud
  have h1 := lift_mixed_size _ _ hu ud' dd dbig s₁
  have h2 := Nat.mul_le_mul_left (r-1) (lift_mixed_size _ _ hu ud' ed ebig s₂)
  have count := mixed_rows_count hr hu layer
  have ar : r-1+1=r := by omega
  have ar2 : 2*r-2=2*(r-1) := by omega
  have ez := congrArg (fun z : ℕ => z*(B.image (·%u)).card) ar2
  have eu := congrArg (fun z : ℕ => z*u) ar
  have ec := congrArg (fun z : ℕ => z*(r*D.sqrt)) ar
  nlinarith only [h1,h2,count,ez,eu,ec,Nat.sub_add_cancel ud]

end OMA.Erdos13MixedRows

end

section

/-  Selection of the first useful pivot in a bounded-multiplier annulus. -/

namespace OMA.Erdos13Mixed
open Finset FullColumns

private def Output (r D E : ℕ) (B : Finset ℕ) : Prop :=
  ∃ w ≤ D/(r+1), ∃ C : Finset ℕ, C ⊆ Icc 1 w ∧ Limited r C ∧
    (r+1)*B.card+w ≤ D+r*C.card+E*D.sqrt

private lemma clear {r D E : ℕ} {B : Finset ℕ} (bound : (r+1)*B.card≤D+E*D.sqrt) :
    Output r D E B :=
  ⟨0,Nat.zero_le _,∅,empty_subset _,by intro x hx; simp at hx,by simpa using bound⟩

private lemma pivot_output {r D u K : ℕ} {P : Finset ℕ} (hr : 3≤r)
    (shell : Erdos13ManyLayers.Shell r r K) (hD : 0<D) (sub : P ⊆ Icc 1 D)
    (lim : Limited r P) (hu : u∈P) (high : D/(r+1)<u) :
    Output r D (K+r*r) (P.filter (u<·)) ∨
      (r*u<D ∧ ∃ d, 0<d ∧ d≤D.sqrt ∧ d∣u ∧ ∀ v∈P, u<v → v<2*u → ¬d∣v) := by
  classical
  let B := P.filter (u<·)
  have bound : D < (r+1)*u := by
    simpa [mul_comm] using (Nat.div_lt_iff_lt_mul (by omega : 0<r+1)).mp high
  have u0 := (mem_Icc.mp (sub hu)).1
  have sq : 0<D.sqrt := Nat.sqrt_pos.mpr hD
  have within (x) (hx : x∈P) := (mem_Icc.mp (sub hx)).2
  have easy (band : ∀ b∈B,D≤r*b) : Output r D (K+r*r) B := by
    have inc : B⊆P := filter_subset _ _
    have bsub (b) (hb : b∈B) := mem_Icc.mp (sub (inc hb))
    have f := limited_free_shell inc (fun b hb => (bsub b hb).2) (fun b hb => by
      have h := Nat.mul_le_mul_left r (band b hb)
      rw [Nat.add_mul,one_mul,←Nat.mul_assoc] at *
      have pos := (bsub b hb).1
      omega) lim
    have h := shell D B (fun b hb => ⟨(bsub b hb).1,band b hb,(bsub b hb).2⟩) f
    apply clear
    have cost := Nat.le_mul_of_pos_right (K+r*r) sq
    omega
  by_cases already : D≤r*u
  · exact Or.inl (easy (fun b hb => already.trans (Nat.mul_le_mul_left _ (mem_filter.mp hb).2.le)))
  by_cases near : (B.filter (·<2*u)).Nonempty
  · rcases pair_or_small hr hu u0 bound.le within lim near with big|small
    · obtain ⟨d,e,db,dv,eb,ev,w₁,w₂⟩ := big
      have layer (b) (hb : b∈B) : b/u∈Icc 1 r := by
        have h := mem_filter.mp hb
        have bl := within _ h.1
        apply mem_Icc.mpr
        constructor
        · exact (Nat.le_div_iff_mul_le u0).mpr (by simpa using h.2.le)
        · have hdiv := (Nat.div_lt_iff_lt_mul u0).mpr (lt_of_le_of_lt bl bound)
          omega
      have comb := Erdos13MixedRows.good_pivot hr u0 (by omega : r*u≤D) B layer dv ev db eb w₁ w₂
      let C := complete B u r
      have memC (x) (hx : x∈C) : x∈Icc 1 (D-r*u) := by
        have lifts := (mem_filter.mp hx).2
        have lo := mem_filter.mp (lifts 1 (mem_Icc.mpr ⟨le_rfl,by omega⟩))
        have hi := within _ (mem_filter.mp (lifts r (mem_Icc.mpr ⟨by omega,le_rfl⟩))).1
        simp only [one_mul] at lo
        exact mem_Icc.mpr ⟨by omega,by omega⟩
      have wbound : D-r*u ≤ D/(r+1) := by
        apply (Nat.le_div_iff_mul_le (by omega : 0<r+1)).mpr
        have wu : D-r*u ≤ u := by rw [Nat.add_mul,one_mul] at bound; omega
        have a := Nat.mul_le_mul_right r wu
        rw [Nat.mul_add,Nat.mul_one]
        nlinarith only [a,Nat.sub_add_cancel (by omega : r*u≤D)]
      refine Or.inl ⟨_,wbound,C,fun _ hx => memC _ hx,limited_complete (by omega) (filter_subset _ _) lim,?_⟩
      change (r+1)*B.card+(D-r*u) ≤ D+r*(complete B u r).card+(K+r*r)*D.sqrt
      exact comb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right D.sqrt (by omega : r*r≤K+r*r)) _)
    · exact Or.inr ⟨by omega,small⟩
  · left
    apply easy
    intro b hb
    have blo : 2*u ≤ b := by
      by_contra! hn
      exact near ⟨b,mem_filter.mpr ⟨hb,hn⟩⟩
    have h := Nat.mul_le_mul_left r blo
    have ru := Nat.mul_le_mul_right u (show r+1≤2*r by omega)
    nlinarith only [bound,h,ru]

theorem mixed_annulus (r : ℕ) (hr : 3≤r) : ∃ E : ℕ, ∀ D : ℕ, 0<D → ∀ P : Finset ℕ,
    P ⊆ Icc 1 D → Limited r P → ∃ w≤D/(r+1), ∃ C : Finset ℕ, C ⊆ Icc 1 w ∧
      Limited r C ∧ (r+1)*(P.filter (D/(r+1)<·)).card+w ≤ D+r*C.card+E*D.sqrt := by
  classical
  obtain ⟨K,shell⟩ := Erdos13ManyLayers.shell_to_arity r hr
  let E := K+r*r
  refine ⟨E+2*(r+1),?_⟩
  intro D hD P sub lim
  let A := P.filter (D/(r+1)<·)
  let good (u : ℕ) := Output r D E (P.filter (u<·))
  let T := A.filter good
  let F := A.filter (fun u => ¬good u)
  have sq : 0<D.sqrt := Nat.sqrt_pos.mpr hD
  have loc {u} (hu : u∈F) := pivot_output hr shell hD sub lim
    (mem_filter.mp (mem_filter.mp hu).1).1 (mem_filter.mp (mem_filter.mp hu).1).2
  have data (u) (hu : u∈F) : r*u<D ∧ ∃ d, 0<d ∧ d≤D.sqrt ∧ d∣u ∧
      ∀ v∈P,u<v → v<2*u → ¬d∣v := (loc hu).resolve_left (mem_filter.mp hu).2
  choose d dp dt dv avoid using fun u : F => (data u u.property).2
  have distinct (u v : F) (lt : u.val<v.val) : d u ≠ d v := by
    intro eqn
    have hu := mem_filter.mp (mem_filter.mp u.property).1
    have hv := mem_filter.mp (mem_filter.mp v.property).1
    have low := (Nat.div_lt_iff_lt_mul (by omega : 0<r+1)).mp hu.2
    have hi := (data v v.property).1
    have short : v.val<2*u.val := by
      by_contra! big
      have h := Nat.mul_le_mul_left r big
      have z := Nat.mul_le_mul_left u.val (show r+1≤2*r by omega)
      nlinarith only [h,z,low,hi]
    exact avoid u v hv.1 lt short (eqn ▸ dv v)
  have inj : Function.Injective d := by
    intro u v eqn
    apply Subtype.ext
    rcases lt_trichotomy u.val v.val with h|h|h
    · exact (distinct u v h eqn).elim
    · exact h
    · exact (distinct v u h eqn.symm).elim
  have cost : F.card ≤ D.sqrt := by
    have h := Fintype.card_le_of_injective (fun u : F => (⟨d u,mem_Icc.mpr ⟨dp u,dt u⟩⟩ :
      {n // n∈Icc 1 D.sqrt})) (fun _ _ e => inj (congrArg Subtype.val e))
    simpa using h
  have part : T.card+F.card=A.card := A.card_filter_add_card_filter_not good
  have fee := Nat.mul_le_mul_left (r+1) cost
  by_cases ex : T.Nonempty
  · let u := T.min' ex
    have hu := T.min'_mem ex
    have gout : good u := (mem_filter.mp hu).2
    obtain ⟨w,hw,C,hc,cl,est⟩ := gout
    have inc : T ⊆ insert u (P.filter (u<·)) := by
      intro x hx
      have low : u≤x := T.min'_le x hx
      rcases eq_or_lt_of_le low with h|h
      · exact mem_insert.mpr (Or.inl h.symm)
      · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,h⟩))
    have sz := (card_le_card inc).trans (card_insert_le _ _)
    have big := Nat.mul_le_mul_left (r+1) sz
    have cover := congrArg (fun z => (r+1)*z) part
    have one := Nat.le_mul_of_pos_right (r+1) sq
    refine ⟨w,hw,C,hc,cl,?_⟩
    change (r+1)*A.card+w≤D+r*C.card+(E+2*(r+1))*D.sqrt
    nlinarith only [big,fee,cover,one,est]
  · have emp := not_nonempty_iff_eq_empty.mp ex
    rw [emp,card_empty,zero_add] at part
    apply clear
    change (r+1)*A.card≤D+(E+2*(r+1))*D.sqrt
    rw [←part]
    nlinarith only [fee,Nat.zero_le (E*D.sqrt),Nat.zero_le ((r+1)*D.sqrt),Nat.zero_le D]

end OMA.Erdos13Mixed

end

section

/-  Closing the square-root error recurrence for sets with bounded multipliers. -/
namespace OMA.Erdos13MixedRows
open Finset FullColumns

def AnnulusStep (r E : ℕ) : Prop :=
  ∀ (D : ℕ), 0<D → ∀ (P : Finset ℕ), P ⊆ Icc 1 D → Limited r P →
    ∃ w ≤ D/(r+1), ∃ C : Finset ℕ, C ⊆ Icc 1 w ∧ Limited r C ∧
      (r+1)*(P.filter (D/(r+1)<·)).card + w ≤ D+r*C.card+E*D.sqrt

lemma limited_sqrt_of_step {r E : ℕ} (hr : 3≤r) (step : AnnulusStep r E) :
    ∀ (D : ℕ) (P : Finset ℕ), P ⊆ Icc 1 D → Limited r P →
      r*P.card ≤ D + (2*r*E)*D.sqrt := by
  intro D
  induction D using Nat.strong_induction_on with
  | h D ih =>
    intro P sub lim
    by_cases dz : D=0
    · subst D
      have emp : P=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have := mem_Icc.mp (sub hx)
        omega
      simp [emp]
    let t := D/(r+1)
    let A := P.filter (fun x => ¬t<x)
    let B := P.filter (t<·)
    have dp : 0<D := by omega
    have tt : (r+1)*t ≤ D := by simpa [t,Nat.mul_comm] using Nat.div_mul_le_self D (r+1)
    have ts : t<D := Nat.div_lt_self dp (by omega)
    have subA : A ⊆ Icc 1 t := by
      intro x hx
      have h := mem_filter.mp hx
      have lo := (mem_Icc.mp (sub h.1)).1
      exact mem_Icc.mpr ⟨lo,by omega⟩
    have anc : A ⊆ P := filter_subset _ _
    have limA : Limited r A := fun x hx b hb lt => lim x (anc hx) b (fun i => anc (hb i)) lt
    have low := ih t ts A subA limA
    obtain ⟨w,wt,C,subC,limC,high⟩ := step D dp P sub lim
    change w≤t at wt
    change (r+1)*B.card+w ≤ D+r*C.card+E*D.sqrt at high
    have inner := ih w (wt.trans_lt ts) C subC limC
    have sw : w.sqrt ≤ t.sqrt := Nat.sqrt_le_sqrt wt
    have st : 2*t.sqrt ≤ D.sqrt := by
      apply Nat.le_sqrt.mpr
      have s := Nat.sqrt_le t
      have h := Nat.mul_le_mul_left 4 s
      have j := Nat.mul_le_mul_right t (show 4 ≤ r+1 by omega)
      nlinarith only [h,j,tt]
    have part : B.card+A.card=P.card := P.card_filter_add_card_filter_not (t<·)
    have eB := Nat.mul_le_mul_left r (show (r+1)*B.card ≤ D+(2*r*E)*w.sqrt+E*D.sqrt by omega)
    have eA := Nat.mul_le_mul_left (r+1) low
    have e1 := Nat.mul_le_mul_left (r*(2*r*E)) sw
    have e2 := Nat.mul_le_mul_left ((2*r+1)*(r*E)) st
    have total := congrArg (fun k : ℕ => (r+1)*r*k) part
    have fin : (r+1)*(r*P.card) ≤ (r+1)*(D+(2*r*E)*D.sqrt) := by
      nlinarith only [tt,eB,eA,e1,e2,total]
    exact Nat.le_of_mul_le_mul_left fin (by omega)
end OMA.Erdos13MixedRows

end

section

/-  A global density bound for the truncated family of divisibility constraints. -/
namespace OMA.Erdos13Mixed
open Finset FullColumns

theorem limited_sqrt_bound (r : ℕ) (hr : 3 ≤ r) :
    ∃ K, ∀ D (P : Finset ℕ), P ⊆ Icc 1 D → Limited r P →
      r*P.card ≤ D + K*D.sqrt := by
  obtain ⟨E,step⟩ := mixed_annulus r hr
  exact ⟨2*r*E,OMA.Erdos13MixedRows.limited_sqrt_of_step hr step⟩

theorem complete_sqrt_bound (r : ℕ) (hr : 3 ≤ r) :
    ∃ K, ∀ (D a : ℕ) (S A : Finset ℕ), S ⊆ A → Free r A →
      complete S a r ⊆ Icc 1 D → r*(complete S a r).card ≤ D + K*D.sqrt := by
  obtain ⟨K,h⟩ := limited_sqrt_bound r hr
  exact ⟨K,fun D a S A inc free sub => h D _ sub
    (limited_complete (by omega) inc (limited_of_free free))⟩

end OMA.Erdos13Mixed

end

section

namespace Erdos13ExtraRow
open Finset FullColumns OMA.Erdos13StrongResidues
open scoped Pointwise

/-- All short scalar images are distinct and stay outside the augmented r-fold sumset. -/
theorem packing {r a : ℕ} {A Q F : Finset ℕ} (hr : 4≤r) (ap : 0<a) (ha : a∈A)
    (strong : ∀ j,0<j → j≤r → Free j A)
    (off : ∀ y∈Q,y<a) (occ : ∀ y∈Q,almost r A a y)
    (sm : ∀ x∈F,0<x ∧ (4*r-1)*x<a) (allrow : ∀ x∈F,full r A a x) :
    r*Q.card+F.card+1≤a := by
  classical
  let : NeZero a := ⟨ap.ne'⟩
  let R := Q.image (fun y : ℕ => (y : ZMod a))
  let T := F.image (fun x : ℕ => (((4*r-1)*x : ℕ) : ZMod a))
  let S := r • insert 0 R
  have read {j : ℕ} {z : ZMod a} (hz : z ∈ j • R) :
      ∃ y : Fin j → ℕ, (∀ i,y i∈Q) ∧ ((∑ i,y i : ℕ) : ZMod a)=z := by
    obtain ⟨v,hv⟩ := mem_nsmul.mp hz
    have pre (i : Fin j) : ∃ y∈Q,(y : ZMod a) = v i := mem_image.mp (v i).property
    choose y hy eq using pre
    exact ⟨y,hy,by simpa [Nat.cast_sum,eq,List.sum_ofFn] using hv⟩
  have nozero (j : ℕ) (jp : 0<j) (jl : j≤r) : (0 : ZMod a)∉ j • R := by
    intro hz
    obtain ⟨y,hy,eq⟩ := read hz
    have pre (i : Fin j) : ∃ b∈A, a<b ∧ (b : ZMod a)=(y i : ZMod a) := by
      obtain ⟨m,hm⟩ := occ _ (hy i)
      let k := if m=2 then 3 else 2
      have km : k≠m := by dsimp [k]; split <;> omega
      have big : 2≤k ∧ k≤r+1 := by dsimp [k]; split <;> omega
      have le := Nat.mul_le_mul_right a big.1
      exact ⟨k*a+y i,hm k (mem_Icc.mpr ⟨by omega,big.2⟩) km,by omega,by simp⟩
    choose b hb bl be using pre
    apply strong j jp jl a ha b hb bl
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_sum,be] using (show (∑ i,(y i : ZMod a))=0 by simpa only [Nat.cast_sum] using eq)
  have sep : Disjoint S T := disjoint_left.mpr (by
    intro z hz ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    obtain ⟨j,jl,hj⟩ := some_nonzero_summands R r hz
    rcases j with _|j
    · have eqz : (((4*r-1)*x : ℕ) : ZMod a)=0 := by simpa using hj
      have div := (ZMod.natCast_eq_zero_iff _ _).mp eqz
      have small := (sm x hx).2
      exact (Nat.not_dvd_of_pos_of_lt (Nat.mul_pos (by omega) (sm x hx).1) small) div
    · obtain ⟨y,hy,eq⟩ := read hj
      exact small_multiple hr (by omega) jl (sm x hx).1 (sm x hx).2 (allrow x hx) (strong r (by omega) le_rfl) y
        (fun i=>off _ (hy i)) (fun i=>occ _ (hy i)) ((ZMod.natCast_eq_natCast_iff _ _ _).mp eq))
  have cR : R.card=Q.card := card_image_of_injOn (by
    intro x hx y hy eq
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (off x hx),Nat.mod_eq_of_lt (off y hy)] using congrArg ZMod.val eq)
  have cT : T.card=F.card := card_image_of_injOn (by
    intro x hx y hy eq
    have e := congrArg ZMod.val eq
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (sm x hx).2,Nat.mod_eq_of_lt (sm y hy).2] at e
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0<4*r-1) e)
  have big := growth_without_short_zero R (by omega : 0<r) nozero
  have cap := (S∪T).card_le_univ
  rw [card_union_of_disjoint sep,ZMod.card,cT] at cap
  change r*R.card+1≤S.card at big
  rw [cR] at big
  omega

end Erdos13ExtraRow

end

section

/-  A strict upper bound on a short final row for arbitrary arity. -/
namespace Erdos13ExtraRow
open Finset FullColumns

theorem tail_bound (r : ℕ) (hr : 4≤r) : ∃ K : ℕ, ∀ {a D : ℕ} {A : Finset ℕ}, 0<a →
    (4*r-1)*D<a → a∈A → (∀ j,0<j → j≤r → Free j A) → (∀ x∈A,x≤(r+1)*a+D) →
    r*r*(A.filter (a<·)).card≤r*r*a+(r-1)*D+K*D.sqrt := by
  classical
  obtain ⟨K,limited⟩ := OMA.Erdos13Mixed.limited_sqrt_bound r (by omega)
  refine ⟨(r-1)*K,?_⟩
  intro a D A ap short ha strong top
  let B := A.filter (a<·)
  let R := B.image (·%a)
  let I := Icc 1 (r+1)
  let L (u : ℕ) := I.filter (fun i=>i*a+u∈B)
  let Q := R.filter (fun u=>r≤(L u).card)
  let F := R.filter (fun u=>r+1≤(L u).card)
  have qi : Q⊆R := filter_subset _ _
  have fi : F⊆R := filter_subset _ _
  have ci : I.card=r+1 := by simp [I]
  have inc (u) : L u⊆I := filter_subset _ _
  have ls (u) : (L u).card≤r+1 := ci ▸ card_le_card (inc u)
  have off (u) (hu : u∈R) : 0<u ∧ u<a := by
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hu
    obtain ⟨yes,lt⟩ := mem_filter.mp hb
    refine ⟨?_,Nat.mod_lt _ ap⟩
    by_contra! zero
    have dv := Nat.dvd_of_mod_eq_zero (show b%a=0 by omega)
    exact strong 1 (by decide) (by omega) a ha (fun _=>b) (fun _=>yes) (fun _=>lt) (by simpa using dv)
  have fx (u) (hu : u∈F) : full r A a u := by
    have eq : L u=I := eq_of_subset_of_card_le (inc u) (by rw [ci]; exact (mem_filter.mp hu).2)
    exact fun i hi=>(mem_filter.mp ((mem_filter.mp (show i∈L u from eq ▸ hi)).2)).1
  have us (u) (hu : u∈F) : u≤D := by
    have := top _ (fx u hu (r+1) (mem_Icc.mpr ⟨by omega,le_rfl⟩))
    omega
  have qx (u) (hu : u∈Q) : almost r A a u := by
    have big := (mem_filter.mp hu).2
    by_cases whole : I⊆L u
    · exact ⟨0,fun i hi _=>(mem_filter.mp ((mem_filter.mp (whole hi)).2)).1⟩
    obtain ⟨m,mi,miss⟩ := not_subset.mp whole
    have incl : L u⊆I.erase m := fun i hi=>mem_erase.mpr ⟨fun e=>miss (e ▸ hi),inc u hi⟩
    have eh := card_erase_add_one mi
    have eq := eq_of_subset_of_card_le incl (by omega)
    exact ⟨m,fun i hi ne=>(mem_filter.mp ((mem_filter.mp (show i∈L u from eq ▸ mem_erase.mpr ⟨ne,hi⟩)).2)).1⟩
  have reserve := packing hr ap ha strong (fun u hu=>(off _ (qi hu)).2) qx
    (fun u hu=>⟨(off _ (fi hu)).1,(Nat.mul_le_mul_left _ (us _ hu)).trans_lt short⟩) fx
  have low := limited D F (fun u hu=>mem_Icc.mpr ⟨(off _ (fi hu)).1,us _ hu⟩)
    (limited_lifts (a:=a) (by omega : 0<r) (fun u hu j hj=>fx u hu j (mem_Icc.mpr
      ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans (by omega)⟩)) (limited_of_free (strong r (by omega) le_rfl)))
  have rcap : r*R.card+1≤a := OMA.Erdos13StrongResidues.tail_bound (by omega) ap ha strong
  have da : D<a := (Nat.le_mul_of_pos_left D (by omega : 0<4*r-1)).trans_lt short
  have fiber (u : ℕ) : (B.filter (fun b=>b%a=u)).card≤(L u).card := by
    apply (card_le_card (t:=(L u).image (fun i=>i*a+u)) ?_).trans card_image_le
    intro b h
    obtain ⟨hb,mod⟩ := mem_filter.mp h
    obtain ⟨hA,ab⟩ := mem_filter.mp hb
    have lo := Nat.div_pos ab.le ap
    have up : b/a<r+2 := (Nat.div_lt_iff_lt_mul ap).mpr (by
      have := top _ hA
      rw [show r+2=(r+1)+1 by omega,Nat.add_mul,Nat.one_mul]
      omega)
    have be : b/a*a+u=b := by rw [←mod,Nat.div_add_mod']
    exact mem_image.mpr ⟨b/a,mem_filter.mpr ⟨mem_Icc.mpr ⟨lo,by omega⟩,by rw [be]; exact hb⟩,be⟩
  have each (u) (hu : u∈R) : (B.filter (fun b=>b%a=u)).card≤(r-1)
      +(if u∈Q then 1 else 0)+(if u∈F then 1 else 0) := by
    have h := fiber u
    have l := ls u
    simp only [Q,F,mem_filter,hu,true_and]
    split_ifs <;> omega
  have cnt := sum_le_sum each
  rw [←card_eq_sum_card_image] at cnt
  simp only [sum_add_distrib,sum_const,Nat.nsmul_eq_mul,sum_ite,filter_mem_eq_inter,
    inter_eq_right.mpr qi,inter_eq_right.mpr fi,Nat.mul_one,mul_zero,add_zero] at cnt
  have bc := Nat.mul_le_mul_left r cnt
  have rr := Nat.mul_le_mul_left (r-1) rcap
  have dec : r-1+1=r := by omega
  have ar := congrArg (·*a) dec
  have fr := congrArg (·*F.card) dec
  have first : r*B.card≤r*a+(r-1)*F.card := by nlinarith only [bc,rr,reserve,ar,fr,Nat.zero_le (r-1)]
  have last := Nat.mul_le_mul_left r first
  have cost := Nat.mul_le_mul_left (r-1) low
  change r*r*B.card≤r*r*a+(r-1)*D+(r-1)*K*D.sqrt
  nlinarith only [last,cost]

end Erdos13ExtraRow

end

section

/-  Strict savings for the sparse terminal interval. -/
namespace OMA.Erdos13UpperShell
open Finset FullColumns ThirdStrip

lemma complete_strict {r a C D : ℕ} (hr : 3 ≤ r) {A P : Finset ℕ}
    (both : ∀ u ∈ P, ∀ k ∈ Icc 1 2, k*a+u ∈ A) (free : Free r A)
    (wide : ∀ (X : ℕ) (S : Finset ℕ), (∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) →
      Free r S → (r+1)*S.card ≤ X+C)
    (within : ∀ u ∈ P, u ≤ D) :
    25*P.card ≤ 12*D + 25*(100*(C+1)+1) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have inductionBound (X : ℕ) : 25*(F X).card ≤ 12*X + 25*(100*(C+1)+1) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ 100*(C+1)
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have hh := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        omega
      let t := if r = 3 then 11*X/24 else X/2
      have ht : t < X := by dsimp [t]; split_ifs <;> omega
      let S := (F X).filter fun x => t < x
      have data (x : ℕ) (hx : x ∈ S) :
          0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X ∧ r*X < (2*r+1)*x := by
        obtain ⟨hFx, htx⟩ := mem_filter.mp hx
        have hxX := (mem_filter.mp hFx).2
        by_cases h3 : r = 3
        · subst r
          simp only [t, if_true] at htx
          constructor
          · omega
          constructor
          · omega
          constructor
          · exact hxX
          · omega
        · simp only [t, if_neg h3] at htx
          have hX : X ≤ 2*x := by omega
          have hh := Nat.mul_le_mul_left r hX
          have hxpos : 0 < x := by omega
          exact ⟨hxpos, by nlinarith only [hh, Nat.zero_le X], hxX, by nlinarith only [hh, hxpos]⟩
      have incl : S ⊆ P := (filter_subset _ _).trans (filter_subset _ _)
      have count := wide X S (fun x hx => ⟨(data x hx).1, (data x hx).2.1, (data x hx).2.2.1⟩)
        (free_wider both free incl (fun x hx => ⟨(data x hx).1,(data x hx).2.2⟩))
      have balance : 25*S.card + 12*t ≤ 12*X := by
        by_cases h3 : r = 3
        · subst r
          simp only [t, if_true]
          omega
        · simp only [t, if_neg h3]
          have hc := Nat.mul_le_mul_right S.card (show 5 ≤ r+1 by omega)
          omega
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have eq : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F, mem_filter]
        constructor
        · rintro ⟨⟨hxP, _⟩, hxt⟩
          exact ⟨hxP, by omega⟩
        · rintro ⟨hxP, hxt⟩
          exact ⟨⟨hxP, by omega⟩, by omega⟩
      rw [eq] at part
      change S.card + (F t).card = (F X).card at part
      have tail := ih t ht
      omega
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using inductionBound D

lemma strip_strict_tail {r a N E C : ℕ} {A B : Finset ℕ} (hr : 3 ≤ r) (ha : 0 < a)
    (hain : a ∈ A) (lo : 2*a ≤ N) (hi : N ≤ 3*a) (subA : B ⊆ A)
    (sub : B ⊆ Ioc a N) (free : FullColumns.Free r A)
    (res : r*(B.image (·%a)).card ≤ a+E)
    (wide : ∀ (X : ℕ) (S : Finset ℕ), (∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) →
      FullColumns.Free r S → (r+1)*S.card ≤ X+C) :
    (24*(r+1)+1)*B.card ≤ 24*N+48*E+2*(25*(100*(C+1)+1)) := by
  classical
  let P := FullColumns.complete B a 2
  have completeLift (u : ℕ) (hu : u ∈ P) (k : ℕ) (hk : k ∈ Icc 1 2) :
      k*a+u ∈ B := (mem_filter.mp hu).2 k hk
  have bounds (u : ℕ) (hu : u ∈ P) : u ≤ N-2*a := by
    have := (mem_Ioc.mp (sub (completeLift u hu 2 (by decide)))).2
    omega
  have half := complete_strict hr
    (fun u hu k hk => subA (completeLift u hu k hk)) free wide bounds
  have layers (b : ℕ) (hb : b ∈ B) : b / a ∈ Icc 1 2 := by
    have mem := mem_Ioc.mp (sub hb)
    have strict : b < 3*a := by
      by_contra! hbr
      have eq : b = 3*a := by omega
      have dv : a ∣ b := eq ▸ dvd_mul_left _ _
      have hsum : a ∣ ∑ _i : Fin r, b := by
        simpa using dv.trans (dvd_mul_left b r)
      exact free a hain (fun _ => b) (fun _ => subA hb) (fun _ => mem.1) hsum
    refine mem_Icc.mpr ⟨Nat.div_pos mem.1.le ha, ?_⟩
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr strict)
  have count : B.card ≤ (B.image (·%a)).card + P.card := by
    simpa [P] using FullColumns.card_bound (B := B) (by decide : 0 < 2) layers
  have subR : P ⊆ B.image (·%a) := filter_subset _ _
  have single : B.card ≤ 2*(B.image (·%a)).card := by have := card_le_card subR; omega
  have enough : 25 ≤ 24*r := by omega
  have weighted := Nat.mul_le_mul_left (24*r-25) single
  have eq := Nat.sub_add_cancel enough
  have eqB := congrArg (fun n : ℕ => n*B.card) eq
  have eqR := congrArg (fun n : ℕ => n*(B.image (·%a)).card) eq
  have dec := Nat.sub_add_cancel lo
  nlinarith only [res, half, count, weighted, eqB, eqR, dec]

lemma third_large_strict {r a d N : ℕ} (hr : 3 ≤ r) (ha : N ≤ 3*a)
    (han : a ≤ N) (hd : 64*r < d) (large : 64 < a/d)
    (B : Finset ℕ) (hs : B ⊆ Ioc a N)
    (hres : r * (B.image (fun x => x%d)).card ≤ d + r - 2) :
    (24*(r+1)+1)*B.card ≤ 24*N+100*r := by
  have hpos : 0 < d := by omega
  have hD := (Nat.mul_le_mul_right d (show 64 ≤ a/d by omega)).trans (Nat.div_mul_le_self _ _)
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at hres
  have hres' : r*R.card ≤ d+r := by omega
  have lengthBound : 3*(N-a) ≤ 2*N := by omega
  let q := (N-a)/d
  have hq : q*d ≤ N-a := Nat.div_mul_le_self _ _
  have len : N-a < (q+1)*d := by
    rw [Nat.add_mul, Nat.one_mul]
    have := Nat.mod_add_div (N-a) d
    have := Nat.mod_lt (N-a) hpos
    change N-a < (N-a)/d*d + d
    rw [Nat.mul_comm ((N-a)/d) d]
    omega
  have cnt : B.card ≤ (q+1)*R.card := by
    apply count_residues_in_blocks hpos
    intro x hx
    have hb := mem_Ioc.mp (hs hx)
    exact mem_Ioc.mpr ⟨hb.1, by omega⟩
  have hc := Nat.mul_le_mul_left r cnt
  have hk := Nat.mul_le_mul_left (q+1) hres'
  have hqr := Nat.mul_le_mul_left q (show 64*r ≤ d by omega)

  have h3 := Nat.mul_le_mul_right B.card hr
  nlinarith only [hc, hk, hqr, hD, hq, han, lengthBound, h3, Nat.zero_le N, Nat.zero_le r]

lemma select_large_scaled {r t N L K : ℕ} (A : Finset ℕ)
    (positive : ∀ a ∈ A, 0 < a)
    (witness : ∀ a ∈ A, (A.filter fun x => a < x).Nonempty →
      ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2)
    (tail : ∀ a ∈ A, ∀ d : ℕ, L < d → d ∣ a →
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 →
      t*(A.filter fun x => a<x).card ≤ N+K) :
    t*A.card ≤ N + K + t*(L+1) := by
  classical
  have aw (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases ht : (A.filter fun x => a < x).Nonempty
    · exact witness a ha ht
    · rw [not_nonempty_iff_eq_empty] at ht
      refine ⟨a, positive a ha, dvd_refl _, ?_, by simp [ht]⟩
      intro b hb hlt
      have hmem : b ∈ (A.filter fun x => a < x) := mem_filter.mpr ⟨hb, hlt⟩
      simp [ht] at hmem
  choose! f pos div later size using aw
  let E := A.filter fun x => f x ≤ L
  have low : E.card ≤ L := by
    have hc : E.card ≤ (Icc 1 (L)).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1, h.2⟩
      · intro x hx y hy he
        have hxa := (mem_filter.mp hx).1
        have hya := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxa y hya h (he ▸ div y hya))
        · exact h
        · exact False.elim (later y hya x hxa h (he ▸ div x hxa))
    simpa using hc
  let G := A.filter fun x => L < f x
  by_cases non : G.Nonempty
  · let a := G.min' non
    have hag : a ∈ G := min'_mem _ _
    have hf := mem_filter.mp hag
    let B := A.filter fun x => a < x
    have ht : t*B.card ≤ N+K := tail a hf.1 (f a) hf.2 (div a hf.1) (size a hf.1)
    have cover : A ⊆ E ∪ insert a B := by
      intro x hx
      by_cases h : f x ≤ L
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have hxg : x ∈ G := mem_filter.mpr ⟨hx, by omega⟩
        have hax : a ≤ x := min'_le _ _ hxg
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cnt := (card_le_card cover).trans (card_union_le _ _)
    have ins := card_insert_le a B
    have hcard : A.card ≤ L+1+B.card := by omega
    have := Nat.mul_le_mul_left (r+1) hcard
    nlinarith only [this, ht]
  · have cover : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact non ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left (r+1) ((card_le_card cover).trans low)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r, Nat.zero_le K]



lemma sparse_upper_strict {r m a E : ℕ} (hr : 3 ≤ r) (A B : Finset ℕ)
    (subA : B ⊆ A) (sub : B ⊆ Ioc a ((r+1)*m))
    (sparse : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m)
    (num : r*B.card ≤ a+E) :
    (24*(r+1)+1)*B.card ≤ 24*((r+1)*m)+25*E := by
  classical
  let T := Ioc (r*m) ((r+1)*m) ∩ A
  change 2*T.card ≤ m at sparse
  by_cases low : a ≤ r*m
  · have incl : B ⊆ Ioc a (r*m) ∪ T := by
      intro x hx
      have hx' := mem_Ioc.mp (sub hx)
      by_cases h : x ≤ r*m
      · exact mem_union_left _ (mem_Ioc.mpr ⟨hx'.1,h⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨mem_Ioc.mpr ⟨by omega,hx'.2⟩,subA hx⟩)
    have bound := (card_le_card incl).trans (card_union_le _ _)
    rw [Nat.card_Ioc] at bound
    have delta := Nat.sub_add_cancel low
    have cap : (r+1)*B.card ≤ (r+1)*(m+E) := by
      nlinarith only [bound, delta, sparse, num, Nat.zero_le m, Nat.zero_le (r*E)]
    have sml : B.card ≤ m+E := Nat.le_of_mul_le_mul_left cap (by omega)
    nlinarith only [bound, delta, sparse, num, sml, Nat.zero_le m]
  · have incl : B ⊆ T := by
      intro x hx
      have hx' := mem_Ioc.mp (sub hx)
      exact mem_inter.mpr ⟨mem_Ioc.mpr ⟨by omega,hx'.2⟩,subA hx⟩
    have hB : 2*B.card ≤ m := (Nat.mul_le_mul_left 2 (card_le_card incl)).trans sparse
    have mul := Nat.mul_le_mul_left r hB
    nlinarith only [hB, mul, Nat.zero_le m, Nat.zero_le E]

theorem stability_third {r m : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ (r+1)*m ≤ 3*a ∧ a ≤ (r+1)*m)
    (free : Free r A) (sparse : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m) :
    (24*(r+1)+1)*A.card ≤ 24*((r+1)*m) +
      (3072*r + 2*(25*(100*((r+1)*(16*r+1)+32*r+1)+1))) +
      (24*(r+1)+1)*(64*r+1) := by
  classical
  let N := (r+1)*m
  have pos (a) (ha : a ∈ A) := (sub a ha).1
  apply select_large_scaled A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a hain d hd hdvd hres
  let B := A.filter fun x => a < x
  change (24*(r+1)+1)*B.card ≤ 24*N+_
  have hBA : B ⊆ A := filter_subset _ _
  have hB : B ⊆ Ioc a N := by
    intro x hx
    have hf := mem_filter.mp hx
    exact mem_Ioc.mpr ⟨hf.2,(sub x hf.1).2.2⟩
  have apos := pos a hain
  have ha : N ≤ 3*a := (sub a hain).2.1
  have han : a ≤ N := (sub a hain).2.2
  by_cases large : 64 < a/d
  · have := third_large_strict hr ha han hd large B hB hres
    omega
  have reduced := OMA.Erdos13Cyclic.residue_bound_of_quotient B apos (by omega : 0<d) hdvd hres
  have hR := reduced.trans (Nat.add_le_add_left (Nat.mul_le_mul_right r (show a/d≤64 by omega)) a)
  by_cases upper : N ≤ 2*a
  · have cnt : B.card ≤ (B.image (fun x => x%a)).card := by
      have hI : B ⊆ Ioc a (a+1*a) := by
        intro x hx
        have hx' := mem_Ioc.mp (hB hx)
        exact mem_Ioc.mpr ⟨hx'.1, by omega⟩
      simpa only [Nat.one_mul] using count_residues_in_blocks apos hI
    have h := sparse_upper_strict hr A B hBA hB sparse ((Nat.mul_le_mul_left r cnt).trans hR)
    change (24*(r+1)+1)*B.card ≤ 24*N+25*(64*r) at h
    omega
  · have w (X : ℕ) (S : Finset ℕ)
        (hs : ∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) (hf : Free r S) :
        (r+1)*S.card ≤ X+((r+1)*(16*r+1)+32*r) := by
      simpa only [Nat.add_assoc] using OMA.Erdos13Cyclic.wide_shell hr S hs hf
    have h := strip_strict_tail hr apos hain (by omega : 2*a ≤ N) ha hBA hB free hR w
    convert h using 1 <;> ring

end OMA.Erdos13UpperShell

end

section

/-  A strict saving for sparse terminal intervals with every element at least N/r. -/

namespace OMA.Erdos13ManyLayers
open Finset FullColumns OMA.Erdos13UpperShell

lemma gap_factor_strict {r J : ℕ} (hJ : 3 ≤ J) (hr : J < r) :
    (4*J+1)*J + 4*(r+1) + 1 ≤ 4*J*(r+1) := by
  have de : r-(J+1)+(J+1)=r := by omega
  have hj1 : J-1+1=J := by omega
  have e1 := congrArg (fun z : ℕ => J*z) de
  have e2 := congrArg (fun z : ℕ => z*(r-(J+1))) hj1
  nlinarith only [hJ,de,hj1,e1,e2,Nat.zero_le ((J-1)*(r-(J+1)))]

lemma pay_shell_strict {r J X C t b : ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (cap : (r+1)*b ≤ X+C) (round : J*t ≤ X) (big : J*(4*J+1)*C ≤ X) :
    (4*J+1)*b+4*t ≤ 4*X := by
  have hcap := Nat.mul_le_mul_left (J*(4*J+1)) cap
  have hround := Nat.mul_le_mul_left (4*(r+1)) round
  have factor := Nat.mul_le_mul_right X (gap_factor_strict hJ hr)
  have hcombine : J*(r+1)*((4*J+1)*b+4*t) ≤ J*(r+1)*(4*X) := by
    nlinarith only [hcap, hround, factor, big]
  exact Nat.le_of_mul_le_mul_left hcombine (by positivity)

lemma complete_bound_strict {r a J C D : ℕ} (hJ : 3 ≤ J) (hr : J < r) {A P : Finset ℕ}
    (allLifts : ∀ u ∈ P, ∀ k ∈ Icc 1 J, k*a+u ∈ A) (free : Free r A)
    (prev : Shell r J C) (within : ∀ u ∈ P, u ≤ D) :
    (4*J+1)*P.card ≤ 4*D + (4*J+1)*(J*(4*J+1)*C+1) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have step (X : ℕ) : (4*J+1)*(F X).card ≤ 4*X + (4*J+1)*(J*(4*J+1)*C+1) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ J*(4*J+1)*C
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        have := Nat.mul_le_mul_left (4*J+1) (show (F X).card ≤ J*(4*J+1)*C+1 by omega)
        omega
      let t := X/J
      have ht : t < X := Nat.div_lt_self (by omega) (by omega)
      let S := P.filter fun u => u ≤ X ∧ X < J*u
      have bound := prev X S (by
        intro x hx
        have h := (mem_filter.mp hx).2
        have hp : 0 < x := by
          by_contra! hz
          simp [show x=0 by omega] at h
        exact ⟨hp,h.2.le,h.1⟩) (free_shell (by omega : 0<J) allLifts free X)
      have envelope := pay_shell_strict hJ hr bound (Nat.mul_div_le X J) (le_of_not_ge small)
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have hiff (x : ℕ) : t<x ↔ X<J*x := by
        dsimp [t]
        rw [Nat.div_lt_iff_lt_mul (by omega : 0<J), Nat.mul_comm]
      have eq₁ : ((F X).filter fun x => t<x) = S := by
        ext x
        simp only [F,S,mem_filter,hiff]
        tauto
      have eq₂ : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F,mem_filter]
        constructor
        · rintro ⟨⟨hx, _⟩, hs⟩
          exact ⟨hx, by omega⟩
        · rintro ⟨hx, hs⟩
          exact ⟨⟨hx, by omega⟩, by omega⟩
      rw [eq₁,eq₂] at part
      have hi := ih t ht
      have hparts := congrArg (fun k => (4*J+1)*k) part
      change (4*J+1)*S.card + 4*t ≤ 4*X at envelope
      rw [Nat.mul_add] at hparts
      omega
  have h := step D
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using h


lemma layers_count_strict {r J N a E K R P B : ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (lo : J*a ≤ N) (imageBound : r*R ≤ a+E) (fullSub : P ≤ R)
    (fullBound : (4*J+1)*P ≤ 4*(N-J*a)+K) (count : B ≤ (J-1)*R+P) :
    (4*J*(r+1)+1)*B ≤ 4*J*N+4*J*J*E+J*K := by
  have sub : J-1+1=J := by omega
  have subR := congrArg (fun k : ℕ => k*R) sub
  have single : B ≤ J*R := by nlinarith only [count,fullSub,subR]
  let H := 4*J*r
  let L := (4*J+1)*(J-1)
  have hL : L ≤ H := by
    have hjr := Nat.mul_le_mul_left (4*J) hr.le
    have hjj := congrArg (fun k : ℕ => (4*J+1)*k) sub
    dsimp [L,H]
    nlinarith only [hjr,hjj,Nat.zero_le J]
  have dec := Nat.sub_add_cancel lo
  have hdc := congrArg (fun n : ℕ => 4*J*n) dec
  have cb := Nat.mul_le_mul_left (J*(4*J+1)) count
  have fb := Nat.mul_le_mul_left J fullBound
  have rb := Nat.mul_le_mul_left (4*J*J) imageBound
  have mult := Nat.mul_le_mul_left (H-L) single
  have e := Nat.sub_add_cancel hL
  have eB := congrArg (fun n : ℕ => n*B) e
  have eR := congrArg (fun n : ℕ => n*J*R) e
  have sj := congrArg (fun k : ℕ => (4*J+1)*k*B) sub
  dsimp [H,L] at mult eB eR
  nlinarith only [cb,fb,rb,mult,eB,eR,sj,hdc]
lemma layer_tail_strict {r J a N E C : ℕ} {A B : Finset ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (ha : 0 < a) (hain : a ∈ A) (lo : J*a ≤ N) (hi : N ≤ (J+1)*a)
    (subA : B ⊆ A) (sub : B ⊆ Ioc a N) (free : Free r A)
    (imageBound : r*(B.image (·%a)).card ≤ a+E) (prev : Shell r J C) :
    (4*J*(r+1)+1)*B.card ≤ 4*J*N+4*J*J*E+J*((4*J+1)*(J*(4*J+1)*C+1)) := by
  classical
  let P := FullColumns.complete B a J
  have completeLift (u : ℕ) (hu : u ∈ P) (k : ℕ) (hk : k ∈ Icc 1 J) :
      k*a+u ∈ B := (mem_filter.mp hu).2 k hk
  have bounds (u) (hu : u ∈ P) : u ≤ N-J*a := by
    have := (mem_Ioc.mp (sub (completeLift u hu J (mem_Icc.mpr ⟨by omega,le_rfl⟩)))).2
    omega
  have last := complete_bound_strict hJ hr
    (fun u hu k hk => subA (completeLift u hu k hk)) free prev bounds
  have layers (b : ℕ) (hb : b ∈ B) : b / a ∈ Icc 1 J := by
    have mem := mem_Ioc.mp (sub hb)
    have strict : b < (J+1)*a := by
      by_contra! hbr
      have eq : b = (J+1)*a := by omega
      have dv : a ∣ b := eq ▸ dvd_mul_left _ _
      have hsum : a ∣ ∑ _i : Fin r, b := by
        simpa using dv.trans (dvd_mul_left b r)
      exact free a hain (fun _ => b) (fun _ => subA hb) (fun _ => mem.1) hsum
    refine mem_Icc.mpr ⟨Nat.div_pos mem.1.le ha, ?_⟩
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr strict)
  have subR : P ⊆ B.image (·%a) := filter_subset _ _
  exact layers_count_strict hJ hr lo imageBound (card_le_card subR) last
    (FullColumns.card_bound (by omega : 0<J) layers)

lemma medium_quotient_strict {r a d N : ℕ} (hr : 3 ≤ r) (han : a ≤ N) (shell : N ≤ r*a)
    (hd : 4*r*r*(r+1) < d) (large : 4*(r+1) < a/d)
    (B : Finset ℕ) (sub : B ⊆ Ioc a N)
    (quot : r * (B.image (fun x => x%d)).card ≤ d+r-2) :
    (2*r*r*(r+1)+1)*B.card ≤ 2*r*r*N+2*r*r*(r+1) := by
  classical
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at quot
  let t := (N-a)/d
  have hdpos : 0 < d := by omega
  have hperiod : t*d ≤ N-a := Nat.div_mul_le_self _ _
  have dsmall := (Nat.mul_le_mul_right d large.le).trans (Nat.div_mul_le_self _ _)
  have hMul : t*(4*r*r*(r+1)) ≤ r*a := by
    exact (Nat.mul_le_mul_left t hd.le).trans (hperiod.trans (by omega))
  have htr : t*(4*r*(r+1)) ≤ a := by
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0<r)
    convert hMul using 1 <;> ring
  have len : N-a < (t+1)*d := by
    rw [Nat.succ_mul]
    have rem := Nat.mod_add_div (N-a) d
    have hrem := Nat.mod_lt (N-a) hdpos
    dsimp [t]
    rw [Nat.mul_comm ((N-a)/d) d]
    omega
  have count : B.card ≤ (t+1)*R.card := by
    apply OMA.Erdos13UpperShell.count_residues_in_blocks hdpos
    intro x hx
    have h := mem_Ioc.mp (sub hx)
    exact mem_Ioc.mpr ⟨h.1, by omega⟩
  have hcount := Nat.mul_le_mul_left r count
  have qbound := Nat.mul_le_mul_left (t+1) (show r*R.card ≤ d+r by omega)
  have hbase : r*B.card ≤ N-a+d+t*r+r := by
    nlinarith only [hcount,qbound,hperiod]
  have L := Nat.mul_le_mul_left (r+1) hbase
  have dec := congrArg (fun z : ℕ => (r+1)*z) (Nat.sub_add_cancel han)
  have hl : 2*r*((r+1)*B.card)+a ≤ 2*r*N+2*r*(r+1) := by
    nlinarith only [L,dec,htr,dsmall,shell]
  have length := card_le_card sub
  rw [Nat.card_Ioc] at length
  have card : B.card ≤ r*a := by omega
  have scaled := Nat.mul_le_mul_left r hl
  nlinarith only [card,scaled]


lemma lift_gain {r M t N C D b : ℕ} (le : t ≤ M) (major : (r+1)*b ≤ N+C)
    (strict : (t*(r+1)+1)*b ≤ t*N+D) :
    (M*(r+1)+1)*b ≤ M*N+(D+M*C) := by
  have mult := Nat.mul_le_mul_left (M-t) major
  have h := Nat.sub_add_cancel le
  have hb := congrArg (fun k : ℕ => k*(r+1)*b) h
  have hn := congrArg (fun k : ℕ => k*N) h
  have hc := Nat.mul_le_mul_right C (Nat.sub_le M t)
  nlinarith only [mult,strict,hb,hn,hc]

/-- A uniform positive gap below the conjectured density when the top m
integers are at most half occupied and the set is supported above N/r. -/
theorem sparse_top_stability_scaled (r M : ℕ) (hr : 3 ≤ r) (base : 24 ≤ M)
    (medium : 2*r*r ≤ M) (layers : 4*r ≤ M) :
    ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 0 < a ∧ (r+1)*m ≤ r*a ∧ a ≤ (r+1)*m) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
      (M*(r+1)+1)*A.card ≤ M*((r+1)*m)+K := by
  classical
  obtain ⟨C, prev⟩ := shell_to_arity r hr
  let D₃ := (3072*r + 2*(25*(100*((r+1)*(16*r+1)+32*r+1)+1))) +
    (24*(r+1)+1)*(64*r+1)
  let L := 4*r*r*(r+1)
  let E := 4*(r+1)*r
  let Dm := 2*r*r*(r+1)
  let Dj := 4*r*r*E+r*((4*r+1)*(r*(4*r+1)*C+1))
  let D := D₃+Dm+Dj
  refine ⟨D+M*C+(M*(r+1)+1)*(L+1), ?_⟩
  intro m A sub free sparse
  let N := (r+1)*m
  have pos (a) (ha : a ∈ A) := (sub a ha).1
  change (M*(r+1)+1)*A.card ≤ M*N+(D+M*C+(M*(r+1)+1)*(L+1))
  rw [← Nat.add_assoc (M*N)]
  apply select_large_scaled A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a hain d hd hdvd quot
  let B := A.filter fun x => a < x
  change (M*(r+1)+1)*B.card ≤ M*N+(D+M*C)
  have hBA : B ⊆ A := filter_subset _ _
  have hB : B ⊆ Ioc a N := fun x hx => mem_Ioc.mpr
    ⟨(mem_filter.mp hx).2,(sub x (hBA hx)).2.2⟩
  have freeB : Free r B := fun x hx b hb => free _ (hBA hx) b (fun i => hBA (hb i))
  have major := prev N B (fun x hx => sub x (hBA hx)) freeB
  have ha := pos a hain
  have han : a ≤ N := (sub a hain).2.2
  have span : N ≤ r*a := (sub a hain).2.1
  by_cases third : N ≤ 3*a
  · have sub3 (x) (hx : x ∈ B) : 0 < x ∧ N ≤ 3*x ∧ x ≤ N := by
      have h := mem_Ioc.mp (hB hx)
      exact ⟨pos x (hBA hx),by omega,h.2⟩
    have card := card_le_card (inter_subset_inter (Subset.rfl (s := Ioc (r*m) N)) hBA)
    have sp : 2*(Ioc (r*m) N ∩ B).card ≤ m := (Nat.mul_le_mul_left 2 card).trans sparse
    have strong : (24*(r+1)+1)*B.card ≤ 24*N+D₃ := by
      simpa only [N,D₃,Nat.add_assoc] using stability_third hr B sub3 freeB sp
    apply lift_gain base major
    exact strong.trans (Nat.add_le_add_left (by dsimp [D]; omega) _)
  by_cases big : 4*(r+1) < a/d
  · have strong := medium_quotient_strict hr han span hd big B hB quot
    apply lift_gain medium major
    exact strong.trans (Nat.add_le_add_left (by dsimp [D,Dm]; omega) _)
  · let J := (N-1)/a
    have hJ : 3 ≤ J := by
      apply (Nat.le_div_iff_mul_le ha).mpr
      omega
    have Jlt : J < r := by
      apply (Nat.div_lt_iff_lt_mul ha).mpr
      omega
    have hLo : J*a ≤ N := (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
    have hi : N ≤ (J+1)*a := by
      have ex := Nat.mod_add_div (N-1) a
      have rem := Nat.mod_lt (N-1) ha
      change N ≤ ((N-1)/a+1)*a
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm ((N-1)/a) a]
      omega
    have dpos : 0 < d := by omega
    have fiber := OMA.Erdos13Cyclic.residue_bound_of_quotient B ha dpos hdvd quot
    have rB := fiber.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right r (show a/d ≤ 4*(r+1) by omega)) a)
    have prevJ : Shell r J C := by
      intro X S hS f
      exact prev X S (fun x hx => ⟨(hS x hx).1,(hS x hx).2.1.trans
        (Nat.mul_le_mul_right x Jlt.le),(hS x hx).2.2⟩) f
    have est := layer_tail_strict hJ Jlt ha hain hLo hi hBA hB free rB prevJ
    have leM := (Nat.mul_le_mul_left 4 Jlt.le).trans layers
    apply lift_gain leM major
    have num : 4*J*J*E+J*((4*J+1)*(J*(4*J+1)*C+1)) ≤ Dj := by
      dsimp [Dj]
      gcongr <;> omega
    change (4*J*(r+1)+1)*B.card ≤ 4*J*N+4*J*J*E+J*((4*J+1)*(J*(4*J+1)*C+1)) at est
    dsimp [D]
    omega


/-- A uniform positive gap below the conjectured density when the top m
integers are at most half occupied and the set is supported above N/r. -/
theorem sparse_top_stability (r : ℕ) (hr : 3 ≤ r) :
    ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 0 < a ∧ (r+1)*m ≤ r*a ∧ a ≤ (r+1)*m) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
      (24*r*r*(r+1)+1)*A.card ≤ 24*r*r*((r+1)*m)+K := by
  apply sparse_top_stability_scaled
  · exact hr
  · nlinarith [Nat.mul_le_mul hr hr]
  · gcongr <;> decide
  · have h := Nat.mul_le_mul_right r (show 1≤r by omega)
    nlinarith only [h,Nat.zero_le (r*r)]

end OMA.Erdos13ManyLayers

end

section

/-  Complete residue lifts prohibit further congruences among offsets. -/

namespace Erdos13ColumnModulo
open Finset

lemma allocate_mixed (m : ℕ) (l u : Fin m → ℕ) (k : ℕ)
    (each : ∀ i, l i ≤ u i) (low : ∑ i, l i ≤ k) (high : k ≤ ∑ i, u i) :
    ∃ f : Fin m → ℕ, (∀ i, l i ≤ f i ∧ f i ≤ u i) ∧ ∑ i, f i = k := by
  induction m generalizing k with
  | zero => exact ⟨fun i => i.elim0,fun i => i.elim0,by simpa [eq_comm] using high⟩
  | succ m ih =>
    let x := min (u 0) (k-∑ i : Fin m, l i.succ)
    rw [Fin.sum_univ_succ] at low high
    have part_bound : (∑ i : Fin m, l i.succ) ≤ ∑ i : Fin m, u i.succ :=
      sum_le_sum fun i _ => each i.succ
    have tail := ih (fun i => l i.succ) (fun i => u i.succ) (k-x) (fun i => each i.succ)
      (by dsimp [x]; omega) (by dsimp [x]; omega)
    obtain ⟨f,hf,hs⟩ := tail
    refine ⟨Fin.cons x f, Fin.forall_fin_succ.mpr ⟨?_,?_⟩,?_⟩
    · simp only [Fin.cons_zero]
      have := each 0
      dsimp [x]
      omega
    · simpa using hf
    · simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hs]
      dsimp [x]
      omega

lemma next_dilate {r a : ℕ} {A P : Finset ℕ} (hr : 3 ≤ r)
    (off : ∀ u ∈ P, 0 < u ∧ u < a)
    (lifts : ∀ u ∈ P, ∀ j ∈ Icc 1 r, j*a+u ∈ A)
    (free : FullColumns.Free r A) (u : ℕ) (hu : u ∈ P)
    (v : Fin r → ℕ) (hv : ∀ i, v i ∈ P) :
    ¬ (∑ i, v i) ≡ (r+1)*u [MOD a] := by
  classical
  intro eqmod
  obtain ⟨c,hc⟩ := Nat.modEq_iff_dvd.mp eqmod
  let n := (univ.filter (fun i : Fin r => v i ≤ u)).card
  have nc : n ≤ r := by simpa [n] using card_filter_le (s := (univ : Finset (Fin r))) (fun i => v i ≤ u)
  have sum_cap : (∑ i, v i) ≤ n*u+(r-n)*(a-1) := by
    have loc (i : Fin r) : v i ≤ if v i ≤ u then u else a-1 := by
      split
      · assumption
      · have := (off _ (hv i)).2
        omega
    have h := sum_le_sum (s := (univ : Finset (Fin r))) (fun i _ => loc i)
    have count := (univ : Finset (Fin r)).card_filter_add_card_filter_not (fun i => v i ≤ u)
    simp only [card_univ,Fintype.card_fin] at count
    simpa only [sum_ite,sum_const,nsmul_eq_mul, Nat.cast_id,
      show #(univ.filter fun i : Fin r => ¬ v i ≤ u) = r-n by dsimp [n]; omega] using h
  have small : (∑ i, v i) + n*a < (r+1)*u+r*a := by
    have nd := Nat.sub_add_cancel nc
    have ru := Nat.mul_le_mul_right u nc
    have aux := congrArg (fun z : ℕ => z*a) nd
    have xpos := (off u hu).1
    nlinarith only [sum_cap,ru,aux,xpos,Nat.mul_le_mul_left (r-n) (Nat.sub_le a 1)]
  have pos := (off u hu).1
  have ua := (off u hu).2
  have ksmall : (r+1)*u < (r+1)*a := Nat.mul_lt_mul_of_pos_left ua (by omega)
  push_cast at hc
  have cmin : (n:ℤ) - r < c := by
    by_contra! hn
    have hz := mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg a)
    zify at small
    nlinarith only [hc,hz,small]
  have cmax : c < (r+1:ℕ) := by
    by_contra! hn
    have hz := mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg a)
    zify at ksmall
    have nn : (0:ℤ) ≤ ∑ i,(v i:ℤ) := sum_nonneg (fun i _ => Int.natCast_nonneg _)
    push_cast at hz
    nlinarith only [hc,hz,ksmall,nn]
  let h := max 1 ((n:ℤ)-c).toNat
  have h1 : 1 ≤ h := le_max_left _ _
  have hlow : (n:ℤ) ≤ (h:ℤ)+c := by
    have hh := le_max_right 1 ((n:ℤ)-c).toNat
    change _ ≤ h at hh
    omega
  have hcap : h ≤ r-1 := by dsimp [h]; omega
  have heither : h=1 ∨ (h:ℤ)=(n:ℤ)-c := by dsimp [h]; omega
  have upper : (((r+1)*h:ℕ):ℤ)+c ≤ (r*r:ℕ) := by
    rcases heither with h₁|h₂
    · rw [h₁,Nat.mul_one]
      have bound : 2*r+1 ≤ r*r := by nlinarith [Nat.mul_le_mul_left r hr]
      omega
    · have z := Nat.mul_le_mul_left r hcap
      have rr : r*(r-1)=r*r-r := by rw [Nat.mul_sub,Nat.mul_one]
      have rt := Nat.le_mul_self r
      zify at z nc ⊢
      have succ : (r:ℤ)-1=(r-1:ℕ) := by omega
      push_cast at *
      nlinarith only [z,nc,h₂,succ]
  let K := (((r+1)*h:ℕ)+c).toNat
  have Kint : (K:ℤ)=((r+1)*h:ℕ)+c := by
    apply Int.toNat_of_nonneg
    rw [Nat.add_mul,Nat.one_mul]
    push_cast
    nlinarith only [hlow,Int.natCast_nonneg n, mul_nonneg (Int.natCast_nonneg r) (Int.natCast_nonneg h)]
  let l (i : Fin r) := h + if v i ≤ u then 1 else 0
  have lsum : ∑ i,l i = r*h+n := by simp [l,sum_add_distrib,n]
  have minK : ∑ i,l i ≤ K := by
    rw [lsum]
    have id : (r+1)*h=r*h+h := by ring
    omega
  obtain ⟨f,hf,hfs⟩ := allocate_mixed r l (fun _ => r) K
    (fun i => by dsimp [l]; split <;> omega) minK (by simpa using (show K ≤ r*r by omega))
  have base := lifts u hu h (mem_Icc.mpr ⟨h1,by omega⟩)
  apply free _ base (fun i => f i*a+v i)
  · intro i
    apply lifts _ (hv i) _ (mem_Icc.mpr ⟨?_,(hf i).2⟩)
    have o := (hf i).1
    dsimp [l] at o
    split at o <;> omega
  · intro i
    have o := (hf i).1
    dsimp [l] at o
    split at o
    · have F := Nat.mul_le_mul_right a o
      have := (off _ hu).2
      rw [Nat.add_mul,Nat.one_mul] at F
      omega
    · have F := Nat.mul_le_mul_right a o
      simp only [Nat.add_zero] at F
      omega
  · refine ⟨r+1,?_⟩
    rw [sum_add_distrib,←sum_mul,hfs]
    zify at Kint hc ⊢
    push_cast at *
    nlinarith only [Kint,hc]

end Erdos13ColumnModulo

end

section

/-  Allocation of a divisor height for modular relations of intermediate arity. -/
namespace Erdos13ColumnModulo

lemma choose_base {r j n : ℕ} (hr : 3 ≤ r) (hj : 0 < j) (nc : n ≤ r)
    (top : 2*(r+j) ≤ r*r+1) (c : ℤ)
    (cl : (n:ℤ)-r < c) (cu : c < (r+j:ℕ)) :
    ∃ h : ℕ, 1 ≤ h ∧ h < r ∧
      (n:ℤ) ≤ j*h+c ∧ (((r+j)*h:ℕ):ℤ)+c ≤ (r*r:ℕ) := by
  by_cases simple : (n:ℤ) ≤ j+c
  · refine ⟨1,le_rfl,by omega,by simpa using simple,?_⟩
    rw [Nat.mul_one]
    omega
  let m := ((n:ℤ)-c).toNat
  have mval : (m:ℤ)=(n:ℤ)-c := by dsimp [m]; omega
  have mcap : m < r := by omega
  have jm : j < m := by omega
  let h := (m-1)/j+1
  have hmin : (h-1)*j < m := by
    have bound := Nat.div_mul_le_self (m-1) j
    dsimp [h]
    exact lt_of_le_of_lt bound (Nat.sub_lt (lt_trans hj jm) (by decide))
  have hmax : m ≤ h*j := by
    have rem := Nat.mod_add_div (m-1) j
    have lt := Nat.mod_lt (m-1) hj
    dsimp [h]
    rw [Nat.add_mul,Nat.one_mul]
    rw [mul_comm j _] at rem
    omega
  have h1 : 1 ≤ h := Nat.succ_pos _
  have hdec : h-1+1=h := by omega
  have part := congrArg (fun z : ℕ => z*j) hdec
  have hm : h ≤ m := by
    have h := Nat.mul_le_mul_left (h-1) hj
    rw [Nat.mul_one] at h
    omega
  have min : (n:ℤ) ≤ j*h+c := by
    rw [Nat.mul_comm] at hmax
    zify at hmax
    omega
  refine ⟨h,h1,by omega,min,?_⟩
  have extra : h*j ≤ m+j-1 := by nlinarith only [hmin, part, Nat.sub_add_cancel (show 1 ≤ m+j by omega)]
  by_cases one : j=1
  · subst j
    simp only [Nat.mul_one,Nat.add_sub_cancel] at extra
    have z := Nat.mul_le_mul_left r (show h ≤ r-1 by omega)
    have dec : r-1+1=r := by omega
    have ident := congrArg (fun x : ℕ => r*x) dec
    zify at extra nc z ident ⊢
    nlinarith only [z,ident,extra,mval,nc]
  · have h2 := Nat.mul_le_mul_left (h-1) (show 2≤j by omega)
    have bound : 2*h≤r+1 := by omega
    have cap : h ≤ r-2 := by omega
    have z := Nat.mul_le_mul_left r cap
    have dec : r-2+2=r := by omega
    have ident := congrArg (fun x : ℕ => r*x) dec
    have extra' : h*j ≤ m+j := by omega
    zify at extra' nc z ident jm mcap ⊢
    nlinarith only [z,ident,extra',nc,jm,mcap,mval]
end Erdos13ColumnModulo

end

section

/-  A complete column rules out dilate relations across an interval of multipliers. -/
namespace Erdos13ColumnModulo
open Finset

lemma dilate_range {r a j : ℕ} {A P : Finset ℕ} (hr : 3 ≤ r) (hj : 0 < j) (top : 2*(r+j) ≤ r*r+1)
    (off : ∀ u ∈ P, 0 < u ∧ u < a)
    (lifts : ∀ u ∈ P, ∀ j ∈ Icc 1 r, j*a+u ∈ A)
    (free : FullColumns.Free r A) (u : ℕ) (hu : u ∈ P)
    (v : Fin r → ℕ) (hv : ∀ i, v i ∈ P) :
    ¬ (∑ i, v i) ≡ (r+j)*u [MOD a] := by
  classical
  intro eqmod
  obtain ⟨c,hc⟩ := Nat.modEq_iff_dvd.mp eqmod
  let n := (univ.filter (fun i : Fin r => v i ≤ u)).card
  have nc : n ≤ r := by simpa [n] using card_filter_le (s := (univ : Finset (Fin r))) (fun i => v i ≤ u)
  have sum_cap : (∑ i, v i) ≤ n*u+(r-n)*(a-1) := by
    have loc (i : Fin r) : v i ≤ if v i ≤ u then u else a-1 := by
      split
      · assumption
      · have := (off _ (hv i)).2
        omega
    have h := sum_le_sum (s := (univ : Finset (Fin r))) (fun i _ => loc i)
    have count := (univ : Finset (Fin r)).card_filter_add_card_filter_not (fun i => v i ≤ u)
    simp only [card_univ,Fintype.card_fin] at count
    simpa only [sum_ite,sum_const,nsmul_eq_mul, Nat.cast_id,
      show #(univ.filter fun i : Fin r => ¬ v i ≤ u) = r-n by dsimp [n]; omega] using h
  have small : (∑ i, v i) + n*a < (r+j)*u+r*a := by
    have nd := Nat.sub_add_cancel nc
    have ru := Nat.mul_le_mul_right u nc
    have aux := congrArg (fun z : ℕ => z*a) nd
    have xpos := (off u hu).1
    have uj := Nat.mul_le_mul_right u hj
    nlinarith only [sum_cap,ru,aux,xpos,uj,Nat.mul_le_mul_left (r-n) (Nat.sub_le a 1)]
  have pos := (off u hu).1
  have ua := (off u hu).2
  have ksmall : (r+j)*u < (r+j)*a := Nat.mul_lt_mul_of_pos_left ua (by omega)
  push_cast at hc
  have cmin : (n:ℤ) - r < c := by
    by_contra! hn
    have hz := mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg a)
    zify at small
    nlinarith only [hc,hz,small]
  have cmax : c < (r+j:ℕ) := by
    by_contra! hn
    have hz := mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg a)
    zify at ksmall
    have nn : (0:ℤ) ≤ ∑ i,(v i:ℤ) := sum_nonneg (fun i _ => Int.natCast_nonneg _)
    push_cast at hz
    nlinarith only [hc,hz,ksmall,nn]
  obtain ⟨h,h1,hcap,hlow,upper⟩ := choose_base hr hj nc top c cmin cmax
  let K := (((r+j)*h:ℕ)+c).toNat
  have Kint : (K:ℤ)=((r+j)*h:ℕ)+c := by
    apply Int.toNat_of_nonneg
    rw [Nat.add_mul]
    push_cast
    nlinarith only [hlow,Int.natCast_nonneg n, mul_nonneg (Int.natCast_nonneg r) (Int.natCast_nonneg h)]
  let l (i : Fin r) := h + if v i ≤ u then 1 else 0
  have lsum : ∑ i,l i = r*h+n := by simp [l,sum_add_distrib,n]
  have minK : ∑ i,l i ≤ K := by
    rw [lsum]
    have id : (r+j)*h=r*h+j*h := by ring
    zify at id ⊢
    push_cast at Kint
    omega
  obtain ⟨f,hf,hfs⟩ := allocate_mixed r l (fun _ => r) K
    (fun i => by dsimp [l]; split <;> omega) minK (by simpa using (show K ≤ r*r by omega))
  have base := lifts u hu h (mem_Icc.mpr ⟨h1,by omega⟩)
  apply free _ base (fun i => f i*a+v i)
  · intro i
    apply lifts _ (hv i) _ (mem_Icc.mpr ⟨?_,(hf i).2⟩)
    have o := (hf i).1
    dsimp [l] at o
    split at o <;> omega
  · intro i
    have o := (hf i).1
    dsimp [l] at o
    split at o
    · have F := Nat.mul_le_mul_right a o
      have := (off _ hu).2
      rw [Nat.add_mul,Nat.one_mul] at F
      omega
    · have F := Nat.mul_le_mul_right a o
      simp only [Nat.add_zero] at F
      omega
  · refine ⟨r+j,?_⟩
    rw [sum_add_distrib,←sum_mul,hfs]
    zify at Kint hc ⊢
    push_cast at *
    nlinarith only [Kint,hc]

end Erdos13ColumnModulo

end

section

/-  Density estimates for complete columns in an aperiodic cyclic quotient. -/
namespace Erdos13ColumnModulo
open Finset
open scoped Pointwise

lemma coprime_scalar {q k : ℕ} (cop : k.Coprime q) :
    Function.Injective (fun x : ZMod q => k • x) := by
  intro x y h
  simpa only [nsmul_eq_mul] using ((ZMod.isUnit_iff_coprime k q).mpr cop).mul_right_inj.mp
    (show (k : ZMod q)*x = k*y by simpa [nsmul_eq_mul] using h)

lemma twice_card {q : ℕ} [NeZero q] (R : Finset (ZMod q)) :
    R.card ≤ 2*(R.image (fun x => 2 • x)).card := by
  let f (x : ZMod q) := (2 • x,2*x.val/q)
  let T := R.image (fun x => 2 • x) ×ˢ range 2
  have incl (x : ZMod q) (hx : x ∈ R) : f x ∈ T := by
    apply mem_product.mpr
    exact ⟨mem_image_of_mem _ hx,mem_range.mpr ((Nat.div_lt_iff_lt_mul (NeZero.pos q)).mpr
      (Nat.mul_lt_mul_of_pos_left x.val_lt (by decide)))⟩
  have inject (x : ZMod q) : (2 • x).val = (2*x.val)%q := by
    have eq : (2 • x : ZMod q) = ((2*x.val:ℕ):ZMod q) := by
      simp [nsmul_eq_mul]
    rw [eq,ZMod.val_natCast]
  have count := card_le_card_of_injOn f incl (by
    intro x hx y hy he
    have h₁ := congrArg (fun t : ZMod q × ℕ => t.1.val) he
    have h₂ := congrArg Prod.snd he
    change (2 • x).val = (2 • y).val at h₁
    change 2*x.val/q = 2*y.val/q at h₂
    rw [inject,inject] at h₁
    have xq := Nat.mod_add_div (2*x.val) q
    have yq := Nat.mod_add_div (2*y.val) q
    rw [h₁,h₂] at xq
    exact ZMod.val_injective q (by omega))
  simpa [T,Nat.mul_comm] using count

lemma cyclic_estimates {q r k L : ℕ} [NeZero q] (hr : 2 ≤ r)
    (R : Finset (ZMod q)) (hne : R.Nonempty)
    (aper : (r • R).addStab = {0})
    (cop : k.Coprime q) (low : r < k) (high : 2*k ≤ r+L)
    (excluded : ∀ x ∈ R, ∀ j ∈ Ioc r (r+L), j • x ∉ r • R) :
    r*R.card+L ≤ q+(r-1) ∧
    (r+1)*R.card+(R.card+1)/2 ≤ q+(r-1) ∧
    (2 ∣ k → (r+2)*R.card ≤ q+(r-1)) ∧
    ((2:ℕ).Coprime q → (r+2)*R.card ≤ q+(r-1)) := by
  classical
  let S := r • R
  have growth : r*R.card ≤ S.card+(r-1) := by
    have h := Finset.card_nsmul_bound (r:=r) (by omega) R hne
    rwa [aper,card_singleton,Nat.mul_one] at h
  have pair (T : Finset (ZMod q)) (disj : Disjoint S T) : S.card+T.card ≤ q := by
    have count := (S∪T).card_le_univ
    rwa [card_union_of_disjoint disj,ZMod.card] at count
  obtain ⟨x,hx⟩ := hne
  have orde : L < addOrderOf x := by
    have pos := addOrderOf_pos x
    by_contra! h
    have bad := excluded x hx (r+addOrderOf x) (mem_Ioc.mpr ⟨by omega,by omega⟩)
    rw [add_nsmul,addOrderOf_nsmul_eq_zero,add_zero] at bad
    exact bad (nsmul_mem_nsmul hx)
  let f (i : ℕ) := (r+1+i) • x
  have E := pair ((range L).image f) (disjoint_left.mpr (by
    intro y hy h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    have := mem_range.mp hi
    exact excluded x hx _ (mem_Ioc.mpr ⟨by omega,by omega⟩) hy))
  have cardF : ((range L).image f).card=L := by
    rw [card_image_of_injOn,card_range]
    intro i hi j hj eq
    have same := (nsmul_eq_nsmul_iff_modEq.mp eq).add_left_cancel' (r+1)
    have iord := (mem_range.mp hi).trans orde
    have jord := (mem_range.mp hj).trans orde
    simpa [Nat.ModEq,Nat.mod_eq_of_lt iord,Nat.mod_eq_of_lt jord] using same
  rw [cardF] at E
  let U := R.image (fun z => k • z)
  let D := R.image (fun z => 2 • z)
  let V := D.image (fun z => k • z)
  have ci := coprime_scalar cop
  have cu : U.card=R.card := card_image_of_injective _ ci
  have cv : V.card=D.card := card_image_of_injective _ ci
  have uv : Disjoint U V := disjoint_left.mpr (by
    intro z hu hv
    obtain ⟨x,hx,hxz⟩ := mem_image.mp hu
    obtain ⟨w,hw,hwz⟩ := mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hw
    have eq : x=2 • y := ci (hxz.trans hwz.symm)
    have forbid := excluded y hy (r+1) (mem_Ioc.mpr ⟨by omega,by omega⟩)
    apply forbid
    have rp : r-1+1=r := by omega
    have o := Finset.add_mem_add (nsmul_mem_nsmul (n:=r-1) hy) hx
    rw [eq,←add_nsmul,←succ_nsmul,rp] at o
    simpa [show r-1+2=r+1 by omega] using o)
  have pack := pair (U∪V) (disjoint_left.mpr (by
    intro z hz h
    rcases mem_union.mp h with hu|hv
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
      exact excluded x hx k (mem_Ioc.mpr ⟨low,by omega⟩) hz
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
      rw [←mul_nsmul] at hz
      exact excluded x hx _ (mem_Ioc.mpr ⟨by omega,high⟩) hz))
  rw [card_union_of_disjoint uv,cu,cv] at pack
  have half := twice_card R
  change R.card ≤ 2*D.card at half
  have full (odd : (2:ℕ).Coprime q) : (r+2)*R.card ≤ q+(r-1) := by
    have dd : D.card=R.card := card_image_of_injective _ (coprime_scalar odd)
    rw [dd] at pack
    nlinarith only [growth,pack]
  refine ⟨by omega,?_,fun d => full (cop.of_dvd_left d),full⟩
  rw [Nat.add_mul,Nat.one_mul]
  omega

lemma packing_arithmetic {r q s k L : ℕ} (hr : 5 ≤ r)
    (low : r < k) (high : 2*k ≤ r+L)
    (full_range : 2*(r+L) ≤ r*r+1 ∧ r*r+1 < 2*(r+L+1))
    (one : r*s+L ≤ q+(r-1)) (two : (r+1)*s+(s+1)/2 ≤ q+(r-1))
    (evenK : 2 ∣ k → (r+2)*s ≤ q+(r-1))
    (oddQ : (2:ℕ).Coprime q → (r+2)*s ≤ q+(r-1)) :
    (r+1)*s ≤ q := by
  have large (hh : 2*(r-1) ≤ s+1) : (r+1)*s ≤ q := by omega
  have small (hh : s+r-1 ≤ L) : (r+1)*s ≤ q := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  by_cases rr : 7 ≤ r
  · have d : r-7+7=r := by omega
    have z := Nat.mul_le_mul_left (r-7) (show 8 ≤ r+1 by omega)
    have Lb : 3*r ≤ L+4 := by
      obtain ⟨_,b⟩ := full_range
      nlinarith only [d,z,b]
    by_cases h : 2*(r-1) ≤ s+1
    · exact large h
    · exact small (by omega)
  · interval_cases r
    · have h6 : k=6 := by omega
      have stronger := evenK (h6 ▸ by decide)
      omega
    · by_cases h : 10 ≤ s+1
      · exact large (by omega)
      by_cases hh : s ≤ 7
      · exact small (by omega)
      by_contra! bad
      have v : q=55 := by omega
      have stronger := oddQ (v ▸ by decide)
      omega

/-- An aperiodic cyclic quotient admitting an invertible k with both k and
2k in the prohibited multiplier interval has density at most 1/(r+1). -/
theorem good_cyclic_packing {q r k L : ℕ} [NeZero q] (hr : 5 ≤ r)
    (R : Finset (ZMod q)) (hne : R.Nonempty)
    (aper : (r • R).addStab = {0}) (cop : k.Coprime q)
    (low : r < k) (high : 2*k ≤ r+L)
    (full_range : 2*(r+L) ≤ r*r+1 ∧ r*r+1 < 2*(r+L+1))
    (excluded : ∀ x ∈ R, ∀ j ∈ Ioc r (r+L), j • x ∉ r • R) :
    (r+1)*R.card ≤ q := by
  obtain ⟨a,b,c,d⟩ := cyclic_estimates (by omega) R hne aper cop low high excluded
  exact packing_arithmetic hr low high full_range a b c d

end Erdos13ColumnModulo

end

section

/-  Reduction of modular complete-column constraints to an aperiodic cyclic group. -/
namespace Erdos13ColumnModulo
open Finset
open scoped Pointwise

theorem reduce_columns {r a L : ℕ} (ha : 0 < a) (P : Finset ℕ) (hne : P.Nonempty)
    (excl : ∀ u ∈ P, ∀ j ∈ Ioc r (r+L), ∀ v : Fin r → ℕ,
      (∀ i,v i ∈ P) → ¬ (∑ i,v i) ≡ j*u [MOD a]) :
    ∃ q : ℕ, ∃ hq : 0 < q, q ∣ a ∧
      let R := P.image (fun x : ℕ => (x : ZMod q))
      (r • R).addStab = {0} ∧
        ∀ x ∈ R, ∀ j ∈ Ioc r (r+L), j • x ∉ r • R := by
  classical
  let : NeZero a := ⟨ha.ne'⟩
  let B := P.image (fun x : ℕ => (x : ZMod a))
  let S := r • B
  have hB : B.Nonempty := hne.image _
  have hS : S.Nonempty := hB.nsmul
  let H := AddAction.stabilizer (ZMod a) (S : Set (ZMod a))
  let Q := ZMod a ⧸ H
  let π := QuotientAddGroup.mk' H
  let g : Q := π 1
  let q := Nat.card Q
  let : Fintype Q := Fintype.ofFinite _
  have hq : 0 < q := by dsimp [q]; rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos
  let : NeZero q := ⟨hq.ne'⟩
  have generates (x : Q) : x ∈ AddSubgroup.zmultiples g := by
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective H x
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(z.val : ℤ),?_⟩
    rw [natCast_zsmul]
    change z.val • π 1 = π z
    rw [←map_nsmul]
    simp [nsmul_eq_mul]
  let e : ZMod q ≃+ Q := zmodAddEquivOfGenerator generates rfl
  let p := e.symm.toAddMonoidHom.comp π
  have p1 : p 1 = 1 := zmodAddEquivOfGenerator_symm_apply_generator generates rfl
  have pn (x : ℕ) : p (x : ZMod a) = (x : ZMod q) := by
    calc
      p (x : ZMod a) = p (x • (1 : ZMod a)) := by simp [nsmul_eq_mul]
      _ = x • p 1 := map_nsmul _ _ _
      _ = x := by rw [p1]; simp [nsmul_eq_mul]
  have surj : Function.Surjective p := e.symm.surjective.comp (QuotientAddGroup.mk'_surjective H)
  have fix (z : ZMod a) : z ∈ H ↔ z +ᵥ S = S := by
    change z ∈ AddAction.stabilizer (ZMod a) (S : Set (ZMod a)) ↔ _
    rw [AddAction.mem_stabilizer_iff,←Finset.coe_vadd_finset,Finset.coe_inj]
  have sat (z : ZMod a) : p z ∈ S.image p ↔ z ∈ S := by
    refine ⟨?_,mem_image_of_mem _⟩
    intro hz
    obtain ⟨y,hy,hEq⟩ := mem_image.mp hz
    have eqπ : π y = π z := e.symm.injective hEq
    have hmem : z-y ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp eqπ.symm
    have hfix := vadd_mem_vadd_finset (a := z-y) hy
    rw [(fix _).mp hmem] at hfix
    simpa [vadd_eq_add] using hfix
  let R := P.image (fun x : ℕ => (x : ZMod q))
  have mapped : S.image p = r • R := by
    have m : B.image p = R := by
      dsimp [B,R]
      rw [image_image]
      exact image_congr fun x _ => pn x
    exact (Finset.image_nsmul p B r).trans (congrArg (r • ·) m)
  refine ⟨q,hq,?_,?_,?_⟩
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp [←pn a]
  · ext w
    change w ∈ (r • R).addStab ↔ _
    rw [←mapped,mem_singleton,mem_addStab (hS.image _)]
    constructor
    · obtain ⟨z,rfl⟩ := surj w
      intro hw
      have hz : z ∈ H := (fix _).mpr (by
        apply Finset.eq_of_subset_of_card_le _ (by simp)
        intro v hv
        obtain ⟨y,hy,rfl⟩ := mem_vadd_finset.mp hv
        apply (sat _).mp
        have h := vadd_mem_vadd_finset (a:=p z) (mem_image_of_mem p hy)
        rw [hw] at h
        simpa [vadd_eq_add] using h)
      have hzero := (QuotientAddGroup.eq_zero_iff z).mpr hz
      change e.symm (π z)=0
      rw [show π z =0 from hzero,map_zero]
    · rintro rfl
      simp
  · intro x hx j hj hjx
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    change j • (u : ZMod q) ∈ r • R at hjx
    rw [←mapped,←pn u,←map_nsmul,sat] at hjx
    obtain ⟨v,hv⟩ := Finset.mem_nsmul.mp hjx
    have rep (i : Fin r) : ∃ w ∈ P, (w : ZMod a)=(v i:ZMod a) := mem_image.mp (v i).property
    choose b hb be using rep
    apply excl u hu j hj b hb
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [Nat.cast_sum,Nat.cast_mul]
    simpa [List.sum_ofFn,be,nsmul_eq_mul] using hv

end Erdos13ColumnModulo

end

section

/-  Geometric estimate for the boundary case of r complete layers. -/
namespace Erdos13ColumnModulo
open Finset FullColumns OMA.Erdos13ManyLayers

lemma pay_critical {r Fct b t X C : ℕ} (hr : 3 ≤ r) (hF : Fct+1=4*(r-1)*(r+1))
    (cap : (r+1)*b ≤ X+C) (round : r*t ≤ X) (large : Fct*C ≤ X) :
    Fct*b+4*r*t ≤ 4*r*X := by
  have dec : r-1+1=r := by omega
  have id := congrArg (fun k : ℕ => 4*k*(r+1)) dec
  have hround := Nat.mul_le_mul_left (4*(r+1)) round
  have hcap := Nat.mul_le_mul_left Fct cap
  have hX := congrArg (fun k : ℕ => k * X) hF
  have dX := congrArg (fun k : ℕ => k * X) id
  have h : (r+1)*(Fct*b+4*r*t) ≤ (r+1)*(4*r*X) := by
    nlinarith only [hcap,hround,hX,dX,large]
  exact Nat.le_of_mul_le_mul_left h (by omega)

lemma complete_critical {r a C D Fct : ℕ} (hr : 3 ≤ r) (hF : Fct+1=4*(r-1)*(r+1))
    {A P : Finset ℕ} (allLifts : ∀ u ∈ P, ∀ k ∈ Icc 1 r, k*a+u ∈ A)
    (free : Free r A) (prev : Shell r r C) (within : ∀ u ∈ P, u ≤ D) :
    Fct*P.card ≤ 4*r*D + Fct*(Fct*C+1) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have step (X : ℕ) : Fct*(F X).card ≤ 4*r*X + Fct*(Fct*C+1) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ Fct*C
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        have := Nat.mul_le_mul_left Fct (show (F X).card ≤ Fct*C+1 by omega)
        omega
      let t := X/r
      have ht : t < X := Nat.div_lt_self (by omega) (by omega)
      let S := P.filter fun u => u ≤ X ∧ X < r*u
      have bound := prev X S (by
        intro x hx
        have h := (mem_filter.mp hx).2
        have hp : 0 < x := by
          by_contra! hz
          simp [show x=0 by omega] at h
        exact ⟨hp,h.2.le,h.1⟩) (free_shell (by omega : 0<r) allLifts free X)
      have envelope := pay_critical (r:=r) hr hF bound (Nat.mul_div_le X r) (le_of_not_ge small)
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have hiff (x : ℕ) : t<x ↔ X<r*x := by
        dsimp [t]
        rw [Nat.div_lt_iff_lt_mul (by omega : 0<r), Nat.mul_comm]
      have eq₁ : ((F X).filter fun x => t<x) = S := by
        ext x
        simp only [F,S,mem_filter,hiff]
        tauto
      have eq₂ : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F,mem_filter]
        constructor
        · rintro ⟨⟨hx, _⟩, hs⟩
          exact ⟨hx, by omega⟩
        · rintro ⟨hx, hs⟩
          exact ⟨⟨hx, by omega⟩, by omega⟩
      rw [eq₁,eq₂] at part
      have hi := ih t ht
      have hparts := congrArg (fun k => Fct*k) part
      change Fct*S.card + 4*r*t ≤ 4*r*X at envelope
      rw [Nat.mul_add] at hparts
      omega
  have h := step D
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using h


end Erdos13ColumnModulo

end

section

namespace Erdos13HalfOccupied

open Finset

/-- Count a set in consecutive periods and in the last partial period. -/
lemma count_by_period (q t s : ℕ) (hs : s ≤ q) (R : Finset ℕ) :
    ∀ (v : ℕ) (B : Finset ℕ), B ⊆ Ico v (v + (t * q + s)) →
      (∀ b ∈ B, b % q ∈ R) → B.card ≤ t * R.card + min s R.card := by
  classical
  have one (v : ℕ) (B : Finset ℕ) (hI : B ⊆ Ico v (v+q))
      (hR : ∀ b ∈ B, b % q ∈ R) : B.card ≤ R.card := by
    apply card_le_card_of_injOn (fun x : ℕ => x % q) hR
    exact (Nat.mod_injOn_Ico v q).mono (by exact_mod_cast hI)
  induction t with
  | zero =>
    intro v B hI hR
    simp only [Nat.zero_mul, Nat.zero_add] at hI ⊢
    apply le_min
    · have := card_le_card hI
      simpa using this
    · apply one v B _ hR
      exact hI.trans (Ico_subset_Ico_right (by omega))
  | succ t ih =>
    intro v B hI hR
    let P := B.filter (fun b => b < v+q)
    let Q := B.filter (fun b => ¬b < v+q)
    have hP : P.card ≤ R.card := by
      apply one v P
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Ico.mpr ⟨(mem_Ico.mp (hI h.1)).1, h.2⟩
      · intro x hx
        exact hR x (mem_filter.mp hx).1
    have hQ : Q.card ≤ t * R.card + min s R.card := by
      apply ih (v+q) Q
      · intro x hx
        have h := mem_filter.mp hx
        have hi := mem_Ico.mp (hI h.1)
        rw [Nat.succ_mul] at hi
        exact mem_Ico.mpr ⟨by omega, by omega⟩
      · intro x hx
        exact hR x (mem_filter.mp hx).1
    have hab := B.card_filter_add_card_filter_not (fun b => b < v+q)
    change P.card + Q.card = B.card at hab
    rw [Nat.succ_mul]
    omega

/-- A period q with at most (q+1)/3 occupied classes cannot support a
strict majority for two full periods, once q exceeds four. For one full
period, its length is forced to lie within one of three quarters of m. -/
lemma small_period_or_near {m q c b : ℕ} (hq : 0 < q)
    (hqm : q ≤ m) (he : 3*c ≤ q+1) (major : m < 2*b)
    (cap : b ≤ (m / q) * c + min (m % q) c) :
    q ≤ 4 ∨ (3*m / 4 - 2 ≤ q ∧ q ≤ 3*m / 4 + 2) := by
  by_cases hsmall : q ≤ 4
  · exact Or.inl hsmall
  right
  let t := m/q
  let s := m%q
  have dec : s + t*q = m := by
    dsimp [s, t]
    simpa only [Nat.mul_comm] using Nat.mod_add_div m q
  have hs : s < q := Nat.mod_lt _ hq
  have hcap : b ≤ t*c + min s c := cap
  have ht : t ≤ 1 := by
    by_contra! high
    have h2c : 2*c ≤ q := by omega
    have hdiff : 2*(q-2*c) ≤ t*(q-2*c) := Nat.mul_le_mul_right _ high
    rw [Nat.mul_sub] at hdiff
    have aux : t*(2*c) ≤ t*q := Nat.mul_le_mul_left t h2c
    have ident : t*(2*c) = 2*(t*c) := by ring
    have hd : t*(q-2*c) = t*q-t*(2*c) := Nat.mul_sub _ _ _
    have hmin : 2*min s c ≤ s+c := by omega
    omega
  have hone : t = 1 := Nat.le_antisymm ht (Nat.div_pos hqm hq)
  rw [hone, Nat.one_mul] at dec hcap
  omega

/-- All but boundedly many possible divisors force the selected small element
above r times the size of the upper interval, up to r-2. -/
lemma force_large_divisor {r m q a v : ℕ} (hr : 3 ≤ r) (hq : 0 < q)
    (hqa : q ≤ a) (B : Finset ℕ) (hB : B ⊆ Ico v (v+m))
    (major : m < 2*B.card)
    (quotient : r * (B.image (fun x => x%q)).card ≤ q + r - 2) :
    q ∈ range 5 ∪ Icc (3*m / 4 - 2) (3*m / 4 + 2) ∨
      (m < q ∧ r*B.card ≤ a+r-2) := by
  classical
  let R := B.image (fun x => x%q)
  have hR (b) (hb : b ∈ B) : b%q ∈ R := mem_image_of_mem _ hb
  change r * R.card ≤ q+r-2 at quotient
  by_cases hqm : q ≤ m
  · left
    have h3 : 3 * R.card ≤ q + 1 := by
      by_cases hc : R.card = 0
      · simp [hc]
      have hr3 := Nat.mul_le_mul_right (R.card-1) hr
      rw [Nat.mul_sub, Nat.mul_sub] at hr3
      have hrc : r ≤ r*R.card := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left r (show 1 ≤ R.card by omega)
      omega
    have rem := Nat.mod_add_div m q
    have dec : m / q * q + m % q = m := by
      simpa only [Nat.mul_comm, Nat.add_comm] using rem
    have hI : B ⊆ Ico v (v + (m/q*q + m%q)) := by simpa only [dec] using hB
    have cap := count_by_period q (m/q) (m%q) (Nat.mod_lt _ hq).le R v B hI hR
    rcases small_period_or_near hq hqm h3 major cap with h | h
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · exact mem_union_right _ (mem_Icc.mpr h)
  · right
    refine ⟨by omega, ?_⟩
    have hinj : (B : Set ℕ).InjOn (fun x => x % q) := by
      apply (Nat.mod_injOn_Ico v q).mono
      intro b hb
      have := mem_Ico.mp (hB hb)
      exact mem_Ico.mpr ⟨this.1, by omega⟩
    have heq : R.card = B.card := card_image_of_injOn hinj
    rw [heq] at quotient
    omega

lemma exceptional_card (m : ℕ) :
    (range 5 ∪ Icc (3*m/4-2) (3*m/4+2)).card ≤ 10 := by
  have h := card_union_le (range 5) (Icc (3*m/4-2) (3*m/4+2))
  simp only [card_range, Nat.card_Icc] at h
  omega

/-- The chosen quotient for the smaller of two elements cannot also divide
the larger element. Therefore all exceptional quotients cost at most ten
elements of a finite set, even when the quotients vary along the set. -/
lemma exceptional_elements (A : Finset ℕ) (f : ℕ → ℕ) (m : ℕ)
    (divides : ∀ a ∈ A, f a ∣ a)
    (only_here : ∀ a ∈ A, ∀ b ∈ A, a < b → ¬ f a ∣ b) :
    (A.filter (fun a => f a ∈ range 5 ∪ Icc (3*m/4-2) (3*m/4+2))).card ≤ 10 := by
  classical
  refine le_trans (card_le_card_of_injOn f ?_ ?_) (exceptional_card m)
  · intro a ha
    exact (mem_filter.mp ha).2
  · intro a ha b hb hfb
    have ha' := (mem_filter.mp ha).1
    have hb' := (mem_filter.mp hb).1
    rcases lt_trichotomy a b with h | h | h
    · exact False.elim (only_here a ha' b hb' h (hfb.symm ▸ divides b hb'))
    · exact h
    · exact False.elim (only_here b hb' a ha' h (hfb ▸ divides a ha'))

end Erdos13HalfOccupied

end

section

/-  The boundary strip from r to r+1 layers for a pivot coprime to an allowed multiplier. -/
namespace Erdos13ColumnModulo
open Finset FullColumns OMA.Erdos13ManyLayers
open scoped Pointwise

lemma integral_margin {q r s : ℕ} (hr : 5 ≤ r)
    (large : (6*r+8)*r ≤ q) (half : (r+1)*s+(s+1)/2 ≤ q+(r-1)) :
    (3*(r+1)+1)*s ≤ 3*q := by
  by_cases hs : s < 6*r
  · have h := Nat.mul_le_mul_left (3*r+4) hs.le
    nlinarith only [large,h]
  · have d := Nat.mod_add_div (s+1) 2
    have e := Nat.mod_lt (s+1) (show 0<2 by decide)
    nlinarith only [half,d,e,le_of_not_gt hs,Nat.sub_add_cancel (show 1≤r by omega)]

lemma critical_column_bound {r a k C D : ℕ} (hr : 5 ≤ r) (ha : 0<a)
    (cop : k.Coprime a) (klo : r<k) (khi : 4*k ≤ r*r+1)
    {A P : Finset ℕ} (off : ∀ u ∈ P, 0 < u ∧ u < a)
    (lifts : ∀ u ∈ P, ∀ i ∈ Icc 1 r, i*a+u ∈ A) (free : Free r A)
    (prev : Shell r r C) (within : ∀ u ∈ P, u ≤ D) :
    let Fct := 4*(r-1)*(r+1)-1
    12*r*(r+1)*P.card+P.card ≤ 12*r*D+12*a+3*Fct*(Fct*C+1)+12*r*((6*r+8)*r+1) := by
  classical
  intro Fct
  by_cases hn : P.Nonempty
  · let L := (r*r+1)/2-r
    have quad := Nat.mul_le_mul_right r (show 2≤r by omega)
    have fr : 2*(r+L) ≤ r*r+1 ∧ r*r+1 < 2*(r+L+1) := by dsimp [L]; omega
    obtain ⟨q,hq,dvd,aper,excluded⟩ := reduce_columns (r:=r) (L:=L) ha P hn (by
      intro u hu j hj f hf
      have h := mem_Ioc.mp hj
      have e : r+(j-r)=j := by omega
      simpa only [e] using dilate_range (by omega : 3 ≤ r) (j:=j-r) (by omega) (by omega)
        off lifts free u hu f hf)
    let : NeZero q := ⟨hq.ne'⟩
    let R := P.image (fun x : ℕ => (x : ZMod q))
    let s := R.card
    have unit := cop.of_dvd_right dvd
    have cardC := cyclic_estimates (r:=r) (by omega) R (hn.image _) aper unit klo (by omega) excluded
    have sharp : (r+1)*s ≤ q := packing_arithmetic hr klo (by omega) fr cardC.1 cardC.2.1
      cardC.2.2.1 cardC.2.2.2
    let T := P.image (·%q)
    have eq : (R.image ZMod.val) = T := by
      dsimp [R,T]
      rw [image_image]
      exact image_congr (fun x _ => ZMod.val_natCast _ _)
    have dense : T.card = s := eq ▸ card_image_of_injective _ (ZMod.val_injective q)
    have group (x) (hx : x ∈ P) : x%q ∈ T := mem_image_of_mem _ hx
    by_cases big : (6*r+8)*r ≤ q
    · have sf := integral_margin hr big cardC.2.1
      change (3*(r+1)+1)*s ≤ 3*q at sf
      have dec : a/q*q = a := Nat.div_mul_cancel dvd
      have cnt := Erdos13HalfOccupied.count_by_period q (a/q) 0 (Nat.zero_le _) T 0 P (by
        intro x hx
        have := (off x hx).2
        simpa only [Nat.zero_add,Nat.add_zero,dec,mem_Ico,Nat.zero_le,true_and] using this) group
      simp only [min_eq_left (Nat.zero_le _),Nat.add_zero,dense] at cnt
      have h₁ := Nat.mul_le_mul_left (3*(r+1)+1) cnt
      have h₂ := Nat.mul_le_mul_left (a/q) sf
      have cc : (3*(r+1)+1)*P.card ≤ 3*a := by nlinarith only [h₁,h₂,dec]
      have hF : Fct+1=4*(r-1)*(r+1) := by
        have h1 : 0 < 4*(r-1)*(r+1) := by exact Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (by omega)
        dsimp [Fct]
        omega
      have gg := complete_critical (by omega : 3≤r) hF lifts free prev within
      have hG := congrArg (fun x : ℕ => x*P.card) hF
      have id := congrArg (fun h : ℕ => 4*h*(r+1)*P.card) (Nat.sub_add_cancel (show 1≤r by omega))
      have bound : 12*r*(r+1)*P.card+P.card ≤ 12*r*D+12*a+3*Fct*(Fct*C+1) := by
        nlinarith only [cc,gg,hG,id]
      omega
    · let b := (D+1)/q
      let z := (D+1)%q
      have dec : b*q+z=D+1 := by simpa [b,z,Nat.add_comm,Nat.mul_comm] using Nat.mod_add_div (D+1) q
      have cnt := Erdos13HalfOccupied.count_by_period q b z (Nat.mod_lt _ hq).le T 0 P (by
        intro x hx
        have := within x hx
        exact mem_Ico.mpr ⟨Nat.zero_le _,by omega⟩) group
      rw [dense] at cnt
      have x := min_le_right z s
      have cs := Nat.mul_le_mul_left (r+1) (show P.card ≤ (b+1)*s by
        rw [Nat.add_mul,Nat.one_mul];omega)
      have sq := Nat.mul_le_mul_left (b+1) sharp
      have cap : (r+1)*P.card ≤ D+1+q := by nlinarith only [cs,sq,dec,Nat.zero_le z]
      have x := Nat.mul_le_mul_left r cap
      have y := Nat.mul_le_mul_left r (show q+1≤(6*r+8)*r+1 by omega)
      have PA : P ⊆ range a := fun u hu => mem_range.mpr (off u hu).2
      have cardA := card_le_card PA
      rw [card_range] at cardA
      nlinarith only [x,y,cardA,Nat.zero_le a,Nat.zero_le (Fct*(Fct*C+1))]
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simp

end Erdos13ColumnModulo

end

section

/-  A cardinal bound in the wider shell when its pivots admit coprime multipliers. -/
namespace Erdos13ColumnModulo
open Finset FullColumns OMA.Erdos13ManyLayers

def Good (r a : ℕ) : Prop := ∃ k : ℕ, r<k ∧ 4*k ≤ r*r+1 ∧ k.Coprime a

def cutoff (r : ℕ) := 24*r*r*(r+1)*(r-1)*(r+1)

lemma tail_arithmetic {r a d t N D s p M K : ℕ} (hr : 5 ≤ r) (div : t*d = a)
    (hd : cutoff r < d) (dec : r*a+D=N)
    (res : r*s ≤ a+t*r) (count : M ≤ (r-1)*s+p)
    (strong : 12*r*(r+1)*p+p ≤ 12*r*D+12*a+K) : (r+1)*M ≤ N+K := by
  have c := Nat.mul_le_mul_left (r*(r+1)) count
  have f := Nat.mul_le_mul_left ((r-1)*(r+1)) res
  have rem := Nat.sub_add_cancel (show 1≤r by omega)
  have id := congrArg (fun z : ℕ => (r+1)*z*a) rem
  have lim := Nat.mul_le_mul_left t hd.le
  dsimp [cutoff] at lim
  have zero := Nat.zero_le r
  have rsum := congrArg (fun z : ℕ => r*z) dec
  have pa : (r-1)*(r+1)*t*r+r*(r+1)*p ≤ r*D+a+K := by
    by_cases big : a ≤ 2*r*(r+1)*p
    · have estimate : 2*r*(r+1)*(12*((r-1)*(r+1)*t*r)) ≤ 2*r*(r+1)*p := by
        nlinarith only [lim,div,big]
      have paid := Nat.le_of_mul_le_mul_left estimate (by positivity)
      nlinarith only [paid,strong,Nat.zero_le K]
    · have z := Nat.mul_le_mul_left ((r-1)*(r+1)*t*r) (show 2 ≤ 24*r*(r+1) by nlinarith [hr])
      have paid : 2*((r-1)*(r+1)*t*r) ≤ a := by nlinarith only [z,lim,div]
      nlinarith only [paid,lt_of_not_ge big,Nat.zero_le (r*D),Nat.zero_le K]
  have step : r*((r+1)*M) ≤ r*N+K := by
    have h : r*(r+1)*M+(r*D+a) ≤ r*N+(r-1)*(r+1)*t*r+r*(r+1)*p := by
      nlinarith only [c,f,id,rsum]
    rw [←Nat.mul_assoc]
    omega
  have finish : r*((r+1)*M) ≤ r*(N+K) := by
    rw [Nat.mul_add]
    have h := Nat.mul_le_mul_right K (show 1 ≤ r by omega)
    rw [Nat.one_mul] at h
    exact step.trans (Nat.add_le_add_left h _)
  exact Nat.le_of_mul_le_mul_left finish (by omega)

theorem good_tail {r N a d C : ℕ} (hr : 5 ≤ r) (ha : 0<a)
    (lo : r*a ≤ N) (hi : N ≤ (r+1)*a) (good : Good r a)
    (hd : cutoff r < d) (dvd : d ∣ a) {A B : Finset ℕ} (hain : a ∈ A)
    (subA : B ⊆ A) (sub : B ⊆ Ioc a N) (free : Free r A)
    (quot : r*(B.image (·%d)).card ≤ d+r-2) (prev : Shell r r C) :
    let Fct := 4*(r-1)*(r+1)-1
    (r+1)*B.card ≤ N+3*Fct*(Fct*C+1)+12*r*((6*r+8)*r+1) := by
  classical
  intro Fct
  obtain ⟨k,klo,khi,cop⟩ := good
  let P := complete B a r
  have lift (u) (hu : u ∈ P) (j) (hj : j ∈ Icc 1 r) : j*a+u ∈ B := (mem_filter.mp hu).2 j hj
  have within (u) (hu : u ∈ P) : u ≤ N-r*a := by
    have := (mem_Ioc.mp (sub (lift u hu r (mem_Icc.mpr ⟨by omega,le_rfl⟩)))).2
    omega
  have no (x) (hx : x ∈ B) : ¬ a ∣ x := by
    intro dv
    apply free a hain (fun _ => x) (fun _ => subA hx) (fun _ => (mem_Ioc.mp (sub hx)).1)
    simpa using dv.trans (dvd_mul_left x r)
  have off (u) (hu : u ∈ P) : 0<u ∧ u<a := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp (mem_filter.mp hu).1
    exact ⟨Nat.pos_of_ne_zero (fun eq => no x hx (Nat.dvd_of_mod_eq_zero eq)),Nat.mod_lt _ ha⟩
  have layers (x) (hx : x ∈ B) : x/a ∈ Icc 1 r := by
    obtain ⟨xlo,xhi⟩ := mem_Ioc.mp (sub hx)
    refine mem_Icc.mpr ⟨Nat.div_pos xlo.le ha,Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr ?_)⟩
    by_contra! h
    change (r+1)*a ≤ x at h
    have eq : x=(r+1)*a := by omega
    exact no x hx (eq ▸ dvd_mul_left _ _)
  have qpos : 0<d := by omega
  have strong := critical_column_bound hr ha cop klo khi off (fun u hu j hj => subA (lift u hu j hj))
    free prev within
  change 12*r*(r+1)*P.card+P.card ≤ 12*r*(N-r*a)+12*a+3*Fct*(Fct*C+1)+12*r*((6*r+8)*r+1) at strong
  rw [Nat.add_assoc (12*r*(N-r*a)+12*a)] at strong
  have rad := OMA.Erdos13Cyclic.residue_bound_of_quotient B ha qpos dvd quot
  have sum := tail_arithmetic hr (Nat.div_mul_cancel dvd) hd (by omega : r*a+(N-r*a)=N)
    rad (FullColumns.card_bound (by omega : 0<r) layers) strong
  simpa only [Nat.add_assoc] using sum

theorem good_shell {r : ℕ} (hr : 5 ≤ r) :
    ∃ K : ℕ, ∀ N (A : Finset ℕ), (∀ a ∈ A, 0<a ∧ N ≤ (r+1)*a ∧ a ≤ N) →
      (∀ a ∈ A, r*a < N → Good r a) → Free r A → (r+1)*A.card ≤ N+K := by
  obtain ⟨C,prev⟩ := shell_to_arity r (by omega)
  let Fct := 4*(r-1)*(r+1)-1
  let K := C+3*Fct*(Fct*C+1)+12*r*((6*r+8)*r+1)
  refine ⟨K+(r+1)*(cutoff r+1),?_⟩
  intro N A sub goods free
  have pos (a) (ha : a∈A) := (sub _ ha).1
  rw [←Nat.add_assoc N K]
  apply OMA.Erdos13UpperShell.select_large_quotient (L:=cutoff r) A pos
    (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a ha d hd dvd quot
  let B := A.filter (a<·)
  change (r+1)*B.card ≤ N+K
  have hBA : B ⊆ A := filter_subset _ _
  have hB : B ⊆ Ioc a N := fun x hx => mem_Ioc.mpr ⟨(mem_filter.mp hx).2,(sub x (hBA hx)).2.2⟩
  by_cases high : N ≤ r*a
  · have e := prev N B (fun x hx => ⟨pos x (hBA hx),high.trans (Nat.mul_le_mul_left r
        (mem_filter.mp hx).2.le),(sub x (hBA hx)).2.2⟩)
      (fun x hx f hf => free x (hBA hx) f (fun i => hBA (hf i)))
    dsimp [K]
    omega
  · have t := good_tail hr (pos a ha) (by omega) (sub a ha).2.1 (goods a ha (by omega))
      hd dvd ha hBA hB free quot prev
    dsimp [K,Fct]
    omega
end Erdos13ColumnModulo

end

section

/-  A uniform strict gap for the sparse-top case on a wider shell of good pivots. -/
namespace Erdos13ColumnModulo
open Finset FullColumns OMA.Erdos13ManyLayers

def localGain (r : ℕ) := 48*r*r*(r+1)
def gain (r : ℕ) := 48*r*r*(r+1)*(r+1)

lemma strict_arithmetic {r a d t N D s p B K : ℕ} (hr : 5 ≤ r) (div : t*d = a)
    (hd : 2*cutoff r < d) (dec : r*a+D=N)
    (res : r*s ≤ a+t*r) (count : B ≤ (r-1)*s+p)
    (strong : 12*r*(r+1)*p+p ≤ 12*r*D+12*a+K) :
    localGain r*(r+1)*B+a ≤ localGain r*N+4*r*(r+1)*K := by
  have c := Nat.mul_le_mul_left (r*(r+1)) count
  have f := Nat.mul_le_mul_left ((r-1)*(r+1)) res
  have rem := Nat.sub_add_cancel (show 1≤r by omega)
  have id := congrArg (fun z : ℕ => (r+1)*z*a) rem
  have lim := Nat.mul_le_mul_left t hd.le
  dsimp [cutoff] at lim
  have rsum := congrArg (fun z : ℕ => r*z) dec
  have co : r*(r+1)*B+(r*D+a) ≤ r*N+(r-1)*(r+1)*t*r+r*(r+1)*p := by
    nlinarith only [c,f,id,rsum]
  dsimp [localGain]
  by_cases big : a ≤ 2*r*(r+1)*p
  · have est : 2*r*(r+1)*(24*((r-1)*(r+1)*t*r)) ≤ 2*r*(r+1)*p := by
      nlinarith only [lim,div,big]
    have paid := Nat.le_of_mul_le_mul_left est (by positivity)
    have main : 24*r*(r+1)*B+p ≤ 24*r*N+2*K := by nlinarith only [co,strong,paid]
    have sc := Nat.mul_le_mul_left (2*r*(r+1)) main
    nlinarith only [big,sc]
  · have z := Nat.mul_le_mul_left ((r-1)*(r+1)*t*r) (show 4 ≤ 48*r*(r+1) by nlinarith [hr])
    have paid : 4*((r-1)*(r+1)*t*r) ≤ a := by nlinarith only [z,lim,div]
    have main : 4*r*(r+1)*B+a ≤ 4*r*N := by
      nlinarith only [co,paid,lt_of_not_ge big,Nat.zero_le (r*D)]
    have sc := Nat.mul_le_mul_left (12*r*(r+1)) main
    have gainA := Nat.mul_le_mul_right a (show 1 ≤ 12*r*(r+1) by nlinarith [hr])
    nlinarith only [sc,gainA,Nat.zero_le (4*r*(r+1)*K)]

theorem good_tail_strict {r N a d C : ℕ} (hr : 5 ≤ r) (ha : 0<a)
    (lo : r*a ≤ N) (hi : N ≤ (r+1)*a) (good : Good r a)
    (hd : 2*cutoff r < d) (dvd : d ∣ a) {A B : Finset ℕ} (hain : a ∈ A)
    (subA : B ⊆ A) (sub : B ⊆ Ioc a N) (free : Free r A)
    (quot : r*(B.image (·%d)).card ≤ d+r-2) (prev : Shell r r C) :
    let Fct := 4*(r-1)*(r+1)-1
    localGain r*(r+1)*B.card+a ≤ localGain r*N+
       4*r*(r+1)*(3*Fct*(Fct*C+1)+12*r*((6*r+8)*r+1)) := by
  classical
  intro Fct
  obtain ⟨k,klo,khi,cop⟩ := good
  let P := complete B a r
  have lift (u) (hu : u ∈ P) (j) (hj : j ∈ Icc 1 r) : j*a+u ∈ B := (mem_filter.mp hu).2 j hj
  have within (u) (hu : u ∈ P) : u ≤ N-r*a := by
    have := (mem_Ioc.mp (sub (lift u hu r (mem_Icc.mpr ⟨by omega,le_rfl⟩)))).2
    omega
  have no (x) (hx : x ∈ B) : ¬ a ∣ x := by
    intro dv
    apply free a hain (fun _ => x) (fun _ => subA hx) (fun _ => (mem_Ioc.mp (sub hx)).1)
    simpa using dv.trans (dvd_mul_left x r)
  have off (u) (hu : u ∈ P) : 0<u ∧ u<a := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp (mem_filter.mp hu).1
    exact ⟨Nat.pos_of_ne_zero (fun eq => no x hx (Nat.dvd_of_mod_eq_zero eq)),Nat.mod_lt _ ha⟩
  have layers (x) (hx : x ∈ B) : x/a ∈ Icc 1 r := by
    obtain ⟨xlo,xhi⟩ := mem_Ioc.mp (sub hx)
    refine mem_Icc.mpr ⟨Nat.div_pos xlo.le ha,Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr ?_)⟩
    by_contra! h
    change (r+1)*a ≤ x at h
    have eq : x=(r+1)*a := by omega
    exact no x hx (eq ▸ dvd_mul_left _ _)
  have qpos : 0<d := by omega
  have strong := critical_column_bound hr ha cop klo khi off (fun u hu j hj => subA (lift u hu j hj))
    free prev within
  change 12*r*(r+1)*P.card+P.card ≤ 12*r*(N-r*a)+12*a+3*Fct*(Fct*C+1)+12*r*((6*r+8)*r+1) at strong
  rw [Nat.add_assoc (12*r*(N-r*a)+12*a)] at strong
  have rad := OMA.Erdos13Cyclic.residue_bound_of_quotient B ha qpos dvd quot
  have sum := strict_arithmetic hr (Nat.div_mul_cancel dvd) hd (by omega : r*a+(N-r*a)=N)
    rad (FullColumns.card_bound (by omega : 0<r) layers) strong
  exact sum


theorem good_sparse_shell {r : ℕ} (hr : 5 ≤ r) :
    ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ), (∀ a ∈ A, 0<a ∧ (r+1)*m ≤ (r+1)*a ∧ a ≤ (r+1)*m) →
      (∀ a ∈ A, r*a < (r+1)*m → Good r a) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
      (gain r*(r+1)+1)*A.card ≤ gain r*((r+1)*m)+K := by
  classical
  obtain ⟨C,prev⟩ := shell_to_arity r (by omega)
  obtain ⟨D,old⟩ := sparse_top_stability r (by omega)
  let F := 4*(r-1)*(r+1)-1
  let K₀ := 4*r*(r+1)*(3*F*(F*C+1)+12*r*((6*r+8)*r+1))
  let K := D+gain r*C+(r+1)*K₀
  refine ⟨K+(gain r*(r+1)+1)*(2*cutoff r+1),?_⟩
  intro m A sub goods free sparse
  let N := (r+1)*m
  have pos (a) (ha : a ∈ A) := (sub a ha).1
  rw [←Nat.add_assoc (gain r*((r+1)*m)) K]
  apply OMA.Erdos13UpperShell.select_large_scaled (L:=2*cutoff r) A pos
    (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a ha d hd dvd quot
  let B := A.filter (a<·)
  change (gain r*(r+1)+1)*B.card ≤ gain r*N+K
  have hBA : B ⊆ A := filter_subset _ _
  have hB : B ⊆ Ioc a N := fun x hx => mem_Ioc.mpr ⟨(mem_filter.mp hx).2,(sub x (hBA hx)).2.2⟩
  by_cases high : N ≤ r*a
  · have shell (x) (hx : x∈B) : 0<x ∧ N≤r*x ∧ x≤N :=
      ⟨pos x (hBA hx),high.trans (Nat.mul_le_mul_left r (mem_filter.mp hx).2.le),(sub x (hBA hx)).2.2⟩
    have freeB : Free r B := fun x hx f hf => free _ (hBA hx) f (fun i => hBA (hf i))
    have sp := Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl (s:=Ioc (r*m) N)) hBA))
    have h := old m B shell freeB (sp.trans sparse)
    have le : 24*r*r ≤ gain r := by dsimp [gain]; nlinarith [Nat.zero_le (r*r*r), Nat.zero_le (r*r*r*r)]
    have t := lift_gain le (prev N B shell freeB) h
    dsimp [K]
    omega
  · have bound := good_tail_strict hr (pos a ha) (by omega) (sub a ha).2.1 (goods a ha (by omega))
      hd dvd ha hBA hB free quot prev
    change localGain r*(r+1)*B.card+a ≤ localGain r*N+K₀ at bound
    have sc := Nat.mul_le_mul_left (r+1) bound
    have lim := (sub a ha).2.1
    change N ≤ (r+1)*a at lim
    have cardB := card_le_card hB
    rw [Nat.card_Ioc] at cardB
    have gg : gain r=localGain r*(r+1) := rfl
    have out : (gain r*(r+1)+1)*B.card ≤ gain r*N + (r+1)*K₀ := by
      have bN : B.card ≤ N := by omega
      rw [gg]
      nlinarith only [sc,lim,bN]
    dsimp [K]
    omega
end Erdos13ColumnModulo

end

section

namespace Erdos13HalfOccupied

open Finset

/-- For m≥6, a divisor large enough for the half-occupied top interval lies
in the upper two thirds of the ambient interval. -/
lemma three_mul_ge_endpoint {r m b a : ℕ} (hr : 3 ≤ r) (hm : 6 ≤ m)
    (half : m < 2*b) (size : r*b ≤ a+r-2) :
    (r+1)*m ≤ 3*a := by
  have h₁ := Nat.mul_le_mul_left r half.le
  have h₂ := Nat.mul_le_mul (show 0 ≤ r-2 by omega) (show 0 ≤ m-6 by omega)
  have hr' : r-2+2=r := by omega
  have hm' : m-6+6=m := by omega
  have hprod := congrArg (fun x : ℕ => x*(m-6+6)) hr'
  have hprod' := congrArg (fun x : ℕ => r*x) hm'
  have heq := congrArg (fun x : ℕ => 2*x) hm'
  have heq' := congrArg (fun x : ℕ => 6*x) hr'
  have hr₂ : 2 ≤ a+r := by omega
  have hs : r*b+2 ≤ a+r := by omega
  nlinarith only [h₁, hprod, hprod', heq, heq', hs, Nat.zero_le ((r-2)*(m-6))]

/-- More than half of the top interval is enough to reduce the remaining
bound to the case with every element at least N/3. The quotient assumptions
are applied only to prospective smaller exceptions. -/
lemma half_occupied_bridge {r m C : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : A ⊆ Icc 1 ((r+1)*m))
    (half : m < 2*(Ioc (r*m) ((r+1)*m) ∩ A).card)
    (quotients : ∀ a ∈ A, 3*a < (r+1)*m →
      ∃ q : ℕ, 0 < q ∧ q ∣ a ∧
        (∀ x ∈ A, a < x → ¬ q ∣ x) ∧
        r*((A.filter (fun x => a < x)).image (fun x => x%q)).card ≤ q+r-2)
    (upper : ∀ S ⊆ A, (∀ x ∈ S, (r+1)*m ≤ 3*x) → S.card ≤ m+C) :
    A.card ≤ m + C + (10+5*(r+1)) := by
  classical
  by_cases big : 6 ≤ m
  · let N := (r+1)*m
    let B := Ioc (r*m) N ∩ A
    let D := A.filter (fun a => 3*a < N)
    let U := A.filter (fun a => ¬ 3*a < N)
    have hDU := A.card_filter_add_card_filter_not (fun a => 3*a < N)
    change D.card + U.card = A.card at hDU
    have hU : U.card ≤ m+C := by
      apply upper U (filter_subset _ _)
      intro x hx
      exact le_of_not_gt (mem_filter.mp hx).2
    have hI : B ⊆ Ico (r*m+1) (r*m+1+m) := by
      intro x hx
      have h := mem_Ioc.mp (mem_inter.mp hx).1
      change r*m<x ∧ x≤(r+1)*m at h
      rw [Nat.add_mul, Nat.one_mul] at h
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    have hqall (a : ℕ) (ha : a ∈ D) : ∃ q : ℕ, 0 < q ∧ q ∣ a ∧
          (∀ x ∈ A, a < x → ¬ q ∣ x) ∧
          r*((A.filter (fun x => a < x)).image (fun x => x%q)).card ≤ q+r-2 := by
      have h := mem_filter.mp ha
      exact quotients a h.1 h.2
    choose! f fpos fdvd fonly fcard using hqall
    have hexc (a : ℕ) (ha : a ∈ D) : f a ∈ range 5 ∪ Icc (3*m/4-2) (3*m/4+2) := by
      have h := mem_filter.mp ha
      change a ∈ A ∧ 3*a<N at h
      have hab : a ≤ r*m := by
        have hm' : m ≤ r*m := by
          simpa using Nat.mul_le_mul_right m (show 1 ≤ r by omega)
        dsimp [N] at h
        rw [Nat.add_mul, Nat.one_mul] at h
        omega
      have hBT : B ⊆ A.filter (fun x => a < x) := by
        intro x hx
        have ⟨h₁, h₂⟩ := mem_inter.mp hx
        exact mem_filter.mpr ⟨h₂, lt_of_le_of_lt hab (mem_Ioc.mp h₁).1⟩
      have card := card_le_card (image_subset_image (f := fun x => x % f a) hBT)
      have hcap := (Nat.mul_le_mul_left r card).trans (fcard a ha)
      have hpos : 0 < a := (mem_Icc.mp (sub h.1)).1
      rcases force_large_divisor hr (fpos a ha) (Nat.le_of_dvd hpos (fdvd a ha))
          B hI half hcap with exc | good
      · exact exc
      · exact False.elim ((not_lt_of_ge (three_mul_ge_endpoint hr big half good.2)) h.2)
    have hD := exceptional_elements D f m fdvd (fun a ha x hx =>
      fonly a ha x (mem_filter.mp hx).1)
    rw [filter_eq_self.mpr hexc] at hD
    omega
  · have hcard := card_le_card sub
    simp only [Nat.card_Icc, Nat.add_one_sub_one] at hcard
    have := Nat.mul_le_mul_left (r+1) (show m ≤ 5 by omega)
    nlinarith

end Erdos13HalfOccupied

end

section

/-  The majority case for every arity at least three. -/

namespace Erdos13HalfOccupied

open Finset

/-- The quotient selection in the majority reduction follows from the cyclic
sumset theorem for every prospective small divisor: its tail contains an
element of the majority set. -/
lemma half_bound_of_shell {r m C : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : A ⊆ Icc 1 ((r+1)*m))
    (free : ∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) →
      ¬ a ∣ ∑ i, b i)
    (half : m < 2*(Ioc (r*m) ((r+1)*m) ∩ A).card)
    (upper : ∀ S ⊆ A, (∀ x ∈ S, (r+1)*m ≤ 3*x) → S.card ≤ m+C) :
    A.card ≤ m + C + (10+5*(r+1)) := by
  apply half_occupied_bridge hr A sub half _ upper
  intro a ha hsmall
  apply OMA.Erdos13Cyclic.witness_of_free (by omega : 2 ≤ r) free
    (fun x hx => (mem_Icc.mp (sub hx)).1) a ha
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (Ioc (r*m) ((r+1)*m) ∩ A).card by omega)
  obtain ⟨hI, hA⟩ := mem_inter.mp hx
  have hlarge := (mem_Ioc.mp hI).1
  have hm : m ≤ r*m := by
    simpa using Nat.mul_le_mul_right m (show 1 ≤ r by omega)
  rw [Nat.add_mul, Nat.one_mul] at hsmall
  exact ⟨x, mem_filter.mpr ⟨hA, by omega⟩⟩

/-- At every arity r≥3, any set exceeding m by a sufficiently large constant
and occupying over half of its top interval contains a forbidden sum. -/
theorem majority_witness {r : ℕ} (hr : 3 ≤ r) : ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → m+K < A.card →
    m < 2*(Ioc (r*m) ((r+1)*m) ∩ A).card →
    ∃ a ∈ A, ∃ b : Fin r → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i := by
  let E := (128*r + 24*((r+1)*(16*r+1)+32*r+1)+2) + (r+1)*(64*r+1)
  refine ⟨E + (10+5*(r+1)), ?_⟩
  intro m A sub large half
  by_contra absent
  have free : FullColumns.Free r A := by
    intro a ha b hb hlt hd
    exact absent ⟨a, ha, b, (fun i => ⟨hb i, hlt i⟩), hd⟩
  have bound : A.card ≤ m+E+(10+5*(r+1)) := by
    apply half_bound_of_shell hr A sub free half
    intro S hS third
    have onS : FullColumns.Free r S := fun a ha b hb => free a (hS ha) b (fun i => hS (hb i))
    have h := OMA.Erdos13UpperShell.bound_on_third_shell hr S
      (fun x hx => ⟨(mem_Icc.mp (sub (hS hx))).1, third x hx, (mem_Icc.mp (sub (hS hx))).2⟩) onS
    have hbound : (r+1)*S.card ≤ (r+1)*m+E := by simpa only [E, Nat.add_assoc] using h
    by_contra! tooMany
    have mul := Nat.mul_le_mul_left (r+1) (show m+E+1 ≤ S.card by omega)
    nlinarith only [hbound, mul, Nat.zero_le (r*E), Nat.zero_le r]
  omega

end Erdos13HalfOccupied

end

section

/-  Four primes force the exceptional pivots into a sparse progression in the
strip from N/(r+1) to N/r, which the strict estimate can absorb. -/

namespace Erdos13ColumnModulo
open Finset FullColumns OMA.Erdos13ManyLayers

lemma bertrand_bad_common_factor {r : ℕ} (hr : 64 ≤ r) :
    ∃ P : ℕ, 64*r*r*r*r ≤ P ∧ ∀ a, ¬ Good r a → P ∣ a := by
  obtain ⟨p₁,h₁,lo₁,hi₁⟩ := Nat.exists_prime_lt_and_le_two_mul r (by omega)
  obtain ⟨p₂,h₂,lo₂,hi₂⟩ := Nat.exists_prime_lt_and_le_two_mul (2*r) (by omega)
  obtain ⟨p₃,h₃,lo₃,hi₃⟩ := Nat.exists_prime_lt_and_le_two_mul (4*r) (by omega)
  obtain ⟨p₄,h₄,lo₄,hi₄⟩ := Nat.exists_prime_lt_and_le_two_mul (8*r) (by omega)
  refine ⟨p₁*p₂*p₃*p₄, ?_, ?_⟩
  · calc
      64*r*r*r*r = r*(2*r)*(4*r)*(8*r) := by ring
      _ ≤ p₁*p₂*p₃*p₄ := by gcongr
  intro a bad
  have bound : 64*r ≤ r*r := by simpa [mul_comm] using Nat.mul_le_mul_right r hr
  have div (p : ℕ) (hp : p.Prime) (lo : r<p) (hi : p≤16*r) : p ∣ a := by
    apply hp.dvd_iff_not_coprime.mpr
    exact fun c => bad ⟨p,lo,by omega,c⟩
  have d₁ := div _ h₁ lo₁ (by omega)
  have d₂ := div _ h₂ (by omega) (by omega)
  have d₃ := div _ h₃ (by omega) (by omega)
  have d₄ := div _ h₄ (by omega) (by omega)
  have c₁₂ := (Nat.coprime_primes h₁ h₂).mpr (by omega)
  have c₁₃ := (Nat.coprime_primes h₁ h₃).mpr (by omega)
  have c₂₃ := (Nat.coprime_primes h₂ h₃).mpr (by omega)
  have c₁₄ := (Nat.coprime_primes h₁ h₄).mpr (by omega)
  have c₂₄ := (Nat.coprime_primes h₂ h₄).mpr (by omega)
  have c₃₄ := (Nat.coprime_primes h₃ h₄).mpr (by omega)
  exact ((c₁₄.mul_left c₂₄).mul_left c₃₄).mul_dvd_of_dvd_of_dvd
    ((c₁₃.mul_left c₂₃).mul_dvd_of_dvd_of_dvd (c₁₂.mul_dvd_of_dvd_of_dvd d₁ d₂) d₃) d₄

lemma finite_bad_common_factor {r l h : ℕ} (lo : l ≤ r) (hi : r ≤ h) (S : Finset ℕ)
    (size : 64*h*h*h*h ≤ S.prod id)
    (primes : ∀ p ∈ S, p.Prime ∧ h < p ∧ 4*p ≤ l*l+1) :
    ∃ P : ℕ, 64*r*r*r*r ≤ P ∧ ∀ a, ¬ Good r a → P ∣ a := by
  refine ⟨S.prod id,le_trans (by gcongr) size,?_⟩
  intro a bad
  rcases Nat.eq_zero_or_pos a with rfl | positive
  · exact dvd_zero _
  have sub : S ⊆ a.primeFactors := by
    intro p hp
    obtain ⟨pr,lower,upper⟩ := primes p hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨pr,pr.dvd_iff_not_coprime.mpr (fun cop => bad ⟨p,hi.trans_lt lower,?_,cop⟩),positive.ne'⟩
    exact upper.trans (Nat.add_le_add_right (Nat.mul_le_mul lo lo) 1)
  exact (Finset.prod_dvd_prod_of_subset _ _ id sub).trans (Nat.prod_primeFactors_dvd a)

/-- Five short lists of primes provide the same bound below the uniform
Bertrand range. -/
lemma bad_common_factor {r : ℕ} (hr : 10 ≤ r) :
    ∃ P : ℕ, 64*r*r*r*r ≤ P ∧ ∀ a, ¬ Good r a → P ∣ a := by
  by_cases h : 64 ≤ r
  · exact bertrand_bad_common_factor h
  by_cases h₃₁ : 31 ≤ r
  · exact finite_bad_common_factor h₃₁ (show r ≤ 63 by omega) {67,71,73,79,83} (by decide) (by decide)
  by_cases h₁₆ : 16 ≤ r
  · exact finite_bad_common_factor h₁₆ (show r ≤ 30 by omega) {31,37,41,43,47} (by decide) (by decide)
  by_cases h₁₂ : 12 ≤ r
  · exact finite_bad_common_factor h₁₂ (show r ≤ 15 by omega) {17,19,23,29,31} (by decide) (by decide)
  by_cases h₁₁ : 11 ≤ r
  · exact finite_bad_common_factor h₁₁ (show r ≤ 11 by omega) {13,17,19,23,29} (by decide) (by decide)
  exact finite_bad_common_factor hr (show r ≤ 10 by omega) {11,13,17,19,23} (by decide) (by decide)

lemma bad_factor_large {r P : ℕ} (hr : 10 ≤ r) (hP : 64*r*r*r*r ≤ P) :
    48*r*r*(r+1)*(r+1)*(r+1)+1 ≤ r*P := by
  refine le_trans ?_ (Nat.mul_le_mul_left r hP)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hr
  ring_nf
  omega

lemma bad_strip_count {r m P : ℕ} (hr : 0 < r) (hp : 0 < P) (B : Finset ℕ)
    (bounds : ∀ a∈B, m ≤ a ∧ r*a < (r+1)*m ∧ P∣a) :
    r*P*B.card ≤ m+r*(P+1) := by
  let L := m/r+1
  have each (x) (hx : x∈B) : x < m+L := by
    have h := (bounds x hx).2.1
    have e := Nat.mod_add_div m r
    have em := Nat.mod_lt m hr
    have hl := Nat.sub_add_cancel (bounds x hx).1
    have hd := congrArg (fun v : ℕ => r*v) hl
    have le : (x-m)*r ≤ m := by nlinarith only [h,hd]
    have lim := (Nat.le_div_iff_mul_le hr).mpr le
    dsimp [L]
    omega
  have hd : (L/P)*P + L%P = L := by simpa [Nat.add_comm,Nat.mul_comm] using Nat.mod_add_div L P
  have cnt := Erdos13HalfOccupied.count_by_period P (L/P) (L%P) (Nat.mod_lt _ hp).le {0} m B
    (fun x hx => mem_Ico.mpr ⟨(bounds x hx).1,by rw [hd]; exact each x hx⟩)
    (fun x hx => by simpa using Nat.mod_eq_zero_of_dvd (bounds x hx).2.2)
  simp only [card_singleton,Nat.mul_one] at cnt
  have c : B.card ≤ L/P+1 := cnt.trans (Nat.add_le_add_left (min_le_right _ _) _)
  have w := Nat.mul_le_mul_left (r*P) c
  have scaled := Nat.mul_le_mul_left r (Nat.div_mul_le_self L P)
  have remain := Nat.div_mul_le_self m r
  dsimp [L] at scaled
  dsimp [L] at w
  nlinarith only [w,scaled,remain]

/-- Removing the bad pivots in the single new strip upgrades a strict estimate
for good pivots to a uniform shell theorem, including arbitrary endpoints. -/
theorem shell_of_paid_gap {r C H₀ P : ℕ} (hr : 5 ≤ r)
    (hp : 0 < P) (div : ∀ a, ¬Good r a → P ∣ a) (factor : H₀*(r+1)+1 ≤ r*P)
    (sparseGood : ∀ (m : ℕ) (A : Finset ℕ),
      (∀ a∈A, 0<a ∧ (r+1)*m ≤ (r+1)*a ∧ a ≤ (r+1)*m) →
      (∀ a∈A, r*a < (r+1)*m → Good r a) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
      (H₀*(r+1)+1)*A.card ≤ H₀*((r+1)*m)+C) :
    ∃ K : ℕ, Shell r (r+1) K := by
  classical
  obtain ⟨D,majority⟩ := Erdos13HalfOccupied.majority_witness (r:=r) (by omega)
  let K := C+r*(P+1)+D
  have rounded (m : ℕ) (A : Finset ℕ)
      (sub : ∀ a∈A, 0<a ∧ (r+1)*m ≤ (r+1)*a ∧ a ≤ (r+1)*m)
      (free : Free r A) : A.card ≤ m+K := by
    by_cases sp : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m
    · let ok (a : ℕ) := r*a < (r+1)*m → Good r a
      let G := A.filter ok
      let B := A.filter (fun a => ¬ok a)
      have gsub : G ⊆ A := filter_subset _ _
      have strong := sparseGood m G (fun a ha => sub a (gsub ha)) (fun a ha => (mem_filter.mp ha).2)
        (fun a ha b hb => free a (gsub ha) b (fun i => gsub (hb i)))
        ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) gsub))).trans sp)
      have bp (a) (ha : a ∈ B) : m ≤ a ∧ r*a < (r+1)*m ∧ P ∣ a := by
        obtain ⟨hx,bad⟩ := mem_filter.mp ha
        change ¬(r*a < (r+1)*m → Good r a) at bad
        push Not at bad
        exact ⟨Nat.le_of_mul_le_mul_left (sub a hx).2.1 (by omega),bad.1,div a bad.2⟩
      have bad := (Nat.mul_le_mul_right B.card factor).trans (bad_strip_count (by omega) hp B bp)
      let H := H₀*(r+1)+1
      have part : G.card + B.card = A.card := A.card_filter_add_card_filter_not ok
      have sum : H*A.card ≤ H*m+(C+r*(P+1)) := by
        rw [←part,Nat.mul_add]
        dsimp [H]
        nlinarith only [strong,bad]
      have positive : 1≤H := by dsimp [H]; omega
      have finish : H*A.card ≤ H*(m+K) := by
        rw [Nat.mul_add]
        have cf := Nat.mul_le_mul_right K positive
        dsimp [K] at cf ⊢
        omega
      exact Nat.le_of_mul_le_mul_left finish positive
    · by_contra! large
      have ex := majority m A (fun a ha => mem_Icc.mpr ⟨(sub a ha).1,(sub a ha).2.2⟩)
        (show m+D < A.card by dsimp [K] at large; omega) (by omega)
      obtain ⟨a,ha,b,hb,s⟩ := ex
      exact free a ha b (fun i => (hb i).1) (fun i => (hb i).2) s
  refine ⟨r+(r+1)*K,?_⟩
  intro N A sub free
  let m := (N+r)/(r+1)
  have dr := Nat.mod_add_div (N+r) (r+1)
  have rem := Nat.mod_lt (N+r) (show 0<r+1 by omega)
  have ends : N ≤ (r+1)*m ∧ (r+1)*m ≤ N+r := by dsimp [m]; omega
  have full (a) (ha : a∈A) : 0<a ∧ (r+1)*m ≤ (r+1)*a ∧ a ≤ (r+1)*m := by
    have h := sub a ha
    have lim : m ≤ a := by
      apply Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega : 0<r+1)).mpr ?_)
      nlinarith only [h.2.1]
    exact ⟨h.1,Nat.mul_le_mul_left _ lim,h.2.2.trans ends.1⟩
  have n := Nat.mul_le_mul_left (r+1) (rounded m A full free)
  rw [Nat.mul_add] at n
  omega

/-- For arity at least ten the conjectured bound holds whenever every member
is at least N/(r+1), for arbitrary integer endpoints N. -/
theorem shell_to_arity_succ (r : ℕ) (hr : 10 ≤ r) :
    ∃ K : ℕ, Shell r (r+1) K := by
  obtain ⟨C,cap⟩ := good_sparse_shell (r:=r) (by omega)
  obtain ⟨P,hP,div⟩ := bad_common_factor hr
  exact shell_of_paid_gap (by omega) (lt_of_lt_of_le (by positivity) hP) div (bad_factor_large hr hP) cap


end Erdos13ColumnModulo

end

section

/-  Local density saving using the wider shell estimate on the remaining tail. -/
namespace Erdos13ColumnModulo
open Finset FullColumns OMA.Erdos13ManyLayers

theorem local_gain_sparse_shell {r : ℕ} (hr : 5 ≤ r) :
    ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ), (∀ a ∈ A, 0<a ∧ (r+1)*m ≤ (r+1)*a ∧ a ≤ (r+1)*m) →
      (∀ a ∈ A, r*a < (r+1)*m → Good r a) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
      (localGain r*(r+1)+1)*A.card ≤ localGain r*((r+1)*m)+K := by
  classical
  obtain ⟨C,prev⟩ := shell_to_arity r (by omega)
  obtain ⟨D,old⟩ := sparse_top_stability r (by omega)
  obtain ⟨Cgood, goodBound⟩ := good_shell hr
  let F := 4*(r-1)*(r+1)-1
  let K₀ := 4*r*(r+1)*(3*F*(F*C+1)+12*r*((6*r+8)*r+1))
  let K := D+localGain r*C+K₀+Cgood
  refine ⟨K+(localGain r*(r+1)+1)*(2*cutoff r+1),?_⟩
  intro m A sub goods free sparse
  let N := (r+1)*m
  have pos (a) (ha : a ∈ A) := (sub a ha).1
  rw [←Nat.add_assoc (localGain r*((r+1)*m)) K]
  apply OMA.Erdos13UpperShell.select_large_scaled (L:=2*cutoff r) A pos
    (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a ha d hd dvd quot
  let B := A.filter (a<·)
  change (localGain r*(r+1)+1)*B.card ≤ localGain r*N+K
  have hBA : B ⊆ A := filter_subset _ _
  have hB : B ⊆ Ioc a N := fun x hx => mem_Ioc.mpr ⟨(mem_filter.mp hx).2,(sub x (hBA hx)).2.2⟩
  by_cases high : N ≤ r*a
  · have shell (x) (hx : x∈B) : 0<x ∧ N≤r*x ∧ x≤N :=
      ⟨pos x (hBA hx),high.trans (Nat.mul_le_mul_left r (mem_filter.mp hx).2.le),(sub x (hBA hx)).2.2⟩
    have freeB : Free r B := fun x hx f hf => free _ (hBA hx) f (fun i => hBA (hf i))
    have sp := Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl (s:=Ioc (r*m) N)) hBA))
    have h := old m B shell freeB (sp.trans sparse)
    have le : 24*r*r ≤ localGain r := by dsimp [localGain]; nlinarith [Nat.zero_le (r*r*r), Nat.zero_le (r*r*r*r)]
    have t := lift_gain le (prev N B shell freeB) h
    dsimp [K]
    omega
  · have bound := good_tail_strict hr (pos a ha) (by omega) (sub a ha).2.1 (goods a ha (by omega))
      hd dvd ha hBA hB free quot prev
    change localGain r*(r+1)*B.card+a ≤ localGain r*N+K₀ at bound
    have subB (x) (hx : x ∈ B) := sub x (hBA hx)
    have goodB (x) (hx : x ∈ B) := goods x (hBA hx)
    have freeB : Free r B := fun x hx f hf => free _ (hBA hx) f (fun i => hBA (hf i))
    have b := goodBound N B subB goodB freeB
    have ma := (sub a ha).2.1
    have sc := Nat.mul_le_mul_right Cgood (show 1 ≤ r+1 by omega)
    rw [Nat.one_mul] at sc
    have size : B.card ≤ a+Cgood := Nat.le_of_mul_le_mul_left (by
      calc (r+1)*B.card ≤ N+Cgood := b
           _ ≤ (r+1)*a+(r+1)*Cgood := Nat.add_le_add ma sc
           _ = (r+1)*(a+Cgood) := (Nat.mul_add ..).symm) (by omega)
    have out : (localGain r*(r+1)+1)*B.card ≤ localGain r*N+K₀+Cgood := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    dsimp [K]
    omega
end Erdos13ColumnModulo

end

section

/-  Four primes suffice for the sharper local estimate at arity nine. -/
namespace Erdos13ColumnModulo
open Finset OMA.Erdos13ManyLayers

lemma bad_nine : ∀ a, ¬Good 9 a → 46189 ∣ a := by
  intro a bad
  have f (p : ℕ) (hp : p.Prime) (lo : 9 < p) (hi : 4*p ≤ 82) : p ∣ a :=
    hp.dvd_iff_not_coprime.mpr (fun h => bad ⟨p,lo,hi,h⟩)
  have d₁ := f 11 (by decide) (by decide) (by decide)
  have d₂ := f 13 (by decide) (by decide) (by decide)
  have d₃ := f 17 (by decide) (by decide) (by decide)
  have d₄ := f 19 (by decide) (by decide) (by decide)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : (11*13*17).Coprime 19)
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : (11*13).Coprime 17)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : (11:ℕ).Coprime 13) d₁ d₂) d₃) d₄

/-- The conjectured bound on the shell down to N/(r+1) holds for all r ≥ 9. -/
theorem shell_down_to_ninth (r : ℕ) (hr : 9 ≤ r) : ∃ K : ℕ, Shell r (r+1) K := by
  by_cases h : 10 ≤ r
  · exact shell_to_arity_succ r h
  have eq : r=9 := by omega
  subst r
  obtain ⟨C,strict⟩ := local_gain_sparse_shell (r:=9) (by decide)
  exact shell_of_paid_gap (by decide) (by decide : 0<46189) bad_nine
    (by decide : localGain 9*(9+1)+1 ≤ 9*46189) strict


end Erdos13ColumnModulo

end

section

/-  # A global estimate via a cutoff on the obstructing cyclic quotient -/

namespace OMA.Erdos13Cyclic
open Finset

/-- The bound holds without any lower cutoff on members of A. The parameter K
balances the number of exceptional moduli and the cost of rounding densities. -/
theorem global_residue_bound {r N K : ℕ} (hr : 2 ≤ r) (hK : 0 < K) (A : Finset ℕ)
    (sub : A ⊆ Icc 1 N) (free : FullColumns.Free r A) :
    r * A.card ≤ N + r * (K + 1 + N / K) := by
  classical
  have witness (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases hne : (A.filter fun x => a < x).Nonempty
    · exact witness_of_free hr free (fun x hx => (mem_Icc.mp (sub hx)).1) a ha hne
    · rw [not_nonempty_iff_eq_empty] at hne
      refine ⟨a, (mem_Icc.mp (sub ha)).1, dvd_refl _, ?_, by simp [hne]⟩
      intro b hb hlt
      have hmem : b ∈ A.filter (a < ·) := mem_filter.mpr ⟨hb,hlt⟩
      simp [hne] at hmem
  choose! f pos div later size using witness
  let E := A.filter (fun a => f a ≤ K)
  have small : E.card ≤ K := by
    have count : E.card ≤ (Icc 1 K).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1,h.2⟩
      · intro x hx y hy he
        have hxA := (mem_filter.mp hx).1
        have hyA := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxA y hyA h (he ▸ div y hyA))
        · exact h
        · exact False.elim (later y hyA x hxA h (he ▸ div x hxA))
    simpa using count
  let G := A.filter (fun a => K < f a)
  by_cases hn : G.Nonempty
  · let a := G.min' hn
    have hag : a ∈ G := min'_mem _ _
    obtain ⟨haA,hdK⟩ := mem_filter.mp hag
    let d := f a
    let k := (N-a)/d + 1
    let T := A.filter (a < ·)
    have hd : 0 < d := pos a haA
    have hda : d ≤ a := Nat.le_of_dvd (mem_Icc.mp (sub haA)).1 (div a haA)
    have han := (mem_Icc.mp (sub haA)).2
    have kd : k*d ≤ N := by
      have := Nat.div_mul_le_self (N-a) d
      dsimp [k]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have kK : k ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr
      ((Nat.mul_le_mul_left k (show K ≤ d from hdK.le)).trans kd)
    have cover : T ⊆ Ioc a (a + k*d) := by
      intro b hb
      obtain ⟨hbA,hab⟩ := mem_filter.mp hb
      have := (mem_Icc.mp (sub hbA)).2
      have eqn := Nat.mod_add_div (N-a) d
      have rem := Nat.mod_lt (N-a) hd
      rw [mul_comm d _] at eqn
      apply mem_Ioc.mpr
      dsimp [k]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have cnt := OMA.Erdos13UpperShell.count_residues_in_blocks hd cover
    have hres := size a haA
    change r * (T.image (fun x => x % d)).card ≤ d+r-2 at hres
    have res' : r * (T.image (fun x => x % d)).card ≤ d+r := by omega
    have tail : r * T.card ≤ N + r * (N/K) := by
      have c1 := Nat.mul_le_mul_left r cnt
      have c2 := Nat.mul_le_mul_left k res'
      have c3 := Nat.mul_le_mul_left r kK
      nlinarith only [c1,c2,c3,kd]
    have contain : A ⊆ E ∪ insert a T := by
      intro x hx
      by_cases h : f x ≤ K
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have xG : x ∈ G := mem_filter.mpr ⟨hx,by omega⟩
        have xa : a ≤ x := min'_le _ _ xG
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cA := (card_le_card contain).trans (card_union_le _ _)
    have ci := card_insert_le a T
    have hA : A.card ≤ K + 1 + T.card := by omega
    have total := Nat.mul_le_mul_left r hA
    nlinarith only [total,tail]
  · have subE : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact hn ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left r ((card_le_card subE).trans small)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r, Nat.zero_le (r * (N/K))]

/-- A square-root choice of cutoff gives a bound uniform in the location of A. -/
theorem global_sqrt_bound {r N : ℕ} (hr : 2 ≤ r) (A : Finset ℕ)
    (sub : A ⊆ Icc 1 N) (free : FullColumns.Free r A) :
    r * A.card ≤ N + r * (2 * N.sqrt + 2) := by
  have hdiv : N / (N.sqrt + 1) < N.sqrt + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr
    (Nat.lt_succ_sqrt N)
  have h := global_residue_bound (K := N.sqrt + 1) hr (by omega) A sub free
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left r (by omega)) N)

end OMA.Erdos13Cyclic

end

section

/-  A strict saving on the wider sparse-top shell and its global consequence. -/
namespace Erdos13ColumnModulo
open Finset FullColumns

def shellWeight (r : ℕ) := 2*(localGain r*(r+1)+1)

lemma paid_twice {r : ℕ} (hr : 9 ≤ r) : ∃ P, 0<P ∧ shellWeight r ≤ r*P ∧
    ∀ a, ¬Good r a → P∣a := by
  by_cases large : 10 ≤ r
  · obtain ⟨P,hP,div⟩ := bad_common_factor large
    refine ⟨P,lt_of_lt_of_le (by positivity) hP,?_,div⟩
    refine le_trans ?_ (Nat.mul_le_mul_left r hP)
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le large
    dsimp [shellWeight,localGain]
    ring_nf
    omega
  · have eq : r=9 := by omega
    subst r
    refine ⟨2*46189,by decide,by decide,?_⟩
    intro a bad
    have two : 2∣a := Nat.prime_two.dvd_iff_not_coprime.mpr (fun c =>
      bad ⟨16,by decide,by decide,c.pow_left 4⟩)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : (2:ℕ).Coprime 46189) two (bad_nine a bad)

lemma sparse_gap_after_bad {r H P n C : ℕ} (hr : 0<r) (hp : 0<P) (hn : 1≤n)
    (div : ∀ a, ¬Good r a → P∣a) (pay : n*(H*(r+1)+1) ≤ (n-1)*(r*P))
    (cap : ∀ (m : ℕ) (G : Finset ℕ),
      (∀ a∈G, 0<a ∧ (r+1)*m ≤ (r+1)*a ∧ a ≤ (r+1)*m) →
      (∀ a∈G, r*a < (r+1)*m → Good r a) → Free r G →
      2*(Ioc (r*m) ((r+1)*m) ∩ G).card ≤ m → (H*(r+1)+1)*G.card ≤ H*((r+1)*m)+C) :
    ∃ K, ∀ (m : ℕ) (A : Finset ℕ),
    (∀ a∈A, 0<a ∧ m ≤ a ∧ a ≤ (r+1)*m) → Free r A →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    n*(H*(r+1)+1)*A.card + m ≤ n*(H*(r+1)+1)*m+K := by
  classical
  refine ⟨n*C+(n-1)*(r*(P+1)),?_⟩
  intro m A sub free sp
  let ok (a : ℕ) := r*a < (r+1)*m → Good r a
  let G := A.filter ok
  let B := A.filter (fun a => ¬ok a)
  have gsub : G ⊆ A := filter_subset _ _
  have strong := cap m G (fun a ha => ⟨(sub a (gsub ha)).1,
    Nat.mul_le_mul_left _ (sub a (gsub ha)).2.1,(sub a (gsub ha)).2.2⟩)
    (fun a ha => (mem_filter.mp ha).2) (fun a ha b hb => free a (gsub ha) b (fun i => gsub (hb i)))
    ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) gsub))).trans sp)
  have bp (a) (ha : a ∈ B) : m ≤ a ∧ r*a < (r+1)*m ∧ P ∣ a := by
    obtain ⟨hx,bad⟩ := mem_filter.mp ha
    change ¬(r*a < (r+1)*m → Good r a) at bad
    push Not at bad
    exact ⟨(sub a hx).2.1,bad.1,div a bad.2⟩
  have lim := Nat.mul_le_mul_left (n-1) (bad_strip_count hr hp B bp)
  have bad := Nat.mul_le_mul_right B.card pay
  have part : G.card + B.card = A.card := A.card_filter_add_card_filter_not ok
  rw [←part,Nat.mul_add]
  have strong' := Nat.mul_le_mul_left n strong
  have dec := congrArg (fun z : ℕ => z*m) (Nat.sub_add_cancel hn)
  nlinarith only [strong',bad,lim,dec]

/-- On the wider shell a top interval containing at most half its integers
forces a positive linear saving as soon as the arity is at least nine. -/
theorem wider_sparse_stability {r : ℕ} (hr : 9 ≤ r) : ∃ C, ∀ (m : ℕ) (A : Finset ℕ),
    (∀ a∈A, 0<a ∧ m ≤ a ∧ a ≤ (r+1)*m) → Free r A →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    shellWeight r*A.card + m ≤ shellWeight r*m+C := by
  obtain ⟨P,hp,factor,div⟩ := paid_twice hr
  obtain ⟨C,cap⟩ := local_gain_sparse_shell (r:=r) (by omega)
  exact sparse_gap_after_bad (n:=2) (by omega) hp (by decide) div (by simpa [shellWeight] using factor) cap

def globalWeight (r : ℕ) := 2*shellWeight r*(r+1)

/-- The coefficient of N in this uniform bound is strictly less than 1/r. -/
theorem global_of_sparse {r W C : ℕ} (hr : 3 ≤ r) (wpos : 0 < W)
    (shell : ∀ (m : ℕ) (A : Finset ℕ), (∀ a∈A, 0<a ∧ m ≤ a ∧ a ≤ (r+1)*m) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m → W*A.card+m ≤ W*m+C) :
    ∃ K : ℕ, ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 N → Free r A →
    (2*W*(r+1)*r+1)*A.card ≤ 2*W*(r+1)*N+K := by
  classical
  obtain ⟨D,majority⟩ := Erdos13HalfOccupied.majority_witness (r:=r) (by omega)
  let M := 2*W*(r+1)
  have mpos : 1 ≤ M := by
    change 0 < 2*W*(r+1)
    positivity
  let E := 2*(r*C+W*r*(2*W+1))
  let K := (r+1)*E+(M*r+1)*D
  have rounded (m) (A : Finset ℕ) (sub : A ⊆ Icc 1 ((r+1)*m)) (free : Free r A) :
      (M*r+1)*A.card ≤ M*((r+1)*m)+K := by
    by_cases sp : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m
    · let S := A.filter (m≤·)
      let L := A.filter fun a => ¬m≤a
      have sA : S ⊆ A := filter_subset _ _
      have lA : L ⊆ A := filter_subset _ _
      have cap := shell m S (fun a ha => ⟨(mem_Icc.mp (sub (sA ha))).1,
        (mem_filter.mp ha).2,(mem_Icc.mp (sub (sA ha))).2⟩)
        (fun a ha b hb => free a (sA ha) b (fun i => sA (hb i)))
        ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) sA))).trans sp)
      change W*S.card + m ≤ W*m+C at cap
      have low := OMA.Erdos13Cyclic.global_residue_bound (K:=2*W) (by omega : 2≤r) (by omega) L
        (fun a ha => mem_Icc.mpr ⟨(mem_Icc.mp (sub (lA ha))).1, le_of_lt (lt_of_not_ge (mem_filter.mp ha).2)⟩)
        (fun a ha b hb => free a (lA ha) b (fun i => lA (hb i)))
      have part : S.card+L.card=A.card := A.card_filter_add_card_filter_not (m≤·)
      have sc := Nat.mul_le_mul_left r cap
      have lc := Nat.mul_le_mul_left W low
      have rem := Nat.mul_le_mul_left r (Nat.div_mul_le_self m (2*W))
      have joint : 2*W*r*A.card + r*m ≤ 2*W*((r+1)*m)+E := by
        rw [←part]
        dsimp [E]
        nlinarith only [sc,lc,rem]
      have high := Nat.mul_le_mul_left (r+1) joint
      have cover := card_le_card sub
      simp only [Nat.card_Icc,Nat.add_one_sub_one] at cover
      have span : A.card ≤ r*((r+1)*m) := cover.trans
        (by simpa using Nat.mul_le_mul_right ((r+1)*m) (show 1 ≤ r by omega))
      change (2*W*(r+1)*r+1)*A.card ≤ 2*W*(r+1)*((r+1)*m)+K
      dsimp [K]
      nlinarith only [high,span,Nat.zero_le ((M*r+1)*D)]
    · have bd : A.card ≤ m+D := by
        by_contra! big
        obtain ⟨a,ha,b,hb,s⟩ := majority m A sub big (by omega)
        exact free a ha b (fun i => (hb i).1) (fun i => (hb i).2) s
      have h := Nat.mul_le_mul_left (M*r+1) bd
      have s := Nat.mul_le_mul_right m mpos
      dsimp [K]
      nlinarith only [h,s,Nat.zero_le ((r+1)*E)]
  refine ⟨K+M*r,?_⟩
  intro N A sub free
  let m := (N+r)/(r+1)
  have dr := Nat.mod_add_div (N+r) (r+1)
  have rem := Nat.mod_lt (N+r) (show 0<r+1 by omega)
  have ends : N ≤ (r+1)*m ∧ (r+1)*m ≤ N+r := by dsimp [m]; omega
  have out := rounded m A (fun a ha => mem_Icc.mpr ⟨(mem_Icc.mp (sub ha)).1,
    (mem_Icc.mp (sub ha)).2.trans ends.1⟩) free
  have sc := Nat.mul_le_mul_left M ends.2
  rw [Nat.mul_add] at sc
  change (M*r+1)*A.card ≤ M*N+(K+M*r)
  omega

/-- The coefficient of N in this uniform bound is strictly less than 1/r. -/
theorem global_strict_bound (r : ℕ) (hr : 9 ≤ r) : ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 N → Free r A →
    (globalWeight r*r+1)*A.card ≤ globalWeight r*N+C := by
  obtain ⟨C,shell⟩ := wider_sparse_stability hr
  exact global_of_sparse (by omega) (by dsimp [shellWeight]; omega) shell

end Erdos13ColumnModulo

end

section

/-  Combining local bounds on adjacent shells and absorbing square-root errors. -/
namespace OMA.Erdos13Universal
open Finset FullColumns OMA.Erdos13ManyLayers

lemma lift_weight {w W a m e : ℕ} (wp : 0<w) (bigger : w≤W)
    (h : w*a+m ≤ w*m+e) : W*a+m ≤ W*m+(W+1)*e := by
  have one := Nat.mul_le_mul_right e (show 1≤w by omega)
  have cap : a ≤ m+e := Nat.le_of_mul_le_mul_left (by rw [Nat.mul_add]; omega) wp
  have extra := Nat.mul_le_mul_left (W-w) cap
  have z := Nat.sub_add_cancel bigger
  have z₁ := congrArg (fun j : ℕ => j*a) z
  have z₂ := congrArg (fun j : ℕ => j*m) z
  have step := Nat.mul_le_mul_right e (Nat.sub_le W w)
  nlinarith only [extra,z₁,z₂,step,h]

lemma sqrt_absorb (r m C : ℕ) :
    2*C*(((r+1)*m).sqrt+1) ≤ m+2*C*(2*C*(r+1)+1) := by
  let z := ((r+1)*m).sqrt
  by_cases small : z ≤ 2*C*(r+1)
  · have b := Nat.mul_le_mul_left (2*C) (Nat.add_le_add_right small 1)
    dsimp [z] at b
    omega
  · have sq : z*z ≤ (r+1)*m := Nat.sqrt_le _
    have b := Nat.mul_le_mul_right z (le_of_not_ge small)
    have e : (r+1)*(2*C*z) ≤ (r+1)*m := by nlinarith only [sq,b]
    have h := Nat.le_of_mul_le_mul_left e (by omega : 0<r+1)
    change 2*C*(z+1) ≤ _
    nlinarith only [h,Nat.zero_le (C*C*(r+1))]

lemma sharp_shell_of_stability {r W C : ℕ} (hr : 3≤r) (wp : 0<W)
    (stable : ∀ (m : ℕ) (A : Finset ℕ), (∀ a∈A, 0<a ∧ m≤a ∧ a≤(r+1)*m) →
      Free r A → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m → W*A.card+m ≤ W*m+C) :
    ∃ K : ℕ, Shell r (r+1) K := by
  obtain ⟨D,major⟩ := Erdos13HalfOccupied.majority_witness hr
  refine ⟨r+(r+1)*(C+D),?_⟩
  intro N A sub free
  let m := (N+r)/(r+1)
  have eq := Nat.mod_add_div (N+r) (r+1)
  have rem := Nat.mod_lt (N+r) (show 0<r+1 by omega)
  have ends : N ≤ (r+1)*m ∧ (r+1)*m ≤ N+r := by dsimp [m]; omega
  have cover (a) (ha : a∈A) : 0<a ∧ m≤a ∧ a≤(r+1)*m := by
    have h := sub a ha
    refine ⟨h.1,?_,h.2.2.trans ends.1⟩
    apply Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega : 0<r+1)).mpr ?_)
    nlinarith only [h.2.1]
  have rd : A.card ≤ m+C+D := by
    by_cases sp : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m
    · have h := stable m A cover free sp
      have e := Nat.mul_le_mul_right C (show 1 ≤ W by omega)
      have t : A.card ≤ m+C := Nat.le_of_mul_le_mul_left (by rw [Nat.mul_add]; omega) wp
      omega
    · by_contra! big
      obtain ⟨a,ha,b,hb,d⟩ := major m A (fun a ha => mem_Icc.mpr ⟨(cover a ha).1,(cover a ha).2.2⟩)
        (by omega) (by omega)
      exact free a ha b (fun i => (hb i).1) (fun i => (hb i).2) d
  rw [Nat.add_assoc] at rd
  have bound := Nat.mul_le_mul_left (r+1) rd
  rw [Nat.mul_add] at bound
  omega

lemma many_below_m_of_stability {r W C : ℕ} (wp : 0<W)
    (stable : ∀ (m : ℕ) (A : Finset ℕ), (∀ a∈A, 0<a ∧ m≤a ∧ a≤(r+1)*m) →
      Free r A → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m → W*A.card+m ≤ W*m+C)
    (m : ℕ) (A : Finset ℕ) (sub : A ⊆ Icc 1 ((r+1)*m)) (free : Free r A)
    (large : m+C < A.card) (sp : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m) :
    m < W*(A.filter (fun x => x < m)).card := by
  let S := A.filter (fun x => ¬ x < m)
  have incl : S ⊆ A := filter_subset _ _
  have cap := stable m S (fun a ha => ⟨(mem_Icc.mp (sub (incl ha))).1,le_of_not_gt (mem_filter.mp ha).2,
    (mem_Icc.mp (sub (incl ha))).2⟩) (fun a ha b hb => free a (incl ha) b (fun i => incl (hb i)))
    ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) incl))).trans sp)
  have p : (A.filter (fun x => x < m)).card+S.card=A.card := A.card_filter_add_card_filter_not (fun x => x < m)
  have h := Nat.mul_lt_mul_of_pos_left large wp
  have c := Nat.mul_le_mul_right C (show 1≤W by omega)
  rw [←p,Nat.mul_add,Nat.mul_add] at h
  omega
end OMA.Erdos13Universal

end

section

/-  A sharp bound for sets avoiding multiples of three, including sets occupying
both of the other residue classes. -/
namespace Erdos13NoThreeMultiples

open Finset

lemma paired_residues (D : Finset ℕ) {q : ℕ} (cop : (3:ℕ).Coprime q)
    (avoid : ∀ b ∈ D, ¬3 ∣ b) :
    (D.image (·%(3*q))).card ≤ 2*(D.image (·%q)).card := by
  classical
  let R := D.image (·%q)
  have h := card_le_card_of_injOn (s := D.image (·%(3*q))) (t := Icc 1 2 ×ˢ R)
    (fun b => (b%3,b%q)) (by
      intro x hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hx
      have hzero : b%3 ≠ 0 := fun h => avoid b hb (Nat.dvd_of_mod_eq_zero h)
      have l := Nat.mod_lt b (by decide : 0<3)
      change (b%(3*q)%3, b%(3*q)%q) ∈ Icc 1 2 ×ˢ R
      rw [Nat.mod_mod_of_dvd b (dvd_mul_right 3 q), Nat.mod_mod_of_dvd b (dvd_mul_left q 3)]
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩, mem_image_of_mem _ hb⟩) (by
      intro x hx y hy he
      have eq := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
        ⟨(show x%3=y%3 from congrArg Prod.fst he), (show x%q=y%q from congrArg Prod.snd he)⟩
      obtain ⟨x',_,rfl⟩ := mem_image.mp hx
      obtain ⟨y',_,rfl⟩ := mem_image.mp hy
      simpa [Nat.ModEq] using eq)
  simpa [card_product, R] using h

lemma split_period (B : Finset ℕ) {v q t w : ℕ} (hq : 0<q)
    (cop : (3:ℕ).Coprime q) (avoid : ∀ b ∈ B, ¬3 ∣ b)
    (sub : B ⊆ Ico v (v+t*(3*q)+w)) (hw : w < 3*q) :
    ∃ u : ℕ, B.card ≤ t*(2*(B.image (·%q)).card)+u ∧
      u ≤ 2*(B.image (·%q)).card ∧
      (w ≤ q → u ≤ min w (B.image (·%q)).card) ∧
      (q ≤ w → w ≤ 2*q → u ≤ (B.image (·%q)).card + min (w-q) (B.image (·%q)).card) := by
  classical
  let P := B.filter fun b => b < v+t*(3*q)
  let S := B.filter fun b => ¬b < v+t*(3*q)
  let R := B.image (·%q)
  let U := B.image (·%(3*q))
  have inclP : P ⊆ Ico v (v+(t*(3*q)+0)) := by
    intro x hx
    obtain ⟨h,hh⟩ := mem_filter.mp hx
    exact mem_Ico.mpr ⟨(mem_Ico.mp (sub h)).1,by omega⟩
  have countP := Erdos13HalfOccupied.count_by_period (3*q) t 0 (by omega) U v P inclP
    (fun x hx => mem_image_of_mem _ (mem_filter.mp hx).1)
  have smallP : P.card ≤ t*(2*R.card) := by
    have b := Nat.mul_le_mul_left t (paired_residues B cop avoid)
    simp only [Nat.zero_min, Nat.add_zero] at countP
    exact countP.trans b
  have sincl : S ⊆ Ico (v+t*(3*q)) (v+t*(3*q)+w) := by
    intro x hx
    obtain ⟨h,hh⟩ := mem_filter.mp hx
    exact mem_Ico.mpr ⟨le_of_not_gt hh,(mem_Ico.mp (sub h)).2⟩
  have rmem (x) (hx : x ∈ S) : x%q ∈ R := mem_image_of_mem _ (mem_filter.mp hx).1
  have smem (x) (hx : x ∈ S) : x%(3*q) ∈ U := mem_image_of_mem _ (mem_filter.mp hx).1
  have ucap := Erdos13HalfOccupied.count_by_period (3*q) 0 w hw.le U _ S (by simpa using sincl) smem
  have uc : S.card ≤ 2*R.card := (show S.card ≤ U.card by simpa using ucap.trans (by simp)).trans (paired_residues B cop avoid)
  have part : P.card + S.card = B.card := B.card_filter_add_card_filter_not _
  refine ⟨S.card,?_,uc,?_,?_⟩
  · change B.card ≤ t*(2*R.card)+S.card
    omega
  · intro h
    simpa using Erdos13HalfOccupied.count_by_period q 0 w h R _ S (by simpa using sincl) rmem
  · intro lo hi
    have h := Erdos13HalfOccupied.count_by_period q 1 (w-q) (by omega) R _ S (by
      simpa [Nat.add_sub_of_le lo] using sincl) rmem
    simpa using h

lemma three_tail {r N a q : ℕ} (hr : 3 ≤ r) (low : 3*a ≤ N)
    (hq : 8*r < q) (qa : q ≤ a) (cop : (3:ℕ).Coprime q)
    (B : Finset ℕ) (avoid : ∀ b ∈ B, ¬3 ∣ b) (sub : B ⊆ Ioc a N)
    (hR : r*(B.image (·%q)).card ≤ q+r-2) : (r+1)*B.card ≤ N+5*r := by
  let c := (B.image (·%q)).card
  let t := (N-a)/(3*q)
  let w := (N-a)%(3*q)
  have dec : t*(3*q)+w = N-a := by simpa [t,w,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div (N-a) (3*q)
  have small : w < 3*q := Nat.mod_lt _ (by omega)
  have cover : B ⊆ Ico (a+1) ((a+1)+t*(3*q)+w) := by
    intro x hx
    have h := mem_Ioc.mp (sub hx)
    exact mem_Ico.mpr ⟨by omega,by omega⟩
  obtain ⟨u,cap,uc,short,mid⟩ := split_period B (by omega) cop avoid cover small
  change B.card ≤ t*(2*c)+u at cap
  change u ≤ 2*c at uc
  change w ≤ q → u ≤ min w c at short
  change q ≤ w → w ≤ 2*q → u ≤ c+min (w-q) c at mid
  change r*c ≤ q+r-2 at hR
  have rc : r*c ≤ q+r := by omega
  have rc3 := Nat.mul_le_mul_right c hr
  have full : (r+1)*(2*c) ≤ 3*q := by nlinarith only [rc,rc3,hq]
  have triple : (r+1)*(3*c) ≤ 4*q+4*r := by nlinarith only [rc,rc3]
  have spend (w' : ℕ) : (r+1)*min w' c ≤ q+r+w' := by
    have h := Nat.mul_le_mul_left r (min_le_right w' c)
    have hw := min_le_left w' c
    nlinarith only [h,hw,rc]
  have total := Nat.mul_le_mul_left (r+1) cap
  have number := Nat.sub_add_cancel (show a ≤ N by omega)
  by_cases wsmall : w ≤ q
  · have f := Nat.mul_le_mul_left t full
    have cost := (Nat.mul_le_mul_left (r+1) (short wsmall)).trans (spend w)
    nlinarith only [total,f,cost,dec,number,qa,Nat.zero_le r]
  by_cases wbig : 2*q ≤ w
  · have f := Nat.mul_le_mul_left t full
    have cost := (Nat.mul_le_mul_left (r+1) uc).trans full
    nlinarith only [total,f,cost,dec,number,qa,wbig,Nat.zero_le r]
  have ht : 0<t := by
    by_contra hx
    have hzero : t=0 := Nat.eq_zero_of_not_pos hx
    rw [hzero, Nat.zero_mul, Nat.zero_add] at dec
    omega
  have f := Nat.mul_le_mul_left (t-1) full
  have tdec : t-1+1=t := by omega
  have fm := congrArg (fun k : ℕ => k*(3*q)) tdec
  have fc := congrArg (fun k : ℕ => (r+1)*(k*(2*c))) tdec
  have cost := Nat.mul_le_mul_left (r+1) (mid (by omega) (by omega))
  have wdec := Nat.sub_add_cancel (show q ≤ w by omega)
  nlinarith only [total,f,fm,fc,triple,cost,spend (w-q),wdec,dec,number,qa]

/-- Every admissible set containing no multiple of three has the conjectured
bound, with no requirement on its distribution between classes one and two. -/
theorem no_three_multiples_bound (r : ℕ) (hr : 3 ≤ r) : ∃ C : ℕ,
    ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → (∀ b ∈ A, ¬3 ∣ b) →
      FullColumns.Free r A → (r+1)*A.card ≤ N+C := by
  let C := (128*r + 24*((r+1)*(16*r+1)+32*r+1)+2) + (r+1)*(64*r+1)
  refine ⟨(C+5*r)+(r+1)*(8*r+1), ?_⟩
  intro N A sub avoid free
  have pos (a : ℕ) (ha : a ∈ A) := (mem_Icc.mp (sub ha)).1
  rw [← Nat.add_assoc N]
  apply OMA.Erdos13UpperShell.select_large_quotient (N := N) (K := C+5*r) (L := 8*r) A pos
    (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a ha q hq dvd quotient
  let B := A.filter (a < ·)
  have hB : B ⊆ Ioc a N := by
    intro b hb
    have h := mem_filter.mp hb
    exact mem_Ioc.mpr ⟨h.2,(mem_Icc.mp (sub h.1)).2⟩
  have good : B ⊆ A := filter_subset _ _
  by_cases low : 3*a ≤ N
  · have cop : (3:ℕ).Coprime q := Nat.prime_three.coprime_iff_not_dvd.mpr
      (fun hz => avoid a ha (hz.trans dvd))
    have t := three_tail hr low hq (Nat.le_of_dvd (pos a ha) dvd) cop B
      (fun b hb => avoid b (good hb)) hB quotient
    change (r+1)*B.card ≤ _
    omega
  · have hs : ∀ b ∈ B, 0<b ∧ N ≤ 3*b ∧ b ≤ N := by
      intro b hb
      have h := mem_Ioc.mp (hB hb)
      exact ⟨by omega,by omega,h.2⟩
    have hf : FullColumns.Free r B := fun a ha b hb => free a (good ha) b (fun i => good (hb i))
    have h := OMA.Erdos13UpperShell.bound_on_third_shell hr B hs hf
    change (r+1)*B.card ≤ _
    dsimp [C]
    omega

end Erdos13NoThreeMultiples

end

section

/-  A strict density gap for sets avoiding multiples of three. -/

namespace Erdos13NoThreeMultiples

open Finset

lemma third_count {v e : ℕ} {S : Finset ℕ} (sub : S ⊆ Ico v (v+e))
    {R : Finset ℕ} (mem : ∀ x ∈ S, x%3 ∈ R) :
    3*S.card ≤ e*R.card+2*R.card := by
  have decomp : e/3*3 + e%3 = e := by omega
  have h := Erdos13HalfOccupied.count_by_period 3 (e/3) (e%3) (by omega) R v S
    (by rwa [decomp]) mem
  have u := min_le_right (e%3) R.card
  by_cases small : e%3=0
  · rw [small,Nat.zero_min,Nat.add_zero] at h
    have t := congrArg (fun k : ℕ => k*R.card) decomp
    rw [small] at t
    nlinarith only [h,t,Nat.zero_le R.card]
  · have t := congrArg (fun k : ℕ => k*R.card) decomp
    have frac := Nat.mul_le_mul_right R.card (show 1 ≤ e%3 by omega)
    nlinarith only [h,t,frac,u]

lemma one_only {v q e : ℕ} {S : Finset ℕ} (hq : 0<q) (small : e≤q)
    (sub : S ⊆ Ico v (v+q+e)) (avoid : ∀ x ∈ S, ¬3∣x)
    (cop : (3:ℕ).Coprime q) :
    3*S.card ≤ 3*(S.image (·%q)).card+e+2 := by
  classical
  let D := S.filter fun x => v+q ≤ x ∧ x-q ∈ S
  let G := S.filter fun x => ¬(v+q ≤ x ∧ x-q ∈ S)
  have dsub : D ⊆ Ico (v+q) (v+q+e) := by
    intro x hx
    have h := mem_filter.mp hx
    exact mem_Ico.mpr ⟨h.2.1,(mem_Ico.mp (sub h.1)).2⟩
  have dres (x) (hx : x ∈ D) : x%3 ∈ ({(2*q)%3} : Finset ℕ) := by
    have h := mem_filter.mp hx
    have ha : x%3 ≠ 0 := fun hz => avoid x h.1 (Nat.dvd_of_mod_eq_zero hz)
    have hb : (x-q)%3 ≠ 0 := fun hz => avoid (x-q) h.2.2 (Nat.dvd_of_mod_eq_zero hz)
    have hc : q%3 ≠ 0 := fun hz =>
      (Nat.prime_three.coprime_iff_not_dvd.mp cop) (Nat.dvd_of_mod_eq_zero hz)
    apply mem_singleton.mpr
    have hqx : q ≤ x := by have := h.2.1; omega
    have eq₀ : (x-q)+q=x := Nat.sub_add_cancel hqx
    have eq₁ : x%3 = ((x-q)%3+q%3)%3 := by rw [← Nat.add_mod,eq₀]
    have eq₂ : (2*q)%3 = (2*(q%3))%3 := by rw [Nat.mul_mod]
    rw [eq₂]
    have hqr := Nat.mod_lt q (by decide : 0<3)
    have hxr := Nat.mod_lt (x-q) (by decide : 0<3)
    rcases (show q%3=1 ∨ q%3=2 by omega) with c|c <;>
      rcases (show (x-q)%3=1 ∨ (x-q)%3=2 by omega) with d|d <;>
      simp_all
  have countD := third_count dsub dres
  simp only [card_singleton,Nat.mul_one] at countD
  have uniq (x y : ℕ) (hx : x ∈ G) (hy : y ∈ G) (lt : x<y) (eq : x%q=y%q) : False := by
    have sx := mem_filter.mp hx
    have sy := mem_filter.mp hy
    have ix := mem_Ico.mp (sub sx.1)
    have iy := mem_Ico.mp (sub sy.1)
    have e : x ≡ y [MOD q] := eq
    obtain ⟨t,ht⟩ := (Nat.modEq_iff_dvd' lt.le).mp e
    have tpos : 0<t := by
      by_contra hn
      have hzero := Nat.eq_zero_of_not_pos hn
      rw [hzero,Nat.mul_zero] at ht
      omega
    have ts : t<2 := by
      by_contra! hn
      have hh := Nat.mul_le_mul_left q hn
      omega
    have ht1 : t=1 := by omega
    rw [ht1,Nat.mul_one] at ht
    exact sy.2 ⟨by omega,(show y-q=x by omega) ▸ sx.1⟩
  have countG : G.card ≤ (S.image (·%q)).card := by
    apply card_le_card_of_injOn (fun x => x%q)
    · intro x hx
      exact mem_image_of_mem _ (mem_filter.mp hx).1
    · intro x hx y hy eq
      rcases lt_trichotomy x y with lt|he|lt
      · exact (uniq x y hx hy lt eq).elim
      · exact he
      · exact (uniq y x hy hx lt eq.symm).elim
  have part : D.card + G.card = S.card := S.card_filter_add_card_filter_not _
  omega

lemma three_gap_tail {r N a q : ℕ} (hr : 3 ≤ r) (hq : 32*r < q) (qa : q ≤ a)
    (cop : (3:ℕ).Coprime q) (B : Finset ℕ) (avoid : ∀ b ∈ B, ¬3∣b)
    (han : a ≤ N) (sub : B ⊆ Ioc a N) (hR : r*(B.image (·%q)).card ≤ q+r-2) :
    (3*r+4)*B.card ≤ 3*N+6*r+6 := by
  classical
  let c := (B.image (·%q)).card
  let t := (N-a)/(3*q)
  let w := (N-a)%(3*q)
  let v := a+1+t*(3*q)
  let P := B.filter fun b => b < v
  let S := B.filter fun b => ¬b < v
  have dec : t*(3*q)+w = N-a := by simpa [t,w,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div (N-a) (3*q)
  have endpt := Nat.sub_add_cancel han
  have small : w < 3*q := Nat.mod_lt _ (by omega)
  have incP : P ⊆ Ico (a+1) (a+1+(t*(3*q)+0)) := by
    intro x hx
    have h := mem_filter.mp hx
    exact mem_Ico.mpr ⟨by have := (mem_Ioc.mp (sub h.1)).1; omega, by simpa [v] using h.2⟩
  have incS : S ⊆ Ico v (v+w) := by
    intro x hx
    have h := mem_filter.mp hx
    exact mem_Ico.mpr ⟨le_of_not_gt h.2,by dsimp [v]; have := (mem_Ioc.mp (sub h.1)).2; omega⟩
  have incB : S ⊆ B := filter_subset _ _
  have noS (x) (hx : x ∈ S) := avoid x (incB hx)
  let R := B.image (·%(3*q))
  have capR : R.card ≤ 2*c := paired_residues B cop avoid
  have capP : P.card ≤ t*(2*c) := by
    have h := Erdos13HalfOccupied.count_by_period (3*q) t 0 (by omega) R (a+1) P
      incP (fun x hx => mem_image_of_mem _ (mem_filter.mp hx).1)
    simp only [Nat.zero_min,Nat.add_zero] at h
    exact h.trans (Nat.mul_le_mul_left _ capR)
  have capS : S.card ≤ 2*c := by
    have h := Erdos13HalfOccupied.count_by_period (3*q) 0 w small.le R v S
      (by simpa using incS) (fun x hx => mem_image_of_mem _ (incB hx))
    simp only [Nat.zero_mul,Nat.zero_add] at h
    exact (h.trans (min_le_right _ _)).trans capR
  have cardS : (S.image (·%q)).card ≤ c := card_le_card (image_subset_image incB)
  change r*c ≤ q+r-2 at hR
  have rc : r*c ≤ q+r := by omega
  have rc3 := Nat.mul_le_mul_right c hr
  have full : (3*r+4)*(2*c) ≤ 9*q := by nlinarith only [rc,rc3,hq]
  have cost : (3*r+4)*S.card ≤ 3*a+3*w+6*r+6 := by
    by_cases short : w≤q
    · have h := Erdos13HalfOccupied.count_by_period q 0 w short (S.image (·%q)) v S
        (by simpa using incS) (fun x hx => mem_image_of_mem _ hx)
      simp only [Nat.zero_mul,Nat.zero_add] at h
      have sc := ((h.trans (min_le_right _ _)).trans cardS)
      have rsc := (Nat.mul_le_mul_left r sc).trans rc
      have th := third_count (R := Icc 1 2) incS (fun x hx => by
        have h₁ : x%3 ≠ 0 := fun hz => noS x hx (Nat.dvd_of_mod_eq_zero hz)
        have h₂ := Nat.mod_lt x (by decide : 0<3)
        exact mem_Icc.mpr ⟨by omega,by omega⟩)
      simp at th
      nlinarith only [rsc,th,qa,Nat.zero_le r,Nat.zero_le w]
    by_cases high : 2*q ≤ w
    · have sc := (Nat.mul_le_mul_left (3*r+4) capS).trans full
      nlinarith only [sc,high,qa,Nat.zero_le r]
    let e := w-q
    have ed : e+q = w := Nat.sub_add_cancel (by omega)
    have short2 : e≤q := by omega
    have inc2 : S ⊆ Ico v (v+q+e) := by simpa only [show v+q+e=v+w by omega] using incS
    have central := one_only (by omega : 0<q) short2 inc2 noS cop
    have f := Nat.mul_le_mul_left (3*r-5) capS
    have h5 : 3*r-5+5=3*r := by omega
    have hs := congrArg (fun x : ℕ => x*S.card) h5
    have hc := congrArg (fun x : ℕ => x*(2*c)) h5
    nlinarith only [central,cardS,f,hs,hc,rc,qa,ed,Nat.zero_le c]
  have part : P.card + S.card = B.card := B.card_filter_add_card_filter_not _
  have fc := Nat.mul_le_mul_left t full
  have pc := Nat.mul_le_mul_left (3*r+4) capP
  rw [← part]
  nlinarith only [fc,pc,cost,dec,endpt]

/-- A set in the two nonzero residue classes modulo three has a uniform
density gap below the conjectured threshold. -/
theorem no_three_multiples_gap (r : ℕ) (hr : 3 ≤ r) (N : ℕ) (A : Finset ℕ)
    (sub : A ⊆ Icc 1 N) (avoid : ∀ b ∈ A, ¬3∣b) (free : FullColumns.Free r A) :
    A.card ≤ (3*N+6*r+6)/(3*r+4)+(32*r+1) := by
  let M := (3*N+6*r+6)/(3*r+4)
  have pos (a : ℕ) (ha : a ∈ A) := (mem_Icc.mp (sub ha)).1
  have select := OMA.Erdos13UpperShell.select_large_quotient (r:=r) (N := (r+1)*M) (K := 0)
    (L := 32*r) A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos) (by
      intro a ha q hq dvd quot
      let B := A.filter (a < ·)
      have hB : B ⊆ Ioc a N := by
        intro b hb
        have h := mem_filter.mp hb
        exact mem_Ioc.mpr ⟨h.2,(mem_Icc.mp (sub h.1)).2⟩
      have cop : (3:ℕ).Coprime q := Nat.prime_three.coprime_iff_not_dvd.mpr
        (fun hz => avoid a ha (hz.trans dvd))
      have bound := three_gap_tail hr hq (Nat.le_of_dvd (pos a ha) dvd) cop B
        (fun b hb => avoid b (mem_filter.mp hb).1) (mem_Icc.mp (sub ha)).2 hB quot
      have divbound : B.card ≤ M := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [Nat.mul_comm] using bound)
      simpa only [Nat.add_zero] using Nat.mul_le_mul_left (r+1) divbound)
  have bound : (r+1)*A.card ≤ (r+1)*(M+(32*r+1)) := by
    simpa only [Nat.add_zero,Nat.mul_add] using select
  exact Nat.le_of_mul_le_mul_left bound (by omega)

end Erdos13NoThreeMultiples

end

section

/-  A strict sparse-tail bound at the last complete column layer. -/

namespace OMA.Erdos13Mixed
open Finset FullColumns

private lemma multiples_outside {r a : ℕ} {B : Finset ℕ} (div : 3∣a)
    (layer : ∀ b∈B,b/a∈Icc 1 r) (avoid : ∀ x∈complete B a r, ¬3∣x) :
    (B.filter (3∣·)).card+r*(complete B a r).card ≤ r*(B.image (·%a)).card := by
  classical
  let R := B.image (·%a)
  let P := complete B a r
  let T := B.filter (3∣·)
  have inc : P⊆R := filter_subset _ _
  have inj : T.card ≤ ((R\P) ×ˢ (Icc 1 r)).card := by
    apply card_le_card_of_injOn (fun x => (x%a,x/a))
    · intro x hx
      obtain ⟨xb,xd⟩ := mem_filter.mp hx
      apply mem_product.mpr
      refine ⟨mem_sdiff.mpr ⟨mem_image_of_mem _ xb,?_⟩,layer x xb⟩
      intro full
      apply avoid _ full
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.mod_mod_of_dvd x div,Nat.mod_eq_zero_of_dvd xd]
    · intro x _ y _ eq
      have e₁ := congrArg Prod.fst eq
      have e₂ := congrArg Prod.snd eq
      change x%a=y%a at e₁
      change x/a=y/a at e₂
      have h₁ := Nat.div_add_mod x a
      have h₂ := Nat.div_add_mod y a
      rw [e₁,e₂,h₂] at h₁
      exact h₁.symm
  have part : (R\P).card+P.card=R.card := card_sdiff_add_card_eq_card inc
  simp only [card_product,Nat.card_Icc,Nat.add_sub_cancel] at inj
  have rhs := congrArg (fun x : ℕ => r*x) part
  change T.card+r*P.card ≤ r*R.card
  nlinarith only [rhs,inj]

private lemma three_global {a N : ℕ} {A B : Finset ℕ} (ha : 0<a)
    (sub : B⊆Ioc a N) (inc : B⊆A) (free : Free 3 A) (layer : ∀ b∈B,b/a∈Icc 1 3)
    (div : 3∣a) (avoid : ∀ x∈complete B a 3, ¬3∣x) {e : ℕ}
    (res : 3*(B.image (·%a)).card≤a+e) :
    52*B.card≤3*N+39*a+39*e+1285 := by
  let S := B.filter (fun b => ¬3∣b)
  have h := Erdos13NoThreeMultiples.no_three_multiples_gap 3 (by decide) N S
    (fun b hb => mem_Icc.mpr ⟨by have := (mem_Ioc.mp (sub (mem_filter.mp hb).1)).1; omega,
      (mem_Ioc.mp (sub (mem_filter.mp hb).1)).2⟩)
    (fun b hb => (mem_filter.mp hb).2)
    (fun b hb y hy => free b (inc (mem_filter.mp hb).1) y (fun i => inc (mem_filter.mp (hy i)).1))
  have bigger := Nat.mul_le_mul_left 13 h
  have floor := Nat.div_mul_le_self (3*N+24) 13
  have split := B.card_filter_add_card_filter_not (3∣·)
  have count := FullColumns.card_bound (B:=B) (a:=a) (J:=3) (by decide) layer
  have mult := multiples_outside div layer avoid
  change _ + S.card = _ at split
  simp only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at bigger count
  omega

theorem critical_tail_gap (r F K : ℕ) (hr : 3≤r) (hF : 0<F) :
    ∃ M>0, ∃ C : ℕ, ∀ (m a : ℕ) (A B : Finset ℕ),
      let N := (r+1)*m
      let R := (B.image (·%a)).card
      let P := complete B a r
      0<a → r*a≤N → N≤(r+1)*a → B⊆Ioc a N → (∀ b∈B,b/a∈Icc 1 r) →
      B⊆A → Free r A → r*R≤a+K*(N.sqrt+1) →
      ((F*r+1)*P.card≤F*a ∨ (r=3 ∧ 3∣a ∧ ∀ u∈P,¬3∣u)) →
      M*(r+1)*B.card+m≤M*N+C*(N.sqrt+1) := by
  obtain ⟨k,full⟩ := complete_sqrt_bound r hr
  let H := F*r+1
  let j := r-1
  let U := j*K+k
  let V := 169*(H*r*U+H*j*K)
  let W := H*r*4*(39*U+39*K+1285)
  refine ⟨169*H*r,by dsimp [H]; positivity,V+W,?_⟩
  intro m a A B
  dsimp only
  intro ha small top sub layer inc free res cases
  let N := (r+1)*m
  let z := N.sqrt+1
  let R := (B.image (·%a)).card
  let P := complete B a r
  let b := B.card
  have ma : m≤a := Nat.le_of_mul_le_mul_left top (by omega)
  have jr : j+1=r := by dsimp [j]; omega
  have ct : b ≤ j*R + P.card := FullColumns.card_bound (by omega) layer
  have rp : r*R≤a+K*z := res
  have ps : P⊆Icc 1 (N-r*a) := by
    intro x hx
    have rows := (mem_filter.mp hx).2
    have lo := (mem_Ioc.mp (sub (rows 1 (mem_Icc.mpr ⟨le_rfl,by omega⟩)))).1
    have hi := (mem_Ioc.mp (sub (rows r (mem_Icc.mpr ⟨by omega,le_rfl⟩)))).2
    simp only [one_mul] at lo
    exact mem_Icc.mpr ⟨by omega,by change r*a+x≤N at hi; omega⟩
  have sz : (N-r*a).sqrt ≤ z := (Nat.sqrt_le_sqrt (Nat.sub_le _ _)).trans (by dsimp [z]; omega)
  have pp : r*P.card≤N-r*a+k*z :=
    (full _ _ _ _ inc free ps).trans (Nat.add_le_add_left (Nat.mul_le_mul_left k sz) _)
  have core : r*b+a ≤ r*a+j*K*z+r*P.card := by
    have l := Nat.mul_le_mul_left r ct
    have rr := Nat.mul_le_mul_left j rp
    have ss := congrArg (fun n : ℕ => n*a) jr
    nlinarith only [l,rr,ss]
  have basic : r*b+a ≤ N+U*z := by
    have exactD := Nat.sub_add_cancel (show r*a≤N from small)
    dsimp [U]
    nlinarith only [core,pp,exactD]
  have mulH : 0<H*r := by dsimp [H]; positivity
  have mn : m≤N := Nat.le_mul_of_pos_left _ (by omega)
  have zp : 1≤z := by dsimp [z]; omega
  change 169*H*r*(r+1)*b+m≤169*H*r*N+(V+W)*z
  rcases cases with gap|⟨eq,div,avoid⟩
  · have gap' : H*P.card≤F*a := gap
    have thin : H*r*b+a≤H*r*a+H*j*K*z := by
      have lhs := Nat.mul_le_mul_left H core
      have rhs := Nat.mul_le_mul_left r gap'
      have ed := congrArg (fun n : ℕ => n*a) (show H=F*r+1 from rfl)
      nlinarith only [lhs,rhs,ed]
    have mixed := Nat.mul_le_mul_left (H*r) basic
    have fin : H*r*(r+1)*b+a≤H*r*N+(H*r*U+H*j*K)*z := by
      nlinarith only [mixed,thin]
    have sc := Nat.mul_le_mul_left 169 fin
    dsimp [V]
    nlinarith only [sc,ma,Nat.zero_le a,Nat.zero_le (W*z)]
  · have f3 : Free 3 A := eq ▸ free
    have ly3 : ∀ b∈B,b/a∈Icc 1 3 := eq ▸ layer
    have av3 : ∀ x∈complete B a 3,¬3∣x := by simpa only [P,eq] using avoid
    have res3 : 3*R≤a+K*z := by simpa only [eq] using rp
    have bd : 52*b≤3*N+39*a+39*(K*z)+1285 :=
      three_global ha sub inc f3 ly3 div av3 res3
    have bas3 : 3*b+a≤N+U*z := by simpa only [eq] using basic
    have combined : 169*b≤42*N+39*U*z+39*K*z+1285 := by nlinarith only [bas3,bd]
    have pre : 169*(3+1)*b+m≤169*N+4*(39*U+39*K+1285)*z := by
      nlinarith only [combined,mn,zp]
    have sc := Nat.mul_le_mul_left (H*r) pre
    have high := Nat.le_mul_of_pos_left m mulH
    dsimp [W]
    rw [eq] at sc high ⊢
    nlinarith only [sc,high,Nat.zero_le (V*z)]

end OMA.Erdos13Mixed

end

section

/-  A cyclic obstruction giving a strict saving for complete columns,
apart from an explicit exceptional case at arity three. -/
namespace Erdos13ColumnModulo
open Finset FullColumns
open scoped Pointwise

lemma scalar_card {q : ℕ} (k : ℕ) (kp : 0<k) [NeZero q] (R : Finset (ZMod q)) :
    R.card ≤ k*(R.image (fun x => k • x)).card := by
  let f (x : ZMod q) := (k • x,k*x.val/q)
  let T := R.image (fun x => k • x) ×ˢ range k
  have incl (x : ZMod q) (hx : x ∈ R) : f x ∈ T := by
    apply mem_product.mpr
    exact ⟨mem_image_of_mem _ hx,mem_range.mpr ((Nat.div_lt_iff_lt_mul (NeZero.pos q)).mpr
      (Nat.mul_lt_mul_of_pos_left x.val_lt kp))⟩
  have inject (x : ZMod q) : (k • x).val = (k*x.val)%q := by
    have eq : (k • x : ZMod q) = ((k*x.val:ℕ):ZMod q) := by
      simp [nsmul_eq_mul]
    rw [eq,ZMod.val_natCast]
  have count := card_le_card_of_injOn f incl (by
    intro x hx y hy he
    have h₁ := congrArg (fun t : ZMod q × ℕ => t.1.val) he
    have h₂ := congrArg Prod.snd he
    change (k • x).val = (k • y).val at h₁
    change k*x.val/q = k*y.val/q at h₂
    rw [inject,inject] at h₁
    have xq := Nat.mod_add_div (k*x.val) q
    have yq := Nat.mod_add_div (k*y.val) q
    rw [h₁,h₂] at xq
    exact ZMod.val_injective q (Nat.eq_of_mul_eq_mul_left kp (by omega)))
  simpa [T,Nat.mul_comm] using count

lemma unrestricted_cycle {q r L : ℕ} [NeZero q] (hr : 3≤r)
    (R : Finset (ZMod q)) (hne : R.Nonempty) (aper : (r • R).addStab = {0})
    (excluded : ∀ x ∈ R, ∀ j ∈ Ioc r (r+L), j • x ∉ r • R) :
    r*R.card+L ≤ q+(r-1) ∧
    (∀ x ∈ R, L < addOrderOf x) ∧
    (∀ j ∈ Ioc r (r+L), j*(r*R.card)+R.card ≤ j*(q+(r-1)) ∧
        (j.Coprime q → (r+1)*R.card ≤ q+(r-1))) := by
  classical
  let S := r • R
  have growth : r*R.card ≤ S.card+(r-1) := by
    have h := Finset.card_nsmul_bound (r:=r) (by omega) R hne
    rwa [aper,card_singleton,Nat.mul_one] at h
  have pair (T : Finset (ZMod q)) (disj : Disjoint S T) : S.card+T.card ≤ q := by
    have count := (S∪T).card_le_univ
    rwa [card_union_of_disjoint disj,ZMod.card] at count
  have order_guard (x) (hx : x ∈ R) : L < addOrderOf x := by
    have pos := addOrderOf_pos x
    by_contra! h
    have bad := excluded x hx (r+addOrderOf x) (mem_Ioc.mpr ⟨by omega,by omega⟩)
    rw [add_nsmul,addOrderOf_nsmul_eq_zero,add_zero] at bad
    exact bad (nsmul_mem_nsmul hx)
  obtain ⟨x,hx⟩ := hne
  have orde := order_guard x hx
  let f (i : ℕ) := (r+1+i) • x
  have E := pair ((range L).image f) (disjoint_left.mpr (by
    intro y hy h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    have := mem_range.mp hi
    exact excluded x hx _ (mem_Ioc.mpr ⟨by omega,by omega⟩) hy))
  have cardF : ((range L).image f).card=L := by
    rw [card_image_of_injOn,card_range]
    intro i hi j hj eq
    have same := (nsmul_eq_nsmul_iff_modEq.mp eq).add_left_cancel' (r+1)
    have iord := (mem_range.mp hi).trans orde
    have jord := (mem_range.mp hj).trans orde
    simpa [Nat.ModEq,Nat.mod_eq_of_lt iord,Nat.mod_eq_of_lt jord] using same
  rw [cardF] at E
  refine ⟨by omega,order_guard,?_⟩
  intro j hj
  have jp : 0<j := by have := (mem_Ioc.mp hj).1; omega
  let V := R.image (fun x => j • x)
  have packing := pair V (disjoint_left.mpr (by
    intro z hz h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    exact excluded x hx j hj hz))
  have sc := scalar_card j jp R
  change R.card ≤ j*V.card at sc
  have jpack := Nat.mul_le_mul_left j packing
  have jgrowth := Nat.mul_le_mul_left j growth
  refine ⟨by nlinarith only [sc,jgrowth,jpack],?_⟩
  intro cop
  have h : V.card=R.card := card_image_of_injective _ (coprime_scalar cop)
  rw [h] at packing
  rw [Nat.add_mul,Nat.one_mul]
  omega

lemma small_three_unit {q : ℕ} (hp : 0<q) (sm : q ≤ 24) (dvd : 3 ∣ q) :
    (4:ℕ).Coprime q ∨ (5:ℕ).Coprime q := by
  obtain ⟨v,rfl⟩ := dvd
  have hi : v ≤ 8 := by omega
  have vp : 0<v := by omega
  interval_cases v <;> decide

def densityFactor (r : ℕ) := 2*(r+1)*r

theorem universal_cycle {q r : ℕ} [NeZero q] (hr : 3≤r)
    (R : Finset (ZMod q)) (hne : R.Nonempty) (aper : (r • R).addStab = {0})
    (excluded : ∀ x ∈ R, ∀ j ∈ Ioc r ((r*r+1)/2), j • x ∉ r • R) :
    (densityFactor r*r+1)*R.card ≤ densityFactor r*q ∨
      (r=3 ∧ (q=3 ∨ q=6) ∧ ∀ x ∈ R, 2 < addOrderOf x) := by
  let L := (r*r+1)/2-r
  have quad := Nat.mul_le_mul_left r hr
  have rL : r+L=(r*r+1)/2 := by dsimp [L]; omega
  have ll : 2 ≤ L := by dsimp [L]; omega
  obtain ⟨span,guard,per⟩ := unrestricted_cycle (L:=L) hr R hne aper (by rwa [rL])
  have one := (per (r+1) (mem_Ioc.mpr ⟨by omega,by omega⟩)).1
  let s := R.card
  change r*s+L ≤ q+(r-1) at span
  change (r+1)*(r*s)+s ≤ (r+1)*(q+(r-1)) at one
  by_cases strict : r*s<q
  · left
    change (densityFactor r*r+1)*s ≤ densityFactor r*q
    by_cases big : 2*(r+1)*(r-1) ≤ s
    · have cut : (2*(r+1)*r+1)*s ≤ 2*(r+1)*q := by nlinarith only [one,big]
      have diff := Nat.mul_le_mul_left (densityFactor r-2*(r+1)) strict.le
      have band : 2*(r+1) ≤ densityFactor r := by
        exact (by simpa only [Nat.mul_one,densityFactor] using Nat.mul_le_mul_left (2*(r+1)) (show 1≤r by omega))
      have dec := Nat.sub_add_cancel band
      have eqL := congrArg (fun z : ℕ => z*(r*s)) dec
      have eqR := congrArg (fun z : ℕ => z*q) dec
      nlinarith only [cut,diff,eqL,eqR]
    · have small : s ≤ densityFactor r :=
        (le_of_lt (lt_of_not_ge big)).trans (Nat.mul_le_mul_left _ (Nat.sub_le r 1))
      have diff := Nat.mul_le_mul_left (densityFactor r) (show r*s+1≤q by omega)
      nlinarith only [diff,small]
  · right
    have eqr : r=3 := by
      by_contra! no
      have g : 4≤r := by omega
      have sq := Nat.mul_le_mul_left r g
      have cut : r≤L := by dsimp [L]; omega
      omega
    subst r
    have lval : L=2 := by decide
    have eq : 3*s=q := by omega
    have sm : q≤24 := by omega
    have cop := small_three_unit (NeZero.pos q) sm (show 3∣q from ⟨s,eq.symm⟩)
    have sharp : 4*s ≤ q+2 := by
      rcases cop with h|h
      · exact (per 4 (mem_Ioc.mpr ⟨by decide,by omega⟩)).2 h
      · exact (per 5 (mem_Ioc.mpr ⟨by decide,by omega⟩)).2 h
    have hp := NeZero.pos q
    exact ⟨rfl,by omega,by simpa [lval] using guard⟩

/-- Complete columns are uniformly sparse throughout their full ambient period.
The only exception forces arity three and removes all multiples of three. -/
theorem complete_universal {r a : ℕ} (hr : 3≤r) (ha : 0<a) (P : Finset ℕ)
    {A : Finset ℕ} (off : ∀ u ∈ P, 0 < u ∧ u<a)
    (lifts : ∀ u ∈ P, ∀ i ∈ Icc 1 r, i*a+u ∈ A) (free : Free r A) :
    (densityFactor r*r+1)*P.card ≤ densityFactor r*a ∨
      r=3 ∧ 3∣a ∧ ∀ u ∈ P, ¬3∣u := by
  classical
  by_cases hn : P.Nonempty
  · let L := (r*r+1)/2-r
    have quad := Nat.mul_le_mul_left r hr
    have rL : r+L=(r*r+1)/2 := by dsimp [L]; omega
    obtain ⟨q,hq,dvd,aper,excluded⟩ := reduce_columns (r:=r) (L:=L) ha P hn (by
      intro u hu j hj f hf
      have h := mem_Ioc.mp hj
      have e : r+(j-r)=j := by omega
      simpa only [e] using dilate_range hr (j:=j-r) (by omega) (by omega) off lifts free u hu f hf)
    let : NeZero q := ⟨hq.ne'⟩
    let R := P.image (fun x : ℕ => (x : ZMod q))
    rcases universal_cycle hr R (hn.image _) aper (by rwa [←rL]) with bound|⟨r3,q36,ord⟩
    · left
      let T := P.image (·%q)
      have eq : R.image ZMod.val=T := by
        dsimp [R,T]
        rw [image_image]
        exact image_congr (fun x _ => ZMod.val_natCast _ _)
      have dense : T.card=R.card := eq ▸ card_image_of_injective _ (ZMod.val_injective q)
      have dec : a/q*q=a := Nat.div_mul_cancel dvd
      have cap := Erdos13HalfOccupied.count_by_period q (a/q) 0 (Nat.zero_le _) T 0 P (by
        intro x hx
        have := (off x hx).2
        simpa only [Nat.zero_add,Nat.add_zero,dec,mem_Ico,Nat.zero_le,true_and] using this)
        (fun x hx => mem_image_of_mem _ hx)
      simp only [min_eq_left (Nat.zero_le _),Nat.add_zero,dense] at cap
      have a1 := Nat.mul_le_mul_left (densityFactor r*r+1) cap
      have a2 := Nat.mul_le_mul_left (a/q) bound
      have aid := congrArg (fun z : ℕ => densityFactor r*z) dec
      nlinarith only [a1,a2,aid]
    · have dq : 3 ∣ q := by rcases q36 with rfl|rfl <;> decide
      refine Or.inr ⟨r3,dq.trans dvd,?_⟩
      intro u hu dvu
      have quo : q ∣ 2*u := by
        obtain ⟨j,rfl⟩ := dvu
        rcases q36 with e|e <;> rw [e]
        · exact ⟨2*j,by ring⟩
        · exact ⟨j,by ring⟩
      have zero : 2 • (u : ZMod q)=0 := by
        rw [nsmul_eq_mul]
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff _ _).mpr quo
      have div := addOrderOf_dvd_iff_nsmul_eq_zero.mpr zero
      have cap := Nat.le_of_dvd (by decide : 0<2) div
      exact (Nat.not_lt_of_ge cap) (ord _ (mem_image_of_mem _ hu))
  · left
    rw [not_nonempty_iff_eq_empty.mp hn]
    simp

end Erdos13ColumnModulo

end

section

/-  Sparse terminal intervals force a strict saving throughout the extended shell. -/
namespace OMA.Erdos13Universal
open Finset FullColumns OMA.Erdos13ManyLayers Erdos13ColumnModulo

/-- The extension to N/(r+1) has a strict positive gap with sparse top, at every arity. -/
theorem boundary_sparse_stability (r : ℕ) (hr : 3≤r) : ∃ W C : ℕ, 0<W ∧
    ∀ (m : ℕ) (A : Finset ℕ), (∀ a∈A, 0<a ∧ m≤a ∧ a≤(r+1)*m) → Free r A →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m → W*A.card+m ≤ W*m+C := by
  classical
  let F := densityFactor r
  have fpos : 0<F := by dsimp [F,densityFactor]; positivity
  obtain ⟨M,mp,Cₗ,low⟩ := OMA.Erdos13Mixed.critical_tail_gap r F r hr fpos
  obtain ⟨Cₕ,high⟩ := sparse_top_stability r hr
  let Wₕ := 24*r*r*(r+1)+1
  let Wₗ := M*(r+1)
  let W := Wₗ+Wₕ+1
  let E := (W+1)*(Cₗ+Cₕ)
  let Q := E+W
  have wpos : 0<W := by dsimp [W]; omega
  refine ⟨2*W,2*Q*(2*Q*(r+1)+1),by positivity,?_⟩
  intro m A sub free sp
  let N := (r+1)*m
  have pos (a : ℕ) (ha : a∈A) := (sub a ha).1
  have mm : m ≤ W*m := by simpa using Nat.mul_le_mul_right m wpos
  have selected := OMA.Erdos13UpperShell.select_large_scaled (r:=r) (L:=N.sqrt) (t:=W)
    (N:=W*m-m) (K:=E*(N.sqrt+1)) A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos) (by
    intro a ha d hd dvd quot
    let B := A.filter (a<·)
    have inc : B ⊆ A := filter_subset _ _
    have hB : B ⊆ Ioc a N := fun x hx => mem_Ioc.mpr ⟨(mem_filter.mp hx).2,(sub x (inc hx)).2.2⟩
    have freeB : Free r B := fun a ha b hb => free _ (inc ha) b (fun i => inc (hb i))
    have ap := pos a ha
    have top : N≤(r+1)*a := Nat.mul_le_mul_left _ (sub a ha).2.1
    have lim : W*B.card+m ≤ W*m+E*(N.sqrt+1) := by
      by_cases earlier : N ≤ r*a
      · have span (x) (hx : x∈B) : 0<x ∧ N≤r*x ∧ x≤N := ⟨pos _ (inc hx),
          earlier.trans (Nat.mul_le_mul_left _ (mem_Ioc.mp (hB hx)).1.le),(mem_Ioc.mp (hB hx)).2⟩
        have h := high m B span freeB
          ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) inc))).trans sp)
        have sharp : Wₕ*B.card+m ≤ Wₕ*m+Cₕ := by dsimp [Wₕ]; nlinarith only [h]
        have lifted := lift_weight (W:=W) (by dsimp [Wₕ]; omega) (by dsimp [W]; omega) sharp
        have c : Cₕ ≤ (Cₗ+Cₕ)*(N.sqrt+1) := by nlinarith [Nat.zero_le (Cₕ*N.sqrt),Nat.zero_le (Cₗ*N.sqrt)]
        have extra := Nat.mul_le_mul_left (W+1) c
        dsimp [E]
        nlinarith only [lifted,extra]
      · have dpos : 0<d := by omega
        have ball := OMA.Erdos13Cyclic.residue_bound_of_quotient B ap dpos dvd quot
        have ab : a/d ≤ N.sqrt := by
          apply Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul dpos).mpr ?_)
          exact lt_of_le_of_lt (sub a ha).2.2 (lt_of_lt_of_le (Nat.lt_succ_sqrt N) (Nat.mul_le_mul_left _ hd))
        have resid : r*(B.image (·%a)).card ≤ a+r*(N.sqrt+1) := by
          have b := Nat.mul_le_mul_right r ab
          nlinarith only [ball,b,Nat.zero_le r]
        have layers (x) (hx : x∈B) : x/a∈Icc 1 r := by
          have z := mem_Ioc.mp (hB hx)
          refine mem_Icc.mpr ⟨Nat.div_pos z.1.le ap, Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ap).mpr ?_)⟩
          by_contra! ge
          change (r+1)*a ≤ x at ge
          have eq : x=(r+1)*a := by omega
          have dxa : a ∣ x := eq ▸ dvd_mul_left _ _
          apply free a ha (fun _ => x) (fun _ => inc hx) (fun _ => z.1)
          simpa using dxa.trans (dvd_mul_left x r)
        let P := complete B a r
        have lifts (u) (hu : u∈P) (i) (hi : i∈Icc 1 r) : i*a+u∈B := (mem_filter.mp hu).2 i hi
        have off (u) (hu : u∈P) : 0<u ∧ u<a := by
          obtain ⟨x,hx,eq⟩ := mem_image.mp (mem_filter.mp hu).1
          have fst := (mem_Ioc.mp (hB (lifts u hu 1 (mem_Icc.mpr ⟨le_rfl,by omega⟩)))).1
          rw [one_mul] at fst
          exact ⟨by omega, eq ▸ Nat.mod_lt x ap⟩
        have dich := complete_universal hr ap P off (fun u hu i hi => inc (lifts u hu i hi)) free
        have h := low m a A B ap (by omega) top hB layers inc free resid dich
        have hh : Wₗ*B.card+m≤Wₗ*m+Cₗ*(N.sqrt+1) := by simpa only [Wₗ,N,Nat.mul_assoc] using h
        have wp : 0<Wₗ := by dsimp [Wₗ]; positivity
        have lifted := lift_weight (W:=W) wp (by dsimp [W]; omega) hh
        have cc := Nat.mul_le_mul_right (N.sqrt+1) (show Cₗ≤Cₗ+Cₕ by omega)
        have extra := Nat.mul_le_mul_left (W+1) cc
        dsimp [E]
        nlinarith only [lifted,extra]
    change W*B.card ≤ W*m-m+E*(N.sqrt+1)
    omega)
  have approx : W*A.card+m ≤ W*m+Q*(N.sqrt+1) := by
    calc
      W*A.card+m ≤ (W*m-m+E*(N.sqrt+1)+W*(N.sqrt+1))+m := Nat.add_le_add_right selected m
      _ = W*m+Q*(N.sqrt+1) := by
        dsimp only [Q]
        rw [Nat.add_mul E W (N.sqrt+1)]
        omega
  have small := sqrt_absorb r m Q
  change 2*Q*(N.sqrt+1) ≤ _ at small
  nlinarith only [approx,small]

/-- The conjectured bound holds for all sets supported above N/(r+1). -/
theorem full_boundary_shell (r : ℕ) (hr : 3≤r) : ∃ K : ℕ, Shell r (r+1) K := by
  obtain ⟨W,C,wp,h⟩ := boundary_sparse_stability r hr
  exact sharp_shell_of_stability hr wp h

/-- The global bound has coefficient strictly smaller than 1/r, uniformly in N. -/
theorem global_subreciprocal (r : ℕ) (hr : 3≤r) : ∃ M C : ℕ, 0<M ∧ ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 N → Free r A → (M*r+1)*A.card ≤ M*N+C := by
  obtain ⟨W,C,wp,h⟩ := boundary_sparse_stability r hr
  obtain ⟨K,cap⟩ := global_of_sparse hr wp h
  exact ⟨2*W*(r+1),K,by positivity,cap⟩

/-- A sparse-top counterexample must have linearly many elements strictly below N/(r+1). -/
theorem many_below_boundary (r : ℕ) (hr : 3≤r) : ∃ W C : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → Free r A → m+C<A.card →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m → m<W*(A.filter (fun x => x < m)).card := by
  obtain ⟨W,C,wp,h⟩ := boundary_sparse_stability r hr
  exact ⟨W,C,many_below_m_of_stability wp h⟩

end OMA.Erdos13Universal

end

section

/-  Divisor certificates with variable larger summands and fixed offsets. -/
namespace Erdos13Variable

open Finset FullColumns

/-- A certificate at one divisor n. The summands indexed by e have already
been replaced by their fixed offsets from n. -/
def CertAt {t : ℕ} (A : Finset ℕ) (e : Fin t → ℕ) (k s n : ℕ) (b : Fin s → ℕ) : Prop :=
  (∀ i, b i ∈ A ∧ n < b i) ∧ (∑ i,b i)+(∑ i,e i)=k*n

def Certificates {t : ℕ} (A S : Finset ℕ) (e : Fin t → ℕ) (k s : ℕ) : Prop :=
  ∀ n ∈ S, ∃ b : Fin s → ℕ, CertAt A e k s n b

/-- A proportional pair of gaps converts a shorter certificate at y into an
r-term witness at the middle point x. Only the variable entries must exceed x. -/
theorem variable_witness_at {r s t k x y z : ℕ} {A : Finset ℕ}
    (hs : s<r) (room : s+t≤r) (e : Fin t → ℕ) (b : Fin s → ℕ)
    (free : Free r A) (hx : x∈A) (hz : z∈A) (xz : x<z) (yx : y<x)
    (offsets : ∀ i,z+e i∈A) (cert : CertAt A e k s y b)
    (order : ∀ i, x<b i) (prop : (r-s)*(z-x)=k*(x-y)) : False := by
  let l := r-s-t
  have slots : s+(t+l)=r := by dsimp [l]; omega
  have times : t+l=r-s := by dsimp [l]; omega
  let tail := Fin.append (fun i : Fin t => z+e i) (fun _ : Fin l => z)
  let f : Fin (s+(t+l)) → ℕ := Fin.append b tail
  have tailmem (i) : tail i∈A := Fin.addCases (fun j => by simpa [tail] using offsets j)
    (fun _ => by simpa [tail] using hz) i
  have tailord (i) : x<tail i := Fin.addCases (fun j => by
    simpa [tail] using (show x<z+e j by omega)) (fun _ => by simpa [tail] using xz) i
  have mem (i) : f i∈A := Fin.addCases (fun j => by simpa [f] using (cert.1 j).1)
    (fun j => by simpa [f] using tailmem j) i
  have high (i) : x<f i := Fin.addCases (fun j => by simpa [f] using order j)
    (fun j => by simpa [f] using tailord j) i
  have gapY := congrArg (fun n : ℕ => k*n) (Nat.sub_add_cancel yx.le)
  have gapZ := congrArg (fun n : ℕ => (r-s)*n) (Nat.sub_add_cancel xz.le)
  have tz := congrArg (fun n : ℕ => n*z) times
  have num : (∑ i,b i)+(t*z+(∑ i,e i)+l*z)=x*(k+(r-s)) := by
    nlinarith only [cert.2,tz,gapY,gapZ,prop]
  have tally : (∑ i,f i)=x*(k+(r-s)) := by
    simpa [f,tail,Fin.sum_univ_add,Finset.sum_add_distrib] using num
  rw [←slots] at free
  exact free x hx f mem high ⟨k+(r-s),tally⟩

/-- The variable summands can depend on the divisor. -/
theorem variable_witness {r s t k : ℕ} {A S : Finset ℕ}
    (hs : s<r) (room : s+t≤r) (e : Fin t → ℕ) (b : ℕ → Fin s → ℕ)
    (free : Free r A) (inside : S ⊆ A) (offsets : ∀ n ∈ S, ∀ i,n+e i∈A)
    (cert : ∀ n ∈ S, CertAt A e k s n (b n))
    {y x z : ℕ} (hy : y∈S) (hx : x∈S) (hz : z∈S) (yx : y<x) (xz : x<z)
    (prop : (r-s)*(z-x)=k*(x-y)) (order : ∀ i,x<b y i) : False :=
  variable_witness_at hs room e (b y) free (inside hx) (inside hz) xz yx (offsets z hz) (cert y hy) order prop

/-- Removing a variable summand with known offset c keeps the certificate
equation after c is appended to e and k is decreased by one. -/
theorem remove_fixed_offset_at {s t k n c : ℕ} {A : Finset ℕ} {e : Fin t → ℕ}
    {b : Fin (s+1) → ℕ} (hk : 0<k) (cert : CertAt A e k (s+1) n b)
    (i : Fin (s+1)) (fixed : b i=n+c) :
    n+c∈A ∧ CertAt A (Fin.snoc e c) (k-1) s n (fun j => b (i.succAbove j)) := by
  refine ⟨fixed ▸ (cert.1 i).1,fun j => cert.1 _,?_⟩
  have part := Fin.sum_univ_succAbove b i
  have off : (∑ j, Fin.snoc e c j) = (∑ j,e j)+c := by
    simp [Fin.sum_univ_castSucc]
  have coeff := congrArg (fun m : ℕ => m*n) (Nat.sub_add_cancel (show 1≤k by omega))
  rw [off]
  nlinarith only [cert.2,part,fixed,coeff]

/-- The summand and its index may both depend on n in the new class. -/
theorem remove_fixed_offset {s t k c : ℕ} {A S : Finset ℕ} {e : Fin t → ℕ}
    (hk : 0<k) (offsets : ∀ n∈S, ∀ i,n+e i∈A)
    (fixed : ∀ n∈S, ∃ b : Fin (s+1) → ℕ, CertAt A e k (s+1) n b ∧ ∃ i,b i=n+c) :
    (∀ n∈S, ∀ i : Fin (t+1), n + (Fin.snoc e c : Fin (t+1) → ℕ) i ∈ A) ∧ Certificates A S (Fin.snoc e c) (k-1) s := by
  constructor
  · intro n hn j
    obtain ⟨b,hb,i,hi⟩ := fixed n hn
    have last := (remove_fixed_offset_at hk hb i hi).1
    exact Fin.lastCases (by simpa using last) (fun i => by simpa using offsets n hn i) j
  · intro n hn
    obtain ⟨b,hb,i,hi⟩ := fixed n hn
    exact ⟨_,(remove_fixed_offset_at hk hb i hi).2⟩

end Erdos13Variable

end

section

/-  Cardinality bounds for one far class and finitely many close classes. -/

namespace Erdos13WeakArity
open Finset

/-- Averaging cardinality bounds for finitely many classes, including an empty index set. -/
theorem scaled_sum_bound {ι α : Type*} (I : Finset ι) (A : ι → Finset α) {K B : ℕ}
    (bound : ∀ i ∈ I, K * I.card * (A i).card ≤ B) :
    K * (∑ i ∈ I, (A i).card) ≤ B := by
  classical
  by_cases ne : I.Nonempty
  · have summed : (∑ i ∈ I, K * I.card * (A i).card) ≤ ∑ _i ∈ I, B :=
      sum_le_sum bound
    rw [←Finset.mul_sum] at summed
    simp only [sum_const, smul_eq_mul] at summed
    have h : I.card * (K * (∑ i ∈ I, (A i).card)) ≤ I.card * B := by
      simpa only [Nat.mul_left_comm, Nat.mul_assoc] using summed
    exact Nat.le_of_mul_le_mul_left h (card_pos.mpr ne)
  · simp [not_nonempty_iff_eq_empty.mp ne]

/-- The close classes can overlap each other and the far class. -/
theorem far_close_count {α : Type*} (S far : Finset α) (close : ℕ → Finset α)
    {K L N C Cfar : ℕ}
    (cover : ∀ x ∈ S, x ∈ far ∨ ∃ i ≤ L, x ∈ close i)
    (farBound : 2*K * far.card ≤ N + Cfar)
    (closeBound : ∀ i ≤ L, 2*K*(L+1) * (close i).card ≤ N + C) :
    K * S.card ≤ N + C + Cfar := by
  classical
  let I := range (L+1)
  have sub : S ⊆ far ∪ I.biUnion close := by
    intro x hx
    rcases cover x hx with hf | ⟨i,hi,hc⟩
    · exact mem_union_left _ hf
    · exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr (by omega),hc⟩)
  have total : S.card ≤ far.card + ∑ i ∈ I, (close i).card :=
    (card_le_card sub).trans (card_union_le .. |>.trans
      (Nat.add_le_add_left (card_biUnion_le ..) _))
  have closeSum : 2*K * (∑ i ∈ I, (close i).card) ≤ N+C :=
    scaled_sum_bound I close (fun i hi => by
      simpa only [I,card_range] using closeBound i (Nat.le_of_lt_succ (mem_range.mp hi)))
  have scaled := Nat.mul_le_mul_left (2*K) total
  rw [Nat.mul_add] at scaled
  have both : 2*(K*S.card) ≤ 2*N + C + Cfar := by
    rw [←Nat.mul_assoc]
    omega
  omega

/-- A finite union with one bound for each index. -/
theorem finite_union_bound {ι α : Type*} (I : Finset ι) (S : Finset α)
    (A : ι → Finset α) {K B : ℕ}
    (cover : ∀ x ∈ S, ∃ i ∈ I, x ∈ A i)
    (bound : ∀ i ∈ I, K * I.card * (A i).card ≤ B) :
    K * S.card ≤ B := by
  classical
  have sub : S ⊆ I.biUnion A := fun x hx => mem_biUnion.mpr (cover x hx)
  exact (Nat.mul_le_mul_left K ((card_le_card sub).trans (card_biUnion_le ..))).trans
    (scaled_sum_bound I A bound)

/-- Multipliers may have different additive error constants. -/
theorem union_over_multipliers (I : Finset ℕ) (S : Finset ℕ) (A : ℕ → Finset ℕ)
    (C : ℕ → ℕ) {K N : ℕ} (cover : ∀ x ∈ S, ∃ k ∈ I, x ∈ A k)
    (bound : ∀ k ∈ I, K * I.card * (A k).card ≤ N + C k) :
    K * S.card ≤ N + ∑ k ∈ I, C k := by
  classical
  apply finite_union_bound I S A cover
  intro k hk
  exact (bound k hk).trans (Nat.add_le_add_left
    (single_le_sum (fun k _ => Nat.zero_le (C k)) hk) _)

end Erdos13WeakArity

end

section

/-  Fixed-multiplier sparsity implies that all shorter forbidden sums can
be removed at a cost with arbitrarily small linear coefficient. -/
namespace Erdos13Shorter
open Finset FullColumns Erdos13Variable Erdos13WeakArity
open scoped Classical

def HasWitness (A : Finset ℕ) (s n : ℕ) : Prop :=
  ∃ b : Fin s → ℕ, (∀ i,b i∈A) ∧ (∀ i,n<b i) ∧ n ∣ ∑ i,b i

def Multiplier (A : Finset ℕ) (s k n : ℕ) : Prop :=
  ∃ b : Fin s → ℕ, (∀ i,b i∈A ∧ n<b i) ∧ (∑ i,b i)=k*n

def FixedSparse (r : ℕ) : Prop :=
  ∀ s<r, ∀ k, s<k → ∀ D, 0<D → ∃ C : ℕ, ∀ (N : ℕ) (A F : Finset ℕ),
  F ⊆ range N → F ⊆ A → Free r A → (∀ n∈F, Multiplier A s k n) → D*F.card≤N+C

/-- Bound all pivots of one shorter arity, including arbitrarily large multipliers. -/
theorem shorter_sparse {r : ℕ} (fixed : FixedSparse r) {s : ℕ} (spos : 0<s) (hs : s<r)
    (K : ℕ) (kpos : 0<K) : ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 N → Free r A → K*(A.filter (fun n => HasWitness A s n)).card ≤ N+C := by
  classical
  let H := 2*K
  have hp : 0<H := by dsimp [H]; omega
  let I := Ioc s (s*H)
  let D := H*I.card
  have Ine : I.Nonempty := ⟨s*H,mem_Ioc.mpr ⟨by
    have z := Nat.mul_lt_mul_of_pos_left (show 1<H by dsimp [H]; omega) spos
    simpa using z,le_rfl⟩⟩
  have dpos : 0<D := Nat.mul_pos hp (card_pos.mpr Ine)
  let valid (k C : ℕ) : Prop := ∀ (hk : k∈I) (N : ℕ) (A F : Finset ℕ),
      F⊆range N → F⊆A → Free r A → (∀ n∈F, Multiplier A s k n) → D*F.card≤N+C
  have many (k : ℕ) : ∃ C : ℕ, valid k C := by
    by_cases hk : k∈I
    · obtain ⟨C,hC⟩ := fixed s hs k (mem_Ioc.mp hk).1 D dpos
      exact ⟨C,fun _ => hC⟩
    · exact ⟨0,fun h => (hk h).elim⟩
  choose C bound using many
  refine ⟨H+1+∑ k∈I,C k,?_⟩
  intro N A sub free
  let S := A.filter (fun n => HasWitness A s n)
  let small := S.filter (fun n => H*n<N)
  let big := S.filter (fun n => ¬H*n<N)
  have split : small.card+big.card=S.card := card_filter_add_card_filter_not ..
  have little : H*small.card ≤ N+H := by
    have smallsub : small ⊆ range (N/H+1) := by
      intro n hn
      have b := (mem_filter.mp hn).2
      exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hp).mpr (by rw [mul_comm]; omega)))
    have cnt := Nat.mul_le_mul_left H (card_le_card smallsub)
    rw [card_range,Nat.mul_add,Nat.mul_one,mul_comm H (N/H)] at cnt
    have := Nat.div_mul_le_self N H
    omega
  let F := fun k => big.filter (fun n => Multiplier A s k n)
  have inside : big⊆A := (filter_subset _ _).trans (filter_subset _ _)
  have cover (n) (hn : n∈big) : ∃ k∈I,n∈F k := by
    have memS := (mem_filter.mp hn).1
    obtain ⟨b,hb,high,k,eq⟩ := (mem_filter.mp memS).2
    have npos := (mem_Icc.mp (sub (inside hn))).1
    have low : s*n < ∑ i,b i := by
      have := sum_lt_sum_of_nonempty (s:= (univ : Finset (Fin s)))
        ⟨⟨0,spos⟩,mem_univ _⟩ (fun i _ => high i)
      simpa using this
    have up : (∑ i,b i) ≤ s*N := by
      have := sum_le_sum (s:=(univ : Finset (Fin s))) (fun i _ => (mem_Icc.mp (sub (hb i))).2)
      simpa using this
    have mulbig : s*N ≤ s*(H*n) := Nat.mul_le_mul_left s (by have := (mem_filter.mp hn).2; omega)
    rw [mul_comm n k] at eq
    have kgt : s<k := Nat.lt_of_mul_lt_mul_right (eq ▸ low)
    have kle : k ≤ s*H := by
      apply Nat.le_of_mul_le_mul_right _ npos
      rw [←eq,Nat.mul_assoc]
      exact up.trans mulbig
    exact ⟨k,mem_Ioc.mpr ⟨kgt,kle⟩,mem_filter.mpr ⟨hn,b,fun i => ⟨hb i,high i⟩,eq⟩⟩
  have bigbound : H*big.card ≤ (N+1)+∑ k∈I,C k := by
    apply union_over_multipliers I big F C cover
    intro k hk
    have subA : F k ⊆ A := (filter_subset _ _).trans inside
    exact bound k hk (N+1) A (F k) (fun n hn => mem_range.mpr
      (Nat.lt_succ_of_le (mem_Icc.mp (sub (subA hn))).2)) subA free (fun n hn => (mem_filter.mp hn).2)
  change K*S.card ≤ _
  have scale := congrArg (fun n : ℕ => H*n) split
  rw [Nat.mul_add] at scale
  dsimp only [H] at little bigbound scale
  dsimp only [H]
  simp only [Nat.mul_assoc] at little bigbound scale
  omega

/-- All positive shorter arities hold on a common subset after a uniformly
sublinear deletion. -/
theorem simultaneous_removal_of_fixed {r : ℕ} (fixed : FixedSparse r)
    (K : ℕ) (kp : 0<K) : ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 N → Free r A → ∃ B ⊆ A, K*(A \ B).card ≤ N+C ∧
      ∀ s : ℕ, 0<s → s≤r → Free s B := by
  classical
  let I := Ico 1 r
  let D := K*(I.card+1)
  have dp : 0<D := Nat.mul_pos kp (by omega)
  let valid (s C : ℕ) : Prop := ∀ (hs : s∈I) (N : ℕ) (A : Finset ℕ),
      A ⊆ Icc 1 N → Free r A → D*(A.filter (fun n => HasWitness A s n)).card ≤ N+C
  have per (s : ℕ) : ∃ C : ℕ, valid s C := by
    by_cases h : s∈I
    · obtain ⟨C,hit⟩ := shorter_sparse fixed (mem_Ico.mp h).1 (mem_Ico.mp h).2 D dp
      exact ⟨C,fun _ => hit⟩
    · exact ⟨0,fun h' => (h h').elim⟩
  choose C bound using per
  refine ⟨∑ s∈I,C s,?_⟩
  intro N A sub free
  let B := A.filter (fun n => ∀ s∈I, ¬HasWitness A s n)
  have inc : B ⊆ A := filter_subset _ _
  refine ⟨B,inc,?_,?_⟩
  · let F := fun s => A.filter (fun n => HasWitness A s n)
    apply union_over_multipliers I (A \ B) F C
    · intro n hn
      obtain ⟨a,nb⟩ := mem_sdiff.mp hn
      have failure : ¬∀ s∈I, ¬HasWitness A s n := fun h => nb (mem_filter.mpr ⟨a,h⟩)
      push Not at failure
      obtain ⟨s,hs,mem⟩ := failure
      exact ⟨s,hs,mem_filter.mpr ⟨a,mem⟩⟩
    · intro s hs
      have kk : K*I.card ≤ D := Nat.mul_le_mul_left K (by omega)
      exact (Nat.mul_le_mul_right _ kk).trans (bound s hs N A sub free)
  · intro s sp sr a ha b hb hlt div
    by_cases eq : s=r
    · subst s
      exact free a (inc ha) b (fun i => inc (hb i)) hlt div
    · exact (mem_filter.mp ha).2 s (mem_Ico.mpr ⟨sp,by omega⟩)
        ⟨b,fun i => inc (hb i),hlt,div⟩

end Erdos13Shorter

end

section

/-  Positively oriented three-point configurations from the corners theorem. -/
namespace Erdos13Mirrored
open Finset

lemma carries_shape {u v M h i j d : ℕ}
    (small : i+d < M) (_small' : j+d < M)
    {c lo hi : ℕ}
    (center : h = c+u*(M-i)+v*j)
    (east : h = hi+u*(M-(i+d))+v*j)
    (north : h = lo+u*(M-i)+v*(j+d)) :
    lo+v*d=c ∧ c+u*d=hi := by
  have cut : M-(i+d)+d=M-i := by omega
  have sc := congrArg (u*·) cut
  rw [Nat.mul_add] at sc north
  omega

lemma carries_shape_rev {u v M k i j d : ℕ}
    (_small : i+d < M) (small' : j+d < M)
    {c lo hi : ℕ}
    (center : k = c+u*(i+d)+v*(M-(j+d)))
    (west : k = hi+u*i+v*(M-(j+d)))
    (south : k = lo+u*(i+d)+v*(M-j)) :
    lo+v*d=c ∧ c+u*d=hi := by
  have cut : M-(j+d)+d=M-j := by omega
  have sc := congrArg (v*·) cut
  rw [Nat.mul_add] at sc center south
  omega

theorem pattern_of_corner {S : Finset ℕ} {T : Finset (ℕ × ℕ)} {u v M h k : ℕ}
    (box : T ⊆ range M ×ˢ range M)
    (maps : ∀ ij∈T, (∃ x∈S, h=x+u*(M-ij.1)+v*ij.2) ∧
                     (∃ y∈S, k=y+u*ij.1+v*(M-ij.2)))
    (existsCorner : ¬ IsCornerFree (T : Set (ℕ × ℕ))) :
    ∃ y∈S, ∃ x∈S, ∃ z∈S, ∃ d, 0<d ∧ d<M ∧ y+v*d=x ∧ x+u*d=z := by
  classical
  unfold IsCornerFree at existsCorner
  push Not at existsCorner
  obtain ⟨i,j,i',j',cor,ne⟩ := existsCorner
  obtain ⟨aa,ab,ba,spacing⟩ := cor
  have limits (p : ℕ × ℕ) (hp : p∈T) : p.1<M ∧ p.2<M := by
    simpa only [mem_product,mem_range] using box hp
  have l1 := limits _ aa
  have l2 := limits _ ab
  have l3 := limits _ ba
  change i<M ∧ j<M at l1
  change i<M ∧ j'<M at l2
  change i'<M ∧ j<M at l3
  rcases lt_or_gt_of_ne ne with forward | back
  · let d := i'-i
    have ii : i'=i+d := by dsimp [d]; omega
    have jj : j'=j+d := by dsimp [d]; omega
    obtain ⟨c,hc,C⟩ := (maps _ aa).1
    obtain ⟨hi,hhi,H⟩ := (maps _ ba).1
    obtain ⟨lo,hlo,L⟩ := (maps _ ab).1
    refine ⟨lo,hlo,c,hc,hi,hhi,d,by dsimp [d]; omega,by dsimp [d]; omega,?_⟩
    exact carries_shape (u:=u) (v:=v) (h:=h) (by omega : i+d<M) (by omega : j+d<M)
      C (by simpa only [←ii] using H) (by simpa only [←jj] using L)
  · let d := i-i'
    have ii : i=i'+d := by dsimp [d]; omega
    have jj : j=j'+d := by dsimp [d]; omega
    obtain ⟨c,hc,C⟩ := (maps _ aa).2
    obtain ⟨hi,hhi,H⟩ := (maps _ ba).2
    obtain ⟨lo,hlo,L⟩ := (maps _ ab).2
    refine ⟨lo,hlo,c,hc,hi,hhi,d,by dsimp [d]; omega,by dsimp [d]; omega,?_⟩
    exact carries_shape_rev (u:=u) (v:=v) (k:=k) (by omega : i'+d<M) (by omega : j'+d<M)
      (by simpa only [←ii,←jj] using C) (by simpa only [←jj] using H)
      (by simpa only [←ii] using L)

end Erdos13Mirrored

end

section

/-  Extract a bounded-gap, positively oriented weighted triple from a
large mirrored fiber. The grid size depends only on the density. -/
namespace Erdos13Mirrored
open Finset

noncomputable def gridSize (K : ℕ) : ℕ :=
  cornersTheoremBound (((1:ℝ)/((K:ℝ)^2))/9)+1

theorem shape_from_large_fiber {S : Finset ℕ} {T : Finset (ℕ × ℕ)}
    {u v M h k K W : ℕ} (Kpos : 0<K) (Wpos : 0<W)
    (grid : gridSize K ≤ M) (wide : W ≤ K*S.card)
    (big : S.card^2*M^2 ≤ W^2*T.card)
    (box : T ⊆ range M ×ˢ range M)
    (maps : ∀ ij∈T, (∃ x∈S, h=x+u*(M-ij.1)+v*ij.2) ∧
                     (∃ y∈S, k=y+u*ij.1+v*(M-ij.2))) :
    ∃ y∈S, ∃ x∈S, ∃ z∈S, ∃ d, 0<d ∧ d<M ∧ y+v*d=x ∧ x+u*d=z := by
  have power := Nat.pow_le_pow_left wide 2
  have lower : W^2*M^2 ≤ W^2*(K^2*T.card) := calc
    _ ≤ (K*S.card)^2*M^2 := Nat.mul_le_mul_right _ power
    _ = K^2*(S.card^2*M^2) := by ring
    _ ≤ K^2*(W^2*T.card) := Nat.mul_le_mul_left _ big
    _ = _ := by ring
  have card : M^2 ≤ K^2*T.card := Nat.le_of_mul_le_mul_left lower (by positivity)
  have dens : ((1:ℝ)/(K:ℝ)^2)*M^2 ≤ T.card := by
    rw [div_mul_eq_mul_div,one_mul,div_le_iff₀ (by positivity)]
    exact_mod_cast (by simpa only [mul_comm] using card : M^2 ≤ T.card*K^2)
  exact pattern_of_corner box maps
    (corners_theorem_nat (by positivity : 0<(1:ℝ)/(K:ℝ)^2)
      (show cornersTheoremBound (((1:ℝ)/(K:ℝ)^2)/9) ≤ M from (Nat.le_succ _).trans grid) T box dens)
end Erdos13Mirrored

end

section

/-  Double counting of the coordinate pairs in mirrored fibers. -/

namespace Erdos13Mirrored

open Finset

noncomputable def fiber (S : Finset ℕ) (u v M h k : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (range M ×ˢ range M).filter fun p =>
    ∃ x ∈ S, ∃ y ∈ S,
      h = x + u * (M-p.1) + v * p.2 ∧ k = y + u * p.1 + v * (M-p.2)

theorem card_le_sum_fibers {S : Finset ℕ} {N : ℕ} (sub : S ⊆ range N) (u v M : ℕ) :
    S.card^2 * M^2 ≤
      ∑ h ∈ range (N+(u+v)*M+1), ∑ k ∈ range (N+(u+v)*M+1), (fiber S u v M h k).card := by
  classical
  let L := N+(u+v)*M+1
  let keys := range L ×ˢ range L
  let dom := (S ×ˢ S) ×ˢ (range M ×ˢ range M)
  let tgt := keys.sigma fun t => fiber S u v M t.1 t.2
  let f : (ℕ × ℕ) × (ℕ × ℕ) → (Σ _ : ℕ × ℕ, ℕ × ℕ) :=
    fun p => ⟨(p.1.1 + u*(M-p.2.1) + v*p.2.2, p.1.2 + u*p.2.1 + v*(M-p.2.2)),p.2⟩
  have bound (x s t : ℕ) (hx : x ∈ S) (hs : s ≤ M) (ht : t ≤ M) :
      x + u*s + v*t < L := by
    have h₁ := Nat.mul_le_mul_left u hs
    have h₂ := Nat.mul_le_mul_left v ht
    have h₃ := mem_range.mp (sub hx)
    dsimp [L]
    rw [Nat.add_mul]
    omega
  have maps p (hp : p ∈ dom) : f p ∈ tgt := by
    obtain ⟨⟨x,y⟩,i,j⟩ := p
    obtain ⟨hxy,hij⟩ := mem_product.mp hp
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    obtain ⟨hi,hj⟩ := mem_product.mp hij
    apply mem_sigma.mpr
    refine ⟨mem_product.mpr ⟨mem_range.mpr ?_, mem_range.mpr ?_⟩, ?_⟩
    · exact bound x _ _ hx (Nat.sub_le ..) (mem_range.mp hj).le
    · exact bound y _ _ hy (mem_range.mp hi).le (Nat.sub_le ..)
    · exact mem_filter.mpr ⟨mem_product.mpr ⟨hi,hj⟩, x,hx,y,hy,rfl,rfl⟩
  have inj : Function.Injective f := by
    rintro ⟨⟨x,y⟩,i,j⟩ ⟨⟨x',y'⟩,i',j'⟩ he
    have hi := congrArg (fun z : Σ _ : ℕ × ℕ, ℕ × ℕ => z.2.1) he
    have hj := congrArg (fun z : Σ _ : ℕ × ℕ, ℕ × ℕ => z.2.2) he
    change i=i' at hi
    change j=j' at hj
    subst i'
    subst j'
    have hx := congrArg (fun z : Σ _ : ℕ × ℕ, ℕ × ℕ => z.1.1) he
    have hy := congrArg (fun z : Σ _ : ℕ × ℕ, ℕ × ℕ => z.1.2) he
    change x+u*(M-i)+v*j = x'+u*(M-i)+v*j at hx
    change y+u*i+v*(M-j) = y'+u*i+v*(M-j) at hy
    have ex : x=x' := by omega
    have ey : y=y' := by omega
    rw [ex,ey]
  have cnt := card_le_card_of_injOn f maps (fun _ _ _ _ h => inj h)
  simpa only [dom,tgt,keys,L,card_product,card_range,card_sigma,sum_product,pow_two] using cnt

theorem exists_large_fiber {S : Finset ℕ} {N : ℕ} (sub : S ⊆ range N) (u v M : ℕ) :
    ∃ h ∈ range (N+(u+v)*M+1), ∃ k ∈ range (N+(u+v)*M+1),
      S.card^2 * M^2 ≤ (N+(u+v)*M+1)^2 * (fiber S u v M h k).card := by
  classical
  let L := N+(u+v)*M+1
  let K := range L ×ˢ range L
  let weight (t : ℕ × ℕ) := (fiber S u v M t.1 t.2).card
  have pos : 0 < L := Nat.succ_pos _
  have ne : K.Nonempty := ⟨(0,0),mem_product.mpr ⟨mem_range.mpr pos,mem_range.mpr pos⟩⟩
  obtain ⟨t,ht,hm⟩ := K.exists_max_image weight ne
  obtain ⟨hh,hk⟩ := mem_product.mp ht
  refine ⟨t.1,hh,t.2,hk,?_⟩
  have total : S.card^2*M^2 ≤ ∑ z ∈ K,weight z := by
    simpa [K,L,weight,sum_product] using card_le_sum_fibers sub u v M
  have maxbound := sum_le_sum (fun z hz => hm z hz)
  exact total.trans (maxbound.trans_eq (by simp [K,L,weight,pow_two]))

theorem exists_dense_fiber {S : Finset ℕ} {N : ℕ} (sub : S ⊆ range N) (u v M : ℕ) :
    ∃ h k : ℕ, S.card^2 * M^2 ≤ (N+(u+v)*M+1)^2 * (fiber S u v M h k).card := by
  obtain ⟨h,_,k,_,hk⟩ := exists_large_fiber sub u v M
  exact ⟨h,k,hk⟩

end Erdos13Mirrored

end

section

namespace Erdos13Mirrored
open Finset

/-- A dense set of integers contains a positively oriented three-point pattern
with gaps in the prescribed ratio and with bounded step. -/
theorem dense_positive_shape {S : Finset ℕ} {N u v K : ℕ}
    (sub : S ⊆ range N) (Kpos : 0<K)
    (large : N+(u+v)*gridSize K+1 ≤ K*S.card) :
    ∃ y∈S, ∃ x∈S, ∃ z∈S, ∃ d, 0<d ∧ d<gridSize K ∧ y+v*d=x ∧ x+u*d=z := by
  classical
  let M := gridSize K
  obtain ⟨h,k,cap⟩ := exists_dense_fiber sub u v M
  let T := fiber S u v M h k
  have bounds : T ⊆ range M ×ˢ range M := filter_subset _ _
  have maps (ij : ℕ × ℕ) (hij : ij∈T) :
      (∃ x∈S, h=x+u*(M-ij.1)+v*ij.2) ∧ (∃ y∈S, k=y+u*ij.1+v*(M-ij.2)) := by
    obtain ⟨x,hx,y,hy,h1,h2⟩ := (mem_filter.mp hij).2
    exact ⟨⟨x,hx,h1⟩,y,hy,h2⟩
  exact shape_from_large_fiber Kpos (by omega : 0<N+(u+v)*M+1) (by rfl : gridSize K ≤ M)
      large cap bounds maps
end Erdos13Mirrored

end

section

/-  A sparse upper bound for variable certificates whose entries stay
uniformly above their base points. -/
namespace Erdos13Variable
open Finset FullColumns Erdos13Mirrored

theorem far_certificates {r s t k K N : ℕ}
    (hs : s<r) (room : s+t≤r) (hk : 0<k) (hK : 0<K) (e : Fin t → ℕ)
    {A S : Finset ℕ} (sub : S ⊆ range N) (inside : S ⊆ A) (free : Free r A)
    (offsets : ∀ n∈S, ∀ i,n+e i∈A)
    (cert : ∀ n ∈ S, ∃ b : Fin s → ℕ, CertAt A e k s n b ∧
      ∀ i,n+(r-s)*gridSize K<b i) :
    K*S.card ≤ N+(k+(r-s))*gridSize K := by
  by_contra! large
  obtain ⟨y,hy,x,hx,z,hz,d,dp,ds,yx,xz⟩ := dense_positive_shape (u:=k) (v:=r-s)
    sub hK (by omega)
  have vg : 0<(r-s)*d := Nat.mul_pos (by omega) dp
  have ug := Nat.mul_pos hk dp
  have first : x-y=(r-s)*d := by omega
  have second : z-x=k*d := by omega
  obtain ⟨b,hb,far⟩ := cert y hy
  apply variable_witness_at hs room e b free (inside hx) (inside hz) (by omega) (by omega)
    (offsets z hz) hb
  · intro i
    have lim := Nat.mul_le_mul_left (r-s) ds.le
    have f := far i
    omega
  · rw [first,second]
    ring

end Erdos13Variable

end

section

/-  A positive density of shorter certificates forces a full forbidden sum. -/
namespace Erdos13WeakArity
open Finset FullColumns Erdos13Variable Erdos13Mirrored

/-- The additive constant can be chosen uniformly in the values and number
of the fixed offsets. -/
lemma weak_arity_density_uniform (r s k K : ℕ) (hs : s<r) (hk : s<k) (KP : 0<K) :
    ∃ C : ℕ, ∀ (t : ℕ), s+t≤r → ∀ (e : Fin t → ℕ) (N : ℕ) (A S : Finset ℕ),
      S ⊆ range N → S ⊆ A → Free r A → (∀ n∈S, ∀ i, n+e i∈A) →
      Certificates A S e k s → K*S.card ≤ N+C := by
  classical
  induction s generalizing k K with
  | zero =>
    refine ⟨K,?_⟩
    intro t room e N A S sub inc free off cert
    have card : S.card≤1 := by
      apply card_le_one.mpr
      intro n hn m hm
      obtain ⟨b,eq₁⟩ := cert n hn
      obtain ⟨c,eq₂⟩ := cert m hm
      have e₁ : (∑ i,e i)=k*n := by simpa using eq₁.2
      have e₂ : (∑ i,e i)=k*m := by simpa using eq₂.2
      exact Nat.eq_of_mul_eq_mul_left hk (e₁.symm.trans e₂)
    have h := Nat.mul_le_mul_left K card
    omega
  | succ s ih =>
    let v := r-(s+1)
    let G := gridSize (2*K)
    let L := v*G
    let Cfar := (k+v)*G
    have vp : 0<v := by dsimp [v]; omega
    have kp : 0<k := by omega
    have Kbig : 0<2*K*(L+1) := by positivity
    obtain ⟨C,lower⟩ := ih (k:=k-1) (K:=2*K*(L+1)) (by omega) (by omega) Kbig
    refine ⟨C+Cfar,?_⟩
    intro t room e N A S sub inc free off cert
    choose! b hb using cert
    let far := S.filter (fun n => ∀ i, n+L < b n i)
    let close (c : ℕ) := S.filter (fun n => ∃ i, b n i=n+c)
    rw [←Nat.add_assoc]
    apply far_close_count S far close (L:=L)
    · intro n hn
      by_cases h : ∀ i, n+L < b n i
      · exact Or.inl (mem_filter.mpr ⟨hn,h⟩)
      · push Not at h
        obtain ⟨i,small⟩ := h
        have large := ((hb n hn).1 i).2
        exact Or.inr ⟨b n i-n,by omega,mem_filter.mpr ⟨hn,i,by omega⟩⟩
    · have fin : far ⊆ S := filter_subset _ _
      exact far_certificates hs room kp (by omega : 0<2*K) e (fin.trans sub) (fin.trans inc)
        free (fun n hn => off n (fin hn)) (fun n hn => ⟨b n,hb n (fin hn),(mem_filter.mp hn).2⟩)
    · intro c hc
      have cin : close c ⊆ S := filter_subset _ _
      obtain ⟨offs,certs⟩ := remove_fixed_offset (k:=k) (s:=s) (c:=c) kp
        (fun n (hn : n ∈ close c) => off n (cin hn)) (fun n hn =>
          ⟨b n,hb n (cin hn),(mem_filter.mp hn).2⟩)
      exact lower (t+1) (by omega) (Fin.snoc e c) N A (close c) (cin.trans sub) (cin.trans inc)
        free offs certs

/-- For a fixed bound on the multiplier, shorter certificates have zero
upper density among divisors of an r-free set. -/
theorem weak_arity_density {r s t k : ℕ} (hs : s<r) (room : s+t≤r) (hk : s<k)
    (e : Fin t→ℕ) (_ep : ∀ i, 0<e i) (K : ℕ) (KP : 0<K) :
    ∃ C : ℕ, ∀ N (A S : Finset ℕ), S⊆range N → S⊆A → FullColumns.Free r A →
      (∀ n∈S, ∀i,n+e i∈A) → Erdos13Variable.Certificates A S e k s → K*S.card≤N+C := by
  obtain ⟨C,h⟩ := weak_arity_density_uniform r s k K hs hk KP
  exact ⟨C,h t room e⟩

end Erdos13WeakArity

end

section

/-  Simultaneous removal of every shorter arity. -/
namespace Erdos13Shorter
open Finset FullColumns Erdos13Variable Erdos13WeakArity

theorem fixed_multiplier_sparse (r : ℕ) : FixedSparse r := by
  intro s hs k hk D dp
  let e : Fin 0 → ℕ := Fin.elim0
  obtain ⟨C,cap⟩ := weak_arity_density hs (t:=0) (by omega) hk e
    (fun i => i.elim0) D dp
  refine ⟨C,?_⟩
  intro N A F sub inc free props
  apply cap N A F sub inc free (fun _ _ i => i.elim0)
  intro n hn
  obtain ⟨b,mem,eq⟩ := props n hn
  exact ⟨b,mem,by simpa using eq⟩

/-- A set free of r-term divisible sums can be made free at every
positive arity up to r after deleting a uniformly sublinear number of elements. -/
theorem simultaneous_removal (r K : ℕ) (kp : 0<K) :
    ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → Free r A →
      ∃ B ⊆ A, K*(A \ B).card ≤ N+C ∧ ∀ s : ℕ, 0<s → s≤r → Free s B :=
  simultaneous_removal_of_fixed (fixed_multiplier_sparse r) K kp

end Erdos13Shorter

end

section

/-  A strict sparse-top estimate in the simultaneous-arity model would imply
the required bounded additive error for the original sparse-top problem. -/
namespace Erdos13Shorter
open Finset FullColumns

/-- Simultaneous shorter freeness and sharp tail support at every retained pivot. -/
theorem simultaneous_residues {r : ℕ} (rp : 0<r) (K : ℕ) (kp : 0<K) :
    ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → Free r A →
      ∃ B ⊆ A, K*(A \ B).card ≤ N+C ∧
        (∀ s : ℕ, 0<s → s≤r → Free s B) ∧
        ∀ a∈B, r*((B.filter (a<·)).image (·%a)).card+1≤a := by
  obtain ⟨C,pr⟩ := simultaneous_removal r K kp
  refine ⟨C,?_⟩
  intro N A sub free
  obtain ⟨B,inc,cost,all⟩ := pr N A sub free
  exact ⟨B,inc,cost,all,fun a ha => OMA.Erdos13StrongResidues.tail_bound rp
    (mem_Icc.mp (sub (inc ha))).1 ha all⟩

/-- Any hereditary class with a strict saving over m in the simultaneous model
has a bounded additive error over m under the original arity-r condition. -/
theorem transfer_sparse_gap (r W E : ℕ) (wp : 0<W) (P : ℕ → Finset ℕ → Prop)
    (hereditary : ∀ {m : ℕ} {A B : Finset ℕ}, P m A → B⊆A → P m B)
    (gap : ∀ (m : ℕ) (B : Finset ℕ), B ⊆ Icc 1 ((r+1)*m) → P m B →
      (∀ j : ℕ, 0<j → j≤r → Free j B) → W*B.card+m ≤ W*m+E) :
    ∃ C : ℕ, ∀ (m : ℕ) (A : Finset ℕ), A ⊆ Icc 1 ((r+1)*m) → P m A →
      Free r A → A.card ≤ m+C := by
  let K := (r+1)*W
  have kp : 0<K := Nat.mul_pos (by omega) wp
  obtain ⟨C,pr⟩ := simultaneous_removal r K kp
  refine ⟨E+C,?_⟩
  intro m A sub p free
  obtain ⟨B,inc,cost,strong⟩ := pr ((r+1)*m) A sub free
  have bound := gap m B (inc.trans sub) (hereditary p inc) strong
  have scale := Nat.mul_le_mul_left (r+1) bound
  have count := card_sdiff_of_subset inc
  have split : (A \ B).card + B.card = A.card := by
    rw [count,Nat.sub_add_cancel (card_le_card inc)]
  have total := Nat.mul_le_mul_left (r+1) (show E ≤ E+C by omega)
  have sumcost : K*A.card ≤ K*m+((r+1)*E+C) := by
    calc
      K*A.card = K*(A \ B).card+K*B.card := by rw [←Nat.mul_add,split]
      _ ≤ (r+1)*m+C+K*B.card := Nat.add_le_add_right cost _
      _ ≤ K*m+((r+1)*E+C) := by
        dsimp only [K]
        simp only [Nat.mul_add,←Nat.mul_assoc] at scale
        omega
  have err : (r+1)*E+C ≤ K*(E+C) := by
    have dom : r+1 ≤ K := by unfold K; exact Nat.le_mul_of_pos_right _ wp
    have e := Nat.mul_le_mul_right E dom
    have c := Nat.le_mul_of_pos_left C kp
    rw [Nat.mul_add]
    omega
  apply Nat.le_of_mul_le_mul_left _ kp
  rw [Nat.mul_add]
  exact sumcost.trans (Nat.add_le_add_left err _)

end Erdos13Shorter

end

section

/-  A support estimate below the reciprocal boundary for every arity at least four. -/
namespace Erdos13ExtraRow
open Finset FullColumns OMA.Erdos13Universal

theorem strong_shell_gap (r : ℕ) (hr : 4≤r) : ∃ V C : ℕ, 0<V ∧ ∀ (m : ℕ) (A : Finset ℕ),
    A⊆Icc 1 ((r+1)*m) → (∀ x∈A,(4*r-1)*((r+1)*m)<((4*r-1)*(r+1)+1)*x) →
    (∀ j,0<j → j≤r → Free j A) → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m →
    V*A.card+m≤V*m+C := by
  classical
  obtain ⟨K,tail⟩ := tail_bound r hr
  obtain ⟨W,C,wp,bound⟩ := boundary_sparse_stability r (by omega)
  let E := 2*r*r+2*K*(2*K*(r+1)+1)
  let V := (2*r*r+1)*W
  refine ⟨V,(V+1)*C+C+W*E,by dsimp [V]; positivity,?_⟩
  intro m A sub shell strong sparse
  let H := A.filter (fun x=>¬x< m)
  have inc : H⊆A := filter_subset _ _
  have high := bound m H (fun x hx=>⟨(mem_Icc.mp (sub (inc hx))).1,
    by have := (mem_filter.mp hx).2; omega,(mem_Icc.mp (sub (inc hx))).2⟩)
    (fun x hx b hb=>strong r (by omega) le_rfl x (inc hx) b (fun i=>inc (hb i)))
    ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) inc))).trans sparse)
  by_cases low : ∃ x∈A,x< m
  swap
  · have eq : H=A := filter_eq_self.mpr (fun x hx lt=>low ⟨x,hx,lt⟩)
    rw [eq] at high
    have wv : W≤V := Nat.le_mul_of_pos_left _ (by positivity : 0<2*r*r+1)
    exact (lift_weight (W:=V) wp wv high).trans (by omega)
  obtain ⟨b,hb,bl⟩ := low
  let a := A.min' ⟨b,hb⟩
  have ha : a∈A := min'_mem _ _
  have amin (x) (hx : x∈A) : a≤x := min'_le _ x hx
  let z := m-a
  have az : a+z=m := Nat.add_sub_of_le ((amin _ hb).trans bl.le)
  have endeq : (r+1)*a+(r+1)*z=(r+1)*m := by rw [←Nat.mul_add,az]
  have sh := shell a ha
  have short : (4*r-1)*((r+1)*z)<a := by rw [←endeq] at sh; nlinarith only [sh]
  have t := tail (D:=(r+1)*z) (mem_Icc.mp (sub ha)).1 short ha strong
    (fun x hx => endeq ▸ (mem_Icc.mp (sub hx)).2)
  have tailcard : A.card≤(A.filter (a<·)).card+1 := by
    have part := A.card_filter_add_card_filter_not (fun x=>a<x)
    have incl : A.filter (fun x=>¬a<x)⊆{a} := by
      intro x hx
      have := amin x (mem_filter.mp hx).1
      have := (mem_filter.mp hx).2
      simpa using (show x=a by omega)
    have le := card_le_card incl
    simp only [card_singleton] at le
    omega
  have pred : r-1+1=r := by omega
  have rid : (r-1)*(r+1)+1=r*r := by nlinarith only [pred,congrArg (·*r) pred]
  have err := sqrt_absorb r z K
  have localbound : 2*r*r*A.card+z≤2*r*r*m+E := by
    dsimp [E]
    nlinarith only [t,Nat.mul_le_mul_left (r*r) tailcard,congrArg (·*z) rid,congrArg (r*r*·) az,err,Nat.zero_le K]
  have lowcap : (A.filter (fun x=>x< m)).card≤z := by
    have tsub : A.filter (fun x=>x< m)⊆Ico a m := fun x hx=>
      mem_Ico.mpr ⟨amin x (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩
    simpa [z] using card_le_card tsub
  have split : (A.filter (fun x=>x< m)).card+H.card=A.card := A.card_filter_add_card_filter_not _
  have lx := Nat.mul_le_mul_left W localbound
  have sx := congrArg (W*·) split
  simp only [Nat.mul_add] at lx sx
  have spare := Nat.zero_le (((2*r*r+1)*W+1)*C)
  dsimp only [V]
  nlinarith only [Nat.mul_le_mul_left W lowcap,sx,lx,high,spare]

theorem original_shell (r : ℕ) (hr : 4≤r) : ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A⊆Icc 1 N →
    (∀ x∈A,(4*r-1)*N<((4*r-1)*(r+1)+1)*x) → Free r A → (r+1)*A.card≤N+C := by
  classical
  obtain ⟨W,C,wp,gap⟩ := strong_shell_gap r hr
  let P (m : ℕ) (A : Finset ℕ) := (∀ x∈A,(4*r-1)*((r+1)*m)<((4*r-1)*(r+1)+1)*x) ∧
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m
  obtain ⟨E,sp⟩ := Erdos13Shorter.transfer_sparse_gap r W C wp P
    (fun h inc=>⟨fun x hx=>h.1 x (inc hx),
      (Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) inc))).trans h.2⟩)
    (fun m B sub p strong=>gap m B sub p.1 strong p.2)
  obtain ⟨D,major⟩ := Erdos13HalfOccupied.majority_witness (r:=r) (by omega)
  refine ⟨(r+1)*(D+E+r),?_⟩
  intro N A sub supp free
  let m := N/(r+1)
  let B := A.filter (·≤(r+1)*m)
  have inc : B⊆A := filter_subset _ _
  have cover : B⊆Icc 1 ((r+1)*m) := fun x hx=>mem_Icc.mpr ⟨(mem_Icc.mp (sub (inc hx))).1,(mem_filter.mp hx).2⟩
  have hfree : Free r B := fun x hx b hb=>free x (inc hx) b (fun i=>inc (hb i))
  have de := Nat.mod_add_div N (r+1)
  have rem := Nat.mod_lt N (show 0<r+1 by omega)
  have base : (r+1)*m≤N := by dsimp [m]; omega
  have s : ∀ x∈B,(4*r-1)*((r+1)*m)<((4*r-1)*(r+1)+1)*x :=
    fun x hx=>(Nat.mul_le_mul_left _ base).trans_lt (supp _ (inc hx))
  have cap : B.card≤ m+D+E := by
    by_cases sparse : 2*(Ioc (r*m) ((r+1)*m) ∩ B).card≤ m
    · have := sp m B cover ⟨s,sparse⟩ hfree
      omega
    · by_contra! big
      obtain ⟨x,hx,b,hb,dvd⟩ := major m B cover (by omega) (by omega)
      exact hfree x hx b (fun i=>(hb i).1) (fun i=>(hb i).2) dvd
  have last : A.filter (fun x=>¬x≤(r+1)*m)⊆Ioc ((r+1)*m) N := by
    intro x hx
    exact mem_Ioc.mpr ⟨by have := (mem_filter.mp hx).2; omega,(mem_Icc.mp (sub (mem_filter.mp hx).1)).2⟩
  have lim := card_le_card last
  rw [Nat.card_Ioc] at lim
  have part : B.card+(A.filter (fun x=>¬x≤(r+1)*m)).card=A.card := A.card_filter_add_card_filter_not _
  have remainder : N-(r+1)*m≤r := by dsimp [m]; omega
  have ac : A.card≤ m+(D+E+r) := by omega
  have sc := Nat.mul_le_mul_left (r+1) ac
  rw [Nat.mul_add] at sc
  omega

end Erdos13ExtraRow

end

section

/-  Multiple exclusion throughout the admissible range of integer carries. -/
namespace Erdos13ExtraRow
open Finset FullColumns

theorem window_multiple {r n a x k : ℕ} {A : Finset ℕ} (hr : 4≤r)
    (nr : n≤r) (xp : 0<x) (xa : x<a) (kl : 4*r-1≤k)
    (cap : k*x<(r*r+1-k)*a) (fx : full r A a x)
    (free : Free r A) (y : Fin n → ℕ) (ya : ∀ i,y i<a) (hy : ∀ i,almost r A a (y i)) :
    ¬(∑ i,y i) ≡ k*x [MOD a] := by
  classical
  intro rel
  let p := (univ.filter fun i=>x<y i).card
  have upper : (∑ i,y i)<k*x+p*a := by
    have pt (i : Fin n) : y i≤(if x<y i then a else 0)+x := by
      have yi := ya i
      split <;> omega
    have lim := sum_le_sum fun i (_ : i∈(univ : Finset (Fin n)))=>pt i
    simp only [sum_add_distrib,sum_ite,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at lim
    change (∑ i,y i)≤p*a+n*x at lim
    have diff := Nat.mul_lt_mul_of_pos_right (show n<k by omega) xp
    omega
  have ap : 0<a := by omega
  have pn : p≤n := by simpa [p] using card_filter_le (s:=(univ : Finset (Fin n))) (fun i=>x<y i)
  have rk : r≤k := by omega
  have ysum : (∑ i,y i)≤k*a+k*x := by
    have t := (Nat.mul_le_mul_right a (pn.trans (nr.trans rk)))
    omega
  have rel' : (∑ i,y i) ≡ k*a+k*x [MOD a] := rel.trans (by simp [Nat.ModEq])
  obtain ⟨c,cc⟩ := (Nat.modEq_iff_dvd' ysum).mp rel'
  have ceq : c*a+(∑ i,y i)=k*a+k*x := by rw [Nat.mul_comm c a,←cc,Nat.sub_add_cancel ysum]
  have lower : 3*r≤c := by
    have t : k*a<(c+p)*a := by nlinarith only [ceq,upper]
    have lt := Nat.lt_of_mul_lt_mul_right t
    omega
  have top : c≤r*r := by
    have kp : k≤r*r+1 := by
      by_contra! big
      rw [Nat.sub_eq_zero_of_le (by omega : r*r+1≤k),Nat.zero_mul] at cap
      omega
    have sub := Nat.sub_add_cancel kp
    have t : c*a<(r*r+1)*a := by nlinarith only [ceq,cap,congrArg (·*a) sub,Nat.zero_le (∑ i,y i)]
    have lt := Nat.lt_of_mul_lt_mul_right t
    omega
  let l := r-n
  have nl : n+l=r := Nat.add_sub_of_le nr
  choose m hm using hy
  let masks : Fin (n+l) → ℕ := Fin.append m (fun _ : Fin l=>r+1)
  obtain ⟨v,hv,tot⟩ := central_heights hr (n:=n+l) (by omega) masks c (by rwa [nl]) (by rwa [nl])
  let b (i : Fin n) := v (Fin.castAdd l i)
  let e (i : Fin l) := v (Fin.natAdd n i)
  have hb (i : Fin n) : 2≤b i ∧ b i≤r+1 ∧ b i≠m i := by simpa [b,masks] using hv (Fin.castAdd l i)
  have he (i : Fin l) : 2≤e i ∧ e i≤r := by
    have h : 2≤e i ∧ e i≤r+1 ∧ e i≠r+1 := by simpa [e,masks] using hv (Fin.natAdd n i)
    omega
  have sum : (∑ i,b i)+(∑ i,e i)=c := by simpa only [Fin.sum_univ_add,b,e] using tot
  let Y (i : Fin n) := b i*a+y i
  let E (i : Fin l) := (e i+1)*a+x
  let f := Fin.append Y E
  have base := fx 1 (mem_Icc.mpr ⟨le_rfl,by omega⟩)
  rw [Nat.one_mul] at base
  have occ (i) : f i∈A := Fin.addCases
    (fun j=>by simpa [f,Y] using hm j (b j) (mem_Icc.mpr ⟨(by have := (hb j).1; omega),(hb j).2.1⟩) (hb j).2.2)
    (fun j=>by simpa [f,E] using fx (e j+1) (mem_Icc.mpr ⟨by omega,by have := (he j).2; omega⟩)) i
  have bl (i : Fin n) : a+x<Y i := by
    have le := Nat.mul_le_mul_right a (hb i).1
    dsimp [Y]; omega
  have el (i : Fin l) : a+x<E i := by
    have le := Nat.mul_le_mul_right a (he i).1
    dsimp [E]; rw [Nat.add_mul,Nat.one_mul]; omega
  have big (i) : a+x<f i := Fin.addCases (fun j=>by simpa [f] using bl j) (fun j=>by simpa [f] using el j) i
  have fn : Free (n+l) A := by rw [nl]; exact free
  apply fn _ base f occ big
  refine ⟨k+l,?_⟩
  have scale := congrArg (·*a) sum
  simp only [Nat.add_mul] at scale
  simp [f,Fin.sum_univ_add,Y,E,sum_add_distrib,←sum_mul,Nat.add_mul]
  nlinarith only [scale,ceq]

end Erdos13ExtraRow

end

section

namespace Erdos13ExtraRow
open Finset FullColumns OMA.Erdos13StrongResidues
open scoped Pointwise

/-- All short scalar images are distinct and stay outside the augmented r-fold sumset. -/
theorem window_packing {r a k : ℕ} {A Q F : Finset ℕ} (hr : 4≤r) (ap : 0<a) (ha : a∈A)
    (strong : ∀ j,0<j → j≤r → Free j A)
    (off : ∀ y∈Q,y<a) (occ : ∀ y∈Q,almost r A a y)
    (kl : 4*r-1≤k) (sm : ∀ x∈F,0<x ∧ x<a / Nat.gcd a k ∧ k*x<(r*r+1-k)*a) (allrow : ∀ x∈F,full r A a x) :
    r*Q.card+F.card+1≤a := by
  classical
  let : NeZero a := ⟨ap.ne'⟩
  let R := Q.image (fun y : ℕ => (y : ZMod a))
  let T := F.image (fun x : ℕ => ((k*x : ℕ) : ZMod a))
  let S := r • insert 0 R
  have read {j : ℕ} {z : ZMod a} (hz : z ∈ j • R) :
      ∃ y : Fin j → ℕ, (∀ i,y i∈Q) ∧ ((∑ i,y i : ℕ) : ZMod a)=z := by
    obtain ⟨v,hv⟩ := mem_nsmul.mp hz
    have pre (i : Fin j) : ∃ y∈Q,(y : ZMod a) = v i := mem_image.mp (v i).property
    choose y hy eq using pre
    exact ⟨y,hy,by simpa [Nat.cast_sum,eq,List.sum_ofFn] using hv⟩
  have nozero (j : ℕ) (jp : 0<j) (jl : j≤r) : (0 : ZMod a)∉ j • R := by
    intro hz
    obtain ⟨y,hy,eq⟩ := read hz
    have pre (i : Fin j) : ∃ b∈A, a<b ∧ (b : ZMod a)=(y i : ZMod a) := by
      obtain ⟨m,hm⟩ := occ _ (hy i)
      let k := if m=2 then 3 else 2
      have km : k≠m := by dsimp [k]; split <;> omega
      have big : 2≤k ∧ k≤r+1 := by dsimp [k]; split <;> omega
      have le := Nat.mul_le_mul_right a big.1
      exact ⟨k*a+y i,hm k (mem_Icc.mpr ⟨by omega,big.2⟩) km,by omega,by simp⟩
    choose b hb bl be using pre
    apply strong j jp jl a ha b hb bl
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_sum,be] using (show (∑ i,(y i : ZMod a))=0 by simpa only [Nat.cast_sum] using eq)
  have sep : Disjoint S T := disjoint_left.mpr (by
    intro z hz ht
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ht
    obtain ⟨j,jl,hj⟩ := some_nonzero_summands R r hz
    obtain ⟨y,hy,eq⟩ := read hj
    have below := (sm x hx).2.1.trans_le (Nat.div_le_self a _)
    exact window_multiple hr jl (sm x hx).1 below kl (sm x hx).2.2 (allrow x hx) (strong r (by omega) le_rfl)
      y (fun i=>off _ (hy i)) (fun i=>occ _ (hy i)) ((ZMod.natCast_eq_natCast_iff _ _ _).mp eq))
  have cR : R.card=Q.card := card_image_of_injOn (by
    intro x hx y hy eq
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (off x hx),Nat.mod_eq_of_lt (off y hy)] using congrArg ZMod.val eq)
  have cT : T.card=F.card := card_image_of_injOn (by
    intro x hx y hy eq
    have h : k*x ≡ k*y [MOD a] := (ZMod.natCast_eq_natCast_iff _ _ _).mp eq
    have e := Nat.ModEq.cancel_left_div_gcd ap h
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt (sm x hx).2.1,Nat.mod_eq_of_lt (sm y hy).2.1] using e)
  have big := growth_without_short_zero R (by omega : 0<r) nozero
  have cap := (S∪T).card_le_univ
  rw [card_union_of_disjoint sep,ZMod.card,cT] at cap
  change r*R.card+1≤S.card at big
  rw [cR] at big
  omega

end Erdos13ExtraRow

end

section

/-  A strict upper bound on a short final row for arbitrary arity. -/
namespace Erdos13ExtraRow
open Finset FullColumns

theorem window_tail (r : ℕ) (hr : 4≤r) : ∃ K : ℕ, ∀ {a D k : ℕ} {A : Finset ℕ}, 0<a →
    4*r-1≤k → D<a / Nat.gcd a k → k*D<(r*r+1-k)*a → a∈A → (∀ j,0<j → j≤r → Free j A) → (∀ x∈A,x≤(r+1)*a+D) →
    r*r*(A.filter (a<·)).card≤r*r*a+(r-1)*D+K*D.sqrt := by
  classical
  obtain ⟨K,limited⟩ := OMA.Erdos13Mixed.limited_sqrt_bound r (by omega)
  refine ⟨(r-1)*K,?_⟩
  intro a D k A ap kl period span ha strong top
  let B := A.filter (a<·)
  let R := B.image (·%a)
  let I := Icc 1 (r+1)
  let L (u : ℕ) := I.filter (fun i=>i*a+u∈B)
  let Q := R.filter (fun u=>r≤(L u).card)
  let F := R.filter (fun u=>r+1≤(L u).card)
  have qi : Q⊆R := filter_subset _ _
  have fi : F⊆R := filter_subset _ _
  have ci : I.card=r+1 := by simp [I]
  have inc (u) : L u⊆I := filter_subset _ _
  have ls (u) : (L u).card≤r+1 := ci ▸ card_le_card (inc u)
  have off (u) (hu : u∈R) : 0<u ∧ u<a := by
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hu
    obtain ⟨yes,lt⟩ := mem_filter.mp hb
    refine ⟨?_,Nat.mod_lt _ ap⟩
    by_contra! zero
    have dv := Nat.dvd_of_mod_eq_zero (show b%a=0 by omega)
    exact strong 1 (by decide) (by omega) a ha (fun _=>b) (fun _=>yes) (fun _=>lt) (by simpa using dv)
  have fx (u) (hu : u∈F) : full r A a u := by
    have eq : L u=I := eq_of_subset_of_card_le (inc u) (by rw [ci]; exact (mem_filter.mp hu).2)
    exact fun i hi=>(mem_filter.mp ((mem_filter.mp (show i∈L u from eq ▸ hi)).2)).1
  have us (u) (hu : u∈F) : u≤D := by
    have := top _ (fx u hu (r+1) (mem_Icc.mpr ⟨by omega,le_rfl⟩))
    omega
  have qx (u) (hu : u∈Q) : almost r A a u := by
    have big := (mem_filter.mp hu).2
    by_cases whole : I⊆L u
    · exact ⟨0,fun i hi _=>(mem_filter.mp ((mem_filter.mp (whole hi)).2)).1⟩
    obtain ⟨m,mi,miss⟩ := not_subset.mp whole
    have incl : L u⊆I.erase m := fun i hi=>mem_erase.mpr ⟨fun e=>miss (e ▸ hi),inc u hi⟩
    have eh := card_erase_add_one mi
    have eq := eq_of_subset_of_card_le incl (by omega)
    exact ⟨m,fun i hi ne=>(mem_filter.mp ((mem_filter.mp (show i∈L u from eq ▸ mem_erase.mpr ⟨ne,hi⟩)).2)).1⟩
  have reserve := window_packing hr ap ha strong (fun u hu=>(off _ (qi hu)).2) qx
    kl (fun u hu=>⟨(off _ (fi hu)).1,(us _ hu).trans_lt period,(Nat.mul_le_mul_left _ (us _ hu)).trans_lt span⟩) fx
  have low := limited D F (fun u hu=>mem_Icc.mpr ⟨(off _ (fi hu)).1,us _ hu⟩)
    (limited_lifts (a:=a) (by omega : 0<r) (fun u hu j hj=>fx u hu j (mem_Icc.mpr
      ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans (by omega)⟩)) (limited_of_free (strong r (by omega) le_rfl)))
  have rcap : r*R.card+1≤a := OMA.Erdos13StrongResidues.tail_bound (by omega) ap ha strong
  have da : D<a := period.trans_le (Nat.div_le_self a _)
  have fiber (u : ℕ) : (B.filter (fun b=>b%a=u)).card≤(L u).card := by
    apply (card_le_card (t:=(L u).image (fun i=>i*a+u)) ?_).trans card_image_le
    intro b h
    obtain ⟨hb,mod⟩ := mem_filter.mp h
    obtain ⟨hA,ab⟩ := mem_filter.mp hb
    have lo := Nat.div_pos ab.le ap
    have up : b/a<r+2 := (Nat.div_lt_iff_lt_mul ap).mpr (by
      have := top _ hA
      rw [show r+2=(r+1)+1 by omega,Nat.add_mul,Nat.one_mul]
      omega)
    have be : b/a*a+u=b := by rw [←mod,Nat.div_add_mod']
    exact mem_image.mpr ⟨b/a,mem_filter.mpr ⟨mem_Icc.mpr ⟨lo,by omega⟩,by rw [be]; exact hb⟩,be⟩
  have each (u) (hu : u∈R) : (B.filter (fun b=>b%a=u)).card≤(r-1)
      +(if u∈Q then 1 else 0)+(if u∈F then 1 else 0) := by
    have h := fiber u
    have l := ls u
    simp only [Q,F,mem_filter,hu,true_and]
    split_ifs <;> omega
  have cnt := sum_le_sum each
  rw [←card_eq_sum_card_image] at cnt
  simp only [sum_add_distrib,sum_const,Nat.nsmul_eq_mul,sum_ite,filter_mem_eq_inter,
    inter_eq_right.mpr qi,inter_eq_right.mpr fi,Nat.mul_one,mul_zero,add_zero] at cnt
  have bc := Nat.mul_le_mul_left r cnt
  have rr := Nat.mul_le_mul_left (r-1) rcap
  have dec : r-1+1=r := by omega
  have ar := congrArg (·*a) dec
  have fr := congrArg (·*F.card) dec
  have first : r*B.card≤r*a+(r-1)*F.card := by nlinarith only [bc,rr,reserve,ar,fr,Nat.zero_le (r-1)]
  have last := Nat.mul_le_mul_left r first
  have cost := Nat.mul_le_mul_left (r-1) low
  change r*r*B.card≤r*r*a+(r-1)*D+(r-1)*K*D.sqrt
  nlinarith only [last,cost]

end Erdos13ExtraRow

end

section

/-  A support estimate below the reciprocal boundary for every arity at least four. -/
namespace Erdos13ExtraRow
open Finset FullColumns OMA.Erdos13Universal

def admitted (r N a : ℕ) : Prop := N≤(r+1)*a ∨ ∃ k : ℕ, 4*r-1≤k ∧
    (N-(r+1)*a)<a / Nat.gcd a k ∧ k*(N-(r+1)*a)<(r*r+1-k)*a

theorem admitted_mono {r M N a : ℕ} (mn : M≤N) (h : admitted r N a) : admitted r M a := by
  rcases h with d|⟨k,kl,per,cap⟩
  · exact Or.inl (mn.trans d)
  · have s := Nat.sub_le_sub_right mn ((r+1)*a)
    exact Or.inr ⟨k,kl,s.trans_lt per,(Nat.mul_le_mul_left k s).trans_lt cap⟩

theorem window_gap (r : ℕ) (hr : 4≤r) : ∃ V C : ℕ, 0<V ∧ ∀ (m : ℕ) (A : Finset ℕ),
    A⊆Icc 1 ((r+1)*m) → (∀ x∈A,admitted r ((r+1)*m) x) →
    (∀ j,0<j → j≤r → Free j A) → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m →
    V*A.card+m≤V*m+C := by
  classical
  obtain ⟨K,tail⟩ := window_tail r hr
  obtain ⟨W,C,wp,bound⟩ := boundary_sparse_stability r (by omega)
  let E := 2*r*r+2*K*(2*K*(r+1)+1)
  let V := (2*r*r+1)*W
  refine ⟨V,(V+1)*C+C+W*E,by dsimp [V]; positivity,?_⟩
  intro m A sub shell strong sparse
  let H := A.filter (fun x=>¬x< m)
  have inc : H⊆A := filter_subset _ _
  have high := bound m H (fun x hx=>⟨(mem_Icc.mp (sub (inc hx))).1,
    by have := (mem_filter.mp hx).2; omega,(mem_Icc.mp (sub (inc hx))).2⟩)
    (fun x hx b hb=>strong r (by omega) le_rfl x (inc hx) b (fun i=>inc (hb i)))
    ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) inc))).trans sparse)
  by_cases low : ∃ x∈A,x< m
  swap
  · have eq : H=A := filter_eq_self.mpr (fun x hx lt=>low ⟨x,hx,lt⟩)
    rw [eq] at high
    have wv : W≤V := Nat.le_mul_of_pos_left _ (by positivity : 0<2*r*r+1)
    exact (lift_weight (W:=V) wp wv high).trans (by omega)
  obtain ⟨b,hb,bl⟩ := low
  let a := A.min' ⟨b,hb⟩
  have ha : a∈A := min'_mem _ _
  have amin (x) (hx : x∈A) : a≤x := min'_le _ x hx
  let z := m-a
  have az : a+z=m := Nat.add_sub_of_le ((amin _ hb).trans bl.le)
  have endeq : (r+1)*a+(r+1)*z=(r+1)*m := by rw [←Nat.mul_add,az]
  have lt := Nat.mul_lt_mul_of_pos_left ((amin _ hb).trans_lt bl) (by omega : 0<r+1)
  obtain ⟨k,kl,per,cap⟩ := (shell a ha).resolve_left (by omega)
  have dz : (r+1)*m-(r+1)*a=(r+1)*z := by omega
  rw [dz] at per cap
  have t := tail (D:=(r+1)*z) (mem_Icc.mp (sub ha)).1 kl per cap ha strong
    (fun x hx => endeq ▸ (mem_Icc.mp (sub hx)).2)
  have tailcard : A.card≤(A.filter (a<·)).card+1 := by
    have part := A.card_filter_add_card_filter_not (fun x=>a<x)
    have incl : A.filter (fun x=>¬a<x)⊆{a} := by
      intro x hx
      have := amin x (mem_filter.mp hx).1
      have := (mem_filter.mp hx).2
      simpa using (show x=a by omega)
    have le := card_le_card incl
    simp only [card_singleton] at le
    omega
  have pred : r-1+1=r := by omega
  have rid : (r-1)*(r+1)+1=r*r := by nlinarith only [pred,congrArg (·*r) pred]
  have err := sqrt_absorb r z K
  have localbound : 2*r*r*A.card+z≤2*r*r*m+E := by
    dsimp [E]
    nlinarith only [t,Nat.mul_le_mul_left (r*r) tailcard,congrArg (·*z) rid,congrArg (r*r*·) az,err,Nat.zero_le K]
  have lowcap : (A.filter (fun x=>x< m)).card≤z := by
    have tsub : A.filter (fun x=>x< m)⊆Ico a m := fun x hx=>
      mem_Ico.mpr ⟨amin x (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩
    simpa [z] using card_le_card tsub
  have split : (A.filter (fun x=>x< m)).card+H.card=A.card := A.card_filter_add_card_filter_not _
  have lx := Nat.mul_le_mul_left W localbound
  have sx := congrArg (W*·) split
  simp only [Nat.mul_add] at lx sx
  have spare := Nat.zero_le (((2*r*r+1)*W+1)*C)
  dsimp only [V]
  nlinarith only [Nat.mul_le_mul_left W lowcap,sx,lx,high,spare]

theorem original_window (r : ℕ) (hr : 4≤r) : ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A⊆Icc 1 N →
    (∀ x∈A,admitted r N x) → Free r A → (r+1)*A.card≤N+C := by
  classical
  obtain ⟨W,C,wp,gap⟩ := window_gap r hr
  let P (m : ℕ) (A : Finset ℕ) := (∀ x∈A,admitted r ((r+1)*m) x) ∧
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m
  obtain ⟨E,sp⟩ := Erdos13Shorter.transfer_sparse_gap r W C wp P
    (fun h inc=>⟨fun x hx=>h.1 x (inc hx),
      (Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) inc))).trans h.2⟩)
    (fun m B sub p strong=>gap m B sub p.1 strong p.2)
  obtain ⟨D,major⟩ := Erdos13HalfOccupied.majority_witness (r:=r) (by omega)
  refine ⟨(r+1)*(D+E+r),?_⟩
  intro N A sub supp free
  let m := N/(r+1)
  let B := A.filter (·≤(r+1)*m)
  have inc : B⊆A := filter_subset _ _
  have cover : B⊆Icc 1 ((r+1)*m) := fun x hx=>mem_Icc.mpr ⟨(mem_Icc.mp (sub (inc hx))).1,(mem_filter.mp hx).2⟩
  have hfree : Free r B := fun x hx b hb=>free x (inc hx) b (fun i=>inc (hb i))
  have de := Nat.mod_add_div N (r+1)
  have rem := Nat.mod_lt N (show 0<r+1 by omega)
  have base : (r+1)*m≤N := by dsimp [m]; omega
  have s : ∀ x∈B,admitted r ((r+1)*m) x := fun x hx=>admitted_mono base (supp _ (inc hx))
  have cap : B.card≤ m+D+E := by
    by_cases sparse : 2*(Ioc (r*m) ((r+1)*m) ∩ B).card≤ m
    · have := sp m B cover ⟨s,sparse⟩ hfree
      omega
    · by_contra! big
      obtain ⟨x,hx,b,hb,dvd⟩ := major m B cover (by omega) (by omega)
      exact hfree x hx b (fun i=>(hb i).1) (fun i=>(hb i).2) dvd
  have last : A.filter (fun x=>¬x≤(r+1)*m)⊆Ioc ((r+1)*m) N := by
    intro x hx
    exact mem_Ioc.mpr ⟨by have := (mem_filter.mp hx).2; omega,(mem_Icc.mp (sub (mem_filter.mp hx).1)).2⟩
  have lim := card_le_card last
  rw [Nat.card_Ioc] at lim
  have part : B.card+(A.filter (fun x=>¬x≤(r+1)*m)).card=A.card := A.card_filter_add_card_filter_not _
  have remainder : N-(r+1)*m≤r := by dsimp [m]; omega
  have ac : A.card≤ m+(D+E+r) := by omega
  have sc := Nat.mul_le_mul_left (r+1) ac
  rw [Nat.mul_add] at sc
  omega

end Erdos13ExtraRow

end

section

/-  Paying for the pivots that have no invertible multiplier by counting their common prime factors. -/
namespace Erdos13ExtraRow
open Finset FullColumns OMA.Erdos13Universal Erdos13ColumnModulo

theorem gap_at_weight {r W C : ℕ} (hr : 4≤r) (wp : 0<W)
    (bound : ∀ (m : ℕ) (A : Finset ℕ), (∀ x∈A,0<x ∧ m≤x ∧ x≤(r+1)*m) →
      Free r A → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m → W*A.card+m≤W*m+C) :
    ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A⊆Icc 1 ((r+1)*m) → (∀ x∈A,admitted r ((r+1)*m) x) →
    (∀ j,0<j → j≤r → Free j A) → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m →
    ((2*r*r+1)*W)*A.card+m≤((2*r*r+1)*W)*m+K := by
  classical
  obtain ⟨K,tail⟩ := window_tail r hr
  let E := 2*r*r+2*K*(2*K*(r+1)+1)
  let V := (2*r*r+1)*W
  refine ⟨(V+1)*C+C+W*E,?_⟩
  intro m A sub shell strong sparse
  change V*A.card+m≤V*m+_
  let H := A.filter (fun x=>¬x< m)
  have inc : H⊆A := filter_subset _ _
  have high := bound m H (fun x hx=>⟨(mem_Icc.mp (sub (inc hx))).1,
    by have := (mem_filter.mp hx).2; omega,(mem_Icc.mp (sub (inc hx))).2⟩)
    (fun x hx b hb=>strong r (by omega) le_rfl x (inc hx) b (fun i=>inc (hb i)))
    ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) inc))).trans sparse)
  by_cases low : ∃ x∈A,x< m
  swap
  · have eq : H=A := filter_eq_self.mpr (fun x hx lt=>low ⟨x,hx,lt⟩)
    rw [eq] at high
    have wv : W≤V := Nat.le_mul_of_pos_left _ (by positivity : 0<2*r*r+1)
    exact (lift_weight (W:=V) wp wv high).trans (by omega)
  obtain ⟨b,hb,bl⟩ := low
  let a := A.min' ⟨b,hb⟩
  have ha : a∈A := min'_mem _ _
  have amin (x) (hx : x∈A) : a≤x := min'_le _ x hx
  let z := m-a
  have az : a+z=m := Nat.add_sub_of_le ((amin _ hb).trans bl.le)
  have endeq : (r+1)*a+(r+1)*z=(r+1)*m := by rw [←Nat.mul_add,az]
  have lt := Nat.mul_lt_mul_of_pos_left ((amin _ hb).trans_lt bl) (by omega : 0<r+1)
  obtain ⟨k,kl,per,cap⟩ := (shell a ha).resolve_left (by omega)
  have dz : (r+1)*m-(r+1)*a=(r+1)*z := by omega
  rw [dz] at per cap
  have t := tail (D:=(r+1)*z) (mem_Icc.mp (sub ha)).1 kl per cap ha strong
    (fun x hx => endeq ▸ (mem_Icc.mp (sub hx)).2)
  have tailcard : A.card≤(A.filter (a<·)).card+1 := by
    have part := A.card_filter_add_card_filter_not (fun x=>a<x)
    have incl : A.filter (fun x=>¬a<x)⊆{a} := by
      intro x hx
      have := amin x (mem_filter.mp hx).1
      have := (mem_filter.mp hx).2
      simpa using (show x=a by omega)
    have le := card_le_card incl
    simp only [card_singleton] at le
    omega
  have pred : r-1+1=r := by omega
  have rid : (r-1)*(r+1)+1=r*r := by nlinarith only [pred,congrArg (·*r) pred]
  have err := sqrt_absorb r z K
  have localbound : 2*r*r*A.card+z≤2*r*r*m+E := by
    dsimp [E]
    nlinarith only [t,Nat.mul_le_mul_left (r*r) tailcard,congrArg (·*z) rid,congrArg (r*r*·) az,err,Nat.zero_le K]
  have lowcap : (A.filter (fun x=>x< m)).card≤z := by
    have tsub : A.filter (fun x=>x< m)⊆Ico a m := fun x hx=>
      mem_Ico.mpr ⟨amin x (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩
    simpa [z] using card_le_card tsub
  have split : (A.filter (fun x=>x< m)).card+H.card=A.card := A.card_filter_add_card_filter_not _
  have lx := Nat.mul_le_mul_left W localbound
  have sx := congrArg (W*·) split
  simp only [Nat.mul_add] at lx sx
  have spare := Nat.zero_le (((2*r*r+1)*W+1)*C)
  dsimp only [V]
  nlinarith only [Nat.mul_le_mul_left W lowcap,sx,lx,high,spare]


def weight (r : ℕ) := (2*r*r+1)*shellWeight r
def usable (r a : ℕ) : Prop := ∃ k : ℕ, 4*r-1≤k ∧ 2*k≤r*r+1 ∧ k.Coprime a

theorem admitted_of_usable {r N a : ℕ} (hr : 4≤r) (short : N<(r+2)*a) (ok : usable r a) : admitted r N a := by
  by_cases high : N≤(r+1)*a
  · exact Or.inl high
  obtain ⟨k,lo,hi,cop⟩ := ok
  have d : N-(r+1)*a<a := by rw [show r+2=r+1+1 by omega,Nat.add_mul,Nat.one_mul] at short; omega
  have c : Nat.gcd a k=1 := cop.symm.gcd_eq_one
  refine Or.inr ⟨k,lo,by simpa [c] using d,?_⟩
  have kp : 0<k := by omega
  exact (Nat.mul_lt_mul_of_pos_left d kp).trans_le (Nat.mul_le_mul_right a (by omega))

theorem paid_gap {r P : ℕ} (hr : 9≤r) (payment : 2*weight r≤P)
    (factor : ∀ a, ¬usable r a → P∣a) : ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A⊆Icc 1 ((r+1)*m) → (∀ a∈A,(r+1)*m<(r+2)*a) →
    (∀ j,0<j → j≤r → Free j A) → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m →
    (2*weight r)*A.card+m≤(2*weight r)*m+K := by
  classical
  obtain ⟨C,h⟩ := wider_sparse_stability hr
  have wp : 0<shellWeight r := by dsimp [shellWeight]; positivity
  obtain ⟨E,bound⟩ := gap_at_weight (by omega : 4≤r) wp h
  refine ⟨2*E,?_⟩
  intro m A sub supp strong sparse
  let G := A.filter (admitted r ((r+1)*m))
  let B := A.filter (fun x=>¬admitted r ((r+1)*m) x)
  have inc : G⊆A := filter_subset _ _
  have good := bound m G (inc.trans sub) (fun x hx=>(mem_filter.mp hx).2)
    (fun j jp jr x hx b hb=>strong j jp jr x (inc hx) b (fun i=>inc (hb i)))
    ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) inc))).trans sparse)
  change weight r*G.card+m≤weight r*m+E at good
  have hp : 0<P := (show 0<2*weight r by dsimp [weight]; positivity).trans_le payment
  have div (x) (hx : x∈B) : P∣x := factor x (fun ok=>(mem_filter.mp hx).2 (admitted_of_usable (by omega) (supp x (mem_filter.mp hx).1) ok))
  have lim (x) (hx : x∈B) : 0<x ∧ x≤ m := by
    refine ⟨(mem_Icc.mp (sub (mem_filter.mp hx).1)).1,?_⟩
    by_contra! gt
    exact (mem_filter.mp hx).2 (Or.inl (Nat.mul_le_mul_left _ gt.le))
  have num : B.card≤ m/P := by
    apply (card_le_card_of_injOn (fun x=>x/P) (t:=Icc 1 (m/P)) ?_ ?_).trans (by simp)
    · intro x hx
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (lim x hx).1 (div x hx)) hp,Nat.div_le_div_right (lim x hx).2⟩
    · intro x hx y hy eq
      simpa [Nat.div_mul_cancel (div x hx),Nat.div_mul_cancel (div y hy)] using congrArg (·*P) eq
  have pay := (Nat.mul_le_mul_left B.card payment)
  have loss := (Nat.mul_le_mul_left P num).trans (Nat.mul_div_le m P)
  have split : G.card+B.card=A.card := A.card_filter_add_card_filter_not _
  rw [←split,Nat.mul_add]
  nlinarith only [pay,loss,good]

end Erdos13ExtraRow

end

section

/-  Prime-power choices cover every pivot except for a progression sparse enough to absorb. -/
namespace Erdos13ExtraRow
open Finset FullColumns Erdos13ColumnModulo

def factors (r : ℕ) : Prop := ∃ P : ℕ, 2*weight r≤P ∧ ∀ a, ¬usable r a → P∣a

theorem finite_factors {r l h : ℕ} (lo : l≤r) (hi : r≤h) (S : Finset ℕ)
    (size : 2*weight h≤S.prod id)
    (primes : ∀ p∈S,p.Prime ∧ ∃ e∈Icc 1 2, 4*h-1≤p^e ∧ 2*p^e≤l*l+1) : factors r := by
  refine ⟨S.prod id,le_trans ?_ size,?_⟩
  · dsimp [weight,shellWeight,localGain]
    gcongr
  intro a bad
  rcases Nat.eq_zero_or_pos a with rfl|pos
  · exact dvd_zero _
  have sub : S⊆a.primeFactors := by
    intro p hp
    obtain ⟨pr,e,_,lb,ub⟩ := primes p hp
    exact Nat.mem_primeFactors.mpr ⟨pr,pr.dvd_iff_not_coprime.mpr (fun cop=>bad
      ⟨p^e,by omega,ub.trans (Nat.add_le_add_right (Nat.mul_le_mul lo lo) 1),cop.pow_left e⟩),pos.ne'⟩
  exact (Finset.prod_dvd_prod_of_subset _ _ id sub).trans (Nat.prod_primeFactors_dvd a)

theorem bertrand_factors {r : ℕ} (hr : 512≤r) : factors r := by
  obtain ⟨p0,pr0,lo0,hi0⟩ := Nat.exists_prime_lt_and_le_two_mul (4*r) (by omega)
  obtain ⟨p1,pr1,lo1,hi1⟩ := Nat.exists_prime_lt_and_le_two_mul (8*r) (by omega)
  obtain ⟨p2,pr2,lo2,hi2⟩ := Nat.exists_prime_lt_and_le_two_mul (16*r) (by omega)
  obtain ⟨p3,pr3,lo3,hi3⟩ := Nat.exists_prime_lt_and_le_two_mul (32*r) (by omega)
  obtain ⟨p4,pr4,lo4,hi4⟩ := Nat.exists_prime_lt_and_le_two_mul (64*r) (by omega)
  obtain ⟨p5,pr5,lo5,hi5⟩ := Nat.exists_prime_lt_and_le_two_mul (128*r) (by omega)
  refine ⟨p0*p1*p2*p3*p4*p5,?_,?_⟩
  · calc
      2*weight r ≤ (4*r)*(8*r)*(16*r)*(32*r)*(64*r)*(128*r) := by
        obtain ⟨x,rfl⟩ := Nat.exists_eq_add_of_le hr
        dsimp [weight,shellWeight,localGain]
        ring_nf
        omega
      _ ≤ p0*p1*p2*p3*p4*p5 := by gcongr
  intro a bad
  have bound := Nat.mul_le_mul_right r hr
  have div (p : ℕ) (pr : p.Prime) (low : 4*r-1≤p) (upp : p≤256*r) : p∣a :=
    pr.dvd_iff_not_coprime.mpr (fun cop=>bad ⟨p,low,by omega,cop⟩)
  have d0 := div p0 pr0 (by omega) (by omega)
  have d1 := div p1 pr1 (by omega) (by omega)
  have d2 := div p2 pr2 (by omega) (by omega)
  have d3 := div p3 pr3 (by omega) (by omega)
  have d4 := div p4 pr4 (by omega) (by omega)
  have d5 := div p5 pr5 (by omega) (by omega)
  have c01 := (Nat.coprime_primes pr0 pr1).mpr (by omega)
  have prod1 := c01.mul_dvd_of_dvd_of_dvd d0 d1
  have c02 := (Nat.coprime_primes pr0 pr2).mpr (by omega)
  have c12 := (Nat.coprime_primes pr1 pr2).mpr (by omega)
  have prod2 := (c02.mul_left c12).mul_dvd_of_dvd_of_dvd prod1 d2
  have c03 := (Nat.coprime_primes pr0 pr3).mpr (by omega)
  have c13 := (Nat.coprime_primes pr1 pr3).mpr (by omega)
  have c23 := (Nat.coprime_primes pr2 pr3).mpr (by omega)
  have prod3 := ((c03.mul_left c13).mul_left c23).mul_dvd_of_dvd_of_dvd prod2 d3
  have c04 := (Nat.coprime_primes pr0 pr4).mpr (by omega)
  have c14 := (Nat.coprime_primes pr1 pr4).mpr (by omega)
  have c24 := (Nat.coprime_primes pr2 pr4).mpr (by omega)
  have c34 := (Nat.coprime_primes pr3 pr4).mpr (by omega)
  have prod4 := (((c04.mul_left c14).mul_left c24).mul_left c34).mul_dvd_of_dvd_of_dvd prod3 d4
  have c05 := (Nat.coprime_primes pr0 pr5).mpr (by omega)
  have c15 := (Nat.coprime_primes pr1 pr5).mpr (by omega)
  have c25 := (Nat.coprime_primes pr2 pr5).mpr (by omega)
  have c35 := (Nat.coprime_primes pr3 pr5).mpr (by omega)
  have c45 := (Nat.coprime_primes pr4 pr5).mpr (by omega)
  have prod5 := ((((c05.mul_left c15).mul_left c25).mul_left c35).mul_left c45).mul_dvd_of_dvd_of_dvd prod4 d5
  exact prod5

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem factors_from_eleven (r : ℕ) (hr : 11≤r) : factors r := by
  by_cases h : 512≤r
  · exact bertrand_factors h
  by_cases c78 : 78≤r
  · exact finite_factors c78 (show r≤511 by omega) {2053,2063,2069,2081,2083,2087,2089} (by decide) (by decide)
  by_cases c26 : 26≤r
  · exact finite_factors c26 (show r≤77 by omega) {307,311,313,317,331,337} (by decide) (by decide)
  by_cases c16 : 16≤r
  · exact finite_factors c16 (show r≤25 by omega) {101,103,107,109,113,127} (by decide) (by decide)
  by_cases c13 : 13≤r
  · exact finite_factors c13 (show r≤15 by omega) {59,61,67,71,73,79,83} (by decide) (by decide)
  by_cases c12 : 12≤r
  · exact finite_factors c12 (show r≤12 by omega) {47,53,59,61,67,71} (by decide) (by decide)
  exact finite_factors hr (show r≤11 by omega) {7,43,47,53,59,61} (by decide) (by decide)

end Erdos13ExtraRow

end

section

/-  The full supported estimate down to N/(r+2) at every arity at least eleven. -/
namespace Erdos13ExtraRow
open Finset FullColumns

theorem original_one_more_row (r : ℕ) (hr : 11≤r) : ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A⊆Icc 1 N →
    (∀ x∈A,N<(r+2)*x) → Free r A → (r+1)*A.card≤N+C := by
  classical
  obtain ⟨P,pay,fac⟩ := factors_from_eleven r hr
  obtain ⟨C,gap⟩ := paid_gap (by omega : 9≤r) pay fac
  let W := 2*weight r
  have wp : 0<W := by dsimp [W,weight,Erdos13ColumnModulo.shellWeight]; positivity
  let P (m : ℕ) (A : Finset ℕ) := (∀ x∈A,(r+1)*m<(r+2)*x) ∧
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m
  obtain ⟨E,sp⟩ := Erdos13Shorter.transfer_sparse_gap r W C wp P
    (fun h inc=>⟨fun x hx=>h.1 x (inc hx),
      (Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) inc))).trans h.2⟩)
    (fun m B sub p strong=>gap m B sub p.1 strong p.2)
  obtain ⟨D,major⟩ := Erdos13HalfOccupied.majority_witness (r:=r) (by omega)
  refine ⟨(r+1)*(D+E+r),?_⟩
  intro N A sub supp free
  let m := N/(r+1)
  let B := A.filter (·≤(r+1)*m)
  have inc : B⊆A := filter_subset _ _
  have cover : B⊆Icc 1 ((r+1)*m) := fun x hx=>mem_Icc.mpr ⟨(mem_Icc.mp (sub (inc hx))).1,(mem_filter.mp hx).2⟩
  have hfree : Free r B := fun x hx b hb=>free x (inc hx) b (fun i=>inc (hb i))
  have de := Nat.mod_add_div N (r+1)
  have rem := Nat.mod_lt N (show 0<r+1 by omega)
  have base : (r+1)*m≤N := by dsimp [m]; omega
  have s : ∀ x∈B,(r+1)*m<(r+2)*x := fun x hx=>base.trans_lt (supp _ (inc hx))
  have cap : B.card≤ m+D+E := by
    by_cases sparse : 2*(Ioc (r*m) ((r+1)*m) ∩ B).card≤ m
    · have := sp m B cover ⟨s,sparse⟩ hfree
      omega
    · by_contra! big
      obtain ⟨x,hx,b,hb,dvd⟩ := major m B cover (by omega) (by omega)
      exact hfree x hx b (fun i=>(hb i).1) (fun i=>(hb i).2) dvd
  have last : A.filter (fun x=>¬x≤(r+1)*m)⊆Ioc ((r+1)*m) N := by
    intro x hx
    exact mem_Ioc.mpr ⟨by have := (mem_filter.mp hx).2; omega,(mem_Icc.mp (sub (mem_filter.mp hx).1)).2⟩
  have lim := card_le_card last
  rw [Nat.card_Ioc] at lim
  have part : B.card+(A.filter (fun x=>¬x≤(r+1)*m)).card=A.card := A.card_filter_add_card_filter_not _
  have remainder : N-(r+1)*m≤r := by dsimp [m]; omega
  have ac : A.card≤ m+(D+E+r) := by omega
  have sc := Nat.mul_le_mul_left (r+1) ac
  rw [Nat.mul_add] at sc
  omega

end Erdos13ExtraRow

end

section

/-  Original free sets with a sparse top interval have many pivots below the new support cutoffs. -/
namespace Erdos13ExtraRow
open Finset FullColumns
open scoped Classical

def outside (r N a : ℕ) := if 11≤r then (r+2)*a≤N else ((4*r-1)*(r+1)+1)*a≤(4*r-1)*N

theorem raw_record {r W E : ℕ} (wp : 0<W) (P : ℕ → ℕ → Prop)
    (gap : ∀ (m : ℕ) (A : Finset ℕ), A⊆Icc 1 ((r+1)*m) → (∀ x∈A,¬P m x) →
      (∀ j,0<j → j≤r → Free j A) → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m →
      W*A.card+m≤W*m+E) :
    ∃ V C : ℕ, 0<V ∧ ∀ (m : ℕ) (A : Finset ℕ), A⊆Icc 1 ((r+1)*m) →
      Free r A → m≤A.card → 2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m → m≤V*(A.filter (P m)).card+C := by
  classical
  obtain ⟨D,remove⟩ := Erdos13Shorter.simultaneous_removal r (2*(r+1)*W) (by positivity)
  refine ⟨2*W,2*E+2*D,by positivity,?_⟩
  intro m A sub free big sparse
  obtain ⟨B,ba,loss,strong⟩ := remove ((r+1)*m) A sub free
  let H := B.filter (fun x=>¬P m x)
  have hb : H⊆B := filter_subset _ _
  have ha := hb.trans ba
  have cap := gap m H (ha.trans sub) (fun x hx=>(mem_filter.mp hx).2)
    (fun j jp jr x hx b h=>strong j jp jr x (hb hx) b (fun i=>hb (h i)))
    ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) ha))).trans sparse)
  have bl : (B.filter (P m)).card≤(A.filter (P m)).card := card_le_card (filter_subset_filter _ ba)
  have a' := card_sdiff_add_card_eq_card ba
  have b' : (B.filter (P m)).card+H.card=B.card := B.card_filter_add_card_filter_not _
  have size : m≤H.card+(A \ B).card+(A.filter (P m)).card := by omega
  have pay : 2*W*(A \ B).card≤ m+D := by
    apply Nat.le_of_mul_le_mul_left (c:=r+1) _ (by omega)
    have err := Nat.le_mul_of_pos_left D (by omega : 0<r+1)
    nlinarith only [loss,err]
  nlinarith only [Nat.mul_le_mul_left W size,cap,pay,Nat.zero_le D]

theorem outside_record (r : ℕ) (hr : 4≤r) : ∃ V C : ℕ, 0<V ∧
    ∀ (m : ℕ) (A : Finset ℕ), A⊆Icc 1 ((r+1)*m) → Free r A → m≤A.card →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card≤ m → m≤V*(A.filter (outside r ((r+1)*m))).card+C := by
  by_cases big : 11≤r
  · obtain ⟨P,pay,fac⟩ := factors_from_eleven r big
    obtain ⟨C,gap⟩ := paid_gap (by omega : 9≤r) pay fac
    apply raw_record (P:=fun m=>outside r ((r+1)*m)) (W:=2*weight r) (E:=C) (by dsimp [weight,Erdos13ColumnModulo.shellWeight]; positivity)
    intro m A sub all strong sparse
    exact gap m A sub (fun x hx=>by simpa [outside,big] using all x hx) strong sparse
  · obtain ⟨W,C,wp,gap⟩ := strong_shell_gap r hr
    apply raw_record (P:=fun m=>outside r ((r+1)*m)) (W:=W) (E:=C) wp
    intro m A sub all strong sparse
    exact gap m A sub (fun x hx=>by simpa [outside,big] using all x hx) strong sparse

end Erdos13ExtraRow

end

theorem OMA.solution : OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1_H2_R1.H2 := by
  classical
  intro r hr
  obtain ⟨V,C,vp,cap⟩ := Erdos13ExtraRow.outside_record r hr
  refine ⟨V,C,vp,?_⟩
  intro m A sub free size sparse
  have bound := cap m A sub free size sparse
  have eq : A.filter (Erdos13ExtraRow.outside r ((r+1)*m)) =
      A.filter (fun a=>if 11 ≤ r then (r+2)*a ≤ (r+1)*m else ((4*r-1)*(r+1)+1)*a ≤ (4*r-1)*((r+1)*m)) := by
    ext a
    simp only [Finset.mem_filter,Erdos13ExtraRow.outside]
  rw [eq] at bound
  exact bound
