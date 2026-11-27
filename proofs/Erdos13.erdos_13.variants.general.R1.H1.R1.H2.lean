import OMAReductions.R_Erdos13_erdos_13_variants_general_R1_H1_R1

-- Credit: @jenil-bodhani


section

/-!
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

/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Adapted from gdahia/ExtendingPollardForTRepresentableSums, commit 516693eeee.
Licensed under the Apache License, Version 2.0, available at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: Mantas Bakšys, Yaël Dillies
-/

/-!
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

/-! # A cyclic quotient obstruction for a forbidden iterated sum -/

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

/-! Widen the upper half by permitting a small incomplete second period. -/

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

/-! # Cyclic quotient witnesses for admissible sets and their residue fibers -/
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

/-! A cardinal bound in the top two thirds of the interval. -/
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

/-! Strict savings for the sparse terminal interval. -/
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

/-! Induction on the number of complete residue layers. -/
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

/-! A strict saving for sparse terminal intervals with every element at least N/r. -/

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
theorem sparse_top_stability (r : ℕ) (hr : 3 ≤ r) :
    ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 0 < a ∧ (r+1)*m ≤ r*a ∧ a ≤ (r+1)*m) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
      (24*r*r*(r+1)+1)*A.card ≤ 24*r*r*((r+1)*m)+K := by
  classical
  obtain ⟨C, prev⟩ := shell_to_arity r hr
  let D₃ := (3072*r + 2*(25*(100*((r+1)*(16*r+1)+32*r+1)+1))) +
    (24*(r+1)+1)*(64*r+1)
  let M := 24*r*r
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
    have leM : 24 ≤ M := by dsimp [M]; nlinarith [Nat.mul_le_mul hr hr]
    apply lift_gain leM major
    exact strong.trans (Nat.add_le_add_left (by dsimp [D]; omega) _)
  by_cases big : 4*(r+1) < a/d
  · have strong := medium_quotient_strict hr han span hd big B hB quot
    have leM : 2*r*r ≤ M := by dsimp [M]; gcongr <;> decide
    apply lift_gain leM major
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
    have leM : 4*J ≤ M := by
      have := Nat.mul_le_mul_right r (show 1 ≤ r by omega)
      dsimp [M]
      nlinarith only [Jlt, this, Nat.zero_le (r*r)]
    apply lift_gain leM major
    have num : 4*J*J*E+J*((4*J+1)*(J*(4*J+1)*C+1)) ≤ Dj := by
      dsimp [Dj]
      gcongr <;> omega
    change (4*J*(r+1)+1)*B.card ≤ 4*J*N+4*J*J*E+J*((4*J+1)*(J*(4*J+1)*C+1)) at est
    dsimp [D]
    omega

end OMA.Erdos13ManyLayers

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

/-! A sharp bound for sets avoiding multiples of three, including sets occupying
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

/-! A strict density gap for sets avoiding multiples of three. -/

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

/-! A general quotient obstruction for terminal densities above 2/(r+1). -/
namespace Erdos13HalfOccupied

open Finset

lemma twice_period_obstruction {r m q c b : ℕ} (hr : 3 ≤ r) (hq : 0 < q)
    (hqm : q ≤ m) (he : r*c ≤ q+r-2) (dense : 2*m < (r+1)*b)
    (cap : b ≤ (m / q)*c + min (m % q) c) :
    q ≤ 6*r ∨ (r*m/(r+1) - r ≤ q ∧ q ≤ r*m/(r+1)+2) := by
  by_cases tiny : q ≤ 6*r
  · exact Or.inl tiny
  right
  let t := m/q
  let s := m%q
  have dec : s + t*q = m := by
    dsimp [s, t]
    simpa only [Nat.mul_comm] using Nat.mod_add_div m q
  have hc3 : 3*c ≤ r*c := Nat.mul_le_mul_right c hr
  have rc : r*c ≤ q+r := by omega
  have rq : (r+1)*c ≤ 2*q := by nlinarith only [hc3,rc,tiny]
  have hc5 : (3*r+1)*c ≤ 4*q := by nlinarith only [hc3,rc,tiny]
  have hcap : b ≤ t*c + min s c := cap
  have hmin (n : ℕ) : (r+1)*min n c ≤ 2*n+(r-1)*c := by
    have ar := Nat.mul_le_mul_left (r-1) (min_le_right n c)
    have h := min_le_left n c
    have eqr : r-1+1=r := by omega
    have eqc := congrArg (fun j => j*(min n c)) eqr
    nlinarith only [ar,h,eqc]
  have ht : t ≤ 1 := by
    by_contra! high
    have hA := Nat.mul_le_mul_left (r+1) hcap
    have diff : (2*q-(r+1)*c) + (r+1)*c = 2*q := Nat.sub_add_cancel rq
    have grow := Nat.mul_le_mul_right (2*q-(r+1)*c) high
    have eq := congrArg (fun k => t*k) diff
    have ec := congrArg (fun k => k*c) (show r-1+1=r by omega)
    nlinarith only [eq,grow,diff,ec,hc5,hA,hmin s,dense,dec]
  have hone : t = 1 := Nat.le_antisymm ht (Nat.div_pos hqm hq)
  rw [hone, Nat.one_mul] at dec hcap
  have b1 : b ≤ 2*c := by omega
  have b2 : b ≤ c+s := by omega
  have bound1 := Nat.mul_le_mul_left (r+1) b1
  have bound2 := Nat.mul_le_mul_left (r+1) b2
  have lb : r*m < (r+1)*(q+r) := by
    have lower : m < (r+1)*c := by nlinarith only [bound1,dense]
    have hmul := Nat.mul_lt_mul_of_pos_left lower (show 0 < r by omega)
    have upper := Nat.mul_le_mul_left (r+1) rc
    nlinarith only [hmul,upper]
  have ltDiv : r*m/(r+1) < q+r :=
    (Nat.div_lt_iff_lt_mul (by omega : 0<r+1)).mpr (by simpa [Nat.mul_comm] using lb)
  refine ⟨by omega, ?_⟩
  have mx := Nat.mul_lt_mul_of_pos_left (dense.trans_le bound2) (show 0 < r by omega)
  have hi := Nat.mul_le_mul_left (r+1) rc
  have md := congrArg (fun x : ℕ => r*(r+1)*x) dec
  have δ : (r-1)*(r+1)*q < (r-1)*(r*m)+2*(r-1)*(r+1) := by
    have id1 := congrArg (fun k : ℕ => k*(r+1)*q) (show r-1+1=r by omega)
    have id2 := congrArg (fun k : ℕ => k*(r*m)) (show r-1+1=r by omega)
    have id3 := congrArg (fun k : ℕ => k*(r+1)) (show r-1+1=r by omega)
    nlinarith only [mx,hi,md,id1,id2,id3,hr,dec]
  have clear : (r+1)*q < r*m+2*(r+1) := Nat.lt_of_mul_lt_mul_left (by
    calc (r-1)*((r+1)*q) = (r-1)*(r+1)*q := by ring
         _ < (r-1)*(r*m)+2*(r-1)*(r+1) := δ
         _ = (r-1)*(r*m+2*(r+1)) := by ring)
  have hdiv := Nat.mod_add_div (r*m) (r+1)
  have hrem := Nat.mod_lt (r*m) (show 0<r+1 by omega)
  by_contra! fail
  have hf := Nat.mul_le_mul_left (r+1) (show r*m/(r+1)+3 ≤ q by omega)
  nlinarith only [hf,clear,hdiv,hrem]



lemma force_arity_shell {r m b a : ℕ} (hr : 3 ≤ r) (hm : (r+1)*r*r ≤ m)
    (dense : 2*m < (r+1)*b) (size : r*b ≤ a+r-2) :
    (r+1)*m ≤ r*a := by
  have factor : (r+1)*(r+1)+1 ≤ 2*r*r := by
    have := Nat.mul_le_mul_right r hr
    nlinarith only [this,hr]
  have big := Nat.mul_le_mul_right m factor
  have cap := Nat.mul_le_mul_left (r*r) dense.le
  have imageBound := Nat.mul_le_mul_left (r*(r+1)) (show r*b ≤ a+r by omega)
  apply Nat.le_of_mul_le_mul_left _ (by omega : 0<r+1)
  nlinarith only [big,cap,imageBound,hm]

/-- If the last m places contain more than 2m/(r+1) points then the desired
bound holds at every arity at least three. -/
theorem twice_terminal_bound (r : ℕ) (hr : 3 ≤ r) : ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → FullColumns.Free r A →
    2*m < (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card → A.card ≤ m+K := by
  classical
  obtain ⟨C, shell⟩ := OMA.Erdos13ManyLayers.shell_to_arity r hr
  refine ⟨C+(7*r+4)+(r+1)*((r+1)*r*r), ?_⟩
  intro m A sub free dense
  by_cases big : (r+1)*r*r ≤ m
  · let N := (r+1)*m
    let B := Ioc (r*m) N ∩ A
    let D := A.filter (fun a => r*a < N)
    let U := A.filter (fun a => ¬r*a < N)
    let E := range (6*r+1) ∪ Icc (r*m/(r+1)-r) (r*m/(r+1)+2)
    have eSize : E.card ≤ 7*r+4 := by
      have h := card_union_le (range (6*r+1)) (Icc (r*m/(r+1)-r) (r*m/(r+1)+2))
      simp only [card_range, Nat.card_Icc] at h
      change (range (6*r+1) ∪ Icc (r*m/(r+1)-r) (r*m/(r+1)+2)).card ≤ _
      omega
    have partition := A.card_filter_add_card_filter_not (fun a => r*a < N)
    change D.card + U.card = A.card at partition
    have uSize : U.card ≤ m+C := by
      have uFree : FullColumns.Free r U := fun x hx b hb => free _ (mem_filter.mp hx).1 b
        (fun i => (mem_filter.mp (hb i)).1)
      have c := shell N U (by
        intro x hx
        have h := mem_filter.mp hx
        have hi := mem_Icc.mp (sub h.1)
        exact ⟨hi.1, le_of_not_gt h.2, hi.2⟩) uFree
      change (r+1)*U.card ≤ (r+1)*m+C at c
      by_contra! high
      have hh := Nat.mul_le_mul_left (r+1) (show m+C+1 ≤ U.card by omega)
      nlinarith only [c,hh,Nat.zero_le (r*C),Nat.zero_le r]
    have hI : B ⊆ Ico (r*m+1) (r*m+1+m) := by
      intro x hx
      have h := mem_Ioc.mp (mem_inter.mp hx).1
      change r*m<x ∧ x≤(r+1)*m at h
      rw [Nat.add_mul, Nat.one_mul] at h
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    have early (a : ℕ) (ha : a ∈ D) : a ≤ r*m := by
      have h := (mem_filter.mp ha).2
      change r*a < (r+1)*m at h
      rw [Nat.add_mul, Nat.one_mul] at h
      have hma := Nat.mul_le_mul_right a hr
      have hmm := Nat.mul_le_mul_right m hr
      omega
    have hBT (a : ℕ) (ha : a ∈ D) : B ⊆ A.filter (fun x => a < x) := by
      intro x hx
      have h := mem_inter.mp hx
      exact mem_filter.mpr ⟨h.2,(early a ha).trans_lt (mem_Ioc.mp h.1).1⟩
    have hnon : B.Nonempty := by
      apply Finset.card_pos.mp
      by_contra! z
      change 2*m < (r+1)*B.card at dense
      have hz : B.card=0 := by omega
      simp [hz] at dense
    have get (a : ℕ) (ha : a ∈ D) : ∃ q : ℕ, 0 < q ∧ q ∣ a ∧
          (∀ x ∈ A, a < x → ¬ q ∣ x) ∧
          r*((A.filter (fun x => a < x)).image (fun x => x%q)).card ≤ q+r-2 :=
      OMA.Erdos13Cyclic.witness_of_free (by omega) free (fun x hx => (mem_Icc.mp (sub hx)).1)
        a (mem_filter.mp ha).1 (hnon.mono (hBT a ha))
    choose! f fpos fdvd fonly fcard using get
    have mapE (a : ℕ) (ha : a ∈ D) : f a ∈ E := by
      let q := f a
      let R := B.image (fun x => x%q)
      have c := card_le_card (image_subset_image (f := fun x => x%q) (hBT a ha))
      have he : r*R.card ≤ q+r-2 := (Nat.mul_le_mul_left r c).trans (fcard a ha)
      have qpos : 0<q := fpos a ha
      by_cases inM : q ≤ m
      · have rem := Nat.mod_add_div m q
        have dec : m/q*q + m%q = m := by simpa only [Nat.mul_comm,Nat.add_comm] using rem
        have incl : B ⊆ Ico (r*m+1) (r*m+1+(m/q*q + m%q)) := by simpa only [dec] using hI
        have bcap := count_by_period q (m/q) (m%q) (Nat.mod_lt _ qpos).le R (r*m+1) B incl
          (fun x hx => mem_image_of_mem _ hx)
        rcases twice_period_obstruction hr qpos inM he dense bcap with h | h
        · exact mem_union_left _ (mem_range.mpr (by omega : q < 6*r+1))
        · exact mem_union_right _ (mem_Icc.mpr h)
      · have inj : (B : Set ℕ).InjOn (fun x => x%q) := by
          apply (Nat.mod_injOn_Ico (r*m+1) q).mono
          intro x hx
          have h := mem_Ico.mp (hI hx)
          exact mem_Ico.mpr ⟨h.1,by omega⟩
        have eq : R.card = B.card := card_image_of_injOn inj
        rw [eq] at he
        have qa := Nat.le_of_dvd (mem_Icc.mp (sub (mem_filter.mp ha).1)).1 (fdvd a ha)
        change q ≤ a at qa
        have bound := force_arity_shell hr big dense (he.trans (by omega : q+r-2≤a+r-2))
        exact False.elim ((not_lt_of_ge bound) (mem_filter.mp ha).2)
    have dSize : D.card ≤ E.card := by
      apply card_le_card_of_injOn f mapE
      intro a ha b hb heq
      rcases lt_trichotomy a b with h | h | h
      · exact False.elim (fonly a ha b (mem_filter.mp hb).1 h (heq.symm ▸ fdvd b hb))
      · exact h
      · exact False.elim (fonly b hb a (mem_filter.mp ha).1 h (heq ▸ fdvd a ha))
    omega
  · have c := card_le_card sub
    simp only [Nat.card_Icc, Nat.add_one_sub_one] at c
    have h := Nat.mul_le_mul_left (r+1) (show m ≤ (r+1)*r*r by omega)
    omega

end Erdos13HalfOccupied

end


section

/-! Bounds within arithmetic progressions using cyclic quotients of a least good element. -/

namespace Erdos13ReducedProgression
open Finset OMA.Erdos13UpperShell

lemma progression_numeric {r d a N L q t s c b : ℕ}
    (hr : 3 ≤ r) (hd : 2 ≤ d) (hq : r+2 ≤ q)
    (available : a+d*L ≤ N) (base : q ≤ a) (periods : t*q+s = L)
    (res : r*c ≤ q+r-2) (cap : b ≤ t*c+min s c) :
    (r+d)*b ≤ N+r-2 := by
  have capacity : r*c ≤ q+(r-2) := by omega
  have two : 2*c+(r-2) ≤ q := by
    by_cases hc : c ≤ 2
    · omega
    have h := Nat.mul_le_mul_right (r-2) (show 3 ≤ c by omega)
    have hr₀ : r-2+2 = r := by omega
    have id := congrArg (fun x => x*c) hr₀
    nlinarith only [capacity,h,id]
  have gap : c ≤ q := by omega
  have gap2 := Nat.mul_le_mul_right (q-c) hd
  have subtract := Nat.sub_add_cancel gap
  have pay : q+(r-2) ≤ d*(q-c) := by omega
  have hcount : b + t*(q-c) ≤ L := by
    have z := congrArg (fun x : ℕ => t*x) subtract
    have ms := min_le_left s c
    nlinarith only [cap,periods,z,ms]
  have hprice := Nat.mul_le_mul_left (t+1) capacity
  have hinc := Nat.mul_le_mul_left r (show b ≤ (t+1)*c by
    have := min_le_right s c
    rw [Nat.add_mul]
    omega)
  have charge := Nat.mul_le_mul_left t pay
  have uses := Nat.mul_le_mul_left d hcount
  have dec : r-2+2=r := by omega
  have bound : (r+d)*b + 2 ≤ N+r := by
    nlinarith only [hinc,hprice,charge,uses,available,base,dec]
  omega

lemma progression_tail {r d a N q : ℕ}
    (hr : 3 ≤ r) (hd : 2 ≤ d) (hq : r+2 ≤ q)
    (qa : q ∣ a) (ha : 0 < a) (han : a ≤ N) (cop : a.Coprime d)
    (B : Finset ℕ) (sub : B ⊆ Ioc a N) (cong : ∀ b ∈ B, b ≡ a [MOD d])
    (quot : r*(B.image (·%q)).card ≤ q+r-2) : (r+d)*B.card ≤ N+r-2 := by
  classical
  let L := (N-a)/d
  let T := (Icc 1 L).filter (fun j => a+d*j ∈ B)
  have rep (b : ℕ) (hb : b ∈ B) : a + d*((b-a)/d) = b := by
    have hx := mem_Ioc.mp (sub hb)
    have dv : d ∣ b-a := (Nat.modEq_iff_dvd' hx.1.le).mp (cong b hb).symm
    rw [Nat.mul_div_cancel' dv]
    omega
  have hc : B.card ≤ T.card := by
    apply card_le_card_of_injOn (fun x => (x-a)/d)
    · intro x hx
      have hi := mem_Ioc.mp (sub hx)
      have eqx := rep x hx
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_,Nat.div_le_div_right (Nat.sub_le_sub_right hi.2 a)⟩,?_⟩
      · change 1 ≤ (x-a)/d
        apply Nat.pos_of_ne_zero
        intro hz
        rw [hz, Nat.mul_zero, Nat.add_zero] at eqx
        omega
      · change a + d * ((x-a)/d) ∈ B
        rwa [eqx]
    · intro x hx y hy he
      have ex := rep x hx
      simpa only [he,rep y hy] using ex.symm
  let R := T.image (·%q)
  have image : R.card ≤ (B.image (·%q)).card := by
    apply card_le_card_of_injOn (fun j => (a+d*j)%q)
    · intro x hx
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
      have eqmod : a+d*(j%q) ≡ a+d*j [MOD q] := ((Nat.mod_modEq j q).mul_left d).add_left a
      change (a+d*(j%q))%q ∈ _
      rw [show (a+d*(j%q))%q=(a+d*j)%q from eqmod]
      exact mem_image_of_mem _ (mem_filter.mp hj).2
    · intro x hx y hy he
      have eqmod : a+d*x ≡ a+d*y [MOD q] := he
      have same := Nat.ModEq.cancel_left_of_coprime (cop.of_dvd_left qa) (eqmod.add_left_cancel' a)
      obtain ⟨j,_,rfl⟩ := mem_image.mp hx
      obtain ⟨k,_,rfl⟩ := mem_image.mp hy
      simpa [Nat.ModEq] using same
  have res := (Nat.mul_le_mul_left r image).trans quot
  have periods : L/q*q+L%q=L := by simpa only [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div L q
  have cap := Erdos13HalfOccupied.count_by_period q (L/q) (L%q) (Nat.mod_lt _ (by omega)).le R 1 T
    (by
      rw [periods]
      intro x hx
      have h := mem_Icc.mp (mem_filter.mp hx).1
      exact mem_Ico.mpr ⟨h.1,by omega⟩)
    (fun j hj => mem_image_of_mem _ hj)
  have available := Nat.mul_div_le (N-a) d
  exact progression_numeric hr hd hq (by dsimp [L]; omega) (Nat.le_of_dvd ha qa) periods res (hc.trans cap)

/-- Every reduced residue class modulo d ≥ 2 admits a sharp density of at
most 1/(r+d). The additive error is uniform in the modulus d. -/
theorem reduced_progression_bound {r d c N : ℕ} (hr : 3 ≤ r) (hd : 2 ≤ d) (cop : c.Coprime d)
    (A : Finset ℕ) (within : A ⊆ Icc 1 N) (cong : ∀ a ∈ A, a ≡ c [MOD d])
    (free : FullColumns.Free r A) : A.card ≤ N/(r+d)+r+3 := by
  have pos (a) (ha : a ∈ A) := (mem_Icc.mp (within ha)).1
  have h := select_large_quotient (r := r) (N := (r+1)*(N/(r+d)+1)) (L := r+1) (K := 0)
    A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos) (by
      intro a ha q hq qa quot
      let B := A.filter (a < ·)
      have hB : B ⊆ Ioc a N := by
        intro x hx
        have h := mem_filter.mp hx
        exact mem_Ioc.mpr ⟨h.2,(mem_Icc.mp (within h.1)).2⟩
      have acop : a.Coprime d := by
        rw [Nat.coprime_iff_gcd_eq_one,(cong a ha).gcd_eq]
        exact cop
      have tail := progression_tail hr hd (by omega) qa (pos a ha) (mem_Icc.mp (within ha)).2 acop
        B hB (fun x hx => (cong x (mem_filter.mp hx).1).trans (cong a ha).symm) quot
      have bt : B.card ≤ N/(r+d)+1 := by
        by_contra! hh
        have t := Nat.mul_le_mul_left (r+d) (show N/(r+d)+2 ≤ B.card by omega)
        have rem := Nat.mod_add_div N (r+d)
        have hl := Nat.mod_lt N (show 0< r+d by omega)
        have linear : (r+d)*B.card ≤ N+r := by omega
        nlinarith only [t,linear,rem,hl,hd]
      simpa using Nat.mul_le_mul_left (r+1) bt)
  have final : (r+1)*A.card ≤ (r+1)*(N/(r+d)+r+3) := by
    convert h using 1
    ring
  exact Nat.le_of_mul_le_mul_left final (by omega)

end Erdos13ReducedProgression

end


section

/-! Necessary conditions for a sparse counterexample. -/
namespace Erdos13SparseConditions

open Finset

/-- A strict density saving on the complement forces a positive density
in the specified subset. -/
lemma count_from_complement {s m K D l u n : ℕ} (part : l+u=n)
    (bound : (s+1)*u ≤ s*m+D) (excess : m+K<n) (room : D ≤ K) :
    m < (s+1)*l := by
  have enough := Nat.mul_lt_mul_of_pos_left excess (show 0<s+1 by omega)
  have eqn := congrArg (fun x : ℕ => (s+1)*x) part
  nlinarith only [enough,eqn,bound,room,Nat.zero_le (s*K)]

/-- Beyond a constant depending only on r, every remaining counterexample
has a sparse terminal block and positive proportions of small denominators,
multiples of three, and even numbers. -/
theorem hard_core_conditions (r : ℕ) (hr : 3 ≤ r) : ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → FullColumns.Free r A → m+K < A.card →
    2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
    (r+1)*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ 2*m ∧
    m < (24*r*r*(r+1)+1)*(A.filter (fun a => r*a<(r+1)*m)).card ∧
    m < (3*r+4)*(A.filter (fun a => 3∣a)).card ∧
    m < (r+2)*(A.filter (fun a => 2∣a)).card := by
  classical
  obtain ⟨C, stable⟩ := OMA.Erdos13ManyLayers.sparse_top_stability r hr
  obtain ⟨T, terminal⟩ := Erdos13HalfOccupied.twice_terminal_bound r hr
  let D₃ := 6*r+6+(3*r+4)*(32*r+1)
  let D₂ := (r+2)*(r+3)
  let K := T+C+D₃+D₂
  refine ⟨K,?_⟩
  intro m A sub free large sparse
  let N := (r+1)*m
  have onSub (S : Finset ℕ) (inc : S ⊆ A) : FullColumns.Free r S :=
    fun a ha b hb => free a (inc ha) b (fun i => inc (hb i))
  constructor
  · by_contra! dense
    have h := terminal m A sub free dense
    dsimp [K] at large
    omega
  constructor
  · let S := A.filter (fun a => ¬r*a<N)
    have inc : S ⊆ A := filter_subset _ _
    have band (a : ℕ) (ha : a ∈ S) : 0<a ∧ N≤r*a ∧ a≤N := by
      have h := mem_filter.mp ha
      have i := mem_Icc.mp (sub h.1)
      exact ⟨i.1,le_of_not_gt h.2,i.2⟩
    have sp := (Nat.mul_le_mul_left 2 (card_le_card
      (inter_subset_inter (Subset.rfl (s := Ioc (r*m) N)) inc))).trans sparse
    have s := stable m S band (onSub S inc) sp
    have s' : (24*r*r*(r+1)+1)*S.card ≤ 24*r*r*(r+1)*m+C := by
      simpa only [Nat.mul_assoc] using s
    exact count_from_complement (A.card_filter_add_card_filter_not (fun a => r*a<N)) s' large
      (by dsimp [K]; omega)
  constructor
  · let S := A.filter (fun a => ¬3∣a)
    have inc : S ⊆ A := filter_subset _ _
    have ratio := Erdos13NoThreeMultiples.no_three_multiples_gap r hr N S (inc.trans sub)
      (fun a ha => (mem_filter.mp ha).2) (onSub S inc)
    have scale := Nat.mul_le_mul_left (3*r+4) ratio
    have floor := Nat.mul_div_le (3*N+6*r+6) (3*r+4)
    have s : (3*(r+1)+1)*S.card ≤ 3*(r+1)*m+D₃ := by
      dsimp [D₃,N] at *
      nlinarith only [scale,floor]
    have h := count_from_complement (A.card_filter_add_card_filter_not (fun a => 3∣a))
      s large (by dsimp [K]; omega)
    simpa only [show 3*(r+1)+1=3*r+4 by omega] using h
  · let S := A.filter (fun a => ¬2∣a)
    have inc : S ⊆ A := filter_subset _ _
    have odd (a : ℕ) (ha : a ∈ S) : a ≡ 1 [MOD 2] := by
      have no : ¬2∣a := (mem_filter.mp ha).2
      have hm : a%2≠0 := fun h => no (Nat.dvd_of_mod_eq_zero h)
      change a%2=1
      omega
    have ratio := Erdos13ReducedProgression.reduced_progression_bound (r := r)
      (d := 2) (c := 1) hr (by decide) (by decide) S (inc.trans sub) odd (onSub S inc)
    have scale := Nat.mul_le_mul_left (r+2) ratio
    have floor := Nat.mul_div_le N (r+2)
    have s : ((r+1)+1)*S.card ≤ (r+1)*m+D₂ := by
      dsimp [D₂,N] at *
      nlinarith only [scale,floor]
    exact count_from_complement (A.card_filter_add_card_filter_not (fun a => 2∣a)) s large
      (by dsimp [K]; omega)

end Erdos13SparseConditions

end

theorem OMA.solution : OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1.H2 := by
  intro r hr
  obtain ⟨K, bound⟩ := Erdos13SparseConditions.hard_core_conditions r hr
  exact ⟨K, fun m A sub excess sparse free => bound m A sub free excess sparse⟩
