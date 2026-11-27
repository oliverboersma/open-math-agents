import FormalConjectures.ErdosProblems.«424»
import Mathlib

/-!
Membership in Hofstadter's set has a finite divisor test using only
smaller arguments. The density problem separates the positive lower
bound of Korsky, arXiv:2608.07910, from a Cauchy bound on the proportions.
-/

open Set Filter
open Erdos424
open scoped Topology

namespace OMA.R_Erdos424_erdos_424_variants_exact_density_R1

/-- Eventual positivity of all sufficiently long initial proportions. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ generatedSet.partialDensity univ n

/-- The normalized counts of generated multiples of three are Cauchy. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    |(generatedSet ∩ {a | a%3=0}).partialDensity univ m -
      (generatedSet ∩ {a | a%3=0}).partialDensity univ n| < ε

/-- The normalized counts of generated integers congruent to two are Cauchy. -/
def H3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    |(generatedSet ∩ {a | a%3=2}).partialDensity univ m -
      (generatedSet ∩ {a | a%3=2}).partialDensity univ n| < ε

section Proof

private theorem generation_mono : Monotone sequenceSet := by
  apply monotone_nat_of_le_succ
  intro i
  exact Set.subset_union_left

private theorem generated_two : 2 ∈ generatedSet := by
  apply mem_iUnion.mpr
  exact ⟨0,by simp [sequenceSet]⟩

private theorem generated_three : 3 ∈ generatedSet := by
  apply mem_iUnion.mpr
  exact ⟨0,by simp [sequenceSet]⟩

private theorem generated_closed {a b : ℕ} (ha : a ∈ generatedSet)
    (hb : b ∈ generatedSet) (hne : a ≠ b) : a*b-1 ∈ generatedSet := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp ha
  obtain ⟨j,hj⟩ := mem_iUnion.mp hb
  exact mem_iUnion.mpr ⟨max i j+1, Or.inr
    ⟨a,b,generation_mono (le_max_left _ _) hi,generation_mono (le_max_right _ _) hj,hne,rfl⟩⟩

private theorem generation_constraints (i : ℕ) :
    ∀ n ∈ sequenceSet i, 2 ≤ n ∧ n%3 ≠ 1 := by
  induction i with
  | zero =>
    intro n hn
    simp only [sequenceSet,mem_insert_iff,mem_singleton_iff] at hn
    rcases hn with rfl|rfl <;> decide
  | succ i ih =>
    intro n hn
    rcases hn with hn | ⟨a,b,ha,hb,_,hn⟩
    · exact ih n hn
    · have ha' := ih a ha
      have hb' := ih b hb
      have hab : 4 ≤ a*b := Nat.mul_le_mul ha'.1 hb'.1
      have hA : a%3 = 0 ∨ a%3 = 2 := by omega
      have hB : b%3 = 0 ∨ b%3 = 2 := by omega
      have hAB : (a*b)%3 ≠ 2 := by
        rw [Nat.mul_mod]
        rcases hA with hA|hA <;> rcases hB with hB|hB <;> simp [hA,hB]
      omega

theorem generated_constraints {n : ℕ} (hn : n ∈ generatedSet) :
    2 ≤ n ∧ n%3 ≠ 1 := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hn
  exact generation_constraints i n hi

/-- Apart from the seeds, membership is equivalent to a factor pair for
n+1 whose two distinct factors have already been generated. -/
theorem generated_iff_smaller_factors (n : ℕ) :
    n ∈ generatedSet ↔ n = 2 ∨ n = 3 ∨
      ∃ a b : ℕ, a ∈ generatedSet ∧ b ∈ generatedSet ∧ a < b ∧ b < n ∧ n+1 = a*b := by
  constructor
  · intro hn
    obtain ⟨i,hi⟩ := mem_iUnion.mp hn
    induction i with
    | zero =>
      have h : n = 2 ∨ n = 3 := by
        simpa only [sequenceSet,mem_insert_iff,mem_singleton_iff] using hi
      exact h.elim Or.inl (fun he => Or.inr (Or.inl he))
    | succ i ih =>
      rcases hi with h | ⟨a,b,ha,hb,hne,he⟩
      · exact ih h
      · have haG : a ∈ generatedSet := mem_iUnion.mpr ⟨i,ha⟩
        have hbG : b ∈ generatedSet := mem_iUnion.mpr ⟨i,hb⟩
        have ha2 := (generated_constraints haG).1
        have hb2 := (generated_constraints hbG).1
        rcases lt_or_gt_of_ne hne with hab|hab
        · have hMul : 2*b ≤ a*b := Nat.mul_le_mul_right b ha2
          exact Or.inr (Or.inr ⟨a,b,haG,hbG,hab,by omega,by omega⟩)
        · have hMul : 2*a ≤ a*b := by
            simpa only [Nat.mul_comm 2 a] using Nat.mul_le_mul_left a hb2
          exact Or.inr (Or.inr ⟨b,a,hbG,haG,hab,by omega,by rw [mul_comm b a]; omega⟩)
  · rintro (rfl|rfl|⟨a,b,ha,hb,hab,_,he⟩)
    · exact generated_two
    · exact generated_three
    · have h : n = a*b-1 := by omega
      rw [h]
      exact generated_closed ha hb (ne_of_lt hab)

private theorem split_partial_density (n : ℕ) :
    generatedSet.partialDensity univ n =
      (generatedSet ∩ {a | a%3=0}).partialDensity univ n +
        (generatedSet ∩ {a | a%3=2}).partialDensity univ n := by
  let L : Set ℕ := (generatedSet ∩ {a | a%3=0}) ∩ Iio n
  let R : Set ℕ := (generatedSet ∩ {a | a%3=2}) ∩ Iio n
  have hUnion : L ∪ R = generatedSet ∩ Iio n := by
    ext a
    constructor
    · rintro (h|h) <;> exact ⟨h.1.1,h.2⟩
    · rintro ⟨ha,hn⟩
      have hc := (generated_constraints ha).2
      have hm : a%3=0 ∨ a%3=2 := by omega
      exact hm.elim (fun h => Or.inl ⟨⟨ha,h⟩,hn⟩) (fun h => Or.inr ⟨⟨ha,h⟩,hn⟩)
  have hDis : Disjoint L R := by
    rw [Set.disjoint_left]
    intro a ha hb
    have h0 : a%3=0 := ha.1.2
    have h2 : a%3=2 := hb.1.2
    omega
  have hL : L.Finite := (Set.finite_Iio n).subset Set.inter_subset_right
  have hR : R.Finite := (Set.finite_Iio n).subset Set.inter_subset_right
  simp only [Set.partialDensity,inter_univ,univ_inter]
  change ((generatedSet ∩ Iio n).ncard:ℝ) / (Iio n).ncard =
    (L.ncard:ℝ)/(Iio n).ncard + (R.ncard:ℝ)/(Iio n).ncard
  rw [← hUnion,Set.ncard_union_eq hDis hL hR,Nat.cast_add,add_div]

private theorem proportion_tends_of_cauchy (S : Set ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      |S.partialDensity univ m - S.partialDensity univ n| < ε) :
    ∃ α : ℝ, S.HasDensity α := by
  have hSeq : CauchySeq (S.partialDensity univ) := by
    refine Metric.cauchySeq_iff.mpr ?_
    intro ε hε
    obtain ⟨N,hN⟩ := h ε hε
    exact ⟨N,fun m hm n hn => by simpa [Real.dist_eq] using hN m hm n hn⟩
  exact cauchySeq_tendsto_of_complete hSeq

theorem main : H1 → H2 → H3 → type_of% @Erdos424.erdos_424.variants.exact_density := by
  intro hPos hZero hTwo
  obtain ⟨c,hc,hCount⟩ := hPos
  obtain ⟨α,hα⟩ := proportion_tends_of_cauchy (generatedSet ∩ {a | a%3=0}) hZero
  obtain ⟨β,hβ⟩ := proportion_tends_of_cauchy (generatedSet ∩ {a | a%3=2}) hTwo
  have hL : generatedSet.HasDensity (α+β) := by
    unfold Set.HasDensity at hα hβ ⊢
    simp only [split_partial_density]
    exact hα.add hβ
  exact ⟨α+β,hc.trans_le (ge_of_tendsto hL hCount),hL⟩

end Proof

end OMA.R_Erdos424_erdos_424_variants_exact_density_R1
