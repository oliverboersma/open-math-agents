import FormalConjectures.ErdosProblems.«1210»
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic

/-!
Primes beyond twice the starting point contribute an ordinary prime-reciprocal
sum with a bounded error. Closer primes give positive offsets that miss a
residue modulo every prime up to the interval length.
-/

namespace OMA.R_Erdos1210_erdos_1210_variants_er80_correction_R1

open Finset

def H1 : Prop :=
  ∀ n m : ℕ, 2 * n ≤ m →
    (∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / ((q : ℝ) - n)) ≤
      (∑ q ∈ (Ico n (m - n)).filter Nat.Prime, 1 / (q : ℝ)) + 2

def H2 : Prop :=
  ∃ C : ℝ, ∀ D : ℕ, ∀ A : Finset ℕ,
    A ⊆ Icc 1 D →
    (∀ p : ℕ, p.Prime → p ≤ D → ∃ r : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ r) →
    (∑ a ∈ A, 1 / (a : ℝ)) ≤ (∑ p ∈ (range D).filter Nat.Prime, 1 / (p : ℝ)) + C

section Proof

private theorem short_bound (C : ℝ)
    (hC : ∀ D : ℕ, ∀ A : Finset ℕ,
      A ⊆ Icc 1 D →
      (∀ p : ℕ, p.Prime → p ≤ D → ∃ r : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ r) →
      (∑ a ∈ A, 1 / (a : ℝ)) ≤ (∑ p ∈ (range D).filter Nat.Prime, 1 / (p : ℝ)) + C)
    (n D : ℕ) (hD : D ≤ n) :
    (∑ q ∈ (Ioc n (n + D)).filter Nat.Prime, 1 / ((q : ℝ) - n)) ≤
      (∑ p ∈ (range D).filter Nat.Prime, 1 / (p : ℝ)) + C := by
  let P := (Ioc n (n + D)).filter Nat.Prime
  let A := P.image (· - n)
  have hAI : A ⊆ Icc 1 D := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ha
    obtain ⟨hnq, hqD⟩ := mem_Ioc.mp (mem_filter.mp hq).1
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hAV (p : ℕ) (hp : p.Prime) (hpD : p ≤ D) :
      ∃ r : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ r := by
    refine ⟨- (n : ZMod p), ?_⟩
    intro a ha heq
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ha
    obtain ⟨hqI, hprime⟩ := mem_filter.mp hq
    have hnq := (mem_Ioc.mp hqI).1
    rw [Nat.cast_sub hnq.le] at heq
    have hq0 : (q : ZMod p) = 0 := by
      calc
        (q : ZMod p) = ((q : ZMod p) - n) + n := (sub_add_cancel _ _).symm
        _ = 0 := by simp [heq]
    have hdiv := (ZMod.natCast_eq_zero_iff q p).mp hq0
    have he := (hprime.dvd_iff_eq hp.ne_one).mp hdiv
    omega
  have hsum : (∑ a ∈ A, 1 / (a : ℝ)) = ∑ q ∈ P, 1 / ((q : ℝ) - n) := by
    have hInj : Set.InjOn (fun q : ℕ => q - n) (P : Set ℕ) := by
      intro x hx y hy he
      have hxs := (mem_Ioc.mp (mem_filter.mp (mem_coe.mp hx)).1).1
      have hys := (mem_Ioc.mp (mem_filter.mp (mem_coe.mp hy)).1).1
      change x - n = y - n at he
      omega
    unfold A
    rw [sum_image hInj]
    apply sum_congr rfl
    intro q hq
    have hnq := (mem_Ioc.mp (mem_filter.mp hq).1).1
    rw [Nat.cast_sub hnq.le]
  rw [← hsum]
  exact hC D A hAI hAV

private theorem sum_prime_union (s t : Finset ℕ) (hd : Disjoint s t) (f : ℕ → ℝ) :
    (∑ q ∈ s.filter Nat.Prime, f q) + (∑ q ∈ t.filter Nat.Prime, f q) =
      ∑ q ∈ (s ∪ t).filter Nat.Prime, f q := by
  rw [filter_union, sum_union (Disjoint.mono (filter_subset _ _) (filter_subset _ _) hd)]

theorem main : H1 → H2 → type_of% @Erdos1210.erdos_1210.variants.er80_correction := by
  intro tail admissible
  obtain ⟨C, hC⟩ := admissible
  refine ⟨C + 3, ?_⟩
  intro n m hnm
  have hfilter (S : Finset ℕ) :
      S.filter (_root_.Prime : ℕ → Prop) = S.filter Nat.Prime := by
    ext p
    simp [Nat.prime_iff]
  rw [hfilter, hfilter]
  by_cases h : m ≤ 2 * n
  · have hnear := short_bound C hC n (m - n) (by omega)
    rw [show n + (m - n) = m by omega] at hnear
    linarith
  have htwo : 2 * n ≤ m := by omega
  have hnear := short_bound C hC n n le_rfl
  rw [show n + n = 2 * n by omega] at hnear
  have htail := tail n m htwo
  have hsum := sum_prime_union (Ioc n (2 * n)) (Ioc (2 * n) m)
    (Ioc_disjoint_Ioc_of_le le_rfl) (fun q => 1 / ((q : ℝ) - n))
  rw [Ioc_union_Ioc_eq_Ioc (by omega) htwo] at hsum
  have hband : Disjoint (range n) (Ico n (m - n)) := by
    apply disjoint_left.mpr
    exact fun p hp hq => (not_le_of_gt (mem_range.mp hp)) (mem_Ico.mp hq).1
  have hrange : range n ∪ Ico n (m - n) = range (m - n) := by
    ext p
    simp only [mem_union, mem_range, mem_Ico]
    omega
  have hprime := sum_prime_union (range n) (Ico n (m - n)) hband (fun q => 1 / (q : ℝ))
  rw [hrange] at hprime
  linarith

end Proof

end OMA.R_Erdos1210_erdos_1210_variants_er80_correction_R1
