import OMAReductions.R_OeisA238585_conjecture_1_R1
import Mathlib

-- Step OeisA238585.conjecture_1.R1.H1: hypothesis H1 of reduction OeisA238585.conjecture_1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! The divisors of 6 are 1, 2, 3 and 6. The first three values are the catalogue tests a_1, a_2
and a_3. For a 6 the three candidate sums 153, 169 and 265 are composite. -/

theorem OMA.solution : OMA.R_OeisA238585_conjecture_1_R1.H1 := by
  intro n hn
  have h6 : n ≤ 6 := Nat.le_of_dvd (by norm_num) hn
  interval_cases n
  · exact absurd hn (by norm_num)
  · exact OeisA238585.a_1
  · exact OeisA238585.a_2
  · exact OeisA238585.a_3
  · exact absurd hn (by norm_num)
  · exact absurd hn (by norm_num)
  · have h5 : Nat.nth Nat.Prime 5 = 13 := by
      have h1 : Nat.count Nat.Prime 13 = 5 := by decide
      rw [← h1]
      exact Nat.nth_count (by norm_num)
    have hIco : Finset.Ico 1 6 = {1, 2, 3, 4, 5} := by decide
    simp only [OeisA238585.a, hIco, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, Finset.sum_singleton,
      Nat.reduceSub, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five,
      Nat.nth_prime_four_eq_eleven, h5]
    decide +kernel
