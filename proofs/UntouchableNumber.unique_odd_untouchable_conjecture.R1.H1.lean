import OMAReductions.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1
import Mathlib

/-! Step H1: no natural number has proper divisors summing to 5. A composite n has a proper
divisor d with d * d at least n, so its proper divisors sum to at least 1 + d, which bounds n
by 16, and the numbers up to 16 are checked directly. -/

-- Step UntouchableNumber.unique_odd_untouchable_conjecture.R1.H1: hypothesis H1 of reduction UntouchableNumber.unique_odd_untouchable_conjecture.R1
-- Credit: @ivillar

theorem OMA.solution : OMA.R_UntouchableNumber_unique_odd_untouchable_conjecture_R1.H1 := by
  rintro ⟨n, hsum⟩
  by_cases hn : n ≤ 16
  · interval_cases n <;> revert hsum <;> decide
  · have hn2 : 2 ≤ n := by omega
    by_cases hp : n.Prime
    · rw [Nat.Prime.sum_properDivisors hp] at hsum
      omega
    · obtain ⟨d, hd1, hd2, hd3⟩ := Nat.exists_dvd_of_not_prime2 hn2 hp
      have hq : n / d ∣ n := Nat.div_dvd_of_dvd hd1
      have hqd : n / d * d = n := Nat.div_mul_cancel hd1
      have hqlt : n / d < n := Nat.div_lt_self (by omega) (by omega)
      have h1 : (1 : ℕ) ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨one_dvd _, by omega⟩
      have hdm : d ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hd1, hd3⟩
      have hqm : n / d ∈ n.properDivisors := Nat.mem_properDivisors.mpr ⟨hq, hqlt⟩
      have hd5 : d ≤ 4 := by
        have h2 : ({1, d} : Finset ℕ) ⊆ n.properDivisors := by
          intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact h1
          · rw [Finset.mem_singleton.mp ht]
            exact hdm
        have h3 := Finset.sum_le_sum_of_subset (f := fun t => t) h2
        rw [Finset.sum_pair (by omega)] at h3
        omega
      have hq5 : n / d ≤ 4 := by
        have hq2 : 2 ≤ n / d := by
          by_contra hcon
          have : n / d * d ≤ 1 * d := Nat.mul_le_mul_right d (by omega)
          omega
        have h2 : ({1, n / d} : Finset ℕ) ⊆ n.properDivisors := by
          intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact h1
          · rw [Finset.mem_singleton.mp ht]
            exact hqm
        have h3 := Finset.sum_le_sum_of_subset (f := fun t => t) h2
        rw [Finset.sum_pair (by omega)] at h3
        omega
      have : n / d * d ≤ 4 * 4 := Nat.mul_le_mul hq5 hd5
      omega
