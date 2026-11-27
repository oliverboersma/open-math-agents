import Mathlib

/-!
# OEIS A001043: Unit fractions from sums of consecutive primes

Source: https://oeis.org/A001043
Credit: @gblacher2

Zhi-Wei Sun's conjecture concerns finite sums of distinct unit fractions
whose denominators are each the sum of a block of consecutive primes.
-/

namespace OMA.S_oeis_a001043

/-- The sum of `m` primes starting at index `k`, with the first prime at index zero. -/
noncomputable def primeBlockSum (m k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, Nat.nth Nat.Prime (k + i)

/-- A finite set of positive denominators gives distinct unit fractions. -/
def HasPrimeBlockExpansion (m : ℕ) (q : ℚ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 0 < d ∧ ∃ k : ℕ, d = primeBlockSum m k) ∧
      (∑ d ∈ D, (1 : ℚ) / (d : ℚ)) = q

theorem main :
    (∀ m : ℕ, 0 < m → Even m → ∀ q : ℚ, 0 < q → HasPrimeBlockExpansion m q) ∧
      (∀ m : ℕ, 1 < m → Odd m → ∀ c d : ℕ, 0 < c → 0 < d → Odd d →
        HasPrimeBlockExpansion m ((c : ℚ) / (d : ℚ))) := by
  sorry

end OMA.S_oeis_a001043
