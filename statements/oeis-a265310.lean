import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Fixed points of the factorial divisibility sequence A265310

Source: https://oeis.org/A265310 (OEIS Foundation, CC BY-SA 4.0).

For positive n, a(n) is the least positive k for which the product of all
positive divisors of n divides k!. The conjecture in the entry states
that a(n) = n exactly for primes, twice primes, and the numbers 1, 8, 9.
The least-positive-index condition is expressed by IsLeast.
-/

namespace OMA.S_oeis_a265310

def divisorProduct (n : ℕ) : ℕ := ∏ d ∈ n.divisors, d

theorem main : ∀ n : ℕ, 0 < n →
    (IsLeast {k : ℕ | 0 < k ∧ divisorProduct n ∣ k.factorial} n ↔
      n.Prime ∨ (∃ p : ℕ, p.Prime ∧ n = 2 * p) ∨ n = 1 ∨ n = 8 ∨ n = 9) := by
  sorry

end OMA.S_oeis_a265310
