import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Eventual residue of a divisor sum of factorial quotients

This is Peter Bala's conjecture that for each k at least three the residue
of A121860(n) is exactly two for all sufficiently large n. The sum runs
over all positive divisors, including both endpoints.

Source: https://oeis.org/A121860
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a121860

def term (n d : ℕ) := n.factorial / (d.factorial*(n/d).factorial)

def value (n : ℕ) := ∑ d ∈ n.divisors, term n d

theorem main : ∀ k : ℕ, 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → value n % k = 2 := by
  sorry

end OMA.S_oeis_a121860
