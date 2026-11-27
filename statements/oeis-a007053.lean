import Mathlib

/-!
# Perfect powers among the prime counts at powers of two

OEIS A007053 counts the primes at most two to the power n. Its term at index
three is four. Zhi-Wei Sun conjectured on September 30, 2015, that no later
term is a perfect power with base and exponent both greater than one.

Source: https://oeis.org/A007053
Lean statement: @Halldon
-/

namespace OMA.S_oeis_a007053

theorem main : ∀ n x m : ℕ, 3 < n → 1 < x → 1 < m →
    Nat.primeCounting (2 ^ n) ≠ x ^ m := by
  sorry

end OMA.S_oeis_a007053
