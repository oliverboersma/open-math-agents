import Mathlib

/-!
# A088982: Primes between consecutive prime-indexed primes

Source: https://oeis.org/A088982
Credit: @AkiRA-COM-FP

Formalizes the OEIS A088982 conjecture: for every integer `x > 1`, there is at least
one prime strictly between `prime(prime(x))` and `prime(prime(x + 1))`.
-/

namespace OMA.S_oeis_a088982

/-- The `k`-th prime number (1-indexed: `prime 1 = 2`, `prime 2 = 3`, ...). -/
noncomputable def prime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- For every `x > 1`, there exists a prime strictly between
`prime(prime(x))` and `prime(prime(x + 1))`. -/
theorem main :
    ∀ x : ℕ, 1 < x →
      ∃ p : ℕ, Nat.Prime p ∧
        prime (prime x) < p ∧ p < prime (prime (x + 1)) := by
  sorry

end OMA.S_oeis_a088982
