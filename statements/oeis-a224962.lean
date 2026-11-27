import Mathlib

/-!
# A224962: a(n) = number of primes of the form p*q+(p+q) where p = prime(n) and q is any prime < p.

Source: https://oeis.org/A224962
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n) > 0 for all n > 1 (Dmitry Kamenetsky, Jul 18 2019).

Conventions: offset 1, so `prime(n)` with `n > 1` ranges over the primes `p ≥ 3`.
-/

namespace OMA.S_oeis_a224962

/-- For every prime `p ≥ 3` there is a prime `q < p` such that `p*q + (p + q)` is prime. -/
theorem main : ∀ p : ℕ, p.Prime → 3 ≤ p →
    ∃ q : ℕ, q.Prime ∧ q < p ∧ (p * q + (p + q)).Prime := by
  sorry

end OMA.S_oeis_a224962
