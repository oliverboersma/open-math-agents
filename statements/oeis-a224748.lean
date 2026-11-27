import Mathlib

/-!
# A224748: Given n-th prime p, a(n) = number of primes of the form p + q - 1 where q is any prime < p.

Source: https://oeis.org/A224748
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n)>0 for all n>2 (Dmitry Kamenetsky, Feb 09 2017).

Conventions: offset 1, so `prime(n)` with `n > 2` ranges over the primes `p ≥ 5`.
-/

namespace OMA.S_oeis_a224748

/-- For every prime `p ≥ 5` there is a prime `q < p` such that `p + q - 1` is prime. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∃ q : ℕ, q.Prime ∧ q < p ∧ (p + q - 1).Prime := by
  sorry

end OMA.S_oeis_a224748
