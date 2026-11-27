import Mathlib

/-!
# A224908: Given n-th prime p, a(n)=number of primes of the form p+q+1 where q is any prime < p.

Source: https://oeis.org/A224908
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: a(n)>0 for all n>3 (Dmitry Kamenetsky, Feb 09 2017).

Conventions: offset 1, so `prime(n)` with `n > 3` ranges over the primes `p ≥ 7`.
-/

namespace OMA.S_oeis_a224908

/-- For every prime `p ≥ 7` there is a prime `q < p` such that `p + q + 1` is prime. -/
theorem main : ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∃ q : ℕ, q.Prime ∧ q < p ∧ (p + q + 1).Prime := by
  sorry

end OMA.S_oeis_a224908
