import Mathlib

/-!
# A383243: Primes of the form p(k)*p(k+1)*(p(k+1) - p(k)) - 1 sorted by increasing k

Source: https://oeis.org/A383243
Credit: @niclorusso

Conjecture (in the comments of A383243): there are infinitely many such primes.

Conventions:
* p(k) is the k-th prime with p(1) = 2 (`Nat.nth Nat.Prime (k - 1)`); k >= 1. Since
  p(k+1) > p(k), the difference p(k+1) - p(k) is an exact natural-number subtraction.
* "infinitely many such primes" is stated for the set of primes of this form.
-/

namespace OMA.S_oeis_a383243

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The conjecture on A383243: there are infinitely many primes of the form
`p(k) * p(k+1) * (p(k+1) - p(k)) - 1`. -/
theorem main : {q : ℕ | q.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧
    q = prime k * prime (k + 1) * (prime (k + 1) - prime k) - 1}.Infinite := by
  sorry

end OMA.S_oeis_a383243
