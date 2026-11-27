import Mathlib

/-!
# A236574: Primes p with prime(p)^3 + 2*p^3 and p^3 + 2*prime(p)^3 both prime

Source: https://oeis.org/A236574
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A236574): This sequence has infinitely many terms.

Conventions:
* prime(n) is the n-th prime with prime(1) = 2 (`Nat.nth Nat.Prime (n - 1)`).
-/

namespace OMA.S_oeis_a236574

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Sun's conjecture on A236574: there are infinitely many primes `p` with `prime(p)^3 + 2p^3` and
`p^3 + 2 prime(p)^3` both prime. -/
theorem main : {p : ℕ | p.Prime ∧ (prime p ^ 3 + 2 * p ^ 3).Prime ∧
    (p ^ 3 + 2 * prime p ^ 3).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a236574
