import Mathlib

/-!
# A119659: Floor of the area of consecutive Prime-Indexed Prime triangles

Source: https://oeis.org/A119659
Credit: @niclorusso

Conjecture (in the comments of A119659): The triples (3,5,11), (5,11,17), (11,17,31) are the only
consecutive PIP triples that cannot form a triangle.

Conventions:
* prime(n) is the n-th prime with prime(1) = 2 (`Nat.nth Nat.Prime (n - 1)`). The prime-indexed
  primes (PIPs, A006450) are q(k) = prime(prime(k)) for k >= 1: 3, 5, 11, 17, 31, 41, ...
* A consecutive PIP triple is (q(k), q(k+1), q(k+2)) for k >= 1. Since q(k) < q(k+1) < q(k+2), it
  forms a (nondegenerate) triangle exactly when q(k) + q(k+1) > q(k+2); it cannot form a triangle
  when q(k) + q(k+1) <= q(k+2).
* "the only triples" is stated as: for k >= 1, q(k) + q(k+1) <= q(k+2) if and only if k is 1, 2
  or 3 (the triples (3,5,11), (5,11,17), (11,17,31)).
-/

namespace OMA.S_oeis_a119659

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The `k`-th prime-indexed prime `prime (prime k)`. -/
noncomputable def pip (k : ℕ) : ℕ := prime (prime k)

/-- The conjecture on A119659: the consecutive PIP triples that cannot form a triangle are exactly
those with `k = 1, 2, 3`. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    (pip k + pip (k + 1) ≤ pip (k + 2) ↔ k = 1 ∨ k = 2 ∨ k = 3) := by
  sorry

end OMA.S_oeis_a119659
