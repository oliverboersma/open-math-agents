import Mathlib

/-!
# A117078: Smallest k such that prime(n+1) = prime(n) + (prime(n) mod k), or 0 if no such k exists

Source: https://oeis.org/A117078
Credit: @niclorusso

Conjecture (in the comments of A117078): 2, 3 and 7 are the only primes for which
log(A000040(n)) < sqrt(A001223(n)).

Conventions:
* A000040(n) = prime(n) is the n-th prime with prime(1) = 2; in Lean `Nat.nth Nat.Prime (n - 1)`.
* A001223(n) = prime(n+1) - prime(n) is the n-th prime gap.
* log is the natural logarithm and sqrt the real square root (`Real.log`, `Real.sqrt`).
* "2, 3 and 7 are the only primes" is stated as: for every n >= 1, the inequality holds if and only
  if prime(n) is 2, 3 or 7.
-/

namespace OMA.S_oeis_a117078

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The conjecture on A117078: `log(prime n) < sqrt(prime (n+1) - prime n)` holds exactly when
`prime n` is `2`, `3` or `7`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (Real.log (prime n) < Real.sqrt ((prime (n + 1) : ℝ) - prime n) ↔
      prime n = 2 ∨ prime n = 3 ∨ prime n = 7) := by
  sorry

end OMA.S_oeis_a117078
