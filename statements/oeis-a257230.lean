import Mathlib

/-!
# A257230: Floor(sqrt(q)-(q-p)), where p and q are consecutive primes

Source: https://oeis.org/A257230
Credit: @niclorusso

Conjecture (in the comments of A257230): a(n) is always positive for n > 30, and is negative only
for n = 4, 9 and 30, corresponding to prime pairs (7, 11), (23, 29) and (113, 127).

Conventions:
* The sequence has offset 1: a(n) = floor(sqrt(q) - (q - p)) with p = prime(n), q = prime(n+1),
  where prime(1) = 2 (A000040). In Lean prime(n) is `Nat.nth Nat.Prime (n - 1)`.
* The square root and the floor are taken in the reals (`Real.sqrt`, `Int.floor`).
* Both parts of the conjecture are stated: a(n) > 0 for every n > 30, and for n >= 1, a(n) < 0
  exactly when n is 4, 9 or 30.
-/

namespace OMA.S_oeis_a257230

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A257230: `a n = floor(sqrt(q) - (q - p))` for the consecutive primes `p = prime n`,
`q = prime (n + 1)`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊Real.sqrt (prime (n + 1)) - ((prime (n + 1) : ℝ) - prime n)⌋

/-- The conjecture on A257230: `a n > 0` for all `n > 30`, and `a n < 0` exactly for
`n = 4, 9, 30`. -/
theorem main :
    (∀ n : ℕ, 30 < n → 0 < a n) ∧
      (∀ n : ℕ, 1 ≤ n → (a n < 0 ↔ n = 4 ∨ n = 9 ∨ n = 30)) := by
  sorry

end OMA.S_oeis_a257230
