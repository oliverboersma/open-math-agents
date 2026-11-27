import Mathlib

/-!
# A259492: Least positive integer k such that prime(k)-k, prime(k)+k, prime(k*n)-k*n, prime(k*n)+k*n, prime(k)+k*n and prime(k*n)+k are all prime.

Source: https://oeis.org/A259492
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A259492): Any positive rational number `r` can be written as
`m/n` with `prime(m) - m`, `prime(m) + m`, `prime(n) - n`, `prime(n) + n`, `prime(m) + n` and
`m + prime(n)` all prime. (The existence of `a(n)` is the case `r = n`, with numerator `k n` and denominator `k`.)

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`; since
  `prime(m) > m`, the subtractions in `ℕ` are exact.
* With this definition `a(1) = 4` and `a(3) = 6`, matching the data of A259492.
-/

namespace OMA.S_oeis_a259492

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- Sun's conjecture of A259492. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ r = (m : ℚ) / n ∧
    (prime m - m).Prime ∧ (prime m + m).Prime ∧ (prime n - n).Prime ∧ (prime n + n).Prime ∧
    (prime m + n).Prime ∧ (m + prime n).Prime := by
  sorry

end OMA.S_oeis_a259492
