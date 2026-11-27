import Mathlib

/-!
# A344598: a(n) = Sum_{k=1..n} phi(k) * (floor(n/k)^2 - floor((n-1)/k)^2).

Source: https://oeis.org/A344598
Credit: @canneyi

Conjecture (Peter Bala, Jan 01 2024, in the entry):
`a(n) = Sum_{k = 1..2*n} (-1)^k * gcd(k, 4*n)`.

Formalization notes:
* Offset 1, as in the entry (data: 1, 4, 7, 12, 13, 24, 19, 32, ...), so the statement is for
  `1 ≤ n`.
* `phi` is Euler's totient function `Nat.totient`.
* `n / k` and `(n - 1) / k` are floor divisions of natural numbers. Both sides are sums of integers.
-/

namespace OMA.S_oeis_a344598

theorem main : ∀ n : ℕ, 1 ≤ n →
    (∑ k ∈ Finset.Icc 1 n,
        (Nat.totient k : ℤ) * (((n / k : ℕ) : ℤ) ^ 2 - (((n - 1) / k : ℕ) : ℤ) ^ 2)) =
      ∑ k ∈ Finset.Icc 1 (2 * n), (-1 : ℤ) ^ k * (Nat.gcd k (4 * n) : ℤ) := by
  sorry

end OMA.S_oeis_a344598
