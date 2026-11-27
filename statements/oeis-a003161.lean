import Mathlib

/-!
# OEIS A003161: a supercongruence for Sum (C(n,k) - C(n,k-1))^3 at odd indices

Source: https://oeis.org/A003161
Credit: @sntntHb

A003161 (a binomial coefficient sum): for a positive integer `r` define
`S(r,n) = Sum_{k = 0..floor(n/2)} ( binomial(n,k) - binomial(n,k-1) )^r`; the sequence is
`a(n) = S(3,n)`.

Conjecture (Peter Bala): let `b(n) = a(2*n-1)`. Then the supercongruence
`b(n*p^k) == b(n*p^(k-1)) (mod p^(3*k))` holds for positive integers `n` and `k` and all primes
`p >= 5`.

Formalized: `a n` is the displayed sum over `ℤ`, where `binomial(n,-1) = 0` (the `k = 0` term is
`1`). `b n = a (2*n - 1)`, and `main` states the congruence modulo `p^(3*k)` for every prime
`p >= 5` and all `n, k >= 1`.
-/

namespace OMA.S_oeis_a003161

/-- `a(n) = Sum_{k = 0..floor(n/2)} (binomial(n,k) - binomial(n,k-1))^3`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    ((n.choose k : ℤ) - (if k = 0 then 0 else (n.choose (k - 1) : ℤ))) ^ 3

/-- `b(n) = a(2*n-1)`. -/
def b (n : ℕ) : ℤ := a (2 * n - 1)

theorem main :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      b (n * p ^ k) ≡ b (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry

end OMA.S_oeis_a003161
