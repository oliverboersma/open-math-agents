import Mathlib

/-!
# OEIS A098274: Apéry-type supercongruences for Sum C(n,k)^2 C(n+k,n) C(n+2k,n)

Source: https://oeis.org/A098274
Credit: @sntntHb

A098274: `a(n) = Sum_{k = 0..n} C(n, k)^2*C(n+k, n)*C(n+2*k, n)`.

Peter Bala (Oct 05 2026): the two types of Apéry numbers, A005258 and A005259, satisfy the pair
of supercongruences `u(n*p^r) == u(n*p^(r-1)) (mod p^(3*r))` and
`u(n*p^r - 1) == u(n*p^(r-1) - 1) (mod p^(3*r))` for all primes `p >= 5` and all positive integers
`n` and `r`. We conjecture that the present sequence satisfies the same pair of
supercongruences.

Formalized: `a` is defined by the displayed sum over `ℕ`, and `main` states both congruences for
`a`, for every prime `p >= 5` and all `n, r >= 1` (with `n*p^r - 1` and `n*p^(r-1) - 1` positive,
so natural subtraction is harmless).
-/

namespace OMA.S_oeis_a098274

/-- `a(n) = Sum_{k = 0..n} C(n, k)^2*C(n+k, n)*C(n+2*k, n)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k ^ 2 * (n + k).choose n * (n + 2 * k).choose n

theorem main :
    ∀ p n r : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < r →
      a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] ∧
      a (n * p ^ r - 1) ≡ a (n * p ^ (r - 1) - 1) [MOD p ^ (3 * r)] := by
  sorry

end OMA.S_oeis_a098274
