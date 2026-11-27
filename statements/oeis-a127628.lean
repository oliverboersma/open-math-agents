import Mathlib

/-!
# A127628: G.f. 1/(1-6*x*c(x)) where c(x) is the g.f. of A000108

Source: https://oeis.org/A127628
Credit: @sntntHb

The sequence (offset 0: `1, 6, 42, 300, 2154, 15492, ...`) has g.f. `1/(1-6*x*c(x))`, `c(x)` the
Catalan g.f.; the entry gives the explicit formula
`a(n) = Sum_{k=0..n} C(2*n,n-k)*(2*k+1)*5^k/(n+k+1)`, which we use as the definition
(each summand is an integer, the ballot number `C(2n,n-k)(2k+1)/(n+k+1)` times `5^k`; the sum is
computed in `ℚ`, so no truncating division occurs).
The entry records the conjecture (R. J. Mathar, Nov 14 2011, verified by Robert Israel, Aug 28 2020):
`Conjecture: 5*n*a(n) + 2*(15-28*n)*a(n-1) + 72*(2*n-3)*a(n-2) = 0.`

The recurrence involves `a(n-2)`, so it is stated for `n ≥ 2` (offset 0).
-/

namespace OMA.S_oeis_a127628

/-- `a n = ∑_{k=0}^{n} C(2n, n-k) (2k+1) 5^k / (n+k+1)` (OEIS A127628). -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    ((Nat.choose (2 * n) (n - k) : ℚ) * (2 * k + 1) * 5 ^ k) / ((n : ℚ) + k + 1)

/-- The conjectured recurrence for OEIS A127628. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    5 * (n : ℚ) * a n + 2 * (15 - 28 * (n : ℚ)) * a (n - 1) +
      72 * (2 * (n : ℚ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a127628
