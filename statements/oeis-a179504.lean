import Mathlib

/-!
# A179504: a(n) = sigma(2n,n) for n>0 with a(0)=1

Source: https://oeis.org/A179504
Credit: @xor2k

Formalizes the OEIS A179504 conjecture (Velin Yanev, offset 0):
a(n) = A023887(n)*((2^n - 1)/(2^(n*(A007814(n) + 1)) - 1) + 2^n) for n > 0.

Conventions: `sigma(m, k)` (sum of the `k`-th powers of the divisors of `m`) is Mathlib's
`ArithmeticFunction.sigma k m`, so `a(n) = ArithmeticFunction.sigma n (2*n)` for `n > 0` and `a(0) = 1`.
`A023887(n) = sigma(n, n)` is `ArithmeticFunction.sigma n n`, and `A007814(n)`, the 2-adic valuation of `n`, is
`padicValNat 2 n`. The right-hand side involves a genuine division, so the identity is stated
in `ℚ` (for `n > 0` the denominator `2^(n*(v+1)) - 1` is nonzero).
-/

namespace OMA.S_oeis_a179504

/-- `a(n) = sigma_n(2n)` for `n > 0`, with `a(0) = 1`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else ArithmeticFunction.sigma n (2 * n)

/-- For every `n > 0`, `a(n) = sigma_n(n) * ((2^n - 1)/(2^(n*(v_2(n) + 1)) - 1) + 2^n)`. -/
theorem main :
    ∀ n : ℕ, 0 < n →
      (a n : ℚ) = (ArithmeticFunction.sigma n n : ℚ) *
        (((2 : ℚ) ^ n - 1) / ((2 : ℚ) ^ (n * (padicValNat 2 n + 1)) - 1) + 2 ^ n) := by
  sorry

end OMA.S_oeis_a179504
