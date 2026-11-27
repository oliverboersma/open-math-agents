import Mathlib

/-!
# A055234: Smallest x such that sigma(x) = n*phi(x), or -1 if no such x exists.

Source: https://oeis.org/A055234
Credit: @divmxnd0x

Conjecture (Farideh Firoozbakht, Sep 12 2004): for each `n`, `a(n) > 0`, i.e. for every `n ≥ 1`
(offset 1) there is a positive integer `x` with `σ(x) = n φ(x)`.

Formalization notes:
* `x` must be positive: for `x = 0` both `σ(0)` and `φ(0)` are `0` in Mathlib, which would make the
  statement trivial.
* `σ(x)` is the sum of the divisors of `x`.
* For `n = 1, ..., 10` the least such `x` is 1, 3, 2, 14, 56, 6, 12, 42, 30, 168, matching the
  data of A055234.
-/

namespace OMA.S_oeis_a055234

/-- Firoozbakht's conjecture: for every `n ≥ 1` some `x ≥ 1` has `σ(x) = n φ(x)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ x : ℕ, 0 < x ∧ ∑ d ∈ x.divisors, d = n * Nat.totient x := by
  sorry

end OMA.S_oeis_a055234
