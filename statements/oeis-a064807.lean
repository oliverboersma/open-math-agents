import Mathlib

/-!
# A064807: Numbers which are divisible by their digital root (A010888).

Source: https://oeis.org/A064807
Credit: @ShoQo

Conjecture (Ivan N. Ianakiev, May 10 2016): All k-multiply perfect numbers belong to this
sequence.

Formalization notes:
* A k-multiply perfect number is a positive `n` with `σ(n) = k * n` for some integer `k`, i.e.
  `n ∣ σ(n)` (this includes `n = 1`, which is in the sequence).
* The digital root of a positive `n` (A010888) is `1 + (n - 1) % 9`, the value reached by
  repeatedly summing decimal digits.
* Checked for every multiply perfect number up to 10^6 (1, 6, 28, 120, 496, 672, 8128, 30240,
  32760, 523776).
-/

namespace OMA.S_oeis_a064807

/-- The digital root (A010888) of a positive integer. -/
def digitalRoot (n : ℕ) : ℕ := 1 + (n - 1) % 9

theorem main : ∀ n : ℕ, 0 < n → n ∣ ArithmeticFunction.sigma 1 n → digitalRoot n ∣ n := by
  sorry

end OMA.S_oeis_a064807
