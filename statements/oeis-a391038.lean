import Mathlib

/-!
# A391038: Number of ways to write n as (p-1)^4/8 + (q-1)^2/4 + (r-1)^2/4 + (s+1)^2/4, where each of p,q,r,s is either 1 or an odd prime.

Source: https://oeis.org/A391038
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A391038): `a(n) > 0` for all `n > 0`, i.e. every positive integer
can be written as `(p-1)^4/8 + (q-1)^2/4 + (r-1)^2/4 + (s+1)^2/4` with each of `p, q, r, s` either 1
or an odd prime.

Formalization notes:
* For `p, q, r, s` equal to 1 or odd, the numerators are divisible by 16, 4, 4, 4 respectively, so
  the divisions in `ℕ` are exact.
* Counting with `q ≤ r` (the two symmetric summands unordered), the number of representations for
  `n = 1, ..., 20` is 1, 1, 2, 2, 3, 3, 2, 3, 3, 3, 5, 3, 4, 4, 2, 4, 3, 3, 5, 3, matching the data of
  A391038.
-/

namespace OMA.S_oeis_a391038

/-- `p` is 1 or an odd prime. -/
def OneOrOddPrime (p : ℕ) : Prop :=
  p = 1 ∨ (p.Prime ∧ Odd p)

/-- Sun's conjecture: every `n > 0` is `(p-1)^4/8 + (q-1)^2/4 + (r-1)^2/4 + (s+1)^2/4`. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ p q r s : ℕ, OneOrOddPrime p ∧ OneOrOddPrime q ∧
    OneOrOddPrime r ∧ OneOrOddPrime s ∧
    n = (p - 1) ^ 4 / 8 + (q - 1) ^ 2 / 4 + (r - 1) ^ 2 / 4 + (s + 1) ^ 2 / 4 := by
  sorry

end OMA.S_oeis_a391038
