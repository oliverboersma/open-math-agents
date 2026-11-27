import Mathlib

/-!
# OEIS A114965: n^2 + 34

Source: https://oeis.org/A114965 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence is `a(n) = n^2 + 34` with offset 0. The entry records the comment:

  Conjecture: n^2 + 34 != x^k for all n,x and k > 1.

(A later comment in the entry reports that the conjecture is true, citing Cohn.)

We formalize this statement: for all natural numbers `n` and `x` and every exponent `k > 1`,
`n^2 + 34` is not equal to `x^k`, i.e. no term of the sequence is a perfect power.
-/

namespace OMA.S_oeis_a114965

/-- `a(n) = n^2 + 34`. -/
def a (n : ℕ) : ℕ := n ^ 2 + 34

/-- No term `n^2 + 34` is a perfect power `x^k` with `k > 1`. -/
theorem main : ∀ n x k : ℕ, 1 < k → a n ≠ x ^ k := by
  sorry

end OMA.S_oeis_a114965
