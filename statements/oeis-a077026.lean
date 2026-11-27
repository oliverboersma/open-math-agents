import Mathlib

/-!
# A077026: a(n) = Sum_{k=1..n} floor(n/k + 1)-floor(n/k + 1/2)

Source: https://oeis.org/A077026
Credit: @xor2k

Formalizes the OEIS A077026 conjecture (Benedict W. J. Irwin, offset 1):
Let f(a,b)=1, if (a+b) mod |a-b| != (a mod |a-b|)+(b mod |a-b|), and 0 otherwise.
a(n) = Sum_{k=1..n-1} 1-f(n,k).

Remark: as literally written the conjecture is false. The two sides differ by exactly 1 for every
`n` tested (1 to 599): the `k = n` term of `a(n)` equals 1 and the conjectured sum stops at
`n - 1`. The evident correction is a(n) = 1 + Sum_{k=1..n-1} (1 - f(n,k)). The statement below
follows the OEIS wording, and the accompanying file refutes it at n = 1.

Conventions: offset 1 as in OEIS, so `n ≥ 1`. The summand of `a(n)` is
`floor(n/k + 1) - floor(n/k + 1/2)` with `n/k` real division and `Int.floor`, summed over
`k = 1..n` in `ℤ`. `f` takes integer arguments, `|a-b|` is the integer absolute value and
`mod` is `Int.emod`, which for a positive modulus is the usual nonnegative remainder; in the
conjecture `|n-k| = n-k > 0` for `1 ≤ k ≤ n-1`. For `n = 1` the sum `Sum_{k=1..n-1}` is
empty (`Finset.Icc 1 0`).
-/

namespace OMA.S_oeis_a077026

/-- `a(n) = Sum_{k=1..n} (floor(n/k + 1) - floor(n/k + 1/2))`. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, (⌊(n : ℝ) / k + 1⌋ - ⌊(n : ℝ) / k + 1 / 2⌋)

/-- `f(a,b) = 1` if `(a+b) mod |a-b| ≠ (a mod |a-b|) + (b mod |a-b|)`, and `0` otherwise. -/
def f (x y : ℤ) : ℤ :=
  if (x + y) % |x - y| ≠ x % |x - y| + y % |x - y| then 1 else 0

/-- For every `n ≥ 1`, `a(n) = Sum_{k=1..n-1} (1 - f(n,k))`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), (1 - f (n : ℤ) (k : ℤ)) := by
  sorry

end OMA.S_oeis_a077026
