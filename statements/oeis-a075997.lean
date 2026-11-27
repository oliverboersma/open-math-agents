import Mathlib

/-!
# A075997: a(n) = [n/2] - [n/3] + [n/4] - [n/5] + [n/6] - ..., where [n/k] = floor(n/k)

Source: https://oeis.org/A075997
Credit: @xor2k

Formalizes the OEIS A075997 conjecture (Benedict W. J. Irwin, offset 0):
Let f(a,b)=1, if (a+b) mod |a-b| != (a mod |a-b|)+(b mod |a-b|), and 0 otherwise.
a(n) = Sum_{k=1..n-1} f(n+k,n-k).

Conventions: the alternating series has only finitely many nonzero terms, since `[n/k] = 0`
for `k > n`, so `a(n) = Sum_{k=2..n} (-1)^k * floor(n/k)`, computed in `ℤ` with `n / k` the
natural-number floor division. `f` takes integer arguments (`n - k` is integer subtraction),
`|a-b|` is the integer absolute value and `mod` is `Int.emod`, which for a positive modulus is
the usual nonnegative remainder; in the conjecture `|a-b| = 2k > 0`. For `n = 0, 1` the sum
`Sum_{k=1..n-1}` is empty (`Finset.Icc 1 (n - 1)` with truncated subtraction is empty for `n = 0`).
The identity is stated for all `n ≥ 0` (offset 0).
-/

namespace OMA.S_oeis_a075997

/-- `a(n) = Sum_{k ≥ 2} (-1)^k * floor(n/k) = Sum_{k=2..n} (-1)^k * floor(n/k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 2 n, (-1) ^ k * ((n / k : ℕ) : ℤ)

/-- `f(a,b) = 1` if `(a+b) mod |a-b| ≠ (a mod |a-b|) + (b mod |a-b|)`, and `0` otherwise. -/
def f (x y : ℤ) : ℤ :=
  if (x + y) % |x - y| ≠ x % |x - y| + y % |x - y| then 1 else 0

/-- For every `n`, `a(n) = Sum_{k=1..n-1} f(n+k, n-k)`. -/
theorem main :
    ∀ n : ℕ, a n = ∑ k ∈ Finset.Icc 1 (n - 1), f ((n : ℤ) + k) ((n : ℤ) - k) := by
  sorry

end OMA.S_oeis_a075997
