import Mathlib

/-!
# A133212: a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3), n > 3; a(0) = 1, a(1) = 4, a(2) = 12, a(3) = 32.

Source: https://oeis.org/A133212
Credit: @JeremyDevs

Formalizes the OEIS A133212 conjecture (R. J. Mathar, Oct 23 2007):
a(n) = 2*A038503(n+3) if n > 0.

Conventions:
* A133212 has offset 0, with a(0) = 1, a(1) = 4, a(2) = 12, a(3) = 32 and
  a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) for n > 3, written with `n + 4` in place of `n`. Because
  the recurrence has a negative coefficient, the terms are taken in `ℤ`.
* A038503 (offset 0) is the sum of every 4th entry of row n of Pascal's triangle, starting at
  "n choose 0": A038503(n) = Sum_{k=0..floor(n/4)} binomial(n, 4k) (formula of the OEIS entry).
  It is the function `b` below, with natural-number values 1, 1, 1, 1, 2, 6, 16, 36, 72, ...
* The identity is asserted for every `n > 0`, as in the source (it fails at `n = 0`:
  a(0) = 1 but 2*A038503(3) = 2).
-/

namespace OMA.S_oeis_a133212

/-- A133212: a(0) = 1, a(1) = 4, a(2) = 12, a(3) = 32, a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | 2 => 12
  | 3 => 32
  | n + 4 => 4 * a (n + 3) - 6 * a (n + 2) + 4 * a (n + 1)

/-- A038503: b(n) = Sum_{k=0..floor(n/4)} binomial(n, 4k). -/
def b (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 4 + 1), n.choose (4 * k)

/-- For every `n > 0`, a(n) = 2*A038503(n+3). -/
theorem main : ∀ n : ℕ, 0 < n → a n = 2 * (b (n + 3) : ℤ) := by
  sorry

end OMA.S_oeis_a133212
