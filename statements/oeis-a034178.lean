import Mathlib

/-!
# A034178: Number of solutions to n = a^2 - b^2, a > b >= 0.

Source: https://oeis.org/A034178
Credit: @ShoQo

Three conjectures from the entry, all marked true there:
* Gregory Bryant (Dec 06 2016): "It appears a(n) can be found by adding together the divisor
  pairs of n and finding the number of even results." (e.g. n = 9: pairs (1,9), (3,3).)
* Joseph Barrera (Nov 29 2020): "It appears a(n) is the number of nonnegative integers k for
  which sqrt(k) + sqrt(k + n) is an integer."
* Joerg Arndt (Jan 04 2024): "G.f.: Sum_{n>=1} x^(n^2)/(1-x^(2*n))" (proved by Sela Fried, 2025).

Formalization notes:
* Offset 1; all three are stated for `n ≥ 1`.
* Divisor pairs of `n` are the pairs `(d, n/d)` with `d ∣ n` and `d ≤ n/d`, i.e. `d * d ≤ n`.
* Arndt's generating function is stated coefficient-wise: since
  `x^(m^2) / (1 - x^(2m)) = Sum_{j>=0} x^(m^2 + 2 m j)`, its coefficient of `x^n` is the number
  of pairs `(m, j)` with `m ≥ 1`, `j ≥ 0` and `m^2 + 2 m j = n`.
-/

namespace OMA.S_oeis_a034178

/-- a(n): the number of pairs `(a, b)` with `a > b ≥ 0` and `n = a^2 - b^2`. -/
noncomputable def a (n : ℕ) : ℕ := {p : ℕ × ℕ | p.2 < p.1 ∧ p.1 ^ 2 = p.2 ^ 2 + n}.ncard

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = {d : ℕ | d ∣ n ∧ d * d ≤ n ∧ Even (d + n / d)}.ncard ∧
    a n = {k : ℕ | ∃ m : ℤ, Real.sqrt k + Real.sqrt ((k + n : ℕ) : ℝ) = m}.ncard ∧
    a n = {p : ℕ × ℕ | 1 ≤ p.1 ∧ p.1 ^ 2 + 2 * p.1 * p.2 = n}.ncard := by
  sorry

end OMA.S_oeis_a034178
