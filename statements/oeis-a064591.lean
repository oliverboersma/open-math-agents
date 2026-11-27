import Mathlib

/-!
# A064591: Nonunitary perfect numbers: k is the sum of its nonunitary divisors; i.e., k = sigma(k) - usigma(k).

Source: https://oeis.org/A064591
Credit: @divmxnd0x

A divisor `d` of `k` is unitary when `gcd(d, k/d) = 1` and nonunitary otherwise. `k` is a
nonunitary perfect number when it equals the sum of its nonunitary divisors.

Conjecture (Michel Lagneau, Jan 21 2015): let `s0` be the sum of the inverses of the even divisors
of `n` and `s1` the sum of the inverses of the odd divisors of `n`; then `n` is in the sequence
if and only if `2 s0 - s1 = 1`.

Formalization notes:
* The terms of A064591 are positive integers, so the equivalence is stated for `n ≥ 1`.
* The sums of inverses are taken in `ℚ`.
* Below 40000 both conditions single out exactly 24, 112, 1984, 32512, the data of A064591.
-/

namespace OMA.S_oeis_a064591

/-- The sum of the nonunitary divisors of `n`: divisors `d` with `gcd(d, n/d) > 1`. -/
def nonunitarySigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors.filter (fun d => 1 < Nat.gcd d (n / d)), d

/-- `n` is a nonunitary perfect number (a term of A064591). -/
def IsNonunitaryPerfect (n : ℕ) : Prop :=
  0 < n ∧ nonunitarySigma n = n

/-- Lagneau's conjecture: `n ≥ 1` is nonunitary perfect iff `2 s0 - s1 = 1`, where `s0` (resp. `s1`)
is the sum of the inverses of the even (resp. odd) divisors of `n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (IsNonunitaryPerfect n ↔
      2 * (∑ d ∈ n.divisors.filter Even, (1 : ℚ) / d) -
        (∑ d ∈ n.divisors.filter Odd, (1 : ℚ) / d) = 1) := by
  sorry

end OMA.S_oeis_a064591
