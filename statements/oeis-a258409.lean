import Mathlib

/-!
# A258409: Greatest common divisor of all (d-1)'s, where the d's are the positive divisors of n.

Source: https://oeis.org/A258409
Credit: @bnb9001

The sequence has offset 2 (for example a(65) = gcd(0, 4, 12, 64) = 4). `a n` is the gcd of
`d - 1` over the divisors `d` of `n`; the divisor 1 contributes 0, which does not change a gcd.

Conjectures stated in the entry:
1. (Thomas Ordowski) a(n) is the GCD of all (p - 1) for primes p dividing n. Robert Israel notes
   that this is true.
2. (Gus Wiseman) a(n) is the GCD of the differences between consecutive divisors of n. Two
   divisors `d < e` of `n` are consecutive when no divisor of `n` lies strictly between them.
We state both, for every `n ≥ 2`.
-/

namespace OMA.S_oeis_a258409

/-- A258409: the gcd of `d - 1` over the divisors `d` of `n`. -/
def a (n : ℕ) : ℕ := n.divisors.gcd (fun d => d - 1)

/-- The gcd of `p - 1` over the primes `p` dividing `n`. -/
def gcdPrimes (n : ℕ) : ℕ := n.primeFactors.gcd (fun p => p - 1)

/-- Pairs `(d, e)` of consecutive divisors of `n`: `d < e` and no divisor lies strictly between. -/
def consecutiveDivisors (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.divisors ×ˢ n.divisors).filter
    (fun p => p.1 < p.2 ∧ ∀ c ∈ n.divisors, ¬ (p.1 < c ∧ c < p.2))

/-- The gcd of the differences between consecutive divisors of `n`. -/
def gcdConsecutive (n : ℕ) : ℕ := (consecutiveDivisors n).gcd (fun p => p.2 - p.1)

/-- For every `n ≥ 2`, `a n` equals the gcd of `p - 1` over the primes `p ∣ n`, and the gcd of the
differences between consecutive divisors of `n`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n = gcdPrimes n ∧ a n = gcdConsecutive n := by
  sorry

end OMA.S_oeis_a258409
