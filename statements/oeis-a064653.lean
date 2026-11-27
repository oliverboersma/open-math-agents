import Mathlib

/-!
# A064653: Integers not expressible as p + q*a^2, a>1 and p, q are primes.

Source: https://oeis.org/A064653
Credit: @divmxnd0x

Dean Hickerson (Oct 12 2001): "I suspect that there are no more terms in the sequence. In fact,
I'll make the stronger conjecture that for all `n > 1260`, `n` can be written as `p + q*a^2` where
`a` is the smallest prime that does not divide `n`." (Checked for `n ≤ 10^9` by D. A. Corneth.)

The statement below is the conjunction of both conjectures: the terms of A064653 are exactly
1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 16, 18, 24, 26, 28, 36, 42, 60, 72, 84, 90, 96, 108, 240, 300, 420,
1050, 1260, and every `n > 1260` is `p + q * a^2` with `a` the least prime not dividing `n`.

Formalization notes:
* The sequence lists positive integers, so `n ≥ 1` in the first part.
* `leastNonDivisorPrime n` is the least prime not dividing `n` (the set is nonempty for `n ≥ 1`).
* Below 2500 the positive integers not of the form `p + q a^2` (`a ≥ 2`) are exactly the listed
  terms, and every `n` with `1261 ≤ n ≤ 2500` has a representation with `a` the least prime not
  dividing `n`.
-/

namespace OMA.S_oeis_a064653

/-- `n` is `p + q * a^2` with primes `p, q` and an integer `a > 1`. -/
def IsRep (n : ℕ) : Prop :=
  ∃ p q a : ℕ, p.Prime ∧ q.Prime ∧ 1 < a ∧ n = p + q * a ^ 2

/-- The least prime not dividing `n`. -/
noncomputable def leastNonDivisorPrime (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ¬ p ∣ n}

/-- Hickerson's conjectures for A064653. -/
theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ IsRep n} =
        {1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 16, 18, 24, 26, 28, 36, 42, 60, 72, 84, 90, 96, 108, 240,
          300, 420, 1050, 1260} ∧
      ∀ n : ℕ, 1260 < n →
        ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q * leastNonDivisorPrime n ^ 2 := by
  sorry

end OMA.S_oeis_a064653
