import Mathlib

/-!
# A064915: Positive integers n that are not of the form p + q * a^2, where p and q are primes and a is the smallest prime not dividing n.

Source: https://oeis.org/A064915
Credit: @divmxnd0x

Conjecture (stated in A064915): there are no more terms in the sequence than the 47 listed
terms, the largest being 1260 (no other terms up to 10^7).

Formalization notes:
* `leastNonDivisorPrime n` is the least prime not dividing `n` (the set is nonempty for `n ≥ 1`).
* The sequence lists positive integers, so `n ≥ 1`.
* Below 3000 the positive integers without such a representation are exactly the 47 numbers on
  the right-hand side (the data of A064915).
-/

namespace OMA.S_oeis_a064915

/-- The least prime not dividing `n`. -/
noncomputable def leastNonDivisorPrime (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ¬ p ∣ n}

/-- The conjecture of A064915: its listed terms are all of its terms. -/
theorem main :
    {n : ℕ | 1 ≤ n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q * leastNonDivisorPrime n ^ 2} =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 22, 24, 26, 28, 30, 36, 42, 48, 54, 60, 66,
        72, 77, 84, 90, 96, 102, 108, 114, 120, 126, 174, 180, 210, 240, 270, 300, 330, 420, 630,
        840, 1050, 1260} := by
  sorry

end OMA.S_oeis_a064915
