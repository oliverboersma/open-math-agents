import Mathlib

/-!
# A071636: Numbers n=4*k+2 such that there is no pair of primes p and q of form 4*i+1 with p+q=n; A071635(n)=0.

Source: https://oeis.org/A071636
Credit: @divmxnd0x

Conjecture (stated in A071636): there are no more terms, i.e. 2, 6, 14, 38, 62 are the only
numbers `n ≡ 2 (mod 4)` that are not the sum of two primes `p, q ≡ 1 (mod 4)`.

Formalization notes:
* `n = 4k + 2` with `k ≥ 0` is expressed as `n % 4 = 2`.
* The two primes may be equal (`p = q`), as in A071635, which counts such representations.
* Below 3000 the numbers `n ≡ 2 (mod 4)` without such a representation are exactly 2, 6, 14,
  38, 62.
-/

namespace OMA.S_oeis_a071636

/-- The conjecture of A071636: these are all `n ≡ 2 (mod 4)` that are not a sum of two primes
congruent to `1` modulo `4`. -/
theorem main :
    {n : ℕ | n % 4 = 2 ∧
        ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p % 4 = 1 ∧ q % 4 = 1 ∧ p + q = n} =
      {2, 6, 14, 38, 62} := by
  sorry

end OMA.S_oeis_a071636
