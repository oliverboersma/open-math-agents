import Mathlib

/-!
# A005234: Primes p such that 1 + product of primes up to p is prime.

Source: https://oeis.org/A005234
Credit: @mbilenko03

The entry records two conjectures:
1. (Arkadiusz Wesolowski, Feb 20 2013) if `p# + 1` is a prime number, then the next prime is less
   than `p# + exp(1) * p`;
2. (Thomas Ordowski, Apr 07 2013) if `p# + 1` is a prime, then the next prime is less than
   `p# + p^2`.

`main` is the conjunction of the two.

Conventions:
- `p` ranges over the primes (the terms of the sequence are primes `p`), and `p#` is the product of
  the primes up to `p`, which is Mathlib's `primorial p`.
- Since `p# + 1` is itself prime, 'the next prime' is the least prime greater than `p# + 1`. The
  least prime greater than `p# + 1` is less than a bound `B` exactly when some prime `q` satisfies
  `p# + 1 < q < B`; this is how both conjectures are stated, which avoids defining a next-prime
  function. The comparison with `p# + exp(1) * p` is made in `ℝ`.
-/

namespace OMA.S_oeis_a005234

open Real

theorem main :
    (∀ p : ℕ, p.Prime → (primorial p + 1).Prime →
      ∃ q : ℕ, q.Prime ∧ primorial p + 1 < q ∧ (q : ℝ) < (primorial p : ℝ) + exp 1 * p) ∧
    (∀ p : ℕ, p.Prime → (primorial p + 1).Prime →
      ∃ q : ℕ, q.Prime ∧ primorial p + 1 < q ∧ q < primorial p + p ^ 2) := by
  sorry

end OMA.S_oeis_a005234
