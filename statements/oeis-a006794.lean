import Mathlib

/-!
# A006794: Primorial -1 primes: primes p such that -1 + product of primes up to p is prime.

Source: https://oeis.org/A006794
Credit: @mbilenko03

Conjecture (Arkadiusz Wesolowski, Jun 19 2016): if `p# - 1` is a prime number, then the previous
prime is greater than `p# - exp(1) * p`.

Conventions:
- `p` ranges over the primes (the terms of the sequence are primes `p`), and `p#` is the product of
  the primes up to `p`, which is Mathlib's `primorial p`.
- Since `p# - 1` is itself prime, 'the previous prime' is the greatest prime less than `p# - 1`.
  It is greater than a bound `B` exactly when some prime `q` satisfies `B < q < p# - 1`; this is
  how the conjecture is stated, which avoids defining a previous-prime function. The comparison
  with `p# - exp(1) * p` is made in `ℝ`; `q < p# - 1` is written `q + 1 < p#` in `ℕ`.
-/

namespace OMA.S_oeis_a006794

open Real

theorem main :
    ∀ p : ℕ, p.Prime → (primorial p - 1).Prime →
      ∃ q : ℕ, q.Prime ∧ q + 1 < primorial p ∧ (primorial p : ℝ) - exp 1 * p < q := by
  sorry

end OMA.S_oeis_a006794
