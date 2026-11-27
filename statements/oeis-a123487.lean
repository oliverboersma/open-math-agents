import Mathlib

/-!
# A123487: Smallest prime q such that (q^p-1)/(q-1) is prime, where p = prime(n); or 0 if none

Source: https://oeis.org/A123487
Credit: @niclorusso

Conjecture (Robert G. Wilson v, Dec 28 2016, and Jones & Zvonkin, in the comments of A123487):
Never is a(n) equal to 0, i.e. a(n) > 0 for all n.

Conventions:
* a(n) > 0 means that for the prime p = prime(n) there is a prime q such that (q^p - 1)/(q - 1) is
  prime. As n ranges over n >= 1, p ranges over all primes, so the conjecture is stated for every
  prime p.
* For q >= 2, q - 1 divides q^p - 1, so (q^p - 1)/(q - 1) = 1 + q + ... + q^(p-1) is an exact
  natural-number division.
-/

namespace OMA.S_oeis_a123487

/-- The conjecture on A123487: for every prime `p` there is a prime `q` such that
`(q^p - 1)/(q - 1)` is prime. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ q : ℕ, q.Prime ∧ ((q ^ p - 1) / (q - 1)).Prime := by
  sorry

end OMA.S_oeis_a123487
