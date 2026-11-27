import Mathlib

/-!
# A069837: Smallest prime which is a concatenation of n primes.

Source: https://oeis.org/A069837
Credit: @divmxnd0x

Conjecture (stated in A069837): for every `n` there exists an `n`-digit prime which is composed of
the digits 2, 3, 5 and 7, i.e. no prime greater than 7 is required in the concatenation.

Formalization notes:
* `n` ranges over `n ≥ 1` (offset 1).
* "`n`-digit" means `Nat.digits 10 p` has length `n` (no leading zeros), and every decimal digit of
  `p` is one of 2, 3, 5, 7.
* For `n = 1, ..., 7` the smallest such primes are 2, 23, 223, 2237, 22273, 222323, 2222273,
  matching the data of A069837.
-/

namespace OMA.S_oeis_a069837

/-- The conjecture of A069837: for every `n ≥ 1` there is an `n`-digit prime all of whose decimal
digits are prime (2, 3, 5 or 7). -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ (Nat.digits 10 p).length = n ∧
    ∀ d ∈ Nat.digits 10 p, d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 7 := by
  sorry

end OMA.S_oeis_a069837
