import Mathlib

/-!
# A070247: Palindromic primes with digit sum 5.

Source: https://oeis.org/A070247
Credit: @divmxnd0x

Conjecture (stated in A070247): there are just 3 palindromic primes with digit sum 2, namely 2, 11
and 101. If any others exist, they must be of the form `10^(2^k) + 1` with `k > 14`.

Formalization notes:
* A number is palindromic (in base 10) when its list of decimal digits, as given by
  `Nat.digits 10` (no leading zeros), equals its reverse.
* The digit sum is the sum of that list.
* Below 10^6 the palindromic primes with digit sum 2 are exactly 2, 11, 101.
-/

namespace OMA.S_oeis_a070247

/-- The conjecture of A070247: 2, 11 and 101 are the only palindromic primes with digit sum 2. -/
theorem main :
    {p : ℕ | p.Prime ∧ (Nat.digits 10 p).reverse = Nat.digits 10 p ∧ (Nat.digits 10 p).sum = 2} =
      {2, 11, 101} := by
  sorry

end OMA.S_oeis_a070247
