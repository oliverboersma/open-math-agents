import Mathlib

/-!
# The 2-adic valuation of A066357

Source: https://oeis.org/A066357
Conjecture: Peter Bala, August 2, 2016.
Proof in the OEIS entry: Clément Garrot, September 13, 2026.

The term a(n) is given by David Callan's formula in the same entry:
C(2n+1) + 2 C(2n) - 2^(2n+1) C(n), where C denotes the Catalan
numbers. The conjecture equates the exponents of 2 in a(n) and C(n).
The signed expression uses integers to avoid truncated subtraction.
-/

namespace OMA.S_oeis_a066357

def a (n : ℕ) : ℤ :=
  (catalan (2*n + 1) : ℤ) + 2 * (catalan (2*n) : ℤ) -
    (2 : ℤ) ^ (2*n + 1) * (catalan n : ℤ)

theorem main : ∀ n : ℕ,
    a n ≠ 0 ∧ (a n).natAbs.factorization 2 = (catalan n).factorization 2 := by
  sorry

end OMA.S_oeis_a066357
