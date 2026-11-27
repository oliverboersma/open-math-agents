import Mathlib

/-!
# OEIS A049505: three congruences for the number of symmetric plane partitions in an n-cube

Source: https://oeis.org/A049505
Credit: @sntntHb

A049505: `a(n) = Product_{1<=i<=j<=n} (i+j+n-1)/(i+j-1)`, the number of symmetric plane
partitions in the `n`-cube.

Conjectures (Peter Bala, Feb 15 2023):
1) the supercongruence `a(p) == 2^((p+1)/2) (mod p^3)` holds for all primes `p >= 3`;
2) the congruence `a(p^2) == (-1)^((p^2-1)/8)*a(p)^(p^2-p+1) (mod p^3)` holds for all primes
   `p >= 3`;
3) the congruence `a(p^3) == a(p^2)^((p^3-p^2+2)/2) (mod p^3)` holds for all primes `p >= 2`.

Formalized: `a n` is the displayed product, computed in `ℚ` (it is an integer). A congruence
`x == y (mod p^3)` between these integers is expressed as `x - y = p^3 * m` for an integer `m`.
The exponents `(p+1)/2`, `(p^2-1)/8` and `(p^3-p^2+2)/2` are exact natural-number quotients for
the primes concerned. `main` is the conjunction of the three conjectures.
-/

namespace OMA.S_oeis_a049505

/-- `a(n) = Product_{1<=i<=j<=n} (i+j+n-1)/(i+j-1)`. -/
def a (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc i n, ((i + j + n - 1 : ℕ) : ℚ) / ((i + j - 1 : ℕ) : ℚ)

theorem main :
    (∀ p : ℕ, p.Prime → 3 ≤ p →
      ∃ m : ℤ, a p - 2 ^ ((p + 1) / 2) = (p : ℚ) ^ 3 * m) ∧
    (∀ p : ℕ, p.Prime → 3 ≤ p →
      ∃ m : ℤ, a (p ^ 2) - (-1) ^ ((p ^ 2 - 1) / 8) * a p ^ (p ^ 2 - p + 1) = (p : ℚ) ^ 3 * m) ∧
    (∀ p : ℕ, p.Prime →
      ∃ m : ℤ, a (p ^ 3) - a (p ^ 2) ^ ((p ^ 3 - p ^ 2 + 2) / 2) = (p : ℚ) ^ 3 * m) := by
  sorry

end OMA.S_oeis_a049505
