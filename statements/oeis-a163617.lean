import Mathlib

/-!
# A163617: a(2*n) = 2*a(n), a(2*n + 1) = 2*a(n) + 2 + (-1)^n, for all n in Z.

Source: https://oeis.org/A163617
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A163617 (Velin Yanev, Dec 17 2016):
a(n) = A003188(n) + (6*n + 1 - (-1)^n)/4.

Conventions:
* The OEIS data has offset 0 (0, 3, 6, 7, 12, 15, 14, 15, 24, ...), and A003188 is defined for
  `n ≥ 0`, so the conjecture is stated for every natural number `n`.
* On the natural numbers the defining relations a(2n) = 2*a(n), a(2n+1) = 2*a(n) + 2 + (-1)^n
  determine the sequence: n = 0 gives a(0) = 2*a(0), hence a(0) = 0, and every `n ≥ 1` is `2m`
  or `2m + 1` with `m = floor(n/2) < n`. The function `a` below is this unique solution, with
  values in `ℤ`.
* A003188(n) is the decimal equivalent of the Gray code for n, A003188(n) = n XOR floor(n/2)
  (formula of the OEIS entry); here `n ^^^ (n / 2)`.
* (6*n + 1 - (-1)^n)/4 is an exact division (the numerator is 6n for even n and 6n + 2 for odd
  n, and the quotient is an integer exactly in the form used), so the identity is stated after
  multiplying by 4: `4 * a n = 4 * A003188(n) + (6 * n + 1 - (-1) ^ n)` in `ℤ`.
-/

namespace OMA.S_oeis_a163617

/-- A163617 on the natural numbers: a(0) = 0, a(2m) = 2*a(m), a(2m+1) = 2*a(m) + 2 + (-1)^m. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then 2 * a ((n + 1) / 2)
    else 2 * a ((n + 1) / 2) + 2 + (-1) ^ ((n + 1) / 2)
decreasing_by all_goals omega

/-- For every `n`, a(n) = A003188(n) + (6*n + 1 - (-1)^n)/4, stated after multiplying by 4. -/
theorem main : ∀ n : ℕ,
    4 * a n = 4 * ((n ^^^ (n / 2) : ℕ) : ℤ) + (6 * (n : ℤ) + 1 - (-1) ^ n) := by
  sorry

end OMA.S_oeis_a163617
