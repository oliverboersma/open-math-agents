import Mathlib

/-!
# A185087: a(n) = Sum_{k=0..floor(n/2)} binomial(n-k,k)*A000108(k+1)

Source: https://oeis.org/A185087
Credit: @sntntHb

Offset 0. Formalizes R. J. Mathar's conjectured recurrence (OEIS A185087, Nov 16 2011):
`(n+4)*a(n) - (2*n+5)*a(n-1) - 3*(n+1)*a(n-2) + 2*(2*n-1)*a(n-3) = 0`,
stated for every `n >= 3`.
-/

namespace OMA.S_oeis_a185087

/-- A185087: `a(n) = Sum_{k=0..floor(n/2)} choose (n-k) k * catalan (k+1)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose (n - k) k * catalan (k + 1)

/-- Mathar's conjectured third-order recurrence, for every `n >= 3`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℤ) + 4) * (a n : ℤ) -
        (2 * (n : ℤ) + 5) * (a (n - 1) : ℤ) -
        3 * ((n : ℤ) + 1) * (a (n - 2) : ℤ) +
        2 * (2 * (n : ℤ) - 1) * (a (n - 3) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a185087
