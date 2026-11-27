import Mathlib

/-!
# A112700: Partial sum of Catalan numbers A000108 multiplied by powers of 6

Source: https://oeis.org/A112700
Credit: @sntntHb

`a(n) = Sum_{k=0..n} 6^k * A000108(k)`, offset 0.

Formalizes R. J. Mathar's conjectured recurrence (OEIS A112700, Jun 08 2016):
`(n+1)*a(n) + (-25*n+11)*a(n-1) + 12*(2*n-1)*a(n-2) = 0`, stated for every `n >= 2`.
-/

namespace OMA.S_oeis_a112700

/-- A112700: `a(n) = Sum_{k=0..n} 6^k * catalan k`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), 6 ^ k * catalan k

/-- Mathar's conjectured second-order recurrence, for every `n >= 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℤ) + 1) * (a n : ℤ) +
        (-25 * (n : ℤ) + 11) * (a (n - 1) : ℤ) +
        12 * (2 * (n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a112700
