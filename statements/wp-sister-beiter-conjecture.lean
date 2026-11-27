import Mathlib

/-!
# The (corrected) Sister Beiter conjecture

Source: https://en.wikipedia.org/wiki/Sister_Beiter_conjecture
Credit: @Drogobo

For `n > 0` let `A(n)` be the largest absolute value of a coefficient of the cyclotomic polynomial
`Φ_n(x)`. For primes `3 ≤ p ≤ q ≤ r` the polynomial `Φ_{pqr}` is called ternary, and Bang (1895)
proved `A(pqr) ≤ p - 1`, so `M(p) := max_{p ≤ q ≤ r prime} A(pqr)` exists. Sister Beiter (1968)
conjectured `M(p) ≤ (p + 1) / 2`; this was disproved, and the corrected Sister Beiter conjecture
is `M(p) ≤ (2 / 3) p`.

`M(p) ≤ (2 / 3) p` says exactly that every coefficient `c` of every such `Φ_{pqr}` satisfies
`|c| ≤ (2 / 3) p`, which over the integers is `3 * |c| ≤ 2 * p`. We use Mathlib's
`Polynomial.cyclotomic n ℤ`. The ranges are those of the source (`3 ≤ p ≤ q ≤ r`, all prime).
-/

namespace OMA.S_wp_sister_beiter_conjecture

open Polynomial

/-- Corrected Sister Beiter conjecture: for primes `3 ≤ p ≤ q ≤ r`, every coefficient of the
ternary cyclotomic polynomial `Φ_{pqr}` has absolute value at most `(2 / 3) p`. -/
theorem main : ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime → 3 ≤ p → p ≤ q → q ≤ r →
    ∀ i : ℕ, 3 * |(cyclotomic (p * q * r) ℤ).coeff i| ≤ 2 * (p : ℤ) := by
  sorry

end OMA.S_wp_sister_beiter_conjecture
