import Mathlib

/-!
# The four supercongruences for row 3 of Bala's Legendre array

Source: https://oeis.org/A364114
Credit: @DomTheDeveloper

Peter Bala defines `a(n)` as the coefficient of `x^n` in
`P_n((1+x)/(1-x))^3/(1-x)`. Put `y=x/(1-x)`. The coefficient of `y^j`
in `P_n(1+2y)` is `(n choose j) * (n+j choose j)`, and the coefficient
of `x^n` in `y^j/(1-x)` is `n choose j`. These identities give `a`.
-/

namespace OMA.S_oeis_a364114

noncomputable def a (n : ℕ) : ℕ :=
  let L : Polynomial ℕ := ∑ j ∈ Finset.range (n + 1),
    Polynomial.monomial j (n.choose j * (n + j).choose j)
  ∑ j ∈ Finset.range (n + 1), n.choose j * (L ^ 3).coeff j

theorem main :
    (∀ (p n r : ℕ), p.Prime → 5 ≤ p → 0 < n → 0 < r →
      Nat.ModEq (p ^ (3 * r)) (a (n * p ^ r)) (a (n * p ^ (r - 1))) ∧
      Nat.ModEq (p ^ (3 * r)) (a (n * p ^ r - 1)) (a (n * p ^ (r - 1) - 1))) ∧
    (∀ p : ℕ, p.Prime → 7 ≤ p →
      Nat.ModEq (p ^ 5) (3 * a p) (10 + 11 * a (p - 1)) ∧
      Nat.ModEq (p ^ 5) ((a p) ^ 21) (7 ^ 21 * (a (p - 1)) ^ 11)) := by
  sorry

end OMA.S_oeis_a364114
