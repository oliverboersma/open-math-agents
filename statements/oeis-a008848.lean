import Mathlib

/-!
# A008848: Squares whose sum of divisors is a square

Source: https://oeis.org/A008848
Credit: @niclorusso

Conjectures (Antti Karttunen, Jul 03 2023, (2) corrected in May 11 2024, in the comments of
A008848): (1) a(2) = 81 is the only prime power (A246655) in this sequence. (2) 81 and 400 are only
terms x for which sigma(x) is in A246655. (3) x = 1 is the only such term that sigma(x) is also a
term.

Conventions:
* The terms are the positive squares x such that sigma(x) is a square, where sigma(x) is the sum of
  the divisors of x (`ArithmeticFunction.sigma 1 x`). The first terms are 1, 81, 400, 32400.
* A246655 is the prime powers p^k with p prime and k >= 1 (so 1 is excluded): Mathlib's
  `IsPrimePow`.
* All three conjectures are stated, as set equalities, joined by `∧`.
-/

namespace OMA.S_oeis_a008848

open ArithmeticFunction

/-- `x` is a term of A008848: a positive square whose sum of divisors is a square. -/
def IsTerm (x : ℕ) : Prop :=
  0 < x ∧ IsSquare x ∧ IsSquare (sigma 1 x)

/-- Karttunen's three conjectures on A008848. -/
theorem main :
    {x : ℕ | IsTerm x ∧ IsPrimePow x} = {81} ∧
      {x : ℕ | IsTerm x ∧ IsPrimePow (sigma 1 x)} = {81, 400} ∧
        {x : ℕ | IsTerm x ∧ IsTerm (sigma 1 x)} = {1} := by
  sorry

end OMA.S_oeis_a008848
