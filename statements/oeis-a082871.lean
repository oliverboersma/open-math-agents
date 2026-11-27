import Mathlib

/-!
# A082871: First component x of pairs (x,y) where x <= y and x!+y! is a square, sorted on x

Source: https://oeis.org/A082871
Credit: @niclorusso

Conjecture (in the comments of A082871): the only solutions for x!+y! = n^2 (x <= y) are
x=0,0,0,1,1,1,2,4 and y=4,5,7,4,5,7,2,5 respectively.

Conventions:
* x, y, n are natural numbers; x! + y! = n^2 for some n means that x! + y! is a perfect square
  (`IsSquare`).
* The conjecture is stated as a set equality for the pairs (x, y) with x <= y: they are exactly
  (0,4), (0,5), (0,7), (1,4), (1,5), (1,7), (2,2), (4,5).
-/

namespace OMA.S_oeis_a082871

/-- The conjecture on A082871: the pairs `x <= y` with `x! + y!` a square are exactly the eight
listed ones. -/
theorem main :
    {xy : ℕ × ℕ | xy.1 ≤ xy.2 ∧ IsSquare (xy.1.factorial + xy.2.factorial)} =
      {(0, 4), (0, 5), (0, 7), (1, 4), (1, 5), (1, 7), (2, 2), (4, 5)} := by
  sorry

end OMA.S_oeis_a082871
