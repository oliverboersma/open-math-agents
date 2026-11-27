import Mathlib

/-!
# A038867: a(n) = (n+5)^3 - n^3

Source: https://oeis.org/A038867
Credit: @xor2k

Formalizes the OEIS A038867 conjecture (Klaus Purath, offset 0):
There are no squares in this sequence.

Conventions: the sequence is indexed by `n : ℕ` from `0` (offset 0) and computed in `ℕ`; the
natural subtraction `(n+5)^3 - n^3` is exact because `n^3 ≤ (n+5)^3`. A square is a natural
number of the form `m * m` (Mathlib's `IsSquare`).
-/

namespace OMA.S_oeis_a038867

/-- `a(n) = (n+5)^3 - n^3`. -/
def a (n : ℕ) : ℕ :=
  (n + 5) ^ 3 - n ^ 3

/-- No term of the sequence is a perfect square. -/
theorem main :
    ∀ n : ℕ, ¬ IsSquare (a n) := by
  sorry

end OMA.S_oeis_a038867
