import Mathlib

/-!
# A393336: Sum of positions of 1's minus sum of positions of 0's in the binary expansion of n.

Source: https://oeis.org/A393336
Credit: @bnb9001

Position 1 is the least significant bit of `n` (offset 0). For example a(6) = 4, because
6 = 110_2 and -1 + 2 + 3 = 4, and a(8) = -2. The binary expansion of 0 is the single digit 0,
so a(0) = -1.

`weight L p` adds `p` for a 1 and subtracts `p` for any other digit, reading the digit list `L`
from the least significant digit at position `p`; `Nat.digits 2 n` lists the binary digits of
`n` from the least significant one.

Conjecture: the sequence contains all integers. Chai Wah Wu notes that the conjecture is true.
-/

namespace OMA.S_oeis_a393336

/-- `weight L p`: signed sum of the positions `p, p + 1, ...` of the digits of `L`, with `+` for
a digit 1 and `-` otherwise. -/
def weight : List ℕ → ℕ → ℤ
  | [], _ => 0
  | d :: L, p => (if d = 1 then (p : ℤ) else -(p : ℤ)) + weight L (p + 1)

/-- A393336: `a 0 = -1`, and for `n > 0` the signed sum of the bit positions of `n`. -/
def a (n : ℕ) : ℤ := if n = 0 then -1 else weight (Nat.digits 2 n) 1

/-- Every integer is a value of the sequence. -/
theorem main : ∀ z : ℤ, ∃ n : ℕ, a n = z := by
  sorry

end OMA.S_oeis_a393336
