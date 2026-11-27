import Mathlib

/-!
# A381006: ordered long legs of the Pythagorean triangles with a = 2^(4n) + 2^(2n+1)

Source: https://oeis.org/A381006
Credit: @xor2k

OEIS name: Ordered long legs of the Pythagorean triangles defined by a = 2^(4n) + 2^(2n+1),
b = 2^(4n) - 2^(4n-2) - 2^(2n) - 1, c = 2^(4n) + 2^(4n-2) + 2^(2n) + 1.

Formalizes the OEIS A381006 conjecture: These Pythagorean triangles are primitive.

Conventions: offset 1 as in OEIS, so `n` ranges over `n >= 1`. The sides a, b, c are the
natural numbers `legA n`, `legB n`, `hyp n` given by the formulas above. For `n >= 1` the
natural-number subtractions in `legB` and the exponent `4 * n - 2` never truncate, so these are
exactly the OEIS values. A Pythagorean triangle (triple) is primitive when its three sides have
greatest common divisor 1, stated as `gcd (gcd a b) c = 1`.
-/

namespace OMA.S_oeis_a381006

/-- The leg a = 2^(4n) + 2^(2n+1). -/
def legA (n : ℕ) : ℕ := 2 ^ (4 * n) + 2 ^ (2 * n + 1)

/-- The leg b = 2^(4n) - 2^(4n-2) - 2^(2n) - 1. -/
def legB (n : ℕ) : ℕ := 2 ^ (4 * n) - 2 ^ (4 * n - 2) - 2 ^ (2 * n) - 1

/-- The hypotenuse c = 2^(4n) + 2^(4n-2) + 2^(2n) + 1. -/
def hyp (n : ℕ) : ℕ := 2 ^ (4 * n) + 2 ^ (4 * n - 2) + 2 ^ (2 * n) + 1

/-- For every `n >= 1` the triple (a, b, c) is primitive: gcd(a, b, c) = 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Nat.gcd (Nat.gcd (legA n) (legB n)) (hyp n) = 1 := by
  sorry

end OMA.S_oeis_a381006
