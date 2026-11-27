import Mathlib

/-!
# A260947: Least k < prime(n) with k = i + j, 0 < i < j, such that i, j, k and i*j*k are primitive roots mod prime(n)

Source: https://oeis.org/A260947
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A260947): a(n) > 0 for all n > 6. In other words, for
any prime p > 13, there are three distinct elements a,b,c of {1,...,p-1} with a+b = c such that
a,b,c and a*b*c are all primitive roots modulo p.

Conventions:
* The conjecture is stated in its second form, for every prime p > 13 (prime(7) = 17).
* g is a primitive root modulo the prime p when its class in `ZMod p` has multiplicative order
  p - 1: `IsPrimitiveRoot (g : ZMod p) (p - 1)`.
* a + b = c is an equation of integers with 0 < a < b and c < p (so a, b, c are distinct elements
  of {1, ..., p-1}); a*b*c is taken modulo p.
-/

namespace OMA.S_oeis_a260947

/-- Sun's conjecture on A260947: for every prime `p > 13` there are `0 < a < b` with `a + b < p`
such that `a`, `b`, `a + b` and `a * b * (a + b)` are all primitive roots modulo `p`. -/
theorem main : ∀ p : ℕ, p.Prime → 13 < p → ∃ a b : ℕ, 0 < a ∧ a < b ∧ a + b < p ∧
    IsPrimitiveRoot (a : ZMod p) (p - 1) ∧ IsPrimitiveRoot (b : ZMod p) (p - 1) ∧
    IsPrimitiveRoot ((a + b : ℕ) : ZMod p) (p - 1) ∧
    IsPrimitiveRoot ((a * b * (a + b) : ℕ) : ZMod p) (p - 1) := by
  sorry

end OMA.S_oeis_a260947
