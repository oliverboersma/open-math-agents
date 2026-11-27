import Mathlib

/-!
# A051064: 3-adic valuations of the Fibonacci numbers

Source: https://oeis.org/A051064 (OEIS Foundation, CC BY-SA 4.0).

a(n) is the exponent of the highest power of 3 dividing 3n (offset 1), i.e.
the 3-adic valuation of 3n. The entry conjectures (attributed to Lengyel) that
a(n) = A007949(A000045(4n)), where A007949 is the 3-adic valuation and A000045
are the Fibonacci numbers, and that all the other 3-adic quadrisections
A007949(A000045(4n + r)), r = 1, 2, 3, are identically zero.
-/

namespace OMA.S_oeis_a051064

/-- `a n` is the 3-adic valuation of `3 n`. -/
def a (n : ℕ) : ℕ := padicValNat 3 (3 * n)

theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = padicValNat 3 (Nat.fib (4 * n))) ∧
      ∀ n r : ℕ, 1 ≤ r → r ≤ 3 → padicValNat 3 (Nat.fib (4 * n + r)) = 0 := by
  sorry

end OMA.S_oeis_a051064
