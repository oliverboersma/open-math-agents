import Mathlib

/-!
# A101292: a(n) = n! + Sum_{i=1..n} i.

Source: https://oeis.org/A101292
Credit: @max-otc

The factoriangular numbers a(n) = n! + (1 + 2 + ... + n), n ≥ 0 (OEIS offset 0):
1, 2, 5, 12, 34, 135, 741, ...
Statement: the only Fibonacci numbers in this sequence are 1, 2, 5, 34
(C. A. Gómez Ruiz and F. Luca, Fibonacci factoriangular numbers, Indag. Math. 28 (2017) 796-804,
verifying a conjecture of Castillo). Fibonacci numbers are Mathlib's `Nat.fib` (F 0 = 0, F 1 = 1).
The set equality also records that each of 1, 2, 5, 34 occurs: a 0 = F 1, a 1 = F 3, a 2 = F 5, a 4 = F 9.
-/

namespace OMA.S_oeis_a101292

/-- The factoriangular number a(n) = n! + ∑_{i=1}^{n} i (OEIS A101292, offset 0). -/
def a (n : ℕ) : ℕ := n.factorial + ∑ i ∈ Finset.Icc 1 n, i

/-- The terms of A101292 that are Fibonacci numbers are exactly 1, 2, 5 and 34. -/
theorem main : Set.range a ∩ Set.range Nat.fib = {1, 2, 5, 34} := by
  sorry

end OMA.S_oeis_a101292
