import Mathlib

/-!
# A259531: Least positive integer k such that p(k)^2 + p(k*n)^2 is prime, where p(.) is the partition function given by A000041, or 0 if no such k exists.

Source: https://oeis.org/A259531
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A259531): Any positive rational number `r` can be written as
`m/n`, where `m` and `n` are positive integers with `p(m)^2 + p(n)^2` prime. (The existence of
`a(n)` is the case `r = n`.)

Formalization notes:
* `p(m)` is the number of partitions of `m`, `Fintype.card (Nat.Partition m)` (A000041).
* With this definition the least `k` with `p(k)^2 + p(k n)^2` prime is 1, 1, 14, 11, 6, 2 for
  `n = 1, 2, 3, 4, 5, 7`, matching the data of A259531.
-/

namespace OMA.S_oeis_a259531

/-- The partition function `p(m)`. -/
def partitionCount (m : ℕ) : ℕ :=
  Fintype.card (Nat.Partition m)

/-- Sun's conjecture of A259531. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ r = (m : ℚ) / n ∧
    (partitionCount m ^ 2 + partitionCount n ^ 2).Prime := by
  sorry

end OMA.S_oeis_a259531
