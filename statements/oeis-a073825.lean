import Mathlib

/-!
OEIS A073825 lists the indices n for which the sum of k^k from k = 1 to n
is prime. Daniel Hoying conjectured on July 20, 2020 that this sequence is infinite.

https://oeis.org/A073825
-/

namespace OMA.S_oeis_a073825

theorem main : {n : ℕ | Nat.Prime (∑ k ∈ Finset.Icc 1 n, k ^ k)}.Infinite := by
  sorry

end OMA.S_oeis_a073825
