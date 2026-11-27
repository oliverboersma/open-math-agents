import Mathlib

/-!
# OEIS A073642

Replace each distinct summand 2^j in the binary expansion of n by j,
and add the results. Velin Yanev's 2017 conjecture identifies this sum
using A011371(n), which is n minus the number of set bits of n, and
A007814(k), the exponent of 2 in k. The sum starts at k=1. Clearing
the denominator gives the following equality of nonnegative integers.

Source: https://oeis.org/A073642
-/

namespace OMA.S_oeis_a073642

theorem main : ∀ n : ℕ, 0 < n →
    2*n.bitIndices.sum + (∑ j ∈ Finset.range n, (padicValNat 2 (j+1))^2) =
    3*(n-n.bitIndices.length) := by
  sorry

end OMA.S_oeis_a073642
