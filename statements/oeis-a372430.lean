import Mathlib

/-!
# OEIS A372430: 4100 is the only number whose binary indices are a subset of its prime indices

Source: https://oeis.org/A372430 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry (Gus Wiseman, 2024): Positive integers k such that the distinct prime indices of k are a
subset of the binary indices of k. Comments: A binary index of n is any position of a 1 in its
reversed binary expansion. A prime index of n is a number m such that prime(m) divides n.
Conjecture: The only number whose binary indices are a subset of its prime indices is 4100, with
binary indices {3,13} and prime indices {1,1,3,3,13}. Verified up to 10,000,000.

Formalization notes:
* Positions in the reversed binary expansion are counted from 1 at the least significant bit, so
  bit i - 1 of n is at position i. prime(m) is the m-th prime, with prime(1) = 2.
* The conjecture is about positive integers k (0 has no binary index and would satisfy the
  condition vacuously).
* Control from the entry: 4100 = 2^12 + 2^2 = 2^2 * 5^2 * 41 has binary indices {3, 13}, and
  prime(3) = 5 and prime(13) = 41 divide it.
-/

namespace OMA.S_oeis_a372430

/-- prime(m), the m-th prime: prime(1) = 2, prime(2) = 3, ... -/
noncomputable def prime (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1)

/-- The binary indices of n: the positions i >= 1 of the 1s in the reversed binary expansion. -/
def binIdx (n : ℕ) : Set ℕ := {i | 1 ≤ i ∧ n.testBit (i - 1) = true}

/-- The prime indices of n, as a set: the m >= 1 with prime(m) | n. -/
def primeIdx (n : ℕ) : Set ℕ := {m | 1 ≤ m ∧ prime m ∣ n}

/-- The conjecture: the only positive k whose binary indices are all prime indices is 4100. -/
theorem main : ∀ k : ℕ, 0 < k → binIdx k ⊆ primeIdx k → k = 4100 := by
  sorry

end OMA.S_oeis_a372430
