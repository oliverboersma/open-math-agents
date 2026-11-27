import Mathlib

/-!
# Ample numbers avoiding the first primes

Thomas Fink, "Recursively abundant and recursively perfect numbers", Conjecture 1.
Source: https://arxiv.org/abs/2008.10398
Credit: @rleshner
-/

namespace OMA.S_arxiv_2008_10398

/-- The size of the recursive divisor tree (Fink, Definition 1). -/
def recursiveDivisors (n : ℕ) : ℕ :=
  1 + ∑ d ∈ n.properDivisors.attach, recursiveDivisors d.val
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.property).2

/-- Taking arbitrary prime cutoffs is equivalent to excluding each initial segment
of the ordered primes. -/
theorem main : ∀ k : ℕ, ∃ n : ℕ, 0 < n ∧ n < recursiveDivisors n ∧
    ∀ p : ℕ, Nat.Prime p → p ≤ k → ¬ p ∣ n := by
  sorry

end OMA.S_arxiv_2008_10398
