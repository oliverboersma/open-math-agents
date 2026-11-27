import Mathlib

/-!
# OEIS A061062: sums of squared factorials

Source: https://oeis.org/A061062 (OEIS Foundation, CC BY-SA 4.0).
Credit: @anmolspace.

Jason Earls contributed the sequence, which starts at index zero. On December 8, 2004,
T. D. Noe recorded the Kurepa-like conjecture below and a counterexample at 20879.
We state the original universal conjecture, with the strict condition that the prime exceed three.
-/

namespace OMA.S_oeis_a061062

/-- The sum of the squares of the factorials from zero through `n`, including both endpoints. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), k.factorial ^ 2

theorem main : ∀ p : ℕ, p.Prime → 3 < p → ¬ p ∣ a (p - 1) := by
  sorry

end OMA.S_oeis_a061062
