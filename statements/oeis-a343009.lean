import Mathlib.NumberTheory.FermatPsp

/-!
# OEIS A343009 and Fermat pseudoprimes to base n

Source: https://oeis.org/A343009 (OEIS Foundation, CC BY-SA 4.0).
Credit: @anmolspace.

Thomas Ordowski proposed the sequence and the pseudoprime conjecture.
The source records a proof by Jianing Song on August 28, 2022.
-/

namespace OMA.S_oeis_a343009

/-- The sequence has offset one and takes the value one at that index. -/
def a (n : ℕ) : ℕ :=
  if n = 1 then 1 else (n ^ (2 * n) - 1) / (n ^ 2 - 1)

theorem main : ∀ n : ℕ, 2 < n → (a n).FermatPsp n := by
  sorry

end OMA.S_oeis_a343009
