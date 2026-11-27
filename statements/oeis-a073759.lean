import Mathlib

/-!
# The largest unrelated number below a positive integer

Source: https://oeis.org/A073759
Credit: @anmolspace

Labos Elemer's sequence is the largest positive integer below n that neither
divides n nor is coprime to n, with value zero when the set is empty.
R. J. Mathar conjectured in 2026 that from n = 5 it equals twice A046667(n).
OEIS defines A046667(n) as half of A046666(n), which is n minus its least
prime divisor. See https://oeis.org/A046667 and https://oeis.org/A046666.
-/

namespace OMA.S_oeis_a073759

/-- On natural numbers, the supremum of an empty finite set is zero. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter (fun m => ¬ m ∣ n ∧ ¬ m.Coprime n)).sup id

/-- A046667 at the indices n ≥ 5 used in the conjecture. -/
def halfGap (n : ℕ) : ℕ := (n - n.minFac) / 2

/-- Mathar's formula for A073759. -/
theorem main : ∀ n : ℕ, 5 ≤ n → a n = 2 * halfGap n := by
  sorry

end OMA.S_oeis_a073759
