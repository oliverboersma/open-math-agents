import Mathlib

/-!
# A000364: Periodicity of the secant numbers

Source: https://oeis.org/A000364, conjecture by Peter Bala (May 8, 2023).
The definition uses the recurrence credited to Ralf Stephan in the same entry.
See https://www.trureturing.org/research/oeis-a000364-secant-number-pure-period-refutation/
for the published counterexample modulo 27.
-/

open scoped BigOperators

namespace OMA.S_oeis_a000364

/-- The secant numbers, indexed from zero. -/
def secantNumber : ℕ → ℤ
  | 0 => 1
  | n + 1 => ∑ j : Fin (n + 1),
      (-1 : ℤ) ^ (j.val + 2) * ((2 * (n + 1)).choose (2 * (j.val + 1)) : ℤ) *
        secantNumber (n - j.val)
termination_by n => n

/-- Bala's original conjecture. Modulus 27 is a counterexample. -/
theorem main :
    ∀ k : ℕ, 0 < k → ∃ p : ℕ, 0 < p ∧ p ∣ k.totient ∧
      ∀ n : ℕ, 1 ≤ n → Int.ModEq k (secantNumber (n + p)) (secantNumber n) := by
  sorry

end OMA.S_oeis_a000364
