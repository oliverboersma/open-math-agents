import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.Divisors

/-!
# The range of divisor-pair sum gcds on composite numbers

Source: https://oeis.org/A143772 (Robert G. Wilson v's 2008 conjecture,
OEIS Foundation, CC BY-SA 4.0). As the positive composite m varies, take the
GCD of d+m/d over every positive divisor d. Its range is conjectured to consist
of all positive even numbers together with 1 and 3.
-/

namespace OMA.S_oeis_a143772

def value (m : ℕ) : ℕ := m.divisors.gcd (fun d => d + m/d)

theorem main : ∀ g : ℕ, 0 < g →
    ((∃ m : ℕ, 1 < m ∧ ¬m.Prime ∧ value m=g) ↔ Even g ∨ g=1 ∨ g=3) := by
  sorry

end OMA.S_oeis_a143772
