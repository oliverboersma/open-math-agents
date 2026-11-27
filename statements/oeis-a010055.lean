import Mathlib

/-!
# Yanev's identity for the prime-power indicator

Source: https://oeis.org/A010055 (OEIS Foundation, CC BY-SA 4.0).
Velin Yanev conjectured in March 2021 that the indicator A010055 at n > 1
equals (n - A048671(n)) / A000010(n). A048671 is the least common multiple
of the positive proper divisors of n, and A000010 is Euler's totient.
The quotient is taken in the rationals, so the equation retains its exact value.
-/

namespace OMA.S_oeis_a010055

noncomputable def a (n : ℕ) : ℕ := if n = 1 ∨ IsPrimePow n then 1 else 0

def lcmProper (n : ℕ) : ℕ := n.properDivisors.lcm id

theorem main : ∀ n : ℕ, 1 < n →
    (a n : ℚ) = ((n : ℚ) - (lcmProper n : ℚ)) / (n.totient : ℚ) := by
  sorry

end OMA.S_oeis_a010055
