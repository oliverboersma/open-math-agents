import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Rat.Defs

/-!
# Reduced numerators of divisor means at prime powers

Source: https://oeis.org/A336838 (OEIS Foundation, CC BY-SA 4.0). For a prime p,
let q be the prime immediately after p. Then A003961(p^e) = q^e and A048673(p)
= (q+1)/2. The function below takes the arithmetic mean over all positive
divisors. Rat.num reads the numerator after cancellation. Its absolute value is
the same nonnegative integer for these positive divisor means.
-/

namespace OMA.S_oeis_a336838

def divisorMean (m : ℕ) : ℚ := ((∑ d ∈ m.divisors, d : ℕ) : ℚ) / m.divisors.card

theorem main : ∀ p q e : ℕ, p.Prime → q.Prime → p < q →
    (∀ r : ℕ, p < r → r < q → ¬ r.Prime) → Odd e →
    (q+1)/2 ∣ (divisorMean (q^e)).num.natAbs := by
  sorry

end OMA.S_oeis_a336838
