import Mathlib

/-!
# Divisibility of numbers whose arithmetic derivative is a primorial greater than one

Source: https://oeis.org/A327978
Credit: @jatin6

David A. Corneth and Antti Karttunen conjectured that no term is divisible by five
and that nine is the only term divisible by three.
-/

namespace OMA.S_oeis_a327978

/-- OEIS A003415. Each prime factor contributes one quotient per occurrence. -/
def arithmeticDerivative (n : ℕ) : ℕ :=
  (n.primeFactorsList.map (fun p => n / p)).sum

theorem main : ∀ n : ℕ, 1 < arithmeticDerivative n →
    (∃ k : ℕ, arithmeticDerivative n = primorial k) →
    (¬ 5 ∣ n) ∧ (3 ∣ n → n = 9) := by
  sorry

end OMA.S_oeis_a327978

