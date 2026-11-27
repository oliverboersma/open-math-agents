import Mathlib.Data.Nat.Factorial.Basic

/-!
# Divisibility of the A295432 factorial quotient

Peter Bala conjectured that 6(6n+1)(12n-1) divides the factorial quotient
A295432(n) for every n at least one. Multiplying by the positive factorial
denominator expresses the original rational divisibility exactly over the
natural numbers.

Source: https://oeis.org/A295432
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a295432

theorem main : ∀ n : ℕ, 0 < n →
    6*(6*n+1)*(12*n-1) *
        ((6*n).factorial*(6*n).factorial*(4*n).factorial*n.factorial) ∣
      (12*n).factorial*(3*n).factorial*(2*n).factorial := by
  sorry

end OMA.S_oeis_a295432
