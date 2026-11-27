import Mathlib

/-!
# The squared-involution recurrence for OEIS A111883

Source: https://oeis.org/A111883
Comparison sequence: https://oeis.org/A000085
Credit: @Heart-galaxy

A111883 has offset 0 and is the square of A000085(n), as recorded by Somos
on August 30, 2005. We define A000085 by its canonical involution-number
initial values 1,1 and recurrence t(n+2)=t(n+1)+(n+1)*t(n). The square and
the recurrence below are written in the integers to preserve signed arithmetic.

Mathar conjectured the order-three recurrence on October 5, 2014. Munarini
confirmed it on August 31, 2017. We state it for every n>=3, exactly the
indices for which all three preceding zero-indexed terms are defined.
The recurrence to be proved is not used in the sequence definition.
-/

namespace OMA.S_oeis_a111883

def involutions : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n+2 => involutions (n+1) + (n+1)*involutions n

def a (n : ℕ) : ℤ := involutions n ^ 2

theorem main : ∀ n : ℕ, 3 ≤ n →
    a n - (n : ℤ)*a (n-1) - (n : ℤ)*((n : ℤ)-1)*a (n-2) +
      ((n : ℤ)-1)*((n : ℤ)-2)^2*a (n-3) = 0 := by
  sorry

end OMA.S_oeis_a111883
