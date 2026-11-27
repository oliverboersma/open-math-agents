import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# OEIS A091539

Source: https://oeis.org/A091539 (OEIS Foundation, CC BY-SA 4.0).
The triple-factorial formula in the entry writes a(n), for n at least 2,
as the product of two integer factors. The first is the product of 3j+2
for j from 0 to n-1 divided by 10. The second is the difference of
3^n times n! and three times the product of 3j+1, divided by 6.
R. J. Mathar's recurrence applies when all three indices are in range.
-/

namespace OMA.S_oeis_a091539

open Finset

def q (n : ℕ) : ℤ := ∏ j ∈ range n, (3*(j:ℤ)+1)
def block (n : ℕ) : ℤ := ∏ j ∈ range n, (3*(j:ℤ)+2)
def numerator (n : ℕ) : ℤ := (3:ℤ)^n * (n.factorial:ℤ) - 3*q n
def rescaled (n : ℕ) : ℤ := numerator n / 6
def factor (n : ℕ) : ℤ := block n / 10
def a (n : ℕ) : ℤ := factor n * rescaled n

theorem main : ∀ n : ℕ, 4 ≤ n →
    a n - (3*(n:ℤ)-1)*(6*(n:ℤ)-5)*a (n-1) +
      3*(3*(n:ℤ)-5)*((n:ℤ)-1)*(3*(n:ℤ)-1)*(3*(n:ℤ)-4)*a (n-2) = 0 := by
  sorry

end OMA.S_oeis_a091539
