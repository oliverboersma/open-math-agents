import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic

/-!
# OEIS A386969

Jules Beauchamp's Recamán variant starts at zero. Subtract the new index
when the difference is nonnegative and has never occurred, otherwise add
the new index and three. Bill McEachen conjectures explicit formulas for
odd and even indices from index three on. Zhuorui He conjectures the
ordinary generating function x(4+2x+11x³−2x⁴−9x⁵)/(1−x²)².

The second conclusion equates the integer coefficients after multiplying
by (1−x²)². The two parity cases in the first conclusion also give
McEachen's equivalent expression using (−1)^n.

Source: https://oeis.org/A386969
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a386969

def nextValue (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  if n + 1 ≤ a n ∧ ∀ i : Fin (n + 1), a i ≠ a n - (n + 1) then
    a n - (n + 1)
  else a n + (n + 1) + 3

def lag (a : ℕ → ℕ) (n k : ℕ) : ℤ :=
  if k ≤ n then (a (n - k) : ℤ) else 0

def numerator : ℕ → ℤ
  | 1 => 4
  | 2 => 2
  | 4 => 11
  | 5 => -2
  | 6 => -9
  | _ => 0

theorem main : ∀ a : ℕ → ℕ, a 0 = 0 → (∀ n, a (n + 1) = nextValue a n) →
    (∀ n, 3 ≤ n → a n = if n % 2 = 0 then 2*n + 7 else n + 5) ∧
    (∀ n, (a n : ℤ) - 2 * lag a n 2 + lag a n 4 = numerator n) := by
  sorry

end OMA.S_oeis_a386969
