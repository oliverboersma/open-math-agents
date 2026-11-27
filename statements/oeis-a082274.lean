import Mathlib.Data.Nat.Digits.Defs

/-!
# OEIS A082274

Source: https://oeis.org/A082274 (Amarnath Murthy, OEIS Foundation,
CC BY-SA 4.0). The sequence lists positive decimal palindromes that remain
palindromic after adding two. The initial seven values are 1 through 7.
The conjectured formula for all subsequent values is equivalent to saying
that the remaining terms are exactly the positive repdigits of nines.
The OEIS entry records Felix Fröhlich's proof from July 2014.
-/

namespace OMA.S_oeis_a082274

def Pal (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

theorem main : ∀ n : ℕ, 0 < n →
    (Pal n ∧ Pal (n + 2) ↔ n ≤ 7 ∨ ∃ k : ℕ, 0 < k ∧ n = 10^k - 1) := by
  sorry

end OMA.S_oeis_a082274
