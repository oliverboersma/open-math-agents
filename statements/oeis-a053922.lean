import Mathlib

/-!
# A053922: Numbers k such that k^2 contains only digits {2,4,6}.

Source: https://oeis.org/A053922
Credit: @divmxnd0x

Conjecture (Harvey P. Dale, Jun 16 2022): every number composed of the numeral six repeated `n`
times and ending in the numeral 8 is a term of this sequence, i.e. the square of `66...68`
(`n` sixes followed by one 8) has only the decimal digits 2, 4 and 6.

Formalization notes:
* The number with `n` sixes followed by an 8 is `10 * (6 * (10^n - 1) / 9) + 8`; here
  `(10^n - 1) / 9` is the repunit with `n` ones (exact division in `ℕ`). For `n = 0` it is `8`,
  itself a term of A053922 (`8^2 = 64`), so `n` ranges over all natural numbers.
* For `n = 0, ..., 7` these numbers are 8, 68, 668, 6668, 66668, 666668, 6666668, 66666668, and
  all their squares have digits in `{2, 4, 6}`, as listed in the data of A053922.
-/

namespace OMA.S_oeis_a053922

/-- The number written with `n` sixes followed by an 8. -/
def sixesEight (n : ℕ) : ℕ :=
  10 * (6 * ((10 ^ n - 1) / 9)) + 8

/-- Dale's conjecture: the square of `66...68` only has the decimal digits 2, 4 and 6. -/
theorem main : ∀ n : ℕ, ∀ d ∈ Nat.digits 10 (sixesEight n ^ 2), d = 2 ∨ d = 4 ∨ d = 6 := by
  sorry

end OMA.S_oeis_a053922
