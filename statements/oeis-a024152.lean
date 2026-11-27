import Mathlib

/-!
# A024152: a(n) = 12^n - n^12

Source: https://oeis.org/A024152
Credit: @AkiRA-COM-FP

Formalizes the OEIS A024152 conjectured linear recurrence of signature
`(25, -234, 1222, -4147, 9867, -17160, 22308, -21879, 16159, -8866, 3510, -949, 157, -12)`.
-/

namespace OMA.S_oeis_a024152

/-- Sequence `a(n) = 12^n - n^12` in `ℤ`. -/
def a (n : ℕ) : ℤ :=
  12 ^ n - (n : ℤ) ^ 12

/-- For every `n >= 14`, `a(n)` satisfies the 14th-order linear recurrence. -/
theorem main :
    ∀ n : ℕ, 14 ≤ n →
      a n = 25 * a (n - 1) - 234 * a (n - 2) + 1222 * a (n - 3) -
        4147 * a (n - 4) + 9867 * a (n - 5) - 17160 * a (n - 6) +
        22308 * a (n - 7) - 21879 * a (n - 8) + 16159 * a (n - 9) -
        8866 * a (n - 10) + 3510 * a (n - 11) - 949 * a (n - 12) +
        157 * a (n - 13) - 12 * a (n - 14) := by
  sorry

end OMA.S_oeis_a024152
