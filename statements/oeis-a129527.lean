import Mathlib

/-!
# A129527: a(2n) = a(n) + 2n, a(2n+1) = 2n + 1

Source: https://oeis.org/A129527
Credit: @AkiRA-COM-FP

Formalizes Velin Yanev's OEIS A129527 conjecture: for every `n > 0`,
`a(n) = 2 * n - A000265(n)`, where `A000265(n)` is the odd part of `n`.
-/

namespace OMA.S_oeis_a129527

/-- The OEIS sequence A129527: `a(0) = 0`, `a(2n) = a(n) + 2n`, `a(2n+1) = 2n + 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      if (n + 1) % 2 = 0 then a ((n + 1) / 2) + (n + 1)
      else n + 1

/-- The odd part of `n` (OEIS A000265): `n` divided by the highest power of `2` dividing `n`. -/
def oddPart (n : ℕ) : ℕ :=
  n / 2 ^ n.factorization 2

/-- For every `n > 0`, `a(n) = 2 * n - oddPart(n)`. -/
theorem main :
    ∀ n : ℕ, 0 < n → a n = 2 * n - oddPart n := by
  sorry

end OMA.S_oeis_a129527
