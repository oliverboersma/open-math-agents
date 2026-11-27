import Mathlib

/-!
# A053645: Distance to largest power of 2 less than or equal to n

Source: https://oeis.org/A053645
Credit: @AkiRA-COM-FP

Formalizes Kurkov's OEIS A053645 conjecture (offset 1):
`a(n) = (1 - A036987(n - 1)) * (1 + a(n - 1))` for all `n > 1`, with `a(1) = 0`,
where `a(n) = n - 2^(floor(log_2 n))` and `A036987(m) = 1` iff `m + 1` is a power of 2.
-/

namespace OMA.S_oeis_a053645

/-- Distance from `n` to the largest power of `2` less than or equal to `n`. -/
def a (n : ℕ) : ℕ :=
  n - 2 ^ Nat.log 2 n

/-- Fredholm-Rueppel sequence A036987: `1` if `m + 1` is a power of `2`, else `0`. -/
def a036987 (m : ℕ) : ℕ :=
  if ∃ k ≤ m + 1, m + 1 = 2 ^ k then 1 else 0

/-- For every `n > 1`, `a(n) = (1 - a036987 (n - 1)) * (1 + a (n - 1))`, with `a 1 = 0`. -/
theorem main :
    a 1 = 0 ∧
    ∀ n : ℕ, 1 < n → a n = (1 - a036987 (n - 1)) * (1 + a (n - 1)) := by
  sorry

end OMA.S_oeis_a053645
