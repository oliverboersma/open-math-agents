import Mathlib

/-!
# A280321: Number of 2 x 2 matrices over {0, ..., n} with det = n * perm

Source: https://oeis.org/A280321
Credit: @AkiRA-COM-FP

Formalizes Colin Barker's OEIS A280321 conjectures (offset 0):
`a(n) = (1 + 2*n)^2` for `n > 1`, and `a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3)` for `n > 4`.
-/

namespace OMA.S_oeis_a280321

/-- Number of 2 x 2 matrices with entries in `{0, ..., n}` satisfying
`det = n * permanent`, i.e., `a*d - b*c = n * (a*d + b*c)`. -/
def a (n : ℕ) : ℕ :=
  (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ
      (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun t =>
      ((t.1 : ℤ) * (t.2.2.2 : ℤ) - (t.2.1 : ℤ) * (t.2.2.1 : ℤ)) =
        (n : ℤ) * ((t.1 : ℤ) * (t.2.2.2 : ℤ) + (t.2.1 : ℤ) * (t.2.2.1 : ℤ)))).card

/-- For every `n > 1`, `a(n) = (1 + 2*n)^2`, and for every `n > 4`,
`a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3)`. -/
theorem main :
    (∀ n : ℕ, 1 < n → a n = (1 + 2 * n) ^ 2) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ)) := by
  sorry

end OMA.S_oeis_a280321
