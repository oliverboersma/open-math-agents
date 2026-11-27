import Mathlib

/-!
# OEIS A000986: Mathar's recurrence for symmetric 0-1 matrices with row sums 2

Source: https://oeis.org/A000986
Credit: @sntntHb

A000986: number of `n X n` symmetric matrices with `(0,1)` entries and all row sums 2
(offset 0: 1, 0, 1, 4, 18, 112, 820, 6912, ...).

Conjecture (R. J. Mathar, Aug 04 2013):
`2*a(n) + 2*(-2*n+1)*a(n-1) + 2*(n^2-2*n-1)*a(n-2) - 2*(n-2)*(n-4)*a(n-3)
 + (n-1)*(n-2)*(n-3)*a(n-4) - (n-2)*(n-3)*(n-4)*a(n-5) = 0`.

Formalized: `a n` counts the symmetric matrices `M : Matrix (Fin n) (Fin n) (Fin 2)` whose rows
all have entry sum 2 (entries read as natural numbers, a diagonal 1 counting once), and `main`
states the recurrence over `ℤ` for every `n >= 5`.
-/

namespace OMA.S_oeis_a000986

open Finset

/-- The number of symmetric `n X n` 0-1 matrices with all row sums 2. -/
def a (n : ℕ) : ℕ :=
  #{M : Matrix (Fin n) (Fin n) (Fin 2) | M.IsSymm ∧ ∀ i, ∑ j, ((M i j : ℕ)) = 2}

theorem main : ∀ n : ℕ, 5 ≤ n →
    2 * (a n : ℤ) + 2 * (-2 * (n : ℤ) + 1) * a (n - 1) +
      2 * ((n : ℤ) ^ 2 - 2 * n - 1) * a (n - 2) - 2 * ((n : ℤ) - 2) * ((n : ℤ) - 4) * a (n - 3) +
      ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * a (n - 4) -
      ((n : ℤ) - 2) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a000986
