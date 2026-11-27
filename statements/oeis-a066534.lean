import Mathlib

/-!
# OEIS A066534: Mathar's recurrence for walks in the Hasse diagram of a Boolean algebra

Source: https://oeis.org/A066534
Credit: @sntntHb

A066534: total number of walks with length > 0 in the Hasse diagram of a Boolean algebra of
order `n` (offset 0: 0, 1, 6, 30, 152, 840, 5232, ...). OEIS gives
`a(n) = Sum_{k=0..n-1} (n!/k!) * 2^k`.

Conjecture (R. J. Mathar, Dec 04 2012):
`a(n) + (-n-4)*a(n-1) + 4*n*a(n-2) + 4*(-n+2)*a(n-3) = 0`.

Formalized: `a n` is the sum above, and `main` states the recurrence over `ℤ` for every `n >= 3`.
-/

namespace OMA.S_oeis_a066534

open Finset

/-- `a(n) = Sum_{k=0..n-1} (n!/k!) * 2^k`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ range n, n.factorial / k.factorial * 2 ^ k

theorem main : ∀ n : ℕ, 3 ≤ n →
    (a n : ℤ) + (-(n : ℤ) - 4) * a (n - 1) + 4 * (n : ℤ) * a (n - 2) +
      4 * (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a066534
