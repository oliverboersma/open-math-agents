import Mathlib

/-!
# A052379: Number of integers from 1 to 10^(n+1)-1 that lack 0 and 1 as a digit.

Source: https://oeis.org/A052379
Credit: @ShoQo

Conjecture (R. J. Mathar, May 18 2007): a(n) = A023001(n+2) - 1. (Vim Wenders, Mar 26 2008:
"The conjecture is true".)

Formalization notes:
* Offset 0: a(n) counts k with 1 ≤ k ≤ 10^(n+1) - 1 whose decimal digits (Mathlib's
  `Nat.digits 10`) avoid 0 and 1 (data: 8, 72, 584, ...).
* A023001(n) = (8^n - 1)/7 (data 0, 1, 9, 73, 585, ...); the division is exact.
-/

namespace OMA.S_oeis_a052379

/-- a(n): integers in [1, 10^(n+1) - 1] with no digit 0 or 1. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (10 ^ (n + 1) - 1)).filter
    (fun k => ∀ d ∈ Nat.digits 10 k, d ≠ 0 ∧ d ≠ 1)).card

/-- A023001: (8^n - 1)/7. -/
def A023001 (n : ℕ) : ℕ := (8 ^ n - 1) / 7

theorem main : ∀ n : ℕ, a n = A023001 (n + 2) - 1 := by
  sorry

end OMA.S_oeis_a052379
