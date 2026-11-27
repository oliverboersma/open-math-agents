import Mathlib

/-!
# A086845: a(1) = 0, a(n) = a(floor(n/2)) + 2*a(ceiling(n/2)) + floor(n/2).

Source: https://oeis.org/A086845
Credit: @marcelopierry

Conjecture (Sean A. Irvine, Jul 14 2022, in the comments of A086845): A086845 is the sequence of
partial sums of A087808.

Conventions:
* A086845 has offset 1: a(1) = 0 and a(n) = a(floor(n/2)) + 2*a(ceiling(n/2)) + floor(n/2) for
  n >= 2, with ceiling(n/2) = (n + 1)/2 in natural-number division. The value a(0) = 0 is a
  placeholder outside the sequence. Data: 0, 1, 3, 5, 9, 12, 16, 19, 27, 32, ...
* A087808 has offset 0: A087808(0) = 0, A087808(2n) = 2*A087808(n) and
  A087808(2n+1) = A087808(n) + 1 (data 0, 1, 2, 2, 4, 3, 4, 3, 8, ...).
* Matching the offsets, the partial sums are a(n) = A087808(0) + ... + A087808(n-1) for n >= 1
  (this reproduces the data of A086845).
-/

namespace OMA.S_oeis_a086845

/-- A087808 (offset 0). -/
def A087808 : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 2 * A087808 ((n + 1) / 2) else A087808 ((n + 1) / 2) + 1
decreasing_by all_goals omega

/-- A086845 (offset 1; a 0 is a placeholder). -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => a ((n + 2) / 2) + 2 * a ((n + 3) / 2) + (n + 2) / 2
decreasing_by all_goals omega

/-- Irvine's conjecture: A086845 is the partial sums of A087808. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.range n, A087808 k := by
  sorry

end OMA.S_oeis_a086845
