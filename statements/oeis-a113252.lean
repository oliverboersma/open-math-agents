import Mathlib

/-!
# A113252: member m = 6 of the 4th-order linear recurrence family a(m, n) of A113249

Source: https://oeis.org/A113252
Credit: @xor2k

OEIS name: Corresponds to m = 6 in a family of 4th-order linear recurrence sequences given by a(n) = m^4*a(n-4) + (2*m)^2*a(n-3) - 4*a(n-1),.

The family, as defined in A113249:
a(m,n) = m^4*a(n-4) + (2*m)^2*a(n-3) - 4*a(n-1), a(m,0) = -1, a(m,1) = 4,
a(m,2) = -13 + 6*(m-1) + 3*(m-1)^2, a(m,3) = (-8+m^2)^2.

Formalizes the conjecture in the comments of OEIS A113252:
Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).

Remark: A113249 to A113256 are the members m = 3, ..., 10 of this family and all carry this same
conjecture about the whole family, so this statement coincides with the one given for A113249.

Conventions: the family parameter `m` ranges over all natural numbers m = 0, 1, 2, ..., as in the
entry, which lists the members m = 0 (A000302), m = 1 (A097948), m = 2 (A056450), m = 3
(A113249), ..., m = 10 (A113256), disregarding signs and/or initial term. Inside the formulas `m` is
cast to `ℤ`, so `m - 1` is integer subtraction. The index `n` has offset 0 as in OEIS. The terms
are signed integers, so `a m : ℕ → ℤ`. The recurrence a(m,n) = m^4*a(m,n-4) + (2*m)^2*a(m,n-3) -
4*a(m,n-1), valid for n >= 4, is written with `n + 4` in place of `n`. Perfect square means
`IsSquare` in `ℤ`, i.e. `a m (2 * n + 1) = r * r` for some integer `r` (this forces the term to
be nonnegative).
-/

namespace OMA.S_oeis_a113252

/-- The family a(m, n): a(m,0) = -1, a(m,1) = 4, a(m,2) = -13 + 6*(m-1) + 3*(m-1)^2,
a(m,3) = (-8+m^2)^2, a(m,n) = m^4*a(m,n-4) + (2*m)^2*a(m,n-3) - 4*a(m,n-1). -/
def a (m : ℕ) : ℕ → ℤ
  | 0 => -1
  | 1 => 4
  | 2 => -13 + 6 * ((m : ℤ) - 1) + 3 * ((m : ℤ) - 1) ^ 2
  | 3 => (-8 + (m : ℤ) ^ 2) ^ 2
  | n + 4 => (m : ℤ) ^ 4 * a m n + (2 * (m : ℤ)) ^ 2 * a m (n + 1) - 4 * a m (n + 3)

/-- For all `m` and `n`, the term `a m (2 * n + 1)` is a perfect square. -/
theorem main : ∀ (m n : ℕ), IsSquare (a m (2 * n + 1)) := by
  sorry

end OMA.S_oeis_a113252
