import Mathlib

/-!
# A145824: Lower twin primes p1 such that p1-1 is a square.

Source: https://oeis.org/A145824
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: There exist an infinite number of primes of this form.

Conventions: a lower twin prime is a prime `p` with `p + 2` prime; `p - 1` a square means `p = k^2 + 1`.
-/

namespace OMA.S_oeis_a145824

/-- There are infinitely many primes `p` with `p + 2` prime and `p - 1` a perfect square. -/
theorem main : {p : ℕ | p.Prime ∧ (p + 2).Prime ∧ ∃ k : ℕ, p = k ^ 2 + 1}.Infinite := by
  sorry

end OMA.S_oeis_a145824
