import Mathlib

/-!
# OEIS A135659: a(n) = 24*n + 7

Source: https://oeis.org/A135659 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence is `a(n) = 24*n + 7` with offset 0. The entry records the comment:

  Conjecture: All Mersenne Primes (A000668) > 3 are in this sequence.

A000668 lists the Mersenne primes, i.e. the primes of the form `2^p - 1`. We formalize this
conjecture: every prime `m` of the form `2^p - 1` with `m > 3` equals `24*n + 7` for some
natural number `n`.
-/

namespace OMA.S_oeis_a135659

/-- `a(n) = 24*n + 7`. -/
def a (n : ℕ) : ℕ := 24 * n + 7

/-- Every Mersenne prime greater than `3` is a term of the sequence. -/
theorem main : ∀ m : ℕ, m.Prime → (∃ p : ℕ, m = 2 ^ p - 1) → 3 < m → ∃ n : ℕ, m = a n := by
  sorry

end OMA.S_oeis_a135659
