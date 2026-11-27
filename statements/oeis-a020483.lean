import Mathlib

/-!
# A020483: Least prime p such that p+2n is also prime.

Source: https://oeis.org/A020483
Credit: @sntntHb

Conjecture (Jens Kruse Andersen, Nov 28 2004, stated on the OEIS page): `a(n)` always exists,
i.e. for every `n ≥ 0` (the offset is 0) there is a prime `p` such that `p + 2n` is also prime.

Existence of some such prime is equivalent to existence of the least one.
-/

namespace OMA.S_oeis_a020483

theorem main : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ (p + 2 * n).Prime := by
  sorry

end OMA.S_oeis_a020483
