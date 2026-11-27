import Mathlib

/-!
# A176268: Primes of a Generalized Cunningham chain of length 9 by the function f(p) = 2 * p + 13.

Source: https://oeis.org/A176268
Credit: @LAPRAI

Formalizes the OEIS comment: It is conjectured that arbitrarily long such chains exist.

Conventions: a chain of length `L` for `f(p) = 2p + 13` is a start `p` such that `p, f(p), ..., f^(L-1)(p)` are all prime.
-/

namespace OMA.S_oeis_a176268

/-- The map `f(p) = 2p + 13`. -/
def f (p : ℕ) : ℕ := 2 * p + 13

/-- For every length `L` there is a chain `p, f(p), ..., f^(L-1)(p)` of primes. -/
theorem main : ∀ L : ℕ, ∃ p : ℕ, ∀ i : ℕ, i < L → (f^[i] p).Prime := by
  sorry

end OMA.S_oeis_a176268
