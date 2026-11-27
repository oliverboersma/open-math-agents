import Mathlib

/-!
# Prime summands congruent to three modulo four (OEIS A279027)

Source: https://oeis.org/A279027, Juri-Stepan Gerasimov, December 31, 2016.
Credit: @Mmexicann
-/

namespace OMA.S_oeis_a279027

/-- Count primes of the form `4*k + 3` for which the complementary summand of `2*n` is prime. -/
def primeCount (n : ℕ) : ℕ :=
  ((Finset.range (2 * n)).filter (fun p =>
    p % 4 = 3 ∧ Nat.Prime p ∧ Nat.Prime (2 * n - p))).card

theorem main : ∀ n : ℕ, 3 ≤ n → 0 < primeCount n := by
  sorry

end OMA.S_oeis_a279027
