import Mathlib.Data.Nat.Prime.Defs

/-!
# A085053: Primes of the form `n * k + 1`

Source: https://oeis.org/A085053
Credit: @hiattco

The sequence counts primes of the form `n * k + 1` for `1 ≤ k ≤ n`.
Its nonvanishing conjecture asks for such a prime for every positive `n`.
-/

namespace OMA.S_oeis_a085053

theorem main : ∀ n : ℕ, 0 < n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ Nat.Prime (n * k + 1) := by
  sorry

end OMA.S_oeis_a085053
