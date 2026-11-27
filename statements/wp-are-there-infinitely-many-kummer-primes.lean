import Mathlib

/-!
# Are there infinitely many Kummer primes?

Source: https://en.wikipedia.org/wiki/Euclid_number#Generalization
Credit: @sntntHb

A Euclid number of the second kind (Kummer number) is `E n = p_n# - 1`, where `p_n#` is the
`n`-th primorial, the product of the first `n` primes. It is not known whether infinitely many
Kummer numbers are prime. The statement below asserts that they are.

Conventions:
- The `i`-th prime (0-indexed) is `Nat.nth Nat.Prime i`, so `Nat.nth Nat.Prime 0 = 2` and
  `p_n# = ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i` is the product of the first `n` primes.
  This differs from Mathlib's `primorial m` (product of the primes `≤ m`).
- For `n = 0` the Kummer number is `1 - 1 = 0`, which is not prime, so including `n = 0`
  does not change the set's infiniteness.
-/

namespace OMA.S_wp_are_there_infinitely_many_kummer_primes

/-- The `n`-th Kummer number `p_n# - 1`. -/
noncomputable def kummerNumber (n : ℕ) : ℕ :=
  (∏ i ∈ Finset.range n, Nat.nth Nat.Prime i) - 1

theorem main : {n : ℕ | (kummerNumber n).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_kummer_primes
