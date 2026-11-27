import Mathlib

/-!
# Infinitely many prime quadruplets?

Source: a prime quadruplet is a set of four primes of the form
`p, p + 2, p + 6, p + 8`. The open question asks whether infinitely many
such quadruplets exist.
Credit: @ihateSAS
-/

namespace OMA.S_wp_are_there_infinitely_many_prime_quadruplets

theorem main :
    Set.Infinite {p : ℕ | p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_prime_quadruplets
