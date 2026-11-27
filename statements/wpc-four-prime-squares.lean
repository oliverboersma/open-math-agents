import Mathlib

/-!
# Sums of four squares of primes (Waring–Goldbach)

Source: https://en.wikipedia.org/wiki/Waring%E2%80%93Goldbach_problem
Credit: @LAPRAI

Is every sufficiently large integer `n ≡ 4 (mod 24)` a sum of four squares of primes?
(Hua proved the analogue with five squares for `n ≡ 5 (mod 24)`.)

## Encoding

* *Sufficiently large*: there is a threshold `N` beyond which the property holds.
* The four primes need not be distinct (the standard reading of a sum of four squares of primes).
* The congruence `n ≡ 4 (mod 24)` is the local condition: a sum of four squares of primes
  larger than `3` is always `≡ 4 (mod 24)`.
* The question is stated in its expected positive form; a disproof would answer it negatively.
-/

namespace OMA.S_wpc_four_prime_squares

/-- Every sufficiently large `n ≡ 4 (mod 24)` is a sum of four squares of primes. -/
theorem main : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n % 24 = 4 →
    ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧
      n = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 := by
  sorry

end OMA.S_wpc_four_prime_squares
