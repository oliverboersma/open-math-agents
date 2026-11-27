import Mathlib

/-!
# A158460: Numbers k such that prime(k-1) + 5 is square and equal to prime(k+1) - 1.

Source: https://oeis.org/A158460
Credit: @ShoQo

Conjecture: "If the condition holds, prime(k-1) and prime(k) are twin primes of the form 10m+1
and 10m+3. I.e., the last digits are 1 and 3." (The entry follows it with an argument: "This is
so because ...".)

Formalization notes:
* prime(j) is the j-th prime, prime(1) = 2, i.e. `Nat.nth Nat.Prime (j - 1)`.
* The condition needs k ≥ 2 so that prime(k-1) exists; it is: prime(k-1) + 5 = s^2 for some s,
  and prime(k-1) + 5 = prime(k+1) - 1.
* The conclusion: prime(k) = prime(k-1) + 2 (twin primes), prime(k-1) ≡ 1 (mod 10) and
  prime(k) ≡ 3 (mod 10).
-/

namespace OMA.S_oeis_a158460

/-- prime(j), the j-th prime (prime(1) = 2). -/
noncomputable def prime (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

theorem main : ∀ k : ℕ, 2 ≤ k →
    (∃ s : ℕ, prime (k - 1) + 5 = s ^ 2) → prime (k - 1) + 5 = prime (k + 1) - 1 →
    prime k = prime (k - 1) + 2 ∧ prime (k - 1) % 10 = 1 ∧ prime k % 10 = 3 := by
  sorry

end OMA.S_oeis_a158460
