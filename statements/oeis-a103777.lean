import Mathlib

/-!
# A103777: Numbers k such that f(k), f(k+1) and f(k+2) are all primes, where f(k) = 8*k^2 + 4*k + 1

Source: https://oeis.org/A103777
Credit: @xor2k

Formalizes the conjecture in the comments of OEIS A103777, which reads:
All terms are divisible by 5, hence conjecture: there is no such k that f(k), f(k+1),f(k+2)
and f(k+3) are primes.

Conventions: `f(k) = 8*k^2 + 4*k + 1` as in the sequence name; `k` ranges over all natural
numbers (the OEIS terms are positive integers; also allowing `k = 0` only makes the statement
stronger). Primality is `Nat.Prime`. The statement says that no four consecutive values
`f(k), f(k+1), f(k+2), f(k+3)` are all prime.
-/

namespace OMA.S_oeis_a103777

/-- The polynomial `f(k) = 8*k^2 + 4*k + 1`. -/
def f (k : ℕ) : ℕ :=
  8 * k ^ 2 + 4 * k + 1

/-- There is no `k` such that `f(k)`, `f(k+1)`, `f(k+2)` and `f(k+3)` are all prime. -/
theorem main :
    ∀ k : ℕ, ¬ (Nat.Prime (f k) ∧ Nat.Prime (f (k + 1)) ∧ Nat.Prime (f (k + 2)) ∧
      Nat.Prime (f (k + 3))) := by
  sorry

end OMA.S_oeis_a103777
