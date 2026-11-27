import Mathlib

/-!
# A092938: a(n) = least prime p such that 2*prime(n) - p is prime.

Source: https://oeis.org/A092938
Credit: @LAPRAI

Formalizes the OEIS comment: a(n) <= prime(n). Conjecture: a(n) = prime(n) only for n = 1 and 2.

Conventions: offset 1, `prime(1) = 2`, so `prime(1), prime(2)` are `2, 3`. Since `a(n) ≤ prime(n)`, `a(n) = prime(n)` means no prime `p < prime(n)` has `2*prime(n) - p` prime. The statement says this happens exactly for the primes `q ≤ 3`.
-/

namespace OMA.S_oeis_a092938

/-- For a prime `q`, no prime `p < q` has `2q - p` prime exactly when `q = 2` or `q = 3`. -/
theorem main : ∀ q : ℕ, q.Prime →
    ((∀ p : ℕ, p.Prime → p < q → ¬ (2 * q - p).Prime) ↔ q ≤ 3) := by
  sorry

end OMA.S_oeis_a092938
