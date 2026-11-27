import Mathlib

/-!
# A300657: a(n) = Sum_{d|n} sigma(d) mod d

Source: https://oeis.org/A300657
Credit: @xor2k

Formalizes the conjecture in the comments of OEIS A300657 (offset 1), which reads:
a(n) >= A054024(n). Conjecture: a(n) = A054024(n) only for the noncomposite numbers A008578.

Conventions:
* `sigma` is the sum of divisors, Mathlib's `ArithmeticFunction.sigma 1`; `mod` is `%` on `ℕ`.
* `a(n) = Sum_{d | n} (sigma(d) mod d)`, summing over `Nat.divisors n` (as in the OEIS programs).
* `A054024(n) = sigma(n) mod n`.
* The noncomposite numbers A008578 are `1` together with the primes.
* `n` ranges over the offset `n >= 1`. The phrase only for is read in the usual OEIS sense of
  exactly for, i.e. as an equivalence: `a(n) = A054024(n)` holds if and only if `n` is `1` or a
  prime. (The direction from noncomposite to equality is the easy one; both are included.)
* The inequality `a(n) >= A054024(n)` is stated in the entry as a fact, not as part of the
  conjecture, and is not formalized here.
-/

namespace OMA.S_oeis_a300657

/-- `A054024(n) = sigma(n) mod n`. -/
def b (n : ℕ) : ℕ :=
  ArithmeticFunction.sigma 1 n % n

/-- `A300657(n) = Sum_{d | n} (sigma(d) mod d)`. -/
def a (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, ArithmeticFunction.sigma 1 d % d

/-- For `n >= 1`, `a(n) = A054024(n)` exactly when `n` is noncomposite (`1` or a prime). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (a n = b n ↔ n = 1 ∨ Nat.Prime n) := by
  sorry

end OMA.S_oeis_a300657
