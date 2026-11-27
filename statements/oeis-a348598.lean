import Mathlib.Data.Nat.Prime.Basic

/-!
# The minimizing modulus in OEIS A348598

Michel Lagneau asks whether the least qualifying prime above a term of
A002496 must use the next term as its modulus. A002496 lists the primes
of the form k² + 1 in increasing order. We quantify directly over two
consecutive such primes, so no assumption of infinitude is needed.

Source: https://oeis.org/A348598
Credit: @domthedeveloper
-/

namespace OMA.S_oeis_a348598

/-- A term of OEIS A002496. -/
def squarePrime (p : ℕ) : Prop :=
  p.Prime ∧ ∃ k : ℕ, p = k ^ 2 + 1

/-- The next term after a in the increasing sequence of square-plus-one primes. -/
def nextSquarePrime (a b : ℕ) : Prop :=
  squarePrime b ∧ a < b ∧ ∀ t, squarePrime t → a < t → b ≤ t

/-- The larger prime p qualifies at a using the larger prime q as its modulus. -/
def qualifies (a p q : ℕ) : Prop :=
  squarePrime p ∧ a < p ∧ squarePrime q ∧ a < q ∧ p % q = a % q

/-- Minimize p over all eligible moduli q. Every witnessing q must be the next term. -/
theorem main : ∀ a b p q : ℕ, squarePrime a → nextSquarePrime a b →
    qualifies a p q → (∀ t r, qualifies a t r → p ≤ t) → q = b := by
  sorry

end OMA.S_oeis_a348598
