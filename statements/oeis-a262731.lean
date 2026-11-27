import Mathlib

/-!
# A262731: Primes p in the form pi(q^2)+pi(r^2) with q and r both prime, where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A262731
Credit: @darealpandaboi

Conjecture (Zhi-Wei Sun): The sequence has infinitely many terms. In general, for each
n = 2, 3, 4, ... there are infinitely many primes p in the form pi(q^n) + pi(r^n) with q and r
both prime.

Translation notes.
* pi is the prime-counting function Nat.primeCounting (number of primes <= x).
* Both parts are stated; the first is the case n = 2 of the second.
* The set for n = 2 reproduces the listed data: 11, 13, 17, 19, 41, 43, 101, 103, 223, 293, ...
  (checked by computer).
-/

namespace OMA.S_oeis_a262731

/-- Primes of the form pi(q^n) + pi(r^n) with q and r prime. -/
def S (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ q r : ℕ, q.Prime ∧ r.Prime ∧
    p = Nat.primeCounting (q ^ n) + Nat.primeCounting (r ^ n)}

theorem main : (S 2).Infinite ∧ ∀ n : ℕ, 2 ≤ n → (S n).Infinite := by
  sorry

end OMA.S_oeis_a262731
