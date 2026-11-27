import Mathlib

/-!
# A234346: Primes of the form 3^k + 3^m - 1, where k and m are positive integers.

Source: https://oeis.org/A234346
Credit: @darealpandaboi

Conjectures on the OEIS page:
* By a conjecture in A234337 or A234347, this sequence should have infinitely many terms.
* (Zhi-Wei Sun) For any integer a > 1, there are infinitely many primes of the form
  a^k + a^m - 1, where k and m are positive integers.

Translation notes.
* Both parts are stated; the first is the case a = 3 of the second.
* With k, m >= 1 and a >= 2, a^k + a^m >= 4, so the natural-number subtraction is exact.
* The set for a = 3 reproduces the listed data: 5, 11, 17, 29, 53, 83, 89, 107, 251, 269, ...
  (checked by computer).
-/

namespace OMA.S_oeis_a234346

/-- Primes of the form a^k + a^m - 1 with k, m positive. -/
def S (a : ℕ) : Set ℕ :=
  {p | p.Prime ∧ ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ p = a ^ k + a ^ m - 1}

theorem main : (S 3).Infinite ∧ ∀ a : ℕ, 1 < a → (S a).Infinite := by
  sorry

end OMA.S_oeis_a234346
