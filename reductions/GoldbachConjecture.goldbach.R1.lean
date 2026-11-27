import FormalConjectures.Wikipedia.GoldbachConjecture

-- Reduction GoldbachConjecture.goldbach.R1 of the Goldbach conjecture
-- Credit: @marcusbuffett

/-!
# Goldbach's conjecture: a kernel-checked initial range, and the open rest

* `H1`: every even `n` with `2 < n ≤ 10000` is a sum of two primes. Checked inside the Lean
  kernel by a verified trial-division search.
* `H2`: every even `n > 10000` is a sum of two primes. This is the open conjecture (it has been
  verified numerically up to `4 * 10 ^ 18` by Oliveira e Silva, Herzog and Pardi; the range here
  is only what is cheap to check in the kernel).
-/

namespace OMA.R_GoldbachConjecture_goldbach_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → Even n → n ≤ 10000 → ∃ p q, Prime p ∧ Prime q ∧ n = p + q

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 < n → Even n → ∃ p q, Prime p ∧ Prime q ∧ n = p + q

theorem main : H1 → H2 → type_of% @GoldbachConjecture.goldbach := by
  intro h1 h2 n hn he
  by_cases h : n ≤ 10000
  · exact h1 n hn he h
  · exact h2 n (by omega) he

end OMA.R_GoldbachConjecture_goldbach_R1
