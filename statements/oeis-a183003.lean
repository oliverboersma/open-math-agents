import Mathlib

/-!
# A183003: a(n) = A183002(n)/2.

Source: https://oeis.org/A183003
Credit: @marcelopierry

Conjecture (Sean A. Irvine, Jul 14 2022, in the comments of A183003): partial sums of A072670.

Conventions:
* A161840(n), the number of noncentral divisors of n, is tau(n) - 2 + (tau(n) mod 2) (the
  formula given in A161840 and A183002), where tau(n) is the number of divisors of n. For n >= 1
  the value is a natural number (tau(1) = 1 gives 0).
* A183002(n) = Sum_{k=1..n} A161840(k), the total number of noncentral divisors of 1, ..., n
  (offset 1), and A183003(n) = A183002(n)/2 (offset 1; data 0, 0, 0, 1, 1, 2, 2, 3, 4, 5, ...).
* A072670(m) (offset 0) is the number of ways to write m as i*j + i + j with 0 < i <= j; such
  i, j are at most m, so they are counted inside {1, ..., m} x {1, ..., m}
  (data 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 2, ...).
* Matching the offsets as in the data, the partial sums are A183003(n) = A072670(0) + ... +
  A072670(n-1) for n >= 1.
-/

namespace OMA.S_oeis_a183003

/-- A161840(n) = tau(n) - 2 + (tau(n) mod 2). -/
def A161840 (n : ℕ) : ℕ := n.divisors.card + n.divisors.card % 2 - 2

/-- A183002(n) = Sum_{k=1..n} A161840(k). -/
def A183002 (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, A161840 k

/-- A183003(n) = A183002(n)/2. -/
def a (n : ℕ) : ℕ := A183002 n / 2

/-- A072670(m): the number of ways to write m = i*j + i + j with 0 < i <= j. -/
def A072670 (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 ≤ p.2 ∧ p.1 * p.2 + p.1 + p.2 = m)).card

/-- Irvine's conjecture: A183003 is the partial sums of A072670. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ m ∈ Finset.range n, A072670 m := by
  sorry

end OMA.S_oeis_a183003
