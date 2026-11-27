import Mathlib

/-!
# A084562: Even numbers having no more than two partitions into two odd primes.

Source: https://oeis.org/A084562
Credit: @darealpandaboi

Conjecture: there are no more terms (than the listed 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 28, 32,
38, 68).

Translation notes.
* A partition of n into two odd primes is an unordered pair {p, q} of odd primes with
  p + q = n; it is counted once, by its smaller part p <= n - p.
* This reading reproduces the listed data exactly: the even n in [2, 20000] with at most two
  such partitions are 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 28, 32, 38, 68 (checked by computer).
* No more terms is stated as: every even n with at most two partitions satisfies n <= 68.
  (n = 0 has no partition and also satisfies n <= 68.)
-/

namespace OMA.S_oeis_a084562

/-- The number of partitions of n into two odd primes p <= q, counted by the smaller part p. -/
def numPartitions (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun p => p.Prime ∧ Odd p ∧ (n - p).Prime ∧ Odd (n - p) ∧ p ≤ n - p)).card

theorem main : ∀ n : ℕ, Even n → numPartitions n ≤ 2 → n ≤ 68 := by
  sorry

end OMA.S_oeis_a084562
