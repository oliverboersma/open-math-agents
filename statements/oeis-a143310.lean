import Mathlib

/-!
# A143310: Triangle read by rows, A000012 * A127446, 1 <= k <= n.

Source: https://oeis.org/A143310
Credit: @marcelopierry

Conjecture (Mats Granvik, Feb 26 2021, in the formulas of A143310):
T(n,k) = Sum_{i=1..n} [i*k <= n]*i*k.

Conventions:
* Rows and columns are indexed by 1 <= k <= n (offset 1). Both factors are lower triangular
  matrices indexed the same way, and the product is the matrix product.
* A000012 as a triangle is the lower triangular matrix of 1's: entry 1 for k <= n.
* A127446(n,k) = n*A051731(n,k), where A051731(n,k) = 1 if k divides n and 0 otherwise
  (1 <= k <= n); entries outside 1 <= k <= n are 0.
* So T(n,k) = Sum_{j=1..n} A000012(n,j)*A127446(j,k), giving the data 1, 3, 2, 6, 2, 3, 10, 6,
  3, 4, ... The Iverson bracket [i*k <= n] is written as an if-then-else.
-/

namespace OMA.S_oeis_a143310

/-- A127446(n,k) = n if k divides n (1 <= k <= n), 0 otherwise. -/
def A127446 (n k : ℕ) : ℕ := if 1 ≤ k ∧ k ≤ n ∧ k ∣ n then n else 0

/-- A000012 as the lower triangular matrix of 1's. -/
def A000012 (n k : ℕ) : ℕ := if k ≤ n then 1 else 0

/-- A143310: the matrix product A000012 * A127446. -/
def T (n k : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 n, A000012 n j * A127446 j k

/-- Granvik's conjecture. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    T n k = ∑ i ∈ Finset.Icc 1 n, if i * k ≤ n then i * k else 0 := by
  sorry

end OMA.S_oeis_a143310
