import Mathlib

/-!
# A134347: A007318^(-1) * A134346.

Source: https://oeis.org/A134347
Credit: @marcelopierry

Conjecture (Knud Werner, Jan 05 2022, in the formulas of A134347):
T(n,k) = 2^(k+1)*binomial(n,k) for k < n; T(n,n) = 2^(n+1)-1.

Conventions:
* Triangles are infinite lower triangular matrices indexed by 0 <= k <= n (offset 0), and the
  product is the matrix product.
* A134346(n,k) = (2^(n+1)-1)*binomial(n,k).
* A007318 is Pascal's triangle; its inverse as a lower triangular matrix has entries
  (-1)^(n-j)*binomial(n,j) (this is the inverse binomial transform named in A134347). So
  T(n,k) = Sum_{j=0..n} (-1)^(n-j)*binomial(n,j)*A134346(j,k), computed in the integers,
  giving the data 1, 2, 3, 2, 8, 7, 2, 12, 24, 15, ...
-/

namespace OMA.S_oeis_a134347

/-- A134346(n,k) = (2^(n+1)-1)*binomial(n,k). -/
def A134346 (n k : ℕ) : ℤ := (2 ^ (n + 1) - 1) * (n.choose k : ℤ)

/-- A134347: the inverse binomial transform of A134346. -/
def T (n k : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (n.choose j : ℤ) * A134346 j k

/-- Werner's conjecture. -/
theorem main : ∀ n k : ℕ, k ≤ n →
    T n k = if k < n then 2 ^ (k + 1) * (n.choose k : ℤ) else 2 ^ (n + 1) - 1 := by
  sorry

end OMA.S_oeis_a134347
