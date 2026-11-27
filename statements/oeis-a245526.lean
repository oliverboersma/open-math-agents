import Mathlib

/-!
# A245526: L(2n) mod prime(n), as the residue r with -prime(n)/2 < r <= prime(n)/2

Source: https://oeis.org/A245526
Credit: @niclorusso

Conjecture (in the comments of A245526): a(n) is always nonzero, i.e., prime(n) never divides the
Lucas number L(2*n).

Conventions:
* prime(n) is the n-th prime with prime(1) = 2 (`Nat.nth Nat.Prime (n - 1)`); offset 1.
* Lucas numbers (A000032): L(0) = 2, L(1) = 1, L(k+2) = L(k+1) + L(k).
* The conjecture is stated in its second form: for every n >= 1, prime(n) does not divide L(2n)
  (which is the same as a(n) /= 0).
-/

namespace OMA.S_oeis_a245526

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (k + 2) = L (k + 1) + L k`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | k + 2 => lucas (k + 1) + lucas k

/-- The conjecture on A245526: `prime n` never divides `L(2n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ¬ prime n ∣ lucas (2 * n) := by
  sorry

end OMA.S_oeis_a245526
