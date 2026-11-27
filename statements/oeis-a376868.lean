import Mathlib

/-!
# A376868: a(n) = n! * 4^binomial(n, 2).

Source: https://oeis.org/A376868
Credit: @marcelopierry

Conjecture (in the comments of A376868): a(n) is the sum of the permanents of all n X n 0-1
matrices.

Conventions:
* Offset 0: a(n) = n! * 4^binomial(n, 2), data 1, 1, 8, 384, 98304, ...
* A 0-1 matrix is an n X n matrix with entries in `Fin 2` = {0, 1}, read as natural numbers;
  the sum runs over all 2^(n^2) such matrices. The permanent is Mathlib's `Matrix.permanent`
  (for n = 0 the empty matrix has permanent 1).
-/

namespace OMA.S_oeis_a376868

/-- A376868(n) = n! * 4^binomial(n, 2). -/
def a (n : ℕ) : ℕ := n.factorial * 4 ^ n.choose 2

/-- The conjecture: the permanents of all n X n 0-1 matrices sum to a(n). -/
theorem main : ∀ n : ℕ,
    ∑ M : Matrix (Fin n) (Fin n) (Fin 2), (M.map (fun x => (x : ℕ))).permanent = a n := by
  sorry

end OMA.S_oeis_a376868
