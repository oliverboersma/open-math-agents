import Mathlib

/-!
# OEIS A007405

Irwin's determinant formula for the Dowling numbers, proved by Sela Fried,
Theorem 2 of https://arxiv.org/abs/2606.09913.
-/

open scoped BigOperators Matrix

namespace OMA.S_oeis_a007405

/-- The Dowling numbers with parameter 2, using Fried's recurrence (16)
after reversing the index of summation. -/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => 1
  | n+1 => a n + ∑ k : Fin (n+1), (n.choose k.val : ℤ)*2^k.val*a (n-k.val)
termination_by n
decreasing_by all_goals omega

/-- The binomial matrix in Irwin's conjecture, with indices starting at zero. -/
def binomialMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i.val+1<j.val then 1 else if i.val+1=j.val then -1 else
    ((n-1-j.val).choose (i.val-j.val) : ℤ)

/-- Irwin's determinant identity at every positive dimension. -/
theorem main :
    ∀ n : ℕ, 0 < n → a (n-1) = (binomialMatrix n).det := by
  sorry

end OMA.S_oeis_a007405
