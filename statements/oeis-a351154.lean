import Mathlib

/-!
# OEIS A351154

The determinant conjectures for the matrix defining the permanent sequence
A351154. The determinant evaluation is due to Sela Fried,
https://oeis.org/A351154/a351154_1.pdf.
-/

open scoped BigOperators Matrix

namespace OMA.S_oeis_a351154

/-- A351153 as a function of the row and one-based column indices. -/
def triangle (n k : ℕ) : ℚ :=
  (n : ℚ)*((k : ℚ)-1) - (k : ℚ)*((k : ℚ)-3)/2

/-- The symmetric matrix used in the definition of A351154. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => triangle n (min i.val j.val+1) + |(i.val : ℚ)-j.val|

/-- The Roman factorial A159333 is defined on all integer indices. -/
noncomputable def romanFactorial (k : ℤ) : ℚ :=
  if 0 ≤ k then (k.toNat.factorial : ℚ) else
    (-1 : ℚ)^(k+1) / ((-k-1).toNat.factorial : ℚ)

/-- The determinant formula and the equality with the absolute Roman factorial. -/
theorem main :
    (M 0).det = 1 ∧ (M 1).det = 1 ∧
    (∀ n : ℕ, 1 < n → (M n).det = -((n-2).factorial : ℚ)) ∧
    (∀ n : ℕ, |(M n).det| = |romanFactorial ((n:ℤ)-2)|) := by
  sorry

end OMA.S_oeis_a351154
