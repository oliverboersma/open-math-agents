import Mathlib.Algebra.Polynomial.Derivative

/-!
# Divisibility of the derivatives of a polynomial

Source: https://mathoverflow.net/questions/335694 (Seva, July 8, 2019).
Credit: @Spinausore

Classify the pairs (f,m) admitting a nonconstant Q. Translating the
variable and scaling f preserve the property, so the family's shift
and nonzero scalar are explicit. Since m ≥ 2, the natDegree bound
also includes the zero remainder.
-/

namespace OMA.S_mo_335694
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem main : ∀ (f : K[X]) (m : ℕ), 2 ≤ m → 2*m ≤ f.natDegree →
    ((∃ Q : K[X], 0 < Q.natDegree ∧ ∀ k : ℕ, 1 ≤ k → k ≤ Q.natDegree →
      ∃ P R : K[X], (derivative^[k]) (Q*f) = P*f+R ∧ R.natDegree < m) ↔
    ∃ (a c : K) (r : K[X]), c ≠ 0 ∧ r.natDegree < m ∧
      f = C c * (X - C a) ^ f.natDegree + r) := by
  sorry

end OMA.S_mo_335694
