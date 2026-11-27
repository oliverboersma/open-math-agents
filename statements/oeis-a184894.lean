import Mathlib

/-!
# OEIS A184894

The sequence takes the coefficient of degree 2m-1 after composing
x+x^3 with itself m times. Hanna conjectured that this coefficient is
divisible by 3 outside the indices (3^j+1)/2. We also determine its
residue at every candidate exception. In particular 365, the candidate
with j=6, still has zero residue.

Source: https://oeis.org/A184894
-/

namespace OMA.S_oeis_a184894

noncomputable def iteratePoly : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | n+1 => iteratePoly n + (iteratePoly n)^3

noncomputable def term (m : ℕ) := (iteratePoly m).coeff (2*m-1)

theorem main :
    (∀ m : ℕ, 0 < m → (¬ 3 ∣ term m) → ∃ j : ℕ, m=(3^j+1)/2) ∧
    (∀ j : ℕ, (term ((3^j+1)/2) : ZMod 3)=(((3^j+1)/2 : ℕ).choose j : ZMod 3)) ∧
    3 ∣ term 365 := by
  sorry

end OMA.S_oeis_a184894
