import Mathlib

/-!
# OEIS A224669

Count (n+1)-by-2 matrices with entries 0,1,2 in which every pair of
consecutive rows forms an idempotent matrix. The four equations below
are the entries of the matrix equation A²=A over the integers. The
recursion counts matrices by choosing the next row, starting at a fixed
first row; summing over that row therefore counts each matrix once.

Barker conjectured the closed form and generating function below; the
entry also gives the empirical recurrence. The power series begins at
index one, as in the source.

Source: https://oeis.org/A224669
-/

namespace OMA.S_oeis_a224669

abbrev Row := Fin 3 × Fin 3

def compatible (r s : Row) : Bool :=
  let a : ℕ := r.1
  let b : ℕ := r.2
  let c : ℕ := s.1
  let d : ℕ := s.2
  decide (a*a+b*c=a ∧ a*b+b*d=b ∧ c*a+d*c=c ∧ c*b+d*d=d)

def completions : ℕ → Row → ℕ
  | 0, _ => 1
  | n+1, r => ∑ s : Row, if compatible r s then completions n s else 0

def term (n : ℕ) := ∑ r, completions n r

noncomputable def series : PowerSeries ℚ := PowerSeries.mk (fun n => if n=0 then 0 else term n)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → (term n : ℝ) =
      -4 + ((1-Real.sqrt 5)^n*(-19+13*Real.sqrt 5) + (1+Real.sqrt 5)^n*(19+13*Real.sqrt 5)) /
        (2^(n+1)*Real.sqrt 5)) ∧
    (∀ k : ℕ, term (k+4)+term (k+1) = 2*term (k+3)) ∧
    ((1-X)*(1-X-X^2))*series = X*(12+X-9*X^2) := by
  sorry

end OMA.S_oeis_a224669
