import Mathlib

/-!
# OEIS A325695

Count partitions of n into three distinct positive parts a < b < c for
which c is not the sum of a and b. The two free coordinates u=a−1 and
v=b−a−1 are nonnegative. They determine a,b, and the remaining part c
is obtained by subtracting a+b from n. Every valid partition occurs once.

Colin Barker proposed the recurrence for n>9 and the rational generating
function below. Multiplication by the denominator, which has constant
coefficient 1, specifies the ordinary generating function uniquely.

Source: https://oeis.org/A325695
-/

namespace OMA.S_oeis_a325695

def allowed (n u v : ℕ) : Bool :=
  let a := u+1
  let b := a+v+1
  let c := n-(a+b)
  decide (b<c ∧ a+b+c=n ∧ c≠a+b)

def term (n : ℕ) : ℕ := ∑ u ∈ Finset.range (n+1),
  ((Finset.range (n+1)).filter (fun v => allowed n u v)).card

noncomputable def series : PowerSeries ℚ := PowerSeries.mk (fun n => term n)

open PowerSeries in
theorem main :
    (∀ k : ℕ, term (k+10)+term (k+5)+term (k+4)+term (k+3) =
      term (k+8)+term (k+7)+term (k+6)+term (k+1)) ∧
    ((1-X)^3*(1+X)^2*(1+X^2)*(1+X+X^2))*series = X^7*(1+X+2*X^2) := by
  sorry

end OMA.S_oeis_a325695
