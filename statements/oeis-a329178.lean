import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A329178: sum of Padovan products at distance two

Source: https://oeis.org/A329178
The Padovan numbers are indexed as in A000931, with initial values 1, 0, 0.
-/

namespace OMA.S_oeis_a329178

def padovan : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | n + 3 => padovan (n+1) + padovan n

def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n+1), padovan (i+5) * padovan (i+7)

theorem main :
    (let x := (PowerSeries.X : PowerSeries ℤ)
     ((1-x)*(1-2*x+x^2-x^3)*(1+x-x^3))*PowerSeries.mk a =
      1+x-x^2+x^3-x^4) ∧
    (∀ n : ℕ, 6 < n →
      a n = 2*a (n-1)-2*a (n-4)+2*a (n-5)-2*a (n-6)+a (n-7)) := by
  sorry

end OMA.S_oeis_a329178
