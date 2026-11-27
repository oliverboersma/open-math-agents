import Mathlib

/-!
Source: https://oeis.org/A032088
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A032/A032088.seq
Credit: @Heart-galaxy

All four imported conjectures are retained. Howroyd records them as true
on October 10, 2017. The sequence uses Russell and Rorabaugh's independent
exact formula (June 22, 2018), a(1)=5, and a(0)=0 for the g.f.'s absent
constant coefficient. On odd n, the source exponent n/2-1/2 is exactly
(n-1)/2, which is an integer. The g.f. is expressed after multiplying by
its denominator with constant coefficient one and expanding the numerator.
The proof adapts the verified base-three A032086 structure.
-/

namespace OMA.S_oeis_a032088

def a (n : ℕ) : ℚ := if n=0 then 0 else if n=1 then 5 else
  ((5:ℚ)^n-(5:ℚ)^((n+1)/2))/2

def series : PowerSeries ℚ := PowerSeries.mk a

theorem main :
    (∀ n : ℕ, 4<n → a n=5*a (n-1)+5*a (n-2)-25*a (n-3)) ∧
    (((1-PowerSeries.C 5*PowerSeries.X)*(1-PowerSeries.C 5*PowerSeries.X^2))*series =
      PowerSeries.C 5*PowerSeries.X-PowerSeries.C 15*PowerSeries.X^2-
        PowerSeries.C 25*PowerSeries.X^3+PowerSeries.C 125*PowerSeries.X^4) ∧
    (∀ n : ℕ, 1<n → Even n → a n=(5:ℚ)^(n/2)*((5:ℚ)^(n/2)-1)/2) ∧
    (∀ n : ℕ, 1<n → Odd n → a n= -5*((5:ℚ)^((n-1)/2)-(5:ℚ)^(n-1))/2) := by
  sorry

end OMA.S_oeis_a032088
