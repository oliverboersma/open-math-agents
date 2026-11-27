import Mathlib

/-!
Source: https://oeis.org/A081921
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A081/A081921.seq
Credit: @Heart-galaxy

The defining e.g.f. is exp(3x)/sqrt(1-x^2). Its half-power factor is
expanded exactly using Y(t)=Sum centralBinom(n)*t^n/4^n and B(x)=Y(x^2).
The companion proof also establishes (1-x^2)*B(x)^2=1 and B(0)=1.
Multiplication by exp(3x) is the source's independent coefficient formula.
Robert Israel records the differential-equation proof of Mathar's
conjecture on March 14, 2019. Offset zero gives the full range n>=3.
-/

namespace OMA.S_oeis_a081921
open PowerSeries

noncomputable def Y : PowerSeries ℚ := mk fun n => (n.centralBinom:ℚ)/(4:ℚ)^n
noncomputable def B : PowerSeries ℚ := Y.subst (X^2)
noncomputable def E : PowerSeries ℚ := (exp ℚ).subst (C 3*X)
noncomputable def egf : PowerSeries ℚ := E*B
noncomputable def a (n : ℕ) : ℚ := (Nat.factorial n:ℚ)*coeff n egf

theorem main : ∀ n : ℕ, 3 ≤ n →
    a n-3*a (n-1)-((n:ℚ)-1)^2*a (n-2)+
      3*((n:ℚ)-1)*((n:ℚ)-2)*a (n-3)=0 := by
  sorry

end OMA.S_oeis_a081921
