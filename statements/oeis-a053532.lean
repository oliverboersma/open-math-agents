import Mathlib

/-!
Source: https://oeis.org/A053532
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A053/A053532.seq
Credit: @Heart-galaxy

The source presents Mathar's recurrence as a conjecture (July 6, 2020),
without a recorded proof status. The independent defining EGF is
(1-x)^(-1/2)*exp(-x/2-x^2/4-x^3/6). Its half-power factor is the exact
central-binomial series Y below. The polynomial P is the same exponent,
written as -x*(6+3x+2x^2)/12. Offset zero gives the full range n>=4.
-/

namespace OMA.S_oeis_a053532
open PowerSeries

noncomputable def Y : PowerSeries ℚ := mk fun n => (n.centralBinom:ℚ)/(4:ℚ)^n
noncomputable def P : PowerSeries ℚ := C (-1/12:ℚ)*X*(6+3*X+2*X^2)
noncomputable def E : PowerSeries ℚ := (exp ℚ).subst P
noncomputable def egf : PowerSeries ℚ := Y*E
noncomputable def a (n : ℕ) : ℚ := (Nat.factorial n:ℚ)*coeff n egf

theorem main : ∀ n : ℕ, 4 ≤ n →
    2*a n+2*(-(n:ℚ)+1)*a (n-1)-((n:ℚ)-1)*((n:ℚ)-2)*((n:ℚ)-3)*a (n-4)=0 := by
  sorry

end OMA.S_oeis_a053532
