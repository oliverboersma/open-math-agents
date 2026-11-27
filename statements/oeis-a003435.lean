import Mathlib

/-!
Source: https://oeis.org/A003435
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A003/A003435.seq
Credit: @Heart-galaxy

The sequence uses Kotesovec's exact two-lag recurrence (February 12, 2014)
with the source's first two values a(2)=8, a(3)=192. This is independent of
Mathar's three-lag conjecture. Values outside the offset-2 domain are set
to zero. Roberto Blanco Gomez records a proof on October 1, 2026.
The full common domain of the conjecture is n>=5. Rational arithmetic
gives exact division and avoids truncated subtraction.
-/

namespace OMA.S_oeis_a003435

def a : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 8
  | 3 => 192
  | k+4 =>
    let n : ℚ := (k:ℚ)+4
    (2*n*(4*n^2-8*n+5)*a (k+3)+4*(n-1)*n*(2*n-1)*a (k+2))/(2*n-3)

theorem main : ∀ n : ℕ, 5 ≤ n →
    a n-(4*(n:ℚ)^2-2*(n:ℚ)+5)*a (n-1)+
      2*((n:ℚ)-1)*(4*(n:ℚ)-17)*a (n-2)+
      12*((n:ℚ)-1)*((n:ℚ)-2)*a (n-3)=0 := by
  sorry

end OMA.S_oeis_a003435
