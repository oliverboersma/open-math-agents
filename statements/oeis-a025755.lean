import Mathlib

/-!
# The corrected Patalan recurrence recorded in OEIS A025755

Source: https://oeis.org/A025755
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A025/A025755.seq
Credit: @Heart-galaxy

A025755 has offset 0, initial a(0)=1, and the explicit formula
100^(n-1)*Pochhammer(9/10,n-1)/n! for n>=1. We represent these exact values
in the rationals and use Mathlib's ascending Pochhammer polynomial evaluated
at 9/10. The two branches below preserve the source's separate zero convention.

Mathar conjectured the displayed recurrence on July 28, 2014. Israel confirmed
it on October 5, 2014 with the explicit correction that it holds for n>=2
and is false at n=1. We retain exactly that corrected range. This file states
the known recurrence and does not assert the invalid index-one instance.
-/

namespace OMA.S_oeis_a025755

noncomputable def a : ℕ → ℚ
  | 0 => 1
  | n + 1 => (100 : ℚ)^n * (ascPochhammer ℚ n).eval (9/10) / (n+1).factorial

theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ)*a n + 10*(-10*(n : ℚ)+11)*a (n-1) = 0 := by
  sorry

end OMA.S_oeis_a025755
