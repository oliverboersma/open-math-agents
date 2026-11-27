import Mathlib

/-!
Source: https://oeis.org/A192989
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A192/A192989.seq
Credit: @Heart-galaxy

The sequence is defined by the exact formal e.g.f. exp((1+x)^3-1).
The coefficient at index n is multiplied by n!, in Q. Munarini records
Mathar's conjectured recurrence as true on August 31, 2017. The source
offset is zero; n>=3 is the complete common domain of its four terms.
-/

namespace OMA.S_oeis_a192989
open PowerSeries

noncomputable def egf : PowerSeries ℚ := (exp ℚ).subst ((1+X)^3-1)
noncomputable def a (n : ℕ) : ℚ := (Nat.factorial n : ℚ)*coeff n egf

theorem main : ∀ n : ℕ, 3 ≤ n →
    a n-3*a (n-1)+6*(-(n:ℚ)+1)*a (n-2)-
      3*((n:ℚ)-1)*((n:ℚ)-2)*a (n-3)=0 := by
  sorry

end OMA.S_oeis_a192989
